{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Crdt.State.Causal
  ( CCrdt(..)
  , digest
  )
where

import GHC.Generics (Generic)
import Data.Serialize
import Algebra.Lattice ((\/), (/\)
                       , JoinSemiLattice((\/)), BoundedJoinSemiLattice(bottom)
                       , MeetSemiLattice((/\))
                       , meets, joins)
import qualified Crdt.Dot.CausalContext as CC
import Crdt.Dot.CausalContext (CausalContext(..))
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map.Lazy as Map
import Data.Map.Lazy (Map)
import qualified Crdt.Dot.DotSet as DS
import Crdt.Dot.DotSet (DotSet)
import Crdt.Dot
import Crdt.State.DotStore (DotStore(..), ccDifferenceDotSet, ccFromDotStore)
import Crdt.State.Digestable (Digestable(..), MaybeDigest(..)
                             , strictlyInflates)
import Crdt.State.Decomposable

data CCrdt i ds =
  CCrdt {dotStore :: ds, causalContext :: CausalContext i}
  deriving (Show, Eq, Read, Generic, Ord)

-- Unioning with the dotstore allows for an optimisation where dots
-- added to the DS do not need to be stored in the CC.
instance (Serialize i, Ord i, Serialize ds, DotStore i ds) => Serialize (CCrdt i ds) where
  put (CCrdt ds cc) = put (ds,(cc `ccDifferenceDotSet` dots ds))
  get = (\(ds,cc) -> CCrdt ds (CC.unionDotSet (dots ds) cc)) <$> get

instance ( Ord i
         , DotStore i ds
         ) =>
  JoinSemiLattice (CCrdt i ds) where
  (\/) (CCrdt dsa cca) (CCrdt dsb ccb) =
    CCrdt ((dsa /\ dsb)
            \/ differenceCC dsa ccb -- (ccFromDotStore dsb \/ ccb)
            \/ differenceCC dsb cca -- (ccFromDotStore dsa \/ cca)
          )
    (cca \/ ccb)

instance (DotStore i ds) => BoundedJoinSemiLattice (CCrdt i ds) where
  bottom = CCrdt bottom CC.empty

instance (Ord i, DotStore i ds, Eq ds) =>
  Digestable (CCrdt i ds) (CCrdt i (DotSet i)) where
  digestStrictlyInflates ccrdt digest'' =
    -- TODO: strictlyInflates can be probably be made more performant,
    -- but going for obvious correctness for now using the standard
    -- definition.
    let DigestDigest digest' = digest ccrdt
    in digest' `strictlyInflates` digest''
  digest (CCrdt ds cc) = DigestDigest (CCrdt (dots ds) cc)
  
ccDifferenceDS :: (Ord i) =>
  CausalContext i -> DotSet i -> CausalContext i
ccDifferenceDS cc ds =
  CC.fromDotSet (dots cc `DS.difference` ds)

instance (DotStore i ds, Decomposable ds) =>
  Decomposable (CCrdt i ds) where
  decompositions (CCrdt ds cc) =
    let removes = [ CCrdt bottom (CC.singleton d)
                  | d <-  CC.toList $ ccDifferenceDS cc (dots ds)
                  ]
    in ((\d -> CCrdt d (CC.fromDotSet . dots $ d)) <$> decompositions ds) ++ removes
