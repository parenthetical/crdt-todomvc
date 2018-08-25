{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Crdt.State.DotPair
  -- (
  -- )
where

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map.Lazy as Map
import Data.Map.Lazy (Map)
import Algebra.Lattice ((\/), (/\)
                       , JoinSemiLattice((\/)), BoundedJoinSemiLattice(bottom)
                       , MeetSemiLattice((/\))
                       , join)
import GHC.Generics (Generic)
import Data.Serialize
import Crdt.Dot
import Crdt.State.DotStore (DotStore(..))
import qualified Crdt.Dot.CausalContext as CC
import Crdt.State.Causal (CCrdt(..))
import Crdt.Dot.DotSet (DotSet(..))
import qualified Crdt.Dot.DotSet as DS
import Crdt.Decomposable
import Data.List as List

newtype DotPair i a b = DotPair { getPair :: (a, b) }
  deriving (Eq, Show, Read, Ord, Generic, JoinSemiLattice)

instance (Ord i, DotStore i a, DotStore i b)
  => MeetSemiLattice (DotPair i a b) where
  (/\) (DotPair (a,b)) (DotPair (a',b')) =
    DotPair ((a /\ a'), (b /\ b'))

instance (Ord i, JoinSemiLattice a, DotStore i a, JoinSemiLattice b, DotStore i b)
  => BoundedJoinSemiLattice (DotPair i a b) where
  bottom = DotPair (bottom,bottom)

instance (DotStore i a, Decomposable a, DotStore i b, Decomposable b) =>
  Decomposable (DotPair i a b) where
  decompositions (DotPair (a,b)) =
    (DotPair . (,bottom) <$> decompositions a)
    ++
    (DotPair . (bottom,) <$> decompositions b)

instance (DotStore i a, DotStore i b) => DotStore i (DotPair i a b) where
  dots (DotPair (a,b)) = join (dots a) (dots b)
  differenceCC (DotPair (a,b)) cc =
    DotPair ( differenceCC a cc
             , differenceCC b cc
             )
