{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Crdt.State.DotStore where

import Data.Set (Set)
import Crdt.Dot (Dot(..))
import qualified Crdt.Dot.DotSet as DS
import Crdt.Dot.DotSet (DotSet)
import Crdt.Dot.CausalContext (CausalContext(..))
import qualified Crdt.Dot.CausalContext as CC
import qualified Data.Map.Lazy as Map
import Data.Map.Lazy (Map)
import qualified Data.IntSet as IntSet
import Data.IntSet (IntSet)
import Algebra.Lattice ((\/), (/\), JoinSemiLattice((\/)), BoundedJoinSemiLattice(bottom)
                       , MeetSemiLattice((/\))
                       , joins)
import Crdt.Dot.VV (VV(..))

class  (Ord i, BoundedJoinSemiLattice ds, MeetSemiLattice ds) =>
       DotStore i ds | ds -> i where
  dots :: ds -> DS.DotSet i
  differenceCC :: ds -> CausalContext i -> ds
  isBottom :: ds -> Bool

instance (Ord i) => DotStore i (DS.DotSet i) where
  isBottom (DS.DotSet ds) = Map.null ds
  dots ds = ds
    
  differenceCC (DS.DotSet ds) (CausalContext cc) =
    DS.DotSet
    $ Map.differenceWith
    (\dots (compr, dots') ->
        let res = (snd $ IntSet.split compr dots) IntSet.\\ dots'
        in if IntSet.null res
           then Nothing
           else Just res)
    ds cc

instance (Ord i) => DotStore i (CausalContext i) where
  isBottom (CausalContext cc) = Map.null cc
  dots (CausalContext cc) =
    DS.DotSet
    . Map.mapWithKey (\actor (compr,ds) ->
                        IntSet.union (IntSet.fromAscList [0..compr]) ds)
    $ cc
  differenceCC (CausalContext a) (CausalContext b) =
    CausalContext
    $ Map.differenceWith
    (\(compr, dots) (compr', dots') ->
        let res = ((IntSet.fromList [compr'+1, compr])
                    \/ (snd $ IntSet.split compr' dots)) IntSet.\\ dots'
        in if IntSet.null res
           then Nothing
           else Just (-1,res))
    a b


instance (Ord i) => DotStore i (VV i) where
  isBottom (VV vv) = Map.null vv
  dots (VV vv) = joins . map (DS.singleton . (uncurry Dot)) $ Map.toList vv
  differenceCC (VV vv) (CC.CausalContext cc) =
    VV
    $ Map.differenceWith
    (\s (compr, ss') ->
       if (s <= compr || IntSet.member s ss')
       then Nothing
       else Just s)
    vv cc
    


-- FIXME: Do this more efficiently.
ccFromDotStore :: (Ord i, DotStore i ds) => ds -> CausalContext i
ccFromDotStore ds = CC.fromDotSet $ dots ds

ccDifferenceDotSet :: (Ord i) => CausalContext i -> DotSet i -> CausalContext i
ccDifferenceDotSet cc ds =
  CC.fromDotSet (dots cc `DS.difference` ds)
