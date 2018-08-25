{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Crdt.State.DotMap
  ( Crdt.State.DotMap.lookup
  , empty
  , singleton
  , keys
  , DotMap(..)
  , Crdt.State.DotMap.map
  , toList
  , toMap
  )
where

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map.Lazy as Map
import Data.Map.Lazy (Map)
import Algebra.Lattice ((\/), (/\)
                       , JoinSemiLattice((\/)), BoundedJoinSemiLattice(bottom)
                       , MeetSemiLattice((/\))
                       , joins)
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

newtype DotMap i k ds = DotMap { getMap :: Map k ds }
  deriving (Eq, Show, Read, Ord, Generic, JoinSemiLattice)

instance (Serialize ds, Ord k, Serialize k, Serialize k) => Serialize (DotMap i k ds)

instance (Ord i, Ord k, DotStore i ds) => MeetSemiLattice (DotMap i k ds) where
  (/\) (DotMap a) (DotMap b) =
    DotMap
    . Map.filter (/= bottom)
    $ a /\ b

instance (Ord i, Ord k, JoinSemiLattice ds, DotStore i ds) => BoundedJoinSemiLattice (DotMap i k ds) where
  bottom = empty

instance (DotStore i ds, Ord k, Decomposable ds, Ord i) => Decomposable (DotMap i k ds) where
  decompositions (DotMap dm) =
    concatMap (\(k,ds) ->
                 List.map (singleton k) (decompositions ds))
    $ Map.toList dm

instance (DotStore i ds, Ord k) => DotStore i (DotMap i k ds) where
  dots (DotMap m) = joins . List.map dots $ Map.elems m
  differenceCC (DotMap dm) cc =
    DotMap
    . Map.filter (/= bottom)
    . Map.map (`differenceCC` cc)
    $ dm

lookup :: (DotStore i ds, Ord k) => k -> DotMap i k ds -> ds
lookup k (DotMap m) =
  Map.findWithDefault bottom k m

empty :: (Ord k, DotStore i ds) => DotMap i k ds
empty = DotMap Map.empty

singleton :: (Ord k, DotStore i ds) => k -> ds -> DotMap i k ds
singleton k ds = DotMap $ Map.singleton k ds

keys :: (Ord k, Ord i) => DotMap i k ds -> Set k
keys (DotMap dm) =
  Map.keysSet dm

map :: (Ord k) => (ds -> ds') -> DotMap i k ds -> DotMap i k ds'
map f (DotMap dm) =
  DotMap $ f <$> dm

toList :: (Ord k) => DotMap i k ds -> [(k,ds)]
toList (DotMap dm) = Map.toList dm

toMap :: (Ord k) => DotMap i k ds -> Map k ds
toMap (DotMap dm) = dm
