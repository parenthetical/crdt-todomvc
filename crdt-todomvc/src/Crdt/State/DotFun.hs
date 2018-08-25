{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Crdt.State.DotFun
  ( singleton
  , insert
  , empty
  , toDotsMap
  , elems
  , DotFun(..)
  , Crdt.State.DotFun.map
  , fromDotSet
  )
where

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map.Lazy as Map
import Data.Map.Lazy (Map,(!))
import qualified Data.IntMap.Lazy as IntMap
import Data.IntMap.Lazy (IntMap)
import qualified Data.IntSet as IntSet
import Algebra.Lattice ((\/), (/\), JoinSemiLattice((\/)), BoundedJoinSemiLattice(bottom), MeetSemiLattice((/\)))
import GHC.Generics (Generic)
import Data.Serialize
import Crdt.Dot
import Crdt.State.DotStore (DotStore(..))
import qualified Crdt.Dot.CausalContext as CC
import Crdt.State.Causal (CCrdt(..))
import qualified Crdt.Dot.DotSet as DS
import Crdt.Dot.DotSet (DotSet(..))
import Crdt.Decomposable
import qualified Data.List as List

newtype DotFun i v =
  DotFun (Map i (IntMap v))
  deriving (Eq, Show, Read, Ord, Generic)

instance (Serialize i, Ord i, Serialize v) => Serialize (DotFun i v)

instance (Ord i, Eq v) => JoinSemiLattice (DotFun i v) where
  (\/) (DotFun a) (DotFun b) =
    DotFun
    . Map.filter (not . IntMap.null)
    -- Not correct in general, only for Causal Crdt use.
    $ Map.unionWith (IntMap.union)
    a
    b
instance (Ord i, Eq v) => BoundedJoinSemiLattice (DotFun i v) where
  bottom = empty

instance (Ord i, Eq v) => MeetSemiLattice (DotFun i v) where
  (/\) (DotFun a) (DotFun b) =
    DotFun
    . Map.filter (not . IntMap.null)
    -- Not correct in general, only for Causal CRDT use.
    $ Map.intersectionWith (IntMap.intersection)
    a
    b

instance (Ord i, Eq v) => Decomposable (DotFun i v) where
  decompositions (DotFun df) =
    concatMap (\(i,svs) ->
                 Prelude.map
                 (DotFun . Map.singleton i . (uncurry IntMap.singleton))
                 (IntMap.toList svs))
    $ Map.toList df

instance (Ord i, Ord v)
   => DotStore i (DotFun i v) where
  dots (DotFun m) = DS.DotSet . Map.map IntMap.keysSet $ m
  differenceCC (DotFun df) (CC.CausalContext cc) =
    -- FIXME: This needs IntMap.restrictKeys but it doesn't exist.
    DotFun
    $ Map.differenceWith
    (\dots (compr, dots') ->
        let res = (snd $ IntMap.split compr dots)
                  IntMap.\\
                  (IntMap.fromSet (const ()) dots')
        in if IntMap.null res
           then Nothing
           else Just res)
    df cc

singleton :: (Ord i) => Dot i -> v -> DotFun i v
singleton (Dot i s) v = DotFun $ Map.singleton i (IntMap.singleton s v)

insert :: (Ord i, Eq v) => Dot i -> v -> DotFun i v -> DotFun i v
insert dot v df = singleton dot v \/ df

empty :: DotFun i v
empty = DotFun Map.empty

toDotsMap :: (Ord i) => DotFun i v -> Map (Dot i) v
toDotsMap (DotFun df) =
  Map.fromAscList
  . concatMap (\(i,svs) ->
                Prelude.map (\(s,v) -> (Dot i s, v))
                $ IntMap.toAscList svs)
  $ Map.toAscList df

elems :: (Ord i) => DotFun i v -> [v]
elems = Map.elems . toDotsMap

fromDotSet :: (Ord i) => a -> DotSet i -> DotFun i a
fromDotSet a (DotSet ds) =
  DotFun $ Map.map (IntMap.fromSet (const a)) ds

map :: (Ord i) => (a -> b) -> DotFun i a -> DotFun i b
map f (DotFun df) =
  DotFun . Map.map (IntMap.map f) $ df

dotsValuesOf :: (Ord i) => i -> DotFun i v -> [(Dot i, v)]
dotsValuesOf i (DotFun df) =
  List.map (\(s,v) -> (Dot i s, v))
  . IntMap.toList
  . Map.findWithDefault IntMap.empty i
  $ df
