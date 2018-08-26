{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Crdt.Dot.DotSet
  ( insert
  , empty
  , singleton
  , member
  , difference
  , DotSet(..)
  )
where

import qualified Data.IntSet as IntSet
import Data.IntSet (IntSet)
-- import qualified Data.Set as Set
import qualified Data.Map.Lazy as Map 
import Data.Map.Lazy (Map,(!))
import Algebra.Lattice ((\/), (/\), MeetSemiLattice((/\)),JoinSemiLattice((\/)), BoundedJoinSemiLattice(bottom))
import GHC.Generics (Generic)
import Data.Serialize
import Crdt.Dot
import qualified Data.RangeSet.IntMap as Range
import Crdt.State.Decomposable

newtype DotSet i =
  DotSet (Map i (IntSet))
  deriving (Eq, Show, Read, Ord, Generic, JoinSemiLattice, BoundedJoinSemiLattice)


instance (Ord i) => MeetSemiLattice (DotSet i) where
  (/\) (DotSet a) (DotSet b) = -- TODO: Could be done better?
    DotSet $ Map.intersectionWith (IntSet.intersection) a b

instance (Serialize i, Ord i) => Serialize (DotSet i) where
  -- put = put . toRanges
  -- get = fromRanges <$> get

instance (Ord i) => Decomposable (DotSet i) where
  decompositions (DotSet ds) =
    concatMap (\(i,ss) ->
                 map
                 (DotSet . Map.singleton i . IntSet.singleton)
                 (IntSet.toList ss))
    $ Map.toList ds

insert :: (Ord i) => Dot i -> DotSet i -> DotSet i
insert d ds = ds \/ singleton d

empty :: DotSet i
empty = DotSet Map.empty

singleton :: (Ord i) => Dot i -> DotSet i
singleton (Dot i s) = DotSet $ Map.singleton i (IntSet.singleton s)

member :: (Ord i) => Dot i -> DotSet i -> Bool
member (Dot i s) (DotSet ds) =
  case Map.lookup i ds of
    Nothing -> False
    Just ss -> IntSet.member s ss

difference :: (Ord i) => DotSet i -> DotSet i -> DotSet i
difference (DotSet a) (DotSet b) =
  DotSet
  $ Map.differenceWith (\a b ->
                          let res = a IntSet.\\ b
                          in if IntSet.null res
                             then Nothing
                             else Just res)
  a b
