{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
module Crdt.Dot.CausalContext
  ( CausalContext(..)
  , empty
  , member
  , singleton
  , insert
  , next
  , toList
  , toRanges
  , fromRanges
  , fromDotSet
  , unionDotSet
  , causalVV
  , fromVV
  , Crdt.Dot.CausalContext.lookup
  )
where

import GHC.Generics (Generic)
import Data.Serialize
import qualified Data.Map.Lazy as Map
import Data.Map.Lazy (Map)
import Crdt.Dot (Dot(..))
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.IntSet as IntSet
import Data.IntSet (IntSet)
import Algebra.Lattice ((\/), (/\), JoinSemiLattice((\/))
                       , BoundedJoinSemiLattice(bottom)
                       , MeetSemiLattice((/\)))
import qualified Data.List as List
import Data.Maybe (isJust,fromJust)
import qualified Data.RangeSet.IntMap as Range
import qualified Crdt.Dot.DotSet as DS
import Crdt.Dot.DotSet (DotSet)
import Crdt.Dot.VV (VV(..))
import qualified Crdt.Dot.VV as VV

newtype CausalContext i
  = CausalContext (Map i (Int, IntSet))
  deriving (Show, Eq, Read, Ord, Generic)

instance (Ord i) => JoinSemiLattice (CausalContext i) where
  (\/) (CausalContext a) (CausalContext b) =
    CausalContext $ Map.unionWith unionI a b

instance (Ord i) => BoundedJoinSemiLattice (CausalContext i) where
  bottom = empty

instance (Ord i) => MeetSemiLattice (CausalContext i) where
  (/\) (CausalContext a) (CausalContext b) =
    CausalContext $ Map.intersectionWith
    (\(compr,dots) (compr', dots') ->
       let m = min compr compr'
       in ( m
          , (IntSet.fromList [m+1,compr] \/ dots)
            `IntSet.intersection`
            (IntSet.fromList [m+1,compr'] \/ dots')
          ))
    a b

instance (Serialize i, Ord i) => Serialize (CausalContext i) where
  put = put . toRanges
  get = fromRanges <$> get

data Range = SingletonRange Int
           | Range Int Int
  deriving (Show, Eq, Read, Ord, Generic)

instance Serialize Range

toRanges :: CausalContext i -> Map i [Range]
toRanges (CausalContext cc) = toRanges' <$> cc

toRanges' :: (Int, IntSet) -> [Range]
toRanges' (compr,ss) =
  map (\(a,b) -> if a == b
                 then SingletonRange a
                 else Range a b)
  . Range.toRangeList
  . Range.fromAscList
  $ ([0..compr] ++ IntSet.toAscList ss)

fromRanges :: Map i [Range] -> CausalContext i
fromRanges rrs = CausalContext (fromRanges' <$> rrs)

fromRanges' :: [Range] -> (Int, IntSet)
fromRanges' rrs =
  compressI (-1, IntSet.fromAscList
                 . concatMap (\case {SingletonRange i -> [i]; Range a b -> [a..b]})
                 $ rrs)


toList :: CausalContext i -> [Dot i]
toList (CausalContext cc) =
  concatMap (\(i,(compr,ss)) ->
         Dot i <$> ([0..compr] ++ IntSet.toList ss))
  $ Map.toList cc


empty = CausalContext Map.empty

member :: (Ord i) => Dot i -> CausalContext i -> Bool
member (Dot actor sequence) (CausalContext cc) =
  let (current,ds') = Map.findWithDefault (-1,IntSet.empty) actor cc
  in sequence <= current || IntSet.member sequence ds'

unionI :: (Int, IntSet) -> (Int, IntSet) -> (Int, IntSet)
unionI (a,as) (b,bs) =
  compressI $ (max a b, IntSet.union as bs)

compressI :: (Int, IntSet) -> (Int, IntSet)
compressI (compr,seqNums) =
  let (toDrop, seqNums') =
        List.span (<= compr) . IntSet.toAscList $ seqNums
      compr' = case takeWhile (uncurry (==)) $ zip [compr+1 ..] seqNums' of
        [] -> compr
        continuous -> (fst . last $ continuous)
  -- TODO: optimisable to use Nothing in case nothing changed.
  in (compr', snd $ IntSet.split compr' seqNums)

singleton :: (Ord i) => Dot i -> CausalContext i
singleton d = insert d empty

-- Ensures actors are always in compressed
insert :: (Ord i) => Dot i -> CausalContext i -> CausalContext i
insert dot@(Dot actor sequence) (CausalContext cc) =
  CausalContext $
  Map.alter
  (\case Nothing ->
           Just . compressI $ (-1, IntSet.singleton sequence)
         Just (current, ds) ->
           case compare sequence (current + 1) of
             EQ -> Just . compressI $ (sequence, ds)
             GT -> Just (current, IntSet.insert sequence ds)
             LT -> Nothing)
  actor
  cc

lookup :: (Ord i) => i -> CausalContext i -> Int
lookup i (CausalContext cc) =
  (fst $ Map.findWithDefault (-1,IntSet.empty) i cc)
  
next :: (Ord i) => i -> CausalContext i -> Dot i
next i (CausalContext cc) =
  Dot i ((fst $ Map.findWithDefault (-1,IntSet.empty) i cc) + 1)


fromDotSet :: (Ord i) => DotSet i -> CausalContext i
fromDotSet (DS.DotSet ds) =
  CausalContext . Map.map (compressI . (-1,)) $ ds

fromVV :: (Ord i) => VV i -> CausalContext i
fromVV (VV vv) =
  CausalContext $ (,IntSet.empty) <$> vv

unionDotSet :: (Ord i) => DotSet i -> CausalContext i -> CausalContext i
unionDotSet ds cc =
  cc \/ fromDotSet ds

-- test = insert (Dot 0 3) $ empty
-- ds = dots . insert (Dot 0 5) . insert (Dot 0 2) . insert (Dot 0 1) $ empty
-- cc = insert (Dot 0 4) . insert (Dot 0 1) $ empty

-- sa = DS.singleton (Dot 0 0)
-- sb = DS.empty
-- cca = singleton (Dot 0 0)
-- ccb = empty --insert (Dot 0 1) $ singleton (Dot 0 0)
-- --x = subtractCCfromDS ds cc
-- x = (sa /\ sb) \/ subtractCCfromDS sa ccb \/ subtractCCfromDS sb cca

causalVV :: (Ord i) => CausalContext i -> VV i
causalVV (CausalContext cc) =
  VV.fromMap $ Map.map fst cc

