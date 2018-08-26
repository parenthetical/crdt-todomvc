{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE GADTs, ScopedTypeVariables #-}

module Crdt
  ( constVal
  , constValUnsafe
  , eoflag
  , edoflag
  , dwflag
  , ewflag
  , gset
  , twopset
  , gcounter
  , pair
  , dict
  , iddict
  , mutableSequence
  , concurrent
  , clrSome
  , clrAlways
  , setOncePickOne
  , pncounter
  , lwwreg
  , lwwdwflag
  , resettableCounter
  , mvregister
  , causallwwreg
  , MapOp(..)
  , addRemoveMap
  , set
  , gset'
  , twopset'
  , awset
  , rwset
  , lwwawset
  , lwwrwset
  , fltr
  , Crdt
  , SeqOp(..)
  , SeqIdxOp(..)
  , Clearable(..)
  , SetOp(..)
  )
where

import Crdt.Ast

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Profunctor
import Data.Semigroup
import Algebra.Lattice (JoinSemiLattice((\/)), BoundedJoinSemiLattice(bottom))
-- import Data.Bifunctor (bimap)
import Numeric.Natural
import Data.Bool (bool)
import Data.Maybe (catMaybes, mapMaybe)
import qualified Data.Graph as G





-- TRIVIAL CRDTs

setOncePickOne :: (CId id, Show a, Read a, Ord a) => Crdt id a (Maybe a)
setOncePickOne =
  -- TODO somehow error out if already set?
  dimap First (fmap getFirst) $ monotoneSemigroup


data Const a = ConstUnset | Const a | ConstMismatch
  deriving (Show,Read,Eq,Ord)

instance (Eq a) => JoinSemiLattice (Const a) where
  (\/) ConstUnset b = b
  (\/) a ConstUnset = a
  (\/) _ ConstMismatch = ConstMismatch
  (\/) ConstMismatch _ = ConstMismatch
  (\/) (Const a) (Const b) =
    if a == b
    then Const a
    else ConstMismatch

instance (JoinSemiLattice (Const a)) =>
  BoundedJoinSemiLattice (Const a) where
  bottom = ConstUnset

constVal :: (CId id, Show a, Read a, Ord a) => Crdt id a (Const a)
constVal =
  lmap Const $ boundedLattice

-- Set once, error if set twice or evaluated without being set.
constValUnsafe :: (CId id, Show a, Read a, Ord a)
  => Crdt id a a
constValUnsafe =
  rmap (\(Const a) -> a) constVal







-- SIMPLE AGGREGATION

-- FIXME this won't actually compile to the correct thing, it should
-- be an anonymous CRDT, i.e. using "boundedLattice".
eoflag :: (CId id) => Crdt id Bool Bool
eoflag =
  dimap (bool [] [()]) (maybe False (const True))
  . concurrent
  $ monotoneSemigroup

-- TODO doublecheck this as well
edoflag :: (CId id) => Crdt id Bool Bool
edoflag = dimap All (maybe False getAll) $ semigroup

gset :: (Ord a, Show a, Read a, CId id) => Crdt id (Set a) (Set a)
gset = boundedLattice

-- Doesn't check "can't remove before known add" invariant
twopset :: (Ord a, Show a, Read a, CId id) => Crdt id (SetOp a) (Set a)
twopset = dimap (\case Add a -> (Set.singleton a, Set.empty)
                       Rem a -> (Set.empty, Set.singleton a))
          (uncurry Set.difference)
          boundedLattice

gcounter :: (CId id) => Crdt id Natural Natural
gcounter = dimap Sum (maybe 0 getSum) $ monotoneSemigroup

pncounter :: (CId id) => Crdt id Int Int
pncounter = dimap Sum (maybe 0 getSum) $ semigroup







-- LAST WRITER WINS

lwwreg :: (CId id, Ord a, Show a, Read a)
  => Crdt id a (Maybe a)
lwwreg = lww setOncePickOne

lwwewflag :: (CId id) => Crdt id Bool Bool
lwwewflag = lww eoflag

lwwdwflag :: (CId id) => Crdt id Bool Bool
lwwdwflag = lww edoflag








-- CRDTs WITH CLEAR / CAUSAL CRDTS

ewflag :: (CId id) => Crdt id Bool Bool
ewflag = clrAlways eoflag

dwflag :: (CId id) => Crdt id Bool Bool
dwflag = clrAlways edoflag

resettableCounter :: (CId id) => Crdt id (Clearable Int) Int
resettableCounter = clrSome pncounter

mvregister :: (Ord a, Show a, Read a, CId id) => Crdt id a (Set a)
mvregister = lmap Set.singleton $ clrAlways gset

causallwwreg :: (Ord a, Show a, Read a, CId id) => Crdt id a (Maybe a)
causallwwreg = clrAlways lwwreg







-- ADD-REMOVE MAP

data MapOp k o = Apply k o | Del k
addRemoveMap :: (Ord k, CId id, Show k, Read k)
  => Crdt id (Clearable o) v -> Crdt id (MapOp k o) (Map k v)
addRemoveMap =
  lmap (\case Apply k o -> (k, Do o); Del k -> (k, Clear))
  . dict






-- SETS

data SetOp a = Add a | Rem a

set :: (Ord a, Show a, Read a, CId id) => Crdt id Bool Bool -> Crdt id (SetOp a) (Set a)
set flag =
  dimap
  (\case Add a -> (a,True); Rem a -> (a,False))
  Map.keysSet
  (dict (fltr id flag))

gset' :: (Ord a, Show a, Read a, CId id) => Crdt id a (Set a)
gset' = lmap Add (set eoflag)

twopset' :: (Ord a, Show a, Read a, CId id) => Crdt id (SetOp a) (Set a)
twopset' = set edoflag

awset :: (Ord a, Show a, Read a, CId id) => Crdt id (SetOp a) (Set a)
awset = set ewflag

rwset :: (Ord a, Show a, Read a, CId id) => Crdt id (SetOp a) (Set a)
rwset = set dwflag

lwwawset :: (Ord a, Show a, Read a, CId id) => Crdt id (SetOp a) (Set a)
lwwawset = set lwwewflag

lwwrwset :: (Ord a, Show a, Read a, CId id) => Crdt id (SetOp a) (Set a)
lwwrwset = set lwwdwflag





-- SEQUENCES

data SeqOp o = SeqIdx Int (SeqIdxOp o) | SeqReplace [o]
  deriving (Eq,Ord,Show,Read)

data SeqIdxOp o = SeqIns o | SeqApply o | SeqDel
  deriving (Eq,Ord,Show,Read)

data SeqVtx i = SeqStart | SeqEnd | SeqVtx i
  deriving (Eq,Ord,Show,Read)


mutableSequence :: (CId id)
  => Crdt id o v
  -> Crdt id (SeqOp o) [v]
mutableSequence c =
  -- Lookup index and transform operation
  dimapv (\s o' ->
           case o' of
             SeqReplace os ->
               -- TODO: Implement replace/insertion of sequences
               -- without hack relying on ordered concurrent
               -- identifiers?
               [ Clear ]
               <>
               map (\o ->
                      Do (Nothing, [ Left [ Left Nothing
                                          , Right Nothing
                                          ]
                                   , Right [ Left True
                                           , Right o
                                           ]
                                   ]))
               (reverse os)
             SeqIdx idx o ->
               (:[]) . Do $ case o of
                 SeqDel ->
                   let (i, _) = s !! idx -- FIXME unsafe
                   in (Just i, [Right [Left False]])
                 SeqIns o'' ->
                   let leftIdx = if idx == -1
                                 then Nothing
                                 else Just $ fst (s !! idx)
                       rightIdx = if (idx + 1) >= length s
                                  then Nothing
                                  else Just $ fst (s !! (idx + 1))
                   in (Nothing, [ Left [ (Left leftIdx)
                                       , (Right rightIdx) ]
                                , Right [ (Left True)
                                        , (Right o'') ]
                                ])
                 SeqApply o'' ->
                   let (i,_) = s !! idx
                   in (Just i, [Right [Right o'']]))
  (map snd)
  . rmap (mapMaybe (\(i,notDeleted,a) ->
                       if notDeleted
                       then Just (i,a)
                       else Nothing)
          . topsort)
  $ sequence' c

sequence' :: (CId id)
  => Crdt id o v
  -> Crdt id [Clearable
              ( Maybe id
              , [(Either [(Either (Maybe id) (Maybe id))] [(Either Bool o)])])]
             ( Map id ( (Maybe id, Maybe id)
                      , (Bool, v)))
sequence' c =
  concurrent
  . clrSome
  . iddict -- FIXME make something like this work for
           -- filter:(\(_, (deleted, _)) -> not deleted).
  . concurrent
  $ (pair (concurrent $ pair constValUnsafe constValUnsafe) (concurrent $ pair edoflag c))

topsort :: (Ord id)
  => Map id ((Maybe id, Maybe id), (Bool, a))
  -> [(id,Bool,a)]
topsort m =
  let (g,lookupVtx,_) = G.graphFromEdges . seqEdges $ m
  in catMaybes
     . map (\(i,_,_) -> i)
     . map lookupVtx
     . G.topSort $ g

seqEdges :: (Ord id)
  => Map id ((Maybe id, Maybe id), (Bool, a))
  -> [(Maybe (id,Bool,a), SeqVtx id, [SeqVtx id])]
seqEdges m =
  let vertices inId =
        (map SeqVtx
         . Map.keys
         . Map.filter (\ ((inId',_),_) ->
                          inId' == inId)
         $ m)
      idEdges =
        map (\(i,((_inId,outId),(deleted,a))) ->
                     ( Just (i,deleted,a)
                     , SeqVtx i
                     , (case outId of
                          Nothing -> SeqEnd
                          Just i' -> SeqVtx i')
                       : vertices (Just i)))
        . Map.toList
        $ m
      start = (Nothing, SeqStart, vertices Nothing)
      end = (Nothing, SeqEnd, [])
  in start:end:idEdges





-- INSTANCES

instance (JoinSemiLattice a) => JoinSemiLattice (Maybe a) where
  Just a \/ Just b = Just (a \/ b)
  Just a \/ Nothing = Just a
  Nothing \/ Just b = Just b
  Nothing \/ Nothing = Nothing

instance (BoundedJoinSemiLattice a) => BoundedJoinSemiLattice (Maybe a) where
  bottom = Nothing

-- TODO contSeq
-- TODO borrow counter
-- addRemovePO :: TODO
-- RGA TODO
-- add-only DAG TODO
