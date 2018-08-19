{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE GADTs, ScopedTypeVariables, DeriveGeneric #-}

module Crdt.Delta (Id,Local(..),compileLocal) where

import qualified Data.Map as Map
import Data.Map (Map)
--import qualified Data.Map.Merge.Lazy as Map
import Data.Semigroup
import qualified Data.IntMap.Lazy as IntMap
import Data.IntMap.Lazy (IntMap)
import Control.Monad.State.Strict (modify, get, runState, State)
import qualified Data.List as List
import Data.Bifunctor
import qualified Data.Set as Set
import qualified Data.IntSet as IntSet
import Data.IntSet (IntSet)
import Algebra.Lattice (JoinSemiLattice((\/)), joins, BoundedJoinSemiLattice())

import Crdt.Ast

newtype Id i = Id (i,Int)
  deriving (Show,Read,Ord,Eq)

instance CId (Id Int) where

type Ctr a = (State (Int,Int)) a

data Local o v where
  Local ::
    { localInitState :: String
    , apply :: String -> o -> String
    , eval :: String -> v
    }
    -> Local o v

compileLocal :: Crdt (Id Int) o v -> Local o v
compileLocal (Crdt o v p) =
  let Comp{bottom,mutator,query,merge} = compileAst p
  in Local
     { localInitState = show (((causalBottom bottom), (-1,-1)) :: ((String, CausalContext Int), (Int,Int)))
     , apply = \state op ->
         let (crdtState@(df,_cc), (ctr,cci)) =
               read state :: ((String, CausalContext Int), (Int,Int))
             ctr' = ctr + 1
             (d,(ctr'',cci')) =
               runState (mutator ctr' 0 (o (query df) op) (causalBottom df)) (ctr',cci)
         in show (d `merge` crdtState, (ctr'',cci'))
     , eval = \state ->
         let ((df,_cc), (_ctr,_cci)) =
               read state :: ((String, CausalContext Int), (Int, Int))
         in v . query $ df
     }

-- TODO rename Comp

-- FIXME merge -> mergeDS
data Comp t i o v where
  Comp ::
       { mutator :: t
                 -> i
                 -> o
                 -> (String, CausalContext i)
                 -> Ctr (String, CausalContext i)
       , merge :: (String, CausalContext i)
               -> (String, CausalContext i)
               -> (String, CausalContext i)
       , query :: String -> v
       , bottom :: String
       , dsDots :: String -> DotSet i
       , decompositions :: String -> [String]
       }
       -> Comp t i o v

compileAst :: (Show i, Read i, Ord i, Ord t, Show o, Read o, Show v, Read v, Read t, Show t)
           => Ast (Id i) o v
           -> Comp t i o v
compileAst p =
  case p of
    Sgr -> compileSgr
    MonotoneSgr -> compileSgr
    Lat -> compileLat
    Clr always x -> compileClr always x
    Dct f x -> compileDct f x
    Pair a b -> compilePair a b
    Lww x -> compileLww x
    IdDct f x -> compileIdDct f x
    Conc x -> compileConc x

type DotFun i a = Map i (IntMap a)
type DotSet i = Map i (IntSet)
type CausalContext i = Map i (Int, IntSet)

causalBottom :: (Ord i) => String -> (String, CausalContext i)
causalBottom dotStore = (dotStore, Map.empty)


compileSgr :: forall t i a. (Show i, Read i, Ord i, Ord a, Semigroup a, Show a, Read a)
  => Comp t i a (Option a)
compileSgr =
  Comp { mutator =
         \_t i a (_str,_cc) -> do
           (_,s) <- modify (second (+1)) >> get
           return
              ( show $ (Map.singleton i (IntMap.singleton s a))
              , Map.singleton i (-1,(IntSet.singleton s))
              )
       , query =
         (\str ->
            let df = read str :: DotFun i a
            in Map.foldMapWithKey
               (\_k -> IntMap.foldMapWithKey (\_k -> Option . Just))
               $ df)
       , bottom = show (Map.empty :: DotFun i a)
       , merge = \(str,cc) (str',cc') ->
           let df = read str :: DotFun i a
               df' = read str' :: DotFun i a
               dfIntersect =
                 Map.filter (not . IntMap.null)
                 $ Map.intersectionWith (IntMap.intersection) df df'
               dfUnion a b =
                 Map.unionWith (IntMap.union) a b
               differenceCC =
                 -- FIXME: this needs IntMap.restrictKeys but it doesn't exist
                 Map.differenceWith
                   (\dots (compr, dots') ->
                      let res = (snd $ IntMap.split compr dots)
                                IntMap.\\
                                (IntMap.fromSet (const ()) dots')
                      in if IntMap.null res
                         then Nothing
                         else Just res)
               (df'',cc'') =
                 ( dfIntersect
                   `dfUnion` (differenceCC df cc')
                   `dfUnion` (differenceCC df' cc)
                 , mergeCC cc cc'
                 )
           in (show df'', cc'')
       , dsDots = \str ->
           Map.map IntMap.keysSet
           $ (read str :: DotFun i a)
       , decompositions = \str ->
           map (show :: DotFun i a -> String)
         . concatMap (\(i,svs) ->
                        Prelude.map
                        (Map.singleton i . (uncurry IntMap.singleton))
                        (IntMap.toList svs))
         . Map.toList
         $ (read str :: DotFun i a)
       }

compileLat :: forall t i a. (Show i, Read i, Ord i, Ord a, BoundedJoinSemiLattice a, Show a, Read a, Ord t, Read t, Show t)
  => Comp t i a (WrappedLattice a)
compileLat =
  let comp@Comp{mutator,query} =
        compileAst Sgr :: Comp t i (WrappedLattice a) (Option (WrappedLattice a))
  in comp
     { mutator = \t i -> mutator t i . WrapLattice
     , query = option mempty id . query
     }

ccFromDS :: (Ord i) => DotSet i -> CausalContext i
ccFromDS ds = Map.map (compressI . (-1,)) $ ds

compileClr :: (Ord i, Ord t, Read i, Show i, Read o, Show o, Read v, Show v, Read t, Show t)
  => Bool
  -> Ast (Id i) o v -> Comp t i (Clearable o) v
compileClr always a =
  let comp@Comp{mutator,bottom,dsDots,merge} = compileAst a
  in comp
     { mutator = \t i o' (str,cc) ->
        let clear = (bottom, (ccFromDS $ dsDots str))
        in -- If clear always, join the Do _ and Clear mutators
         case o' of
           Clear ->
             return clear
           Do o'' -> do
             delta <- (mutator t i o'' (str,cc))
             return (case always of
                       True -> merge clear delta
                       False -> delta)
     }

compilePair :: (Ord i, Read o, Show o, Read o', Show o'
               , Read v, Show v, Read v', Show v'
               , Read i, Show i, Read t, Show t, Ord t)
  => Ast (Id i) o v -> Ast (Id i) o' v' -> Comp t i (Either o o') (v,v')
compilePair a b =
  let Comp{bottom=bottoma,mutator=mutatora,query=querya,merge=mergea,dsDots=dsDotsa,decompositions=decompositionsa} = compileAst a
      Comp{bottom=bottomb,mutator=mutatorb,query=queryb,merge=mergeb,dsDots=dsDotsb,decompositions=decompositionsb} = compileAst b
  in Comp
     { bottom = show (bottoma,bottomb)
     , mutator = \t i o (str,cc) ->
         let (stra, strb) = (read str :: (String, String))
         in case o of
           Left o' -> do
             (stra',cc') <- mutatora t i o' (stra,cc)
             return (show (stra', bottomb), cc')
           Right o' -> do
             (strb',cc') <- mutatorb t i o' (strb,cc)
             return (show (bottoma, strb'), cc')
     , merge = \(str,cc) (str',cc') ->
         let (stra,strb) = read str
             (stra',strb') = read str'
             (stra'',cca) = mergea (stra,cc) (stra',cc')
             (strb'',ccb) = mergeb (strb,cc) (strb',cc')
         in (show (stra'',strb''), cca `mergeCC` ccb)
     , query = \str ->
         let (stra,strb) = read str
         in (querya stra, queryb strb)
     , dsDots = \str ->
         let (stra,strb) = read str
         in dsDotsa stra \/ dsDotsb strb
     , decompositions = \str ->
         let (stra, strb) = read str
         in map (show :: (String, String) -> String)
            $ (((,bottomb) <$> decompositionsa stra)
               ++
               ((bottoma,) <$> decompositionsb strb))
     }

compileDct :: forall i o v k t.
  (Ord i, Ord k, Semigroup v, Show k, Read k, Show v, Read v, Ord t, Read t, Show t, Show i, Read i, Show o, Read o)
  => (v -> Bool) -> Ast (Id i) o v -> Comp t i (k,o) (MonoidMap k v)
compileDct f p =
  let Comp{mutator,query,merge,dsDots,bottom,decompositions} =
        compileAst p
  in Comp
     { bottom = show (Map.empty :: Map k String)
     , mutator = \t i (k,o) (str,cc) -> do
         let m = read str :: Map k String
         (v',cc') <-
               mutator t i o (Map.findWithDefault bottom k m, cc)
         return (show $ Map.singleton k v', cc')
     , merge = \(str,cc) (str',cc') ->
         let m = read str :: Map k String
             m' = read str' :: Map k String
             ks = Set.toList (Map.keysSet m `Set.union` Map.keysSet m')
             msccs =
               map (\k ->
                      let (m'',cc'') =
                            merge
                            (Map.findWithDefault bottom k m, cc)
                            (Map.findWithDefault bottom k m', cc')
                      in (Map.singleton k m'', cc''))
               ks
         in ( (show :: Map k String -> String)
              . Map.filter (/= bottom) . Map.unions . map fst $ msccs
            , joinsCC . map snd $ msccs
            )
       , query = \str ->
           let m = read str :: Map k String
           in MonoidMap . Map.filter f . Map.map query $ m
       , dsDots = \str ->
           let m = read str :: Map k String
           in joins . map dsDots . Map.elems $ m
       , decompositions = \str ->
           map (show :: Map k String -> String)
           . concatMap (\(k,v) -> Map.singleton k <$> decompositions v)
           . Map.toList
           $ (read str :: Map k String)
       }

-- FIXME cleaner re-use of Dct
compileIdDct :: forall i o v t.
  (Ord i, Monoid v, Show v, Read v, Ord t, Read t, Show t, Show i, Read i, Show o, Read o)
  => (v -> Bool) -> Ast (Id i) o v -> Comp t i (Maybe (Id i),o) (MonoidMap (Id i) v)
compileIdDct f p =
  let comp@Comp{mutator} =
        compileAst ((Dct f p) :: Ast (Id i) (Id i, o) (MonoidMap (Id i) v))
  in comp
     { mutator = \t i (mid,o) ccrdt ->
         case mid of
           Nothing -> do
             (count,_) <- modify (first (+1)) >> get
             mutator t i (Id (i,count), o) ccrdt
           Just id' ->
             mutator t i (id', o) ccrdt
     }

-- FIXME can we avoid storing entire CCrdt delta's?
-- FIXME cleaner re-use of DotFun
compileLww :: forall i t o v.
  (Ord i, Ord t, Read i, Show i, Read o, Show o, Read v, Show v, Read t, Show t)
  => Ast (Id i) o v -> Comp t i o v
compileLww x =
  let Comp{mutator,query,merge,bottom} =
        compileAst x
      comp@Comp{mutator=mutator',query=query'} =
        compileAst (Sgr :: Ast (Id i)
                           [(t, (String, CausalContext i))]
                           (Option [(t, (String, CausalContext i))]))
      getCCrdt str =
        case query' str of
          Option Nothing -> (causalBottom bottom)
          Option (Just es) ->
            let maxT = maximum . map fst $ es
            in foldl merge (causalBottom bottom)
               . map snd
               . filter ((== maxT) . fst)
               $ es
  in comp
     { mutator =
        \t i op (str,cc) -> do
          delta <- (mutator t i op (getCCrdt str))
          mutator' t i
            [(t, delta)]
            (str,cc)
     , query = query . fst . getCCrdt
     }

compileConc ::
  (Ord i, Ord t, Read i, Show i, Read o, Show o, Read v, Show v, Read t, Show t)
  => Ast (Id i) o v -> Comp t i [o] v
compileConc x =
  let comp@Comp{mutator,merge,bottom} =
        compileAst x
  in comp
     { mutator =
         \t i ops (str,cc) ->
           fmap (foldl merge (causalBottom bottom))
           . mapM (\op -> mutator t i op (str,cc))
           $ ops
     }

compressI :: (Int, IntSet) -> (Int, IntSet)
compressI (compr,seqNums) =
  let (_toDrop, seqNums') =
        List.span (<= compr) . IntSet.toAscList $ seqNums
      compr' = case takeWhile (uncurry (==)) $ zip [compr+1 ..] seqNums' of
        [] -> compr
        continuous -> (fst . last $ continuous)
  -- TODO: optimisable to use Nothing in case nothing changed.
  in (compr', snd $ IntSet.split compr' seqNums)

unionI :: (Int, IntSet) -> (Int, IntSet) -> (Int, IntSet)
unionI (a,as) (b,bs) =
  compressI $ (max a b, IntSet.union as bs)

mergeCC :: (Ord i) => CausalContext i -> CausalContext i -> CausalContext i
mergeCC = Map.unionWith unionI

joinsCC :: (Ord i) => [CausalContext i] -> CausalContext i
joinsCC = foldl mergeCC Map.empty
