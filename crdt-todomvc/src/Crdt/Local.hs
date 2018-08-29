{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE GADTs, ScopedTypeVariables, DeriveGeneric #-}

module Crdt.Local (Id,Local(..),compile) where

import Data.Semigroup
import Crdt.Ast (Ast(..), Crdt(..),Clearable(..),MonoidMap(..),WrappedLattice(..))
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import Control.Monad.State (modify, get, runState, State)
import Data.Either (partitionEithers)
import Data.List.NonEmpty (NonEmpty((:|)), nonEmpty)
import Control.Monad (foldM)
import Data.Bool (bool)
import Algebra.Lattice (BoundedJoinSemiLattice())
import Data.Bifunctor
import Control.Monad (join)
import Debug.Trace

type Id = Integer

type Ctr a = (State Id) a

data Local o v where
  Local ::
    { localInitState :: String
    , apply :: String -> o -> String
    , eval :: String -> v
    }
    -> Local o v

data X o v where
  X :: (Show a, Read a, Monoid v)
    => { _doOp :: [o] -> (Maybe a) -> Ctr (Maybe a)
       , _query :: Maybe a -> Maybe v
       }
    -> X o v

compile :: Crdt Id o v
        -> Local o v
compile (Crdt o v ast) =
  case compileAst (/= mempty) ast of
    X xo xv -> compile' o v xo (maybe mempty id . xv)

compile' :: forall o v o' v' a.
             (Show a, Read a)
          => (v' -> o -> o')
          -> (v' -> v)
          -> ([o'] -> (Maybe a) -> Ctr (Maybe a))
          -> (Maybe a -> v')
          -> Local o v
compile' o v xo xv =
  Local
  (show ((Nothing, 0) :: (Maybe a,Id)))
  (\state op ->
    let (s,ctr) = read state :: (Maybe a,Id)
        (s',ctr') = runState (xo [o (xv $ s) op] s) ctr
    in show (s', ctr'))
  (\state ->
      v . xv . fst $ (read state :: (Maybe a, Id)))

type Ast' = Ast Id

-- TODO use stability
compileAst :: (Show o, Read o, Eq o)
  => (v -> Bool) -> Ast' o v -> X o v
compileAst f ast = case ast of
  Pair a a' ->
    compilePair (compileAst (const True) a) (compileAst (const True) a')
  Sgr -> compileSgr
  MonotoneSgr -> compileSgr
  Lat -> compileLat
  Dct a -> compileDct (compileAst (const True) a)
  Conc a -> compileConc (compileAst f a)
  Clr always a -> compileClr f always (compileAst (const True) a)
  -- Lww is equivalent to Clear when there is no concurrency.
  Lww a -> compileLww (compileAst f (Clr True a))
  MapId f' a -> compileMapId f' (compileAst f a)
  Filter f' a -> compileFilter f' (compileAst f' a)

compileFilter :: (v -> Bool)
              -> X o v
              -> X o v
compileFilter f (X o v) =
  X
  o
  (join
   . fmap (\v' -> if f v'
                  then Just v'
                  else Nothing)
    . v)

compileMapId :: (Id -> o -> o')
             -> X o' v'
             -> X o v'
compileMapId f (X o v) =
  X (\ops s -> do
        ops' <- mapM (\op -> do
                          i <- modify (+1) >> get
                          return $ f i op)
                 ops
        o ops' s)
  v


compileLww :: X (Clearable o) v -> X o v
compileLww (X o v) =
  X (o . fmap Do) v

compilePair :: X o v
            -> X o' v'
            -> X (Either o o') (v,v')
compilePair (X o v) (X o' v') =
  X
  (\ops s ->
     -- TODO Make shorter and less repetitive.
     let (lops, rops) = partitionEithers ops
     in case s of
       Nothing -> do
         l <- o lops Nothing
         r <- o' rops Nothing
         return $ case (l,r) of
           (Nothing,Nothing) ->
             Nothing
           _ -> Just (l,r)
       Just (l,r) -> do
         l' <- o lops l
         r' <- o' rops r
         return $ case (l',r') of
           (Nothing,Nothing) ->
             Nothing
           _ -> Just $ (l',r'))
  (join
   . fmap (\(l,r) ->
             case (v l, v' r) of
               (Nothing,Nothing) -> Nothing
               x ->
                 Just . bimap (maybe mempty id) (maybe mempty id) $ x))

compileSgr :: (Semigroup a, Show a, Read a)
           => X a (Option a)
compileSgr =
  X
  (\as ->
     return
     . maybe
     (sconcat <$> nonEmpty as)
     (\a' -> Just . sconcat $ (a' :| as)))
  (fmap (Option . Just))

compileLat :: (BoundedJoinSemiLattice a, Show a, Read a)
           => X a (WrappedLattice a)
compileLat =
  X
  (\as ->
     let as' = WrapLattice <$> as
     in return
        . maybe
        (sconcat <$> nonEmpty as')
        (\a' -> Just . sconcat $ (a' :| as')))
  id


compileDct :: (Ord k, Show k, Read k)
           => X o v
           -> X (k,o) (MonoidMap k v)
compileDct (X o v) =
  X
  (\ops s -> do
     foldM (\s' (k, ops') ->
             case s' of
               Nothing -> do
                 mv <- o ops' Nothing
                 return $ case mv of
                   Nothing -> Nothing
                   Just v' -> Just . Map.singleton k $ v'
               Just m -> do
                 mv <- o ops' . Map.lookup k $ m
                 return $ case mv of
                   Nothing ->
                     let m' = Map.delete k m
                     in if Map.null m'
                        then Nothing
                        else Just m'
                   Just v' ->
                     Just $ Map.insert k v' m)
       s
     . Map.toList
     . Map.unionsWith (++)
     . map (Map.map (:[]) . uncurry Map.singleton)
     $ ops)
  (fmap (MonoidMap . (Map.mapMaybe (v . Just))))

compileConc :: ()
            => X o v
            -> X [o] v
compileConc (X o v) =
  X
  (\ops s -> o (concat ops) s)
  v

compileClr :: ()
           => (v -> Bool)
           -> Bool
           -> X o v
           -> X (Clearable o) v
compileClr f always (X o v) =
  X
  (\ops s -> do
     let dos = mapMaybe (\case Clear -> Nothing; Do a -> Just a) ops
         hasClear = always || any (\case Clear -> True; _ -> False) ops
     mv <- o dos . bool s Nothing $ hasClear
     return
       . join
       . fmap (\v' ->
               if always
                  && (not . f $ (maybe mempty id . v . Just $ v'))
               then Nothing
               else mv)
       $ mv)
  v
