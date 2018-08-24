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
import Crdt.Ast
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import Control.Monad.State (modify, get, runState, State)
import Data.Either (partitionEithers)
import Data.List.NonEmpty (NonEmpty((:|)), nonEmpty)
import Control.Monad (foldM)
import Data.Bool (bool)
import Algebra.Lattice (BoundedJoinSemiLattice())

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
  X :: (Show a, Read a)
    => { _doOp :: [o] -> (Maybe a) -> Ctr (Maybe a)
       , _query :: Maybe a -> v
       }
    -> X o v

compile :: Crdt Id o v
        -> Local o v
compile (Crdt o v ast) =
  case compileAst ast of
    X xo xv -> compile' o v xo xv

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
compileAst :: (Show o, Read o, Show v, Read v) => Ast' o v -> X o v
compileAst = \case
  Pair a a' ->
    compilePair (compileAst a) (compileAst a')
  Sgr ->
    compileSgr
  MonotoneSgr ->
    compileSgr
  Lat ->
    compileLat
  Dct _f a ->
    compileDct (compileAst a)
  Conc a ->
    compileConc (compileAst a)
  Clr always a ->
    compileClr always (compileAst a)
  Lww a ->
    -- Lww is equivalent to Clear when there is no concurrency.
    compileLww (compileAst (Clr True a))
  IdDct f a ->
    compileIdDct (compileAst (Dct f a))

compileIdDct :: X (Id,o) (MonoidMap Id v)
             -> X (Maybe Id, o) (MonoidMap Id v)
compileIdDct (X o v) =
  X (\ops s -> do
       ops' <- mapM (\(mid,op) ->
                       (,op) <$> (maybe (modify (+1) >> get) return mid))
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
  (maybe
   (v Nothing, v' Nothing)
   (\(l,r) -> (v l, v' r)))

compileSgr :: (Semigroup a, Show a, Read a)
           => X a (Option a)
compileSgr =
  X
  (\as ->
     return
     . maybe
     (sconcat <$> nonEmpty as)
     (\a' -> Just . sconcat $ (a' :| as)))
  Option

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
  (maybe mempty id)


compileDct :: (Ord k, Read k, Show k)
           => X o v
           -> X (k,o) (MonoidMap k v)
compileDct (X o v) =
  X
  (\ops s -> do
     foldM (\s' (k, ops') ->
             case s' of
               Nothing -> do
                 -- TODO empty map -> Nothing
                 mv <- o ops' Nothing
                 return $ case mv of
                   Nothing -> Nothing
                   Just v' -> Just . Map.singleton k $ v'
               Just m -> do
                 mv <- o ops' . Map.lookup k $ m
                 return $ case mv of
                   Nothing ->
                     Just $ Map.delete k m
                   Just v' ->
                     Just $ Map.insert k v' m)
       s
     . Map.toList
     . Map.unionsWith (++)
     . map (Map.map (:[]) . uncurry Map.singleton)
     $ ops)
  (MonoidMap . maybe Map.empty (fmap (v . Just)))

compileConc :: ()
            => X o v
            -> X [o] v
compileConc (X o v) =
  X
  (\ops s -> o (concat ops) s)
  v

compileClr :: ()
           => Bool
           -> X o v
           -> X (Clearable o) v
compileClr always (X o v) =
  X
  (\ops s ->
     let dos = mapMaybe (\case Clear -> Nothing; Do a -> Just a) ops
     in o dos (bool s Nothing
               $ (always || any (\case Clear -> True; _ -> False) ops)))
  v
