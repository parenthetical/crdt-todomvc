{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE GADTs, ScopedTypeVariables #-}
{-# LANGUAGE DeriveAnyClass #-}

module Crdt.Ast where

import Data.Profunctor
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Semigroup
import Algebra.Lattice (JoinSemiLattice((\/)), BoundedJoinSemiLattice(bottom))
import Data.Bifunctor

data Clearable o = Clear | Do o
  deriving (Functor, Show, Read)

data Ast id o v where
  Sgr :: (Ord a, Semigroup a)
    => Ast id a (Option a)
  MonotoneSgr :: (Semigroup a, Ord a)
    => Ast id a (Option a)
  Lat :: (Ord a, BoundedJoinSemiLattice a)
    => Ast id a (WrappedLattice a)
  Clr :: (Show o, Read o, Show v, Read v)
    => Bool
    -> Ast id o v
    -> Ast id (Clearable o) v
  Dct :: (Ord k, Monoid v, Show k, Read k, Show v, Read v, Show o, Read o)
    => (v -> Bool)
    -> Ast id o v
    -> Ast id (k,o) (MonoidMap k v)
  Pair :: (Monoid v, Monoid v', Show o, Read o, Show o', Read o'
          , Show v, Read v, Show v', Read v')
    => Ast id o v
    -> Ast id o' v'
    -> Ast id (Either o o') (v,v')
  Lww :: (Show o, Read o, Show v, Read v)
    => Ast id o v
    -> Ast id o v
  IdDct :: (Ord id, Monoid v, Show o, Read o, Show v, Read v)
    => (v -> Bool)
    -> Ast id o v
    -> Ast id (Maybe id, o) (MonoidMap id v)
  Conc :: (Show o, Read o, Show v, Read v)
    => Ast id o v
    -> Ast id [o] v

data Crdt id o v where
  Crdt :: (Monoid v', Show o', Read o',
           Show v', Read v',
           Show id, Read id)
    => (v' -> o -> o')
    -> (v' -> v)
    -> Ast id o' v'
    -> Crdt id o v

instance (Show id, Read id) => Profunctor (Crdt id) where
  dimap = dimapv . const


class (Show id, Read id, Ord id) => CId id where

instance CId Int where
instance CId Integer where

dimapv :: ()
  => (v' -> o -> o') -> (v' -> v) -> Crdt id o' v' -> Crdt id o v
dimapv o v (Crdt o' v' p) =
  Crdt (\v''_ -> o' v''_ . o (v' v''_)) (v . v') p


semigroup  :: (Show id, Read id, Semigroup a, Show a, Read a, Ord a) => Crdt id a (Maybe a)
semigroup =
  rmap getOption $ Crdt (\_ a -> a) id Sgr

monotoneSemigroup :: (Show id, Read id, Semigroup a, Ord a, Show a, Read a) => Crdt id a (Maybe a)
monotoneSemigroup =
  rmap getOption $ Crdt (\_ a -> a) id MonotoneSgr

boundedLattice :: (BoundedJoinSemiLattice a, Show id, Read id, Show a, Read a, Ord a)
           => Crdt id a a
boundedLattice =
  Crdt (\_ a -> a) unwrapLattice Lat

clr :: Bool -> Crdt id o v -> Crdt id (Clearable o) v
clr always (Crdt o v (Clr always' p)) =
  Crdt
  (\v' op -> case op of Clear -> Clear; Do o' -> o v' o')
  v
  (Clr (always || always') p) -- Verify correctness of this
clr always (Crdt o v p) =
  Crdt
  (\v' op -> case op of
      Clear -> Clear
      Do o' -> Do $ (o v' o'))
  v
  (Clr always p)

dict :: (Ord k, Show k, Read k) =>
  (v -> Bool) -> Crdt id o v -> Crdt id (k,o) (Map k v)
dict f (Crdt o v p) =
  Crdt
  (\v' (k,o') ->
     ((k,) $ o (Map.findWithDefault mempty k . getMonoidMap $ v') o'))
  -- TODO for now duplicate the filter in v, but this shouldn't be necessary
  (Map.filter f . Map.map v . getMonoidMap)
  ((Dct (f . v) p))


iddict :: (Ord id, Show id, Read id)
     => (v -> Bool)
     -> Crdt id o v
     -> Crdt id (Maybe id, o) (Map id v)
iddict f (Crdt o v p) =
  Crdt
  (\v' (k,o') ->
     ((k,) $ o (case k of
                    Nothing -> mempty
                    Just k' -> Map.findWithDefault mempty k' . getMonoidMap $ v')
       o'))
  -- TODO for now duplicate the filter in v, but this shouldn't be necessary
  (Map.filter f . Map.map v . getMonoidMap)
  ((IdDct (f . v) p))
  
pair :: Crdt id o v
     -> Crdt id o' v'
     -> Crdt id (Either o o') (v,v')
pair (Crdt o v pl) (Crdt o' v' pr) =
  Crdt
  (\(vl,vr) op ->
      case op of
        Left a -> Left $ o vl a
        Right a -> Right $ o' vr a)
  (bimap v v')
  (Pair pl pr)

concurrent :: Crdt id o v -> Crdt id [o] v
concurrent (Crdt o v p) =
  (Crdt (\v' os' -> o v' <$> os') v (Conc p))
--  Crdt (\v' os -> concatMap (o v') os) v p

lww :: Crdt id o v -> Crdt id o v
lww (Crdt o v p) =
  Crdt o v (Lww p)

clrAlways ::(Show id, Read id) =>  Crdt id o v -> Crdt id o v
clrAlways = lmap Do . clr True

clrSome :: Crdt id o v -> Crdt id (Clearable o) v
clrSome = clr False

newtype MonoidMap k v = MonoidMap { getMonoidMap :: Map k v }
  deriving (Show,Read,Eq)

instance (Semigroup v, Ord k) => Semigroup (MonoidMap k v) where
  (<>) (MonoidMap a) (MonoidMap b) = MonoidMap $ Map.unionWith (<>) a b

instance (Ord k, Semigroup v) => Monoid (MonoidMap k v) where
  mempty = MonoidMap Map.empty
  mappend = (<>)

newtype WrappedLattice l = WrapLattice { unwrapLattice :: l }
  deriving (Show, Read, Ord, Eq)

instance Monoid x => Semigroup x where
  (<>) = mappend

instance JoinSemiLattice l => Semigroup (WrappedLattice l) where
  (<>) (WrapLattice a) (WrapLattice b) = WrapLattice (a \/ b)
instance (BoundedJoinSemiLattice l) => Monoid (WrappedLattice l) where
  mempty = WrapLattice bottom
  mappend = (<>)
