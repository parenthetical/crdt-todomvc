{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Crdt.Dot.VV where

import Algebra.Lattice (JoinSemiLattice((\/)), BoundedJoinSemiLattice(bottom)
                       , MeetSemiLattice ((/\)), BoundedMeetSemiLattice(top)
                       )
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import GHC.Generics (Generic)
import Data.Serialize
import Crdt.Dot (Dot(..))
import Crdt.Decomposable
import qualified Data.List as List

newtype VV i = VV (Map i Int)
  deriving (Eq,Ord,Show,Read,Generic)

instance (Ord i,Serialize i) => Serialize (VV i)

instance (Ord i) => JoinSemiLattice (VV i) where
  (\/) (VV a) (VV b) = VV $
    Map.unionWith max a b
instance (Ord i) => MeetSemiLattice (VV i) where
  (/\) (VV a') (VV b') = VV $
    Map.mapMaybe id
    $ Map.intersectionWith (\a b -> Just $ min a b) a' b'

instance (Ord i) =>
  BoundedJoinSemiLattice (VV i) where
  bottom = start

instance (Ord i) =>
  BoundedMeetSemiLattice (VV i) where
  top = start

instance (Ord i) => Decomposable (VV i) where
  decompositions (VV vv) =
    map (VV . (uncurry Map.singleton))
    $ Map.toList vv

singleton :: (Ord i) => (Dot i) -> VV i
singleton (Dot i s) = VV $ Map.singleton i s

includes :: (Ord i) => VV i -> VV i -> Bool
includes (VV b) (VV a) =
  let allKeys = Set.toList (Map.keysSet a \/ Map.keysSet b)
  in (all (\k -> Map.findWithDefault 0 k a <= Map.findWithDefault 0 k b)
       $ allKeys)


before :: (Ord i) => VV i -> VV i -> Bool
before (VV a) (VV b) =
  let allKeys = Set.toList (Map.keysSet a \/ Map.keysSet b)
  in (all (\k -> Map.findWithDefault 0 k a <= Map.findWithDefault 0 k b)
       $ allKeys)
     && (any (\k -> Map.findWithDefault 0 k a < Map.findWithDefault 0 k b)
         $ allKeys)

after :: (Ord i) => VV i -> VV i -> Bool
after = flip before

concurrent :: (Ord i) => VV i -> VV i -> Bool
concurrent a b = not ((a `before` b) || (b `before` a))

start :: VV i
start = VV $ Map.empty

lookup :: (Ord i) => i -> VV i -> Int
lookup i (VV m) = Map.findWithDefault 0 i m

-- FIXME: Take into account s == 0?
member :: (Ord i) => Dot i -> VV i -> Bool
member (Dot i s) (VV m) =
  case Map.lookup i m of
    Nothing -> False
    Just s' -> s <= s'

increment :: (Ord i) => i -> VV i -> VV i
increment i (VV m) = VV $
  Map.insert i (Map.findWithDefault 0 i m + 1) m

fromMap :: (Ord i) => Map i Int -> VV i
fromMap = VV

toMap :: (Ord i) => VV i -> Map i Int
toMap (VV vv) = vv

update :: (Ord i) => i -> Int -> VV i -> VV i
update i s (VV m) = VV $
  Map.insertWith max i s m

updateDot :: (Ord i) => Dot i -> VV i -> VV i
updateDot (Dot i s) (VV m) = VV $
  Map.insertWith max i s m

toDots :: (Ord i) => VV i -> [Dot i]
toDots (VV vv) = map (uncurry Dot) . Map.toList $ vv

fromDots :: (Ord i) => [Dot i] -> VV i
fromDots = List.foldl' (flip updateDot) start

delete :: (Ord i) => i -> VV i -> VV i
delete i (VV vv) = VV $ Map.delete i vv
