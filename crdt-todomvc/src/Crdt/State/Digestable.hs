{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

module Crdt.State.Digestable where

import Data.Set as Set
import Data.List as List
import Algebra.Lattice (joins,joinLeq,JoinSemiLattice((\/)), BoundedJoinSemiLattice(bottom))
import GHC.Generics (Generic)
import Data.Serialize
import Crdt.Decomposable

data MaybeDigest digest crdt
  = DigestDigest digest
  | DigestDelta crdt
  deriving (Show,Read,Eq,Ord,Generic)

instance (Serialize crdt, Serialize digest) => Serialize (MaybeDigest crdt digest)

strictlyInflates :: (JoinSemiLattice crdt, Eq crdt) => crdt -> crdt -> Bool
strictlyInflates a b = not $ joinLeq a b

-- Join of the decompositions of s which inflate digest
minDelta :: (Decomposable crdt, Eq crdt, Digestable crdt digest)
  => crdt -> MaybeDigest digest crdt -> crdt
minDelta s digest =
  joins
  . List.filter (case digest of
                   (DigestDelta t) -> (`strictlyInflates` t)
                   (DigestDigest r) -> (`digestStrictlyInflates` r))
  $ decompositions s

class (BoundedJoinSemiLattice crdt, Eq crdt) =>
      Digestable crdt digest  | crdt -> digest where
  digestStrictlyInflates :: crdt -> digest -> Bool
  digest :: crdt -> MaybeDigest digest crdt
