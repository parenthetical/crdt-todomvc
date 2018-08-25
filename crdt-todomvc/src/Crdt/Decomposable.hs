module Crdt.Decomposable where

import Algebra.Lattice (BoundedJoinSemiLattice())

class (BoundedJoinSemiLattice a) => Decomposable a where
  decompositions :: a -> [a]
  decompositions a = [a]

