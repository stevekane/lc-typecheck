{-# LANGUAGE RankNTypes #-}

module StackFun (
  StackFun(..), 
  stackFun, 
  (⊗),
) where

{-
In Conal Elliot's papers he makes the following argument:

A program written in some typed lambda calculus can be modeled in some vocabulary
from category theory by introducing enough structure to the category to match the 
expressiveness of the terms in the lambda calculus. 

The primary motivation for doing this is to eliminate free variables and to represent
the original program (in a calculus) as an expression in an algebra. This algebra
then can be interpreted in any setting that is homomorphic to the original program.

Homomorphisms are functions that carry members of one algebraic structure to members
of another algebraic structure. In this setting, we are saying that all categorical
morphisms defined in the Category encoding the original program must have meanings
in the new settings that preserve homomorphism.

Homomorphism is a function between elements of two algebraic structures that preserves
the structure of under a set of operations / morphisms defined in the structure.

For example, if we have a Group G with * and a Group H with + then the homomorphism f
says that x * y = z => f x + f y = f z. This means that it is entirely possible that there
is no such homomorphism between two structures.

∃z ∈ G.∀x y ∈ G. z = x * y

f:G -> H
  x |-> f(x)
  y |-> f(y)
  z |-> f(z)

We'd like the operation * in group G to behave the same as the operation + in group H:

  x * y = z => f(x) + f(y) = f(z)

So we begin the process of defining a homomorphism that preserves the structure of 
an operation by declaring what must be true:

Let's pick a really stupid example: We'd like to carry all programs of the form:

  1 * 2

to the Group H where the operator is basically trivial and it says that all elements
are a pair of a number and the character 'f': (N, 'f') the group action will have the same
name (though it has a different meaning)

in Group H we say that (a,c) * (b,c) = (a*b,c)

instance Group G where
  l * r = l * r

instance Group H where
  l * r = (fst l * fst r, 'f')

f x = (x,'f')

f x * f y = f (x * y)
(x, 'f') * (y, 'f') = (x * y, 'f')

The homomorphism exists if the rule above is satisfied for some f:

  f x * f y = f (x * y)

This is what must be true 
-}

import Prelude hiding (id, (.))
import Data.Bifunctor (bimap)
import Control.Category (Category(..))

sfirst :: (a -> b) -> forall z.((a,z) -> (b,z))
sfirst f (a,z) = (f a, z)

newtype StackFun a b = SF (forall z.((a,z) -> (b,z)))

stackFun:: (a -> b) -> StackFun a b
stackFun f = SF (sfirst f)

class Category k => AssociativeCategory k where
  rassoc :: k ((a,b),c) (a,(b,c))
  lassoc :: k (a,(b,c)) ((a,b),c)

class Category k => BraidedCategory k where
  swap :: k (a,b) (b,a)

class Category k => MonoidalCategory k where
  (⊗) :: k a c -> k b d -> k (a,b) (c,d)
  first :: k a c -> k (a,b) (c,b)
  second :: k b d -> k (a,b) (a,d)

instance AssociativeCategory (->) where
  rassoc ((a,b),c) = (a,(b,c))
  lassoc (a,(b,c)) = ((a,b),c)

instance BraidedCategory (->) where
  swap (a,b) = (b,a)

instance MonoidalCategory (->) where
  first f (a,b) = (f a,b)
  second g = swap . first g . swap
  f ⊗ g = bimap f g

instance Category StackFun where
  id = SF id
  SF g . SF f = SF (g . f) 

instance AssociativeCategory StackFun where
  rassoc = stackFun rassoc
  lassoc = stackFun lassoc

instance BraidedCategory StackFun where
  swap = stackFun swap

instance MonoidalCategory StackFun where
  first (SF f) = SF (lassoc . f . rassoc)
  second g = swap . first g . swap
  f ⊗ g = first f . second g