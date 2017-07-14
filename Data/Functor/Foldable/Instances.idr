-- ----------------------------------------------------------------- [ Lib.idr ]
-- Module      : Data.Functor.Foldable.Instances
-- Description : Instances of 'Recursive' and 'Corecursive' for various
--               things.
-- --------------------------------------------------------------------- [ EOH ]
module Data.Functor.Foldable.Instances

import Data.Functor.Foldable

%access export

data ListF : Type -> Type -> Type where
  NilF : ListF _ _
  Cons : a -> b -> ListF a b

data List' : Type -> Type where
  ListFx : (Fix (ListF a)) -> List' (Fix (ListF a))

implementation Functor (ListF a) where
  map _ NilF       = NilF
  map f (Cons a b) = Cons a (f b)

interface Functor f => Recursive (f : Type -> Type) (t : Type) where
  project : t -> f t

interface Functor f => Corecursive (f : Type -> Type) (t : Type) where
  embed : f t -> t

implementation Recursive (ListF a) (List a) where
  project [] = NilF
  project (x::xs) = Cons x xs

implementation Corecursive (ListF a) (List a) where
  embed NilF = []
  embed (Cons x xs) = x::xs
