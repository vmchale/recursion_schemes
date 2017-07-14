-- ----------------------------------------------------------------- [ Lib.idr ]
-- Module      : Data.Functor.Foldable.Instances
-- Description : Instances of 'Recursive' and 'Corecursive' for various
--               things.
-- --------------------------------------------------------------------- [ EOH ]
module Data.Functor.Foldable.Instances

import Data.Functor.Foldable

%access public export

data StreamF : Type -> Type -> Type where
  NilStream : StreamF _ _
  ConsStream : a -> b -> StreamF a b

data Stream' : Type -> Type where
  StreamFx : (Fix (StreamF a)) -> Stream' (Fix (StreamF a))

data ListF : Type -> Type -> Type where
  NilF : ListF _ _
  Cons : a -> b -> ListF a b

data LFix : Type -> Type where
  ListFx : Fix (ListF a) -> LFix (Fix (ListF a))

implementation Functor (StreamF a) where
  map _ NilStream       = NilStream
  map f (ConsStream a b) = ConsStream a (f b)

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

implementation Recursive (StreamF a) (Stream a) where
  project (x::xs) = ConsStream x xs

implementation Corecursive (StreamF a) (Stream a) where
  embed (ConsStream x xs) = x::xs
