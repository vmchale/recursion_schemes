-- ----------------------------------------------------------------- [ Lib.idr ]
-- Module      : Data.Functor.Foldable
-- Description : 
-- --------------------------------------------------------------------- [ EOH ]
module Data.Functor.Foldable

import Prelude.List

%access export

-- | Fix-point data type for catamorphisms of various kinds
data Fix : (Type -> Type) -> Type where
  Fx : f (Fix f) -> Fix f

data ListF : Type -> Type -> Type where
  NilF : ListF _ _
  Cons : a -> b -> ListF a b

unfix : Fix f -> f (Fix f)
unfix (Fx x) = x

implementation Functor (ListF a) where
  map _ NilF       = NilF
  map f (Cons a b) = Cons a (f b)

-- | Ideally, we'd get something nicer like in Haskell, but we don't have that unfortunately :(
interface Functor f => Recursive (f : Type -> Type) (t : Type) where
  project : t -> f t

interface Functor f => Corecursive (f : Type -> Type) (t : Type) where
  embed : f t -> t

cata' : (Functor f, Recursive f a) => (f a -> a) -> a -> a
cata' f = c where c = f . map c . project

implementation Recursive (ListF a) (List a) where
  project [] = NilF
  project (x::xs) = Cons x xs

implementation Corecursive (ListF a) (List a) where
  embed NilF = []
  embed (Cons x xs) = x::xs

cata : Functor f => (f a -> a) -> Fix f -> a
cata f = f . map (cata f) . unfix

para : Functor f => (f (Fix f, a) -> a) -> Fix f -> a
para f = snd . cata (\x => (Fx $ map fst x, f x))

zygo : Functor f => (f b -> b) -> (f (b, a) -> a) -> Fix f -> a
zygo f g = snd . cata (\x => (f $ map fst x, g x))

mutu : Functor f => (f (b, a) -> b) -> (f (b, a) -> a) -> Fix f -> a
mutu f g = snd . cata (\x => (f x, g x))

hylo : Functor f => (f b -> b) -> (a -> f a) -> a -> b
hylo f g = h
  where h = f . map h . g
