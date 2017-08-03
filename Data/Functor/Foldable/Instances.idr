-- ------------------------------------- [ Data.Functor.Foldable.Instances.idr ]
-- Module      : Data.Functor.Foldable.Instances
-- Description : Instances of 'Recursive' and 'Corecursive' for various
--               things.
-- --------------------------------------------------------------------- [ EOH ]
module Data.Functor.Foldable.Instances

-- %default total

%access public export

interface (Functor f) => Base t (f : Type -> Type) where
  type : Type
  functor : Type -> Type

  type {t} = t
  functor {f} = f

data ListF : Type -> Type -> Type where
  NilF : ListF _ _
  Cons : a -> b -> ListF a b

implementation Functor (ListF a) where
  map _ NilF       = NilF
  map f (Cons a b) = Cons a (f b)

implementation Base (List a) (ListF a) where

interface (Functor f, Base t f) => Corecursive (f : Type -> Type) (t : Type) where
  embed : (Base t f) => f t -> t

interface (Base t f, Functor f) => Recursive (f : Type -> Type) (t : Type) where
  project : (Base t f) => t -> f t

ana : (Corecursive f t) => (t -> f t) -> t -> t
ana g = a 
  where a x = embed . map a . g $ x

postpro : (Recursive f t, Corecursive f t) => (f t -> f t) -> (t -> f t) -> t -> t
postpro e g = a 
  where a x = embed . map (ana (e . project) . a) . g $ x

cata : (Recursive f t, Base a f) => (f a -> a) -> t -> a
cata f = c 
  where c x = f . map c . project $ x

prepro : (Recursive f t, Corecursive f t) => (f t -> f t) -> (f t -> t) -> t -> t
prepro e f = c 
  where c x = f . map (c . (cata (embed . e))) . project $ x

implementation Recursive (ListF a) (List a) where
  base' = a
  project [] = NilF
  project (x::xs) = Cons x xs

implementation Corecursive (ListF a) (List a) where
  base = a
  embed NilF = []
  embed (Cons x xs) = x::xs
