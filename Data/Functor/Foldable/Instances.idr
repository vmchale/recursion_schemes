-- ------------------------------------- [ Data.Functor.Foldable.Instances.idr ]
-- Module      : Data.Functor.Foldable.Instances
-- Description : Instances of 'Recursive' and 'Corecursive' for various
--               things.
-- --------------------------------------------------------------------- [ EOH ]
module Data.Functor.Foldable.Instances

--import Data.Functor.Foldable

%access public export

data ListF : Type -> Type -> Type where
  NilF : ListF _ _
  Cons : a -> b -> ListF a b

implementation Functor (ListF a) where
  map _ NilF       = NilF
  map f (Cons a b) = Cons a (f b)

interface Functor f => Corecursive (f : Type -> Type) (t : Type) where
  base : Type
  embed : f t -> t

interface Functor f => Recursive (f : Type -> Type) (t : Type) where
  base' : Type
  project : t -> f t

ana : (Corecursive f t) => (t -> f t) -> t -> t
ana g = a where a = embed . map a . g

postpro : (Recursive f t, Corecursive f t) => (f t -> f t) -> (t -> f t) -> t -> t
postpro e g = a where a = embed . map (ana (e . project) . a) . g

cata : (Recursive f t) => (f t -> t) -> t -> t
cata f = c where c = f . map c . project

prepro : (Recursive f t, Corecursive f t) => (f t -> f t) -> (f t -> t) -> t -> t
prepro e f = c where c = f . map (c . (cata (embed . e))) . project

implementation Recursive (ListF a) (List a) where
  base' = a
  project [] = NilF
  project (x::xs) = Cons x xs

implementation Corecursive (ListF a) (List a) where
  base = a
  embed NilF = []
  embed (Cons x xs) = x::xs
