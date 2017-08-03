-- ----------------------------------------------------------------- [ Lib.idr ]
-- Module      : Data.Functor.Foldable
-- Description : 
-- --------------------------------------------------------------------- [ EOH ]
module Data.Functor.Foldable

import Control.Monad.Free

-- %default total

%access public export

-- | Fix-point data type for catamorphisms of various kinds
data Fix : (Type -> Type) -> Type where
  Fx : f (Fix f) -> Fix f

||| Create a fix-point with a functor
fix : f (Fix f) -> Fix f
fix = Fx

||| Unfix a 'Fix f'
unfix : Fix f -> f (Fix f)
unfix (Fx x) = x

||| Mendler's histomorphism
mhisto : (((Fix f) -> c) -> (Fix f -> f (Fix f)) -> f (Fix f) -> c) -> Fix f -> c
mhisto psi = psi (mhisto psi) unfix . unfix

||| Mendler's catamorphism
mcata : (Functor f) => (((Fix f) -> c) -> f (Fix f) -> c) -> Fix f -> c
mcata psi = psi (mcata psi) . unfix

||| Hylomorphism
hylo : Functor f => (f b -> b) -> (a -> f a) -> a -> b
hylo f g = h
  where h x = f . map h . g $ x

||| Elgot algebra (see [this paper](https://arxiv.org/abs/cs/0609040))
elgot : Functor f => (f a -> a) -> (b -> Either a (f b)) -> b -> a
elgot phi psi = h where h = (id `either` phi . map h) . psi

||| Elgot coalgebra
coelgot : Functor f => ((a, f b) -> b) -> (a -> f a) -> a -> b
coelgot phi psi = h where h = phi . (\x => (x, (map h . psi) x))

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

interface (Functor f, Base t f) => Corecursive (f : Type -> Type) (t : Type) where
  embed : (Base t f) => f t -> t

interface (Base t f, Functor f) => Recursive (f : Type -> Type) (t : Type) where
  project : (Base t f) => t -> f t

ana : (Corecursive f t, Base a f) => (a -> f a) -> a -> t
ana g = a'
  where a' x = embed . map a' . g $ x

postpro : (Recursive f t, Corecursive f t, Base t f) => (f t -> f t) -> (a -> f a) -> a -> t
postpro e g = a'
  where a' x = embed . map (ana (e . project) . a') . g $ x

||| Catamorphism (see [here](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.41.125&rep=rep1&type=pdf))
cata : (Recursive f t, Base a f) => (f a -> a) -> t -> a
cata f = c 
  where c x = f . map c . project $ x

prepro : (Recursive f t, Corecursive f t, Base a f) => (f t -> f t) -> (f a -> a) -> t -> a
prepro e f = c 
  where c x = f . map (c . (cata (embed . e))) . project $ x

||| Paramorphism
para : (Recursive f t, Corecursive f t, Base (t, a) f) => (f (t, a) -> a) -> t -> a
para f = snd . cata (\x => (embed $ map fst x, f x))

||| Mutumorphism
mutu : (Recursive f b, Recursive f a, Base (b, a) f) => (f (b, a) -> b) -> (f (b, a) -> a) -> b -> a
mutu f g = snd . cata (\x => (f x, g x))

||| Zygomorphism (see [here](http://www.iis.sinica.edu.tw/~scm/pub/mds.pdf) for a neat example)
zygo : (Recursive f b, Base (b, a) f) => (f b -> b) -> (f (b, a) -> a) -> b -> a
zygo f g = snd . cata (\x => (f $ map fst x, g x))
