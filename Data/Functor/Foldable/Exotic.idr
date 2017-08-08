module Data.Functor.Foldable.Exotic

import Control.Arrow
import Data.Functor.Foldable
import Data.Functor.Foldable.Instances
import Data.Composition

%access public export

||| Interface holding homomorphisms of F-algebras.
interface (Functor f) => Hom (f : Type -> Type) where
  subtype : (f a -> a) -> (f b -> b)

interface (Functor f, Functor g) => SubHom (f : Type -> Type) (g : Type -> Type) t1 t2 where
  phi : (Recursive f t1) => (f t1 -> t1) -> (g t2 -> t2) -> (g t2 -> t2)


||| Dendromorphism, simultaneously tearing down two structures at once
dendro : (Recursive f1 t1, Base a1 f1, Recursive f2 t2, Recursive f1 a1, SubHom f1 f2 a1 a2, Base a2 f2) => (f1 a1 -> a1) -> (f2 a2 -> a2) -> t2 -> a2
dendro = cata .* phi

||| Mendler's catamorphism
mcata : ({y : _} -> ((y -> c) -> f y -> c)) -> Fix f -> c
mcata psi = psi (mcata psi) . unfix

||| Mendler's histomorphism
mhisto : ({y : _} -> ((y -> c) -> (y -> f y) -> f y -> c)) -> Fix f -> c
mhisto psi = psi (mhisto psi) unfix . unfix

||| Elgot algebra (see [this paper](https://arxiv.org/abs/cs/0609040))
elgot : Functor f => (f a -> a) -> (b -> Either a (f b)) -> b -> a
elgot phi psi = h where h = (id `either` phi . map h) . psi

||| Anamorphism that allows shortcuts.
micro : (Functor f, Corecursive f a) => (b -> Either a (f b)) -> b -> a
micro = elgot embed

||| Elgot coalgebra
coelgot : Functor f => ((a, f b) -> b) -> (a -> f a) -> a -> b
coelgot phi psi = h where h = phi . (\x => (x, (map h . psi) x))
