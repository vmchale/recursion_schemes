module Data.Functor.Foldable.Exotic

import Data.Functor.Foldable
import Data.Functor.Foldable.Instances
import Data.Composition

%access public export

interface Subtype b where
  switch : b -> b

||| Interface for homomorphisms of F-algebras paramaterized by G-algebras.
interface (Functor f, Functor g) => SubHom (f : Type -> Type) (g : Type -> Type) t1 t2 where
  phi : (Recursive f t1) => (f t1 -> t1) -> (g t2 -> t2) -> (g t2 -> t2)

||| Interface for homomorphisms of F-coalgebras parametrized by G-coalgebras
interface (Functor f, Functor g) => CoSubHom (f : Type -> Type) (g : Type -> Type) t1 t2 where
  psi : (Corecursive f t1) => (t1 -> f t1) -> (t2 -> g t2) -> (t2 -> g t2)

||| A dendromorphism simultaneously tears down two structures at once.
dendro : (Recursive f1 t1, Base a1 f1, Recursive f2 t2, Recursive f1 a1, SubHom f1 f2 a1 a2, Base a2 f2, Subtype a2) => (f1 a1 -> a1) -> (f2 a2 -> a2) -> t2 -> a2
dendro = pseudocata .* phi where
  pseudocata f = c where
    c x = switch . f . map (switch . c) . project $ x

||| A chemamorphism builds up a structure using two base functors.
chema : (Corecursive f1 t1, Base a1 f1, Corecursive f2 t2, Corecursive f1 a1, CoSubHom f1 f2 a1 a2, Base a2 f2, Subtype a2) => (a1 -> f1 a1) -> (a2 -> f2 a2) -> a2 -> t2
chema = pseudoana .* psi where
  pseudoana g = a where
    a x = embed . map (a . switch) . g . switch $ x

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
