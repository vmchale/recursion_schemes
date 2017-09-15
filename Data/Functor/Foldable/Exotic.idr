module Data.Functor.Foldable.Exotic

import Control.Arrow
import Control.Monad.Identity
import Control.Comonad
import Control.Comonad.Cofree
import Data.Functor.Foldable
import Data.Functor.Foldable.Instances
import Data.Composition
import Data.Bifunctor

%access public export

interface Subtype b where
  switch : b -> b

-- Notes on indexed data types:
--     - An IDT is a trialgebra
-- for a synchromorphism, we need three data types:
--     1) A structure to traverse (IDT)
--     2) A "pocket" for intermediate results (IDT)
--     3) A stucture collecting results (ADT)
-- We addtionally need:
--     1) 

{-synchro : BuiltAlgebra -> StructToBuilt -> Structure -> PocketToStruct -> StructToPocket -> PocketAlgebra
synchro = ?hole-}


||| Gibbons' metamorphism. Tear down a structure, transform it, and then build up a new structure
meta : (Functor f, Base b g, Base a f, Corecursive f t', Recursive g t) => (a -> f a) -> (b -> a) -> (g b -> b) -> t -> t'
meta f e g = ana f . e . cata g

||| Erwig's metamorphism. Essentially a hylomorphism with a natural
||| transformation in between. This allows us to use more than one functor in a
||| hylomorphism.
hyloPro : (Functor f, Functor g) => (f a -> a) -> ({c:_} -> g c -> f c) -> (b -> g b) -> b -> a
hyloPro h e k x = h . e . map (hyloPro h e k) . k $ x

||| A dynamorphism builds up with an anamorphism and tears down with a
||| histomorphism. Useful for lexical scoping.  
dynaPro : (Functor f, Functor g) => (f (Cofree f a) -> a) -> ({c:_} -> g c -> f c) -> (b -> g b) -> b -> a
dynaPro phi eta psi = ghylo distHisto distAna phi (eta . map Id . psi)

||| A dynamorphism without a natural transformation in between.
dyna : (Functor f) => (f (Cofree f a) -> a) -> (b -> f b) -> b -> a
dyna phi = dynaPro phi id

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

--Basically, this forms an F-algebra from a loopkup functoin plus a function that gives us the lookup function
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
