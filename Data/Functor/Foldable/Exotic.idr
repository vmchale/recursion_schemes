module Data.Functor.Foldable.Exotic

import Control.Arrow
import Control.Monad.Identity
import Control.Comonad
import Control.Comonad.Cofree
import Data.Functor.Foldable.Mod
import Data.Functor.Foldable.Instances

%access public export

infixl 9 .*

(.*) : (c -> d) -> (a -> b -> c) -> (a -> b -> d)
(.*) f g x y = f (g x y)

||| Gibbons' metamorphism. Tear down a structure, transform it, and then build up a new structure
meta : (Functor f, Corecursive f t', Recursive g t) => (a -> f a) -> (b -> a) -> (g b -> b) -> t -> t'
meta f e g = ana f . e . cata g

||| Erwig's metamorphism. Essentially a hylomorphism with a natural
||| transformation in between. This allows us to use more than one functor in a
||| hylomorphism.
hyloPro : (Functor f, Functor g) => (f a -> a) -> ({c:_} -> g c -> f c) -> (b -> g b) -> b -> a
hyloPro h e k = g
  where g x = h . e . map g . k $ x

||| A dynamorphism builds up with an anamorphism and tears down with a
||| histomorphism. Useful for lexical scoping.  
dynaPro : (Functor f, Functor g) => (f (Cofree f a) -> a) -> ({c:_} -> g c -> f c) -> (b -> g b) -> b -> a
dynaPro phi eta psi = ghylo distHisto distAna phi (eta . map Id . psi)

||| A dynamorphism without a natural transformation in between.
dyna : (Functor f) => (f (Cofree f a) -> a) -> (b -> f b) -> b -> a
dyna phi = dynaPro phi id

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
