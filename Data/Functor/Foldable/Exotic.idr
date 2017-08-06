module Data.Functor.Foldable.Exotic

import Control.Arrow
import Data.Functor.Foldable
import Data.Functor.Foldable.Instances

%access public export

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
shortAna : (Functor f, Corecursive f a) => (b -> Either a (f b)) -> b -> a
shortAna = elgot embed

||| Elgot coalgebra
coelgot : Functor f => ((a, f b) -> b) -> (a -> f a) -> a -> b
coelgot phi psi = h where h = phi . (\x => (x, (map h . psi) x))
