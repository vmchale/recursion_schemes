module Data.Functor.Foldable.Exotic

%access public export

-- | Fix-point data type for exotic recursion schemes of various kinds
data Fix : (Type -> Type) -> Type where
  Fx : f (Fix f) -> Fix f

||| Create a fix-point with a functor
fix : f (Fix f) -> Fix f
fix = Fx

||| Unfix a 'Fix f'
unfix : Fix f -> f (Fix f)
unfix (Fx x) = x

||| Mendler's histomorphism
mhisto : ({y : _} -> ((y -> c) -> (y -> f y) -> f y -> c)) -> Fix f -> c
mhisto psi = psi (mhisto psi) unfix . unfix

||| Mendler's catamorphism
mcata : (Functor f) => ({y : _} -> ((y -> c) -> f y -> c)) -> Fix f -> c
mcata psi = psi (mcata psi) . unfix

||| Elgot algebra (see [this paper](https://arxiv.org/abs/cs/0609040))
elgot : Functor f => (f a -> a) -> (b -> Either a (f b)) -> b -> a
elgot phi psi = h where h = (id `either` phi . map h) . psi

||| Elgot coalgebra
coelgot : Functor f => ((a, f b) -> b) -> (a -> f a) -> a -> b
coelgot phi psi = h where h = phi . (\x => (x, (map h . psi) x))
