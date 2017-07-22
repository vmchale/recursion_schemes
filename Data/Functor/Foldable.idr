-- ----------------------------------------------------------------- [ Lib.idr ]
-- Module      : Data.Functor.Foldable
-- Description : 
-- --------------------------------------------------------------------- [ EOH ]
module Data.Functor.Foldable

import Control.Monad.Free

-- %default total

%access export

-- | Fix-point data type for catamorphisms of various kinds
data Fix : (Type -> Type) -> Type where
  Fx : f (Fix f) -> Fix f

||| Create a fix-point with a functor
fix : f (Fix f) -> Fix f
fix = Fx

||| Unfix a 'Fix f'
unfix : Fix f -> f (Fix f)
unfix (Fx x) = x

||| Anamorphism
ana : Functor f => (a -> f a) -> a -> Fix f
ana g = fix . map (ana g) . g

--futu : Functor f => (a -> f (Free f a)) -> a -> Fix f
--futu g = fix . map (futu g) . g

||| Apomorphism
apo : Functor f => (a -> f (Either (Fix f)  a)) -> a -> Fix f
apo g = fix . map (either id (apo g)) . g

||| Postpromorphism
postpro : Functor f => (f (Fix f) -> f (Fix f)) -> (a -> f a) -> a -> Fix f
postpro e g = fix . map (ana (e . unfix) . (postpro e g)) . g

||| Catamorphism
cata : Functor f => (f a -> a) -> Fix f -> a
cata f = f . map (cata f) . unfix

||| Prepromorphism
prepro : Functor f => (f (Fix f) -> f (Fix f)) -> (f a -> a) -> Fix f -> a
prepro n f = f . map ((prepro n f) . cata (fix . n)) . unfix

||| Paramorphism
para : Functor f => (f (Fix f, a) -> a) -> Fix f -> a
para f = snd . cata (\x => (Fx $ map fst x, f x))

||| Zygomorphism
zygo : Functor f => (f b -> b) -> (f (b, a) -> a) -> Fix f -> a
zygo f g = snd . cata (\x => (f $ map fst x, g x))

||| Mutumorphism
mutu : Functor f => (f (b, a) -> b) -> (f (b, a) -> a) -> Fix f -> a
mutu f g = snd . cata (\x => (f x, g x))


||| Mendler's histomorphism
mhisto : (((Fix f) -> c) -> (Fix f -> f (Fix f)) -> f (Fix f) -> c) -> Fix f -> c
mhisto psi = psi (mhisto psi) unfix . unfix

||| Mendler's catamorphism
mcata : (Functor f) => (((Fix f) -> c) -> f (Fix f) -> c) -> Fix f -> c
mcata psi = psi (mcata psi) . unfix

||| Hylomorphism
hylo : Functor f => (f b -> b) -> (a -> f a) -> a -> b
hylo f g = h
  where h = f . map h . g

||| Elgot algebra (see [this paper](https://arxiv.org/abs/cs/0609040))
elgot : Functor f => (f a -> a) -> (b -> Either a (f b)) -> b -> a
elgot phi psi = h where h = (id `either` phi . map h) . psi

||| Elgot coalgebra
coelgot : Functor f => ((a, f b) -> b) -> (a -> f a) -> a -> b
coelgot phi psi = h where h = phi . (\x => (x, (map h . psi) x))
