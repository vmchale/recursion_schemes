-- ----------------------------------------------------------------- [ Lib.idr ]
-- Module      : Recursion_schemes.Lib
-- Description : 
-- --------------------------------------------------------------------- [ EOH ]
module Recursion_schemes.Lib

%access export

-- | Fix-point data type for catamorphisms of various kinds
data Fix : (Type -> Type) -> Type where
  Fx : f (Fix f) -> Fix f

project : Fix f -> f (Fix f)
project (Fx x) = x

embed : f (Fix f) -> Fix f
embed = Fx

cata : Functor f => (f a -> a) -> Fix f -> a
cata f = f . map (cata f) . project

para : Functor f => (f (Fix f, a) -> a) -> Fix f -> a
para f = snd . cata (\x => (Fx $ map fst x, f x))

zygo : Functor f => (f b -> b) -> (f (b, a) -> a) -> Fix f -> a
zygo f g = snd . cata (\x => (f $ map fst x, g x))

mutu : Functor f => (f (b, a) -> b) -> (f (b, a) -> a) -> Fix f -> a
mutu f g = snd . cata (\x => (f x, g x))

hylo : Functor f => (f b -> b) -> (a -> f a) -> a -> b
hylo f g = h
  where h = f . map h . g
