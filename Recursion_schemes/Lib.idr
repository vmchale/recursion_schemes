-- ----------------------------------------------------------------- [ Lib.idr ]
-- Module      : Recursion_schemes.Lib
-- Description : 
-- --------------------------------------------------------------------- [ EOH ]
module Recursion_schemes.Lib

%access export

data Fix : (Type -> Type) -> Type where
  FixPoint : f (Fix f) -> Fix f

unFix : Fix f -> f (Fix f)
unFix (FixPoint x) = x

cata : Functor f => (f a -> a) -> Fix f -> a
cata f = f . map (cata f) . unFix

para : Functor f => (f (Fix f, a) -> a) -> Fix f -> a
para f = snd . cata (\x => (FixPoint $ map fst x, f x))

zygo : Functor f => (f b -> b) -> (f (b, a) -> a) -> Fix f -> a
zygo f g = snd . cata (\x => (f $ map fst x, g x))

mutu : Functor f => (f (b, a) -> b) -> (f (b, a) -> a) -> Fix f -> a
mutu f g = snd . cata (\x => (f x, g x))
