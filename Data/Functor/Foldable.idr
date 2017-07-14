-- ----------------------------------------------------------------- [ Lib.idr ]
-- Module      : Data.Functor.Foldable
-- Description : 
-- --------------------------------------------------------------------- [ EOH ]
module Data.Functor.Foldable

%access export

-- | Fix-point data type for catamorphisms of various kinds
data Fix : (Type -> Type) -> Type where
  Fx : f (Fix f) -> Fix f

fix : f (Fix f) -> Fix f
fix = Fx

unfix : Fix f -> f (Fix f)
unfix (Fx x) = x

ana : Functor f => (a -> f a) -> a -> Fix f
ana g = fix . map (ana g) . g

apo : Functor f => (a -> f (Either (Fix f)  a)) -> a -> Fix f
apo g = fix . map (either id (apo g)) . g

postpro : Functor f => (f (Fix f) -> f (Fix f)) -> (a -> f a) -> a -> Fix f
postpro e g = fix . map (ana (e . unfix) . (postpro e g)) . g
  
cata : Functor f => (f a -> a) -> Fix f -> a
cata f = f . map (cata f) . unfix

prepro : Functor f => (f (Fix f) -> f (Fix f)) -> (f a -> a) -> Fix f -> a
prepro n f = f . map ((prepro n f) . cata (fix . n)) . unfix

para : Functor f => (f (Fix f, a) -> a) -> Fix f -> a
para f = snd . cata (\x => (Fx $ map fst x, f x))

zygo : Functor f => (f b -> b) -> (f (b, a) -> a) -> Fix f -> a
zygo f g = snd . cata (\x => (f $ map fst x, g x))

mutu : Functor f => (f (b, a) -> b) -> (f (b, a) -> a) -> Fix f -> a
mutu f g = snd . cata (\x => (f x, g x))

hylo : Functor f => (f b -> b) -> (a -> f a) -> a -> b
hylo f g = h
  where h = f . map h . g
