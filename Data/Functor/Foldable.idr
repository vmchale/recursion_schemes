module Data.Functor.Foldable

import Control.Monad.Free

%access public export

interface (Functor f) => Base t (f : Type -> Type) where
  type : Type
  functor : Type -> Type

interface (Functor f, Base t f) => Corecursive (f : Type -> Type) (t : Type) where
  embed : (Base t f) => f t -> t

interface (Base t f, Functor f) => Recursive (f : Type -> Type) (t : Type) where
  project : (Base t f) => t -> f t

||| Anamorphism, meant to build up a structure recursively.
ana : (Corecursive f t, Base a f) => (a -> f a) -> a -> t
ana g = a'
  where a' x = embed . map a' . g $ x

||| Postpromorphism. Unfold a structure, applying a natural transformation along the way.
postpro : (Recursive f t, Corecursive f t, Base t f) => (f t -> f t) -> (a -> f a) -> a -> t
postpro e g = a'
  where a' x = embed . map (ana (e . project) . a') . g $ x

||| Catamorphism. Fold a structure. (see [here](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.41.125&rep=rep1&type=pdf))
cata : (Recursive f t, Base a f) => (f a -> a) -> t -> a
cata f = c 
  where c x = f . map c . project $ x

||| Histomorphism.
{-histo : (Base t f, Recursive f t) => (f (Cofree f a) -> a) -> t -> a
histo = ?holeyHistomorphismsBatman-}

distFutu : (Functor f) => Free f (f a) -> f (Free f a)
distFutu (Pure fa) = Pure <$> fa
distFutu (Bind as) = Bind <$> (distFutu <$> as)

gan : (Corecursive f t, Monad m) => (k : {b : _} -> m (f b) -> f (m b)) -> (g : a -> f (m a)) -> m (f (m a)) -> t
gan k g x = embed . map ((gan k g) . liftA g . join) . k $ x

||| Generalized Anamorphism
gana : (Corecursive f t, Base a f, Monad m) => (k : {b : _} -> m (f b) -> f (m b)) -> (g : a -> f (m a)) -> a -> t
gana k g = (gan k g) . pure . g

||| Futumorphism.
futu : (Base a f, Corecursive f t, Functor f) => (a -> f (Free f a)) -> a -> t
futu = gana distFutu

||| Prepromorphism. Fold a structure while applying a natural transformation at each step.
prepro : (Recursive f t, Corecursive f t, Base a f) => (f t -> f t) -> (f a -> a) -> t -> a
prepro e f = c 
  where c x = f . map (c . (cata (embed . e))) . project $ x

||| Paramorphism
para : (Recursive f t, Corecursive f t, Base (t, a) f) => (f (t, a) -> a) -> t -> a
para f = snd . cata (\x => (embed $ map fst x, f x))

||| Mutumorphism
mutu : (Recursive f b, Recursive f a, Base (b, a) f) => (f (b, a) -> b) -> (f (b, a) -> a) -> b -> a
mutu f g = snd . cata (\x => (f x, g x))

||| Zygomorphism (see [here](http://www.iis.sinica.edu.tw/~scm/pub/mds.pdf) for a neat example)
zygo : (Recursive f t, Base t f, Base (b, a) f) => (f b -> b) -> (f (b, a) -> a) -> t -> a
zygo f g = snd . cata (\x => (f $ map fst x, g x))

||| Hylomorphism. Equivalent to a catamorphism and an anamorphism taken together.
hylo : Functor f => (f b -> b) -> (a -> f a) -> a -> b
hylo f g = h
  where h x = f . map h . g $ x
