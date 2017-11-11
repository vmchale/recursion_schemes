||| Module containing the main typeclasses and recursion schemes on them.
module Data.Functor.Foldable.Mod

import Control.Monad.Identity
import Control.Monad.Free
import Control.Comonad
import Control.Comonad.Cofree

%access public export

||| This is an interface which does nothing interesting, but it functions as a
||| way of saying "f is a base functor with underlying type t"
interface Base t (f : Type -> Type) where

||| Interface for corecursive data types. Corecursive types correspond to
||| anamorphisms.
interface (Functor f, Base t f) => Corecursive (f : Type -> Type) (t : Type) where
  embed : f t -> t

||| Recursive types correspond to catamorphisms.
interface (Functor f, Base t f) => Recursive (f : Type -> Type) (t : Type) where
  project : t -> f t

||| Anamorphism, meant to build up a structure recursively.
ana : (Corecursive f t, Base a f) => (a -> f a) -> a -> t
ana g = a'
  where a' x = embed . map a' . g $ x

||| Postpromorphism. Unfold a structure, applying a natural transformation along the way.
postpro : (Recursive f t, Corecursive f t, Base t f) => (f t -> f t) -> (a -> f a) -> a -> t
postpro e g = a'
  where a' x = embed . map (ana (e . project) . a') . g $ x

||| Generalized Anamorphism
||| @ k A distributive law
||| @ g A (f . m)-coalgebra
gana : (Corecursive f t, Base a f, Monad m) => (k : {b : _} -> m (f b) -> f (m b)) -> (g : a -> f (m a)) -> a -> t
gana k g = (gan k g) . pure . g
  where gan : (Corecursive f t, Monad m) => (k : {b : _} -> m (f b) -> f (m b)) -> (g : a -> f (m a)) -> m (f (m a)) -> t
        gan k g x = embed . map ((gan k g) . map g . join) . k $ x

||| Generalized catamorphism
||| @ k A distributive law
||| @ g A (f . w)-algebra
gcata : (Recursive f t, Base a f, Comonad w) => (k : {b:_} -> f (w b) -> w (f b)) -> (g : f (w a) -> a) -> t -> a
gcata k g = g . extract . (gcat k g)
  where gcat : (Recursive f t, Comonad w) => (k : {b:_} -> f (w b) -> w (f b)) -> (g : f (w a) -> a) -> t -> w (f (w a))
        gcat k g x = k . map (duplicate . map g . (gcat k g)) . project $ x

||| Generalized hylomorphism
||| @ k A distributive law on f
||| @ l A distributive law on l
||| @ f' A (f . w)-algebra
||| @ g' A (f . m)-coalgebra
ghylo : (Functor f, Comonad w, Monad m) => 
        (k : {b:_} -> f (w b) -> w (f b)) ->
        (l : {c:_} -> m (f c) -> f (m c)) ->
        (f' : f (w b) -> b) ->
        (g' : a -> f (m a)) ->
        a -> b
ghylo k l f' g' = extract . (gh k l f' g') . pure where
  gh : (Functor f, Comonad w, Monad m) => (k : {d:_} -> f (w d) -> w (f d)) -> (l : {c:_} -> m (f c) -> f (m c)) -> (f' : f (w b) -> b) -> (g' : a -> f (m a)) -> m a -> w b
  gh k l f' g' x = map f' . k . map (duplicate . (gh k l f' g') . join) . l . map g' $ x

||| Distributive law for catamorphisms
distCata : Functor f => f (Identity a) -> Identity (f a)
distCata = Id . map runIdentity

||| Distributive law for anamorphisms.
distAna : Functor f => Identity (f a) -> f (Identity a)
distAna = map Id . runIdentity

||| Distributive law for futumorphisms.
distFutu : (Functor f) => Free f (f a) -> f (Free f a)
distFutu (Pure fa) = Pure <$> fa
distFutu (Bind as) = Bind <$> (distFutu <$> as)

||| Futumorphism
futu : (Base a f, Corecursive f t) => (a -> f (Free f a)) -> a -> t
futu = gana distFutu

||| Distributive law for histomorphisms
distHisto : (Functor f) => f (Cofree f a) -> Cofree f (f a)
distHisto = unfold g where
  g as = (extract <$> as, unwrap <$> as)

||| Histomorphism
histo : (Base a f, Recursive f t) => (f (Cofree f a) -> a) -> t -> a
histo = gcata distHisto

||| Chronomorphism
chrono : Functor f => (f (Cofree f b) -> b) -> (a -> f (Free f a)) -> a -> b
chrono = ghylo distHisto distFutu

||| Catamorphism. Folds a structure. (see [here](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.41.125&rep=rep1&type=pdf))
cata : (Recursive f t, Base a f) => (f a -> a) -> t -> a
cata f = c 
  where c x = f . map c . project $ x

||| Prepromorphism. Fold a structure while applying a natural transformation at each step.
prepro : (Recursive f t, Corecursive f t, Base a f) => (f t -> f t) -> (f a -> a) -> t -> a
prepro e f = c 
  where c x = f . map (c . (cata (embed . e))) . project $ x

||| Catamorphism interweaving two data types.
dicata : (Recursive f b, Recursive f a, Base (b, a) f) => (f (b, a) -> b) -> (f (b, a) -> a) -> b -> a
dicata f g = snd . cata (\x => (f x, g x))

||| Mutumorphism
mutu : (Recursive f t, Base t f) => (f (a, a) -> a) -> (f (a, a) -> a) -> t -> a
mutu f g x = g . map (\x => (mutu g f x, mutu f g x)) . project $ x

||| Zygomorphism (see [here](http://www.iis.sinica.edu.tw/~scm/pub/mds.pdf) for a neat example)
zygo : (Recursive f t, Base t f, Base (b, a) f) => (f b -> b) -> (f (b, a) -> a) -> t -> a
zygo f g = snd . cata (\x => (f $ map fst x, g x))

||| Paramorphism
para : (Recursive f t, Corecursive f t, Base (t, a) f) => (f (t, a) -> a) -> t -> a
para f = snd . cata (\x => (embed $ map fst x, f x))

||| Hylomorphism; equivalent to a catamorphism and an anamorphism taken together.
hylo : Functor f => (f b -> b) -> (a -> f a) -> a -> b
hylo f g = h
  where h x = f . map h . g $ x
