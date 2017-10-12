-- ------------------------------------- [ Data.Functor.Foldable.Instances.idr ]
-- Module      : Data.Functor.Foldable.Internal.Instances
-- Description : Instances of 'Recursive' and 'Corecursive' for various
--               things.
-- --------------------------------------------------------------------- [ EOH ]
module Data.Functor.Foldable.Instances

import Control.Monad.Free
import Data.Functor.Foldable.Mod

%access public export

implementation Base Nat Maybe where

implementation Recursive Maybe Nat where
  project Z = Nothing
  project (S a) = Just a

implementation Corecursive Maybe Nat where
  embed Nothing = Z
  embed (Just a) = S a

||| Fix-point data type for exotic recursion schemes of various kinds
data Fix : (Type -> Type) -> Type where
  Fx : f (Fix f) -> Fix f

||| Nu fix-point functor for coinduction
codata Nu : (f : Type -> Type) -> Type -> Type where
  NuF : ((a -> f a) -> a) -> b -> Nu f b

{-data Mu :  (f : Type -> Type) -> Type where
  MuF : ({ a : _ } -> (f a -> a) -> a) -> Mu f-}

implementation Functor (Nu f) where
  map g (NuF h a) = NuF h (g a)

implementation (Functor f) => Base t (Nu f) where

implementation (Functor f) => Base (Fix t) f where

||| Create a fix-point with a functor
fix : f (Fix f) -> Fix f
fix = Fx

||| Unfix a 'Fix f'
unfix : Fix f -> f (Fix f)
unfix (Fx x) = x

data ListF : Type -> Type -> Type where
  NilF : ListF _ _
  Cons : a -> b -> ListF a b

implementation Functor (ListF a) where
  map _ NilF       = NilF
  map f (Cons a b) = Cons a (f b)

implementation Base b (ListF a) where

||| Lambek's lemma assures us this function always exists.
lambek : (Recursive f t, Corecursive f t, Base (f t) f) => (t -> f t)
lambek = cata (map embed)

||| The dual of Lambek's lemma.
colambek : (Recursive f t, Corecursive f t, Base (f t) f) => (f t -> t)
colambek = ana (map project)

implementation Recursive (ListF a) (List a) where
  project [] = NilF
  project (x::xs) = Cons x xs

implementation Corecursive (ListF a) (List a) where
  embed NilF = []
  embed (Cons x xs) = x::xs

||| Futumorphism
futu' : (Base a (ListF t), Corecursive (ListF t) t) => (a -> (ListF t) (Free (ListF t) a)) -> a -> t
futu' = gana distFutu
