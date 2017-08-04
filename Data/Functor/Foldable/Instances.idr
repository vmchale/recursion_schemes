-- ------------------------------------- [ Data.Functor.Foldable.Instances.idr ]
-- Module      : Data.Functor.Foldable.Internal.Instances
-- Description : Instances of 'Recursive' and 'Corecursive' for various
--               things.
-- --------------------------------------------------------------------- [ EOH ]
module Data.Functor.Foldable.Instances

import Data.Functor.Foldable

%access public export

-- | Fix-point data type for exotic recursion schemes of various kinds
data Fix : (Type -> Type) -> Type where
  Fx : f (Fix f) -> Fix f

implementation (Functor f) => Base (Fix t) f where
  type = Fix f
  functor = f

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

implementation Base (List a) (ListF a) where
  type = (List a)
  functor = (ListF a)

implementation Base (Bool, Int) (ListF Int) where
  type = (Bool, Int)
  functor = ListF Int

implementation Recursive (ListF a) (List a) where
  project [] = NilF
  project (x::xs) = Cons x xs

implementation Corecursive (ListF a) (List a) where
  embed NilF = []
  embed (Cons x xs) = x::xs
