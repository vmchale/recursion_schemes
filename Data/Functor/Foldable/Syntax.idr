module Data.Functor.Foldable.Syntax

import Data.Functor.Foldable

%access public export

||| Interface holding homomorphisms of F-algebras.
interface (Functor f) => Hom (f : Type -> Type) where
  subtype : (f a -> a) -> (f b -> b)

interface (Functor f, Functor g) => SubHom (f : Type -> Type) (g : Type -> Type) t1 t2 where
  phi : (Recursive f t1) => (f t1 -> t1) -> (g t2 -> t2) -> (g t2 -> t2)

data Simple = List (List Simple)
            | SimpleString String
            | Num Int
            | Sum Simple Simple

data SimpleF a = ListF (List a)
            | StringF String
            | NumF Int
            | SumF a a

data Complex = Conditional Bool Complex Complex
             | Simp Simple
             | ForLoop Simple Complex

data ComplexF a = ConditionalF Bool a a
             | SimpF Simple
             | ForLoopF Simple a

implementation Functor SimpleF where
  map f (ListF ls) = ListF (map f ls)
  map f str@(StringF s) = str
  map f num@(NumF n) = num
  map f (SumF a b) = SumF (f a) (f b)

implementation Functor ComplexF where
  map f (ConditionalF b x y) = ConditionalF b (f x) (f y)
  map f (ForLoopF range x) = ForLoopF range (f x)
  map f s@(SimpF simple) = s

implementation Base Simple SimpleF where
  type = Simple
  functor = SimpleF

implementation (Base Simple SimpleF) => Recursive SimpleF Simple where
  project (List ls) = ListF ls
  project (SimpleString s) = StringF s
  project (Num i) = NumF i
  project (Sum m n) = SumF m n

implementation (Base Simple SimpleF) => SubHom SimpleF ComplexF Simple Complex where
  phi subFAlgebra fAlgebra = fAlgebra . collapseInner
    where collapseInner : ComplexF Complex -> ComplexF Complex
          collapseInner (SimpF simple) = SimpF $ cata subFAlgebra simple
          collapseInner (ForLoopF simple c) = ForLoopF (cata subFAlgebra simple) c
          collapseInner x = x

dicata : (Recursive f1 t1, Base a1 f1, SubHom f1 f2 t1 t2, Recursive f2 t2, Base a2 f2) => (f1 a1 -> a1) -> (f2 a2 -> a2) -> t2 -> a2
dicata subFAlgebra fAlgebra = cata composed
  where --composed : (SubHom f1 f2 t1 t2, Recursive f2 t2, Base a2 f2) => f2 a2 -> a2
        composed = phi subFAlgebra fAlgebra
