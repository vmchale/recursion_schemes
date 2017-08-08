module Data.Functor.Foldable.Syntax

import Data.Functor.Foldable
import Data.Functor.Foldable.Exotic

%access public export

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

