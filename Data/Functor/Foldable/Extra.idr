module Data.Functor.Foldable.Extra

import Data.Functor.Foldable.Mod
import Data.Functor.Foldable.Instances

%access public export

conditionalParamorphism : (a -> a -> Bool) -> List a -> List (List a)
conditionalParamorphism c = para psi
  where psi : ListF a (List a, List (List a)) -> List (List a)
        psi NilF = []
        psi (Cons x ((a::as), (b::bs))) = if (c x a) then (x::b)::bs else [x]::(b::bs)
