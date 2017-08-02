module Test.Spec

import Specdris.Spec
import Data.Functor.Foldable
import Data.Functor.Foldable.Instances
import Data.Vect

algebra : ListF (List a) (List (List a)) ->  List (List a)
algebra NilF = []
algebra (Cons x xs) = x::xs 

coalgebra : (List a) -> ListF (List a) (List a)
coalgebra (x::xs) = Cons (x::xs) xs
coalgebra [] = NilF

suffix : (List a) -> (List (List a))
suffix = hylo algebra coalgebra . drop 1

export
specSuite : IO ()
specSuite = 
  spec $ do
    describe "hylo" $
      it "should be able to implement the suffix function" $
        (suffix . unpack) "ego" `shouldBe` [['g','o'], ['o']]
