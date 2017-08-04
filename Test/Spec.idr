module Test.Spec

import Specdris.Spec
import Data.Functor.Foldable
import Data.Functor.Foldable.Instances
import Data.Vect

zygoPseudoalgebra : ListF Int (Bool, Int) -> Int
zygoPseudoalgebra NilF = 0
zygoPseudoalgebra (Cons n (b, x)) = if b then (n+x) else (n-x)

zygoAlgebra : ListF Int Bool -> Bool
zygoAlgebra NilF = False
zygoAlgebra (Cons _ bool) = not bool

plusMinus : List Int -> Int
plusMinus = zygo zygoAlgebra zygoPseudoalgebra

algebra' : ListF (List a) (List a) -> List a
algebra' NilF = []
algebra' (Cons x xs) = x ++ xs

implementation Base (List a) (ListF (List a)) where
  type = List a
  functor = ListF (List a)

cataConcat : List (List a) -> List a
cataConcat = cata algebra'

algebra : ListF (List a) (List (List a)) ->  List (List a)
algebra NilF = []
algebra (Cons x xs) = x::xs 

coalgebra : List a -> ListF (List a) (List a)
coalgebra (x::xs) = Cons (x::xs) xs
coalgebra [] = NilF

suffix : List a -> List (List a)
suffix = hylo algebra coalgebra . drop 1

export
specSuite : IO ()
specSuite = 
  spec $ do
    describe "hylo" $
      it "should be able to implement the suffix function" $
        (suffix . unpack) "ego" `shouldBe` [['g','o'], ['o']]
    describe "cata" $
      it "should be able to implement 'concat'" $
      (cataConcat . map unpack) [ "I", "am" ] `shouldBe` ['I', 'a', 'm']
    describe "zygo" $
      it "should be able to implement plusMinus" $
        plusMinus [1,2,3] `shouldBe` -4
