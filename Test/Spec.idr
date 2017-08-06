module Test.Spec

import Specdris.Spec
import Data.Functor.Foldable
import Data.Functor.Foldable.Instances
import Data.Functor.Foldable.Exotic
import Data.Vect

evenOdd : Nat -> Bool
evenOdd = mutu odd even where
  odd : NatF (Bool, Bool) -> Bool
  odd ZeroF = False
  odd (SuccF (_, b)) = b
  even : NatF (Bool, Bool) -> Bool
  even ZeroF = True
  even (SuccF (_, b)) = b

collatzAlgebra : ListF Int (List Int) -> (List Int)
collatzAlgebra = embed

collatzCoalgebra : Int -> Either (List Int) (ListF Int Int)
collatzCoalgebra 1 = Left [1]
collatzCoalgebra 2 = Left [2, 1]
collatzCoalgebra 3 = Left [3, 10, 5, 16, 8, 4, 2, 1]
collatzCoalgebra 4 = Left [6, 3, 10, 5, 16, 8, 4, 2, 1]
collatzCoalgebra n with (modInt n 2)
  | 0 = Right $ Cons n (divInt n 2)
  | _ = Right $ Cons n (3 * n + 1)

collatz : Int -> List Int
collatz = elgot collatzAlgebra collatzCoalgebra

elgotCoalgebra : List a -> Either (List (List a)) (ListF (List a) (List a))
elgotCoalgebra [] = Right NilF
elgotCoalgebra (x :: []) = Left ([[x]])
elgotCoalgebra (x :: xs) = Right (Cons (x :: xs) xs) 

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

elgotSuffix : List a -> List (List a)
elgotSuffix = elgot algebra elgotCoalgebra . drop 1

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
    describe "elgot" $
      it "should generalize a hylomorphism" $
        (elgotSuffix . unpack) "ego" `shouldBe` [['g','o'], ['o']]
    describe "elgot" $
      it "should provide a simple way to compute the Collatz sequence associated with a number" $
        collatz 12 `shouldBe` [12, 6, 3, 10, 5, 16, 8, 4, 2, 1]
    describe "mutu'" $ 
      it "should be able to do recursion on the natural numbers to check for parity" $
        (evenOdd . fromIntegerNat) 10 `shouldBe` True
