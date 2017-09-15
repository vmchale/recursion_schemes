module Test.Spec

import Specdris.Spec
import Data.Functor.Foldable
import Data.Functor.Foldable.Instances
import Data.Functor.Foldable.Exotic
import Data.Vect
import Control.Monad.Free

roundedSqrt : Nat -> Nat
roundedSqrt = cast . cast {to=Integer} . sqrt . cast

numCoalgebra : Nat -> (ListF Nat Nat)
numCoalgebra Z = NilF
numCoalgebra (S n) = (Cons (S n) n)

toN : Nat -> List Nat
toN = reverse . ana numCoalgebra

isPrime : Nat -> List Nat -> Bool
isPrime n ns = all (\a => mod n a /= 0) (filter (<= (roundedSqrt n)) ns)

dedup : (Eq a) => List a -> List a
dedup = para pseudoalgebra where
  pseudoalgebra : (Eq a) => ListF a (List a, List a) -> List a
  pseudoalgebra NilF                 = []
  pseudoalgebra (Cons x (past, xs))  = if elem x past then xs else x :: xs

evenOdd : Nat -> Bool
evenOdd = mutu odd even where
  odd : NatF (Bool, Bool) -> Bool
  odd ZeroF = False
  odd (SuccF (_, b)) = b
  even : NatF (Bool, Bool) -> Bool
  even ZeroF = True
  even (SuccF (_, b)) = b

collatzCoalgebra : Int -> Either (List Int) (ListF Int Int)
collatzCoalgebra 1 = Left [1]
collatzCoalgebra 2 = Left [2, 1]
collatzCoalgebra 3 = Left [3, 10, 5, 16, 8, 4, 2, 1]
collatzCoalgebra 4 = Left [6, 3, 10, 5, 16, 8, 4, 2, 1]
collatzCoalgebra n with (modInt n 2)
  | 0 = Right $ Cons n (divInt n 2)
  | _ = Right $ Cons n (3 * n + 1)

collatz : Int -> List Int
collatz = micro collatzCoalgebra

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
    describe "micro" $
      it "should provide a simple way to compute the Collatz sequence associated with a number" $
        collatz 12 `shouldBe` [12, 6, 3, 10, 5, 16, 8, 4, 2, 1]
    describe "mutu" $ 
      it "should be able to do recursion on the natural numbers to check for parity" $
        (evenOdd . fromIntegerNat) 10 `shouldBe` True
    describe "para" $
      it "should provide an elegant way to remove duplicates from a list when order doesn't matter" $
        dedup [1,1,2,3,4,5,4] `shouldBe` [1,2,3,5,4]
    describe "ana" $
      it "should give the first n naturals" $
        toN 5 `shouldBe` [1,2,3,4,5]
