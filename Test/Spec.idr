module Test.Spec

import Specdris.Spec
import Data.Functor.Foldable
import Data.Vect
import Control.Comonad.Cofree

-- FIXME morphisms with constraints? particularly re: symmteries
-- "safe" compilation using this?
-- particularly discrete pseudo-hamiltonian dynamics
-- oh man finite symplectic geometry

-- TODO computation of pi from http://www.cs.ox.ac.uk/jeremy.gibbons/publications/metamorphisms-mpc.pdf

naturals : Nat -> ListF Nat Nat
naturals Z = NilF
naturals (S n) = Cons (n + 1) n

-- TODO have a "wrapped n" monad? then `take n` is type-safer

-- This is also an instructive use of cofree comonads!
-- Do note that it indexes starting at 0.
catalan : Nat -> Nat
catalan = dyna coalgebra naturals
  where
    coalgebra : ListF Nat (Cofree (ListF Nat) Nat) -> Nat
    coalgebra NilF = 1
    coalgebra (Cons n table) = sum (Prelude.List.zipWith (*) xs (reverse xs))
      where
        xs = take n table
        take : Nat -> (Cofree (ListF Nat) Nat) -> List Nat
        take Z _ = []
        take (S n) (Co a NilF) = [a]
        take (S n) (Co a (Cons v as)) = a :: take n as

roundedSqrt : Nat -> Nat
roundedSqrt = cast . cast {to=Integer} . sqrt . cast

toN : Nat -> List Nat
toN = reverse . ana naturals

isPrime : Nat -> List Nat -> Bool
isPrime n ns = all (\a => mod n a /= 0) (filter (<= (roundedSqrt n)) ns)

dedup : (Eq a) => List a -> List a
dedup = para pseudoalgebra where
  pseudoalgebra : (Eq a) => ListF a (List a, List a) -> List a
  pseudoalgebra NilF                 = []
  pseudoalgebra (Cons x (past, xs))  = if elem x past then xs else x :: xs

evenOdd : Nat -> Bool
evenOdd = mutu odd even where
  odd : Maybe (Bool, Bool) -> Bool
  odd Nothing = False
  odd (Just (_, b)) = b
  even : Maybe (Bool, Bool) -> Bool
  even Nothing = True
  even (Just (_, b)) = b

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

-- fibonacci zygomorphism?

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
    describe "dyna" $
      it "should do something with catalan numbers" $
        catalan 6 `shouldBe` 132
    describe "ana" $
      it "should give the first n naturals" $
        toN 5 `shouldBe` [1,2,3,4,5]
