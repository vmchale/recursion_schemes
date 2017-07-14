module Test.Spec

import Specdris.Spec
import Data.Functor.Foldable
import Data.Vect

export

specSuite : IO ()
specSuite = spec $ do
  describe "something trivial" $
    it "should add two numbers correctly" $
      14 + 3 `shouldBe` 17

