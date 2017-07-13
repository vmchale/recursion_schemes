module Test.Spec

import Specdris.Spec
import Recursion_schemes.Lib

export

specSuite : IO ()
specSuite = spec $ do
  describe "sum" $
    it "should sum a list correctly" $
      sum [1,2,3] `shouldBe` 6
