-- ----------------------------------------------------------------- [ Lib.idr ]
-- Module      : Recursion_schemes.Lib
-- Description : 
-- --------------------------------------------------------------------- [ EOH ]
module Recursion_schemes.Lib

%access export

data Fix : (Type -> Type) -> Type where
  FixPoint : f (Fix f) -> Fix f

