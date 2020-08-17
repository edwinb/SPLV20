module RLE

import Decidable.Equality

rep : Nat -> a -> List a
rep 0 x = []
rep (S k) x = x :: rep k x

data RunLength : List ty -> Type where
     Empty : RunLength []
     Run : (n : Nat) -> (x : ty) -> RunLength more ->
           RunLength (rep n x ++ more)

rle : DecEq a => (xs : List a) -> RunLength xs
rle [] = Empty
rle (x :: xs) with (rle xs)
  rle (x :: []) | Empty = Run 1 x Empty
  rle (x :: (rep n y ++ more)) | (Run n y comp) with (decEq x y)
    rle (y :: (rep n y ++ more)) | (Run n y comp) | (Yes Refl)
        = Run (S n) y comp
    rle (x :: (rep n y ++ more)) | (Run n y comp) | (No contra)
        = Run 1 x $ Run n y comp

testComp : RunLength {ty=Char} ?
testComp = Run 3 'x' $ Run 4 'y' $ Empty

data Singleton : a -> Type where
     Val : (x : a) -> Singleton x

uncompress : RunLength {ty} xs -> Singleton xs
