uncurry : (a -> b -> c) -> (a, b) -> c

curry : ((a, b) -> c) -> a -> b -> c

selectThings : ((a, b), (c, d)) -> (b, c)

append : List a -> List a -> List a











data HList : List Type -> Type where
     Nil : HList []
     (::) : t -> HList ts -> HList (t :: ts)

data ElemAt : Nat -> Type -> List xs -> Type where
     AtZ :                  ElemAt Z     t (t :: ts)
     AtS : ElemAt k t ts -> ElemAt (S k) t (u :: ts)

%name HList xs, ys
%name ElemAt p

lookup : ElemAt i ty tys -> HList tys -> ty
lookup AtZ (x :: xs) = x
lookup (AtS p) (x :: xs) = lookup p xs
