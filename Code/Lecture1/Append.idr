appendNeutral : (xs : List a) -> xs = xs ++ []
appendNeutral [] = Refl
appendNeutral (x :: xs) = cong (x ::) (appendNeutral xs)

appendAssoc : (xs, ys, zs : List a) ->
              xs ++ (ys ++ zs) = (xs ++ ys) ++ zs
appendAssoc [] ys zs = Refl
appendAssoc (x :: xs) ys zs = cong (x ::) (appendAssoc xs ys zs)
