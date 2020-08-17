
dup : (1 x : ty) -> (ty, ty)


my_id : a -> a

not_id : {a : Type} -> a -> a

descType : Type -> String
descType Int = "Int"
descType String = "String"
descType (List a) = "List of " ++ descType a
descType (a -> b) = ?hmmm -- "Function"
descType _ = "Something else"

