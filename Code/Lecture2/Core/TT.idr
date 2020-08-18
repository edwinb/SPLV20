module Core.TT

import Data.List
import Decidable.Equality

-- In Idris2, this is defined in Core.Name
public export
data Name : Type where
     UN : String -> Name -- user written name
     MN : String -> Int -> Name -- machine generated name

export
nameEq : (x : Name) -> (y : Name) -> Maybe (x = y)
nameEq (UN x) (UN y) with (decEq x y)
  nameEq (UN y) (UN y) | (Yes Refl) = Just Refl
  nameEq (UN x) (UN y) | (No contra) = Nothing
nameEq (MN x t) (MN x' t') with (decEq x x')
  nameEq (MN x t) (MN x t') | (Yes Refl) with (decEq t t')
    nameEq (MN x t) (MN x t) | (Yes Refl) | (Yes Refl) = Just Refl
    nameEq (MN x t) (MN x t') | (Yes Refl) | (No contra) = Nothing
  nameEq (MN x t) (MN x' t') | (No contra) = Nothing
nameEq _ _ = Nothing

export
Eq Name where
  (==) (UN x) (UN y) = x == y
  (==) (MN x i) (MN y j) = i == j && x == y
  (==) _ _ = False

nameTag : Name -> Int
nameTag (UN _) = 0
nameTag (MN _ _) = 1

export
Ord Name where
  compare (UN x) (UN y) = compare x y
  compare (MN x i) (MN y j)
      = case compare x y of
             EQ => compare i j
             t => t
  compare x y = compare (nameTag x) (nameTag y)

public export
data NameType : Type where
     Func : NameType
     Bound : NameType
     DataCon : (tag : Int) -> (arity : Nat) -> NameType
     TyCon : (tag : Int) -> (arity : Nat) -> NameType

export
Show NameType where
  show Func = "Func"
  show (DataCon t a) = "DataCon " ++ show (t, a)
  show (TyCon t a) = "TyCon " ++ show (t, a)
  show Bound = "Bound"

public export
data IsVar : Name -> Nat -> List Name -> Type where
     First : IsVar n Z (n :: ns)
     Later : IsVar n i ns -> IsVar n (S i) (m :: ns)

public export
dropVar : (ns : List Name) -> {idx : Nat} ->
          (0 p : IsVar name idx ns) -> List Name

public export
data Var : List Name -> Type where
     MkVar : {i : Nat} -> (0 p : IsVar n i vars) -> Var vars

public export
data PiInfo : Type where
     Implicit : PiInfo
     Explicit : PiInfo

public export
data Binder : Type -> Type where
     Lam : PiInfo -> ty -> Binder ty
     Pi : PiInfo -> ty -> Binder ty

     PVar : ty -> Binder ty -- pattern bound variables ...
     PVTy : ty -> Binder ty -- ... and their type

export
Functor Binder where
  map func (Lam x ty) = Lam x (func ty)
  map func (Pi x ty) = Pi x (func ty)
  map func (PVar ty) = PVar (func ty)
  map func (PVTy ty) = PVTy (func ty)

public export
data Term : List Name -> Type where
     Local : (idx : Nat) -> -- de Bruijn index
             (0 p : IsVar name idx vars) -> -- proof that index is valid
             Term vars
     Ref : NameType -> Name -> Term vars -- a reference to a global name
     Meta : Name -> List (Term vars) -> Term vars
     Bind : (x : Name) -> -- any binder, e.g. lambda or pi
            Binder (Term vars) ->
            (scope : Term (x :: vars)) -> -- one more name in scope
            Term vars
     App : Term vars -> Term vars -> Term vars -- function application
     TType : Term vars
     Erased : Term vars

-- Term manipulation

export
weaken : Term vars -> Term (x :: vars)

export
embed : Term vars -> Term (vars ++ more)

export
contract : Term (x :: vars) -> Maybe (Term vars)

export
subst : Term vars -> Term (x :: vars) -> Term vars

public export
data CompatibleVars : List Name -> List Name -> Type where
     CompatPre : CompatibleVars xs xs
     CompatExt : CompatibleVars xs ys -> CompatibleVars (n :: xs) (m :: ys)

export
renameVars : CompatibleVars xs ys -> Term xs -> Term ys

--- Show instances

export
getFnArgs : Term vars -> (Term vars, List (Term vars))
getFnArgs tm = getFA [] tm
  where
    getFA : List (Term vars) -> Term vars ->
            (Term vars, List (Term vars))
    getFA args (App f a) = getFA (a :: args) f
    getFA args tm = (tm, args)

export
showSep : String -> List String -> String
showSep sep [] = ""
showSep sep [x] = x
showSep sep (x :: xs) = x ++ sep ++ showSep sep xs

export
Show Name where
  show (UN n) = n
  show (MN n i) = "{" ++ n ++ ":" ++ show i ++ "}"

export
nameAt : {vars : _} ->
         (idx : Nat) -> (0 p : IsVar n idx vars) -> Name
nameAt {vars = n :: ns} Z First = n
nameAt {vars = n :: ns} (S k) (Later p) = nameAt k p

export 
{vars : _} -> Show (Term vars) where
  show tm = let (fn, args) = getFnArgs tm in showApp fn args
    where
      showApp : {vars : _} -> Term vars -> List (Term vars) -> String
      showApp (Local {name} idx p) []
         = show (nameAt idx p) ++ "[" ++ show idx ++ "]"
      showApp (Ref _ n) [] = show n
      showApp (Meta n args) []
          = "?" ++ show n ++ "_" ++ show args
      showApp (Bind x (Lam p ty) sc) []
          = "\\" ++ show x ++ " : " ++ show ty ++
            " => " ++ show sc
      showApp (Bind x (Pi Explicit ty) sc) []
          = "((" ++ show x ++ " : " ++ show ty ++
            ") -> " ++ show sc ++ ")"
      showApp (Bind x (Pi Implicit ty) sc) []
          = "{" ++ show x ++ " : " ++ show ty ++
            "} -> " ++ show sc
      showApp (Bind x (PVar ty) sc) []
          = "pat " ++ show x ++ " : " ++ show ty ++
            " => " ++ show sc
      showApp (Bind x (PVTy ty) sc) []
          = "pty " ++ show x ++ " : " ++ show ty ++
            " => " ++ show sc
      showApp (App _ _) [] = "[can't happen]"
      showApp TType [] = "Type"
      showApp Erased [] = "[_]"
      showApp _ [] = "???"
      showApp f args = "(" ++ assert_total (show f) ++ " " ++
                        assert_total (showSep " " (map show args))
                     ++ ")"
