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
dropVar (n :: xs) First = xs
dropVar (n :: xs) (Later p) = n :: dropVar xs p

public export
data Var : List Name -> Type where
     MkVar : {i : Nat} -> (0 p : IsVar n i vars) -> Var vars

public export
data NVar : Name -> List Name -> Type where
     MkNVar : {i : Nat} -> (0 p : IsVar n i vars) -> NVar n vars

export
weakenNVar : (ns : List Name) ->
             {idx : Nat} -> (0 p : IsVar name idx inner) ->
             NVar name (ns ++ inner)
weakenNVar [] x = MkNVar x
weakenNVar (y :: xs) x
   = let MkNVar x' = weakenNVar xs x in
         MkNVar (Later x')

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
binderType : Binder tm -> tm
binderType (Lam x ty) = ty
binderType (Pi x ty) = ty
binderType (PVar ty) = ty
binderType (PVTy ty) = ty

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

public export
interface Weaken (tm : List Name -> Type) where
  weaken : {n, vars : _} -> tm vars -> tm (n :: vars)
  weakenNs : {vars : _} -> (ns : List Name) -> tm vars -> tm (ns ++ vars)

  weakenNs [] t = t
  weakenNs (n :: ns) t = weaken (weakenNs ns t)

  weaken = weakenNs [_]

-- Term manipulation
export
apply : Term vars -> List (Term vars) -> Term vars
apply fn [] = fn
apply fn (a :: args) = apply (App fn a) args

export
embed : Term vars -> Term (vars ++ more)
embed tm = believe_me tm -- Really??

export
getFnArgs : Term vars -> (Term vars, List (Term vars))
getFnArgs tm = getFA [] tm
  where
    getFA : List (Term vars) -> Term vars ->
            (Term vars, List (Term vars))
    getFA args (App f a) = getFA (a :: args) f
    getFA args tm = (tm, args)

export
isVar : (n : Name) -> (ns : List Name) -> Maybe (Var ns)
isVar n [] = Nothing
isVar n (m :: ms)
    = case nameEq n m of
           Nothing => do MkVar p <- isVar n ms
                         pure (MkVar (Later p))
           Just Refl => pure (MkVar First)

export
varExtend : IsVar x idx xs -> IsVar x idx (xs ++ ys)
varExtend p = believe_me p

export
insertNVarNames : {outer, ns : _} ->
                  (idx : Nat) ->
                  (0 p : IsVar name idx (outer ++ inner)) ->
                  NVar name (outer ++ (ns ++ inner))
insertNVarNames {ns} {outer = []} idx prf = weakenNVar ns prf
insertNVarNames {outer = (y :: xs)} Z First = MkNVar First
insertNVarNames {ns} {outer = (y :: xs)} (S i) (Later x)
    = let MkNVar prf = insertNVarNames {ns} i x in
          MkNVar (Later prf)

export
insertNames : {outer, inner : _} ->
              (ns : List Name) -> Term (outer ++ inner) ->
              Term (outer ++ (ns ++ inner))
insertNames ns (Local idx prf)
    = let MkNVar prf' = insertNVarNames {ns} idx prf in
          Local _ prf'
insertNames ns (Ref nt name) = Ref nt name
insertNames ns (Meta name args)
    = Meta name (map (insertNames ns) args)
insertNames {outer} {inner} ns (Bind x b scope)
    = Bind x (assert_total (map (insertNames ns) b))
           (insertNames {outer = x :: outer} {inner} ns scope)
insertNames ns (App fn arg)
    = App (insertNames ns fn) (insertNames ns arg)
insertNames ns Erased = Erased
insertNames ns TType = TType

export
Weaken Term where
  weakenNs ns tm = insertNames {outer = []} ns tm

namespace Bounds
  public export
  data Bounds : List Name -> Type where
       None : Bounds []
       Add : (x : Name) -> Name -> Bounds xs -> Bounds (x :: xs)

export
addVars : {later, bound : _} ->
          {idx : Nat} ->
          Bounds bound -> (0 p : IsVar name idx (later ++ vars)) ->
          NVar name (later ++ (bound ++ vars))
addVars {later = []} {bound} bs p = weakenNVar bound p
addVars {later = (x :: xs)} bs First = MkNVar First
addVars {later = (x :: xs)} bs (Later p)
  = let MkNVar p' = addVars {later = xs} bs p in
        MkNVar (Later p')

resolveRef : {later : _} ->
             (done : List Name) -> Bounds bound -> Name ->
             Maybe (Term (later ++ (done ++ bound ++ vars)))
resolveRef done None n = Nothing
resolveRef {later} {vars} done (Add {xs} new old bs) n
    = if n == old
         then rewrite appendAssociative later done (new :: xs ++ vars) in
              let MkNVar p = weakenNVar {inner = new :: xs ++ vars}
                                        (later ++ done) First in
                     Just (Local _ p)
         else rewrite appendAssociative done [new] (xs ++ vars)
                in resolveRef (done ++ [new]) bs n

mkLocals : {later, bound : _} ->
           Bounds bound ->
           Term (later ++ vars) -> Term (later ++ (bound ++ vars))
mkLocals bs (Local idx p)
    = let MkNVar p' = addVars bs p in Local _ p'
mkLocals bs (Ref Bound name)
    = maybe (Ref Bound name) id (resolveRef [] bs name)
mkLocals bs (Ref nt name)
    = Ref nt name
mkLocals bs (Meta name xs)
    = maybe (Meta name (map (mkLocals bs) xs))
            id (resolveRef [] bs name)
mkLocals {later} bs (Bind x b scope)
    = Bind x (map (mkLocals bs) b)
           (mkLocals {later = x :: later} bs scope)
mkLocals bs (App fn arg)
    = App (mkLocals bs fn) (mkLocals bs arg)
mkLocals bs Erased = Erased
mkLocals bs TType = TType

export
refsToLocals : {bound : _} ->
               Bounds bound -> Term vars -> Term (bound ++ vars)
refsToLocals None y = y
refsToLocals bs y = mkLocals {later = []} bs y

-- Replace any reference to 'x' with a locally bound name 'new'
export
refToLocal : (x : Name) -> (new : Name) -> Term vars -> Term (new :: vars)
refToLocal x new tm = refsToLocals (Add new x None) tm

-- Replace any Ref Bound in a type with appropriate local
export
resolveNames : (vars : List Name) -> Term vars -> Term vars
resolveNames vars (Ref Bound name)
    = case isVar name vars of
           Just (MkVar prf) => Local _ prf
           _ => Ref Bound name
resolveNames vars (Meta n xs)
    = Meta n (map (resolveNames vars) xs)
resolveNames vars (Bind x b scope)
    = Bind x (map (resolveNames vars) b) (resolveNames (x :: vars) scope)
resolveNames vars (App fn arg)
    = App (resolveNames vars fn) (resolveNames vars arg)
resolveNames vars tm = tm

-- Substitute some explicit terms for names in a term, and remove those
-- names from the scope
namespace SubstEnv
  public export
  data SubstEnv : List Name -> List Name -> Type where
       Nil : SubstEnv [] vars
       (::) : Term vars ->
              SubstEnv ds vars -> SubstEnv (d :: ds) vars

  findDrop : {drop : _} -> {idx : Nat} ->
             (0 p : IsVar name idx (drop ++ vars)) ->
             SubstEnv drop vars -> Term vars
  findDrop {drop = []} var env = Local _ var
  findDrop {drop = x :: xs} First (tm :: env) = tm
  findDrop {drop = x :: xs} (Later p) (tm :: env)
      = findDrop p env

  find : {drop, vars, outer : _} -> {idx : Nat} ->
         (0 p : IsVar name idx (outer ++ (drop ++ vars))) ->
         SubstEnv drop vars ->
         Term (outer ++ vars)
  find {outer = []} var env = findDrop var env
  find {outer = x :: xs} First env = Local _ First
  find {outer = x :: xs} (Later p) env = weaken (find p env)

  substEnv : {drop, vars, outer : _} ->
             SubstEnv drop vars -> Term (outer ++ (drop ++ vars)) ->
             Term (outer ++ vars)
  substEnv env (Local _ prf)
      = find prf env
  substEnv env (Ref x name) = Ref x name
  substEnv env (Meta n xs)
      = Meta n (map (substEnv env) xs)
  substEnv {outer} env (Bind x b scope)
      = Bind x (map (substEnv env) b)
               (substEnv {outer = x :: outer} env scope)
  substEnv env (App fn arg)
      = App (substEnv env fn) (substEnv env arg)
  substEnv env Erased = Erased
  substEnv env TType = TType

  export
  substs : {drop, vars : _} ->
           SubstEnv drop vars -> Term (drop ++ vars) -> Term vars
  substs env tm = substEnv {outer = []} env tm

  export
  subst : {vars, x : _} -> Term vars -> Term (x :: vars) -> Term vars
  subst val tm = substEnv {outer = []} {drop = [_]} [val] tm

-- Replace an explicit name with a term
export
substName : {vars : _} -> Name -> Term vars -> Term vars -> Term vars
substName x new (Ref nt name)
    = case nameEq x name of
           Nothing => Ref nt name
           Just Refl => new
substName x new (Meta n xs)
    = Meta n (map (substName x new) xs)
-- ASSUMPTION: When we substitute under binders, the name has always been
-- resolved to a Local, so no need to check that x isn't shadowing
substName x new (Bind y b scope)
    = Bind y (map (substName x new) b) (substName x (weaken new) scope)
substName x new (App fn arg)
    = App (substName x new fn) (substName x new arg)
substName x new tm = tm

public export
data CompatibleVars : List Name -> List Name -> Type where
     CompatPre : CompatibleVars xs xs
     CompatExt : CompatibleVars xs ys -> CompatibleVars (n :: xs) (m :: ys)

export
areVarsCompatible : (xs : List Name) -> (ys : List Name) ->
                    Maybe (CompatibleVars xs ys)
areVarsCompatible [] [] = pure CompatPre
areVarsCompatible (x :: xs) (y :: ys)
    = do compat <- areVarsCompatible xs ys
         pure (CompatExt compat)
areVarsCompatible _ _ = Nothing

export
renameVars : CompatibleVars xs ys -> Term xs -> Term ys
renameVars compat tm = believe_me tm -- no names in term, so it's identity
-- But how would we would define it?

export
renameTop : (m : Name) -> Term (n :: vars) -> Term (m :: vars)
renameTop m tm = renameVars (CompatExt CompatPre) tm

--- Show instances

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
