module Core.CaseTree

import Core.TT

import Data.List

mutual
  -- Case trees
  -- We may only dispatch on variables, not expressions
  public export
  data CaseTree : List Name -> Type where
       -- case x return scTy of { p1 => e1 ; ... }
       Case : {name, vars : _} ->
              (idx : Nat) ->
              (0 p : IsVar name idx vars) ->
              (scTy : Term vars) -> List (CaseAlt vars) ->
              CaseTree vars
       -- RHS: no need for further inspection
       STerm : Term vars -> CaseTree vars
       -- error from a partial match
       Unmatched : (msg : String) -> CaseTree vars
       -- Absurd context
       Impossible : CaseTree vars

  -- Case alternatives. Unlike arbitrary patterns, they can be at most
  -- one constructor deep.
  -- Idris2 also needs cases for 'Delay' and primitives.
  public export
  data CaseAlt : List Name -> Type where
       -- Constructor for a data type; bind the arguments and subterms.
       ConCase : Name -> (tag : Int) -> (args : List Name) ->
                 CaseTree (args ++ vars) -> CaseAlt vars
       -- Catch-all case
       DefaultCase : CaseTree vars -> CaseAlt vars

mutual
  insertCaseNames : {outer, inner : _} ->
                    (ns : List Name) -> CaseTree (outer ++ inner) ->
                    CaseTree (outer ++ (ns ++ inner))
  insertCaseNames {inner} {outer} ns (Case idx prf scTy alts)
      = let MkNVar prf' = insertNVarNames {outer} {inner} {ns} _ prf in
            Case _ prf' (insertNames {outer} ns scTy)
                (map (insertCaseAltNames {outer} {inner} ns) alts)
  insertCaseNames {outer} ns (STerm x) = STerm (insertNames {outer} ns x)
  insertCaseNames ns (Unmatched msg) = Unmatched msg
  insertCaseNames ns Impossible = Impossible

  insertCaseAltNames : {outer, inner : _} ->
                       (ns : List Name) ->
                       CaseAlt (outer ++ inner) ->
                       CaseAlt (outer ++ (ns ++ inner))
  insertCaseAltNames {outer} {inner} ns (ConCase x tag args ct)
      = ConCase x tag args
           (rewrite appendAssociative args outer (ns ++ inner) in
                    insertCaseNames {outer = args ++ outer} {inner} ns
                        (rewrite sym (appendAssociative args outer inner) in
                                 ct))
  insertCaseAltNames ns (DefaultCase ct)
      = DefaultCase (insertCaseNames ns ct)

export
Weaken CaseTree where
  weakenNs ns t = insertCaseNames {outer = []} ns t

-- Patterns, which arise from LHS expressions, and are converted to
-- case trees
public export
data Pat : Type where
     PCon : Name -> (tag : Int) -> (arity : Nat) ->
            List Pat -> Pat
     PLoc : Name -> Pat
     PUnmatchable : Term [] -> Pat

export
Show Pat where
  show (PCon n t a args) = show n ++ show (t, a) ++ show args
  show (PLoc n) = "{" ++ show n ++ "}"
  show _ = "_"

export
mkPat' : List Pat -> Term [] -> Term [] -> Pat
mkPat' args orig (Ref Bound n) = PLoc n
mkPat' args orig (Ref (DataCon t a) n) = PCon n t a args
mkPat' args orig (App fn arg)
    = let parg = mkPat' [] arg arg in
                 mkPat' (parg :: args) orig fn
mkPat' args orig tm = PUnmatchable orig

export
argToPat : Term [] -> Pat
argToPat tm
    = mkPat' [] tm tm

export
mkTerm : (vars : List Name) -> Pat -> Term vars
mkTerm vars (PCon n tag arity xs)
    = apply (Ref (DataCon tag arity) n) (map (mkTerm vars) xs)
mkTerm vars (PLoc n)
    = case isVar n vars of
           Just (MkVar prf) => Local _ prf
           _ => Ref Bound n
mkTerm vars (PUnmatchable tm) = embed tm

-- Show instances

mutual
  export
  {vars : _} -> Show (CaseTree vars) where
    show (Case {name} idx prf ty alts)
        = "case " ++ show name ++ "[" ++ show idx ++ "] : " ++ show ty ++ " of { " ++
                showSep " | " (assert_total (map show alts)) ++ " }"
    show (STerm tm) = show tm
    show (Unmatched msg) = "Error: " ++ show msg
    show Impossible = "Impossible"

  export
  {vars : _} -> Show (CaseAlt vars) where
    show (ConCase n tag args sc)
        = show n ++ " " ++ showSep " " (map show args) ++ " => " ++
          show sc
    show (DefaultCase sc)
        = "_ => " ++ show sc
