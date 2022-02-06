module Core.UnifyState

import Core.Context
import Core.Core
import Core.Env
import Core.TT

import Data.List
import Data.SortedMap
import Data.SortedSet

public export
data Constraint : Type where
     -- An unsolved constraint, noting two terms which need to be convertible
     -- in a particular environment
     MkConstraint : {vars : _} ->
                    (env : Env Term vars) ->
                    (x : Term vars) -> (y : Term vars) ->
                    Constraint
     -- An unsolved sequence of constraints, arising from arguments in an
     -- application where solving later constraints relies on solving earlier
     -- ones
     MkSeqConstraint : {vars : _} ->
                       (env : Env Term vars) ->
                       (xs : List (Term vars)) ->
                       (ys : List (Term vars)) ->
                       Constraint
     -- A resolved constraint
     Resolved : Constraint

public export
record UState where
  constructor MkUState
  holes : SortedSet Name
  guesses : SortedSet Name
  constraints : SortedMap Int Constraint -- map for finding constraints by ID
  nextName : Int
  nextConstraint : Int

export
initUState : UState
initUState = MkUState empty empty empty 0 0

export
data UST : Type where

export
resetNextVar : {auto u : Ref UST UState} ->
               Core ()
resetNextVar
    = do ust <- get UST
         put UST ({ nextName := 0 } ust)

-- Generate a global name based on the given root, in the current namespace
export
genName : {auto u : Ref UST UState} ->
          String -> Core Name
genName str
    = do ust <- get UST
         put UST ({ nextName $= (+1) } ust)
         pure (MN str (nextName ust))

addHoleName : {auto u : Ref UST UState} ->
              Name -> Core ()
addHoleName n
    = do ust <- get UST
         put UST ({ holes $= insert n } ust)

addGuessName : {auto u : Ref UST UState} ->
               Name -> Core ()
addGuessName n
    = do ust <- get UST
         put UST ({ guesses $= insert n  } ust)

export
removeHole : {auto u : Ref UST UState} ->
             Name -> Core ()
removeHole n
    = do ust <- get UST
         put UST ({ holes $= delete n } ust)

export
addConstraint : {auto u : Ref UST UState} ->
                Constraint -> Core Int
addConstraint constr
    = do ust <- get UST
         let cid = nextConstraint ust
         put UST ({ constraints $= insert cid constr,
                           nextConstraint := cid+1 } ust)
         pure cid

export
deleteConstraint : {auto u : Ref UST UState} ->
                Int -> Core ()
deleteConstraint cid
    = do ust <- get UST
         put UST ({ constraints $= delete cid } ust)

-- Make a type which abstracts over an environment
-- Don't include 'let' bindings, since they have a concrete value and
-- shouldn't be generalised
export
abstractEnvType : {vars : _} ->
                  Env Term vars -> (tm : Term vars) -> Term []
abstractEnvType [] tm = tm
abstractEnvType (Pi e ty :: env) tm
    = abstractEnvType env (Bind _ (Pi e ty) tm)
abstractEnvType (b :: env) tm
    = abstractEnvType env (Bind _ (Pi Explicit (binderType b)) tm)

mkConstantAppArgs : {vars : _} ->
                    Env Term vars ->
                    (wkns : List Name) ->
                    List (Term (wkns ++ (vars ++ done)))
mkConstantAppArgs [] wkns = []
mkConstantAppArgs {done} {vars = x :: xs} (b :: env) wkns
    = let rec = mkConstantAppArgs {done} env (wkns ++ [x]) in
          Local (length wkns) (mkVar wkns) ::
                  rewrite (appendAssociative wkns [x] (xs ++ done)) in rec
  where
    mkVar : (wkns : List Name) ->
            IsVar name (length wkns) (wkns ++ name :: vars ++ done)
    mkVar [] = First
    mkVar (w :: ws) = Later (mkVar ws)

-- Create a new metavariable with the given name and return type,
-- and return a term which is the metavariable applied to the environment
-- (and which has the given type)
export
newMeta : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} ->
          Env Term vars -> Name -> Term vars -> Def ->
          Core (Term vars)
newMeta {vars} env n ty def
    = do let hty = abstractEnvType env ty
         let hole = newDef hty def
         addDef n hole
         addHoleName n
         pure (Meta n envArgs)
  where
    envArgs : List (Term vars)
    envArgs = let args = reverse (mkConstantAppArgs {done = []} env []) in
                  rewrite sym (appendNilRightNeutral vars) in args

mkConstant : {vars : _} ->
             Env Term vars -> Term vars -> Term []
mkConstant [] tm = tm
mkConstant {vars = x :: _} (b :: env) tm
    = let ty = binderType b in
          mkConstant env (Bind x (Lam Explicit ty) tm)

-- Given a term and a type, add a new guarded constant to the global context
-- by applying the term to the current environment
-- Return the replacement term (the name applied to the environment)
export
newConstant : {vars : _} ->
              {auto u : Ref UST UState} ->
              {auto c : Ref Ctxt Defs} ->
              Env Term vars ->
              (tm : Term vars) -> (ty : Term vars) ->
              (constrs : List Int) ->
              Core (Term vars)
newConstant {vars} env tm ty constrs
    = do let def = mkConstant env tm
         let defty = abstractEnvType env ty
         cn <- genName "postpone"
         let guess = newDef defty (Guess def constrs)
         addDef cn guess
         addGuessName cn
         pure (Meta cn envArgs)
  where
    envArgs : List (Term vars)
    envArgs = let args = reverse (mkConstantAppArgs {done = []} env []) in
                  rewrite sym (appendNilRightNeutral vars) in args
