module TTImp.Elab.Term

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.TT
import Core.Unify
import Core.Value

import TTImp.TTImp

import Data.Maybe

checkExp : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} ->
           Env Term vars ->
           (term : Term vars) ->
           (got : Glued vars) ->
           (expected : Maybe (Glued vars)) ->
           Core (Term vars, Glued vars)
checkExp env term got Nothing = pure (term, got)
checkExp env term got (Just exp)
   = -- 'got' had better unify with exp. This might solve some of the
     -- metavariables. If so, recheck any existing constraints.
     do defs <- get Ctxt
        ures <- unify env !(getNF got) !(getNF exp)

        -- If there are constraints, return a guarded definition. Otherwise,
        -- we've won.
        case constraints ures of
             [] => do -- Success: if any holes were solved, rerun unification
                      -- for any existing constraints
                      when (holesSolved ures) $
                           solveConstraints
                      pure (term, exp)
             cs => do cty <- getTerm exp
                      ctm <- newConstant env term cty cs
                      pure (ctm, got)

-- Check a raw term, given (possibly) the current environment and its expected 
-- type, if known.
-- Returns a pair of checked term and its type.
-- A type is 'Glued', that is, a pair of a term and its normal form, though
-- typically only one has been computed, and the other will be computed if
-- needed.
export
checkTerm : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            Env Term vars -> RawImp -> Maybe (Glued vars) ->
            Core (Term vars, Glued vars)
-- If the n exists in 'env', that's its type.
-- Otherwise, if it exists in the Defs, that's its type.
-- Otherwise, it's undefined.
checkTerm env (IVar n) exp
    = case defined n env of
           Just (MkIsDefined p) =>
               let binder = getBinder p env in
                   checkExp env (Local _ p)
                                (gnf env (binderType binder))
                                exp
           Nothing =>
             do defs <- get Ctxt
                Just gdef <- lookupDef n defs
                     | Nothing => throw (UndefinedName n)
                let nt = case definition gdef of
                              DCon t a => DataCon t a
                              TCon t a => TyCon t a
                              _ => Func
                checkExp env (Ref nt n) (gnf env (embed (type gdef))) exp
checkTerm env (IPi p mn argTy retTy) exp
    = do let n = fromMaybe (MN "_" 0) mn
         (argTytm, gargTyty) <- checkTerm env argTy (Just gType)
         let env' : Env Term (n :: vars)
                  = Pi p argTytm :: env
         (retTytm, gretTyty) <- checkTerm env' retTy (Just gType)
         checkExp env (Bind n (Pi p argTytm) retTytm) gType exp
checkTerm env (ILam p mn argTy scope) Nothing
    = throw (GenericMsg "Can't infer type for lambda")
checkTerm env (ILam p mn argTy scope) (Just exp)
    = do let n = fromMaybe (MN "_" 0) mn
         (argTytm, gargTyty) <- checkTerm env argTy (Just gType)
         let env' : Env Term (n :: vars)
                  = Lam p argTytm :: env
         expTyNF <- getNF exp
         defs <- get Ctxt
         case !(quote defs env expTyNF) of
              Bind _ (Pi _ ty) sc =>
                 do let env' : Env Term (n :: vars)
                             = Lam p argTytm :: env
                    let scty = renameTop n sc
                    (scopetm, gscopety) <-
                              checkTerm env' scope (Just (gnf env' scty))
                    checkExp env (Bind n (Lam p argTytm) scopetm)
                                 (gnf env (Bind n (Pi p argTytm) !(getTerm gscopety)))
                                 (Just exp)
              _ => throw (GenericMsg "Lambda must have a function type")
checkTerm env (IPatvar n ty scope) exp
    = do (ty, gTyty) <- checkTerm env ty (Just gType)
         let env' : Env Term (n :: vars)
                  = PVar ty :: env
         (scopetm, gscopety) <- checkTerm env' scope Nothing
         checkExp env (Bind n (PVar ty) scopetm)
                      (gnf env (Bind n (PVTy ty) !(getTerm gscopety)))
                      exp
checkTerm env (IApp f a) exp
    = do -- Get the function type (we don't have an expected type)
         (ftm, gfty) <- checkTerm env f Nothing
         fty <- getNF gfty
         -- We can only proceed if it really does have a function type
         case fty of
              -- Ignoring the implicitness for now
              NBind x (Pi _ ty) sc =>
                    do defs <- get Ctxt
                       -- Check the argument type, given the expected argument
                       -- type
                       (atm, gaty) <- checkTerm env a
                                                (Just (glueBack defs env ty))
                       -- Calculate the type of the application by continuing
                       -- to evaluate the scope with 'atm'
                       sc' <- sc defs (toClosure env atm)
                       checkExp env (App ftm atm) (glueBack defs env sc') exp
              _ => throw (GenericMsg "Not a function type")
checkTerm env Implicit Nothing
    = throw (GenericMsg "Unknown type for implicit")
checkTerm env Implicit (Just exp)
    = do expty <- getTerm exp
         nm <- genName "_"
         -- Create a metavariable, and hope that it gets solved via
         -- checkExp later
         metaval <- newMeta env nm expty Hole
         pure (metaval, exp)
checkTerm env IType exp = checkExp env TType gType exp
