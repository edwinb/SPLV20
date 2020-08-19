module TTImp.ProcessDef

import Core.CaseBuilder
import Core.CaseTree
import Core.Context
import Core.Env
import Core.Normalise
import Core.TT
import Core.Value

import TTImp.Elab.Term
import TTImp.TTImp

getRHSEnv : {vars : _} ->
            Env Term vars -> Term vars -> Term vars ->
            Core (vars' ** (Env Term vars', Term vars', Term vars'))
-- The names have to match here, and if type checking is implemented correctly
-- they will, but we don't have a way to express that! So we need to check.
getRHSEnv env (Bind n (PVar ty) sc) (Bind n' (PVTy _) scty) with (nameEq n n')
  getRHSEnv env (Bind n (PVar ty) sc) (Bind n' (PVTy _) scty) | Nothing
      = throw (GenericMsg "Can't happen: names don't match in getRHSEnv")
  getRHSEnv env (Bind n (PVar ty) sc) (Bind n (PVTy _) scty) | (Just Refl)
      = getRHSEnv (PVar ty :: env) sc scty
getRHSEnv env lhs ty = pure (vars ** (env, lhs, ty))

processClause : {auto c : Ref Ctxt Defs} ->
                ImpClause -> Core Clause
processClause (PatClause lhs rhs)
    = do -- Check the LHS
         (lhstm, lhsty) <- checkTerm [] lhs Nothing
         -- Get the pattern variables from the LHS, and the expected type, 
         -- and check the RHS in that context

         (vars ** (env, lhsenv, rhsexp)) <-
             getRHSEnv [] lhstm !(getTerm lhsty)
         -- Check the RHS in that context
         (rhstm, rhsty) <- checkTerm env rhs (Just (gnf env rhsexp))
         pure (MkClause env lhsenv rhstm)

export
processDef : {auto c : Ref Ctxt Defs} ->
             Name -> List ImpClause -> Core ()
processDef n clauses
    = do defs <- get Ctxt
         Just gdef <- lookupDef n defs
              | Nothing => throw (GenericMsg ("No type declaration for " ++ show n))
         chkcs <- traverse processClause clauses

         -- Now we have all the clauses, make a case tree
         (args ** tree) <- getPMDef n (type gdef) chkcs

         -- Update the definition with the compiled tree
         updateDef n (record { definition = PMDef args tree })
         coreLift $ putStrLn $ "Processed " ++ show n
