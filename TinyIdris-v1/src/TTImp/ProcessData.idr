module TTImp.ProcessData

import Core.Context
import Core.Env
import Core.Normalise
import Core.TT

import TTImp.Elab.Term
import TTImp.TTImp

import Data.List

export
processCon : {auto c : Ref Ctxt Defs} ->
             ImpTy -> Core (Name, Term [])
processCon (MkImpTy n ty)
    = do (tychk, _) <- checkTerm [] ty (Just gType)
         -- Exercise: What other checks are needed?
         -- Name doesn't exist; return type is the data type we're defining
         pure (n, tychk)

export
processData : {auto c : Ref Ctxt Defs} ->
              ImpData -> Core ()
processData (MkImpData n tycon datacons)
    = do (tychk, _) <- checkTerm [] tycon (Just gType)
         -- Add it to the context before checking data constructors
         -- Exercise: We should also check whether it's already defined!
         defs <- get Ctxt
         arity <- getArity defs [] tychk
         addDef n (newDef tychk (TCon 0 arity))
         chkcons <- traverse processCon datacons

         defs <- get Ctxt
         traverse_ (\ (i, (cn, ty)) =>
                       do carity <- getArity defs [] ty
                          addDef cn (newDef ty (DCon (cast i) carity)))
                   (zip [0..(length chkcons)] chkcons)
         -- Idris 2 has to do a bit more work here to relate the type constructor
         -- and data constructors (e.g. for totality checking, interactive
         -- editing) but this is enough for our purposes
         coreLift $ putStrLn $ "Processed " ++ show n
