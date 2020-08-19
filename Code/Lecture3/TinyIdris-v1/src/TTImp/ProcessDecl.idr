module TTImp.ProcessDecl

import Core.Context
import Core.TT

import TTImp.ProcessData
import TTImp.ProcessDef
import TTImp.ProcessType

import TTImp.TTImp

export
processDecl : {auto c : Ref Ctxt Defs} ->
              ImpDecl -> Core ()
processDecl (IClaim (MkImpTy n ty)) = processType n ty
processDecl (IData ddef) = processData ddef
processDecl (IDef x xs) = processDef x xs
