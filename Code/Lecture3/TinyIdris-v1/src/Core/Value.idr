module Core.Value

import Core.Context
import Core.Env
import Core.TT

mutual
  public export
  data LocalEnv : List Name -> List Name -> Type where
       Nil  : LocalEnv free []
       (::) : Closure free -> LocalEnv free vars -> LocalEnv free (x :: vars)

  public export
  data Closure : List Name -> Type where
       MkClosure : {vars : _} ->
                   LocalEnv free vars ->
                   Env Term free ->
                   Term (vars ++ free) -> Closure free

  -- The head of a value: things you can apply arguments to
  public export
  data NHead : List Name -> Type where
       NLocal : (idx : Nat) -> (0 p : IsVar name idx vars) ->
                NHead vars
       NRef   : NameType -> Name -> NHead vars
       NMeta  : Name -> List (Closure vars) -> NHead vars

  -- Values themselves. 'Closure' is an unevaluated thunk, which means
  -- we can wait until necessary to reduce constructor arguments
  public export
  data NF : List Name -> Type where
       NBind    : (x : Name) -> Binder (NF vars) ->
                  (Defs -> Closure vars -> Core (NF vars)) -> NF vars
       NApp     : NHead vars -> List (Closure vars) -> NF vars
       NDCon    : Name -> (tag : Int) -> (arity : Nat) ->
                  List (Closure vars) -> NF vars
       NTCon    : Name -> (tag : Int) -> (arity : Nat) ->
                  List (Closure vars) -> NF vars
       NType    : NF vars
       NErased  : NF vars
