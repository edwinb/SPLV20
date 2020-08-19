module Core.Context

import Core.CaseTree
import public Core.Core
import Core.Env
import public Core.TT

import Data.SortedMap

public export
data Def : Type where
    None : Def -- Not yet defined
    PMDef : (args : List Name) -> (treeCT : CaseTree args) ->
            Def -- Ordinary function definition
    DCon : (tag : Int) -> (arity : Nat) -> Def -- data constructor
    TCon : (tag : Int) -> (arity : Nat) -> Def
    Hole : Def
    Guess : (guess : Term []) ->
            (constraints : List Int) -> Def -- unification constraints

-- Idris 2 holds a lot more information about names than just their
-- type and definition, but that's enough for us here
public export
record GlobalDef where
  constructor MkGlobalDef
  type : Term []
  definition : Def

export
newDef : Term [] -> Def -> GlobalDef
newDef ty d = MkGlobalDef ty d

-- A mapping from names to definitions
-- Again there's more to this in Idris 2 since we need to deal with namespaces,
-- and there's also an array to map "resolved" name ids, which is much faster
-- for name lookups in general.
export
Defs : Type
Defs = SortedMap Name GlobalDef

-- This doesn't actually need to be in Core in this system, but it is in
-- Idris 2, because:
--  * the context is an IO array underneath, for O(1) lookup
--  * definitions can be updated on lookup, since we actually store things
--    as a binary encoded form that's stored on disk, and only decode when
--    first used.
-- So, it's in Core here so that there's a more clear mapping to the full
-- version.
export
lookupDef : Name -> Defs -> Core (Maybe GlobalDef)
lookupDef n defs = pure (SortedMap.lookup n defs)

export
initDefs : Core Defs
initDefs = pure empty

export
clearDefs : Defs -> Core Defs
clearDefs d = pure empty

-- A phantom type for finding references to the context
export
data Ctxt : Type where

-- A program consists of a series of data declarations, function type
-- declarations, and function clauses. Even in full Idris 2, this is what
-- everything translates down to. The following types represent well-type
-- data declarations and clauses, ready for adding to the context.

public export
record Constructor where
  constructor MkCon
  name : Name
  arity : Nat
  type : Term []

-- Well typed data declaration
public export
data DataDef : Type where
     MkData : (tycon : Constructor) -> (datacons : List Constructor) ->
              DataDef

-- A well typed pattern clause
public export
data Clause : Type where
     MkClause : {vars : _} ->
                (env : Env Term vars) ->
                (lhs : Term vars) -> (rhs : Term vars) -> Clause

-- Add (or replace) a definition
export
addDef : {auto c : Ref Ctxt Defs} ->
         Name -> GlobalDef -> Core ()
addDef n d
    = do defs <- get Ctxt
         put Ctxt (insert n d defs)

export
updateDef : {auto c : Ref Ctxt Defs} ->
            Name -> (GlobalDef -> GlobalDef) -> Core ()
updateDef n upd
    = do defs <- get Ctxt
         Just gdef <- lookupDef n defs
              | Nothing => throw (UndefinedName n)
         addDef n (upd gdef)
