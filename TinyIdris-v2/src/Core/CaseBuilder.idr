module Core.CaseBuilder

import Core.CaseTree
import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.TT
import Core.Value

import Data.LengthMatch
import Data.List
import Data.String

import Decidable.Equality

data ArgType : List Name -> Type where
     Known : (ty : Term vars) -> ArgType vars -- arg has type 'ty'
     Stuck : (fty : Term vars) -> ArgType vars
         -- ^ arg will have argument type of 'fty' when we know enough to
         -- calculate it
     Unknown : ArgType vars
         -- arg's type is not yet known due to a previously stuck argument

{ns : _} -> Show (ArgType ns) where
  show (Known t) = "Known " ++ show t
  show (Stuck t) = "Stuck " ++ show t
  show Unknown = "Unknown"

record PatInfo (pvar : Name) (vars : List Name) where
  constructor MkInfo
  {idx : Nat}
  {name : Name}
  pat : Pat
  0 loc : IsVar name idx vars
  argType : ArgType vars -- Type of the argument being inspected (i.e.
                         -- *not* refined by this particular pattern)

{-
NamedPats is a list of patterns on the LHS of a clause. Each entry in
the list gives a pattern, and a proof that there is a variable we can
inspect to see if it matches the pattern.

A definition consists of a list of clauses, which are a 'NamedPats' and
a term on the RHS. There is an assumption that corresponding positions in
NamedPats always have the same 'Elem' proof, though this isn't expressed in
a type anywhere.
-}

data NamedPats : List Name -> -- pattern variables still to process
                 List Name -> -- the pattern variables still to process,
                              -- in order
                 Type where
     Nil : NamedPats vars []
     (::) : PatInfo pvar vars ->
            -- ^ a pattern, where its variable appears in the vars list,
            -- and its type. The type has no variable names; any names it
            -- refers to are explicit
            NamedPats vars ns -> NamedPats vars (pvar :: ns)

getPatInfo : NamedPats vars todo -> List Pat
getPatInfo [] = []
getPatInfo (x :: xs) = pat x :: getPatInfo xs

updatePats : {vars, todo : _} ->
             {auto c : Ref Ctxt Defs} ->
             Env Term vars ->
             NF vars -> NamedPats vars todo -> Core (NamedPats vars todo)
updatePats env nf [] = pure []
updatePats {todo = pvar :: ns} env (NBind _ (Pi _ farg) fsc) (p :: ps)
  = case argType p of
         Unknown =>
            do defs <- get Ctxt
               empty <- clearDefs defs
               pure ({argType := Known !(quote empty env farg) } p
                          :: !(updatePats env !(fsc defs (toClosure env (Ref Bound pvar))) ps))
         _ => pure (p :: ps)
updatePats env nf (p :: ps)
  = case argType p of
         Unknown =>
            do defs <- get Ctxt
               empty <- clearDefs defs
               pure ({argType := Stuck !(quote empty env nf) } p :: ps)
         _ => pure (p :: ps)

substInPatInfo : {pvar, vars, todo : _} ->
                 {auto c : Ref Ctxt Defs} ->
                 Name -> Term vars -> PatInfo pvar vars ->
                 NamedPats vars todo ->
                 Core (PatInfo pvar vars, NamedPats vars todo)
substInPatInfo {pvar} {vars} n tm p ps
    = case argType p of
           Known ty => pure ({argType := Known (substName n tm ty) } p, ps)
           Stuck fty =>
             do defs <- get Ctxt
                empty <- clearDefs defs
                let env = mkEnv vars
                case !(nf defs env (substName n tm fty)) of
                     NBind _ (Pi _ farg) fsc =>
                       pure ({argType := Known !(quote empty env farg) } p,
                                 !(updatePats env
                                       !(fsc defs (toClosure env
                                             (Ref Bound pvar))) ps))
                     _ => pure (p, ps)
           Unknown => pure (p, ps)

-- Substitute the name with a term in the pattern types, and reduce further
-- (this aims to resolve any 'Stuck' pattern types)
substInPats : {vars, todo : _} ->
              {auto c : Ref Ctxt Defs} ->
              Name -> Term vars -> NamedPats vars todo ->
              Core (NamedPats vars todo)
substInPats n tm [] = pure []
substInPats n tm (p :: ps)
    = do (p', ps') <- substInPatInfo n tm p ps
         pure (p' :: !(substInPats n tm ps'))

getPat : {idx : Nat} ->
         (0 el : IsVar name idx ps) -> NamedPats ns ps -> PatInfo name ns
getPat First (x :: xs) = x
getPat (Later p) (x :: xs) = getPat p xs

dropPat : {idx : Nat} ->
          (0 el : IsVar name idx ps) ->
          NamedPats ns ps -> NamedPats ns (dropVar ps el)
dropPat First (x :: xs) = xs
dropPat (Later p) (x :: xs) = x :: dropPat p xs

Weaken ArgType where
  weaken (Known ty) = Known (weaken ty)
  weaken (Stuck fty) = Stuck (weaken fty)
  weaken Unknown = Unknown

Weaken (PatInfo p) where
  weaken (MkInfo p el fty) = MkInfo p (Later el) (weaken fty)

-- FIXME: perhaps 'vars' should be second argument so we can use Weaken interface
weaken : {x, vars : _} ->
         NamedPats vars todo -> NamedPats (x :: vars) todo
weaken [] = []
weaken (p :: ps) = weaken p :: weaken ps

weakenNs : {vars : _} ->
           (ns : List Name) ->
           NamedPats vars todo -> NamedPats (ns ++ vars) todo
weakenNs ns [] = []
weakenNs ns (p :: ps)
    = weakenNs ns p :: weakenNs ns ps

(++) : NamedPats vars ms -> NamedPats vars ns -> NamedPats vars (ms ++ ns)
(++) [] ys = ys
(++) (x :: xs) ys = x :: xs ++ ys

tail : NamedPats vars (p :: ps) -> NamedPats vars ps
tail (x :: xs) = xs

take : (as : List Name) -> NamedPats vars (as ++ bs) -> NamedPats vars as
take [] ps = []
take (x :: xs) (p :: ps) = p :: take xs ps

data PatClause : (vars : List Name) -> (todo : List Name) -> Type where
     MkPatClause : List Name -> -- names matched so far (from original lhs)
                   NamedPats vars todo ->
                   (rhs : Term vars) -> PatClause vars todo

getNPs : PatClause vars todo -> NamedPats vars todo
getNPs (MkPatClause _ lhs rhs) = lhs

substInClause : {a, vars, todo : _} ->
                {auto c : Ref Ctxt Defs} ->
                PatClause vars (a :: todo) ->
                Core (PatClause vars (a :: todo))
substInClause {vars} {a} (MkPatClause pvars (MkInfo pat pprf fty :: pats) rhs)
    = do pats' <- substInPats a (mkTerm vars pat) pats
         pure (MkPatClause pvars (MkInfo pat pprf fty :: pats') rhs)

data Partitions : List (PatClause vars todo) -> Type where
     ConClauses : {todo, vars, ps : _} ->
                  (cs : List (PatClause vars todo)) ->
                  Partitions ps -> Partitions (cs ++ ps)
     VarClauses : {todo, vars, ps : _} ->
                  (vs : List (PatClause vars todo)) ->
                  Partitions ps -> Partitions (vs ++ ps)
     NoClauses : Partitions []

data ClauseType = ConClause | VarClause

clauseType : PatClause vars (a :: as) -> ClauseType
clauseType (MkPatClause pvars (MkInfo arg _ ty :: rest) rhs)
    = getClauseType arg
  where
    -- used to get the remaining clause types
    clauseType' : Pat -> ClauseType
    clauseType' (PCon _ _ _ xs) = ConClause
    clauseType' _                 = VarClause

    getClauseType : Pat -> ClauseType
    getClauseType (PCon _ _ _ xs) = ConClause
    getClauseType l = clauseType' l

partition : {a, as, vars : _} ->
            (ps : List (PatClause vars (a :: as))) -> Partitions ps
partition [] = NoClauses
partition (x :: xs) with (partition xs)
  partition (x :: (cs ++ ps)) | (ConClauses cs rest)
        = case clauseType x of
               ConClause => ConClauses (x :: cs) rest
               VarClause => VarClauses [x] (ConClauses cs rest)
  partition (x :: (vs ++ ps)) | (VarClauses vs rest)
        = case clauseType x of
               ConClause => ConClauses [x] (VarClauses vs rest)
               VarClause => VarClauses (x :: vs) rest
  partition (x :: []) | NoClauses
        = case clauseType x of
               ConClause => ConClauses [x] NoClauses
               VarClause => VarClauses [x] NoClauses

data ConType : Type where
     CName : Name -> (tag : Int) -> ConType
-- Idris 2 also needs to know if it's a delayed expression or constant:
--      CDelay : ConType
--      CConst : Constant -> ConType

conTypeEq : (x, y : ConType) -> Maybe (x = y)
conTypeEq (CName x tag) (CName x' tag')
   = do Refl <- nameEq x x'
        case decEq tag tag' of
             Yes Refl => Just Refl
             No contra => Nothing

data Group : List Name -> -- variables in scope
             List Name -> -- pattern variables still to process
             Type where
     ConGroup : {newargs : _} ->
                Name -> (tag : Int) ->
                List (PatClause (newargs ++ vars) (newargs ++ todo)) ->
                Group vars todo
-- Idris 2 also has to group delays and constants:
--      DelayGroup : {tyarg, valarg : _} ->
--                   List (PatClause (tyarg :: valarg :: vars)
--                                   (tyarg :: valarg :: todo)) ->
--                   Group vars todo
--      ConstGroup : Constant -> List (PatClause vars todo) ->
--                   Group vars todo


data GroupMatch : ConType -> List Pat -> Group vars todo -> Type where
  ConMatch : LengthMatch ps newargs ->
             GroupMatch (CName n tag) ps
               (ConGroup {newargs} n tag (MkPatClause pvs pats rhs :: rest))
  NoMatch : GroupMatch ct ps g

checkGroupMatch : (c : ConType) -> (ps : List Pat) -> (g : Group vars todo) ->
                  GroupMatch c ps g
checkGroupMatch (CName x tag) ps (ConGroup {newargs} x' tag' (MkPatClause pvs pats rhs :: rest))
    = case checkLengthMatch ps newargs of
           Nothing => NoMatch
           Just prf => case (nameEq x x', decEq tag tag') of
                            (Just Refl, Yes Refl) => ConMatch prf
                            _ => NoMatch
checkGroupMatch (CName x tag) ps _ = NoMatch
checkGroupMatch _ _ _ = NoMatch

data PName : Type where

nextName : {auto i : Ref PName Int} ->
           String -> Core Name
nextName root
    = do x <- get PName
         put PName (x + 1)
         pure (MN root x)

nextNames : {vars : _} ->
            {auto i : Ref PName Int} ->
            {auto c : Ref Ctxt Defs} ->
            String -> List Pat -> Maybe (NF vars) ->
            Core (args ** NamedPats (args ++ vars) args)
nextNames root [] fty = pure ([] ** [])
nextNames {vars} root (p :: pats) fty
     = do defs <- get Ctxt
          empty <- clearDefs defs
          n <- nextName root
          let env = mkEnv vars
          fa_tys <- the (Core (Maybe (NF vars), ArgType vars)) $
              case fty of
                   Nothing => pure (Nothing, Unknown)
                   Just (NBind _ (Pi _ NErased) fsc) =>
                      pure (Just !(fsc defs (toClosure env (Ref Bound n))),
                        Unknown)
                   Just (NBind _ (Pi _ farg) fsc) =>
                      pure (Just !(fsc defs (toClosure env (Ref Bound n))),
                        Known !(quote empty env farg))
                   Just t =>
                      pure (Nothing, Stuck !(quote empty env t))
          (args ** ps) <- nextNames {vars} root pats (fst fa_tys)
          let argTy = case snd fa_tys of
                           Unknown => Unknown
                           Known t => Known (weakenNs (n :: args) t)
                           Stuck t => Stuck (weakenNs (n :: args) t)
          pure (n :: args ** MkInfo p First argTy :: weaken ps)

-- replace the prefix of patterns with 'pargs'
newPats : (pargs : List Pat) -> LengthMatch pargs ns ->
          NamedPats vars (ns ++ todo) ->
          NamedPats vars ns
newPats [] NilMatch rest = []
newPats (newpat :: xs) (ConsMatch w) (pi :: rest)
  = { pat := newpat} pi :: newPats xs w rest

updateNames : List (Name, Pat) -> List (Name, Name)
updateNames = mapMaybe update
  where
    update : (Name, Pat) -> Maybe (Name, Name)
    update (n, PLoc p) = Just (p, n)
    update _ = Nothing

updatePatNames : List (Name, Name) -> NamedPats vars todo -> NamedPats vars todo
updatePatNames _ [] = []
updatePatNames ns (pi :: ps)
    = { pat $= update } pi :: updatePatNames ns ps
  where
    update : Pat -> Pat
    update (PCon n i a ps) = PCon n i a (map update ps)
    update (PLoc n)
        = case lookup n ns of
               Nothing => PLoc n
               Just n' => PLoc n'
    update p = p

groupCons : {a, vars, todo : _} ->
            {auto i : Ref PName Int} ->
            {auto ct : Ref Ctxt Defs} ->
            Name ->
            List Name ->
            List (PatClause vars (a :: todo)) ->
            Core (List (Group vars todo))
groupCons fn pvars cs
     = gc [] cs
  where
    addConG : {vars', todo' : _} ->
              Name -> (tag : Int) ->
              List Pat -> NamedPats vars' todo' ->
              (rhs : Term vars') ->
              (acc : List (Group vars' todo')) ->
              Core (List (Group vars' todo'))
    -- Group all the clauses that begin with the same constructor, and
    -- add new pattern arguments for each of that constructor's arguments.
    -- The type of 'ConGroup' ensures that we refer to the arguments by
    -- the same name in each of the clauses
    addConG {vars'} {todo'} n tag pargs pats rhs []
        = do cty <- the (Core (NF vars')) $ if n == UN "->"
                      then pure $ NBind (MN "_" 0) (Pi Explicit NType) $
                              (\d, a => pure $ NBind (MN "_" 1) (Pi Explicit NErased)
                                (\d, a => pure NType))
                      else do defs <- get Ctxt
                              Just t <- lookupDef n defs
                                   | Nothing => pure NErased
                              nf defs (mkEnv vars') (embed (type t))
             (patnames ** newargs) <- nextNames {vars=vars'} "e" pargs (Just cty)
             -- Update non-linear names in remaining patterns (to keep
             -- explicit dependencies in types accurate)
             let pats' = updatePatNames (updateNames (zip patnames pargs))
                                        (weakenNs patnames pats)
             let clause = MkPatClause {todo = patnames ++ todo'}
                              pvars
                              (newargs ++ pats')
                              (weakenNs patnames rhs)
             pure [ConGroup n tag [clause]]
    addConG {vars'} {todo'} n tag pargs pats rhs (g :: gs) with (checkGroupMatch (CName n tag) pargs g)
      addConG {vars'} {todo'} n tag pargs pats rhs
              ((ConGroup {newargs} n tag ((MkPatClause pvars ps tm) :: rest)) :: gs)
                   | (ConMatch {newargs} lprf)
        = do let newps = newPats pargs lprf ps
             let pats' = updatePatNames (updateNames (zip newargs pargs))
                                        (weakenNs newargs pats)
             let newclause : PatClause (newargs ++ vars') (newargs ++ todo')
                   = MkPatClause pvars
                                 (newps ++ pats')
                                 (weakenNs newargs rhs)
             -- put the new clause at the end of the group, since we
             -- match the clauses top to bottom.
             pure ((ConGroup n tag (MkPatClause pvars ps tm :: rest ++ [newclause]))
                         :: gs)
      addConG n tag pargs pats rhs (g :: gs) | NoMatch
        = do gs' <- addConG n tag pargs pats rhs gs
             pure (g :: gs')

    addGroup : {vars, todo, idx : _} ->
               Pat -> (0 p : IsVar name idx vars) ->
               NamedPats vars todo -> Term vars ->
               List (Group vars todo) ->
               Core (List (Group vars todo))
    addGroup (PCon n t a pargs) pprf pats rhs acc
         = if a == length pargs
              then addConG n t pargs pats rhs acc
              else throw (CaseCompile fn (NotFullyApplied n))
    addGroup _ pprf pats rhs acc = pure acc -- Can't happen, not a constructor
--         -- FIXME: Is this possible to rule out with a type? Probably.

    gc : {a, vars, todo : _} ->
         List (Group vars todo) ->
         List (PatClause vars (a :: todo)) ->
         Core (List (Group vars todo))
    gc acc [] = pure acc
    gc {a} acc ((MkPatClause pvars (MkInfo pat pprf fty :: pats) rhs) :: cs)
        = do acc' <- addGroup pat pprf pats rhs acc
             gc acc' cs

getFirstPat : NamedPats ns (p :: ps) -> Pat
getFirstPat (p :: _) = pat p

getFirstArgType : NamedPats ns (p :: ps) -> ArgType ns
getFirstArgType (p :: _) = argType p

-- Check whether all the initial patterns have the same concrete, known
-- and matchable type, which is multiplicity > 0.
-- If so, it's okay to match on it
sameType : {ns : _} ->
           {auto i : Ref PName Int} ->
           {auto c : Ref Ctxt Defs} ->
           Name ->
           Env Term ns -> List (NamedPats ns (p :: ps)) ->
           Core ()
sameType fn env [] = pure ()
sameType {ns} fn env (p :: xs)
    = do defs <- get Ctxt
         case getFirstArgType p of
              Known t => sameTypeAs !(nf defs env t)
                                    (map getFirstArgType xs)
              ty => throw (CaseCompile fn DifferingTypes)
  where
    firstPat : NamedPats ns (np :: nps) -> Pat
    firstPat (pinf :: _) = pat pinf

    headEq : NF ns -> NF ns -> Bool
    headEq (NBind _ (Pi _ _) _) (NBind _ (Pi _ _) _) = True
    headEq (NTCon n _ _ _) (NTCon n' _ _ _) = n == n'
    headEq NType NType = True
    headEq (NApp (NRef _ n) _) (NApp (NRef _ n') _) = n == n'
    headEq NErased _ = True
    headEq _ NErased = True
    headEq _ _ = False

    sameTypeAs : NF ns -> List (ArgType ns) -> Core ()
    sameTypeAs ty [] = pure ()
    sameTypeAs ty (Known t :: xs) =
         do defs <- get Ctxt
            if headEq ty !(nf defs env t)
               then sameTypeAs ty xs
               else throw (CaseCompile fn DifferingTypes)
    sameTypeAs ty _ = throw (CaseCompile fn DifferingTypes)

-- Check whether all the initial patterns are the same, or are all a variable.
-- If so, we'll match it to refine later types and move on
samePat : List (NamedPats ns (p :: ps)) -> Bool
samePat [] = True
samePat (pi :: xs)
    = samePatAs (getFirstPat pi) (map getFirstPat xs)
  where
    samePatAs : Pat -> List Pat -> Bool
    samePatAs p [] = True
    samePatAs (PCon n t a args) (PCon n' t' _ _ :: ps)
        = n == n' && t == t' && samePatAs (PCon n t a args) ps
    samePatAs (PLoc n) (PLoc _ :: ps) = samePatAs (PLoc n) ps
    samePatAs x y = False

getFirstCon : NamedPats ns (p :: ps) -> Pat
getFirstCon (p :: _) = pat p

-- Count the number of distinct constructors in the initial pattern
countDiff : List (NamedPats ns (p :: ps)) -> Nat
countDiff xs = length (distinct [] (map getFirstCon xs))
  where
    isVar : Pat -> Bool
    isVar (PCon _ _ _ _) = False
    isVar _ = True

    -- Return whether two patterns would lead to the same match
    sameCase : Pat -> Pat -> Bool
    sameCase (PCon _ t _ _) (PCon _ t' _ _) = t == t'
    sameCase x y = isVar x && isVar y

    distinct : List Pat -> List Pat -> List Pat
    distinct acc [] = acc
    distinct acc (p :: ps)
       = if elemBy sameCase p acc
            then distinct acc ps
            else distinct (p :: acc) ps

getScore : {ns : _} ->
           {auto i : Ref PName Int} ->
           {auto c : Ref Ctxt Defs} ->
           Name ->
           List (NamedPats ns (p :: ps)) ->
           Core (Either CaseError ())
getScore name npss
    = do catch (do sameType name (mkEnv ns) npss
                   pure (Right ()))
               (\err => case err of
                             CaseCompile _ err => pure (Left err)
                             _ => throw err)

-- Pick the leftmost matchable thing with all constructors in the
-- same family, or all variables, or all the same type constructor.
pickNext : {p, ns, ps : _} ->
           {auto i : Ref PName Int} ->
           {auto c : Ref Ctxt Defs} ->
           Name -> List (NamedPats ns (p :: ps)) ->
           Core (n ** NVar n (p :: ps))
-- last possible variable
pickNext {ps = []} fn npss
    = if samePat npss
         then pure (_ ** MkNVar First)
         else do Right () <- getScore fn npss
                       | Left err => throw (CaseCompile fn err)
                 pure (_ ** MkNVar First)
pickNext {ps = q :: qs} fn npss
    = if samePat npss
         then pure (_ ** MkNVar First)
         else  case !(getScore fn npss) of
                    Right () => pure (_ ** MkNVar First)
                    _ => do (_ ** MkNVar var) <- pickNext fn (map tail npss)
                            pure (_ ** MkNVar (Later var))

moveFirst : {idx : Nat} -> (0 el : IsVar name idx ps) -> NamedPats ns ps ->
            NamedPats ns (name :: dropVar ps el)
moveFirst el nps = getPat el nps :: dropPat el nps

shuffleVars : {idx : Nat} -> (0 el : IsVar name idx todo) -> PatClause vars todo ->
              PatClause vars (name :: dropVar todo el)
shuffleVars el (MkPatClause pvars lhs rhs)
    = MkPatClause pvars (moveFirst el lhs) rhs

mutual
  {- 'PatClause' contains a list of patterns still to process (that's the
     "todo") and a right hand side with the variables we know about "vars".
     So "match" builds the remainder of the case tree for
     the unprocessed patterns. "err" is the tree for when the patterns don't
     cover the input (i.e. the "fallthrough" pattern, which at the top
     level will be an error). -}
  match : {vars, todo : _} ->
          {auto i : Ref PName Int} ->
          {auto c : Ref Ctxt Defs} ->
          Name ->
          List (PatClause vars todo) -> (err : Maybe (CaseTree vars)) ->
          Core (CaseTree vars)
  -- Before 'partition', reorder the arguments so that the one we
  -- inspect next has a concrete type that is the same in all cases, and
  -- has the most distinct constructors (via pickNext)
  match {todo = (_ :: _)} fn clauses err
      = do (n ** MkNVar next) <- pickNext fn (map getNPs clauses)
           let clauses' = map (shuffleVars next) clauses
           let ps = partition clauses'
           maybe (pure (Unmatched "No clauses"))
                 Core.pure
                !(mixture fn ps err)
  match {todo = []} fn [] err
       = maybe (pure (Unmatched "No patterns"))
               pure err
  match {todo = []} fn ((MkPatClause pvars [] Erased) :: _) err
       = pure Impossible
  match {todo = []} fn ((MkPatClause pvars [] rhs) :: _) err
       = pure $ STerm rhs

  caseGroups : {pvar, vars, todo : _} ->
               {auto i : Ref PName Int} ->
               {auto c : Ref Ctxt Defs} ->
               Name ->
               {idx : Nat} -> (0 p : IsVar pvar idx vars) -> Term vars ->
               List (Group vars todo) -> Maybe (CaseTree vars) ->
               Core (CaseTree vars)
  caseGroups {vars} fn el ty gs errorCase
      = do g <- altGroups gs
           pure (Case _ el (resolveNames vars ty) g)
    where
      altGroups : List (Group vars todo) -> Core (List (CaseAlt vars))
      altGroups [] = maybe (pure [])
                           (\e => pure [DefaultCase e])
                           errorCase
      altGroups (ConGroup {newargs} cn tag rest :: cs)
          = do crest <- match fn rest (map (weakenNs newargs) errorCase)
               cs' <- altGroups cs
               pure (ConCase cn tag newargs crest :: cs')

  conRule : {a, vars, todo : _} ->
            {auto i : Ref PName Int} ->
            {auto c : Ref Ctxt Defs} ->
            Name ->
            List (PatClause vars (a :: todo)) ->
            Maybe (CaseTree vars) ->
            Core (CaseTree vars)
  conRule fn [] err = maybe (pure (Unmatched "No constructor clauses")) pure err
  -- ASSUMPTION, not expressed in the type, that the patterns all have
  -- the same variable (pprf) for the first argument. If not, the result
  -- will be a broken case tree... so we should find a way to express this
  -- in the type if we can.
  conRule {a} fn cs@(MkPatClause pvars (MkInfo pat pprf fty :: pats) rhs :: rest) err
      = do refinedcs <- traverse substInClause cs
           groups <- groupCons fn pvars refinedcs
           ty <- case fty of
                      Known t => pure t
                      _ => throw (CaseCompile fn UnknownType)
           caseGroups fn pprf ty groups err

  varRule : {a, vars, todo : _} ->
            {auto i : Ref PName Int} ->
            {auto c : Ref Ctxt Defs} ->
            Name ->
            List (PatClause vars (a :: todo)) ->
            Maybe (CaseTree vars) ->
            Core (CaseTree vars)
  varRule {vars} {a} fn cs err
      = do alts' <- traverse updateVar cs
           match fn alts' err
    where
      updateVar : PatClause vars (a :: todo) -> Core (PatClause vars todo)
      -- replace the name with the relevant variable on the rhs
      updateVar (MkPatClause pvars (MkInfo (PLoc n) prf fty :: pats) rhs)
          = pure $ MkPatClause (n :: pvars)
                        !(substInPats a (Local _ prf) pats)
                        (substName n (Local _ prf) rhs)
      -- match anything, name won't appear in rhs but need to update
      -- LHS pattern types based on what we've learned
      updateVar (MkPatClause pvars (MkInfo pat prf fty :: pats) rhs)
          = pure $ MkPatClause pvars
                        !(substInPats a (mkTerm vars pat) pats) rhs

  mixture : {a, vars, todo : _} ->
            {auto i : Ref PName Int} ->
            {auto c : Ref Ctxt Defs} ->
            {ps : List (PatClause vars (a :: todo))} ->
            Name ->
            Partitions ps ->
            Maybe (CaseTree vars) ->
            Core (Maybe (CaseTree vars))
  mixture fn (ConClauses cs rest) err
      = do fallthrough <- mixture fn rest err
           pure (Just !(conRule fn cs fallthrough))
  mixture fn (VarClauses vs rest) err
      = do fallthrough <- mixture fn rest err
           pure (Just !(varRule fn vs fallthrough))
  mixture fn {a} {todo} NoClauses err
      = pure err
-- 

mkPatClause : {auto c : Ref Ctxt Defs} ->
              Name ->
              (args : List Name) -> Term [] ->
              (List Pat, Term []) ->
              Core (PatClause args args)
mkPatClause fn args ty (ps, rhs)
    = maybe (throw (CaseCompile fn DifferingArgNumbers))
            (\eq =>
               do defs <- get Ctxt
                  nty <- nf defs [] ty
                  ns <- mkNames args ps eq (Just nty)
                  pure (MkPatClause [] ns
                          (rewrite sym (appendNilRightNeutral args) in
                                   (weakenNs args rhs))))
            (checkLengthMatch args ps)
  where
    mkNames : (vars : List Name) -> (ps : List Pat) ->
              LengthMatch vars ps -> Maybe (NF []) ->
              Core (NamedPats vars vars)
    mkNames [] [] NilMatch fty = pure []
    mkNames (arg :: args) (p :: ps) (ConsMatch eq) fty
        = do defs <- get Ctxt
             empty <- clearDefs defs
             fa_tys <- the (Core (Maybe _, ArgType _)) $
                case fty of
                     Nothing => pure (Nothing, CaseBuilder.Unknown)
                     Just (NBind _ (Pi _ farg) fsc) =>
                        pure (Just !(fsc defs (toClosure [] (Ref Bound arg))),
                                Known (embed {more = arg :: args}
                                          !(quote empty [] farg)))
                     Just t =>
                        pure (Nothing,
                                Stuck (embed {more = arg :: args}
                                        !(quote empty [] t)))
             pure (MkInfo p First (Builtin.snd fa_tys)
                      :: weaken !(mkNames args ps eq (Builtin.fst fa_tys)))

export
patCompile : {auto c : Ref Ctxt Defs} ->
             Name ->
             Term [] -> List (List Pat, Term []) ->
             Maybe (CaseTree []) ->
             Core (args ** CaseTree args)
patCompile fn ty [] def
    = maybe (pure ([] ** Unmatched "No definition"))
            (\e => pure ([] ** e))
            def
patCompile fn ty (p :: ps) def
    = do let ns = getNames 0 (fst p)
         pats <- mkPatClausesFrom ns (p :: ps)
         i <- newRef PName (the Int 0)
         cases <- match fn pats
                        (rewrite sym (appendNilRightNeutral ns) in
                                 map (TT.weakenNs ns) def)
         pure (_ ** cases)
  where
    mkPatClausesFrom : (args : List Name) ->
                       List (List Pat, Term []) ->
                       Core (List (PatClause args args))
    mkPatClausesFrom ns [] = pure []
    mkPatClausesFrom ns (p :: ps)
        = do p' <- mkPatClause fn ns ty p
             ps' <- mkPatClausesFrom ns ps
             pure (p' :: ps')

    getNames : Int -> List Pat -> List Name
    getNames i [] = []
    getNames i (x :: xs) = MN "arg" i :: getNames (i + 1) xs

toPatClause : {auto c : Ref Ctxt Defs} ->
              Name -> (Term [], Term []) ->
              Core (List Pat, Term [])
toPatClause n (lhs, rhs)
    = case getFnArgs lhs of
           (Ref Func fn, args)
              => do defs <- get Ctxt
                    if n == fn
                       then pure (map argToPat args, rhs)
                       else throw (GenericMsg ("Wrong function name in pattern LHS " ++ show (n, fn)))
           (f, args) => throw (GenericMsg "Not a function name in pattern LHS")

-- Assumption (given 'Term []) is that the pattern variables are
-- explicitly named. We'll assign de Bruijn indices when we're done, and
-- the names of the top level variables we created are returned in 'args'
export
simpleCase : {auto c : Ref Ctxt Defs} ->
             Name -> Term [] -> (def : Maybe (CaseTree [])) ->
             (clauses : List (Term [], Term [])) ->
             Core (args ** CaseTree args)
simpleCase fn ty def clauses
    = do ps <- traverse (toPatClause fn) clauses
         defs <- get Ctxt
         patCompile fn ty ps def

-- Converting a list of pattern clauses to a case tree.
-- Returns the generated argument names for the top level arguments,
-- and a case tree which deconstructs them
export
getPMDef : {auto c : Ref Ctxt Defs} ->
           Name -> -- name of function we're compiling
           Term [] -> -- function's type
           List Clause -> -- input clauses
           Core (args ** CaseTree args)
getPMDef fn ty []
    = do defs <- get Ctxt
         pure (!(getArgs 0 !(nf defs [] ty)) ** (Unmatched "No clauses"))
  where
    getArgs : Int -> NF [] -> Core (List Name)
    getArgs i (NBind x (Pi _ _) sc)
        = do defs <- get Ctxt
             sc' <- sc defs (toClosure [] Erased)
             pure (MN "arg" i :: !(getArgs i sc'))
    getArgs i _ = pure []
getPMDef fn ty clauses
    = do defs <- get Ctxt
         let cs = map (toClosed defs) (labelPat 0 clauses)
         (_ ** t) <- simpleCase fn ty Nothing cs
         pure (_ ** t)
  where
    labelPat : Int -> List a -> List (String, a)
    labelPat i [] = []
    labelPat i (x :: xs) = ("pat" ++ show i ++ ":", x) :: labelPat (i + 1) xs

    mkSubstEnv : Int -> String -> Env Term vars -> SubstEnv vars []
    mkSubstEnv i pname [] = Nil
    mkSubstEnv i pname (v :: vs)
       = Ref Bound (MN pname i) :: mkSubstEnv (i + 1) pname vs

    close : {vars : _} ->
            Env Term vars -> String -> Term vars -> Term []
    close {vars} env pname tm
        = substs (mkSubstEnv 0 pname env)
              (rewrite appendNilRightNeutral vars in tm)

    toClosed : Defs -> (String, Clause) -> (Term [], Term [])
    toClosed defs (pname, MkClause env lhs rhs)
          = (close env pname lhs, close env pname rhs)
