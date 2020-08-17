module Core.Normalise

import Core.CaseTree
import Core.Context
import Core.Env
import Core.TT
import Core.Value

import Data.Nat
import Data.Vect

-- A pair of a term and its normal form. This could be constructed either
-- from a term (via 'gnf') or a normal form (via 'glueBack') but the other
-- part will only be constructed when needed, because it's in Core.
public export
data Glued : List Name -> Type where
     MkGlue : Core (Term vars) -> 
              (Ref Ctxt Defs -> Core (NF vars)) -> Glued vars

export
getTerm : Glued vars -> Core (Term vars)
getTerm (MkGlue tm _) = tm

export
getNF : {auto c : Ref Ctxt Defs} -> Glued vars -> Core (NF vars)
getNF {c} (MkGlue _ nf) = nf c

Stack : List Name -> Type
Stack vars = List (Closure vars)

export
evalClosure : {free : _} -> Defs -> Closure free -> Core (NF free)

export
toClosure : Env Term outer -> Term outer -> Closure outer
toClosure env tm = MkClosure [] env tm

data CaseResult a
     = Result a
     | NoMatch -- case alternative didn't match anything
     | GotStuck -- alternative matched, but got stuck later
 
-- So that we can call 'eval' with new defs
evalTop : {free, vars : _} ->
          Defs -> Env Term free -> LocalEnv free vars ->
          Term (vars ++ free) -> Stack free -> Core (NF free)

parameters (defs : Defs)
  mutual
    eval : {free, vars : _} ->
           Env Term free -> LocalEnv free vars ->
           Term (vars ++ free) -> Stack free -> Core (NF free)
    eval env locs (Local idx prf) stk
        = evalLocal env idx prf stk locs
    eval env locs (Ref nt fn) stk
        = evalRef env nt fn stk (NApp (NRef nt fn) stk)
    eval {vars} {free} env locs (Meta name args) stk
        = evalMeta env name (map (MkClosure locs env) args) stk
    eval env locs (Bind x (Lam _ ty) scope) (thunk :: stk)
        = eval env (thunk :: locs) scope stk
    eval env locs (Bind x b scope) stk
        = do b' <- traverse (\tm => eval env locs tm []) b
             pure $ NBind x b'
                      (\defs', arg => evalTop defs' env (arg :: locs) scope stk)
    eval env locs (App fn arg) stk
        = eval env locs fn (MkClosure locs env arg :: stk)
    eval env locs TType stk = pure NType
    eval env locs Erased stk = pure NErased

    evalLocClosure : {free : _} ->
                     Env Term free ->
                     Stack free ->
                     Closure free ->
                     Core (NF free)
    evalLocClosure env stk (MkClosure locs' env' tm')
        = eval env' locs' tm' stk

    evalLocal : {free, vars : _} ->
                Env Term free ->
                (idx : Nat) -> (0 p : IsVar name idx (vars ++ free)) ->
                Stack free ->
                LocalEnv free vars ->
                Core (NF free)
    -- If it's one of the free variables, we are done
    -- (Idris 2 has Let bindings, which we'd need to check and evaluate here)
    evalLocal {vars = []} env idx prf stk locs
        = pure $ NApp (NLocal idx prf) stk
    evalLocal env Z First stk (x :: locs)
        = evalLocClosure env stk x
    evalLocal {vars = x :: xs} {free}
              env (S idx) (Later p) stk (_ :: locs)
        = evalLocal {vars = xs} env idx p stk locs

    evalMeta : {free : _} ->
               Env Term free ->
               Name -> List (Closure free) ->
               Stack free -> Core (NF free)
    evalMeta env nm args stk
        = evalRef env Func nm (args ++ stk) (NApp (NMeta nm args) stk)

    evalRef : {free : _} ->
              Env Term free ->
              NameType -> Name -> Stack free -> (def : Lazy (NF free)) ->
              Core (NF free)
    -- if it's a constructor, no need to look it up
    evalRef env (DataCon tag arity) fn stk def
        = pure $ NDCon fn tag arity stk
    evalRef env (TyCon tag arity) fn stk def
        = pure $ NTCon fn tag arity stk
    evalRef env Bound fn stk def
        = pure def
    evalRef env nt n stk def
        = do Just res <- lookupDef n defs
                  | Nothing => pure def
             evalDef env (definition res) stk def

    getCaseBound : List (Closure free) ->
                   (args : List Name) ->
                   LocalEnv free more ->
                   Maybe (LocalEnv free (args ++ more))
    getCaseBound []            []        loc = Just loc
    getCaseBound []            (_ :: _)  loc = Nothing -- mismatched arg length
    getCaseBound (arg :: args) []        loc = Nothing -- mismatched arg length
    getCaseBound (arg :: args) (n :: ns) loc = (arg ::) <$> getCaseBound args ns loc

    evalConAlt : {more, free : _} ->
                 Env Term free ->
                 LocalEnv free more ->
                 Stack free ->
                 (args : List Name) ->
                 List (Closure free) ->
                 CaseTree (args ++ more) ->
                 Core (CaseResult (NF free))
    evalConAlt env loc stk args args' sc
         = do let Just bound = getCaseBound args' args loc
                   | Nothing => pure GotStuck
              evalTree env bound stk sc

    tryAlt : {free, more : _} ->
             Env Term free ->
             LocalEnv free more ->
             Stack free -> NF free -> CaseAlt more ->
             Core (CaseResult (NF free))
    -- Ordinary constructor matching
    tryAlt {more} env loc stk (NDCon nm tag' arity args') (ConCase x tag args sc)
         = if tag == tag'
              then evalConAlt env loc stk args args' sc
              else pure NoMatch
    -- Default case matches against any *concrete* value
    tryAlt env loc stk val (DefaultCase sc)
         = if concrete val
              then evalTree env loc stk sc
              else pure GotStuck
      where
        concrete : NF free -> Bool
        concrete (NDCon _ _ _ _) = True
        concrete _ = False
    tryAlt _ _ _ _ _ = pure GotStuck

    findAlt : {args, free : _} ->
              Env Term free ->
              LocalEnv free args ->
              Stack free -> NF free -> List (CaseAlt args) ->
              Core (CaseResult (NF free))
    findAlt env loc stk val [] = pure GotStuck
    findAlt env loc stk val (x :: xs)
         = do Result val <- tryAlt env loc stk val x
                   | NoMatch => findAlt env loc stk val xs
                   | GotStuck => pure GotStuck
              pure (Result val)

    evalTree : {args, free : _} -> Env Term free -> LocalEnv free args ->
               Stack free -> CaseTree args ->
               Core (CaseResult (NF free))
    evalTree env loc stk (Case idx x _ alts)
      = do xval <- evalLocal env idx (varExtend x) [] loc
           -- Idris 2 also updates the local environment here, to save
           -- recomputing, but it involves a slightly trickier definition
           -- of closures, so we'll just carry on
           findAlt env loc stk xval alts
    evalTree env loc stk (STerm tm)
          = do res <- eval env loc (embed tm) stk
               pure (Result res)
    evalTree env loc stk _ = pure GotStuck

    -- Take arguments from the stack, as long as there's enough.
    -- Returns the arguments, and the rest of the stack
    takeFromStack : (arity : Nat) -> Stack free ->
                    Maybe (Vect arity (Closure free), Stack free)
    takeFromStack arity stk = takeStk arity stk []
      where
        takeStk : (remain : Nat) -> Stack free ->
                  Vect got (Closure free) ->
                  Maybe (Vect (got + remain) (Closure free), Stack free)
        takeStk {got} Z stk acc = Just (rewrite plusZeroRightNeutral got in
                                    reverse acc, stk)
        takeStk (S k) [] acc = Nothing
        takeStk {got} (S k) (arg :: stk) acc
           = rewrite sym (plusSuccRightSucc got k) in
                     takeStk k stk (arg :: acc)

    argsFromStack : (args : List Name) ->
                    Stack free ->
                    Maybe (LocalEnv free args, Stack free)
    argsFromStack [] stk = Just ([], stk)
    argsFromStack (n :: ns) [] = Nothing
    argsFromStack (n :: ns) (arg :: args)
         = do (loc', stk') <- argsFromStack ns args
              pure (arg :: loc', stk')

    evalDef : {free : _} ->
              Env Term free ->
              Def ->
              Stack free -> (def : Lazy (NF free)) ->
              Core (NF free)
    evalDef env (PMDef args tree) stk def
        = case argsFromStack args stk of
               Nothing => pure def
               Just (locs', stk') =>
                    do Result res <- evalTree env locs' stk' tree
                            | _ => pure def
                       pure res
    evalDef env _ stk def = pure def

evalClosure defs (MkClosure locs env tm)
    = eval defs env locs tm []

evalTop defs = eval defs

export
nf : {vars : _} ->
     Defs -> Env Term vars -> Term vars -> Core (NF vars)
nf defs env tm = eval defs env [] tm []

export
gnf : {vars : _} ->
      Env Term vars -> Term vars -> Glued vars
gnf env tm
    = MkGlue (pure tm)
             (\c => do defs <- get Ctxt
                       nf defs env tm)
export
gType : Glued vars
gType = MkGlue (pure TType) (const (pure NType))

export
data QVar : Type where

public export
interface Quote (tm : List Name -> Type) where
    quote : {vars : _} ->
            Defs -> Env Term vars -> tm vars -> Core (Term vars)
    quoteGen : {vars : _} ->
               Ref QVar Int -> Defs -> Env Term vars -> tm vars -> Core (Term vars)

    quote defs env tm
        = do q <- newRef QVar 0
             quoteGen q defs env tm

genName : {auto q : Ref QVar Int} -> String -> Core Name
genName n
    = do i <- get QVar
         put QVar (i + 1)
         pure (MN n i)

mutual
  quoteArgs : {bound, free : _} ->
              Ref QVar Int -> Defs -> Bounds bound ->
              Env Term free -> List (Closure free) ->
              Core (List (Term (bound ++ free)))
  quoteArgs q defs bounds env [] = pure []
  quoteArgs q defs bounds env (a :: args)
      = pure $ (!(quoteGenNF q defs bounds env !(evalClosure defs a)) ::
                !(quoteArgs q defs bounds env args))

  quoteHead : {bound, free : _} ->
              Ref QVar Int -> Defs ->
              Bounds bound -> Env Term free -> NHead free ->
              Core (Term (bound ++ free))
  quoteHead {bound} q defs bounds env (NLocal _ prf)
      = let MkVar prf' = addLater bound prf in
            pure $ Local _ prf'
    where
      addLater : {idx : _} ->
                 (ys : List Name) -> (0 p : IsVar n idx xs) ->
                 Var (ys ++ xs)
      addLater [] isv = MkVar isv
      addLater (x :: xs) isv
          = let MkVar isv' = addLater xs isv in
                MkVar (Later isv')
  quoteHead q defs bounds env (NRef Bound (MN n i))
      = case findName bounds of
             Just (MkVar p) => pure $ Local _ (varExtend p)
             Nothing => pure $ Ref Bound (MN n i)
    where
      findName : Bounds bound' -> Maybe (Var bound')
      findName None = Nothing
      findName (Add x (MN n' i') ns)
          = if i == i' -- this uniquely identifies it, given how we
                       -- generated the names, and is a faster test!
               then Just (MkVar First)
               else do MkVar p <-findName ns
                       Just (MkVar (Later p))
      findName (Add x _ ns)
          = do MkVar p <- findName ns
               Just (MkVar (Later p))
  quoteHead q defs bounds env (NRef nt n) = pure $ Ref nt n
  quoteHead q defs bounds env (NMeta n args)
      = do args' <- quoteArgs q defs bounds env args
           pure $ Meta n args'

  quoteBinder : {bound, free : _} ->
                Ref QVar Int -> Defs -> Bounds bound ->
                Env Term free -> Binder (NF free) ->
                Core (Binder (Term (bound ++ free)))
  quoteBinder q defs bounds env (Lam p ty)
      = do ty' <- quoteGenNF q defs bounds env ty
           pure (Lam p ty')
  quoteBinder q defs bounds env (Pi p ty)
      = do ty' <- quoteGenNF q defs bounds env ty
           pure (Pi p ty')
  quoteBinder q defs bounds env (PVar ty)
      = do ty' <- quoteGenNF q defs bounds env ty
           pure (PVar ty')
  quoteBinder q defs bounds env (PVTy ty)
      = do ty' <- quoteGenNF q defs bounds env ty
           pure (PVTy ty')

  quoteGenNF : {bound, vars : _} ->
               Ref QVar Int ->
               Defs -> Bounds bound ->
               Env Term vars -> NF vars -> Core (Term (bound ++ vars))
  quoteGenNF q defs bound env (NBind n b sc)
      = do var <- genName "qv"
           sc' <- quoteGenNF q defs (Add n var bound) env
                       !(sc defs (toClosure env (Ref Bound var)))
           b' <- quoteBinder q defs bound env b
           pure (Bind n b' sc')
  quoteGenNF q defs bound env (NApp f args)
      = do f' <- quoteHead q defs bound env f
           args' <- quoteArgs q defs bound env args
           pure $ apply f' args'
  quoteGenNF q defs bound env (NDCon n t ar args)
      = do args' <- quoteArgs q defs bound env args
           pure $ apply (Ref (DataCon t ar) n) args'
  quoteGenNF q defs bound env (NTCon n t ar args)
      = do args' <- quoteArgs q defs bound env args
           pure $ apply (Ref (TyCon t ar) n) args'
  quoteGenNF q defs bound env NErased = pure Erased
  quoteGenNF q defs bound env NType = pure TType

export
Quote NF where
  quoteGen q defs env tm = quoteGenNF q defs None env tm

export
Quote Term where
  quoteGen q defs env tm = pure tm

export
Quote Closure where
  quoteGen q defs env c = quoteGen q defs env !(evalClosure defs c)

export
glueBack : {vars : _} ->
           Defs -> Env Term vars -> NF vars -> Glued vars
glueBack defs env nf
    = MkGlue (do empty <- clearDefs defs
                 quote empty env nf)
             (const (pure nf))

export
normalise : {free : _} ->
            Defs -> Env Term free -> Term free -> Core (Term free)
normalise defs env tm = quote defs env !(nf defs env tm)

public export
interface Convert (tm : List Name -> Type) where
  convert : {vars : _} ->
            Defs -> Env Term vars ->
            tm vars -> tm vars -> Core Bool
  convGen : {vars : _} ->
            Ref QVar Int ->
            Defs -> Env Term vars ->
            tm vars -> tm vars -> Core Bool

  convert defs env tm tm'
      = do q <- newRef QVar 0
           convGen q defs env tm tm'


mutual
  allConv : {vars : _} ->
            Ref QVar Int -> Defs -> Env Term vars ->
            List (Closure vars) -> List (Closure vars) -> Core Bool
  allConv q defs env [] [] = pure True
  allConv q defs env (x :: xs) (y :: ys)
      = pure $ !(convGen q defs env x y) && !(allConv q defs env xs ys)
  allConv q defs env _ _ = pure False

  chkConvHead : {vars : _} ->
                Ref QVar Int -> Defs -> Env Term vars ->
                NHead vars -> NHead vars -> Core Bool
  chkConvHead q defs env (NLocal idx _) (NLocal idx' _) = pure $ idx == idx'
  chkConvHead q defs env (NRef _ n) (NRef _ n') = pure $ n == n'
  chkConvHead q defs env (NMeta n args) (NMeta n' args')
     = if n == n'
          then allConv q defs env args args'
          else pure False
  chkConvHead q defs env _ _ = pure False

  convBinders : {vars : _} ->
                Ref QVar Int -> Defs -> Env Term vars ->
                Binder (NF vars) -> Binder (NF vars) -> Core Bool
  convBinders q defs env (Pi ix tx) (Pi iy ty)
      = convGen q defs env tx ty
  convBinders q defs env (Lam ix tx) (Lam iy ty)
      = convGen q defs env tx ty
  convBinders q defs env bx by
      = pure False

  export
  Convert NF where
    convGen q defs env (NBind x b sc) (NBind x' b' sc')
        = do var <- genName "conv"
             let c = MkClosure [] env (Ref Bound var)
             bok <- convBinders q defs env b b'
             if bok
                then do bsc <- sc defs c
                        bsc' <- sc' defs c
                        convGen q defs env bsc bsc'
                else pure False
    -- Can also do eta conversion here, but let's skip that for simplicity
    -- EXERCISE (Medium): How would you add it? How would you test it?

    convGen q defs env (NApp val args) (NApp val' args')
        = if !(chkConvHead q defs env val val')
             then allConv q defs env args args'
             else pure False

    convGen q defs env (NDCon nm tag _ args) (NDCon nm' tag' _ args')
        = if tag == tag'
             then allConv q defs env args args'
             else pure False
    convGen q defs env (NTCon nm tag _ args) (NTCon nm' tag' _ args')
        = if nm == nm'
             then allConv q defs env args args'
             else pure False
    convGen q defs env NErased _ = pure True
    convGen q defs env _ NErased = pure True
    convGen q defs env NType NType = pure True
    convGen q defs env x y = pure False

  export
  Convert Term where
    convGen q defs env x y
        = convGen q defs env !(nf defs env x) !(nf defs env y)

  export
  Convert Closure where
    convGen q defs env x y
        = convGen q defs env !(evalClosure defs x) !(evalClosure defs y)

export
getValArity : {vars : _} ->
              Defs -> Env Term vars -> NF vars -> Core Nat
getValArity defs env (NBind x (Pi _ _) sc)
    = pure (S !(getValArity defs env !(sc defs (toClosure env Erased))))
getValArity defs env val = pure 0

export
getArity : {vars : _} ->
           Defs -> Env Term vars -> Term vars -> Core Nat
getArity defs env tm = getValArity defs env !(nf defs env tm)
