{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

-- Copyright 2018 Google LLC
--
-- Licensed under the Apache License, Version 2.0 (the "License");
-- you may not use this file except in compliance with the License.
-- You may obtain a copy of the License at
--
--     https://www.apache.org/licenses/LICENSE-2.0
--
-- Unless required by applicable law or agreed to in writing, software
-- distributed under the License is distributed on an "AS IS" BASIS,
-- WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
-- See the License for the specific language governing permissions and
-- limitations under the License.

import Control.Applicative
import Control.Effect
import Control.Effect.Error
import Control.Effect.NonDet
import Control.Effect.Reader
import Control.Effect.State
import Control.Effect.Writer
import Data.Foldable (asum)
import Data.Function
import Data.List (intercalate)
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S
import qualified Data.Set.Monad as SM
import Debug.Trace
import GHC.Exts (IsString (..))
import Text.Show.Pretty (pPrint)

data BinOp = Plus | Minus | Times | Div
  deriving (Eq, Ord, Show)

data Expr n {- name -} l {- label -}
  = Var n
  | App l (Expr n l) (Expr n l)
  | Lam n (Expr n l)
  | Rec n (Expr n l)
  | IfZero (Expr n l) (Expr n l) (Expr n l)
  | Lit Int
  | Op2 BinOp (Expr n l) (Expr n l)
  deriving (Eq, Ord)

type Label = Int

data Name = Name Label String
  deriving (Eq, Ord)

type UExpr = Expr String ()

type LExpr = Expr Name Label

label :: UExpr -> LExpr
label e =
  run
    $ runReader
      (M.empty :: M.Map String Name)
    $ evalState (0 :: Label) (label' e)
  where
    freshLabel = do l <- get; put (l + 1); return l
    freshName x = Name <$> freshLabel <*> pure x
    label' (Var x) = Var <$> asks (M.! x)
    label' (App () e1 e2) = App <$> freshLabel <*> label' e1 <*> label' e2
    label' (Lam x e) = do
      name <- freshName x
      Lam name <$> local (M.insert x name) (label' e)
    label' (Rec x e) = do
      name <- freshName x
      Rec name <$> local (M.insert x name) (label' e)
    label' (IfZero e1 e2 e3) = IfZero <$> label' e1 <*> label' e2 <*> label' e3
    label' (Lit i) = return $ Lit i
    label' (Op2 op e1 e2) = Op2 op <$> label' e1 <*> label' e2

{- Pretty-printing -}

instance Show Name where
  show (Name l x) = x ++ "_" ++ show l

pretty :: LExpr -> String
pretty (Var x) = show x
pretty (App l t1 t2) = show l ++ ":(" ++ pretty t1 ++ " " ++ pretty t2 ++ ")"
pretty (Lam x t) = "(" ++ show x ++ " -> " ++ pretty t ++ ")"
pretty (Rec x t) = "(fix (" ++ show x ++ " -> " ++ pretty t ++ "))"
pretty (IfZero a b c) =
  "(ifZero "
    ++ pretty a
    ++ " then "
    ++ pretty b
    ++ " else "
    ++ pretty c
    ++ ")"
pretty (Lit i) = show i
pretty (Op2 op e1 e2) = "(" ++ pretty e1 ++ pop op ++ pretty e2 ++ ")"
  where
    pop Plus = " + "
    pop Minus = " - "
    pop Times = " * "
    pop Div = " / "

instance Show LExpr where
  show e = "\"" ++ pretty e ++ "\""

{- Values -}

type Env a = M.Map Name a

class Value m a v | v -> a where

  toInt :: Int -> m v

  asClosure :: v -> m (Env a, Name, LExpr)

  toClosure :: Env a -> Name -> LExpr -> m v

  op2 :: BinOp -> v -> v -> m v

  isZero :: v -> m Bool

{-- concrete values --}

type ConcreteEnv = Env Int

data ConcreteValue = VInt Int | VClosure ConcreteEnv Name LExpr
  deriving (Eq, Ord, Show)

instance
  ( Member (Error String) sig,
    Carrier sig m
  ) =>
  Value m Int ConcreteValue
  where

  toInt i = return (VInt i)

  asClosure (VClosure env x e) = return (env, x, e)
  asClosure v = throwError (show v ++ " is not a closure")

  toClosure env x e = return (VClosure env x e)

  op2 op a b = do
    ai <- asInt a
    bi <- asInt b
    case op of
      Plus -> return (VInt (ai + bi))
      Minus -> return (VInt (ai - bi))
      Times -> return (VInt (ai * bi))
      Div ->
        if bi == 0
          then throwError "division by zero"
          else return (VInt (ai `div` bi))

  isZero v = do
    vi <- asInt v
    return (vi == 0)

{-- abstract values --}

type AbstractEnv = Env History

data AbstractInt = SomeInt | ExactInt Int
  deriving (Eq, Ord, Show)

data AbstractValue = AInt AbstractInt | AClosure AbstractEnv Name LExpr
  deriving (Eq, Ord, Show)

instance
  ( Member (Error String) sig,
    Carrier sig m,
    Alternative m
  ) =>
  Value m History AbstractValue
  where

  toInt i = return (AInt (ExactInt i))

  asClosure (AClosure env x e) = return (env, x, e)
  asClosure v = throwError (show v ++ " is not a closure")

  toClosure env x e = return (AClosure env x e)

  op2 Plus (AInt (ExactInt i)) (AInt (ExactInt j)) = return (AInt (ExactInt (i + j)))
  op2 Plus (AInt _) (AInt _) = return (AInt SomeInt)
  op2 Minus (AInt (ExactInt i)) (AInt (ExactInt j)) = return (AInt (ExactInt (i - j)))
  op2 Minus (AInt _) (AInt _) = return (AInt SomeInt)
  op2 Times (AInt (ExactInt i)) (AInt (ExactInt j)) = return (AInt (ExactInt (i * j)))
  op2 Times (AInt _) (AInt _) = return (AInt SomeInt)
  op2 Div (AInt _) (AInt (ExactInt 0)) = throwError "division by zero"
  op2 Div (AInt (ExactInt i)) (AInt (ExactInt j)) = return (AInt (ExactInt (i `div` j)))
  op2 Div (AInt _) (AInt _) = throwError "division by zero" <|> return (AInt SomeInt)
  op2 op a b = throwError ("type error " ++ show (op, a, b))

  isZero (AInt (ExactInt n)) = return (n == 0)
  isZero (AInt SomeInt) = return True <|> return False
  isZero x = throwError ("type error isZero: " ++ show x)

{- Stores -}

class MonadStore m a v | v -> a where

  find :: a -> m v

  ext :: a -> v -> m ()

  alloc :: Label -> m a

type Store a v = M.Map a v

{-- concrete stores --}

type ConcreteStore = Store Int ConcreteValue

asInt ::
  ( Member (Error String) sig,
    Carrier sig m
  ) =>
  ConcreteValue ->
  m Int
asInt (VInt i) = return i
asInt v = throwError (show v ++ " is not an int")

instance
  ( Member (Error String) sig,
    Member (State ConcreteStore) sig,
    Carrier sig m
  ) =>
  MonadStore m Int ConcreteValue
  where

  find a = do
    maybeVal <- gets (M.lookup a)
    case maybeVal of
      Just v -> return v
      Nothing -> throwError ("unknown address " ++ show a)

  ext a v = modify (M.insert a v)

  alloc _ = gets (M.size :: ConcreteStore -> Int)

{-- abstract stores --}

newtype History = History [Label]
  deriving (Eq, Ord)

instance Show History where
  show (History xs) = "\"@" ++ intercalate "," (map show xs) ++ "\""

type AbstractStore = Store History (S.Set AbstractValue)

instance
  ( Member (Error String) sig,
    Member (Reader History) sig,
    Member (State AbstractStore) sig,
    Carrier sig m,
    Alternative m
  ) =>
  MonadStore m History AbstractValue
  where

  find a = do
    maybeVals <- gets @AbstractStore (M.lookup a)
    case maybeVals of
      Just vals -> asum (map pure (S.toList vals))
      Nothing -> throwError ("unknown address " ++ show a)

  ext a v = do
    maybeVals <- gets (M.lookup a)
    let newVals = case maybeVals of
          Nothing -> S.singleton v
          Just vs -> S.insert (AInt SomeInt) (S.filter isAClosure vs)
    modify (M.insert a newVals)
    where
      isAClosure (AClosure _ _ _) = True
      isAClosure _ = False

  alloc l = asks @History (cons l)
    where
      cons l (History ls) = History (l : ls)

{- Garbage Collection -}

type Roots a = S.Set a

askRoots ::
  ( Member (Reader (Roots a)) sig,
    Carrier sig m
  ) =>
  m (Roots a)
askRoots = ask

extraRoots ::
  ( Member (Reader (Roots a)) sig,
    Carrier sig m,
    Ord a
  ) =>
  Roots a ->
  m b ->
  m b
extraRoots roots = local (roots `S.union`)

fv :: Ord n => Expr n l -> S.Set n
fv (Lit _) = S.empty
fv (Op2 _ a b) = fv a `S.union` fv b
fv (IfZero a b c) = fv a `S.union` fv b `S.union` fv c
fv (Var x) = S.singleton x
fv (Lam x e) = S.delete x (fv e)
fv (App _ a b) = fv a `S.union` fv b
fv (Rec x e) = S.delete x (fv e)

class HasRoots e a where
  roots :: e -> Roots a

exprRoots :: Ord a => LExpr -> Env a -> Roots a
exprRoots e env = S.map (env M.!) (fv e)

instance HasRoots ConcreteValue Int where
  roots (VInt _) = S.empty
  roots (VClosure env n e) = exprRoots (Lam n e) env

instance HasRoots AbstractValue History where
  roots (AInt _) = S.empty
  roots (AClosure env n e) = exprRoots (Lam n e) env

instance (Ord v, HasRoots a v) => HasRoots (S.Set a) v where
  roots = S.unions . map roots . S.toList

gc :: (Ord a, HasRoots v a) => Roots a -> Store a v -> Store a v
gc addresses store = store `M.restrictKeys` reachable addresses addresses
  where
    reachable as seen
      | S.null as = seen
      | otherwise = reachable (as' S.\\ seen) (seen `S.union` as')
      where
        as' = S.unions [roots (store M.! a) | a <- S.toList as]

evGc ::
  forall sig m a v av.
  ( Member (Reader (Roots a)) sig,
    Member (State (Store a av)) sig,
    Carrier sig m,
    Ord a,
    HasRoots v a,
    HasRoots av a
  ) =>
  ((LExpr -> m v) -> LExpr -> m v) ->
  (LExpr -> m v) ->
  LExpr ->
  m v
evGc ev0 ev e = do
  rs <- askRoots
  v <- ev0 ev e
  modify @(Store a av) (gc (S.union rs (roots v)))
  return v

{- Interpreter -}

ev ::
  forall sig m a v.
  ( Member (Error String) sig,
    Member (Reader (Env a)) sig,
    Member (Reader (Roots a)) sig,
    Carrier sig m,
    MonadStore m a v,
    Value m a v,
    HasRoots v a,
    Ord a
  ) =>
  (LExpr -> m v) ->
  LExpr ->
  m v
ev ev e = ev' e
  where
    ev' :: LExpr -> m v
    ev' (Lit i) = toInt i
    ev' (Op2 op a b) = do
      env <- ask @(Env a)
      av <- extraRoots (exprRoots b env) (ev a)
      bv <- extraRoots (roots @v @a av) (ev b)
      op2 op av bv
    ev' (IfZero a b c) = do
      env <- ask @(Env a)
      let newRooots = S.union (exprRoots b env) (exprRoots c env)
      av <- extraRoots newRooots (ev a)
      isZeroA <- isZero av
      ev (if isZeroA then b else c)
    ev' (Var x) = do
      env <- ask
      find (env M.! x)
    ev' (Lam x e) = do
      env <- ask
      toClosure env x e
    ev' (App _ a b) = do
      env <- ask @(Env a)
      av <- extraRoots (exprRoots b env) (ev a)
      bv <- extraRoots (roots @v @a av) (ev b)
      (env, x@(Name l _), e) <- asClosure @m @a @v av
      addr <- alloc @m @a @v l
      ext addr bv
      local (const (M.insert x addr env)) (ev e)
    ev' (Rec f@(Name l _) e) = do
      env <- ask @(Env a)
      addr <- alloc @m @a @v l
      ve <- local (M.insert f addr) (ev e)
      ext addr ve
      return ve

{- Concrete semantics -}

eval :: LExpr -> (ConcreteStore, Either String ConcreteValue)
eval e =
  fix (evGc @_ @_ @Int @_ @ConcreteValue ev) e
    & runReader (M.empty :: ConcreteEnv) -- environment
    & runReader (S.empty :: Roots Int) -- garbage collection roots
    & runError -- error
    & runState (M.empty :: ConcreteStore) -- store
    & run

{- Trace semantics -}

evTell ::
  forall sig m a v av.
  ( Member (Reader (Roots a)) sig,
    Member (State (Store a av)) sig,
    Member (Reader (Env a)) sig,
    Member (Writer [MachineState a v av]) sig,
    Carrier sig m
  ) =>
  ((LExpr -> m v) -> LExpr -> m v) ->
  (LExpr -> m v) ->
  LExpr ->
  m v
evTell ev0 ev e = do
  env <- ask @(Env a)
  roots <- askRoots
  store <- get @(Store a av)
  v <- ev0 ev e
  tell [MachineState env roots store e v]
  return v

data MachineState a v av
  = MachineState
      { cmEnv :: Env a,
        cmRoots :: Roots a,
        cmStore :: Store a av,
        cmExpr :: LExpr,
        cmValue :: v
      }
  deriving (Ord, Eq, Show)

type ConcreteMachineState = MachineState Int ConcreteValue ConcreteValue

type AbstractMachineState = MachineState History AbstractValue (S.Set AbstractValue)

evalCollect ::
  LExpr ->
  ([ConcreteMachineState], (ConcreteStore, Either String ConcreteValue))
evalCollect e =
  fix
    ( evGc @_ @_ @Int @_ @ConcreteValue
        (evTell @_ @_ @Int @_ @ConcreteValue ev)
    )
    e
    & runReader (M.empty :: ConcreteEnv) -- environment
    & runReader (S.empty :: Roots Int) -- garbage collection roots
    & runError -- error
    & runState (M.empty :: ConcreteStore) -- store
    & runWriter
    & run

{- Abstract semantics -}

{-- history --}

localHistory ::
  ( Member (Reader History) sig,
    Carrier sig m
  ) =>
  (History -> History) ->
  m a ->
  m a
localHistory = local @History

evHistory ::
  ( Member (Reader History) sig,
    Carrier sig m
  ) =>
  Int ->
  ((LExpr -> m v) -> LExpr -> m v) ->
  (LExpr -> m v) ->
  LExpr ->
  m v
evHistory limit ev0 ev e
  | App l _ _ <- e = localHistory (extendHistory l) (ev0 ev e)
  | otherwise = ev0 ev e
  where
    extendHistory x (History xs)
      | length xs <= limit = History (x : xs)
      | otherwise = History xs

{-- cache --}

type Configuration = (LExpr, AbstractEnv, Roots History, AbstractStore)

type ValueAndStore = (AbstractValue, AbstractStore)

type Cache = M.Map Configuration (S.Set ValueAndStore)

getCacheIn :: (Member (Reader Cache) sig, Carrier sig m) => m Cache
getCacheIn = ask

withLocalCacheIn :: (Member (Reader Cache) sig, Carrier sig m) => Cache -> m a -> m a
withLocalCacheIn cache = local (const cache)

getCacheOut :: (Member (State Cache) sig, Carrier sig m) => m Cache
getCacheOut = get

putCacheOut :: (Member (State Cache) sig, Carrier sig m) => Cache -> m ()
putCacheOut = put

modifyCacheOut f = do
  cache <- getCacheOut
  putCacheOut (f cache)

evCache ::
  ( Member (Reader AbstractEnv) sig,
    Member (State AbstractStore) sig,
    Member (Reader (Roots History)) sig,
    Member (Reader Cache) sig,
    Member (State Cache) sig,
    Carrier sig m,
    Alternative m
  ) =>
  ((LExpr -> m AbstractValue) -> LExpr -> m AbstractValue) ->
  (LExpr -> m AbstractValue) ->
  LExpr ->
  m AbstractValue
evCache ev0 ev e = do
  env <- ask
  roots <- askRoots
  store <- get
  let config = (e, env, roots, store)
  cacheOut <- getCacheOut
  case M.lookup config cacheOut of
    Just entries -> do
      (configIn, storeIn) <- asum (map return (S.toList entries))
      put storeIn
      return configIn
    Nothing -> do
      cacheIn <- getCacheIn
      let entries = fromMaybe S.empty (M.lookup config cacheIn)
      putCacheOut (M.insertWith S.union config entries cacheOut)
      v <- ev0 ev e
      store' <- get
      modifyCacheOut (M.insertWith S.union config (S.singleton (v, store')))
      return v

fixCache ::
  ( Member (Reader AbstractEnv) sig,
    Member (State AbstractStore) sig,
    Member (Reader (Roots History)) sig,
    Member (Reader Cache) sig,
    Member (State Cache) sig,
    Carrier sig m,
    Alternative m
  ) =>
  (LExpr -> m AbstractValue) ->
  LExpr ->
  m AbstractValue
fixCache ev e = do
  env <- ask
  roots <- askRoots
  store <- get
  let config = (e, env, roots, store)
  cachePlus <- mlfp M.empty $ \cache -> do
    putCacheOut M.empty
    put store
    withLocalCacheIn cache (ev e)
    getCacheOut
  let entries = cachePlus M.! config
  asum
    $ map
      ( \(value, store') -> do
          put store'
          return value
      )
    $ S.toList entries

mlfp bot f = loop bot
  where
    loop x = do
      x' <- f x
      if x == x' then return x else loop x'

{-- abstract monad stack --}

evalAbstract ::
  Int ->
  LExpr ->
  ( Cache,
    SM.Set
      ( ( AbstractStore,
          ([AbstractMachineState], Either String AbstractValue)
        )
      )
  )
evalAbstract limit e =
  eval e
    & runReader (M.empty :: AbstractEnv) -- environment
    & runReader (S.empty :: Roots History) -- garbage collection roots
    & runReader (History []) -- history
    & runError @String -- error
    & runWriter @[AbstractMachineState] -- trace
    & runState (M.empty :: AbstractStore) -- store
    & runNonDet @SM.Set -- non-determinism
    & runReader (M.empty :: Cache) -- cache-in
    & runState (M.empty :: Cache) -- cache-out
    & run
  where
    eval =
      ev
        & evTell @_ @_ @History @_ @(S.Set AbstractValue)
        & evGc @_ @_ @History @_ @(S.Set AbstractValue)
        & evHistory limit
        & evCache
        & fix
        & fixCache

{- Example -}

instance IsString UExpr where
  fromString = Var

a @: b = App () a b

a *: b = Op2 Times a b

a -: b = Op2 Minus a b

a +: b = Op2 Plus a b

a /: b = Op2 Div a b

letIn x e1 e2 = Lam x e2 @: e1

fiblike :: UExpr
fiblike =
  Rec
    "fib"
    ( Lam
        "n"
        ( IfZero
            "n"
            (Lit 1)
            (("fib" @: ("n" -: Lit 1)) +: ("fib" @: ("n" -: Lit 1)))
        )
    )

fact :: UExpr
fact =
  Rec "fact" (Lam "n" (IfZero "n" (Lit 1) ("n" *: ("fact" @: ("n" -: Lit 1)))))

test =
  letIn
    "f"
    fact
    (Lam "x" (IfZero "x" (Lit 1 /: "x") ("f" @: "x")) @: Lit 4)

main = do
  printHeader "-- CONCRETE --"
  pPrint $ eval ltest
  printHeader "-- CONCRETE TRACE --"
  pPrint $ evalCollect ltest
  printHeader "-- ABSTRACT 1 --"
  pPrint $ snd $ evalAbstract 1 ltest
  printHeader "-- ABSTRACT 2 --"
  pPrint $ snd $ evalAbstract 2 ltest
  where
    printHeader s = putStrLn ("\n" ++ s ++ "\n")
    ltest = label test
