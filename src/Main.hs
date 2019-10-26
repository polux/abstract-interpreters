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
import qualified Control.Effect as E
import qualified Control.Effect.Error as E
import qualified Control.Effect.NonDet as E
import qualified Control.Effect.Reader as E
import qualified Control.Effect.State as E
import qualified Control.Effect.Writer as E
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.List
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans
import Control.Monad.Trans.Control
import Control.Monad.Writer
import Data.Foldable (asum)
import Data.Function
import Data.Functor.Classes
import Data.Functor.Compose
import Data.List (intercalate)
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S
import Data.Traversable
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
  E.run
    $ E.runReader
      (M.empty :: M.Map String Name)
    $ E.evalState (0 :: Label) (label' e)
  where
    freshLabel = do l <- E.get; E.put (l + 1); return l
    freshName x = Name <$> freshLabel <*> pure x
    label' (Var x) = Var <$> E.asks (M.! x)
    label' (App () e1 e2) = App <$> freshLabel <*> label' e1 <*> label' e2
    label' (Lam x e) = do
      name <- freshName x
      Lam name <$> E.local (M.insert x name) (label' e)
    label' (Rec x e) = do
      name <- freshName x
      Rec name <$> E.local (M.insert x name) (label' e)
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
  ( E.Member (E.Error String) sig,
    E.Carrier sig m
  ) =>
  Value m Int ConcreteValue
  where

  toInt i = return (VInt i)

  asClosure (VClosure env x e) = return (env, x, e)
  asClosure v = E.throwError (show v ++ " is not a closure")

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
          then E.throwError "division by zero"
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
  ( E.Member (E.Error String) sig,
    Alternative m,
    E.Carrier sig m
  ) =>
  Value m History AbstractValue
  where

  toInt i = return (AInt (ExactInt i))

  asClosure (AClosure env x e) = return (env, x, e)
  asClosure v = E.throwError (show v ++ " is not a closure")

  toClosure env x e = return (AClosure env x e)

  op2 Plus (AInt (ExactInt i)) (AInt (ExactInt j)) = return (AInt (ExactInt (i + j)))
  op2 Plus (AInt _) (AInt _) = return (AInt SomeInt)
  op2 Minus (AInt (ExactInt i)) (AInt (ExactInt j)) = return (AInt (ExactInt (i - j)))
  op2 Minus (AInt _) (AInt _) = return (AInt SomeInt)
  op2 Times (AInt (ExactInt i)) (AInt (ExactInt j)) = return (AInt (ExactInt (i * j)))
  op2 Times (AInt _) (AInt _) = return (AInt SomeInt)
  op2 Div (AInt _) (AInt (ExactInt 0)) = E.throwError "division by zero"
  op2 Div (AInt (ExactInt i)) (AInt (ExactInt j)) = return (AInt (ExactInt (i `div` j)))
  op2 Div (AInt _) (AInt _) = E.throwError "division by zero" <|> return (AInt SomeInt)
  op2 op a b = E.throwError ("type error " ++ show (op, a, b))

  isZero (AInt (ExactInt n)) = return (n == 0)
  isZero (AInt SomeInt) = return True <|> return False
  isZero x = E.throwError ("type error isZero: " ++ show x)

{- Stores -}

class MonadStore m a v | v -> a where

  find :: a -> m v

  ext :: a -> v -> m ()

  alloc :: Label -> m a

type Store a v = M.Map a v

{-- concrete stores --}

type ConcreteStore = Store Int ConcreteValue

asInt ::
  ( E.Member (E.Error String) sig,
    E.Carrier sig m
  ) =>
  ConcreteValue ->
  m Int
asInt (VInt i) = return i
asInt v = E.throwError (show v ++ " is not an int")

instance
  ( E.Member (E.Error String) sig,
    E.Member (E.State ConcreteStore) sig,
    E.Carrier sig m
  ) =>
  MonadStore m Int ConcreteValue
  where

  find a = do
    maybeVal <- E.gets (M.lookup a)
    case maybeVal of
      Just v -> return v
      Nothing -> E.throwError ("unknown address " ++ show a)

  ext a v = E.modify (M.insert a v)

  alloc _ = E.gets (M.size :: ConcreteStore -> Int)

{-- abstract stores --}

newtype History = History [Label]
  deriving (Eq, Ord)

instance Show History where
  show (History xs) = "\"@" ++ intercalate "," (map show xs) ++ "\""

type AbstractStore = Store History (S.Set AbstractValue)

instance
  ( E.Member (E.Error String) sig,
    E.Member (E.Reader History) sig,
    E.Member (E.State AbstractStore) sig,
    Alternative m,
    E.Carrier sig m
  ) =>
  MonadStore m History AbstractValue
  where

  find a = do
    maybeVals <- E.gets @AbstractStore (M.lookup a)
    case maybeVals of
      Just vals -> asum (map pure (S.toList vals))
      Nothing -> E.throwError ("unknown address " ++ show a)

  ext a v = do
    maybeVals <- E.gets (M.lookup a)
    let newVals = case maybeVals of
          Nothing -> S.singleton v
          Just vs -> S.insert (AInt SomeInt) (S.filter isAClosure vs)
    E.modify (M.insert a newVals)
    where
      isAClosure (AClosure _ _ _) = True
      isAClosure _ = False

  alloc l = E.asks @History (cons l)
    where
      cons l (History ls) = History (l : ls)

{- Garbage Collection -}

type Roots a = S.Set a

askRoots ::
  ( E.Member (E.Reader (Roots a)) sig,
    E.Carrier sig m
  ) =>
  m (Roots a)
askRoots = E.ask

extraRoots ::
  ( E.Member (E.Reader (Roots a)) sig,
    Ord a,
    E.Carrier sig m
  ) =>
  Roots a ->
  m b ->
  m b
extraRoots roots = E.local (roots `S.union`)

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
  ( E.Member (E.Reader (Roots a)) sig,
    E.Member (E.State (Store a av)) sig,
    Ord a,
    HasRoots v a,
    HasRoots av a,
    E.Carrier sig m
  ) =>
  ((LExpr -> m v) -> LExpr -> m v) ->
  (LExpr -> m v) ->
  LExpr ->
  m v
evGc ev0 ev e = do
  rs <- askRoots
  v <- ev0 ev e
  E.modify @(Store a av) (gc (S.union rs (roots v)))
  return v

{- Interpreter -}

ev ::
  forall sig m a v.
  ( E.Member (E.Error String) sig,
    E.Member (E.Reader (Env a)) sig,
    E.Member (E.Reader (Roots a)) sig,
    MonadStore m a v,
    Value m a v,
    HasRoots v a,
    Ord a,
    E.Carrier sig m
  ) =>
  (LExpr -> m v) ->
  LExpr ->
  m v
ev ev e = ev' e
  where
    ev' :: LExpr -> m v
    ev' (Lit i) = toInt i
    ev' (Op2 op a b) = do
      env <- E.ask @(Env a)
      av <- extraRoots (exprRoots b env) (ev a)
      bv <- extraRoots (roots @v @a av) (ev b)
      op2 op av bv
    ev' (IfZero a b c) = do
      env <- E.ask @(Env a)
      let newRooots = S.union (exprRoots b env) (exprRoots c env)
      av <- extraRoots newRooots (ev a)
      isZeroA <- isZero av
      ev (if isZeroA then b else c)
    ev' (Var x) = do
      env <- E.ask
      find (env M.! x)
    ev' (Lam x e) = do
      env <- E.ask
      toClosure env x e
    ev' (App _ a b) = do
      env <- E.ask @(Env a)
      av <- extraRoots (exprRoots b env) (ev a)
      bv <- extraRoots (roots @v @a av) (ev b)
      (env, x@(Name l _), e) <- asClosure @m @a @v av
      addr <- alloc @m @a @v l
      ext addr bv
      E.local (const (M.insert x addr env)) (ev e)
    ev' (Rec f@(Name l _) e) = do
      env <- E.ask @(Env a)
      addr <- alloc @m @a @v l
      ve <- E.local (M.insert f addr) (ev e)
      ext addr ve
      return ve

{- Concrete semantics -}

eval :: LExpr -> (ConcreteStore, Either String ConcreteValue)
eval e =
  fix (evGc @_ @_ @Int @_ @ConcreteValue ev) e
    & E.runReader (M.empty :: ConcreteEnv) -- environment
    & E.runReader (S.empty :: Roots Int) -- garbage collection roots
    & E.runError -- error
    & E.runState (M.empty :: ConcreteStore) -- store
    & E.run

{- Trace semantics -}

evTell ::
  forall sig m a v av.
  ( E.Member (E.Reader (Roots a)) sig,
    E.Member (E.State (Store a av)) sig,
    E.Member (E.Reader (Env a)) sig,
    E.Member (E.Writer [MachineState a v av]) sig,
    E.Carrier sig m
  ) =>
  ((LExpr -> m v) -> LExpr -> m v) ->
  (LExpr -> m v) ->
  LExpr ->
  m v
evTell ev0 ev e = do
  env <- E.ask @(Env a)
  roots <- askRoots
  store <- E.get @(Store a av)
  v <- ev0 ev e
  E.tell [MachineState env roots store e v]
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
    & E.runReader (M.empty :: ConcreteEnv) -- environment
    & E.runReader (S.empty :: Roots Int) -- garbage collection roots
    & E.runError -- error
    & E.runState (M.empty :: ConcreteStore) -- store
    & E.runWriter
    & E.run

{- Abstract semantics -}

{-- history --}

localHistory ::
  ( E.Member (E.Reader History) sig,
    E.Carrier sig m
  ) =>
  (History -> History) ->
  m a ->
  m a
localHistory = E.local @History

evHistory ::
  ( E.Member (E.Reader History) sig,
    E.Carrier sig m
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

getCacheIn :: (E.Member (E.Reader Cache) sig, E.Carrier sig m) => m Cache
getCacheIn = E.ask

withLocalCacheIn :: (E.Member (E.Reader Cache) sig, E.Carrier sig m) => Cache -> m a -> m a
withLocalCacheIn cache = E.local (const cache)

getCacheOut :: (E.Member (E.State Cache) sig, E.Carrier sig m) => m Cache
getCacheOut = E.get

putCacheOut :: (E.Member (E.State Cache) sig, E.Carrier sig m) => Cache -> m ()
putCacheOut = E.put

modifyCacheOut f = do
  cache <- getCacheOut
  putCacheOut (f cache)

evCache ::
  ( E.Member (E.Reader AbstractEnv) sig,
    E.Member (E.State AbstractStore) sig,
    E.Member (E.Reader (Roots History)) sig,
    E.Member (E.Reader Cache) sig,
    E.Member (E.State Cache) sig,
    E.Carrier sig m,
    Alternative m
  ) =>
  ((LExpr -> m AbstractValue) -> LExpr -> m AbstractValue) ->
  (LExpr -> m AbstractValue) ->
  LExpr ->
  m AbstractValue
evCache ev0 ev e = do
  env <- E.ask
  roots <- askRoots
  store <- E.get
  let config = (e, env, roots, store)
  cacheOut <- getCacheOut
  case M.lookup config cacheOut of
    Just entries -> do
      (configIn, storeIn) <- asum (map return (S.toList entries))
      E.put storeIn
      return configIn
    Nothing -> do
      cacheIn <- getCacheIn
      let entries = fromMaybe S.empty (M.lookup config cacheIn)
      putCacheOut (M.insertWith S.union config entries cacheOut)
      v <- ev0 ev e
      store' <- E.get
      modifyCacheOut (M.insertWith S.union config (S.singleton (v, store')))
      return v

fixCache ::
  ( E.Member (E.Reader AbstractEnv) sig,
    E.Member (E.State AbstractStore) sig,
    E.Member (E.Reader (Roots History)) sig,
    E.Member (E.Reader Cache) sig,
    E.Member (E.State Cache) sig,
    E.Carrier sig m,
    Alternative m
  ) =>
  (LExpr -> m AbstractValue) ->
  LExpr ->
  m AbstractValue
fixCache ev e = do
  env <- E.ask
  roots <- askRoots
  store <- E.get
  let config = (e, env, roots, store)
  cachePlus <- mlfp M.empty $ \cache -> do
    putCacheOut M.empty
    E.put store
    withLocalCacheIn cache (ev e)
    getCacheOut
  let entries = cachePlus M.! config
  asum
    $ map
      ( \(value, store') -> do
          E.put store'
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
    [ ( AbstractStore,
        ([AbstractMachineState], Either String AbstractValue)
      )
    ]
  )
evalAbstract limit e =
  fixCache (fix (evCache (evHistory limit (evGc @_ @_ @History @_ @(S.Set AbstractValue) (evTell @_ @_ @History @_ @(S.Set AbstractValue) ev))))) e
    & E.runReader (M.empty :: AbstractEnv) -- environment
    & E.runReader (S.empty :: Roots History) -- garbage collection roots
    & E.runReader (History []) -- history
    & E.runError @String -- error
    & E.runWriter @[AbstractMachineState] -- trace
    & E.runState (M.empty :: AbstractStore) -- store
    & E.runNonDet @[] -- non-determinism
    & E.runReader (M.empty :: Cache) -- cache-in
    & E.runState (M.empty :: Cache) -- cache-out
    & E.run

{- Example -}

instance IsString UExpr where
  fromString = Var

a @: b = App () a b

a *: b = Op2 Times a b

a -: b = Op2 Minus a b

a +: b = Op2 Plus a b

a /: b = Op2 Div a b

letIn x e1 e2 = Lam x e2 @: e1

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
  pPrint $ S.fromList $ snd $ evalAbstract 1 ltest
  printHeader "-- ABSTRACT 2 --"
  pPrint $ S.fromList $ snd $ evalAbstract 2 ltest
  where
    printHeader s = putStrLn ("\n" ++ s ++ "\n")
    ltest = label test
