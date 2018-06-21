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

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternSynonyms #-}

import Control.Applicative
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.List
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans
import Control.Monad.Trans.Control
import Control.Monad.Writer
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S
import Data.Traversable
import Debug.Trace
import GHC.Exts (IsString(..))
import Text.Show.Pretty (pPrint)
import Data.Functor.Compose
import Data.Functor.Classes
import Data.List (intercalate)
import Data.Function

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
label e = fst $ runIdentity (runReaderT (runStateT (label' e) 0) M.empty)
 where
  freshLabel = do { l <- get; put (l+1); return l }
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
pretty (IfZero a b c) = "(ifZero " ++ pretty a ++ " then " ++ pretty b ++ " else " ++ pretty c ++ ")"
pretty (Lit i) = show i
pretty (Op2 op e1 e2) = "(" ++ pretty e1 ++ pop op ++ pretty e2 ++ ")"
  where pop Plus = " + "
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

instance MonadError String m => Value m Int ConcreteValue where
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
      Div -> if bi == 0
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

instance (MonadError String m, MonadPlus m) => Value m History AbstractValue where
  toInt i = return (AInt (ExactInt i))

  asClosure (AClosure env x e) = return (env, x, e)
  asClosure v = throwError (show v ++ " is not a closure")

  toClosure env x e = return (AClosure env x e)

  op2 Plus (AInt (ExactInt i)) (AInt (ExactInt j)) = return (AInt (ExactInt (i+j)))
  op2 Plus (AInt _) (AInt _) = return (AInt SomeInt)

  op2 Minus (AInt (ExactInt i)) (AInt (ExactInt j)) = return (AInt (ExactInt (i-j)))
  op2 Minus (AInt _) (AInt _) = return (AInt SomeInt)

  op2 Times (AInt (ExactInt i)) (AInt (ExactInt j)) = return (AInt (ExactInt (i*j)))
  op2 Times (AInt _) (AInt _) = return (AInt SomeInt)

  op2 Div (AInt _) (AInt (ExactInt 0)) = throwError "division by zero"
  op2 Div (AInt (ExactInt i)) (AInt (ExactInt j)) = return (AInt (ExactInt (i `div` j)))
  op2 Div (AInt _) (AInt _) = throwError "division by zero" `mplus` return (AInt SomeInt)

  op2 op a b = throwError ("type error " ++ show (op, a, b))

  isZero (AInt (ExactInt n)) = return (n == 0)
  isZero (AInt SomeInt) = return True `mplus` return False
  isZero x = throwError ("type error isZero: " ++ show x)

{- Stores -}

class MonadStore m a v | v -> a where
  find :: a -> m v
  ext :: a -> v -> m ()
  alloc :: Label -> m a

{-- concrete stores --}

type ConcreteStore = M.Map Int ConcreteValue

asInt :: MonadError String m => ConcreteValue -> m Int
asInt (VInt i) = return i
asInt v = throwError (show v ++ " is not an int")

instance (MonadError String m, MonadState ConcreteStore m) => MonadStore m Int ConcreteValue where
  find a = do
    maybeVal <- gets (M.lookup a)
    case maybeVal of
      Just v -> return v
      Nothing -> throwError ("unknown address " ++ show a)

  ext a v = modify (M.insert a v)

  alloc _ = gets M.size

{-- abstract stores --}

newtype History = History [Label]
  deriving (Eq, Ord)

instance Show History where
  show (History xs) = "\"@" ++ intercalate "," (map show xs) ++ "\""

type AbstractStore = M.Map History (S.Set AbstractValue)

instance MonadStore Abstract History AbstractValue where
  find a = do
    maybeVals <- gets (M.lookup a)
    case maybeVals of
      Just vals -> msum (map return (S.toList vals))
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

  alloc l = Abstract . lift $ asks (cons l)
    where cons l (History ls) = History (l:ls)

{- Interpreter -}

ev
  :: forall m a v
   . ( MonadError String m
     , MonadReader (Env a) m
     , MonadStore m a v
     , Value m a v
     )
  => (LExpr -> m v)
  -> LExpr
  -> m v
ev ev e = ev' e
 where
  ev' (Lit i) = toInt i
  ev' (Op2 op a b) = do
    av <- ev a
    bv <- ev b
    op2 op av bv
  ev' (IfZero a b c) = do
    isZeroA <- ev a >>= isZero
    if isZeroA then ev b else ev c
  ev' (Var x) = do
    env <- ask
    find (env M.! x)
  ev' (Lam x e) = do
    env <- ask
    toClosure env x e
  ev' (App _ a b) = do
    (env, x@(Name l _), e) <- ev a >>= asClosure @m @a @v
    bv <- ev b
    addr <- alloc @m @a @v l
    ext addr bv
    local (const (M.insert x addr env)) (ev e)
  ev' (Rec f@(Name l _) e) = do
    env <- ask
    addr <- alloc @m @a @v l
    ev <- local (M.insert f addr) (ev e)
    ext addr ev
    return ev

{- Concrete semantics -}

eval :: LExpr -> (Either String ConcreteValue, ConcreteStore)
eval e =
  runIdentity
    $ flip runStateT M.empty    -- store
    $ runExceptT                -- errors
    $ flip runReaderT M.empty   -- environment
    $ fix ev e

{- Trace semantics -}

evTell ev0 ev e = do
  v <- ev0 ev e
  env <- ask
  store <- get
  tell [(env, store, e, v)]
  return v

type ConcreteMachineState = (Env Int, ConcreteStore, LExpr, ConcreteValue)

evalCollect
  :: LExpr
  -> ((Either String ConcreteValue, ConcreteStore), [ConcreteMachineState])
evalCollect e =
  fix (evTell ev) e
    & flip runReaderT M.empty  -- environment
    & runExceptT               -- errors
    & flip runStateT M.empty   -- store
    & runWriterT               -- collected states
    & runIdentity

{- Abstract semantics -}

{-- history --}

class MonadHistory m where
  localHistory :: (History -> History) -> m a -> m a

evHistory
  :: MonadHistory m
  => Int
  -> ((LExpr -> m mValue) -> LExpr -> m mValue)
  -> (LExpr -> m mValue)
  -> LExpr
  -> m mValue
evHistory limit ev0 ev e
  | App l _ _ <- e = localHistory (extendHistory l) (ev0 ev e)
  | otherwise = ev0 ev e
 where
  extendHistory x (History xs) | length xs <= limit = History (x : xs)
                               | otherwise = History xs

{-- cache --}

type Configuration = (LExpr, AbstractEnv, AbstractStore)
type ValueAndStore = (AbstractValue, AbstractStore)
type Cache = M.Map Configuration (S.Set ValueAndStore)

-- We need to define a custom class because there can only be one instance of
-- MonadReader and MonadState per monad and those are already used by the env
-- and the store.
class MonadCache m where
  getCacheIn :: m Cache
  withLocalCacheIn :: Cache -> m a -> m a
  getCacheOut :: m Cache
  putCacheOut :: Cache -> m ()

modifyCacheOut f = do
  cache <- getCacheOut
  putCacheOut (f cache)

evCache
  :: ( MonadReader AbstractEnv m
     , MonadState AbstractStore m
     , MonadCache m
     , MonadPlus m
     )
  => ((LExpr -> m AbstractValue) -> LExpr -> m AbstractValue)
  -> (LExpr -> m AbstractValue)
  -> LExpr
  -> m AbstractValue
evCache ev0 ev e = do
  env <- ask
  store <- get
  let config = (e, env, store)
  cacheOut <- getCacheOut
  case M.lookup config cacheOut of
    Just entries -> do
      (configIn, storeIn) <- msum (map return (S.toList entries))
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

fixCache
  :: ( MonadReader AbstractEnv m
     , MonadState AbstractStore m
     , MonadCache m
     , MonadPlus m
     )
  => (LExpr -> m AbstractValue)
  -> LExpr
  -> m AbstractValue
fixCache ev e = do
  env <- ask
  store <- get
  let config = (e, env, store)
  cachePlus <- mlfp M.empty $ \cache -> do
    putCacheOut M.empty
    put store
    withLocalCacheIn cache (ev e)
    getCacheOut
  let entries = cachePlus M.! config
  msum
    $ map
        (\(value, store') -> do
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

type AbstractStack =
  ReaderT AbstractEnv
    (ReaderT History
      (ExceptT String
        (StateT AbstractStore
          (ListT
            (ReaderT Cache
              (StateT Cache Identity))))))

newtype Abstract a = Abstract { runAbstract :: AbstractStack a }
  deriving
    ( Functor
    , Applicative
    , Monad
    , MonadReader AbstractEnv
    , MonadState AbstractStore
    , MonadError String)

liftControl
  :: (MonadTransControl t, Monad m, Monad (t m))
  => (Run t -> m (StT t a))
  -> t m a
liftControl f = liftWith f >>= restoreT . return

-- We can't rely on GeneralizedNewtypeDeriving for the Alternative instance
-- because it would select the ExceptT instance instead of the ListT one.
instance Alternative Abstract where
  empty = Abstract . lift . lift . lift $ empty
  Abstract a <|> Abstract b = Abstract $
    liftControl $ \run1 ->     -- peel ReaderT
      liftControl $ \run2 ->   -- peel ExceptT
        liftControl $ \run3 -> -- peel SateT
          (run3 . run2 . run1) a <|> (run3 . run2 . run1) b

instance MonadPlus Abstract

instance MonadCache Abstract where
  getCacheIn = Abstract . lift . lift . lift . lift $ ask
  withLocalCacheIn c (Abstract m) = Abstract $
    liftControl $ \run1 ->
      liftControl $ \run2 ->
        liftControl $ \run3 ->
          liftControl $ \run4 ->
            local (const c) (run4 . run3 . run2 . run1 $ m)
  getCacheOut = Abstract . lift . lift . lift . lift . lift $ get
  putCacheOut c = Abstract . lift . lift . lift . lift . lift $ put c

instance MonadHistory Abstract where
  localHistory f a =
    Abstract $ liftControl $ \run -> local f (run (runAbstract a))

evalAbstract :: Int -> LExpr -> ([(Either String AbstractValue, AbstractStore)], Cache)
evalAbstract limit e =
  fixCache (fix (evCache (evHistory limit ev))) e
    & runAbstract
    & flip runReaderT M.empty      -- environment
    & flip runReaderT (History []) -- history
    & runExceptT                   -- errors
    & flip runStateT M.empty       -- store
    & runListT                     -- non-determinism
    & flip runReaderT M.empty      -- cache-in
    & flip runStateT M.empty       -- cache-out
    & runIdentity

{- Example -}

instance IsString UExpr where
  fromString = Var

a @: b = App () a b
a *: b = Op2 Times a b
a -: b = Op2 Minus a b
a +: b = Op2 Plus a b
a /: b = Op2 Div a b

letIn x e1 e2 = Lam x e2 @: e1

fact =
  Rec "fact" (Lam "n" (IfZero "n" (Lit 1) ("n" *: ("fact" @: ("n" -: Lit 1)))))

test =
  letIn "f" fact
  (Lam "x" (IfZero "x" (Lit 1 /: "x") ("f" @: "x")) @: Lit 4)

main = do
  printHeader "-- CONCRETE --"
  pPrint $ eval ltest
  printHeader "-- CONCRETE TRACE --"
  pPrint $ evalCollect ltest
  printHeader "-- ABSTRACT 3 --"
  pPrint $ S.fromList $ fst $ evalAbstract 3 ltest
  printHeader "-- ABSTRACT 6 --"
  pPrint $ S.fromList $ fst $ evalAbstract 6 ltest

  where printHeader s = putStrLn ("\n" ++ s ++ "\n")
        ltest = label test
