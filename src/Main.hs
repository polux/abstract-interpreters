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

data BinOp = Plus | Minus | Times | Div
  deriving (Eq, Ord, Show)

data Expr
  = Var String
  | App Expr Expr
  | Lam String Expr
  | Rec String Expr
  | IfZero Expr Expr Expr
  | Lit Int
  | Op2 BinOp Expr Expr
  deriving (Eq, Ord, Show)

instance IsString Expr where
  fromString = Var

data ConcreteValue = VInt Int | VClosure (Env Int) String Expr
  deriving (Eq, Ord, Show)

type Env a = M.Map String a
type ConcreteStore = M.Map Int ConcreteValue
type AbstractStore = M.Map String (S.Set AbstractValue)

class Value m a v | v -> a where
  toInt :: Int -> m v
  asClosure :: v -> m (Env a, String, Expr)
  toClosure :: Env a -> String -> Expr -> m v
  op2 :: BinOp -> v -> v -> m v
  isZero :: v -> m Bool

class MonadStore m a v | v -> a where
  find :: a -> m v
  ext :: a -> v -> m ()
  alloc :: String -> m a

asInt :: MonadError String m => ConcreteValue -> m Int
asInt (VInt i) = return i
asInt v = throwError (show v ++ " is not an int")

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

instance (MonadError String m, MonadState ConcreteStore m) => MonadStore m Int ConcreteValue where
  find a = do
    maybeVal <- gets (M.lookup a)
    case maybeVal of
      Just v -> return v
      Nothing -> throwError ("unknown address " ++ show a)

  ext a v = modify (M.insert a v)

  alloc _ = gets M.size

data AbstractInt = SomeInt | ExactInt Int
  deriving (Eq, Ord, Show)
data AbstractValue = AInt AbstractInt | AClosure (Env String) String Expr
  deriving (Eq, Ord, Show)

instance (MonadError String m, MonadPlus m) => Value m String AbstractValue where
  toInt i = return (AInt (ExactInt i))

  asClosure (AClosure env x e) = return (env, x, e)
  asClosure v = throwError (show v ++ " is not a closure")

  toClosure env x e = return (AClosure env x e)

  op2 Plus (AInt _) (AInt _) = return (AInt SomeInt)
  op2 Minus (AInt _) (AInt _) = return (AInt SomeInt)
  op2 Times (AInt _) (AInt _) = return (AInt SomeInt)
  op2 Div (AInt _) (AInt ai)
    | ExactInt 0 <- ai = throwError "division by zero"
    | ExactInt _ <- ai = return (AInt SomeInt)
    | otherwise = throwError "division by zero" `mplus` return (AInt SomeInt)
  op2 op a b = throwError ("type error " ++ show (op, a, b))

  isZero (AInt (ExactInt n)) = return (n == 0)
  isZero (AInt SomeInt) = return True `mplus` return False
  isZero x = throwError ("type error isZero: " ++ show x)

instance ( MonadError String m
         , MonadState AbstractStore m
         , MonadPlus m
         )
      => MonadStore m String AbstractValue where
  find a = do
    maybeVals <- gets (M.lookup a)
    case maybeVals of
      Just vals -> msum (map return (S.toList vals))
      Nothing -> throwError ("unknown address " ++ show a)

  ext a v = modify (M.insertWith S.union a (S.singleton v))

  alloc x = return x

ev
  :: forall m a v
   . ( MonadError String m
     , MonadReader (Env a) m
     , MonadStore m a v
     , Value m a v
     )
  => (Expr -> m v)
  -> Expr
  -> m v
ev ev e = ev' e
 where
  ev' :: Expr -> m v
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
  ev' (App a b) = do
    (env, x, e) <- ev a >>= asClosure @m @a @v
    bv <- ev b
    addr <- alloc @m @a @v x
    ext addr bv
    local (const (M.insert x addr env)) (ev e)
  ev' (Rec f e) = do
    env <- ask
    addr <- alloc @m @a @v f
    ev <- local (M.insert f addr) (ev e)
    ext addr ev
    return ev

evTell ev0 ev e = do
  v <- ev0 ev e
  env <- ask
  store <- get
  tell [(env, store, e, v)]
  return v

type Configuration = (Expr, Env String, AbstractStore)
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
  :: ( MonadReader (Env String) m
     , MonadState AbstractStore m
     , MonadCache m
     , MonadPlus m
     )
  => ((Expr -> m AbstractValue) -> Expr -> m AbstractValue)
  -> (Expr -> m AbstractValue)
  -> Expr
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
  :: ( MonadReader (Env String) m
     , MonadState AbstractStore m
     , MonadCache m
     , MonadPlus m
     )
  => (Expr -> m AbstractValue)
  -> Expr
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

eval :: Expr -> (Either String ConcreteValue, ConcreteStore)
eval e =
  runIdentity
    $ flip runStateT M.empty    -- store
    $ runExceptT                -- errors
    $ flip runReaderT M.empty   -- environment
    $ fix ev e

type ConcreteMachineState = (Env Int, ConcreteStore, Expr, ConcreteValue)

evalCollect
  :: Expr
  -> ((Either String ConcreteValue, ConcreteStore), [ConcreteMachineState])
evalCollect e =
  runIdentity
    $ runWriterT               -- collected states
    $ flip runStateT M.empty   -- store
    $ runExceptT               -- errors
    $ flip runReaderT M.empty  -- environment
    $ fix (evTell ev) e

type AbstractStack =
  ReaderT (Env String)
    (ExceptT String
      (StateT AbstractStore
        (ListT
          (ReaderT Cache
            (StateT Cache Identity)))))

newtype Abstract a = Abstract { runAbstract :: AbstractStack a }
  deriving
    ( Functor
    , Applicative
    , Monad
    , MonadReader (Env String)
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

evalAbstract :: Expr -> ([(Either String AbstractValue, AbstractStore)], Cache)
evalAbstract e =
  runIdentity
    $ flip runStateT M.empty   -- cache-out
    $ flip runReaderT M.empty  -- cache-in
    $ runListT                 -- non-determinism
    $ flip runStateT M.empty   -- store
    $ runExceptT               -- errors
    $ flip runReaderT M.empty  -- environment
    $ runAbstract
    $ fixCache (fix (evCache ev)) e

a *: b = Op2 Times a b
a -: b = Op2 Minus a b
a +: b = Op2 Plus a b
a /: b = Op2 Div a b

letIn x e1 e2 = App (Lam x e2) e1

fact = Rec
  "fact"
  (Lam "n" (IfZero "n" (Lit 1) ("n" *: ("fact" `App` ("n" -: Lit 1)))))

test = letIn
  "f"
  fact
  (App
    (Lam "x" (IfZero (Var "x") (Lit 1 /: Var "x") (App (Var "f") (Var "x"))))
    (Lit 4)
  )

main = pPrint $ S.fromList $ fst $ evalAbstract test
