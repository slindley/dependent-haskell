{- Nats Using the singleton library

     http://hackage.haskell.org/package/singletons
-}

{-# LANGUAGE
    DataKinds, PolyKinds,
    RankNTypes, GADTs, TypeFamilies, TypeOperators,
    ConstraintKinds,
    TemplateHaskell #-}

module Nat where

import Data.Singletons

data Nat = Z | S Nat

$(genSingletons [''Nat])

type Natty n = SNat n
type NATTY = SingI

natty :: NATTY n => Sing n
natty = sing

-- natter effectively converts an explicit SNat to an implicit NATTY
natter :: SNat x -> (NATTY x => t) -> t
natter x b = case singInstance x of SingInstance -> b

{- plus -}
$(singletons [d|
  plus :: Nat -> Nat -> Nat
  Z     `plus` n = n
  (S m) `plus` n = S (m `plus` n)|])

type m :+ n = m `Plus` n
(/+/) = sPlus

{- minus -}
$(singletons [d|
  minus :: Nat -> Nat -> Nat
  Z     `minus` n     = Z
  (S m) `minus` Z     = S m
  (S m) `minus` (S n) = m `minus` n|])

type m :- n = m `Minus` n
(/-/) = sMinus

{- max -}
$(singletons [d|
  maxNat :: Nat -> Nat -> Nat
  maxNat Z     n     = n
  maxNat (S m) Z     = S m
  maxNat (S m) (S n) = S (maxNat m n)|])

type Max m n = MaxNat m n
maxn = sMaxNat

{- min -}
$(singletons [d|
  minNat :: Nat -> Nat -> Nat
  minNat Z     Z     = Z
  minNat Z     (S n) = Z
  minNat (S m) Z     = Z
  minNat (S m) (S n) = S (minNat m n)|])

type Min m n = MinNat m n
minn = sMinNat

data Cmp :: Nat -> Nat -> * where
  LTNat :: (NATTY z, (x :+ S z) ~ y,          Max x y ~ y, (x :- y) ~ Z)   => SNat z -> Cmp x y
  EQNat :: (          x         ~ y,          Max x y ~ x, (x :- y) ~ Z)   =>           Cmp x y
  GTNat :: (NATTY z, x          ~ (y :+ S z), Max x y ~ x, (x :- y) ~ S z) => SNat z -> Cmp x y

cmp :: SNat x -> SNat y -> Cmp x y
cmp SZ     SZ     = EQNat
cmp SZ     (SS y) = LTNat y
cmp (SS x) SZ     = GTNat x
cmp (SS x) (SS y) = case cmp x y of
  LTNat z -> LTNat z
  EQNat   -> EQNat
  GTNat z -> GTNat z

data CmpCuts :: Nat -> Nat -> Nat -> Nat -> * where
  LTCuts :: NATTY b => SNat b -> CmpCuts a (S b :+ c) (a :+ S b) c
  EQCuts :: CmpCuts a b a b
  GTCuts :: NATTY b => SNat b -> CmpCuts (a :+ S b) c a (S b :+ c)

cmpCuts :: ((a :+ b) ~ (c :+ d)) => SNat a -> SNat b -> SNat c -> SNat d -> CmpCuts a b c d
cmpCuts SZ b SZ     d  = EQCuts
cmpCuts SZ b (SS c) d  = LTCuts c
cmpCuts (SS a) b SZ d  = GTCuts a
cmpCuts (SS a) b (SS c) d = case cmpCuts a b c d of
  LTCuts z -> LTCuts z
  EQCuts   -> EQCuts
  GTCuts z -> GTCuts z

{-
leftCan :: forall a b c t. ((a :+ b) ~ (a :+ c)) => SNat a -> SNat b -> SNat c -> ((b ~ c) => t) -> t
leftCan SZ b c t = t
leftCan (SS a) b c t = leftCan a b c t

assocLR :: forall l a b c t. (l ~ ((a :+ b) :+ c)) => SNat a -> SNat b -> SNat c -> ((l ~ (a :+ (b :+ c))) => t) -> t
assocLR SZ b c t = t
assocLR (SS a) b c t = assocLR a b c t
-}

