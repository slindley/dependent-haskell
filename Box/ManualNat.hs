{- Nats using manually encoded singletons and type families -}

{-# LANGUAGE
    DataKinds, PolyKinds,
    RankNTypes, GADTs, TypeFamilies, TypeOperators
  #-}

module Nat where

data Nat = Z | S Nat

data Natty :: Nat -> * where
  SZ :: Natty Z
  SS :: Natty n -> Natty (S n)

class NATTY (n :: Nat) where
  natty :: Natty n

instance NATTY Z where
  natty = SZ

instance NATTY n => NATTY (S n) where
  natty = SS natty

-- natter effectively converts an explicit Natty to an implicit NATTY
natter :: Natty n -> (NATTY n => t) -> t
natter SZ     t = t
natter (SS n) t = natter n t

{- plus -}
type family (m :: Nat) :+ (n :: Nat) :: Nat
type instance Z :+ n = n
type instance S m :+ n = S (m :+ n)

(/+/) :: Natty m -> Natty n -> Natty (m :+ n)
SZ /+/ n = n
SS m /+/ n = SS (m /+/ n)

{- minus -}
type family (m :: Nat) :- (n :: Nat) :: Nat
type instance Z   :- n   = Z
type instance S m :- Z   = S m
type instance S m :- S n = (m :- n)

(/-/) :: Natty m -> Natty n -> Natty (m :- n)
SZ   /-/ n    = SZ
SS m /-/ SZ   = SS m
SS m /-/ SS n = m /-/ n

{- max -}
type family Max (m :: Nat) (n :: Nat) :: Nat
type instance Max Z     n     = n
type instance Max (S m) Z     = S m
type instance Max (S m) (S n) = S (Max m n)

maxn :: Natty m -> Natty n -> Natty (Max m n)
maxn SZ     n      = n
maxn (SS m) SZ     = SS m
maxn (SS m) (SS n) = SS (maxn m n)


data Cmp :: Nat -> Nat -> * where
  LTNat :: ((x :+ S z) ~ y,          Max x y ~ y, (x :- y) ~ Z)   => Natty z -> Cmp x y
  EQNat :: (x          ~ y,          Max x y ~ x, (x :- y) ~ Z)   =>            Cmp x y
  GTNat :: (x          ~ (y :+ S z), Max x y ~ x, (x :- y) ~ S z) => Natty z -> Cmp x y

cmp :: Natty x -> Natty y -> Cmp x y
cmp SZ     SZ     = EQNat
cmp SZ     (SS y) = LTNat y
cmp (SS x) SZ     = GTNat x
cmp (SS x) (SS y) = case cmp x y of
  LTNat z -> LTNat z
  EQNat   -> EQNat
  GTNat z -> GTNat z

data CmpCuts :: Nat -> Nat -> Nat -> Nat -> * where
  LTCuts :: Natty b -> CmpCuts a (S b :+ c) (a :+ S b) c
  EQCuts :: CmpCuts a b a b
  GTCuts :: Natty b -> CmpCuts (a :+ S b) c a (S b :+ c)

cmpCuts :: ((a :+ b) ~ (c :+ d)) => Natty a -> Natty b -> Natty c -> Natty d -> CmpCuts a b c d
cmpCuts SZ b SZ     d  = EQCuts
cmpCuts SZ b (SS c) d  = LTCuts c
cmpCuts (SS a) b SZ d  = GTCuts a
cmpCuts (SS a) b (SS c) d = case cmpCuts a b c d of
  LTCuts z -> LTCuts z
  EQCuts   -> EQCuts
  GTCuts z -> GTCuts z

{-
leftCan :: forall a b c t. ((a :+ b) ~ (a :+ c)) => Natty a -> Natty b -> Natty c -> ((b ~ c) => t) -> t
leftCan SZ b c t = t
leftCan (SS a) b c t = leftCan a b c t

assocLR :: forall l a b c t. (l ~ ((a :+ b) :+ c)) => Natty a -> Natty b -> Natty c -> ((l ~ (a :+ (b :+ c))) => t) -> t
assocLR SZ b c t = t
assocLR (SS a) b c t = assocLR a b c t
-}

{- Min -}
type family Min (m :: Nat) (n :: Nat) :: Nat
type instance Min Z     Z     = Z
type instance Min Z     (S n) = Z
type instance Min (S m) Z     = Z
type instance Min (S m) (S n) = S (Min m n)

minn :: Natty m -> Natty n -> Natty (Min m n)
minn SZ     SZ     = SZ
minn SZ     (SS n) = SZ
minn (SS m) SZ     = SZ
minn (SS m) (SS n) = SS (minn m n)
