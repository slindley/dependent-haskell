module Irr where

data Nat : Set where
  ze : Nat
  su : Nat -> Nat

Ar : Nat -> Set
Ar ze = Nat
Ar (su n) = Nat -> Ar n

data Vec (X : Set) : Nat -> Set where
  [] : Vec X ze
  _::_ : forall {n} -> X -> Vec X n -> Vec X (su n)

_+_ : Nat -> Nat -> Nat
ze + y = y
su x + y = su (x + y)

vtake : {X : Set}(m : Nat).(n : Nat) ->
        Vec X (m + n) -> Vec X m
vtake ze n _ = []
vtake (su m) n (x :: xs) = x :: vtake m n xs

{-
foo : .(n : Nat) -> Vec Nat n -> Ar n
foo n xs = ?
-}