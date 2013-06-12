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

foo : .(n : Nat) -> Vec Nat n -> Ar n
foo n xs = ?