{-# LANGUAGE GADTs, DataKinds, KindSignatures #-}

module Wrap where

import Nat
import Vec
import Box
import CharBox

data WNat :: * where
  WNat :: NATTY n => Natty n -> WNat

wrapNat :: Int -> WNat
wrapNat 0 = WNat SZ
wrapNat n = case wrapNat (n-1) of
              WNat wn -> WNat (SS wn)

intOfNat :: Natty n -> Int
intOfNat SZ = 0
intOfNat (SS n) = 1 + intOfNat n

data WPoint :: * where
  WPoint :: Natty x -> Natty y -> WPoint

wrapPoint :: (Int, Int) -> WPoint
wrapPoint (x, y) =
  case (wrapNat x, wrapNat y) of
    (WNat x, WNat y) -> WPoint x y

data WCharBox :: * where
  WCharBox :: Size w h -> CharBox '(w, h) -> WCharBox

data WrappedVec a :: * where
  WVec :: Vec n a -> WrappedVec a

vecOfList :: [a] -> WrappedVec a
vecOfList []     = WVec V0
vecOfList (x:xs) = case vecOfList xs of
  WVec v -> WVec (x :> v)

charBoxOfString :: String -> WCharBox
charBoxOfString s = case vecOfList s of
  WVec v -> WCharBox (vlength v, one) (boxS v)

charBoxOfStrings :: [String] -> WCharBox
charBoxOfStrings []     = WCharBox (SZ, SZ) boxZ
charBoxOfStrings (s:ss) = case (charBoxOfString s, charBoxOfStrings ss) of
  (WCharBox (w1, h1) b1, WCharBox (w2, h2) b2) ->
    WCharBox
      (w1 `maxn` w2, h1 /+/ h2)
      (joinV (w1, h1) (w2, h2) b1 b2)
