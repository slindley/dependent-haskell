{-# LANGUAGE DataKinds, KindSignatures, GADTs, TypeFamilies, TypeOperators,
    RankNTypes, PolyKinds, ScopedTypeVariables #-}

module CharBox where

import Data.Monoid
import Control.Applicative
import Data.Foldable
import Data.Traversable

import Box

type CharMatrix = Matrix Char
type CharBox xy = Box CharMatrix xy

unMat :: Matrix a '(x,y) -> Vec y (Vec x a)
unMat (Mat m) = m

matrixChar :: Char -> (Natty x, Natty y) -> CharMatrix '(x, y)
matrixChar c (x, y) = Mat (vcopies y (vcopies x c))
                      -- alternatively we could do the much less efficient:
                      --   natter x (natter y (Mat (pure (pure c))))

renderCharBox :: (Natty x, Natty y) -> CharBox '(x, y) -> CharMatrix '(x, y)
renderCharBox _      (Stuff css)     = css
renderCharBox (x, y) Clear           = matrixChar ' ' (x, y)
renderCharBox (x, _) (Ver y1 t y2 b) =
  Mat (unMat (renderCharBox (x, y1) t) `vappend` unMat (renderCharBox (x, y2) b))
renderCharBox (_, y) (Hor x1 l x2 r) =
  Mat (vcopies y vappend `vapp` unMat (renderCharBox (x1, y) l) `vapp` unMat (renderCharBox (x2, y) r))

renderCharBox' :: (NATTY x, NATTY y) => CharBox '(x, y) -> CharMatrix '(x, y)
renderCharBox' = renderCharBox (natty, natty)

renderBox :: (NATTY x, NATTY y) => (forall xy.p xy -> CharMatrix xy) -> Box p '(x, y) -> CharMatrix '(x, y)
renderBox f b = renderCharBox' (ebox (Stuff . f) b)

clear :: (Natty x, Natty y) -> Box p '(x, y)
clear (x, y) = Clear

emptyBox :: Box p '(Z, Z)
emptyBox = clear (Zy, Zy)

hGap :: Natty x -> Box p '(x, Z)
hGap x = clear (x, Zy)

vGap :: Natty y -> Box p '(Z, y)
vGap y = clear (Zy, y)

boxChar :: Char -> (Natty x, Natty y) -> CharBox '(x, y)
boxChar c (x, y) = Stuff (matrixChar c (x, y))

boxS :: Vec x Char -> CharBox '(x, S Z)
boxS s = Stuff (Mat (pure s))

type family Max (m :: Nat) (n :: Nat) :: Nat
type instance Max Z     n     = n
type instance Max (S m) Z     = S m
type instance Max (S m) (S n) = S (Max m n)

maxn :: Natty m -> Natty n -> Natty (Max m n)
maxn Zy     n      = n
maxn (Sy m) Zy     = Sy m
maxn (Sy m) (Sy n) = Sy (maxn m n)

--- lemmas about max ---
maxAddR :: forall x y z t.Natty x -> Natty y -> ((Max x (x :+ S y) ~ (x :+ S y)) => t) -> t
maxAddR Zy     y t = t
maxAddR (Sy x) y t = maxAddR x y t

maxAddL :: forall x y z t.Natty x -> Natty y -> ((Max (x :+ S y) x ~ (x :+ S y)) => t) -> t
maxAddL x y t = maxAddR x y (maxSym x (x /+/ Sy y) t)

maxRefl :: forall x y t.Natty x -> ((Max x x ~ x) => t) -> t
maxRefl Zy     t = t
maxRefl (Sy x) t = maxRefl x t

maxSym :: forall x y t.Natty x -> Natty y -> ((Max x y ~ Max y x) => t) -> t
maxSym Zy Zy         t = t
maxSym Zy (Sy y)     t = t
maxSym (Sy x) Zy     t = t
maxSym (Sy x) (Sy y) t = maxSym x y t
------------------------

-- place boxes horizontally
joinH' :: (Natty x1, Natty y1) -> (Natty x2, Natty y2) ->
            Box p '(x1, y1) -> Box p '(x2, y2) -> Box p '(x1 :+ x2, Max y1 y2)
joinH' (x1, y1) (x2, y2) b1 b2 =
  case cmp y1 y2 of
    EQNat ->
      maxRefl y1 (Hor x1 b1 x2 b2)
    LTNat n' ->
      maxAddR y1 n' (Hor x1 (Ver y1 b1 (Sy n') (clear (x1, Sy n'))) x2 b2)
    GTNat n' ->
      maxAddL y2 n' (Hor x1 b1 x2 (Ver y2 b2 (Sy n') (clear (x2, Sy n'))))
joinH :: (NATTY x1, NATTY y1, NATTY x2, NATTY y2) =>
           Box p '(x1, y1) -> Box p '(x2, y2) -> Box p '(x1 :+ x2, Max y1 y2)
joinH = joinH' (natty, natty) (natty, natty)

-- place boxes vertically
joinV' :: (Natty x1, Natty y1) -> (Natty x2, Natty y2) ->
            Box p '(x1, y1) -> Box p '(x2, y2) -> Box p '(Max x1 x2, y1 :+ y2)
joinV' (x1, y1) (x2, y2) b1 b2 =
  case cmp x1 x2 of
    EQNat    ->
      maxRefl x1 (Ver y1 b1 y2 b2)
    LTNat n' ->
      maxAddR x1 n' (Ver y1 (Hor x1 b1 (Sy n') (clear (Sy n', y1))) y2 b2)
    GTNat n' ->
      maxAddL x2 n' (Ver y1 b1 y2 (Hor x2 b2 (Sy n') (clear (Sy n', y2))))
joinV :: (NATTY x1, NATTY y1, NATTY x2, NATTY y2) =>
           Box p '(x1, y1) -> Box p '(x2, y2) -> Box p '(Max x1 x2, y1 :+ y2)
joinV = joinV' (natty, natty) (natty, natty)
