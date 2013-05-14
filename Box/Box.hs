{-# LANGUAGE
    DataKinds, PolyKinds,
    RankNTypes, GADTs, TypeOperators, FlexibleInstances #-}

module Box where

import Data.Monoid
import Control.Applicative
import Data.Foldable

import Nat
import Vec

data Box :: ((Nat, Nat) -> *) -> (Nat, Nat) -> * where
  Stuff :: p xy -> Box p xy
  Clear :: Box p xy
  Hor :: Natty x1 -> Box p '(x1, y) -> Natty x2 -> Box p '(x2, y) -> Box p '(x1 :+ x2, y)
  Ver :: Natty y1 -> Box p '(x, y1) -> Natty y2 -> Box p '(x, y2) -> Box p '(x, y1 :+ y2)

type s :-> t = forall i. s i -> t i

ebox :: (p :-> Box q) -> Box p :-> Box q
ebox f (Stuff b) = f b
ebox f Clear = Clear
ebox f (Hor x1 l x2 r) = Hor x1 (ebox f l) x2 (ebox f r)
ebox f (Ver y1 t y2 b) = Ver y1 (ebox f t) y2 (ebox f b)

class Cut (p :: (Nat, Nat) -> *) where
  horCut :: Natty xl -> Natty xr -> p '(xl :+ xr, y) -> (p '(xl, y), p '(xr, y))
  verCut :: Natty yt -> Natty yb -> p '(x, yt :+ yb) -> (p '(x, yt), p '(x, yb))

instance Cut p => Cut (Box p) where
  horCut xl xr (Stuff p) = (Stuff pl, Stuff pr) where (pl, pr) = horCut xl xr p
  horCut xl xr Clear = (Clear, Clear)
  horCut xl xr (Hor x1 b1 x2 b2) = case cmpCuts xl xr x1 x2 of
    LTCuts z -> let (ll, lr) = horCut xl (SS z) b1 in (ll, Hor (SS z) lr x2 b2)
    EQCuts   -> (b1, b2)
    GTCuts z -> let (rl, rr) = horCut (SS z) xr b2 in (Hor x1 b1 (SS z) rl, rr)
  horCut xl xr (Ver y1 tb y2 bb) = (Ver y1 tl y2 bl, Ver y1 tr y2 br)
    where (tl, tr) = horCut xl xr tb ; (bl, br) = horCut xl xr bb

  verCut yl yr (Stuff p) = (Stuff pl, Stuff pr) where (pl, pr) = verCut yl yr p
  verCut yl yr Clear = (Clear, Clear)
  verCut yl yr (Ver y1 b1 y2 b2) = case cmpCuts yl yr y1 y2 of
    LTCuts z -> let (tt, tb) = verCut yl (SS z) b1 in (tt, Ver (SS z) tb y2 b2)
    EQCuts   -> (b1, b2)
    GTCuts z -> let (bt, bb) = verCut (SS z) yr b2 in (Ver y1 b1 (SS z) bt, bb)
  verCut yl yr (Hor x1 tb x2 bb) = (Hor x1 tl x2 bl, Hor x1 tr x2 br)
    where (tl, tr) = verCut yl yr tb ; (bl, br) = verCut yl yr bb

instance Cut p => Monoid (Box p xy) where
  mempty = Clear
  mappend b Clear = b
  mappend Clear b' = b'
  mappend b@(Stuff _) _ = b
  mappend (Hor x1 b1 x2 b2) b' = Hor x1 (mappend b1 b1') x2 (mappend b2 b2')
    where (b1', b2') = horCut x1 x2 b'
  mappend (Ver y1 b1 y2 b2) b' = Ver y1 (mappend b1 b1') y2 (mappend b2 b2')
    where (b1', b2') = verCut y1 y2 b'

data Matrix :: * -> (Nat, Nat) -> * where
  Mat :: Vec y (Vec x a) -> Matrix a '(x, y)

instance Show x => Show (Matrix x '(m, n)) where
  show = show . (foldMap ((:[]) . foldMap (:[]))) . unMat

unMat :: Matrix a '(x,y) -> Vec y (Vec x a)
unMat (Mat m) = m

instance Cut (Matrix e) where
  horCut xl xr (Mat ess) = (Mat (fst <$> lrs), Mat (snd <$> lrs)) where
    lrs = vchop xl xr <$> ess
  verCut yt yb (Mat ess) = (Mat tess, Mat bess) where
    (tess, bess) = vchop yt yb ess

{- smart constructors for clear boxes -}
clear :: (Natty x, Natty y) -> Box p '(x, y)
clear (x, y) = Clear

emptyBox :: Box p '(Z, Z)
emptyBox = Clear

hGap :: Natty x -> Box p '(x, Z)
hGap x = Clear

vGap :: Natty y -> Box p '(Z, y)
vGap y = Clear

{- placing boxes -}

{-
--- lemmas about max ---

-- we wire this knowledge into the Cmp datatype

maxAddR :: forall x y z t.Natty x -> Natty y -> ((Max x (x :+ S y) ~ (x :+ S y)) => t) -> t
maxAddR SZ     y t = t
maxAddR (SS x) y t = maxAddR x y t

maxAddL :: forall x y z t.Natty x -> Natty y -> ((Max (x :+ S y) x ~ (x :+ S y)) => t) -> t
maxAddL x y t = maxAddR x y (maxSym x (x /+/ SS y) t)

maxRefl :: forall x y t.Natty x -> ((Max x x ~ x) => t) -> t
maxRefl SZ     t = t
maxRefl (SS x) t = maxRefl x t

maxSym :: forall x y t.Natty x -> Natty y -> ((Max x y ~ Max y x) => t) -> t
maxSym SZ SZ         t = t
maxSym SZ (SS y)     t = t
maxSym (SS x) SZ     t = t
maxSym (SS x) (SS y) t = maxSym x y t
------------------------
-}

-- place boxes horizontally
joinH :: (Natty x1, Natty y1) -> (Natty x2, Natty y2) ->
            Box p '(x1, y1) -> Box p '(x2, y2) -> Box p '(x1 :+ x2, Max y1 y2)
joinH (x1, y1) (x2, y2) b1 b2 =
  case cmp y1 y2 of
    LTNat n' -> Hor x1 (Ver y1 b1 (SS n') (clear (x1, SS n'))) x2 b2
    EQNat    -> Hor x1 b1 x2 b2
    GTNat n' -> Hor x1 b1 x2 (Ver y2 b2 (SS n') (clear (x2, SS n')))

-- place boxes vertically
joinV :: (Natty x1, Natty y1) -> (Natty x2, Natty y2) ->
            Box p '(x1, y1) -> Box p '(x2, y2) -> Box p '(Max x1 x2, y1 :+ y2)
joinV (x1, y1) (x2, y2) b1 b2 =
  case cmp x1 x2 of
    LTNat n' -> Ver y1 (Hor x1 b1 (SS n') (clear (SS n', y1))) y2 b2
    EQNat    -> Ver y1 b1 y2 b2
    GTNat n' -> Ver y1 b1 y2 (Hor x2 b2 (SS n') (clear (SS n', y2)))

{- cropping -}
type Size w h = (Natty w, Natty h)
type Point x y = (Natty x, Natty y)

type Region x y w h = (Point x y, Size w h)

cropper :: Cut p => Region x y w h -> Size s t -> Box p '(s, t) -> Box p '(w, h)
cropper ((x, y), (w, h)) (s, t) b =
  fit (s /-/ x, t /-/ y) (w, h) (clip (s, t) (x, y) b)

clip :: Cut p => Size w h -> Point x y -> Box p '(w, h) -> Box p '(w :- x, h :- y)
clip (w, h) (x, y) b = clipV (w /-/ x, h) y (clipH (w, h) x b)

clipH :: Cut p => Size w h -> Natty x -> Box p '(w, h) -> Box p '(w :- x, h)
clipH (w, h) x b =
  case cmp w x of
    GTNat d -> snd (horCut x (SS d) b)
    _       -> Clear

clipV :: Cut p => Size w h -> Natty y -> Box p '(w, h) -> Box p '(w, h :- y)
clipV (w, h) y b =
  case cmp h y of
    GTNat d -> snd (verCut y (SS d) b)
    _       -> Clear

fit :: Cut p => Size w1 h1 -> Size w2 h2 -> Box p '(w1, h1) -> Box p '(w2, h2)
fit (w1, h1) (w2, h2) b = fitV h1 h2 (fitH w1 w2 b)

fitH :: Cut p => Natty w1 -> Natty w2 -> Box p '(w1, h) -> Box p '(w2, h)
fitH w1 w2 b =
  case cmp w1 w2 of
    LTNat d -> Hor w1 b (SS d) Clear
    EQNat   -> b
    GTNat d -> fst (horCut w2 (SS d) b)

fitV :: Cut p => Natty h1 -> Natty h2 -> Box p '(w, h1) -> Box p '(w, h2)
fitV h1 h2 b =
  case cmp h1 h2 of
    LTNat d -> Ver h1 b (SS d) Clear
    EQNat   -> b
    GTNat d -> fst (verCut h2 (SS d) b)
