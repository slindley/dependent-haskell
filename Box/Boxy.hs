-- experimenting with replacing Hor and Ver with a single Jux constructor

{-# LANGUAGE
    DataKinds, PolyKinds, TypeFamilies,
    RankNTypes, GADTs, TypeOperators, FlexibleInstances #-}

module Boxy where

import Data.Monoid
import Control.Applicative
import Data.Foldable

import Nat
import Vec

{- dimensions -}
data Dimension = Hor | Ver
  deriving (Show, Eq)

data SDimension :: Dimension -> * where
  SHor :: SDimension Hor
  SVer :: SDimension Ver

type family Perp (d :: Dimension) :: Dimension
type instance Perp Hor = Ver
type instance Perp Ver = Hor

perp :: SDimension d -> SDimension (Perp d)
perp SHor = SVer
perp SVer = SHor

{- composition -}
-- Comp r d m
--   describes how to compose in dimension d with
--     r in dimension perp(d) fixed; and
--     m in dimension d
type family Comp (r :: Nat) (d :: Dimension) (m :: Nat) :: (Nat, Nat)
type instance Comp r Hor m = '(m, r)
type instance Comp r Ver m = '(r, m) 

{- projection -}
type family Proj (d :: Dimension) (s :: (Nat, Nat)) :: Nat
type instance Proj Hor '(w, h) = w
type instance Proj Ver '(w, h) = h

proj :: SDimension d -> Size w h -> Natty (Proj d '(w, h))
proj SHor (w, h) = w
proj SVer (w, h) = h

data Box :: ((Nat, Nat) -> *) -> (Nat, Nat) -> * where
  Stuff :: p wh -> Box p wh
  Clear :: Box p wh
  Jux :: Natty r -> SDimension d ->
           Natty m -> Box p (Comp r d m) ->
             Natty n -> Box p (Comp r d n) ->
               Box p (Comp r d (m :+ n))
--   Hor :: Natty w1 -> Box p '(w1, h) -> Natty w2 -> Box p '(w2, h) -> Box p '(w1 :+ w2, h)
--   Ver :: Natty h1 -> Box p '(w, h1) -> Natty h2 -> Box p '(w, h2) -> Box p '(w, h1 :+ h2)

type s :-> t = forall i. s i -> t i

ebox :: (p :-> Box q) -> Box p :-> Box q
ebox f (Stuff c)             = f c
ebox f Clear                 = Clear
ebox f (Jux r d m1 b1 m2 b2) = Jux r d m1 (ebox f b1) m2 (ebox f b2)

class Cut (p :: (Nat, Nat) -> *) where
  cut :: Natty r -> SDimension d ->
           Natty m -> Natty n ->
             p (Comp r d (m :+ n)) ->
               (p (Comp r d m), p (Comp r d n))

-- equal dimensions
cutEq :: (Cut p, (m :+ n) ~ (w1 :+ w2)) =>
           Natty r -> SDimension d ->
             Natty m -> Natty n ->
               Natty w1 -> Box p (Comp r d w1) ->
               Natty w2 -> Box p (Comp r d w2) ->
                 (Box p (Comp r d m), Box p (Comp r d n))
cutEq r d m n w1 b1 w2 b2 =
  case cmpCuts m n w1 w2 of
    LTCuts z  ->  let (b11, b12) = cut r d m (SS z) b1
                  in (b11, Jux r d (SS z) b12 w2 b2)
    EQCuts    ->  (b1, b2)
    GTCuts z  ->  let (b21, b22) = cut r d (SS z) n b2
                  in (Jux r d w1 b1 (SS z) b21, b22)

-- unequal dimensions
cutNeq d m n h1 b1 h2 b2 =
  (Jux m (perp d) h1 b11 h2 b21, Jux n (perp d) h1 b12 h2 b22)
  where (b11, b12) = cut h1 d m n b1
        (b21, b22) = cut h2 d m n b2

instance Cut p => Cut (Box p) where
  cut r d m n (Stuff p) = (Stuff p1, Stuff p2)  
    where (p1, p2) = cut r d m n p
  cut r d m n Clear = (Clear, Clear)
  cut r d m n (Jux _ d' w1 b1 w2 b2) =
    case (d, d') of
      (SHor, SHor) -> cutEq r SHor m n w1 b1 w2 b2
      (SHor, SVer) -> cutNeq SHor m n w1 b1 w2 b2
      (SVer, SHor) -> cutNeq SVer m n w1 b1 w2 b2
      (SVer, SVer) -> cutEq r SVer m n w1 b1 w2 b2

{- placing boxes -}
join' ::
  (Comp h1 d w1 ~ Comp w1 (Perp d) h1,
   Comp h1 d w2 ~ Comp w2 (Perp d) h1,
   Comp h2 d w1 ~ Comp w1 (Perp d) h2,
   Comp h2 d w2 ~ Comp w2 (Perp d) h2) =>
     SDimension d ->
       Natty w1 -> Natty h1 ->
         Natty w2 -> Natty h2 ->
           Box p (Comp h1 d w1) -> Box p (Comp h2 d w2) ->
             Box p (Comp (Max h1 h2) d (w1 :+ w2))
join' d w1 h1 w2 h2 b1 b2 =
  case cmp h1 h2 of
    LTNat n -> Jux (maxn h1 h2) d w1 (Jux w1 (perp d) h1 b1 (SS n) Clear) w2 b2
    EQNat   -> Jux (maxn h1 h2) d w1 b1 w2 b2
    GTNat n -> Jux (maxn h1 h2) d w1 b1 w2 (Jux w2 (perp d) h2 b2 (SS n) Clear)


-- place boxes next to each other
joinD :: SDimension d ->
           (Natty w1, Natty h1) ->
             (Natty w2, Natty h2) ->
               Box p (Comp h1 d w1) -> Box p (Comp h2 d w2) ->
                 Box p (Comp (Max h1 h2) d (w1 :+ w2))
joinD d (w1, h1) (w2, h2) b1 b2 =
  case d of
    SHor -> join' SHor w1 h1 w2 h2 b1 b2
    SVer -> join' SVer w1 h1 w2 h2 b1 b2

{- cropping -}
type Size w h = (Natty w, Natty h)
type Point x y = (Natty x, Natty y)
type Region x y w h = (Point x y, Size w h)

clipD :: Cut p =>
           SDimension d ->
             Size w h -> Natty x ->
               Box p (Comp (Proj (Perp d) '(w, h)) d (Proj d '(w, h))) ->
                 Box p (Comp (Proj (Perp d) '(w, h)) d (Proj d '(w, h) :- x))
clipD d s x b =
  case cmp (proj d s) x of
    GTNat z -> snd (cut (proj (perp d) s) d x (SS z) b)
    _       -> Clear

clip :: Cut p => Size w h -> Point x y -> Box p '(w, h) -> Box p '(w :- x, h :- y)
clip (w, h) (x, y) b = clipD SVer (w /-/ x, h) y (clipD SHor (w, h) x b)

fitD :: Cut p =>
  Natty h ->
    SDimension d ->
      Natty w1 -> Natty w2 ->
        Box p (Comp h d w1) -> Box p (Comp h d w2)
fitD h d w1 w2 b =
  case cmp w1 w2 of
    LTNat z -> Jux h d w1 b (SS z) Clear
    EQNat   -> b
    GTNat z -> fst (cut h d w2 (SS z) b)

fit :: Cut p => Size w1 h1 -> Size w2 h2 -> Box p '(w1, h1) -> Box p '(w2, h2)
fit (w1, h1) (w2, h2) b = fitD w2 SVer h1 h2 (fitD h1 SHor w1 w2 b)

crop :: Cut p => Region x y w h -> Size s t -> Box p '(s, t) -> Box p '(w, h)
crop ((x, y), (w, h)) (s, t) b =
  fit (s /-/ x, t /-/ y) (w, h) (clip (s, t) (x, y) b)


instance Cut p => Monoid (Box p wh) where
  mempty = Clear
  mappend b Clear = b
  mappend Clear b' = b'
  mappend b@(Stuff _) _ = b
  mappend (Jux h d w1 b1 w2 b2) b' = Jux h d w1 (mappend b1 b1') w2 (mappend b2 b2')
    where (b1', b2') = cut h d w1 w2 b'

data Matrix :: * -> (Nat, Nat) -> * where
  Mat :: Vec y (Vec x a) -> Matrix a '(x, y)

instance Show a => Show (Matrix a '(x, y)) where
  show = show . (foldMap ((:[]) . foldMap (:[]))) . unMat

unMat :: Matrix a '(x,y) -> Vec y (Vec x a)
unMat (Mat m) = m

instance Cut (Matrix e) where
  cut _ SHor m n (Mat ess) =
    (Mat (fst <$> ps), Mat (snd <$> ps)) where
      ps = vchop m n <$> ess
  cut _ SVer m n (Mat ess) = (Mat tess, Mat bess) where
    (tess, bess) = vchop m n ess

{- smart constructors for clear boxes -}
clear :: (Natty w, Natty h) -> Box p '(w, h)
clear (x, y) = Clear

emptyBox :: Box p '(Z, Z)
emptyBox = Clear

hGap :: Natty w -> Box p '(w, Z)
hGap _ = Clear

vGap :: Natty h -> Box p '(Z, h)
vGap _ = Clear


