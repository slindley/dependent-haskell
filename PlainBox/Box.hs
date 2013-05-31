{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Box where

import Data.Monoid

type Size = (Int, Int)
type Point = (Int, Int)
type Region = (Point, Size)

type Box a = (Size, Block a)
data Block a
  = Stuff a
  | Clear                    
  | Ver (Box a) (Box a)
  | Hor (Box a) (Box a)

class Cut a where
  horCut :: Int -> a -> (a, a)
  verCut :: Int -> a -> (a, a)

instance Cut a => Cut (Block a) where
  horCut m (Stuff p) = (Stuff p1, Stuff p2) where (p1, p2) = horCut m p
  horCut m Clear = (Clear, Clear)
  horCut m (Hor ((x1, y1), b1) ((x2, y2), b2))
    | m < x1  = let (b11, b12) = horCut m b1 in (b11, Hor ((x1-m, y1), b12) ((x2, y2), b2))
    | m == x1 = (b1, b2)
    | m > x1  = let (b21, b22) = horCut (m-x1) b2 in (Hor ((x1, y1), b1) ((m-x1, y2), b21), b22)
  horCut m (Ver (xy1, b1) (xy2, b2)) = (Ver (xy1, b11) (xy2, b21), Ver (xy1, b12) (xy2, b22))
    where (b11, b12) = horCut m b1
          (b21, b22) = horCut m b2

  verCut m (Stuff p) = (Stuff p1, Stuff p2) where (p1, p2) = verCut m p
  verCut m Clear = (Clear, Clear)
  verCut m (Ver ((x1, y1), b1) ((x2, y2), b2))
    | m < y1  = let (b11, b12) = verCut m b1 in (b11, Ver ((x1, y1-m), b12) ((x2, y2), b2))
    | m == y1 = (b1, b2)
    | m > y1  = let (b21, b22) = verCut (m-y1) b2 in (Ver ((x1, y1), b1) ((x2, m-y1), b21), b22)
  verCut m (Hor (xy1, b1) (xy2, b2)) = (Hor (xy1, b11) (xy2, b21), Hor (xy1, b12) (xy2, b22))
    where (b11, b12) = verCut m b1
          (b21, b22) = verCut m b2

instance Cut a => Cut (Box a) where
  horCut m ((w, h), b) = (((m, h), b1), ((w-m, h), b2)) where (b1, b2) = horCut m b
  verCut m ((w, h), b) = (((w, m), b1), ((w, h-m), b2)) where (b1, b2) = verCut m b

-- this doesn't really make sense
-- it is only correct if the sizes of the boxes match up
instance Cut a => Monoid (Block a) where
  mempty = Clear
  mappend b Clear = b
  mappend Clear b' = b'
  mappend b@(Stuff _) _ = b
  mappend (Hor (xy1@(x1, _), b1) (xy2@(x2, _), b2)) b' = Hor (xy1, mappend b1 b1') (xy2, mappend b2 b2')
    where (b1', b2') = horCut x1 b'
  mappend (Ver (xy1@(_, y1), b1) (xy2@(_, y2), b2)) b' = Ver (xy1, mappend b1 b1') (xy2, mappend b2 b2')
    where (b1', b2') = verCut y1 b'

-- this makes even less sense
instance Cut a => Monoid (Box a) where
  mempty = ((0, 0), Clear)
  mappend ((0, 0), b1) (xy2, b2) = (xy2, mappend b1 b2)
  mappend (xy1, b1)    (xy2, b2) = (xy1, mappend b1 b2)

clear :: Size -> Box a
clear xy = (xy, Clear)

hGap :: Int -> Box a
hGap x = clear (x, 0)

vGap :: Int -> Box a
vGap y = clear (0, y)

joinH :: Box a -> Box a -> Box a
joinH b1@((x1, y1), _) b2@((x2, y2), _)
  | y1 < y2
  = ((x1 + x2, y2), Hor ((x1, y2), Ver b1 ((x1, y2 - y1), Clear)) b2)
  | y1 == y2 = ((x1 + x2, y1), Hor b1 b2)
  | y1 > y2
  = ((x1 + x2, y1), Hor b1 ((x2, y1), Ver b2 ((x2, y1 - y2), Clear)))

joinV :: Box a -> Box a -> Box a
joinV b1@((x1, y1), _) b2@((x2, y2), _)
  | x1 < x2
  = ((x2, y1 + y2), Ver ((x2, y1), Hor b1 ((x2 - x1, y1), Clear)) b2)
  | x1 == x2 = ((x1, y1 + y2), Ver b1 b2)
  | x1 > x2
  = ((x1, y1 + y2), Ver b1 ((x1, y2), Hor b2 ((x1 - x2, y2), Clear)))

{- cropping -}
cropper :: Cut p => Region -> Box p -> Box p
cropper ((x, y), (w, h)) b =
  fit (w, h) (clip (x, y) b)

clip :: Cut p => Point -> Box p -> Box p
clip (x, y) b@((w, h), _) = clipV y (clipH x b)

clipH :: Cut p => Int -> Box p -> Box p
clipH x b@((w, h), _)
  | w > x = snd (horCut x b)
  | w <= x = ((x-w, h), Clear)

clipV :: Cut p => Int -> Box p -> Box p
clipV y b@((w, h), _)
  | h > y = snd (verCut y b)
  | h <= y = ((w, y-h), Clear)

fit :: Cut p => Size -> Box p -> Box p
fit (w, h) b = fitV h (fitH w b)

fitH :: Cut p => Int -> Box p -> Box p
fitH w2 box@((w1, h), _)
  | w1 < w2  = ((w2, h), Hor box ((w2-w1, h), Clear))
  | w1 == w2 = box
  | w1 > w2  = fst (horCut w2 box)

fitV :: Cut p => Int -> Box p -> Box p
fitV h2 box@((w, h1), _)
  | h1 < h2  = ((w, h2), Ver box ((w, h2-h1), Clear))
  | h1 == h2 = box
  | h1 > h2  = fst (verCut h2 box)
