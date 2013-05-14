{-# LANGUAGE DataKinds, KindSignatures, GADTs, TypeFamilies, TypeOperators,
    RankNTypes, PolyKinds, ScopedTypeVariables, MultiParamTypeClasses #-}

module CharBox where

import Data.Monoid
import Control.Applicative
import Data.Foldable
import Data.Traversable

import Box

type CharMatrix = Matrix Char
type CharBox xy = Box CharMatrix xy

matrixChar :: Char -> (Natty x, Natty y) -> CharMatrix '(x, y)
matrixChar c (x, y) = Mat (vcopies y (vcopies x c))
                      -- alternatively we could do the presumably less efficient:
                      --   natter x (natter y (Mat (pure (pure c))))

renderCharBox' :: (Natty x, Natty y) -> CharBox '(x, y) -> CharMatrix '(x, y)
renderCharBox' _      (Stuff css)     = css
renderCharBox' (x, y) Clear           = matrixChar ' ' (x, y)
renderCharBox' (x, _) (Ver y1 t y2 b) =
  Mat (unMat (renderCharBox' (x, y1) t) `vappend` unMat (renderCharBox' (x, y2) b))
renderCharBox' (_, y) (Hor x1 l x2 r) =
  Mat (vcopies y vappend `vapp` unMat (renderCharBox' (x1, y) l) `vapp` unMat (renderCharBox' (x2, y) r))

renderCharBox :: (NATTY x, NATTY y) => CharBox '(x, y) -> CharMatrix '(x, y)
renderCharBox = renderCharBox' (natty, natty)

renderBox :: (NATTY x, NATTY y) => (forall xy.p xy -> CharMatrix xy) -> Box p '(x, y) -> CharMatrix '(x, y)
renderBox f b = renderCharBox (ebox (Stuff . f) b)

stringsOfCharMatrix :: CharMatrix '(x, y) -> [String]
stringsOfCharMatrix (Mat vs) = foldMap ((:[]) . foldMap (:[])) vs

boxChar :: Char -> (Natty x, Natty y) -> CharBox '(x, y)
boxChar c (x, y) = Stuff (matrixChar c (x, y))

boxZ :: CharBox '(Z, Z)
boxZ = emptyBox

boxS :: Vec x Char -> CharBox '(x, S Z)
boxS s = Stuff (Mat (pure s))

one  = SS SZ
type One = S Z

{- unused bounded stuff -}

{-

-- a bounded string (no more than n characters)
data BString (n :: Nat) where
  BNil  :: Natty n -> BString n
  BCons :: Char -> BString n -> BString (S n)

bmax :: BString n -> Natty n
bmax (BNil g)      = g
bmax (BCons _ cs)  = SS (bmax cs)


data Split (s :: Nat -> *) (t :: Nat -> *) (n :: Nat) where
  Split :: s l -> t r -> Split s t (l :+ r)

newtype FlipVec a n = FlipVec {unFlipVec :: Vec n a}

boundCharVec :: Natty d -> Vec n Char -> BString (n :+ d)
boundCharVec d V0        = BNil d
boundCharVec d (c :> cs) = BCons c (boundCharVec d cs)

splitBString :: BString w -> Split (FlipVec Char) Natty w
splitBString (BNil g)     = Split (FlipVec V0) g
splitBString (BCons c cs) = case splitBString cs of
                               Split (FlipVec cs') g -> Split (FlipVec (c :> cs')) g

boxOfBString :: BString w -> CharBox '(w, One)
boxOfBString s = case splitBString s of
                   Split (FlipVec cs) g -> Hor (vlength cs) (boxS cs) g Clear
-- boxOfBString (BNil  g)    = clear (g, one) 
-- boxOfBString (BCons c cs) = Hor one (boxChar c (one, one)) (bmax cs) (boxOfBString cs)

boxOfBStrings :: Vec h (BString w) -> CharBox '(w, h)
boxOfBStrings V0        = Clear
boxOfBStrings (s :> ss) = Ver one (boxOfBString s) (vlength ss) (boxOfBStrings ss)

weakenBString :: BString n -> BString (S n) 
weakenBString (BNil g)     = BNil (SS g)
weakenBString (BCons c cs) = BCons c (weakenBString cs)

-}