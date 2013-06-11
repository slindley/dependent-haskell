{-# LANGUAGE DataKinds, TypeOperators,
    RankNTypes, GADTs #-}

module CharBox where

import Control.Applicative
import Data.Foldable

import Nat
import Vec
import Box

type CharMatrix = Matrix Char
type CharBox wh = Box CharMatrix wh

-- The call to |natter| here is necessary if Natty does not include a
-- |NATTY| constraint, but can be ommitted if it does.
idMatrix :: Natty n -> Matrix Int '(n, n)
idMatrix (SS n) = natter n (Mat ((1 :> pure 0) :> ((0 :>) <$> (unMat (idMatrix n)))))
idMatrix SZ     = Mat V0

matrixChar :: Char -> (Natty w, Natty h) -> CharMatrix '(w, h)
matrixChar c (w, h) = Mat (vcopies h (vcopies w c))
                      -- alternatively we could do the presumably less efficient:
                      --   natter w (natter h (Mat (pure (pure c))))

renderCharBox :: Size w h -> CharBox '(w, h) -> CharMatrix '(w, h)
renderCharBox _      (Stuff css)     = css
renderCharBox (w, h) Clear           = matrixChar ' ' (w, h)
renderCharBox (w, _) (Ver h1 b1 h2 b2) =
  Mat (unMat (renderCharBox (w, h1) b1) `vappend` unMat (renderCharBox (w, h2) b2))
renderCharBox (_, h) (Hor w1 b1 w2 b2) =
  Mat (vcopies h vappend `vapp` unMat (renderCharBox (w1, h) b1) `vapp` unMat (renderCharBox (w2, h) b2))

renderBox :: (NATTY w, NATTY h) => (forall wh.p wh -> CharMatrix wh) -> Box p '(w, h) -> CharMatrix '(w, h)
renderBox f b = renderCharBox (natty, natty) (ebox (Stuff . f) b)

stringsOfCharMatrix :: CharMatrix wh -> [String]
stringsOfCharMatrix (Mat vs) = foldMap ((:[]) . foldMap (:[])) vs

boxChar :: Char -> Size w h -> CharBox '(w, h)
boxChar c s = Stuff (matrixChar c s)

boxZ :: CharBox '(Z, Z)
boxZ = emptyBox

boxS :: Vec m Char -> CharBox '(m, S Z)
boxS s = Stuff (Mat (pure s))

one  = SS SZ
type One = S Z

