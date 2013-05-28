{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module CharBox where

import Box

type CharMatrix = [[Char]]
type CharBox = Box CharMatrix

matrixChar :: Char -> Size -> CharMatrix
matrixChar c (x, y) = replicate y (replicate x c)

renderCharBox :: CharBox -> CharMatrix
renderCharBox (_, Stuff css) = css
renderCharBox ((x, y), Clear) = matrixChar ' ' (x, y)
renderCharBox (_, Ver b1 b2)     =
  renderCharBox b1 ++ renderCharBox b2
renderCharBox (_, Hor b1 b2) =
  zipWith (++) (renderCharBox b1) (renderCharBox b2)

instance Cut CharMatrix where
  horCut m css = (map (take m) css, map (drop m) css)
  verCut m css = (take m css, drop m css)
