{-# LANGUAGE DataKinds, KindSignatures, GADTs, TypeFamilies, TypeOperators,
    RankNTypes, PolyKinds #-}

module Cursor where

import Nat
import Vec
import Box
import CharBox

data WrappedNat :: * where
  WNat :: NATTY n => Natty n -> WrappedNat
  
wrapNat :: Int -> WrappedNat
wrapNat 0 = WNat SZ
wrapNat n = case wrapNat (n-1) of
              WNat wn -> WNat (SS wn)

intOfNat :: Natty n -> Int
intOfNat SZ = 0
intOfNat (SS n) = 1 + intOfNat n

data WrappedPoint :: * where
  WPoint :: Natty x -> Natty y -> WrappedPoint

wrapPoint :: (Int, Int) -> WrappedPoint
wrapPoint (x, y) =
  case (wrapNat x, wrapNat y) of
    (WNat x, WNat y) -> WPoint x y

data WrappedBox :: * where
  WBox :: Size w h -> CharBox '(w, h) -> WrappedBox

data WrappedVec a :: * where
  WVec :: Vec n a -> WrappedVec a


type Cursor a m = ([a], m, [a])
type StringCursor = Cursor Char ()

type TextCursor = Cursor String StringCursor

deactivate :: Cursor a () -> (Int, [a])
deactivate c = outward 0 c where
  outward i ([], (), xs)     = (i, xs)
  outward i (x : xz, (), xs) = outward (i + 1) (xz, (), x : xs)


activate :: (Int, [a]) -> Cursor a ()
activate (i, xs) = inward i ([], (), xs) where
  inward _ c@(_, (), [])     = c
  inward 0 c                 = c
  inward i (xz, (), x : xs)  = inward (i - 1) (x : xz, (), xs)

vecOfList :: [a] -> WrappedVec a
vecOfList []     = WVec V0
vecOfList (x:xs) = case vecOfList xs of
                     WVec v -> WVec (x :> v)

boxOfString :: String -> WrappedBox
boxOfString s = case vecOfList s of
                  WVec v -> WBox (vlength v, one) (boxS v)

boxOfStrings :: [String] -> WrappedBox
boxOfStrings []     = WBox (SZ, SZ) boxZ
boxOfStrings (s:ss) = case (boxOfString s, boxOfStrings ss) of
                        (WBox (x1, y1) b1, WBox (x2, y2) b2) ->
                             WBox
                               (x1 `maxn` x2, y1 /+/ y2)
                               (joinV (x1, y1) (x2, y2) b1 b2)

whatAndWhere :: TextCursor -> (WrappedBox, (Int, Int))
whatAndWhere (czz, cur, css) = (boxOfStrings strs, (x, y))
  where
    (x, cs) = deactivate cur
    (y, strs) = deactivate (czz, (), cs : css)

data ArrowDir = UpArrow | DownArrow | LeftArrow | RightArrow
data Modifier = Normal | Shift | Control

data Key
  = CharKey Char                -- an ordinary printable character
  | ArrowKey Modifier ArrowDir  -- an arrow key
  | Return
  | Backspace
  | Delete
  | Quit

directions :: [(Char, ArrowDir)]
directions = [('A', UpArrow), ('B', DownArrow),
              ('C', RightArrow), ('D', LeftArrow)]

escapeKeys :: [(String, Key)]
escapeKeys =
  [([c], ArrowKey Normal d) | (c, d) <- directions] ++
  [("1;2" ++ [c], ArrowKey Shift d) | (c, d) <- directions] ++
  [("1;5" ++ [c], ArrowKey Control d) | (c, d) <- directions] ++
  [("3~", Delete)]

data Damage
  = NoChange       -- use this if nothing at all happened
  | PointChanged   -- use this if we moved the cursor but kept the text
  | LineChanged    -- use this if we changed text only on the current line
  | LotsChanged    -- use this if we changed text off the current line
  deriving (Show, Eq, Ord)

{--------------------------------------------------------------------------}
{- Given a Key and an initial TextCursor, either reject the keystroke or  -}
{- return a modified cursor, with an overestimate of the damage we've     -}
{- done.                                                                  -}
{--------------------------------------------------------------------------}

handleKey :: Key -> TextCursor -> Maybe (Damage, TextCursor)
handleKey (CharKey c) (sz, (cz, (), cs), ss) =
  Just (LineChanged, (sz, (c : cz, (), cs), ss))
handleKey (ArrowKey Normal LeftArrow) (sz, (c : cz, (), cs), ss) =
  Just (PointChanged, (sz, (cz, (), c : cs), ss))
handleKey (ArrowKey Normal RightArrow) (sz, (cz, (), c : cs), ss) =
  Just (PointChanged, (sz, (c : cz, (), cs), ss))
handleKey (ArrowKey Normal UpArrow) (sUp : sz, pos, ss) =
  Just (PointChanged, (sz, activate (i, sUp), s : ss))
    where
      (i, s) = deactivate pos
handleKey (ArrowKey Normal DownArrow) (sz, pos, sDown : ss) =
  Just (PointChanged, (s : sz, activate (i, sDown), ss))
    where
      (i, s) = deactivate pos
handleKey Return (sz, (cz, (), cs), ss) =
  Just (LotsChanged, (prefix : sz, ([], (), cs), ss))
  where
    (_, prefix) = deactivate (cz, (), [])
handleKey Delete (sz, (cz, (), c : cs), ss) =
  Just (LineChanged, (sz, (cz, (), cs), ss))
handleKey Backspace (sz, (c : cz, (), cs), ss) =
  Just (LineChanged, (sz, (cz, (), cs), ss))
handleKey Delete (sz, (cz, (), []), s : ss) =
  Just (LotsChanged, (sz, (cz, (), s), ss))
handleKey Backspace (s : sz, ([], (), cs), ss) =
  Just (LotsChanged, (sz, (cz, (), cs), ss))
           where
             (cz, _, _) = activate (length s, s)
handleKey _ _ = Nothing
