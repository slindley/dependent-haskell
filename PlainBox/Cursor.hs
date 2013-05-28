module Cursor where

import Box
import CharBox

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

layZ :: Box p
layZ = clear (0, 0)

layS :: String -> CharBox
layS s = ((length s, 1), Stuff [s])

whatAndWhere :: TextCursor -> (CharBox, Point)
whatAndWhere (czz, cur, css) = (foldr (joinV . layS) layZ strs, (x, y)) where
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

