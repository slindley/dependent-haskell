{- deprecated {-# INCLUDE <mycurses.h> #-} -}
{-# LANGUAGE ForeignFunctionInterface #-}

-- use flag -lncurses to compile

import Foreign
import Foreign.C (CInt(..))
import ANSIEscapes
import System.IO
import System.Environment

import Box
import CharBox
import Cursor

data Window = Window
type WindowPtr = Ptr Window

foreign import ccall
  initscr :: IO () 

foreign import ccall "endwin"
  endwin :: IO CInt

foreign import ccall "refresh"
  refresh :: IO CInt

foreign import ccall "&LINES"
  linesPtr :: Ptr CInt

foreign import ccall "&COLS"
  colsPtr :: Ptr CInt

scrSize :: IO (Int, Int)
scrSize = do
    lnes <- peek linesPtr
    cols <- peek colsPtr
    return (fromIntegral cols, fromIntegral lnes)

copies :: Int -> a -> [a]
copies n a = take n (repeat a)

crlf :: IO ()
crlf = putStr "\r\n"

putLn :: String -> IO ()
putLn x = putStr x >> crlf

type ScreenState = (Point, Size)
  -- position in buffer of top left corner of screen, screen size

onScreen :: Point -> ScreenState -> ScreenState
onScreen (cx, cy) ((px, py), s@(sw, sh))
  = (( intoRange px cx sw, intoRange py cy sh), s)
  where
    intoRange i j x
      | i <= j && j <= i + x = i   -- in range, no change
      | otherwise = max 0 (j - div x 2)

getEscapeKey :: [(String, Key)] -> IO (Maybe Key)
getEscapeKey [] = return Nothing
getEscapeKey sks = case lookup "" sks of
  Just k -> return (Just k)
  _ -> do
    c <- getChar
    getEscapeKey [(cs, k) | (d : cs, k) <- sks, d == c]

keyReady :: IO (Maybe Key)
keyReady = do
  b <- hReady stdin
  if not b then return Nothing else do
    c <- getChar
    case c of
      '\n' -> return $ Just Return
      '\r' -> return $ Just Return
      '\b' -> return $ Just Backspace
      '\DEL' -> return $ Just Backspace
      _ | c >= ' ' -> return $ Just (CharKey c)
      '\ESC' -> do
        b <- hReady stdin
        if not b then return $ Just Quit else do
          c <- getChar
          case c of
            '[' -> getEscapeKey escapeKeys
            _ -> return $ Just Quit
      _ -> return $ Nothing

layout :: CharBox -> [String] 
layout = renderCharBox

outer :: ScreenState -> TextCursor -> IO ()
outer ps tc = inner ps tc (whatAndWhere tc) LotsChanged
  where
  inner ps@(p, s) tc lc@(l, c@(cx, cy)) d = do
    refresh
    s' <- scrSize
    let ps'@((px, py), (sw, _)) = onScreen c (p, s')
    let d' = if ps /= ps' then LotsChanged else d
    case d' of
      LotsChanged -> do
        clearScreen
        resetCursor
        mapM_ putStr (layout (cropper ps' l))
      LineChanged -> do
        resetCursor
        down (cy - py)
        mapM_ putStr (layout (cropper ((px, cy), (sw, 1)) l))
      _ -> return ()
    if d' > NoChange then do
      resetCursor
      forward (cx - px)
      down (cy - py)
     else return ()
    mc <- keyReady
    case mc of
      Nothing -> inner ps' tc lc NoChange
      Just Quit -> return ()
      Just k -> case handleKey k tc of
        Nothing -> inner ps' tc lc NoChange
        Just (d, tc') -> inner ps' tc' (whatAndWhere tc') d

main :: IO ()
main = do 
  hSetBuffering stdout NoBuffering
  hSetBuffering stdin NoBuffering
  xs <- getArgs
  s <- case xs of
    [] -> return ""
    (x : _) -> readFile x
  let (l, ls) = case lines s of
        [] -> ("", [])
        (l : ls) -> (l, ls)
  initscr
  outer ((0, 0), (-1, -1)) ([], ([], (), l), ls)
  endwin
  return ()
