{- deprecated {-# INCLUDE <mycurses.h> #-} -}
{-# LANGUAGE DataKinds, KindSignatures, GADTs, TypeFamilies, TypeOperators,
    RankNTypes, PolyKinds, ForeignFunctionInterface #-}

-- use flag -lncurses to compile

import Foreign
import Foreign.C (CInt(..))
import ANSIEscapes
import System.IO
import System.Environment

import Box
import CharBox
import PlainCursor

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

type UPoint = (Int, Int)
type USize = (Int, Int)

type ScreenState = (UPoint, USize)
  -- position in buffer of top left corner of screen, screen size

-- onScreen c ps
--   c is where the cursor currently is
--   ps is where the viewport currently is
--   the return value is an updated viewport
--   containing c
onScreen :: UPoint -> ScreenState -> ScreenState
onScreen (cx, cy) ((px, py), s@(sw, sh))
  = (( intoRange px cx sw, intoRange py cy sh), s)
  where
    intoRange i j x
      | i <= j && j <= i + x = i   -- in range, no change
      | otherwise = max 0 (j - div x 2)

-- if we did the following, and defined appropriate wrappers over the
-- curses API then we could remove the calls to wrapPoint in the main
-- loop and use type indexed nats everywhere
{-
type ScreenState' = (WrappedPoint, WrappedPoint)

onScreen' :: WrappedPoint -> ScreenState' -> ScreenState'
onScreen' (WPoint cx cy) (WPoint px py, WPoint sw sh) =
  case (intoRange px cx sw, intoRange py cy sh) of
    (WNat px', WNat py') -> (WPoint px' py', WPoint sw sh)
    where
      intoRange :: Natty i -> Natty j -> Natty x -> WrappedNat
      intoRange i j x =
        case (cmp i j, cmp j (i /+/ x)) of
          (GTNat _, _) -> case div2 x of WNat d -> WNat (j /-/ d)
          (_, GTNat _) -> case div2 x of WNat d -> WNat (j /-/ d)
          _            -> WNat i  

      div2 :: Natty n -> WrappedNat
      div2 Zy          = WNat Zy
      div2 (Sy Zy)     = WNat Zy
      div2 (Sy (Sy n)) = case div2 n of WNat m -> WNat (Sy m)
-}

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

layout :: Size w h -> CharBox '(w, h) -> [String]
layout s l = stringsOfCharMatrix (renderCharBox' s l)

outer :: ScreenState -> TextCursor -> IO ()
outer ps tc = inner ps tc (whatAndWhere tc) LotsChanged
  where
  inner ps@(p, _) tc lc@(WBox (lw, lh) l, c@(cx, cy)) d = do
    refresh
    s' <- scrSize
    let ps'@((px, py), (sw, sh)) = onScreen c (p, s')
    if px < 0 || py < 0 || fst s' < 0 || snd s' < 0 then error "oops" else return ()
    let d' = if ps /= ps' then LotsChanged else d
    case d' of
      LotsChanged -> do
        clearScreen
        resetCursor
        case (wrapPoint (px, py), wrapPoint (sw, sh)) of
          (WPoint x y, WPoint w h) -> do
            let cropped = cropper ((x, y), (w, h)) (lw, lh) l
            mapM_ putStr (layout (w, h) cropped)
      LineChanged -> do
        resetCursor
        down (cy - py)
        case (wrapPoint (px, cy), wrapPoint (sw, 1)) of
          (WPoint x y, WPoint w h) -> do
            let cropped = cropper ((x, y), (w, h)) (lw, lh) l
            mapM_ putStr (layout (w, h) cropped)
      _ -> return ()
    if d' > NoChange then do
      resetCursor
      forward (cx - px)
      down (cy - py)
     else return ()
    mc <- keyReady
    case mc of
      Nothing   -> inner ps' tc lc NoChange
      Just Quit -> return ()
      Just k    -> case handleKey k tc of
        Nothing       -> inner ps' tc lc NoChange
        Just (d, tc') -> inner ps' tc' (whatAndWhere tc') d

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

--foreign import ccall unsafe "nomacro_getyx" 
--        nomacro_getyx :: Ptr Window -> Ptr CInt -> Ptr CInt -> IO ()

--standardScreen :: Window
--standardScreen = unsafePerformIO (peek stdscr)

--foreign import ccall "static &stdscr" 
--    stdscr :: Ptr Window


--getYX :: Ptr Window -> IO (Int, Int)
-- getYX w =
--     alloca $ \py ->                 -- allocate two ints on the stack
--         alloca $ \px -> do
--             nomacro_getyx w py px   -- writes current cursor coords
--             y <- peek py
--             x <- peek px
--             return (fromIntegral y, fromIntegral x)


