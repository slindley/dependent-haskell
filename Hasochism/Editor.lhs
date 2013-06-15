%if False

> {-# LANGUAGE GADTs, PolyKinds, KindSignatures, MultiParamTypeClasses,
>     DataKinds, FlexibleInstances, RankNTypes, FlexibleContexts,
>     TypeOperators, TypeFamilies #-}

> module Main where
>
> import Prelude hiding (mapM_)
>
> import Control.Applicative
> import Data.Traversable
> import Data.Foldable
>
> import Foreign
> import Foreign.C (CInt(..))
> import ANSIEscapes
> import System.IO
> import System.Environment
>
> import NatVec
> import Pies
> import BoxPleasure

%endif

We outline the design of a basic text editor, which represents the
text buffer as a size-indexed box. Using this representation
guarantees that manipulations such as cropping the buffer to generate
screen output only generate well-formed boxes of a given size. We will
also need to handle dynamic values coming from the outside world. We
convert these to equivalent size-indexed values using existentials,
building on the |Ex| data type of Section~\ref{sec:merge-sort} and the
separating and non-separating conjunction operators of
Section~\ref{subsec:conjunction}.

\subsection{Character Boxes}

%format matrixChar = "\F{matrixChar}"
%format renderCharBox = "\F{renderCharBox}"
%format stringsOfCharMatrix = "\F{stringsOfCharMatrix}"

A character box is a box whose content is given by character
matrices.

> type CharMatrix = Matrix Char
> type CharBox = Box CharMatrix

Concretely, we will use a character box to represent a text buffer. We
can fill an entire matrix with the same character.
 
> matrixChar :: Char -> Size wh -> CharMatrix wh
> matrixChar c (w :&&: h) = Mat (vcopies h (vcopies w c))

We can render a character box as a character matrix.

> renderCharBox ::
>   Size wh -> CharBox wh -> CharMatrix wh
> renderCharBox _       (Stuff css)        = css
> renderCharBox wh  Clear              =
>   matrixChar ' ' wh
> renderCharBox (w :&&: _)  (Ver h1 b1 h2 b2)  =
>   Mat (unMat (renderCharBox (w :&&: h1) b1)
>     `vappend` unMat (renderCharBox (w :&&: h2) b2))
> renderCharBox (_ :&&: h) (Hor w1 b1 w2 b2)   =
>   Mat (  vcopies h vappend `vapp`
>          unMat (  renderCharBox (w1 :&&: h) b1) `vapp`
>                   unMat (renderCharBox (w2 :&&: h) b2))

We can display a character matrix as a list of strings.

> stringsOfCharMatrix :: CharMatrix wh -> [String]
> stringsOfCharMatrix (Mat vs) =
>   foldMap ((:[]) . foldMap (:[])) vs

In order to be able to cut (and hence crop) boxes with matrix content
we instantiate the |Cut| type class for matrices.

> instance Cut (Matrix e) where
>   horCut m _ (Mat ess) =
>     (Mat (fst <$> ps), Mat (snd <$> ps)) where
>       ps = vchop m <$> ess
>   verCut m _ (Mat ess) = (Mat tess, Mat bess) where
>     (tess, bess) = vchop m ess 

%$

\subsection{Existentials}
\label{subsec:more-existentials}

%format wrapNat = "\F{wrapNat}"
%format wrapPair = "\F{wrapPair}"
%format wrapInt = "\F{wrapInt}"
%format wrapSize = "\F{wrapSize}"
%format wrapPoint = "\F{wrapPoint}"
%format wrapRegion = "\F{wrapRegion}"
%format wrapVec = "\F{wrapVec}"
%format wrapLenVec = "\F{wrapLenVec}"
%format wrapString = "\F{wrapString}"
%format wrapStrings = "\F{wrapStrings}"

%format intToNat = "\F{intToNat}"
%format unFlip = "\F{unFlip}"
%format unLenVec = "\F{unLenVec}"
%format unSizeCharBox = "\F{unSizeCharBox}"

%if False

> data Ex (p :: k -> *) where
>   Ex :: p i -> Ex p

> type WNat = Ex Natty

> wrapNat :: Nat -> WNat
> wrapNat  Z      =  Ex Zy
> wrapNat  (S m)  =  case wrapNat m of
>                      Ex n -> Ex (Sy n)

%endif

In Section~\ref{sec:merge-sort} we introduced existentially quantified
singletons as a means for taking dynamic values and converting them
into equivalent singletons.

We now present combinators for constructing existentials over
composite indexes. For the editor, we will need to generate a region,
that is, a pair of pairs of singleton naturals from a pair of pairs of
natural numbers.

> wrapPair :: (a -> Ex p) ->
>             (b -> Ex q) ->
>               (a, b) -> Ex (p :**: q)
> wrapPair w1 w2 (x1, x2) =
>   case (w1 x1, w2 x2) of
>     (Ex v1, Ex v2) -> Ex (v1 :&&: v2)

The |wrapPair| function wraps a pair of dynamic objects in a suitable
existential package using a separated conjunction.

> type WPoint = Ex Point
> type WSize = Ex Size
> type WRegion = Ex Region

> intToNat :: Int -> Nat
> intToNat 0 = Z
> intToNat n = S (intToNat (n-1))

> wrapInt = wrapNat . intToNat
> wrapPoint  = wrapPair wrapInt wrapInt
> wrapSize   = wrapPair wrapInt wrapInt
> wrapRegion = wrapPair wrapPoint wrapSize

We might wish to wrap vectors, but the |Vec| type takes the length
index first, so we cannot use it as is with |Ex|. Thus we can define
and use a |Flip| combinator, which reverses the arguments of a two
argument type-operator.

> newtype Flip f a b = Flip {unFlip :: f b a}

> type WVec a = Ex (Flip Vec a)

> wrapVec :: [a] -> WVec a
> wrapVec []      = Ex (Flip V0)
> wrapVec (x:xs)  = case wrapVec xs of
>   Ex (Flip v) -> Ex (Flip (x :> v))

In fact, we wish to wrap a vector up together with its length. This is
where the non-separating conjunction comes into play. The |Natty|
representing the length of the vector and the |Flip Vec a|
representing the vector itself should share the same index.

> type WLenVec a = Ex (Natty :*: Flip Vec a)

> wrapLenVec :: [a] -> WLenVec a
> wrapLenVec []      = Ex (Zy :&: Flip V0)
> wrapLenVec (x:xs)  = case wrapLenVec xs of
>   Ex (n :&: Flip v) -> Ex (Sy n :&: Flip (x :> v))

Similarly, we use non-separating conjunction to wrap a box with its
size.

> type WSizeCharBox = Ex (Size :*: CharBox)

Given a string of length |w|, we can wrap it as a character box of
size |(w, 1)|.

> wrapString :: String -> WSizeCharBox
> wrapString s = case wrapLenVec s of
>   Ex (n :&: Flip v) ->
>     Ex ((n :&&: Sy Zy) :&: Stuff (Mat (pure v)))

Given a list of |h| strings of maximum length |w|, we can wrap it as a
character box of size |(w, h)|.

> wrapStrings :: [String] -> WSizeCharBox
> wrapStrings []      = Ex ((Zy :&&: Zy) :&: Clear)
> wrapStrings (s:ss)  =
>   case (wrapString s, wrapStrings ss) of
>     (  Ex ((w1 :&&: h1) :&: b1),
>        Ex ((w2 :&&: h2) :&: b2)) ->
>          Ex (  ((w1 `maxn` w2) :&&: (h1 /+/ h2)) :&:
>                juxV (w1 :&&: h1) (w2 :&&: h2) b1 b2)

\todo{Observe that pattern synonyms would be helpful here.}

\todo{Observe that the \singletons library doesn't appear to provide
  any special support for existential quantification over singletons}

\subsection{Cursors}

%format deactivate = "\F{deactivate}"
%format outward = "\F{outward}"
%format activate = "\F{activate}"
%format inward = "\F{inward}"
%format whatAndWhere = "\F{whatAndWhere}"

We use a zipper structure~\cite{Huet97} to represent a cursor into a
text buffer. We make no attempt to statically track the size of the
buffer as a cursor, but do so when we wish to manipulate the whole
buffer.

A cursor is a triple consisting of: a backwards list of elements
before the current position, the object at the current position, and a
forward list of elements after the current position.

> type Cursor a m = ([a], m, [a])

The elements of a |StringCursor| are characters.

> type StringCursor = Cursor Char ()

The elements of a |TextCursor| are strings. The object at the current
position is a |StringCursor|.
 
> type TextCursor = Cursor String StringCursor

The |deactivate| and |activate| functions convert between a unit cursor and a pair of a list and its length.

> deactivate :: Cursor a () -> (Int, [a])
> deactivate c = outward 0 c where
>   outward i ([], (), xs)     = (i, xs)
>   outward i (x : xz, (), xs) = outward (i + 1) (xz, (), x : xs)
>
> activate :: (Int, [a]) -> Cursor a ()
> activate (i, xs) = inward i ([], (), xs) where
>   inward _ c@(_, (), [])     = c
>   inward 0 c                 = c
>   inward i (xz, (), x : xs)  = inward (i - 1) (x : xz, (), xs)
 
The |whatAndWhere| function uses |deactivate| and |wrapStrings| to
generate a well-formed existentially quantified box from a
|TextCursor|.

> whatAndWhere :: TextCursor -> (WSizeCharBox, (Int, Int))
> whatAndWhere (czz, cur, css) = (wrapStrings strs, (x, y))
>   where
>     (x, cs) = deactivate cur
>     (y, strs) = deactivate (czz, (), cs : css)

%if False

> data ArrowDir = UpArrow | DownArrow | LeftArrow | RightArrow
> data Modifier = Normal | Shift | Control
> 
> data Key
>   = CharKey Char                -- an ordinary printable character
>   | ArrowKey Modifier ArrowDir  -- an arrow key
>   | Return
>   | Backspace
>   | Delete
>   | Quit
> 
> directions :: [(Char, ArrowDir)]
> directions = [('A', UpArrow), ('B', DownArrow),
>               ('C', RightArrow), ('D', LeftArrow)]
> 
> escapeKeys :: [(String, Key)]
> escapeKeys =
>   [([c], ArrowKey Normal d) | (c, d) <- directions] ++
>   [("1;2" ++ [c], ArrowKey Shift d) | (c, d) <- directions] ++
>   [("1;5" ++ [c], ArrowKey Control d) | (c, d) <- directions] ++
>   [("3~", Delete)]
> 
> data Damage
>   = NoChange       -- nothing at all happened
>   | PointChanged   -- we moved the cursor but kept the text
>   | LineChanged    -- we changed text only on the current line
>   | LotsChanged    -- we changed text off the current line
>   deriving (Show, Eq, Ord)
 
%% > {--------------------------------------------------------------------------}
%% > {- Given a Key and an initial TextCursor, either reject the keystroke or  -}
%% > {- return a modified cursor, with an overestimate of the damage we've     -}
%% > {- done.                                                                  -}
%% > {--------------------------------------------------------------------------}
%% > 

> handleKey :: Key -> TextCursor -> Maybe (Damage, TextCursor)
> handleKey (CharKey c) (sz, (cz, (), cs), ss) =
>   Just (LineChanged, (sz, (c : cz, (), cs), ss))
> handleKey (ArrowKey Normal LeftArrow) (sz, (c : cz, (), cs), ss) =
>   Just (PointChanged, (sz, (cz, (), c : cs), ss))
> handleKey (ArrowKey Normal RightArrow) (sz, (cz, (), c : cs), ss) =
>   Just (PointChanged, (sz, (c : cz, (), cs), ss))
> handleKey (ArrowKey Normal UpArrow) (sUp : sz, pos, ss) =
>   Just (PointChanged, (sz, activate (i, sUp), s : ss))
>     where
>       (i, s) = deactivate pos
> handleKey (ArrowKey Normal DownArrow) (sz, pos, sDown : ss) =
>   Just (PointChanged, (s : sz, activate (i, sDown), ss))
>     where
>       (i, s) = deactivate pos
> handleKey Return (sz, (cz, (), cs), ss) =
>   Just (LotsChanged, (prefix : sz, ([], (), cs), ss))
>   where
>     (_, prefix) = deactivate (cz, (), [])
> handleKey Delete (sz, (cz, (), c : cs), ss) =
>   Just (LineChanged, (sz, (cz, (), cs), ss))
> handleKey Backspace (sz, (c : cz, (), cs), ss) =
>   Just (LineChanged, (sz, (cz, (), cs), ss))
> handleKey Delete (sz, (cz, (), []), s : ss) =
>   Just (LotsChanged, (sz, (cz, (), s), ss))
> handleKey Backspace (s : sz, ([], (), cs), ss) =
>   Just (LotsChanged, (sz, (cz, (), cs), ss))
>            where
>              (cz, _, _) = activate (length s, s)
> handleKey _ _ = Nothing

%endif

\subsection{The Inner Loop}

We give a brief overview of the editor's inner loop. The full code is
available as literate Haskell at:

  \url{https://github.com/slindley/dependent-haskell/tree/master/Hasochism}

The current position in the text buffer is represented using a zipper
structure over an undindexed list of strings. The current position and
size of the screen is represented as two pairs of integers. On a
change to the buffer, the inner loop proceeds as follows.
\begin{itemize}
\item Wrap the current screen position and size as a singleton region
  using |wrapRegion|.
\item Unravel the zipper structure using |whatAndWhere| to reveal the
  underlying structure of the buffer as a list of strings.
\item This invokes |wrapStrings| to wrap the list of strings as an
  existential over a suitably indexed |CharBox|.
\item Crop the wrapped |CharBox| according to the wrapped singleton
  region.
\item Render the result as a list of strings using
  |stringsOfCharMatrix . renderCharBox|.
\end{itemize}

We take advantage of dependent types to ensure that cropping yields
boxes of the correct size. The rest of the editor does not use
dependent types. The wrapping functions convert non-dependent data
into equivalent dependent data. Rendering does the opposite.

We expect that converting back and forth between raw and indexed data
every time something changes is expensive. We leave a full performance
evaluation to future work. One might hope to use indexed data
everywhere. This is infeasible in practice, because of the need to
interact with the outside world, and in particular foreign APIs
(including the curses library we use for our text editor).

%if False

> foreign import ccall
>   initscr :: IO () 
> 
> foreign import ccall "endwin"
>   endwin :: IO CInt
> 
> foreign import ccall "refresh"
>   refresh :: IO CInt
> 
> foreign import ccall "&LINES"
>   linesPtr :: Ptr CInt
> 
> foreign import ccall "&COLS"
>   colsPtr :: Ptr CInt
 
> scrSize :: IO (Int, Int)
> scrSize = do
>     lnes <- peek linesPtr
>     cols <- peek colsPtr
>     return (fromIntegral cols, fromIntegral lnes)
> 
> copies :: Int -> a -> [a]
> copies n a = take n (repeat a)
> 
> crlf :: IO ()
> crlf = putStr "\r\n"
> 
> putLn :: String -> IO ()
> putLn x = putStr x >> crlf
 
%% > -- onScreen c r
%% > --   c is where the cursor currently is
%% > --   r is where the viewport currently is
%% > --   the return value is an updated viewport
%% > --   containing c

> type UPoint = (Int, Int)
> type USize = (Int, Int)
> type URegion = (UPoint, USize)
>
> onScreen :: UPoint -> URegion -> URegion
> onScreen (cx, cy) ((px, py), s@(sw, sh))
>   = (( intoRange px cx sw, intoRange py cy sh), s)
>   where
>     intoRange i j x
>       | i <= j && j <= i + x = i   -- in range, no change
>       | otherwise = max 0 (j - div x 2)
 
> getEscapeKey :: [(String, Key)] -> IO (Maybe Key)
> getEscapeKey [] = return Nothing
> getEscapeKey sks = case lookup "" sks of
>   Just k -> return (Just k)
>   _ -> do
>     c <- getChar
>     getEscapeKey [(cs, k) | (d : cs, k) <- sks, d == c]
> 
> keyReady :: IO (Maybe Key)
> keyReady = do
>   b <- hReady stdin
>   if not b then return Nothing else do
>     c <- getChar
>     case c of
>       '\n' -> return $ Just Return
>       '\r' -> return $ Just Return
>       '\b' -> return $ Just Backspace
>       '\DEL' -> return $ Just Backspace
>       _ | c >= ' ' -> return $ Just (CharKey c)
>       '\ESC' -> do
>         b <- hReady stdin
>         if not b then return $ Just Quit else do
>           c <- getChar
>           case c of
>             '[' -> getEscapeKey escapeKeys
>             _ -> return $ Just Quit
>       _ -> return $ Nothing
 
> layout :: Size wh -> CharBox wh -> [String]
> layout s l = stringsOfCharMatrix (renderCharBox s l)
> 
> outer :: URegion -> TextCursor -> IO ()
> outer ps tc = inner ps tc (whatAndWhere tc) LotsChanged
>   where
>   inner ps@(p, _) tc lc@(Ex ((lw :&&: lh) :&: l), c@(cx, cy)) d = do
>     refresh
>     s' <- scrSize
>     let ps'@((px, py), (sw, sh)) = onScreen c (p, s')
>     let d' = if ps /= ps' then LotsChanged else d
>     case d' of
>       LotsChanged -> do
>         clearScreen
>         resetCursor
>         case wrapRegion ps' of
>           Ex ((x :&&: y) :&&: (w :&&: h)) -> do
>             let cropped = crop ((x :&&: y) :&&: (w :&&: h)) (lw :&&: lh) l
>             mapM_ putStr (layout (w :&&: h) cropped)
>       LineChanged -> do
>         resetCursor
>         down (cy - py)
>         case wrapRegion ((px, cy), (sw, 1)) of
>           Ex ((x :&&: y) :&&: (w :&&: h)) -> do
>             let cropped = crop ((x :&&: y) :&&: (w :&&: h)) (lw :&&: lh) l
>             mapM_ putStr (layout (w :&&: h) cropped)
>       _ -> return ()
>     if d' > NoChange then do
>       resetCursor
>       forward (cx - px)
>       down (cy - py)
>      else return ()
>     mc <- keyReady
>     case mc of
>       Nothing   -> inner ps' tc lc NoChange
>       Just Quit -> return ()
>       Just k    -> case handleKey k tc of
>         Nothing       -> inner ps' tc lc NoChange
>         Just (d, tc') -> inner ps' tc' (whatAndWhere tc') d
 
> main = do 
>   hSetBuffering stdout NoBuffering
>   hSetBuffering stdin NoBuffering
>   xs <- getArgs
>   s <- case xs of
>     [] -> return ""
>     (x : _) -> readFile x
>   let (l, ls) = case lines s of
>         [] -> ("", [])
>         (l : ls) -> (l, ls)
>   initscr
>   outer ((0, 0), (-1, -1)) ([], ([], (), l), ls)
>   endwin

%endif
