%if False

> {-# LANGUAGE GADTs, PolyKinds, KindSignatures, MultiParamTypeClasses,
>     DataKinds, FlexibleInstances, RankNTypes, FlexibleContexts,
>     TypeOperators, TypeFamilies #-}

> module Editor where
>
> import Control.Applicative
> import Data.Traversable
> import Data.Foldable
>
> import NatVec
> import BoxPleasure

> (/+/) :: Natty m -> Natty n -> Natty (m :+ n)
> Zy   /+/ n    = n
> Sy m /+/ n   = Sy (m /+/ n)

> class NATTY (n :: Nat) where
>   natty :: Natty n
> 
> instance NATTY Z where
>   natty = Zy
> 
> instance NATTY n => NATTY (S n) where
>   natty = Sy natty
> 
> natter :: Natty n -> (NATTY n => t) -> t
> natter Zy     t = t
> natter (Sy n) t = natter n t

> vlength :: Vec n x -> Natty n
> vlength V0        = Zy
> vlength (x :> xs) = Sy (vlength xs)

> vcopies :: forall n x.Natty n -> x -> Vec n x
> vcopies Zy x = V0
> vcopies (Sy n) x = x :> vcopies n x   
> 
> vapp :: forall n s t.Vec n (s -> t) -> Vec n s -> Vec n t
> vapp V0 V0 = V0
> vapp (f :> fs) (s :> ss) = f s :> vapp fs ss
 
> instance NATTY n => Applicative (Vec n) where
>   pure = vcopies natty where
>   (<*>) = vapp where
> 
> instance Traversable (Vec n) where
>   traverse f V0 = pure V0
>   traverse f (x :> xs) = (:>) <$> f x <*> traverse f xs

%$

> instance Functor (Vec n) where
>   fmap = fmapDefault
> 
> instance Foldable (Vec n) where
>   foldMap = foldMapDefault


> data Matrix :: * -> (Nat, Nat) -> * where
>   Mat :: Vec h (Vec w a) -> Matrix a (Pair w h)
>
> unMat :: Matrix a (Pair w h) -> Vec h (Vec w a)
> unMat (Mat vs) = vs

%endif

\subsection{Character matrix boxes}

We implement a text editor using a character matrix box to represent
the text buffer.

> type CharMatrix = Matrix Char
> type CharBox wh = Box CharMatrix wh

We can fill an entire matrix with the same character.
 
> matrixChar :: Char -> (Natty w, Natty h) -> CharMatrix (Pair w h)
> matrixChar c (w, h) = Mat (vcopies h (vcopies w c))

We can render a character matrix box as a character matrix.

> renderCharBox ::
>   Size w h -> CharBox (Pair w h) -> CharMatrix (Pair w h)
> renderCharBox _       (Stuff css)        = css
> renderCharBox (w, h)  Clear              =
>   matrixChar ' ' (w, h)
> renderCharBox (w, _)  (Ver h1 b1 h2 b2)  =
>   Mat (unMat (renderCharBox (w, h1) b1)
>     `vappend` unMat (renderCharBox (w, h2) b2))
> renderCharBox (_, h) (Hor w1 b1 w2 b2)   =
>   Mat (  vcopies h vappend `vapp`
>          unMat (  renderCharBox (w1, h) b1) `vapp`
>                   unMat (renderCharBox (w2, h) b2))

We can display a character matrix as a list of strings.

> stringsOfCharMatrix :: CharMatrix wh -> [String]
> stringsOfCharMatrix (Mat vs) =
>   foldMap ((:[]) . foldMap (:[])) vs

In order to be able to cut (and hence crop) matrix boxes we
instantiate the |Cut| type class for matrices.

> instance Cut (Matrix e) where
>   horCut m _ (Mat ess) =
>     (Mat (fst <$> ps), Mat (snd <$> ps)) where
>       ps = vchop m <$> ess
>   verCut m _ (Mat ess) = (Mat tess, Mat bess) where
>     (tess, bess) = vchop m ess 

%$

\subsection{$\Sigma$ types}

Sometimes, it is necessary to convert unindexed values to equivalent
type-indexed values. For instance, we may receive a natural number at
run-time represented as an |Int|, and wish to convert it to an
|Natty|. Of course, we cannot statically specify the index on the
returned |Natty|, but we can quantify over it, essentially defining a
$\Sigma$ type.

> data WNat :: * where
>   WNat :: Natty n -> WNat

The |WNat| data type amounts to a Haskell encoding of the type
$\Sigma$|(n : Nat) DOT n|. We can now wrap an |Int| as a |WNat|.

> wrapNat :: Int -> WNat
> wrapNat  0  =  WNat Zy
> wrapNat  n  =  case wrapNat (n-1) of
>                  WNat wn -> WNat (Sy wn)

Similarly, we implement functionality for wrapping points.

> data WPoint :: * where
>   WPoint :: Natty x -> Natty y -> WPoint
> 
> wrapPoint :: (Int, Int) -> WPoint
> wrapPoint (x, y) =
>   case (wrapNat x, wrapNat y) of
>     (WNat x, WNat y) -> WPoint x y

We can wrap a list as a vector.

> data WrappedVec a :: * where
>   WVec :: Vec n a -> WrappedVec a
>
> wrapList :: [a] -> WrappedVec a
> wrapList []      = WVec V0
> wrapList (x:xs)  = case wrapList xs of
>   WVec v -> WVec (x :> v)

Given a string of length |w|, we can wrap it as a character box of
size |(w, 1)|.

> data WCharBox :: * where
>   WCharBox :: Size w h -> CharBox (Pair w h) -> WCharBox
>
> wrapString :: String -> WCharBox
> wrapString s = case wrapList s of
>   WVec v ->
>     WCharBox (vlength v, Sy Zy) (Stuff (Mat (pure v)))

Given a list of |h| strings of maximum length |w|, we can wrap it as a
character box of size |(w, h)|.

> wrapStrings :: [String] -> WCharBox
> wrapStrings []      = WCharBox (Zy, Zy) Clear
> wrapStrings (s:ss)  =
>   case (wrapString s, wrapStrings ss) of
>     (WCharBox (w1, h1) b1, WCharBox (w2, h2) b2) ->
>       WCharBox
>         (w1 `maxn` w2, h1 /+/ h2)
>         (joinV (w1, h1) (w2, h2) b1 b2)


\subsection{The inner loop}

We give a brief overview of the editor's inner loop. The full code is
available at:

  \url{https://github.com/slindley/dependent-haskell/tree/master/Box}

The current position in the text buffer is represented using a zipper
structure over an undindexed list of strings. The current position and
size of the screen is represented as two pairs of integers. On a
change to the buffer, the inner loop proceeds as follows.
\begin{itemize}
\item Wrap the current screen position and size as a singleton region
  using |wrapRegion|.
\item Unravel the zipper structure to reveal the underlying structure
  of the buffer as a list of strings.
\item Use |wrapStrings| to wrap the list of strings as a suitably
  indexed |CharBox|.
\item Crop the |CharBox| according to the wrapped singleton region.
  size.
\item Render the result as a list of strings using
  |stringsOfCharMatrix . renderCharBox|.
\end{itemize}

We take advantage of dependent types to ensure that cropping yields
boxes of the correct size. The rest of the editor does not use
dependent types. The wrapping functions convert non-dependent data
into equivalent dependent data. Rendering does the opposite.

