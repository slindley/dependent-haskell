\documentclass{beamer}
%
%\documentclass[serif]{beamer}

%\usepackage[T1]{fontenc}
%\usepackage{fourier}

%include polycode.fmt
%include forall.fmt

\DeclareMathAlphabet{\mathkw}{OT1}{cmss}{bx}{n}
%subst keyword a = "\mathkw{" a "}"
%subst conid a = "\mathsf{" a "}"
%format where = "\;\mathkw{where}"
%format family = "\mathkw{family}"

%format * = "\star"
%format PRIME = "{}^{\prime}\!\!"
%format Prime = "{}^{\prime}"
%format PRIMEPRIME = "{}^{\prime\prime}\!\!"

%format :+ = ":\!\!+\,"
%format :- = ":\!\!-\,"

%format /+/ = "/\!\!+\!\!/"
%format /-/ = "/\!\!-\!\!/"

%format <$> = "<\!\!\mathord{\$}\!\!>"
%format <*> = "<\!\!\mathord{\star}\!\!>"

%format :**: = ":\!\!*\!*\!\!:"
%format :&&: = ":\!\!\&\!\&\!\!:"

%format :*: = ":\!\!*\!\!:"
%format :&: = ":\!\!\&\!\!:"

%format :-> = ":\to"
%%% ":\!\!-\!\!>"

%format (Pair (x) (y)) = Prime(x, y)

%format x1 = x "_1"
%format x2 = x "_2"
%format xn = x "_n"

%format y1 = y "_1"
%format y2 = y "_2"

%format w1 = w "_1"
%format w2 = w "_2"

%format h1 = h "_1"
%format h2 = h "_2"

%format wh1 = wh "_1"
%format wh2 = wh "_2"


%format b1 = b "_1"
%format b2 = b "_2"
%format b11 = b "_{11}"
%format b12 = b "_{12}"
%format b21 = b "_{21}"
%format b22 = b "_{22}"

%format p1 = p "_1"
%format p2 = p "_2"

%format EXISTS = "\exists\!"
%format DOT = "\!\!.\!\!"

%format ~ = "\sim"

%format BAD = "\hfill(\times)"

%format iota = "\iota"
%format kappa = "\kappa"


%format show = "\F{show}"

%format const = "\F{const}"
%format id = "\F{id}"

%format fst = "\F{fst}"
%format snd = "\F{snd}"

\newcommand{\F}{\mathsf}

\renewcommand{\hscodestyle}{\small}

\newcommand\todo[1]{\textbf{TODO: }{#1}}

%\usepackage{beamerthemesplit}


\setbeamersize{text margin left = 2em}

\usepackage{amsmath}
\usepackage{xspace}
\usepackage{url}
\usepackage{hyperref}
\usepackage{tikz}

\usetheme{Frankfurt}


%% \usetikzlibrary{arrows}

%% \usepackage{amsmath}
%% \usepackage{fleqn}
%% %\usepackage{graphicx}
%% \usepackage{mathpartir}
%% \usepackage{xspace}
%% \usepackage{stmaryrd}
%% %\usepackage{color}
%% \usepackage{suffix}

%% \usetheme{Frankfurt}

% disable useless navigation symbols
\setbeamertemplate{navigation symbols}{}

% disable the section information
\setbeamertemplate{headline}{}

% use triangles for bullets
\setbeamertemplate{itemize items}[triangle]

\title{Hasochism}
\subtitle{The pleasure and pain of dependently typed Haskell programming}
\author{Sam Lindley}
%\email{Sam.Lindley@@ed.ac.uk}
\institute{Laboratory for foundations of computer science \\
           The University of Edinburgh \\[.2cm]
           {\texttt\tiny Sam.Lindley@@ed.ac.uk}}
\date{23rd September 2013}


%% macros


\begin{document}

\begin{frame}
\titlepage

\begin{center}
(joint work with Conor McBride)
\end{center}

\end{frame}

%if False

> {-# LANGUAGE GADTs, PolyKinds, KindSignatures, MultiParamTypeClasses,
>     DataKinds, FlexibleInstances, RankNTypes, FlexibleContexts,
>     TypeOperators, TypeFamilies #-}

> import Control.Applicative
> import Data.Traversable
> import Data.Foldable

> type Pair (x :: j) (y :: k) = '(x, y)

%endif

%% \begin{frame}

%% \frametitle{Milner's coincidences}
%% \[\begin{array}{l||r@@{\quad}l}
%% \textrm{syntactic category}  & \textbf{terms}      &     \textbf{types} \\
%%                              &        \mid~~       & \quad\mid \\
%% \textrm{phase distinction}   & \textbf{dynamic}    &    \textbf{static} \\
%%                              &        \mid~~       & \quad\mid \\
%% \textrm{inference}           & \textbf{explicit}   &  \textbf{implicit} \\
%%                              &        \mid~~       & \quad\mid \\
%% \textrm{abstraction}         & \textbf{simple}     & \textbf{dependent} \\
%% \end{array}\]

%% \end{frame}

\begin{frame}
\frametitle{This talk}

\begin{itemize}
\item Four different universal quantifiers for dependently typed
  Haskell programming.
\item Avoiding explicit proofs by squirreling extra type equations
  into proof objects.
\item Existentials for encapsulating dependent types.
\end{itemize}
\end{frame}

\begin{frame}
\frametitle{Data type promotion (|forall ((n :: Nat)).|)}

%format :+ = "\mathbin{\mbox{$:\!\!+$}}"
%format vappend = "\F{vappend}"

% deriving (Show, Eq, Ord)

> data Nat = Z | S Nat

With |DataKinds| enabled, the |Nat| data type can be used as a kind.

Length indexed vectors:

> data Vec :: Nat -> * -> * where
>   V0    ::                  Vec Z x
>   (:>)  :: x -> Vec n x ->  Vec (S n) x

Type level addition:

> type family (m :: Nat) :+ (n :: Nat) :: Nat
> type instance  Z    :+  n  =  n
> type instance  S m  :+  n  =  S (m :+ n)

Appending length indexed vectors:

> vappend :: Vec m x -> Vec n x -> Vec (m :+ n) x
> vappend  V0         ys  =  ys
> vappend  (x :> xs)  ys  =  x :> vappend xs ys

\end{frame}


\begin{frame}
\frametitle{Singletons (|forall n. Natty n ->|)}

%format vchop = "\F{vchop}"

Inverting |vappend|:

< vchop :: Vec (m :+ n) x -> (Vec m x, Vec n x) -- |BAD|

We cannot write |vchop| as |m| is not available at run time.

\medskip

Singleton GADT for naturals:

> data Natty :: Nat -> * where
>   Zy  :: Natty Z
>   Sy  :: Natty n -> Natty (S n)

If we pass in a |Natty m|, then we can compute over it at run time:

> vchop :: Natty m -> Vec (m :+ n) x -> (Vec m x, Vec n x)
> vchop Zy      xs         =  (V0,       xs)
> vchop (Sy m)  (x :> xs)  =  (x :> ys,  zs)
>   where (ys, zs) = vchop m xs

\end{frame}

\begin{frame}
\frametitle{Proxies (|forall ((n :: Nat)). Proxy n ->|)}

%format vtake = "\F{vtake}"

Compute the first component of |vchop|:

< vtake :: Natty m -> Vec (m :+ n) x -> Vec m x -- |BAD|
< vtake Zy      xs         =  V0
< vtake (Sy m)  (x :> xs)  =  x :> vtake m xs

Doesn't type check because GHC doesn't know how to instantiate |n| in
the recursive call.

%format kappa = "\kappa"

A proxy is an explicit representation of a type:

> data Proxy :: kappa -> * where
>   Proxy :: Proxy i

This type checks:

> vtake :: Natty m -> Proxy n -> Vec (m :+ n) x -> Vec m x
> vtake Zy      n  xs         =  V0
> vtake (Sy m)  n  (x :> xs)  =  x :> vtake m n xs

%format proxy = "\F{proxy}"

Generate a proxy from existing data:

> proxy :: f i -> Proxy i
> proxy _ = Proxy

\end{frame}

\begin{frame}
\frametitle{Implicit singletons (|forall n. NATTY n =>|)}

%format read = "\F{read}"

%format :**: = ":\!\!*\!*\!\!:"
%format :&&: = ":\!\!\&\!\&\!\!:"
 
%format natter = "\F{natter}"
%format natty = "\F{natty}"
%format vcopies = "\F{vcopies}"
%format vapp = "\F{vapp}"
%format pure = "\F{pure}"
%format traverse = "\F{traverse}"

%format fmap = "\F{fmap}"
%format fmapDefault = "\F{fmapDefault}"
%format foldMapDefault = "\F{foldMapDefault}"
%format foldMap = "\F{foldMap}"

> class NATTY (n :: Nat) where
>   natty :: Natty n
> 
> instance NATTY Z where
>   natty = Zy
> 
> instance NATTY n => NATTY (S n) where
>   natty = Sy natty

%format vtrunc = "\F{vtrunc}"

An implicit version of |vtake| that infers the required length from
the result type:

> vtrunc :: NATTY m => Proxy n -> Vec (m :+ n) x -> Vec m x
> vtrunc = vtake natty

< > vtrunc Proxy (1 :> 2 :> 3 :> 4 :> V0) :: Vec (S (S Z)) Int
< 1 :> 2 :> V0

\end{frame}


\begin{frame}
\frametitle{Four kinds of universal quantifier}

\[
\begin{array}{r||cc}
                 & \textbf{implicit}      & \textbf{explicit} \\
\hline
\textbf{static}  & |forall ((n :: Nat))|  & |forall ((n :: Nat)). Proxy n ->| \\
\textbf{dynamic} & |forall n. NATTY n =>| & |forall n. Natty n ->| \\
\end{array}
\]

\end{frame}

\begin{frame}
\frametitle{Instances for indexed types}

> instance NATTY n => Applicative (Vec n) where
>   pure   = vcopies natty
>   (<*>)  = vapp
>
> vcopies :: forall n x. Natty n -> x -> Vec n x
> vcopies  Zy      x  =  V0
> vcopies  (Sy n)  x  =  x :> vcopies n x   
>
> vapp :: forall n s t. Vec n (s -> t) -> Vec n s -> Vec n t
> vapp  V0         V0         = V0
> vapp  (f :> fs)  (s :> ss)  = f s :> vapp fs ss
                           
\end{frame}

%if False

> instance Traversable (Vec n) where
>   traverse f V0 = pure V0
>   traverse f (x :> xs) = (:>) <$> f x <*> traverse f xs
>
> instance Foldable (Vec n) where
>   foldMap = foldMapDefault
>
> instance Functor (Vec n) where
>   fmap = fmapDefault

%endif

\begin{frame}
\frametitle{Converting between implicit and explict singletons}

Implicit to explicit:

< natty :: NATTY n => Natty n

Explicit to implicit:

> natter :: Natty n -> (NATTY n => t) -> t
> natter  Zy      t  =  t
> natter  (Sy n)  t  =  natter n t

\end{frame}

%format cmp = "\F{cmp}"

%format juxH = "\F{juxH}"
%format juxV = "\F{juxV}"

%format maxLT = "\F{maxLT}"
%format maxEQ = "\F{maxEQ}"
%format maxGT = "\F{maxGT}"

%% duplicates

%format cmpBase = cmp
%format CmpBase = Cmp
%format LTNatBase = LTNat
%format EQNatBase = EQNat
%format GTNatBase = GTNat


%format juxHPain = juxH

\begin{frame}
\frametitle{Proof objects}

The result of comparing two natural numbers:

> data CmpBase :: Nat -> Nat -> * where
>   LTNatBase  :: Natty z  ->  CmpBase m (m :+ S z)
>   EQNatBase  ::              CmpBase m m
>   GTNatBase  :: Natty z  ->  CmpBase (n :+ S z) n

A comparison function:

> cmpBase :: Natty m -> Natty n -> CmpBase m n
> cmpBase Zy      Zy      = EQNatBase
> cmpBase Zy      (Sy n)  = LTNatBase n
> cmpBase (Sy m)  Zy      = GTNatBase m
> cmpBase (Sy m)  (Sy n)  = case cmpBase m n of
>   LTNatBase z  ->  LTNatBase z
>   EQNatBase    ->  EQNatBase
>   GTNatBase z  ->  GTNatBase z

\end{frame}

\begin{frame}
\frametitle{The Procrustes function}

Fit a vector of length |m| into a vector of length |n| by padding or
trimming as necessary:

> procrustes :: a -> Natty m -> Natty n -> Vec m a -> Vec n a
> procrustes p m n xs = case cmpBase m n of
>   LTNatBase z  -> vappend xs (vcopies (Sy z) p)
>   EQNatBase    -> xs
>   GTNatBase z  -> vtake n (proxy (Sy z)) xs 

\end{frame}



\begin{frame}
\frametitle{Boxes}

\begin{itemize}
\item Boxes are size-indexed rectangular tilings.
\item A box |b| with content of size-indexed type |p| and size |wh| has type
|Box p wh|.
\end{itemize}

> data Box :: ((Nat, Nat) -> *) -> (Nat, Nat) -> * where
>   Stuff  ::  p wh -> Box p wh
>   Clear  ::  Box p wh
>   Hor    ::  Natty w1  -> Box p (Pair w1 h)  ->
>              Natty w2  -> Box p (Pair w2 h)  -> Box p (Pair (w1 :+ w2) h)
>   Ver    ::  Natty h1  -> Box p (Pair w h1)  ->
>              Natty h2  -> Box p (Pair w h2)  -> Box p (Pair w (h1 :+ h2))


\end{frame}

\begin{frame}
\frametitle{Boxes are monads in a category of indexed types}

Morphisms:

> type s :-> t = forall i. s i -> t i

%format returnIx = "\F{returnIx}"
%format extendIx = "\F{extendIx}"

Monads over indexed types:

> class MonadIx (m :: (kappa -> *) -> (kappa -> *)) where
>   returnIx  ::  a :-> m a
>   extendIx  ::  (a :-> m b) -> (m a :-> m b)

|Box| is a |MonadIx|:

> instance MonadIx Box where
>   returnIx                       = Stuff
>   extendIx  f (Stuff c)          = f c
>   extendIx  f Clear              = Clear
>   extendIx  f (Hor w1 b1 w2 b2)  =
>     Hor w1 (extendIx f b1) w2 (extendIx f b2)
>   extendIx  f (Ver h1 b1 h2 b2)  =
>     Ver h1 (extendIx f b1) h2 (extendIx f b2)

\end{frame}


\begin{frame}
\frametitle{Two flavours of conjunction for indexed things}

Separating conjunction:

> data (p :: iota -> *) :**: (q :: kappa -> *) :: (iota, kappa) -> * where
>   (:&&:) :: p iota -> q kappa -> (p :**: q) (Pair iota kappa)


Non-separating conjunction:

> data (p :: kappa -> *) :*: (q :: kappa -> *) :: kappa -> * where
>   (:&:) :: p kappa -> q kappa -> (p :*: q) k

\end{frame}

% \usetikzlibrary{shapes.misc}
\usetikzlibrary{positioning}

\tikzset{stuff/.style={
% The shape:
rectangle,
minimum size=10mm,
% The rest
draw=black,
top color=white,bottom color=red!100,
font=\huge}}

\tikzset{stuff2/.style={
% The shape:
rectangle,
minimum size=22mm,
% The rest
draw=black,
top color=white,bottom color=blue!100,
font=\huge}}

\tikzset{blank/.style={
% The shape:
rectangle,
minimum size=10mm,
% The rest
draw=black}}

\tikzset{op/.style={
% The shape:
rectangle,
minimum size=5mm,
% The rest
draw=white,
font=\huge}}


\begin{frame}[fragile]
\frametitle{Horizontal juxtaposition}

Place two boxes side-by-side:

> juxHPain :: Size (Pair w1 h1) -> Size (Pair w2 h2) ->
>               Box p (Pair w1 h1) -> Box p (Pair w2 h2) -> Box p (Pair (w1 :+ w2) (Max h1 h2))
>
> type Size = Natty :**: Natty
>
> type family Max (m :: Nat) (n :: Nat) :: Nat
> type instance Max  Z      n      = n
> type instance Max  (S m)  Z      = S m
> type instance Max  (S m)  (S n)  = S (Max m n)

\begin{tikzpicture}[node distance=2mm and 2mm]
  \node (z0) [blank, draw=white] {~};
  \node (a0) [stuff, below=of z0] {~}; 
  \node (plus) [op, draw=white, right=of a0, yshift=6mm] {+};
  \node (b0) [stuff2, right=of plus] {~};
  \node (equals) [op, draw=white, right=of b0] {=};
  \node (z) [blank, right=of equals, yshift=6mm] {~};
  \node (a) [stuff, below=of z] {~}; 
  \node (b) [stuff2, right=of a, yshift=6mm] {~};
\end{tikzpicture}

\end{frame}

\begin{frame}
\frametitle{Horizontal Juxtaposition (broken)}

< juxH (w1 :&&: h1) (w2 :&&: h2) b1 b2 =
<   case cmp h1 h2 of
<     LTNat n  -> Hor w1 (Ver h1 b1 (Sy n) Clear) w2 b2   -- |BAD|
<     EQNat    -> Hor w1 b1 w2 b2                         -- |BAD|
<     GTNat n  -> Hor w1 b1 w2 (Ver h2 b2 (Sy n) Clear)   -- |BAD|

Doesn't type check because GHC has no way of knowing that the
height of the resulting box is the maximum of the heights of the
component boxes.

\end{frame}

\begin{frame}
\frametitle{Pain}

% For each case we must compute an explicit proof to satisfy the type checker:

> juxHPain (w1 :&&: h1) (w2 :&&: h2) b1 b2 =
>   case cmpBase h1 h2 of
>     LTNatBase z  -> maxLT h1 z  $ Hor w1 (Ver h1 b1 (Sy z) Clear) w2 b2
>     EQNatBase    -> maxEQ h1    $ Hor w1 b1 w2 b2
>     GTNatBase z  -> maxGT h2 z  $ Hor w1 b1 w2 (Ver h2 b2 (Sy z) Clear)
>
> maxLT ::  forall m z t.Natty m -> Natty z ->
>             ((Max m (m :+ S z) ~ (m :+ S z)) => t) -> t
> maxLT Zy      z  t  =  t
> maxLT (Sy m)  z  t  =  maxLT m z t
>
> maxEQ :: forall m t.Natty m -> ((Max m m ~ m) => t) -> t
> maxEQ Zy      t  =  t
> maxEQ (Sy m)  t  =  maxEQ m t
> 
> maxGT ::  forall n z t.Natty n -> Natty z ->
>             ((Max (n :+ S z) n ~ (n :+ S z)) => t) -> t
> maxGT Zy      z  t  =  t
> maxGT (Sy n)  z  t  =  maxGT n z t

\end{frame}

%format maxn = "\F{maxn}"

%format juxH = "\F{juxH}"
%format juxV = "\F{juxV}"
%format crop = "\F{crop}"
%format fit = "\F{fit}"
%format fitH  = "\F{fitH}"
%format fitV = "\F{fitV}"
%format clip = "\F{clip}"
%format clipH = "\F{clipH}"
%format clipV = "\F{clipV}"
%format crop = "\F{crop}"

%format horCut = "\F{horCut}"
%format verCut = "\F{verCut}"
%format cmpCuts = "\F{cmpCuts}"
%format cmp = "\F{cmp}"

%format mempty = "\F{mempty}"
%format mappend = "\F{mappend}"

%% duplicates

%format CmpBaseR = Cmp
%format LTNatBaseR = LTNat
%format EQNatBaseR = EQNat
%format GTNatBaseR = GTNat

%format CmpEx = Cmp
%format LTNatEx = LTNat
%format EQNatEx = EQNat
%format GTNatEx = GTNat

%format CmpMax = Cmp
%format LTNatMax = LTNat
%format EQNatMax = EQNat
%format GTNatMax = GTNat

\begin{frame}
\frametitle{Type equations for free}

% \only<1>{

> data CmpBaseR :: Nat -> Nat -> * where
>   LTNatBaseR  :: Natty z  ->  CmpBaseR m (m :+ S z)
>   EQNatBaseR  ::              CmpBaseR m m
>   GTNatBaseR  :: Natty z  ->  CmpBaseR (n :+ S z) n

% }
% \only<2>{

Make GADT type equations explicit:

> data CmpEx :: Nat -> Nat -> * where
>   LTNatEx :: ((m :+ S z) ~ n)  => Natty z ->  CmpEx m n
>   EQNatEx :: (m ~ n)           =>             CmpEx m n
>   GTNatEx :: (m ~ (n :+ S z))  => Natty z ->  CmpEx m n

% }
% \only<3->{

Add more type equations:

> data CmpMax :: Nat -> Nat -> * where
>   LTNatMax :: ((m :+ S z) ~ n,  Max m n ~ n)  => Natty z ->  CmpMax m n
>   EQNatMax :: (m ~ n,           Max m n ~ m)  =>             CmpMax m n
>   GTNatMax :: (m ~ (n :+ S z),  Max m n ~ m)  => Natty z ->  CmpMax m n

% }
\end{frame}

\begin{frame}
\frametitle{Pleasure}

> juxH ::  Size (Pair w1 h1) -> Size (Pair w2 h2) ->
>   Box p (Pair w1 h1) -> Box p (Pair w2 h2) -> Box p (Pair (w1 :+ w2) (Max h1 h2))
> juxH (w1 :&&: h1) (w2 :&&: h2) b1 b2 =
>   case cmp h1 h2 of
>     LTNat z  -> Hor w1 (Ver h1 b1 (Sy z) Clear) w2 b2
>     EQNat    -> Hor w1 b1 w2 b2
>     GTNat z  -> Hor w1 b1 w2 (Ver h2 b2 (Sy z) Clear)

The required properties of maximum are now available as type equations
in the proof object.

\end{frame}

\begin{frame}
\frametitle{Scalability}

\begin{itemize}
\item Can add extra type equations to |Cmp| by hand.
\item Seems difficult to be more modular without higher-order
  constraints.
\item Works for equations on other functions defined inductively on
  the structure of natural numbers (e.g. subtraction).
\end{itemize}

\end{frame}

\begin{frame}
\frametitle{Existentials}

> data Ex (p :: kappa -> *) where
>   Ex :: p i -> Ex p

A `wrapped |Nat|' is a |Natty| singleton for any type-level number.

> type WNat = Ex Natty

Translating a |Nat| to its wrapped version:

> wrapNat :: Nat -> WNat
> wrapNat  Z      =  Ex Zy
> wrapNat  (S m)  =  case wrapNat m of Ex n -> Ex (Sy n)

\begin{itemize}
\item Now we can take a plain natural number at run-time and use it in
  code that expects a |Natty|.

\item Particularly useful for interfacing with library code which uses
  plain natural numbers.
%% (e.g. we interface our boxes library with curses to implement a
%%   screen editor).
\end{itemize}

\end{frame}

\begin{frame}
\frametitle{Other stuff}

In the paper:

\begin{itemize}
\item Philosophy.

\item An implementation of merge sort that guarantees the ordering
  invariant for its output in which the proofs are silent.

\item More on boxes:
  \begin{itemize}
  \item  cropping
  \item  monoidal structure of boxes
  \item  a screen editor using boxes
  \end{itemize}
\end{itemize}

Literate Haskell code at:

\url{https://github.com/slindley/dependent-haskell/tree/master/Hasochism}

\end{frame}

\begin{frame}
\frametitle{Conclusion}

\begin{itemize}
\item Dependently-typed programming in Haskell is already feasible.
\item The proliferation of representations of the same data type
  (|Nat|, |Natty|, |NATTY|, and |WNat|) is painful.
\item We might alleviate some pain by providing more uniform support
  for different kinds of universal quantifier and allowing each type
  to be used unduplicated wherever meaningful.
\end{itemize}

\end{frame}

%if False

> cmp :: Natty m -> Natty n -> Cmp m n
> cmp Zy      Zy      = EQNat
> cmp Zy      (Sy n)  = LTNat n
> cmp (Sy m)  Zy      = GTNat m
> cmp (Sy m)  (Sy n)  = case cmp m n of
>   LTNat z  ->  LTNat z
>   EQNat    ->  EQNat
>   GTNat z  ->  GTNat z

> type family (m :: Nat) :- (n :: Nat) :: Nat
> type instance Z    :-  n    = Z
> type instance S m  :-  Z    = S m
> type instance S m  :-  S n  = (m :- n)

> data Cmp :: Nat -> Nat -> * where
>   LTNat :: ((m :+ S z) ~ n,  Max m n ~ n,  (m :- n) ~ Z)    =>
>       Natty z ->  Cmp m n
>   EQNat :: (m ~ n,           Max m n ~ m,  (m :- n) ~ Z)    =>
>                   Cmp m n
>   GTNat :: (m ~ (n :+ S z),  Max m n ~ m,  (m :- n) ~ S z)  =>
>       Natty z ->  Cmp m n

%endif

\end{document}
