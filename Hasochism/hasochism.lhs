\documentclass[preprint]{sigplanconf}


% US Letter page size
%\pdfpagewidth=8.5in
%\pdfpageheight=11in

%include polycode.fmt
%include forall.fmt

\DeclareMathAlphabet{\mathkw}{OT1}{cmss}{bx}{n}
%subst keyword a = "\mathkw{" a "}"
%subst conid a = "\mathsf{" a "}"
%format where = "\;\mathkw{where}"
%format family = "\mathkw{family}"

%format * = "\star\,"
%format PRIME = "{}^{\prime}\!\!"
%format PRIMEPRIME = "{}^{\prime\prime}\!\!"

%format :+ = ":\!\!+\,"
%format :- = ":\!\!-\,"

%format /+/ = "/\!\!+\!\!/"
%format /-/ = "/\!\!-\!\!/"

%format <$> = "<\!\!\mathord{\$}\!\!>"
%format <*> = "<\!\!\mathord{\star}\!\!>"


%format x1 = "x_1"
%format x2 = "x_2"

%format y1 = "y_1"
%format y2 = "y_2"

%format w1 = "w_1"
%format w2 = "w_2"

%format h1 = "h_1"
%format h2 = "h_2"

%format wh1 = "\mathit{wh}_1"
%format wh2 = "\mathit{wh}_2"


%format b1 = "b_1"
%format b2 = "b_2"
%format b11 = "b_{11}"
%format b12 = "b_{12}"
%format b21 = "b_{21}"
%format b22 = "b_{22}"

%format EXISTS = "\exists\!"
%format DOT = "\!\!.\!\!"

\renewcommand{\hscodestyle}{\small}

\usepackage{amsmath}
\usepackage{xspace}

\newcommand{\singletons}{\textsf{singletons}\xspace}

\begin{document}

\conferenceinfo{Name}{Date, Address} 
\copyrightyear{Year} 
\copyrightdata{[to be supplied]} 

%% \titlebanner{banner above paper title}        % These are ignored unless
%% \preprintfooter{short description of paper}   % 'preprint' option specified.

\title{Hasochism}
%\subtitle{Subtitle Text, if any}

\authorinfo{Sam Lindley}
           {University of Strathclyde}
           {sam.lindley@@strath.ac.uk}
\authorinfo{Conor McBride}
           {University of Strathclyde}
           {conor.mcbride@@strath.ac.uk}

\maketitle

\begin{abstract}
\end{abstract}

%% \category{CR-number}{subcategory}{third-level}

%% \terms
%% term1, term2

%% \keywords
%% keyword1, keyword2

\section{Introduction}

In the design of Standard ML, Milner and his colleagues achieved a remarkable
alignment of distinctions:
\[\begin{array}{||l||||r||l||}
\hline
\textrm{syntactic category}  & \textbf{terms}      &     \textbf{types} \\
\textrm{phase distinction}   & \textbf{dynamic}    &    \textbf{static} \\
\textrm{inference}           & \textbf{explicit}   &  \textbf{implicit} \\
\textrm{abstraction}         & \textbf{simple}     & \textbf{dependent} \\
\hline
\end{array}\]

The things you write are the things you run, namely terms, for which
abstraction (with an explicit $\lambda$) is simply typed---the bound
variable does not occur in the return type of the function. The things
which you leave to be inferred, namely polymorphic type schemes, exist
only at compile time and allow (outermost) dependent abstraction over
types, with implicit application at usage sites instantiating the
bound variables.

An unintended consequence of Milner's achievement is that we sometimes
blur the distinctions between these distinctions. We find it hard to
push them out of alignment because we lose sight of the very
possibility of doing so. For example, some have voiced objections to
the prospect of terms in types on the grounds that efficient
compilation relies on erasure to the dynamic fragment of the
language. However, renegotiating the term/type distinction need not
destroy the dynamic/static distinction, as shown by the Coq's
venerable program extraction algorithm, erasing types and proofs from
dependently typed constructions.

Meanwhile, Haskell's type classes demonstrate the value of dynamic
components which are none the less implicit---instance
dictionaries. Indeed, type inference seems a timid virtue once you
glimpse the prospect of \emph{program} inference, yet some are made
nervous by the prospect of unwritten programs being run. Similarly,
Haskell's combination of higher kinds and constraints means that
sometimes static types must be given explicitly, in order not only to
check them, but also to drive the generation of invisible boilerplate.

\section{$\Pi$ versus $\forall$ versus explicit $\forall$}

%include natvec.lhs

\section{Explicit $\Pi$ versus implicit $\Pi$}

%include pies.lhs

\section{The NATTY-in-Natty question}

%include NATTYInNatty.lhs

\section{Classes-as-relations --- silence is golden}

%include MergeSort.lhs

\section{Evidence is data and proof}

%include evidence.lhs

\section{Box library (first-attempt)}

%include box-one.lhs

\section{Box library (second-attempt)}

%include box-two.lhs

\section{Conclusion}

\newpage

[OLD stuff]

\section{Boxes}

building UIs with boxes

...

in order to ensure boxes are well-formed, we index the type of a box
type by its size

\subsection{Promoting natural numbers}

Data type of natural numbers:

> data Nat = Z | S Nat

The data type |Nat| can be promoted to a data kind, and the term
constructors |Z| and |S| can be promoted to type constructors.

To bridge the gap between terms and types, we also define a
\emph{singleton} data type |SNat|, which mirrors the structure of
|Nat|.

> data SNat :: Nat -> * where
>   SZ :: SNat Z
>   SS :: SNat n -> SNat (S n)

A value of type |Nat| is a plain natural number $n$, whereas a value
of type |Nat| is a natural number $n$ indexed by $n$ as a promoted
|Nat|. For any type |n| of the promoted kind |Nat|, there is but a
single inhabitant of |SNat n| (discounting |undefined|).

It is sometimes useful to infer the corresponding |SNat| from a
promoted |Nat|. This is exactly what the |NATTY| type class does:

> class NATTY (n :: Nat) where
>   natty :: SNat n
> 
> instance NATTY Z where
>   natty = SZ
> 
> instance NATTY n => NATTY (S n) where
>   natty = SS natty

%% The |NATTY| type class has exactly the same structure as the |Nat| and
%% |SNat| data types. In total we have given four different
%% representations of the natural number data type: the |Nat| data type,
%% the promoted |Nat| data kind, the singleton |SNat| data type, and the
%% |NATTY| type class. Given the |Nat| data type, promotion gives us the
%% data kind for free. In constrast, the singleton data type and type
%% class are defined manually.

Occasionally we have at hand an explicit |SNat n|, but would like to
use it in a context with an implicit |NATTY n| type class constraint.

> natter :: SNat n -> (NATTY n => t) -> t
> natter SZ     t = t
> natter (SS n) t = natter n t

The |natter| function effectively converts an explicit |SNat| to an
implicit |NATTY|.

\paragraph*{Operations on natural numbers}

In general, each operation on natural numbers must be defined three
times: once for |Nat| values, once for promoted |Nat| types, and once
for |SNat| values. In this paper we will only give definitions for the
latter two cases, as they are the only ones we use for our
examples. We define such functions for addition, maximum, and
subtraction.

Addtion on |Nat| types is defined as a type family.

> type family (m :: Nat) :+ (n :: Nat) :: Nat
> type instance Z :+ n = n
> type instance S m :+ n = S (m :+ n)

Addition on |SNat| values is defined as a function.

> (/+/) :: SNat m -> SNat n -> SNat (m :+ n)
> SZ /+/ n = n
> SS m /+/ n = SS (m /+/ n)

Notice that the type of the function depends on the type family. The
definitions of subtraction and maximum are similar.

> type family (m :: Nat) :- (n :: Nat) :: Nat
> type instance Z   :- n   = Z
> type instance S m :- Z   = S m
> type instance S m :- S n = (m :- n)
> 
> (/-/) :: SNat m -> SNat n -> SNat (m :- n)
> SZ   /-/ n    = SZ
> SS m /-/ SZ   = SS m
> SS m /-/ SS n = m /-/ n
>
> type family Max (m :: Nat) (n :: Nat) :: Nat
> type instance Max Z     n     = n
> type instance Max (S m) Z     = S m
> type instance Max (S m) (S n) = S (Max m n)
> 
> maxn :: SNat m -> SNat n -> SNat (Max m n)
> maxn SZ     n      = n
> maxn (SS m) SZ     = SS m
> maxn (SS m) (SS n) = SS (maxn m n)

To keep the definitions total we assert that $0 - n = 0$ for all $n$.

\paragraph*{The \singletons library}

Using Eisenberg and Weirich's \singletons
library~\cite{singletons} we can automatically generate the |SNat| and
|NATTY| type class from the |Nat| data type.

> data Nat = Z | S Nat
> 
> $(genSingletons [PRIMEPRIME Nat])
> 
> type NATTY = SingRep
> 
> natty :: NATTY n => SNat n
> natty = sing
> 
> natter :: SNat n -> (NATTY n => t) -> t
> natter n b = case singInstance n of SingInstance -> b

%$

There is one material difference between our hand-coded version and
the singleton data type generated by the \singletons
library. Modulo inessential differences, the latter generates the
following datatype:

< data SNat :: Nat -> * where
<   SZ :: SNat Z
<   SS :: NATTY n => SNat n -> SNat (S n)

Unlike our original version, the generated singleton has a |NATTY|
constraint on the |SS| constructor.

%% We discuss the impact of this design choice in
%% Section~\ref{sec:extra-singleton-constraint}.

Another feature of the \singletons library is that it allows one to
automatically generate operations on |Nat| values, promoted |Nat|
types, and singleton |SNat| values from a single function definition.

< $(singletons [d|
<   plus :: Nat -> Nat -> Nat
<   Z     `plus` n = n
<   (S m) `plus` n = S (m `plus` n)|])
< 
< type m :+ n = m `Plus` n
< (/+/) = sPlus

%$

\subsection{Boxes without size-indexed types}

We present an abstract GUI library based on \emph{boxes}, which
represent rectangular chunks of two-dimensional space.

> type Box a = (Size, Block a)
> type Size = (Int, Int)
> data Block a
>   = Stuff a
>   | Clear                    
>   | Ver (Box a) (Box a)
>   | Hor (Box a) (Box a)

The type of a box is indexed by the type of its underlying
content. Boxes are constructed from underlying content, clear boxes,
and horizontal and vertical composition.
%
Each box is indexed by its size. This information appears in the value
of a box, but not in its type. In the next section we will present a
type-indexed variant of boxes, in which the type of a box is indexed
by its size.

We can join two boxes together, horizontally or vertically, adding
appropriate padding if the sizes do not match up.

> joinH :: Box a -> Box a -> Box a
> joinH b1@((w1, h1), _) b2@((w2, h2), _)
>   | h1 < h2
>   = (  (w1 + w2, h2),
>        Hor ((w1, h2), Ver b1 ((w1, h2 - h1), Blank)) b2)
>   | h1 == h2 = ((w1 + w2, h1), Hor b1 b2)
>   | h1 > h2
>   = (  (w1 + w2, h1),
>        Hor b1 ((w2, h1), Ver b2 ((w2, h1 - h2), Blank)))
> 
> joinV :: Box a -> Box a -> Box a
> joinV b1@((w1, h1), _) b2@((w2, h2), _)
>   | w1 < w2
>   = (  (w2, h1 + h2),
>        Ver ((w2, h1), Hor b1 ((w2 - w1, h1), Blank)) b2)
>   | w1 == w2 = ((w1, h1 + h2), Ver b1 b2)
>   | w1 > w2
>   = (  (w1, h1 + h2),
>        Ver b1 ((w1, h2), Hor b2 ((w1 - w2, h2), Blank)))

For cutting up boxes, and two-dimensional entities in general, we
introduce a type class |Cut|.

> class Cut a where
>   horCut :: Int -> a -> (a, a)
>   verCut :: Int -> a -> (a, a)

We can cut horizontally or vertically by supplying the position at
which to perform the cut.

> instance Cut a => Cut (Block a) where
>   horCut m (Stuff p) = (Stuff p1, Stuff p2)
>     where (p1, p2) = horCut m p
>   horCut m Clear = (Clear, Clear)
>   horCut m (Hor ((w1, h1), b1) ((w2, h2), b2))
>     | m < w1  =  let (b11, b12) = horCut m b1
>                  in (b11, Hor ((w1-m, h1), b12) ((w2, h2), b2))
>     | m == w1 =  (b1, b2)
>     | m > w1  =  let (b21, b22) = horCut (m-w1) b2
>                  in (Hor ((w1, h1), b1) ((m-w1, h2), b21), b22)
>   horCut m (Ver (wh1, b1) (wh2, b2)) =
>     (Ver (wh1, b11) (wh2, b21), Ver (wh1, b12) (wh2, b22))
>     where (b11, b12) = horCut m b1
>           (b21, b22) = horCut m b2
> 
>   verCut m (Stuff p) = (Stuff p1, Stuff p2)
>     where (p1, p2) = verCut m p
>   verCut m Clear = (Clear, Clear)
>   verCut m (Ver ((w1, h1), b1) ((w2, h2), b2))
>     | m < h1  =  let (b11, b12) = verCut m b1
>                  in (b11, Ver ((w1, h1-m), b12) ((w2, h2), b2))
>     | m == h1 =  (b1, b2)
>     | m > h1  =  let (b21, b22) = verCut (m-h1) b2
>                  in (Ver ((w1, h1), b1) ((w2, m-h1), b21), b22)
>   verCut m (Hor (wh1, b1) (wh2, b2)) =
>     (Hor (wh1, b11) (wh2, b21), Hor (wh1, b12) (wh2, b22))
>     where (b11, b12) = verCut m b1
>           (b21, b22) = verCut m b2
>
> instance Cut a => Cut (Box a) where
>   horCut m ((w, h), b) = (((m, h), b1), ((w-m, h), b2))
>     where (b1, b2) = horCut m b
>   verCut m ((w, h), b) = (((w, m), b1), ((w, h-m), b2))
>     where (b1, b2) = verCut m b

The definition of cutting for boxes is routine. When cutting the
composition of two sub-boxes, we must identify which sub-box the cut
occurs in, and recurse appropriately. Note that we will also need to
define cutting for underlying content.

We now proceed to define cropping in terms of cutting.

A point identifies a position inside a box, where |(0, 0)| represents
the top-left corner, and we count top-to-bottom, left-to-right.

> type Point = (Int, Int)

A size is a pair of a width and a height.

> type Size = (Int, Int)

A region identifies a rectangular area inside a box by a pair of the
point representing the top-left corner of the region, and the size of
the region.

> type Region = (Point, Size)

We can \emph{crop} a box to a region. We decompose cropping into two
parts, \emph{clipping} and \emph{fitting}.

> clip :: Cut p => Point -> Box p -> Box p
> clip (x, y) b@((w, h), _) = clipV y (clipH x b)
> 
> clipH :: Cut p => Int -> Box p -> Box p
> clipH x b@((w, h), _)
>   | w > x = snd (horCut x b)
>   | w <= x = ((x-w, h), Clear)
> 
> clipV :: Cut p => Int -> Box p -> Box p
> clipV y b@((w, h), _)
>   | h > y = snd (verCut y b)
>   | h <= y = ((w, y-h), Clear)

Clipping discards everything to the left and above the specified
point.

> fit :: Cut p => Size -> Box p -> Box p
> fit (w, h) b = fitV h (fitH w b)
> 
> fitH :: Cut p => Int -> Box p -> Box p
> fitH w2 box@((w1, h), _)
>   | w1 < w2  = ((w2, h), Hor box ((w2-w1, h), Clear))
>   | w1 == w2 = box
>   | w1 > w2  = fst (horCut w2 box)
> 
> fitV :: Cut p => Int -> Box p -> Box p
> fitV h2 box@((w, h1), _)
>   | h1 < h2  = ((w, h2), Ver box ((w, h2-h1), Clear))
>   | h1 == h2 = box
>   | h1 > h2  = fst (verCut h2 box)

Fitting pads or cuts a box to the given size.

> crop :: Cut p => Region -> Box p -> Box p
> crop ((x, y), (w, h)) b =
>   fit (w, h) (clip (x, y) b)

To crop a box to a region, we simply clip then fit.

\subsection{Boxes with size-indexed types}

Taking advantage of GHC's data type promotion feature (enabled with
the |DataKinds| extension), we now adapt our code in order to index
the \emph{type} of each box by its size.

The main advantage of doing this is that we can statically guarantee
that only well-formed boxes can be constructed.

> data Box :: ((Nat, Nat) -> *) -> (Nat, Nat) -> * where
>   Stuff :: p wh -> Box p wh
>   Clear :: Box p wh
>   Hor ::  SNat w1 -> Box p PRIME(w1, h) ->
>           SNat w2 -> Box p PRIME(w2, h) -> Box p PRIME(w1 :+ w2, h)
>   Ver ::  SNat h1 -> Box p PRIME(w, h1) ->
>           SNat h2 -> Box p PRIME(w, h2) -> Box p PRIME(w, h1 :+ h2)

When composing boxes horizontally, we add together their widths, at
the level of types. The widths of the boxes are stored as
witnesses. We can only compose two boxes horizontally if they have the
same height. The situation is analogous for composing boxes
vertically.

Let us consider how to define the join operations for type-indexed
boxes. This is where things start to get interesting. Suppose we wish
to join two boxes horizontally. The final width is given by the sum of
the widths of the two boxes. The final height is the maximum of the
heights of the two boxes. We might expect to give |joinH| the
following type:

< Box p PRIME(w1, h1) -> Box p PRIME(w2, h2) ->
<   Box p PRIME(w1 :+ w2, Max h1 h2)

As we will need to reason by comparing the sizes of the two boxes as
values, we add two extra arguments to |joinH|, one for the size of
each box.

> joinH :: (SNat w1, SNat h1) -> (SNat w2, SNat h2) ->
>            Box p PRIME(w1, h1) -> Box p PRIME(w2, h2) ->
>              Box p PRIME(w1 :+ w2, Max h1 h2)

Let us define a comparison function on singleton natural numbers.

< cmp :: SNat m -> SNat n -> Ordering
< cmp SZ     SZ     = EQ
< cmp SZ     (SS n) = LT
< cmp (SS m) SZ     = GT
< cmp (SS m) (SS n) = cmp m n

Now we can attempt to write a definition for joinH as follows:

> joinH (w1, h1) (w2, h2) b1 b2 =
>   case cmp h1 h2 of
>     LT -> Hor  w1  (Ver  h1
>                          b1
>                          (h2 /-/ h1)
>                          (clear (w1, h2 /-/ h1)))
>                w2  b2
>     EQ -> Hor  w1  b1 w2 b2
>     GT -> Hor  w1  b1 w2 (Ver  h2
>                                b2
>                                (h1 /-/ h2)
>                                (clear (w2, h1 /-/ h2)))

Alas, this does not type check, because GHC has no way of knowing the
necessary laws of arithmetic (such as $h_1 + (h_2-h_1) = h_2$) and
$\mathit{max}(h_1, h_2) = h_2$ whenever $h_1 \leq h_2$).

One approach to resolving this issue is to encode each of the required
laws as lemmas. What we need to do is to ensure that the corresponding
type equalities are in the typing context. For instance here is an
encoding of the lemma that $\mathit{max}(x, x) = x$:

> maxRefl :: forall x t.SNat x -> ((Max x x ~ x) => t) -> t
> maxRefl SZ     t = t
> maxRefl (SS x) t = maxRefl x t

To instantiate |maxRefl|, we supply it with a natural number, and the
corresponding type equality constraint is brought into scope.

[TODO: should probably give a worked example of using such a law.]

In general such laws are encoded by functions of type:

< forall x_1 ... x_n.SNat x_1 -> ... -> SNat x_n -> ((l ~ r) => t) -> t

where |l| and |r| are the left- and right-hand-side of the law.

Using this pattern, it is now possible to use GHC as a theorem
prover. As GHC does not provide anything in the way of direct support
for theorem proving (along the lines of tactics in Coq), we would like
to avoid the pain of explicit theorem proving as much as
possible. Thus we present an alternative approach.

The key idea is to encode the laws we need in suitable proof objects
in such a way that the laws hold by construction. Let us refine the
standard Haskell |Ordering| type to be indexed by the natural numbers
under comparison. As a naive first attempt, we might try the
following:

< data Cmp :: Nat -> Nat -> * where
<   LTNat :: Cmp m (m :+ S z)
<   EQNat :: Cmp m m
<   GTNat :: Cmp (n :+ S z) n

The equals case is straightforward: $m = m$. If |m < n|, then there
exists some |z| such that $n = m + (z + 1)$. Similarly if |m > n| then
there exists some |z| such that $m = n + (z + 1)$.

Often it is useful to be able to compute on the difference between the
two numbers as a value. In the |EQNat| case, this is simply |0|. In
the other two cases it is |z + 1|, thus in each case we store a
singleton representation of |z| as a witness.

< data Cmp :: Nat -> Nat -> * where
<   LTNat :: SNat z -> Cmp m (n :+ S z)
<   EQNat :: Cmp x x
<   GTNat :: SNat z -> Cmp (n :+ S z) n

We can refine our comparison function accordingly.

> cmp :: SNat x -> SNat y -> Cmp x y
> cmp SZ     SZ     = EQNat
> cmp SZ     (SS y) = LTNat y
> cmp (SS x) SZ     = GTNat x
> cmp (SS x) (SS y) = case cmp x y of
>   LTNat z -> LTNat z
>   EQNat   -> EQNat
>   GTNat z -> GTNat z

Let us write a definition for |joinH|.

> joinH (w1, h1) (w2, h2) b1 b2 =
>   case cmp h1 h2 of
>     LTNat n  ->
>       Hor w1 (Ver h1 b1 (SS n) (clear (w1, SS n))) w2 b2
>     EQNat    -> Hor w1 b1 w2 b2
>     GTNat n  ->
>       Hor w1 b1 w2 (Ver h2 b2 (SS n) (clear (w2, SS n)))

The property that $y_1 < y_2$ implies that there exists a $z$ such
that $y_2 = y_1 + (z + 1)$, is now implicit in the proof object |LTNat
n| --- the type of |n| is |SNat z|. Unfortunately, this code still
does not type check, because GHC still has now way of knowing the
properties relating comparisons and |max|.

Again, we could proceed by proving suitable lemmas. Instead, we shove
the law we need into the |Cmp| proof objects. First, we note that our
previous definition of |Cmp| is equivalent to the following version.

< data Cmp :: Nat -> Nat -> * where
<   LTNat :: ((m :+ S z)  ~ n        )  =>
<     SNat z ->  Cmp m n
<   EQNat :: (m           ~ n        )  =>
<                Cmp m n
<   GTNat :: (m           ~ (n :+ S z)) => 
<     SNat z ->  Cmp m n

GADT = existential data types + type equalities.

Now, we can add some more equalities concerning |Max|.

< data Cmp :: Nat -> Nat -> * where
<   LTNat :: ((m :+ S z)  ~ n,           Max m n ~ n)  =>
<     SNat z ->  Cmp m n
<   EQNat :: (m           ~ n,           Max m n ~ m)  =>
<                Cmp m n
<   GTNat :: (m           ~ (n :+ S z),  Max m n ~ m)  =>
<     SNat z ->  Cmp m n

Having added these straightforward equalities, our definition of
|joinH| now type checks! 

The |joinV| function is defined similarly.

> joinV :: (SNat w1, SNat h1) -> (SNat w2, SNat h2) ->
>            Box p PRIME(w1, h1) -> Box p PRIME(w2, h2) ->
>              Box p PRIME(Max w1 w2, h1 :+ h2)
> joinV (w1, h1) (w2, h2) b1 b2 =
>   case cmp w1 w2 of
>     LTNat n  ->
>       Ver h1 (Hor w1 b1 (SS n) (clear (SS n, h1))) h2 b2
>     EQNat    -> Ver h1 b1 h2 b2
>     GTNat n  ->
>       Ver h1 b1 h2 (Hor w2 b2 (SS n) (clear (SS n, h2)))

We refine the |Cut| type class, adding an extra argument to each of
the |horCut| and |verCut| functions.

> class Cut (p :: (Nat, Nat) -> *) where
>   horCut :: SNat m -> SNat n ->
>               p PRIME(m :+ n, h) -> (p PRIME(m, h), p PRIME(n, h))
>   verCut :: SNat m -> SNat n ->
>               p PRIME(w, m :+ n) -> (p PRIME(w, m), p PRIME(w, n))

Thus |horCut| takes natural numbers |m| and |n|, an indexed thing of
width $m + n$ and height $h$, and cuts it into two indexed things of
height |h|, one of width |m|, and the other of width |n|. The |verCut|
function is similar.

In order to handle the case in which we horizontally cut the
horizontal composition of two boxes, we need to perform a special kind
of comparison. In general, we wish to compare natural numbers $a$ and
$c$ in the presence of the equation $a + b = c + d$, and capture the
constraints on $a$, $b$, $c$, and $d$ that are implied by the result
of the comparison. For instance, if $a \leq c$ then there must exist
some number $z$, such that $b = (z + 1) + d$ and $c = a + (z + 1)$.

We encode proof objects for cut comparisons using the following data
type.

> data CmpCuts :: Nat -> Nat -> Nat -> Nat -> * where
>   LTCuts :: (b ~ (S z :+ d), c ~ (a :+ S z)) =>
>     SNat z ->  CmpCuts a b c d
>   EQCuts :: (a ~ c, b ~ d) =>
>                CmpCuts a b c d
>   GTCuts :: (a ~ (c :+ S z), d ~ (S z :+ b)) =>
>     SNat z ->  CmpCuts a b c d 

We can straightforwardly define a cut comparison function.

> cmpCuts :: ((a :+ b) ~ (c :+ d)) =>
>   SNat a -> SNat b ->
>   SNat c -> SNat d ->
>     CmpCuts a b c d
> cmpCuts SZ b SZ     d  = EQCuts
> cmpCuts SZ b (SS c) d  = LTCuts c
> cmpCuts (SS a) b SZ d  = GTCuts a
> cmpCuts (SS a) b (SS c) d = case cmpCuts a b c d of
>   LTCuts z  -> LTCuts z
>   EQCuts    -> EQCuts
>   GTCuts z  -> GTCuts z
> 

Now we define cuts for boxes.

> instance Cut p => Cut (Box p) where
>   horCut m n (Stuff p) = (Stuff p1, Stuff p2)
>     where (p1, p2) = horCut m n p
>   horCut m n Clear = (Clear, Clear)
>   horCut m n (Hor w1 b1 w2 b2) =
>     case cmpCuts m n w1 w2 of
>       LTCuts z  ->  let (b11, b12) = horCut m (SS z) b1
>                     in (b11, Hor (SS z) b12 w2 b2)
>       EQCuts    ->  (b1, b2)
>       GTCuts z  ->  let (b21, b22) = horCut (SS z) n b2
>                     in (Hor w1 b1 (SS z) b21, b22)
>   horCut m n (Ver h1 b1 h2 b2) =
>     (Ver h1 b11 h2 b21, Ver h1 b12 h2 b22)
>     where (b11, b12) = horCut m n b1
>           (b21, b22) = horCut m n b2
> 
>   verCut m n (Stuff p) = (Stuff p1, Stuff p2)
>     where (p1, p2) = verCut m n p
>   verCut m n Clear = (Clear, Clear)
>   verCut m n (Ver h1 b1 h2 b2) =
>     case cmpCuts m n h1 h2 of
>       LTCuts z  ->  let (b11, b12) = verCut m (SS z) b1
>                     in (b11, Ver (SS z) b12 h2 b2)
>       EQCuts    ->  (b1, b2)
>       GTCuts z  ->  let (b21, b22) = verCut (SS z) n b2
>                     in (Ver h1 b1 (SS z) b21, b22)
>   verCut m n (Hor w1 b1 w2 b2) =
>     (Hor w1 b11 w2 b21, Hor w1 b12 w2 b22)
>     where (b11, b12) = verCut m n b1
>           (b21, b22) = verCut m n b2

We already have most of the machinery we need for defining clipping,
fitting, and thus cropping. Let us define some type aliases first.

> type Size w h = (SNat w, SNat h)
> type Point x y = (SNat x, SNat y)
> type Region x y w h = (Point x y, Size w h)

The type of |clip| is:

< Cut p => Size w h -> Point x y ->
<            Box p PRIME(w, h) -> Box p PRIME(w :- x, h :- y)

In order to account for the subtraction in the result, we need to
augment our |Cmp| data type to include the necessary equations.

> data Cmp :: Nat -> Nat -> * where
>   LTNat ::
>     ((m :+ S z)   ~ n,           Max m n ~ n,  (m :- n) ~ Z)    =>
>       SNat z ->  Cmp m n
>   EQNat ::
>     (m            ~ n,           Max m n ~ m,  (m :- n) ~ Z)    =>
>                  Cmp m n
>   GTNat ::
>     (m            ~ (n :+ S z),  Max m n ~ m,  (m :- n) ~ S z)  =>
>       SNat z ->  Cmp m n

Now we can define clipping, fitting, and cropping.

> clip :: Cut p => Size w h -> Point x y ->
>   Box p PRIME(w, h) -> Box p PRIME(w :- x, h :- y)
> clip (w, h) (x, y) b = clipV (w /-/ x, h) y (clipH (w, h) x b)
> 
> clipH :: Cut p => Size w h -> SNat x ->
>   Box p PRIME(w, h) -> Box p PRIME(w :- x, h)
> clipH (w, h) x b = case cmp w x of
>   GTNat d  -> snd (horCut x (SS d) b)
>   _        -> Clear
> 
> clipV :: Cut p => Size w h -> SNat y ->
>   Box p PRIME(w, h) -> Box p PRIME(w, h :- y)
> clipV (w, h) y b = case cmp h y of
>   GTNat d  -> snd (verCut y (SS d) b)
>   _        -> Clear
>
> fit :: Cut p => Size w1 h1 -> Size w2 h2 ->
>   Box p PRIME(w1, h1) -> Box p PRIME(w2, h2)
> fit (w1, h1) (w2, h2) b = fitV h1 h2 (fitH w1 w2 b)
> 
> fitH :: Cut p => SNat w1 -> SNat w2 ->
>   Box p PRIME(w1, h) -> Box p PRIME(w2, h)
> fitH w1 w2 b = case cmp w1 w2 of
>   LTNat d  -> Hor w1 b (SS d) Clear
>   EQNat    -> b
>   GTNat d  -> fst (horCut w2 (SS d) b)
> 
> fitV :: Cut p => SNat h1 -> SNat h2 ->
>   Box p PRIME(w, h1) -> Box p PRIME(w, h2)
> fitV h1 h2 b = case cmp h1 h2 of
>   LTNat d  -> Ver h1 b (SS d) Clear
>   EQNat    -> b
>   GTNat d  -> fst (verCut h2 (SS d) b)
>
> crop :: Cut p => Region x y w h -> Size s t ->
>   Box p PRIME(s, t) -> Box p PRIME(w, h)
> crop ((x, y), (w, h)) (s, t) b =
>   fit (s /-/ x, t /-/ y) (w, h) (clip (s, t) (x, y) b)

A convenient feature of our cropping code is that type-level
subtraction is confined to the |clip| function. This works because in
the type of |fit| the output box is independent of the size of the
input box.

In an earlier version of the code we experimented with a cropping
function of type:

> Cut p => Region x y w h -> Size s t ->
>   Box p PRIME(s, t) -> Box p PRIME(Min w (s :- x), Min h (t :- y))

This proved considerably more difficult as we had to reason about
interactions between subtraction, addition, and minimum.

\subsection{Length-indexed vector types}

For implementing our text editor we will use boxes in which the
underlying content consists of character matrices. We represent
matrices as vectors of vectors. In this section we define vectors,
where the type of a vector is indexed by its length and its element
type.

> data Vec :: Nat -> * -> * where
>   V0   ::                 Vec Z x
>   (:>) :: x -> Vec n x -> Vec (S n) x
> 
> vlength :: Vec n x -> SNat n
> vlength V0        = SZ
> vlength (x :> xs) = vlength (x :> xs) = SS (vlength xs)
> 
> instance Show x => Show (Vec n x) where
>   show = show . foldMap (:[])

The |vlength| function illustrates the practical difference between
our version of |SNat|, and the one automatically generated by the
\singletons library. The above definition does not type-check in the
latter case. The problem is that the constraint |NATTY m| must hold
where |m| is the length of xs. If we use the \singletons library, then
we need to rewrite the second line as:

> vlength (x :> xs) = natter n (SS n) where n = vlength xs

bringing the necessary constraint into scope.

Vectors are foldable, traversable, applicative functors.

> instance Functor (Vec n) where
>   fmap = fmapDefault
> 
> instance Foldable (Vec n) where
>   foldMap = foldMapDefault
>
> vcopies :: forall n x.SNat n -> x -> Vec n x
> vcopies SZ x = V0
> vcopies (SS n) x = x :> vcopies n x   
> 
> vapp :: forall n s t.Vec n (s -> t) -> Vec n s -> Vec n t
> vapp V0 V0 = V0
> vapp (f :> fs) (s :> ss) = f s :> vapp fs ss
> 
> instance NATTY n => Applicative (Vec n) where
>   pure = vcopies natty where
>   (<*>) = vapp where

> instance Traversable (Vec n) where
>   traverse f V0 = pure V0
>   traverse f (x :> xs) = (:>) <$> f x <*> traverse f xs

%$

We choose to expose the |vcopies| and |vapp| functions which are both
polymorphic in the length of the vector, as sometimes the extra
generality over |pure| and |(<*>)| is useful.

We can straightforwardly define operations for appending and cutting
vectors.
 
> vappend :: Vec m a -> Vec n a -> Vec (m :+ n) a
> vappend V0        ys = ys
> vappend (x :> xs) ys = x :> vappend xs ys
> 
> vcut :: SNat m -> SNat n ->
>   Vec (m :+ n) a -> (Vec m a, Vec n a)
> vcut SZ n xs = (V0, xs)
> vcut (SS m) n (x :> xs) = (x :> ys, zs)
>   where (ys, zs) = vcut m n xs

\subsection{Matrices}

A matrix is simply a vertical vector of horizontal vectors.

> data Matrix :: * -> (Nat, Nat) -> * where
>   Mat :: Vec h (Vec w a) -> Matrix a PRIME(w, h)
> 
> instance Show x => Show (Matrix x PRIME(w, h)) where
>   show = show . (foldMap ((:[]) . foldMap (:[]))) . unMat
> 
> unMat :: Matrix a PRIME(w,h) -> Vec h (Vec w a)
> unMat (Mat m) = m
> 
> instance Cut (Matrix e) where
>   horCut m n (Mat ess) =
>     (Mat (fst <$> ps), Mat (snd <$> ps)) where
>       ps = vcut m n <$> ess
>   verCut m n (Mat ess) = (Mat tess, Mat bess) where
>     (tess, bess) = vcut m n ess 

%$

\subsection{Character boxes}

> type CharMatrix = Matrix Char
> type CharBox wh = Box CharMatrix wh
> 
> matrixChar :: Char -> (SNat w, SNat h) -> CharMatrix PRIME(w, h)
> matrixChar c (w, h) = Mat (vcopies h (vcopies w c))
> 
> renderCharBox ::
>   Size w h -> CharBox PRIME(w, h) -> CharMatrix PRIME(w, h)
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
>
> stringsOfCharMatrix :: CharMatrix wh -> [String]
> stringsOfCharMatrix (Mat vs) =
>   foldMap ((:[]) . foldMap (:[])) vs

\subsection{Wrapping indexed types}

Sometimes, it is useful to convert unindexed values to type-indexed
vales. For instance, we may receive a natural number at run-time
represented as an |Int|, and wish to convert it to an |SNat|. Of
course, we cannot statically specify the index on the returned |SNat|,
but we can existentially quantify over it.

> data WNat :: * where
>   WNat :: SNat n -> WNat

The |WNat| data type is a Haskell encoding of the type |EXISTS n DOT
SNat n|. We can now wrap an |Int| as a |WNat|.

> wrapNat :: Int -> WNat
> wrapNat  0  =  WNat SZ
> wrapNat  n  =  case wrapNat (n-1) of
>                  WNat wn -> WNat (SS wn)

Similarly, we implement functionality for wrapping points.

> data WPoint :: * where
>   WPoint :: SNat x -> SNat y -> WPoint
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
size |(w, 1)|. Given a list of |h| strings of maximum length |w|, we
can wrap it as a character box of size |(w, h)|.

> data WCharBox :: * where
>   WCharBox :: Size w h -> CharBox PRIME(w, h) -> WCharBox
>
> wrapString :: String -> WCharBox
> wrapString s = case wrapList s of
>   WVec v -> WCharBox (vlength v, one) (boxS v)

> wrapStrings :: [String] -> WCharBox
> wrapStrings []      = WCharBox (SZ, SZ) boxZ
> wrapStrings (s:ss)  =
>   case (wrapString s, wrapStrings ss) of
>     (WCharBox (w1, h1) b1, WCharBox (w2, h2) b2) ->
>       WCharBox
>         (w1 `maxn` w2, h1 /+/ h2)
>         (joinV (w1, h1) (w2, h2) b1 b2)

\subsection{Cursors}

> type Cursor a m = ([a], m, [a])
> type StringCursor = Cursor Char ()
> 
> type TextCursor = Cursor String StringCursor
> 
> deactivate :: Cursor a () -> (Int, [a])
> deactivate c = outward 0 c where
>   outward i ([], (), xs)     = (i, xs)
>   outward i (x : xz, (), xs) = outward (i + 1) (xz, (), x : xs)
> 
> 
> activate :: (Int, [a]) -> Cursor a ()
> activate (i, xs) = inward i ([], (), xs) where
>   inward _ c@(_, (), [])     = c
>   inward 0 c                 = c
>   inward i (xz, (), x : xs)  = inward (i - 1) (x : xz, (), xs)
> 
> whatAndWhere :: TextCursor -> (WCharBox, (Int, Int))
> whatAndWhere (czz, cur, css) = (wrapStrings strs, (x, y))
>   where
>     (x, cs) = deactivate cur
>     (y, strs) = deactivate (czz, (), cs : css)
> 
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

\subsection{An editor}

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
 
> layout :: Size w h -> CharBox PRIME(w, h) -> [String]
> layout s l = stringsOfCharMatrix (renderCharBox s l)
> 
> outer :: URegion -> TextCursor -> IO ()
> outer ps tc = inner ps tc (whatAndWhere tc) LotsChanged
>   where
>   inner ps@(p, _) tc lc@(WCharBox (lw, lh) l, c@(cx, cy)) d = do
>     refresh
>     s' <- scrSize
>     let ps'@((px, py), (sw, sh)) = onScreen c (p, s')
>     let d' = if ps /= ps' then LotsChanged else d
>     case d' of
>       LotsChanged -> do
>         clearScreen
>         resetCursor
>         case (wrapPoint (px, py), wrapPoint (sw, sh)) of
>           (WPoint x y, WPoint w h) -> do
>             let cropped = crop ((x, y), (w, h)) (lw, lh) l
>             mapM_ putStr (layout (w, h) cropped)
>       LineChanged -> do
>         resetCursor
>         down (cy - py)
>         case (wrapPoint (px, cy), wrapPoint (sw, 1)) of
>           (WPoint x y, WPoint w h) -> do
>             let cropped = crop ((x, y), (w, h)) (lw, lh) l
>             mapM_ putStr (layout (w, h) cropped)
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



%% \appendix
%% \section{Appendix Title}

%% This is the text of the appendix, if you need one.

%% \acks

%% Acknowledgments, if needed.

% We recommend abbrvnat bibliography style.

\bibliographystyle{abbrvnat}

\bibliography{hasochism}

% The bibliography should be embedded for final submission.

%% \begin{thebibliography}{}
%% \softraggedright

%% \bibitem[Smith et~al.(2009)Smith, Jones]{smith02}
%% P. Q. Smith, and X. Y. Jones. ...reference text...

%% \end{thebibliography}

\end{document}
