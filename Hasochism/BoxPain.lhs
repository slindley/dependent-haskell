%if False

> {-# LANGUAGE GADTs, PolyKinds, KindSignatures, MultiParamTypeClasses,
>     DataKinds, FlexibleInstances, RankNTypes, FlexibleContexts,
>     TypeOperators, TypeFamilies #-}

> module BoxPain where
>
> import NatVec
> import Evidence
>
> type family Max (m :: Nat) (n :: Nat) :: Nat
> type instance Max Z     n     = n
> type instance Max (S m) Z     = S m
> type instance Max (S m) (S n) = S (Max m n)
> 
> maxn :: Natty m -> Natty n -> Natty (Max m n)
> maxn Zy     n      = n
> maxn (Sy m) Zy     = Sy m
> maxn (Sy m) (Sy n) = Sy (maxn m n)

%endif

%format maxn = "\F{maxn}"

%format cmp = "\F{cmp}"

%format joinH = "\F{joinH}"
%format joinV = "\F{joinV}"

%format maxLT = "\F{maxLT}"
%format maxEQ = "\F{maxEQ}"
%format maxGT = "\F{maxGT}"


In this section we introduce our main example, an algebra for building
size-indexed rectangular tilings, which we call simply \emph{boxes}.

\subsection{Two flavours of conjunction}
\label{subsec:conjunction}

In order to define size indexes, we introduce some kit which turns out
to be more generally useful. The type of sizes is given by the
\emph{separated conjunction} of |Natty| with |Natty|.

> type Size = Natty :**: Natty
>
> data (p :: j -> *) :**: (q :: k -> *) :: (j, k) -> * where
>   (:&&:) :: p j -> q k -> (p :**: q) (Pair j k)

In general, the separating conjunction |:**:| of two indexed type
constructors is an indexed product whose index is also a product, in
which each component of the indexed product is indexed by the
corresponding component of the index.

We also define a \emph{non-separating conjunction}.

> data (p :: k -> *) :*: (q :: k -> *) :: k -> * where
>   (:&:) :: p k -> q k -> (p :*: q) k

The non-separating conjunction |:*:| is an indexed product in which
the index is shared across both components of the product.

We will use both separating and non-separating conjunction extensively
in Section~\ref{subsec:more-existentials}.

\subsection{Box and Join}

We now introduce the type of boxes.

> data Box :: ((Nat, Nat) -> *) -> (Nat, Nat) -> * where
>   Stuff  ::  p wh -> Box p wh
>   Clear  ::  Box p wh
>   Hor    ::  Natty w1 -> Box p (Pair w1 h) ->
>              Natty w2 -> Box p (Pair w2 h) -> Box p (Pair (w1 :+ w2) h)
>   Ver    ::  Natty h1 -> Box p (Pair w h1) ->
>              Natty h2 -> Box p (Pair w h2) -> Box p (Pair w (h1 :+ h2))

A box |b| with content of size-indexed type |p| and size |wh| has type
|Box p wh|. Boxes are constructed from content (|Stuff|), clear boxes
(|Clear|), and horizontal (|Hor|) and vertical (|Ver|) composition.
%
Given suitable instantiations for the content, boxes can be used as
the building blocks for arbitrary graphical user interfaces. In
Section~\ref{sec:editor} we instantiate content to the type of
character matrices, which we use to implement a text editor.

A natural operation to define is the one that joins two boxes
together, horizontally or vertically, adding appropriate padding if
the sizes do not match up. Let us consider the horizontal version
|joinH|. Its type signature is:

> joinH ::  Size (Pair w1 h1) -> Size (Pair w2 h2) ->
>           Box p (Pair w1 h1) -> Box p (Pair w2 h2) ->
>             Box p (Pair (w1 :+ w2) (Max h1 h2))

As well as the two boxes it takes singleton representations of their
sizes, as it must compute on the sizes.

We might try to write a definition for |joinH| as follows:

< joinH (w1 :&&: h1) (w2 :&&: h2) b1 b2 =
<   case cmp h1 h2 of
<     LTNat n  ->
<       Hor w1 (Ver h1 b1 (Sy n) Clear) w2 b2   -- |BAD|
<     EQNat    ->
<       Hor w1 b1 w2 b2                         -- |BAD|
<     GTNat n  ->
<       Hor w1 b1 w2 (Ver h2 b2 (Sy n) Clear)   -- |BAD|

Unfortunately, this code does not type check, because GHC has no way
of knowing that the height of the resulting box is the maximum of the
heights of the component boxes.

\subsection{Pain}

One approach to resolving this issue is to encode lemmas, given by
parameterised equations, as Haskell functions.
%
In general, such lemmas may be encoded as functions of type:

< forall x1 ... xn.Natty x1 -> ... -> Natty xn -> ((l ~ r) => t) -> t

where |l| and |r| are the left- and right-hand-side of the equation,
and |x1|, \dots, |xn| are natural number variables that may appear
free in the equation. The first |n| arguments are singleton natural
numbers. The last argument represents a context that expects the
equation to hold.

For |joinH|, we need one lemma for each case of the comparison:

> joinH (w1 :&&: h1) (w2 :&&: h2) b1 b2 =
>   case cmp h1 h2 of
>     LTNat z  -> maxLT h1 z $
>       Hor w1 (Ver h1 b1 (Sy z) Clear) w2 b2
>     EQNat    -> maxEQ h1 $
>       Hor w1 b1 w2 b2
>     GTNat z  -> maxGT h2 z $
>       Hor w1 b1 w2 (Ver h2 b2 (Sy z) Clear)

%$

Each lemma is defined by a straightforward induction:

> maxLT ::  forall m z t.Natty m -> Natty z ->
>             ((Max m (m :+ S z) ~ (m :+ S z)) => t) -> t
> maxLT Zy      z  t  =  t
> maxLT (Sy m)  z  t  =  maxLT m z t

> maxEQ :: forall m t.Natty m -> ((Max m m ~ m) => t) -> t
> maxEQ Zy      t  =  t
> maxEQ (Sy m)  t  =  maxEQ m t
 
> maxGT ::  forall n z t.Natty n -> Natty z ->
>             ((Max (n :+ S z) n ~ (n :+ S z)) => t) -> t
> maxGT Zy      z  t  =  t
> maxGT (Sy n)  z  t  =  maxGT n z t

Using this pattern, it is now possible to use GHC as a theorem
prover. As GHC does not provide anything in the way of direct support
for theorem proving (along the lines of tactics in Coq, say), we would
like to avoid the pain of explicit theorem proving as much as
possible. Thus, we choose to change tack and switch to an alternative
approach.
