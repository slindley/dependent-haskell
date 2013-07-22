%if False

> {-# LANGUAGE GADTs, PolyKinds, KindSignatures, MultiParamTypeClasses,
>     DataKinds, FlexibleInstances, RankNTypes, FlexibleContexts,
>     TypeOperators, TypeFamilies #-}

> module BoxPleasure where
>
> import Data.Monoid
> import NatVec
>

> data (p :: iota -> *) :**: (q :: kappa -> *) :: (iota, kappa) -> * where
>   (:&&:) :: p iota -> q kappa -> (p :**: q) (Pair iota kappa)
>
> data (p :: kappa -> *) :*: (q :: kappa -> *) :: kappa -> * where
>   (:&:) :: p kappa -> q kappa -> (p :*: q) kappa

> type Size = Natty :**: Natty
> 
> type family Max (m :: Nat) (n :: Nat) :: Nat
> type instance Max Z     n     = n
> type instance Max (S m) Z     = S m
> type instance Max (S m) (S n) = S (Max m n)

> cmp :: Natty m -> Natty n -> Cmp m n
> cmp Zy      Zy      = EQNat
> cmp Zy      (Sy n)  = LTNat n
> cmp (Sy m)  Zy      = GTNat m
> cmp (Sy m)  (Sy n)  = case cmp m n of
>   LTNat z  ->  LTNat z
>   EQNat    ->  EQNat
>   GTNat z  ->  GTNat z

> data Box :: ((Nat, Nat) -> *) -> (Nat, Nat) -> * where
>   Stuff  ::  p wh -> Box p wh
>   Clear  ::  Box p wh
>   Hor    ::  Natty w1 -> Box p (Pair w1 h) ->
>              Natty w2 -> Box p (Pair w2 h) -> Box p (Pair (w1 :+ w2) h)
>   Ver    ::  Natty h1 -> Box p (Pair w h1) ->
>              Natty h2 -> Box p (Pair w h2) -> Box p (Pair w (h1 :+ h2))

%endif

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

%format CmpEx = Cmp
%format LTNatEx = LTNat
%format EQNatEx = EQNat
%format GTNatEx = GTNat

%format CmpMax = Cmp
%format LTNatMax = LTNat
%format EQNatMax = EQNat
%format GTNatMax = GTNat


%% > data  Cmp :: Nat -> Nat -> * where
%% >   LTNat  :: (Max m (m :+ S z) ~ (m :+ S z))  => Natty z  ->  Cmp m (m :+ S z)
%% >   EQNat  :: (Max m m ~ m)                    =>              Cmp m m
%% >   GTNat  :: (Max (n :+ S z) n ~ (n :+ S z))  => Natty z  ->  Cmp (n :+ S z) n

\subsection{Pleasure}

In order to avoid explicit calls to lemmas we would like to obtain the
type equations we need for free as part of the proof object. As a
first step, we observe that this is essentially what we are already
doing in the proof object to encode the necessary equations concerning
addition. One can always rephrase a GADT as an existential algebraic
data type with suitable type equalities. For our basic |Cmp| data
type, this yields:

> data CmpEx :: Nat -> Nat -> * where
>   LTNatEx :: ((m :+ S z) ~ n)  => Natty z ->  CmpEx m n
>   EQNatEx :: (m ~ n)           =>             CmpEx m n
>   GTNatEx :: (m ~ (n :+ S z))  => Natty z ->  CmpEx m n

Now the fun starts. As well as the equations that define the proof
object, we can incorporate other equations that encapsulate further
knowledge implied by the result of the comparison. For now we add
equations for computing the maximum of |m| and |n| in each case.

> data CmpMax :: Nat -> Nat -> * where
>   LTNatMax :: ((m :+ S z) ~ n,  Max m n ~ n)  =>
>     Natty z ->  CmpMax m n
>   EQNatMax :: (m ~ n,           Max m n ~ m)  =>
>                 CmpMax m n
>   GTNatMax :: (m ~ (n :+ S z),  Max m n ~ m)  =>
>     Natty z ->  CmpMax m n

Having added these straightforward equalities, our definition of
|juxH| now type checks without the need to explicitly invoke any lemmas. 

> juxH ::  Size (Pair w1 h1) -> Size (Pair w2 h2) ->
>           Box p (Pair w1 h1) -> Box p (Pair w2 h2) ->
>             Box p (Pair (w1 :+ w2) (Max h1 h2))
> juxH (w1 :&&: h1) (w2 :&&: h2) b1 b2 =
>   case cmp h1 h2 of
>     LTNat z  ->
>       Hor w1 (Ver h1 b1 (Sy z) Clear) w2 b2
>     EQNat    ->
>       Hor w1 b1 w2 b2
>     GTNat z  ->
>       Hor w1 b1 w2 (Ver h2 b2 (Sy z) Clear)

The |juxV| function is defined similarly.

%if False

> juxV ::  Size (Pair w1 h1) -> Size (Pair w2 h2) ->
>           Box p (Pair w1 h1) -> Box p (Pair w2 h2) ->
>             Box p (Pair (Max w1 w2) (h1 :+ h2))
> juxV (w1 :&&: h1) (w2 :&&: h2) b1 b2 =
>   case cmp w1 w2 of
>     LTNat n  ->
>       Ver h1 (Hor w1 b1 (Sy n) Clear) h2 b2
>     EQNat    ->
>       Ver h1 b1 h2 b2
>     GTNat n  ->
>       Ver h1 b1 h2 (Hor w2 b2 (Sy n) Clear)

%endif

As we shall see in Section~\ref{subsec:cutting}, it can be useful to
attach further equational constraints to the |Cmp| constructors. A
limitation of our current formulation is that we have to go back and
modify the |Cmp| data type each time we wish to add a new
equation. Ideally we would have some way of keeping the constraints
open. This seems fiddly to achieve with Haskell as it stands, because
one appears to require higher-order constraints. We leave a proper
investigation to future work.

\subsection{Cutting}
\label{subsec:cutting}


For cutting up boxes, and two-dimensional entities in general, we
introduce a type class |Cut|.

> class Cut (p :: (Nat, Nat) -> *) where
>   horCut ::  Natty m -> Natty n ->
>                p (Pair (m :+ n) h) -> (p (Pair m h), p (Pair n h))
>   verCut ::  Natty m -> Natty n ->
>                p (Pair w (m :+ n)) -> (p (Pair w m), p (Pair w n))

We can cut horizontally or vertically by supplying the width or height
of the two smaller boxes we wish to cut a box into. Thus |horCut|
takes natural numbers |m| and |n|, an indexed thing of width $m + n$
and height $h$, and cuts it into two indexed things of height |h|, one
of width |m|, and the other of width |n|. The |verCut| function is
similar.

In order to handle the case in which we horizontally cut the
horizontal composition of two boxes, we need to perform a special kind
of comparison. In general, we wish to compare natural numbers $a$ and
$c$ given the equation $a + b = c + d$, and capture the constraints on
$a$, $b$, $c$, and $d$ implied by the result of the comparison. For
instance, if $a \leq c$ then there must exist some number $z$, such
that $b = (z + 1) + d$ and $c = a + (z + 1)$.

We encode proof objects for cut comparisons using the following data
type.

> data CmpCuts :: Nat -> Nat -> Nat -> Nat -> * where
>   LTCuts :: (b ~ (S z :+ d), c ~ (a :+ S z)) =>
>     Natty z ->  CmpCuts a b c d
>   EQCuts :: (a ~ c, b ~ d) =>
>                 CmpCuts a b c d
>   GTCuts :: (a ~ (c :+ S z), d ~ (S z :+ b)) =>
>     Natty z ->  CmpCuts a b c d 

We can straightforwardly define a cut comparison function.

> cmpCuts :: ((a :+ b) ~ (c :+ d)) =>
>   Natty a -> Natty b ->
>   Natty c -> Natty d ->
>     CmpCuts a b c d
> cmpCuts Zy b Zy     d  = EQCuts
> cmpCuts Zy b (Sy c) d  = LTCuts c
> cmpCuts (Sy a) b Zy d  = GTCuts a
> cmpCuts (Sy a) b (Sy c) d = case cmpCuts a b c d of
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
>       LTCuts z  ->  let (b11, b12) = horCut m (Sy z) b1
>                     in (b11, Hor (Sy z) b12 w2 b2)
>       EQCuts    ->  (b1, b2)
>       GTCuts z  ->  let (b21, b22) = horCut (Sy z) n b2
>                     in (Hor w1 b1 (Sy z) b21, b22)
>   horCut m n (Ver h1 b1 h2 b2) =
>     (Ver h1 b11 h2 b21, Ver h1 b12 h2 b22)
>     where (b11, b12) = horCut m n b1
>           (b21, b22) = horCut m n b2
 
<   verCut m n b = ...

%if False

>   verCut m n (Stuff p) = (Stuff p1, Stuff p2)
>     where (p1, p2) = verCut m n p
>   verCut m n Clear = (Clear, Clear)
>   verCut m n (Ver h1 b1 h2 b2) =
>     case cmpCuts m n h1 h2 of
>       LTCuts z  ->  let (b11, b12) = verCut m (Sy z) b1
>                     in (b11, Ver (Sy z) b12 h2 b2)
>       EQCuts    ->  (b1, b2)
>       GTCuts z  ->  let (b21, b22) = verCut (Sy z) n b2
>                     in (Ver h1 b1 (Sy z) b21, b22)
>   verCut m n (Hor w1 b1 w2 b2) =
>     (Hor w1 b11 w2 b21, Hor w1 b12 w2 b22)
>     where (b11, b12) = verCut m n b1
>           (b21, b22) = verCut m n b2

%endif

The interesting case occurs when horizontally cutting the horizontal
composition of two sub-boxes. We must identify which sub-box the cut
occurs in, and recurse appropriately. Note that we rely on being able
to cut content. The definition of vertical box cutting is similar.

\subsection{Boxes as Monoids}

As well as monadic structure, boxes also have monoidal structure.

> instance Cut p => Monoid (Box p wh) where
>   mempty = Clear
>   mappend b Clear               = b
>   mappend Clear b'              = b'
>   mappend b@(Stuff _) _         = b
>   mappend (Hor w1 b1 w2 b2) b'  =
>     Hor w1 (mappend b1 b1') w2 (mappend b2 b2')
>       where (b1', b2') = horCut w1 w2 b'
>   mappend (Ver h1 b1 h2 b2) b'  =
>     Ver h1 (mappend b1 b1') h2 (mappend b2 b2')
>       where (b1', b2') = verCut h1 h2 b'

The multiplication operation |b `mappend` b'| overlays |b| on top of
|b'|. It makes essential use of cutting to handle the |Hor| and |Ver|
cases.

\subsection{Cropping = Clipping + Fitting}

We can \emph{crop} a box to a region. First we need to specify an
suitably indexed type of regions..
%
A point identifies a position inside a box, where |(Zy, Zy)|
represents the top-left corner, counting top-to-bottom, left-to-right.

> type Point = Natty :**: Natty

A region identifies a rectangular area inside a box by a pair of the
point representing the top-left corner of the region, and the size of
the region.

> type Region = Point :**: Size

We decompose cropping into two parts, \emph{clipping} and
\emph{fitting}.

Clipping discards everything to the left and above the specified
point. The type signature of |clip| is:

> clip :: Cut p => Size (Pair w h) -> Point (Pair x y) ->
>   Box p (Pair w h) -> Box p (Pair (w :- x) (h :- y))

where |:-| is type level subtraction:

> type family (m :: Nat) :- (n :: Nat) :: Nat
> type instance Z   :- n   = Z
> type instance S m :- Z   = S m
> type instance S m :- S n = (m :- n)

In order to account for the subtraction in the result, we need to
augment the |Cmp| data type to include the necessary equations.

> data Cmp :: Nat -> Nat -> * where
>   LTNat :: ((m :+ S z) ~ n,  Max m n ~ n,  (m :- n) ~ Z)    =>
>       Natty z ->  Cmp m n
>   EQNat :: (m ~ n,           Max m n ~ m,  (m :- n) ~ Z)    =>
>                   Cmp m n
>   GTNat :: (m ~ (n :+ S z),  Max m n ~ m,  (m :- n) ~ S z)  =>
>       Natty z ->  Cmp m n

To clip in both dimensions, we first clip horizontally, and then clip
vertically.
%

In order to define clipping we first lift subtraction on types |:-| to
subtract on singleton naturals |/-/|.

> (/-/) :: Natty m -> Natty n -> Natty (m :- n)
> Zy   /-/ n    = Zy
> Sy m /-/ Zy   = Sy m
> Sy m /-/ Sy n = m /-/ n

In general one needs to define each operation on naturals three times:
once for |Nat| values, once for |Nat| types, and once for |Natty|
values. The pain can be somewhat alleviated using the \singletons
library~\cite{EisenbergW12}, which provides a Template Haskell
extension to automatically generate all three versions from a single
definition.

Let us now define clipping.

> clip (w :&&: h) (x :&&: y) b =
>   clipV (w /-/ x :&&: h) y (clipH (w :&&: h) x b)
> 
> clipH :: Cut p => Size (Pair w h) -> Natty x ->
>   Box p (Pair w h) -> Box p (Pair (w :- x) h)
> clipH (w :&&: h) x b = case cmp w x of
>   GTNat d  -> snd (horCut x (Sy d) b)
>   _        -> Clear
> 
> clipV :: Cut p => Size (Pair w h) -> Natty y ->
>   Box p (Pair w h) -> Box p (Pair w (h :- y))
> clipV (w :&&: h) y b = case cmp h y of
>   GTNat d  -> snd (verCut y (Sy d) b)
>   _        -> Clear

Fitting pads or cuts a box to the given size. To fit in both
dimensions, we first fit horizontally, and then fit veritcally.

> fit :: Cut p => Size (Pair w1 h1) -> Size (Pair w2 h2) ->
>   Box p (Pair w1 h1) -> Box p (Pair w2 h2)
> fit (w1 :&&: h1) (w2 :&&: h2) b = fitV h1 h2 (fitH w1 w2 b)
> 
> fitH :: Cut p => Natty w1 -> Natty w2 ->
>   Box p (Pair w1 h) -> Box p (Pair w2 h)
> fitH w1 w2 b = case cmp w1 w2 of
>   LTNat d  -> Hor w1 b (Sy d) Clear
>   EQNat    -> b
>   GTNat d  -> fst (horCut w2 (Sy d) b)
> 
> fitV :: Cut p => Natty h1 -> Natty h2 ->
>   Box p (Pair w h1) -> Box p (Pair w h2)
> fitV h1 h2 b = case cmp h1 h2 of
>   LTNat d  -> Ver h1 b (Sy d) Clear
>   EQNat    -> b
>   GTNat d  -> fst (verCut h2 (Sy d) b)

Note that |fitH| and |fitV| do essentially the same thing as the
|procrustes| function, but on boxes rather than vectors, and always
using |Clear| boxes for padding.

To crop a box to a region, we simply clip then fit.

> crop :: Cut p => Region (Pair (Pair x y) (Pair w h)) -> Size (Pair s t) ->
>   Box p (Pair s t) -> Box p (Pair w h)
> crop ((x :&&: y) :&&: (w :&&: h)) (s :&&: t) b =
>   fit  ((s /-/ x) :&&: (t /-/ y)) (w :&&: h)
>        (clip (s :&&: t) (x :&&: y) b)

A convenient feature of our cropping code is that type-level
subtraction is confined to the |clip| function. This works because in
the type of |fit| the output box is independent of the size of the
input box.

In an earlier version of the code we experimented with a more refined
cropping function of type:

< Cut p => Region (Pair (Pair x y) (Pair w h)) -> Size (Pair s t) ->
<   Box p (Pair s t) -> Box p (Pair (Min w (s :- x)) (Min h (t :- y)))

where |Min| is minimum on promoted |Nat|s.

This proved considerably more difficult to use as we had to reason
about interactions between subtraction, addition, and
minimum. Moreover, the less-refined version is often what we want in
practice.



%%  LocalWords:  PolyKinds KindSignatures MultiParamTypeClasses cmp
%%  LocalWords:  DataKinds FlexibleInstances RankNTypes TypeOperators
%%  LocalWords:  FlexibleContexts TypeFamilies BoxPleasure Monoid Cmp
%%  LocalWords:  NatVec Zy EQNat Sy LTNat GTNat wh Hor Ver GADT CmpEx
%%  LocalWords:  datatype equalities LTNatEx EQNatEx GTNatEx CmpMax
%%  LocalWords:  LTNatMax EQNatMax GTNatMax juxH juxV equational snd
%%  LocalWords:  Haskell horCut verCut CmpCuts LTCuts EQCuts GTCuts
%%  LocalWords:  cmpCuts recurse Monoids monadic monoidal mempty fitV
%%  LocalWords:  mappend verically clipV clipH veritcally fitH fst
%%  LocalWords:  procrustes
