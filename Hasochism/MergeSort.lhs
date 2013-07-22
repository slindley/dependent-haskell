%if False

> {-# LANGUAGE GADTs, PolyKinds, KindSignatures, MultiParamTypeClasses,
>     DataKinds, FlexibleInstances, RankNTypes, FlexibleContexts #-}

> module MergeSort where
> import NatVec

%endif

%format owoto = "\F{owoto}"
%format merge = "\F{merge}"
%format deal = "\F{deal}"
%format sort = "\F{sort}"

%format wrapNat = "\F{wrapNat}"

%format ni = "\F{ni}"


%The following is a stunt, but quite a safe stunt so do try it at
%home. It uses some of the entertaining new toys to bake order
%invariants into merge sort.

We turn now to a slightly larger example---a development of merge-sort
which guarantees by type alone to produce outputs in order. The significant
thing about this construction is what is missing from it: explicit proofs.
By coding the necessary logic using type classes, we harness instance
inference as an implicit proof search mechanism and find it quite adequate
to the task.

Let us start by defining $\leq$ as a `type' class, seen as a relation.

> class LeN (m :: Nat) (n :: Nat) where
> instance             LeN Z n where
> instance LeN m n =>  LeN (S m) (S n) where

If we wanted to \emph{close} this type class, we could use module
abstraction method of Kiselyov and
Shan~\cite{Kiselyov07position:lightweight} which uses a non-exported
superclass. We leave this elaboration to the interested reader.
This |LeN| class has no methods, but it might make sense to deliver
at least the explicit evidence of ordering in the corresponding GADT,
just as the |NATTY| class method delivers |Natty| evidence.

In order to sort numbers, we need to know that any two numbers can be
ordered \emph{one way or the other} (OWOTO). Let us say what it means
for two numbers to be so orderable.

> data OWOTO :: Nat -> Nat -> * where
>   LE  :: LeN x y  => OWOTO x y
>   GE  :: LeN y x  => OWOTO x y

Testing which way around the numbers are is quite a lot like the usual
Boolean version, except with evidence. The step case requires
unpacking and repacking because the constructors are used at different
types. However, instance inference is sufficient to deduce the logical
goals from the information revealed by testing.

> owoto :: forall m n. Natty m -> Natty n -> OWOTO m n
> owoto Zy      n       = LE
> owoto (Sy m)  Zy      = GE
> owoto (Sy m)  (Sy n)  = case owoto m n of
>   LE  ->  LE
>   GE  ->  GE

Now we know how to put numbers in order, let us see how to make
ordered lists. The plan is to describe what it is to be in order
between \emph{loose bounds}~\cite{McBride00:case-talk}. Of course, we
do not want to exclude any elements from being sortable, so the type
of bounds extends the element type with bottom and top elements.

> data Bound x = Bot | Val x | Top deriving (Show, Eq, Ord)

We extend the notion of $\leq$ accordingly, so that instance inference
can manage bound checking.

> class LeB (a :: Bound Nat)(b :: Bound Nat) where
> instance              LeB Bot      b         where
> instance LeN x y =>   LeB (Val x)  (Val y)   where
> instance              LeB (Val x)  Top       where
> instance              LeB Top      Top       where

And here are ordered lists of numbers: an |OList l u| is a sequence
|x1 :< x2 :< ... :< xn :< ONil| such that |l <= x1 <= x2 <= ... <= xn
<= u|. The |x :<| checks that |x| is above the lower bound, then
imposes |x| as the lower bound on the tail.

> data OList :: Bound Nat -> Bound Nat -> * where
>   ONil  ::  LeB l u => OList l u
>   (:<)  ::  forall l x u. LeB l (Val x) =>
>             Natty x -> OList (Val x) u -> OList l u

We can write merge for ordered lists just the same way we would if
they were ordinary. The key invariant is that if both lists share the
same bounds, so does their merge.

> merge :: OList l u -> OList l u -> OList l u
> merge  ONil       lu         = lu
> merge  lu         ONil       = lu
> merge  (x :< xu)  (y :< yu)  = case owoto x y of
>   LE  ->  x  :< merge xu (y :< yu)
>   GE  ->  y  :< merge (x :< xu) yu

The branches of the case analysis extend what is already known from
the inputs with just enough ordering information to satisfy the
requirements for the results. Instance inference acts as a basic
theorem prover: fortunately (or rather, with a bit of practice) the
proof obligations are easy enough.

Now that we can combine ordered lists of singleton numbers, we shall need to
construct singletons for the numbers we intend to sort. We do so via a
general data type for existential quantification.

> data Ex (p :: kappa -> *) where
>   Ex :: p i -> Ex p

A `wrapped |Nat|' is then a |Natty| singleton for any type-level number.

> type WNat = Ex Natty

We can translate a |Nat| to its wrapped version by writing what is,
morally, another obfuscated identity function between our two types
of term level natural numbers.

> wrapNat :: Nat -> WNat
> wrapNat  Z      =  Ex Zy
> wrapNat  (S m)  =  case wrapNat m of Ex n -> Ex (Sy n)

You can see that |wrapNat| delivers the |WNat| corresponding
to the |Nat| it receives, but that property is sadly not enforced by
type. However, once we have |WNat|s, we can build merge-sort in the usual
divide-and-conquer way.

> deal :: [x] -> ([x], [x])
> deal []        = ([], [])
> deal (x : xs)  = (x : zs, ys) where (ys, zs) = deal xs

> sort :: [Nat] -> OList Bot Top
> sort []   = ONil
> sort [n]  = case wrapNat n of Ex n -> n :< ONil
> sort xs   = merge (sort ys) (sort zs) where (ys, zs) = deal xs

The need to work with |WNat| is a little clunky, compared to the
version one might write in Agda where one |Nat| type serves for |Nat|
and its promotion, |Natty|, |NATTY| and |WNat|, but Agda does not have
the proof search capacity of Haskell's constraint solver, and so
requires the theorem proving to be more explicit. There is certainly
room for improvement in both settings.



%if False
\todo{Hide the following code?}

[Here's some spare kit I built to see what was happening.

> instance Show (Natty n) where
>   show Zy = "Zy"
>   show (Sy n) = "(Sy " ++ show n ++ ")"

> instance Show (OList l u) where
>   show ONil = "ONil"
>   show (x :< xs) = show x ++ " :< " ++ show xs

> ni :: Int -> Nat
> ni 0 = Z
> ni x = S (ni (x - 1))

And nothing was hidden.]
%endif

%%  LocalWords:  GADTs PolyKinds KindSignatures MultiParamTypeClasses
%%  LocalWords:  DataKinds FlexibleInstances RankNTypes MergeSort LeN
%%  LocalWords:  FlexibleContexts NatVec Kiselyov Shan superclass Zy
%%  LocalWords:  GADT orderable OWOTO owoto forall Sy sortable Eq Ord
%%  LocalWords:  LeB OList xn ONil lu xu yu prover WNat wrapNat xs zs
%%  LocalWords:  ys Agda Haskell's ni
