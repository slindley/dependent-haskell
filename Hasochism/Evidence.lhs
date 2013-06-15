%% duplicated thingies

%format CmpN = Cmp
%format LTNatN = LTNat
%format EQNatN = EQNat
%format GTNatN = GTNat

%format vcopies = "\F{vcopies}"
%format procrustes = "\F{procrustes}"
%format cmp = "\F{cmp}"

%if False

> {-# LANGUAGE GADTs,
>     PolyKinds, DataKinds, RankNTypes, FlexibleContexts,
>     TypeOperators, TypeFamilies #-}

> module Evidence where
>
> import NatVec
> import Pies

%endif

Let us consider the operation of comparing two singleton natural
numbers. We refine the standard Haskell |Ordering| type to be indexed
by the natural numbers under comparison.

As a na{\"\i}ve first attempt, we might copy the following definition from
McBride and McKinna~\cite{McBrideM04}:

> data  CmpN :: Nat -> Nat -> * where
>   LTNatN  :: CmpN m (m :+ S z)
>   EQNatN  :: CmpN m m
>   GTNatN  :: CmpN (n :+ S z) n

If |m < n|, then there exists some |z| such that $n = m + (z +
1)$. Similarly if |m > n| then there exists some |z| such that $m = n
+ (z + 1)$.

Following a comparison, it can be useful to be able to inspect the
difference between two numbers. In the |EQNat| case, this is simply
|0|. In the other two cases it is |z + 1|, thus in each case we store
a singleton representation of |z| as a witness.

> data  Cmp :: Nat -> Nat -> * where
>   LTNat  :: Natty z  ->  Cmp m (m :+ S z)
>   EQNat  ::              Cmp m m
>   GTNat  :: Natty z  ->  Cmp (n :+ S z) n

Note that in more conventional dependently typed programming
languages, such as Agda, it is not possible to write an equivalent of
our naive definition of |Cmp|---the value of |z| must be provided as
an argument to the |LTNat| and |GTNat| constructors.

We can now write a comparison function that constructs a suitable
proof object:

> cmp :: Natty m -> Natty n -> Cmp m n
> cmp Zy      Zy      = EQNat
> cmp Zy      (Sy n)  = LTNat n
> cmp (Sy m)  Zy      = GTNat m
> cmp (Sy m)  (Sy n)  = case cmp m n of
>   LTNat z  ->  LTNat z
>   EQNat    ->  EQNat
>   GTNat z  ->  GTNat z

The |procrustes| function fits a vector of length |m| into a vector of
length |n|, by padding or trimming as necessary.  (Procrustes was a
mythical Greek brigand who would make his unfortunate guests fit into
an iron bed either by stretching their limbs or by chopping them
off.)

> procrustes :: a -> Natty m -> Natty n -> Vec m a -> Vec n a
> procrustes p m n xs = case cmp m n of
>   LTNat z  -> vappend xs (vcopies (Sy z) p)
>   EQNat    -> xs
>   GTNat z  -> vtake n (proxy (Sy z)) xs 

In both the less-than and greater-than cases, we need the evidence |z|
provided by the |Cmp| data type; in the former, we even compute with it.

Dependently typed programming often combines testing with the acquisition
of new data that is justified by the test---the difference, in this case---
and the refinement of the data being tested---the discovery that one number
is the other plus the difference. We make sure that every computation which
analyses data has a type which characterizes what we expect to learn.



%%  LocalWords:  GADTs PolyKinds DataKinds RankNTypes TypeOperators
%%  LocalWords:  FlexibleContexts TypeFamilies NatVec Haskell na ve
%%  LocalWords:  McKinna LTNatN EQNatN GTNatN EQNat Cmp LTNat GTNat
%%  LocalWords:  Agda cmp Zy Sy procrustes Vec xs vappend vcopies
%%  LocalWords:  vtake characterizes
