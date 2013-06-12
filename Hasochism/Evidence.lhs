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
>
> vcopies :: forall n x.Natty n -> x -> Vec n x
> vcopies Zy x = V0
> vcopies (Sy n) x = x :> vcopies n x   

%endif

Let us consider the operation of comparing two singleton natural
numbers. We refine the standard Haskell |Ordering| type to be indexed
by the natural numbers under comparison.

As a naive first attempt, we might try the following:

> data  CmpN :: Nat -> Nat -> * where
>   LTNatN  :: CmpN m (m :+ S z)
>   EQNatN  :: CmpN m m
>   GTNatN  :: CmpN (n :+ S z) n

The equals case is straightforward: $m = m$. If |m < n|, then there
exists some |z| such that $n = m + (z + 1)$. Similarly if |m > n| then
there exists some |z| such that $m = n + (z + 1)$.

Often it is useful to be able to compute on the difference between the
two numbers as a value. In the |EQNat| case, this is simply |0|. In
the other two cases it is |z + 1|, thus in each case we store a
singleton representation of |z| as a witness.

> data  Cmp :: Nat -> Nat -> * where
>   LTNat  :: Natty z  ->  Cmp m (m :+ S z)
>   EQNat  ::              Cmp m m
>   GTNat  :: Natty z  ->  Cmp (n :+ S z) n

Note that in more conventional dependently typed programming languages
such as Agda there it is not possible to write an equivalent of our
naive definition of |Cmp| --- the value of |z| must be provided as an
argument to the |LTNat| and |GTNat| constructors.

We can now write a comparison function that constructs a suitable
proof object:

> cmp :: Natty x -> Natty y -> Cmp x y
> cmp Zy      Zy      = EQNat
> cmp Zy      (Sy y)  = LTNat y
> cmp (Sy x)  Zy      = GTNat x
> cmp (Sy x)  (Sy y)  = case cmp x y of
>   LTNat z  ->  LTNat z
>   EQNat    ->  EQNat
>   GTNat z  ->  GTNat z

Procrustes is a character from Greek mythology who fits his victims
into an iron bed either by stretching their limbs or by chopping them
off. The |procrustes| function fits a vector of length |m| into a
vector of length |n|, by padding or trimming as necessary.

> procrustes :: a -> Natty m -> Natty n -> Vec m a -> Vec n a
> procrustes p m n xs = case cmp m n of
>   LTNat z  -> vappend xs (vcopies (Sy z) p)
>   EQNat    -> xs
>   GTNat z  -> vtake n (proxy (Sy z)) xs 

In both the less-than and greater-than cases we compute explicitly
with the evidence |z| provided by the |Cmp| data type.