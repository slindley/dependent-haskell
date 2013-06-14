%if False

> {-# LANGUAGE GADTs, PolyKinds, KindSignatures, MultiParamTypeClasses,
>     DataKinds, FlexibleInstances, RankNTypes, FlexibleContexts #-}

> module NATTYInNatty where
>
> import Control.Applicative
> import Data.Traversable
> import Data.Foldable
>
> import NatVec
> import Pies

%% natural numbers again

> class NATTYC (n :: Nat) where
>   nattyC :: NattyC n
> 
> instance NATTYC Z where
>   nattyC = ZyC
> 
> instance NATTYC n => NATTYC (S n) where
>   nattyC = SyC nattyC

%% vectors again

> data VecC :: Nat -> * -> * where
>   V0C   ::                  VecC Z x
>   (:>>) :: x -> VecC n x -> VecC (S n) x
> 
> vcopiesC :: forall n x.NattyC n -> x -> VecC n x
> vcopiesC ZyC x = V0C
> vcopiesC (SyC n) x = x :>> vcopiesC n x   
> 
> vappC :: forall n s t.VecC n (s -> t) -> VecC n s -> VecC n t
> vappC V0C V0C = V0C
> vappC (f :>> fs) (s :>> ss) = f s :>> vappC fs ss
> 
> instance NATTYC n => Applicative (VecC n) where
>   pure = vcopiesC nattyC where
>   (<*>) = vappC where
> 
> instance Traversable (VecC n) where
>   traverse f V0C = pure V0C
>   traverse f (x :>> xs) = (:>>) <$> f x <*> traverse f xs

%$

> instance Functor (VecC n) where
>   fmap = fmapDefault
> 
> instance Foldable (VecC n) where
>   foldMap = foldMapDefault

%endif

%% function definitions

%format unMat = "\F{unMat}"

%format vlength = "\F{vlength}"
%format idMatrix = "\F{idMatrix}"

%% duplicated thingies

%format NattyD = Natty
%format ZyD = Zy
%format SyD = Sy

%format NattyC = Natty
%format ZyC = Zy
%format SyC = Sy

%format NATTYC = NATTY
%format natterC = natter

%format VecC = Vec
%format V0C = V0
%format :>> = :>

%format vlengthC = vlength

%format MatrixC = Matrix
%format MatC = Mat
%format unMatC = unMat
%format idMatrixC = idMatrix

Recall that we defined the singleton representation of natural numbers
as follows.

> data NattyD :: Nat -> * where
>   ZyD :: NattyD Z
>   SyD :: NattyD n -> NattyD (S n)

Another possible design choice is to insert a |NATTY| constraint in
the successor case, effectively storing two copies of the predecessor.
This is the choice taken by Eisenberg and Weirich in the Singletons
library~\cite{EisenbergW12}.

> data NattyC :: Nat -> * where
>   ZyC :: NattyC Z
>   SyC :: NATTYC n => NattyC n -> NattyC (S n)

Each choice has advantages and disadvantages. The unconstrained version
clearly makes for easier construction of singletons, whilst the constrained
version makes for more powerful elimination.

Without the |NATTY| constraint on |Sy|, we can write a function to
compute the length of a vector as follows:

> vlength :: Vec n x -> Natty n
> vlength V0         = Zy
> vlength (x :> xs)  = Sy (vlength xs)

However, with the |NATTY| constraint on |Sy|, the construction
becomes more complex, and we must write:

> vlengthC :: VecC n x -> NattyC n
> vlengthC V0C         = ZyC
> vlengthC (x :>> xs)  = natterC n (SyC n) where n = vlengthC xs

in order to bring the appropriate |NATTY| constraint into scope for
the inductive case.

%if False

> data MatrixC :: * -> (Nat, Nat) -> * where
>   MatC :: VecC h (VecC w a) -> MatrixC a (Pair w h)
>
> unMatC :: MatrixC a (Pair w h) -> VecC h (VecC w a)
> unMatC (MatC vs) = vs

%endif

Let us write a function to construct an identity matrix of size
|n|. Here, we are eliminating a singleton. Without the |NATTY| constraint
on |Sy|, we must use |natter| to
enable the use of the relevant |Applicative| structure.

> idMatrix :: Natty n -> Matrix Int (Pair n n)
> idMatrix (Sy n)  = natter n $
>   Mat ((1 :> pure 0) :> ((0 :>) <$> unMat (idMatrix n)))
> idMatrix Zy      = Mat V0

%$

However, with the |NATTY| constraint on |Sy|, we can omit |natter|,
because the required constraint is brought into scope by pattern
matching.

> idMatrixC :: NattyC n -> MatrixC Int (Pair n n)
> idMatrixC (SyC n)  = 
>   MatC ((1 :>> pure 0) :>> ((0 :>>) <$> unMatC (idMatrixC n)))
> idMatrixC ZyC      = MatC V0C

%$

For contructions like |vlength| it is most convenient to omit the
|NATTY| constraint from the successor constructor.  For eliminations
like |idMatrix|, it is most convenient to attach the |NATTY|
constraint to the successor constructor. It is hard to predict which
polarity is more likely to dominate, but the issue with elimination
happens only when we have the explicit witness but need the implicit
one.

There is also a time/space trade-off, as including the constraint
effectively requires storing the same information twice at each node,
but allows for an implementation of |natter| by one step of case analysis,
rather than a full recursion.

%format natterC = natter

> natterC :: NattyC n -> (NATTYC n => t) -> t
> natterC ZyC      t  = t
> natterC (SyC n)  t  = t

SHE has vacillated between the two: the first implementation did not
add the constraint; a tricky example provoked us to add it, but it broke
too much code, so we reverted the change. Our experience suggests that
omitting the constraint is more convenient more of the time. We should,
however, prefer to omit the entire construction.
