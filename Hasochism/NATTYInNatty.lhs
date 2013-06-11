%if False

> {-# LANGUAGE GADTs, PolyKinds, KindSignatures, MultiParamTypeClasses,
>     DataKinds, FlexibleInstances, RankNTypes, FlexibleContexts #-}

> module NATTYInNatty where
> import Control.Applicative
> import Data.Traversable
> import Data.Foldable

> type Pair (x :: Nat) (y :: Nat) = '(x, y)

%% natural numbers

> data Nat = Z | S Nat
> 
> data Natty :: Nat -> * where
>   Zy :: Natty Z
>   Sy :: Natty n -> Natty (S n)
> 
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

%% vectors

> data Vec :: Nat -> * -> * where
>   V0   ::                 Vec Z x
>   (:>) :: x -> Vec n x -> Vec (S n) x
> 
> vcopies :: forall n x.Natty n -> x -> Vec n x
> vcopies Zy x = V0
> vcopies (Sy n) x = x :> vcopies n x   
> 
> vapp :: forall n s t.Vec n (s -> t) -> Vec n s -> Vec n t
> vapp V0 V0 = V0
> vapp (f :> fs) (s :> ss) = f s :> vapp fs ss
> 
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


%% natural numbers again

> class NATTYC (n :: Nat) where
>   nattyC :: NattyC n
> 
> instance NATTYC Z where
>   nattyC = ZyC
> 
> instance NATTYC n => NATTYC (S n) where
>   nattyC = SyC nattyC
> 
> natterC :: NattyC n -> (NATTYC n => t) -> t
> natterC ZyC     t = t
> natterC (SyC n) t = natterC n t

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

%format natter = "\F{natter}"
%format natty = "\F{natty}"
%format vcopies = "\F{vcopies}"
%format vapp = "\F{vapp}"
%format pure = "\F{pure}"
%format traverse = "\F{traverse}"

%format fmap = "\F{fmap}"
%format fmapDefault = "\F{fmapDefault}"
%format foldMap = "\F{foldMap}"

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
the successor case.

> data NattyC :: Nat -> * where
>   ZyC :: NattyC Z
>   SyC :: NATTYC n => NattyC n -> NattyC (S n)

Each choice has advantages and disadvantages.

Without the |NATTY| constraint on |Sy|, we can write a function to
compute the length of a vector as follows:

> vlength :: Vec n x -> Natty n
> vlength V0        = Zy
> vlength (x :> xs) = Sy (vlength xs)

Conversely, with the |NATTY| constraint on |Sy|, we must write:

> vlengthC :: VecC n x -> NattyC n
> vlengthC V0C        = ZyC
> vlengthC (x :>> xs) = natterC n (SyC n) where n = vlengthC xs

in order to bring the appropriate |NATTY| constraint into scope for
the inductive case.

Let us define a matrix as a vertical vector of horizontal vectors.

> data Matrix :: * -> (Nat, Nat) -> * where
>   Mat :: Vec h (Vec w a) -> Matrix a (Pair w h)
>
> unMat :: Matrix a (Pair w h) -> Vec h (Vec w a)
> unMat (Mat vs) = vs

%if False

> data MatrixC :: * -> (Nat, Nat) -> * where
>   MatC :: VecC h (VecC w a) -> MatrixC a (Pair w h)
>
> unMatC :: MatrixC a (Pair w h) -> VecC h (VecC w a)
> unMatC (MatC vs) = vs

%endif

Let us write a function to construct an identity matrix of size
|n|. Without the |NATTY| constraint on |Sy|, we must use |natter| to
bring the appropriate typing constraint into scope.

> idMatrix :: Natty n -> Matrix Int (Pair n n)
> idMatrix (Sy n)  =
>   natter n (Mat ((1 :> pure 0) :> ((0 :>) <$>
>     (unMat (idMatrix n)))))
> idMatrix Zy      = Mat V0

%$

Conversely, with the |NATTY| constraint on |Sy|, we can omit |natter|,
because the required constraint is already in scope.

> idMatrixC :: NattyC n -> MatrixC Int (Pair n n)
> idMatrixC (SyC n)  = 
>   MatC ((1 :>> pure 0) :>> ((0 :>>) <$>
>     (unMatC (idMatrixC n))))
> idMatrixC ZyC      = MatC V0C

%$

For writing |vlength| it is most convenient to omit the |NATTY|
constraint from the successor constructor.
%
For writing |idMatrix|, it is most convenient to attach the |NATTY|
constraint to the successor constructor.

