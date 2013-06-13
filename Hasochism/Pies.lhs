%if False

> {-# LANGUAGE GADTs, PolyKinds, KindSignatures, MultiParamTypeClasses,
>     DataKinds, FlexibleInstances, RankNTypes, FlexibleContexts,
>     TypeOperators, TypeFamilies #-}

> module Pies where
>
> import NatVec
> import Control.Applicative
> import Data.Foldable
> import Data.Traversable

%endif

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

We have already seen that using |Natty| we can simulate explicit $\Pi$
types in Haskell. Using type classes, we can make these implicit.

\todo{say something about implicit $\Pi$ types in Agda?}

The |NATTY| type class defines a single method |natty|, that infers
the |Natty| corresponding to each promoted |Nat|.

> class NATTY (n :: Nat) where
>   natty :: Natty n
> 
> instance NATTY Z where
>   natty = Zy
> 
> instance NATTY n => NATTY (S n) where
>   natty = Sy natty

Occasionally we have at hand an explicit |Natty n|, but would like to
use it in a context with an implicit |NATTY n| type class constraint.
 
> natter :: Natty n -> (NATTY n => t) -> t
> natter Zy     t = t
> natter (Sy n) t = natter n t

The |natter| function effectively converts an explicit |Natty| to an
implicit |NATTY|.

Using a |NATTY| type class constraint, we can define an |Applicative|
instance for vectors.

> instance NATTY n => Applicative (Vec n) where
>   pure = vcopies natty where
>   (<*>) = vapp where
>
> vcopies :: forall n x.Natty n -> x -> Vec n x
> vcopies Zy x = V0
> vcopies (Sy n) x = x :> vcopies n x   
> 
> vapp :: forall n s t.Vec n (s -> t) -> Vec n s -> Vec n t
> vapp V0 V0 = V0
> vapp (f :> fs) (s :> ss) = f s :> vapp fs ss

We choose to expose the |vcopies| and |vapp| functions which are both
polymorphic in the length of the vector, as sometimes the extra
generality over |pure| and |(<*>)| is useful.

Vectors are traversable, foldable functors.
                             
> instance Traversable (Vec n) where
>   traverse f V0 = pure V0
>   traverse f (x :> xs) = (:>) <$> f x <*> traverse f xs
>
> instance Foldable (Vec n) where
>   foldMap = foldMapDefault

> instance Functor (Vec n) where
>   fmap = fmapDefault
 
%$%

