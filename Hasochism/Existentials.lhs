%if False

> {-# LANGUAGE GADTs, PolyKinds, KindSignatures, MultiParamTypeClasses,
>     DataKinds, FlexibleInstances, RankNTypes, FlexibleContexts,
>     TypeOperators, TypeFamilies #-}

> module Pies where
>
> import NatVec

%endif

%format :**: = ":\!\!*\!*\!\!:"
%format :&&: = ":\!\!\&\!\&\!\!:"

> data Ex (p :: k -> *) where
>   Ex :: p i -> Ex p

> type WNat = Ex Natty

> data (p :: j -> *) :**: (q :: k -> *) :: (j, k) -> * where
>   (:&&:) :: p j -> q k -> (p :**: q) (Pair j k)

> type WPoint = Ex (Natty :**: Natty)
> type WRegion = Ex ((Natty :**: Natty) :**: (Natty :**: Natty))

> newtype Flip f a b = Flip {unFlip :: f b a}

> type WVec a = Ex (Flip Vec a)

