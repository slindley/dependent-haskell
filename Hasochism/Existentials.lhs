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

> wrapNat :: Int -> WNat
> wrapNat  0  =  Ex Zy
> wrapNat  n  =  case wrapNat (n-1) of
>                  Ex wn -> Ex (Sy wn)

> data (p :: j -> *) :**: (q :: k -> *) :: (j, k) -> * where
>   (:&&:) :: p j -> q k -> (p :**: q) (Pair j k)

> wrapPair :: (a -> Ex p) ->
>             (b -> Ex q) ->
>               (a, b) -> Ex (p :**: q)
> wrapPair w1 w2 (x1, x2) =
>   case (w1 x1, w2 x2) of
>     (Ex v1, Ex v2) -> Ex (v1 :&&: v2)

> type WPoint = Ex (Natty :**: Natty)
> type WSize = Ex (Natty :**: Natty)
> type WRegion = Ex ((Natty :**: Natty) :**: (Natty :**: Natty))

> wrapPoint = wrapPair wrapNat wrapNat
> wrapSize = wrapPair wrapNat wrapNat
> wrapRegion = wrapPair wrapPoint wrapSize

> newtype Flip f a b = Flip {unFlip :: f b a}

> type WVec a = Ex (Flip Vec a)

> wrapVec :: [a] -> WVec a
> wrapVec []      = Ex (Flip V0)
> wrapVec (x:xs)  = case wrapVec xs of
>   Ex (Flip v) -> Ex (Flip (x :> v))

