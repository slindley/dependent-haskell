%if False

> {-# LANGUAGE GADTs, PolyKinds, KindSignatures, MultiParamTypeClasses,
>     DataKinds, FlexibleInstances, RankNTypes, FlexibleContexts #-}

> module NatVec where

%endif

The |DataKinds| extension has the impact of duplicating an ordinary data type, such as

> data Nat = Z | S Nat deriving (Show, Eq, Ord)

at the \emph{kind} level. It is pleasant to think that the \emph{same} |Nat| is both a
type and a kind, but sadly, the current conceptual separation of types and kinds
requires the construction of a separate kind-level replica.

The |Nat| kind is now available for deployment in the indexing of
generalized algebraic data types, now bearing an even stronger resemblance to the
inductive families of dependent type theories. The family of \emph{vectors} is the
traditional first example of such a creature, and we shall resist the contrarian
urge because we shall need vectors later in the paper.

> data Vec :: Nat -> * -> * where
>   Nil   ::                  Vec Z x
>   (:>)  :: x -> Vec n x ->  Vec (S n) x

However, Haskell allows us to depart a little from tradition by
giving |Vec| its length \emph{index} to the left of its payload type
\emph{parameter}, |x|. A data type's parameters, like |x| here, are
abstracted uniformly over the whole declaration: we could instantiate
|x| with |Char| and acquire a more specific valid declaration. A data
type's indices vary in the way they are used, either in the return
types of constructors, or in recursive positions.