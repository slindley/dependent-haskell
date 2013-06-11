%if False

> {-# LANGUAGE GADTs, PolyKinds, KindSignatures, MultiParamTypeClasses,
>     DataKinds, FlexibleInstances, RankNTypes, FlexibleContexts,
>     TypeOperators, TypeFamilies #-}

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
>   V0    ::                  Vec Z x
>   (:>)  :: x -> Vec n x ->  Vec (S n) x

In Haskell, one must choose a type's order of arguments with care, as
partial application is permitted but $\lambda$-abstraction is not.
Here we depart a little from the dependently typed tradition by giving
|Vec| its length \emph{index} to the left of its payload type
\emph{parameter}, |x|, because we plan to develop the functorial
structure of each |Vec n| in the next section.

However, type level data are useful for more than just indexing data types.
We may indeed compute with them, making use of Haskell's `type family' extension,
which allows us to define `families' (meaning merely `functions') of `types'
in the sloppy sense of `things at the type level', not just the pedantic sense
of `things of kind |*|'.

> type family (m :: Nat) :+ (n :: Nat) :: Nat
> type instance  Z    :+  n  =  n
> type instance  S m  :+  n  =  S (m :+ n)

In an intensional dependent type theory, such a definition extends the
normalization algorithm by which the type checker decides type
equality up to the partial evaluation of open terms. If syntactically
distinct types share a normal form, then they share the same terms.
Of course, functions often have algebraic properties, e.g. associativity and
commutativity, which are not obvious from computation alone. Fortunately,
one can formulate `propositional equality' types, whose inhabitants
constitute evidence for equations. Values can be transported between
provably equal types by explicit appeal to such evidence.

In Haskell's kernel type equality is entirely syntactic. The above is
a collection of axioms for Haskell's propositional equality, and every
program which relies on computation must be elaborated in terms of
explicit appeal to evidence. The translation from the surface language
to the kernel attempts to generate this evidence by a powerful but
inscrutable constraint solving heuristic. Experience suggests that the
solver computes aggressively, regardless of whether type level programs
are totally recursive, so we may confidently type vector concatenation
in terms of addition.

> vappend :: Vec m x -> Vec n x -> Vec (m :+ n) x
> vappend  V0         ys  =  ys
> vappend  (x :> xs)  ys  =  x :> vappend xs ys

Note that the numbers here play an entirely static role: the flow of
control can be determined entirely from the constructors of the first
vector. Suppose, however, that we wish to invert concatenation,
chopping a vector in two.

< vchop :: Vec (m :+ n) x -> (Vec m x, Vec n x)

Unlike with |vappend|, we shall certainly need |m| at run time, and we
shall need to refer to it explicitly in order to judge where to
chop. However, Haskell's dependent |forall|-quantifier is for implicit
and exclusively static things. The standard solution is to define the
run time replica of some static data as a GADT.

> data Natty :: Nat -> * where
>   Zy  :: Natty Z
>   Sy  :: Natty n -> Natty (S n)

