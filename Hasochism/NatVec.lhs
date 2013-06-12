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
urge to choose another because we shall need vectors later in the paper.

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

%format vappend = "\F{vappend}"

> vappend :: Vec m x -> Vec n x -> Vec (m :+ n) x
> vappend  V0         ys  =  ys
> vappend  (x :> xs)  ys  =  x :> vappend xs ys

Note that the numbers here play an entirely static role: the flow of
control can be determined entirely from the constructors of the first
vector. Suppose, however, that we wish to invert concatenation,
chopping a vector in two.

%format vchop = "\F{vchop}"

< vchop :: Vec (m :+ n) x -> (Vec m x, Vec n x)

Unlike with |vappend|, we shall certainly need |m| at run time, and we
shall need to refer to it explicitly in order to judge where to
chop. However, Haskell's dependent |forall|quantifier is for implicit
and exclusively static things. The standard solution is to define the
run time replica of some static data as a \emph{singleton} GADT.

> data Natty :: Nat -> * where
>   Zy  :: Natty Z
>   Sy  :: Natty n -> Natty (S n)

Each type level value |n| in the |Nat| kind has a unique representative
in the type |Natty n|, so analysing the latter will reveal useful facts
about the former. The `$\Pi$-types', often written $(x\!:\!S)\to T$, of
dependent type theory abstract dependently over explicit dynamic things.
In Haskell, we can simulate this by abstracting dependently at the type
level and non-dependently over the singleton representative. We translate
(from Agda notation to Haskell):
\[
  (x\!:\!|Nat|)\to T \qquad \leadsto \qquad |forall (x :: Nat). Natty x -> T|
\]

Thus equipped, we may write

> vchop :: Natty m -> Vec (m :+ n) x -> (Vec m x, Vec n x)
> vchop Zy      xs         =  (V0,       xs)
> vchop (Sy m)  (x :> xs)  =  (x :> ys,  zs)
>   where (ys, zs) = vchop m xs

There may be an argument from implementation inertia in favour of this
means of dependent quantification, but it proliferates representations
of cognate notions, which is an eccentric way to keep things simple.

A further disturbance is in store if we choose to compute only the first
component returned by |vchop|. Cutting out the suffix gives us

%format vtake = "\F{vtake}"
%format BAD = "\hfill(\times)"

< vtake :: Natty m -> Vec (m :+ n) x -> Vec m x -- |BAD|
< vtake Zy      xs         =  V0
< vtake (Sy m)  (x :> xs)  =  x :> vtake m xs

but the resulting type error

{\tiny
\begin{verbatim}
NatVec.lhs:120:44:
    Could not deduce (n2 ~ (n1 :+ n0))
    from the context (m ~ 'S n1)
      bound by a pattern with constructor
                 Sy :: forall (n :: Nat). Natty n -> Natty ('S n),
               in an equation for `vtake'
      at NatVec.lhs:120:10-13
    or from ((m :+ n) ~ 'S n2)
      bound by a pattern with constructor
                 :> :: forall x (n :: Nat). x -> Vec n x -> Vec ('S n) x,
               in an equation for `vtake'
      at NatVec.lhs:120:18-24
      `n2' is a rigid type variable bound by
           a pattern with constructor
             :> :: forall x (n :: Nat). x -> Vec n x -> Vec ('S n) x,
           in an equation for `vtake'
           at NatVec.lhs:120:18
    Expected type: Vec (n1 :+ n0) x
      Actual type: Vec n2 x
    In the second argument of `vtake', namely `xs'
    In the second argument of `(:>)', namely `vtake m xs'
    In the expression: x :> vtake m xs
\end{verbatim}
}

amounts to the fact that it is not clear how to instantiate |n| in the
recursive call. It takes sophisticated reasoning about addition to
realise that |(m :+)| is injective. To GHC, it is just an unknown
axiomatised function. The problem did not arise for |vchop|, because
relaying the suffix, |zs|, from the recursive output to the result is
makes clear that the same |n| is needed in both places. This |n| is
not needed at run time, but without it there is no way to see that the
program makes sense.

The upshot is that there are data which, despite being static, must be
made explicit. One way to manifest them is via `proxy types', e.g.,

%format kappa = "\kappa"

> data Proxy :: kappa -> * where
>   Proxy :: Proxy i

As you can see, the only dynamic information in |Proxy i| is definedness,
which there is never the need to check. Kind polymorphism allows us to
declare the proxy type once for all. The only point of a proxy is to
point out that it has the same type at its binding and its usage sites.
Although it is compulsory to instantiate quantifiers by inference,
proxies let us rig the guessing game so that GHC can win it. We repair
the definition of |vtake| thus:

> vtake :: Natty m -> Proxy n -> Vec (m :+ n) x -> Vec m x
> vtake Zy      n  xs         =  V0
> vtake (Sy m)  n  (x :> xs)  =  x :> vtake m n xs

Of course, when calling |vtake|, we need to get a proxy from somewhere. If
we do not already have one, we can write |(Proxy :: Proxy t)| for the
relevant type level expression |t|. The |ScopedTypeVariables|
extension allows us to write open types. If we already have some other
value with the same index, e.g. a singleton value, we can erase it to a
proxy with

%format proxy = "\F{proxy}"

> proxy :: f i -> Proxy i
> proxy _ = Proxy

[so we have an explicit intersection; much needed in Agda]
