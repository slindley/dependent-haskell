%if False

> {-# LANGUAGE GADTs, PolyKinds, KindSignatures, MultiParamTypeClasses,
>     DataKinds, FlexibleInstances, RankNTypes, FlexibleContexts,
>     TypeOperators, TypeFamilies #-}

> module NatVec where

> type Pair (x :: j) (y :: k) = '(x, y)

%endif

Haskell's |DataKinds| extension~\cite{YorgeyWCJVM12} has the impact of
duplicating an ordinary data type, such as

> data Nat = Z | S Nat deriving (Show, Eq, Ord)

at the \emph{kind} level. That is, for the price of the above
\emph{type} declaration, GHC silently generates a new \emph{kind},
also |Nat|, with inhabitants formed by type level data
constructors '|Z| and '|S|, where the prefixed quote may be dropped for
names which do not clash with declared types. It is pleasant to think
that the \emph{same} |Nat| is both a type and a kind, but sadly, the
current conceptual separation of types and kinds requires the
construction of a separate kind-level replica.

The |Nat| kind is now available as a domain for various forms of
universal quantification, classified on the one hand by whether the
quantified values are available only statically or also dynamically,
and on the other hand by whether the associated abstraction and
application are implicit or explicit in the program text. Picking
apart Milner's alignment of distinctions, we acquire a matrix of four
dependent quantifiers for term-like things. In this section and the
next, we explore the Haskell encodings and the typical usage of these
quantifiers, tabulated here for the
paradigmatic example of natural numbers:
\[
\begin{array}{r||cc}
     & \textbf{implicit} & \textbf{explicit} \\
\hline
\textbf{static} & |forall ((n :: Nat)).| & |forall ((n :: Nat)). Proxy n ->| \\
\textbf{dynamic} & |forall n. NATTY n =>| & |forall n. Natty n ->| \\
\end{array}
\]

To get to work, we must find types which involve
numbers. Generalized algebraic data types, now bearing an even
stronger resemblance to the inductive families of dependent type
theories, provide one source. The family of \emph{vectors} is the
traditional first example of such a creature, and we shall resist the
contrarian urge to choose another because we shall need vectors later
in the paper.

> data Vec :: Nat -> * -> * where
>   V0    ::                  Vec Z x
>   (:>)  :: x -> Vec n x ->  Vec (S n) x

In Haskell, one must choose a type's order of arguments with care, as
partial application is permitted but $\lambda$-abstraction is not.
Here we depart a little from the dependently typed tradition by giving
|Vec| its length \emph{index} to the left of its payload type
\emph{parameter}, |x|, because we plan to develop the functorial
structure of each |Vec n| in the next section.

We note that the correspondence with the inductive families of Agda,
Coq and Idris is not exact. The |n| in the Haskell type of |(:>)| is
given a \emph{static} implicit quantifier and erased at run time,
whereas its type theoretic counterpart is \emph{dynamic} and implicit.
Idris, at least, is clever enough to erase the run time copy of |n|,
through Brady's `forcing' optimization~\cite{BradyMM03}.

Meanwhile, type level data are useful for more than just indexing data types.
We may indeed compute with them, making use of Haskell's `type family' extension,
which allows us to define `families' (meaning merely `functions') of `types'
in the sloppy sense of `things at the type level', not just the pedantic sense
of `things of kind |*|'.

%format :+ = "\mathbin{\mbox{$:\!\!+$}}"

> type family (m :: Nat) :+ (n :: Nat) :: Nat
> type instance  Z    :+  n  =  n
> type instance  S m  :+  n  =  S (m :+ n)

In an intensional dependent type theory, such a definition extends the
normalization algorithm by which the type checker decides type
equality up to the partial evaluation of open terms. If syntactically
distinct types share a normal form, then they share the same terms. E.g.,
in type theory, terms inhabiting |Vec (S (S Z) :+ n) x| also inhabit
|Vec (S (S n)) x| without further ado.
Of course, functions often satisfy laws, e.g. associativity and
commutativity, which are not directly computational: terms of type
|Vec (n :+ S (S Z)) x| do not inhabit |Vec (S (S n)) x|, even though the two
coincide for all concrete values of |n|. Fortunately,
one can formulate `propositional equality' types, whose inhabitants
constitute evidence for equations. Values can be transported between
provably equal types by explicit appeal to such evidence.

In Haskell's kernel, type equality is entirely
syntactic~\cite{SulzmannCJD07}, so that kernel terms in |Vec (S (S Z) :+ n) x|
do not also inhabit |Vec (S (S n)) x|. The above `definition' \emph{axiomatizes} |(:+)|
for Haskell's propositional equality, and every program which relies
on computing sums must be elaborated with explicit appeal to
evidence derived from those axioms. The translation from the surface language to the kernel
attempts to generate this evidence by a powerful but inscrutable
constraint solving heuristic. Experience suggests that the solver
computes aggressively, regardless of whether type level programs are
totally recursive, so we may confidently type vector concatenation in
terms of addition.

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

\todo{Reinstate the definition of \mbox{|(/+/)|} somewhere.}
%if False

> (/+/) :: Natty m -> Natty n -> Natty (m :+ n)
> Zy    /+/  n  = n
> Sy m  /+/  n  = Sy (m /+/ n)

%endif

Each type level value |n| in the |Nat| kind has a unique representative
in the type |Natty n|, so analysing the latter will reveal useful facts
about the former. The `$\Pi$-types', often written $(x\!:\!S)\to T$, of
dependent type theory abstract dependently over explicit dynamic things.
In Haskell, we can simulate this by abstracting dependently at the type
level and non-dependently over the singleton representative. We translate
(from Agda notation to Haskell):
\[
  (n\!:\!|Nat|)\to T \qquad \leadsto \qquad |forall (n :: Nat). Natty n -> |T
\]
Thus equipped, we may write

> vchop :: Natty m -> Vec (m :+ n) x -> (Vec m x, Vec n x)
> vchop Zy      xs         =  (V0,       xs)
> vchop (Sy m)  (x :> xs)  =  (x :> ys,  zs)
>   where (ys, zs) = vchop m xs

There may be an argument from implementation inertia in favour of this
means of dependent quantification, but it proliferates representations
of cognate notions, which is an eccentric way to keep things simple.

Moreover, we can only construct $\Pi$-types with domains admitting the
singleton construction. Whilst Monnier and
Haguenauer~\cite{monnierhaguenauer2010} have given a generic treatment
of the singleton construction, their result is not reproducible in
current GHC because GADTs are not promotable as kinds. We cannot form
a Haskell analogue of
\[
  (n\!:\!|Nat|)\to (|xs|\!:\!|Vec n x|)\to T[|xs|]
\]
but we expect this gap to be plugged in the near future. Promoting
|Vec n x| to a kind perforce involves using numbers not only in terms
and types, but in kinds as well. In the new, more flexible world, the
type/kind distinction is increasingly inconvenient, and a clear
candidate for abolition, as Weirich, Hsu, and Eisenberg
propose~\cite{Weirich13}.

Meanwhile, a further disturbance is in store if we choose to compute
only the first component returned by |vchop|. Cutting out the suffix
gives us

%format vtake = "\F{vtake}"

< vtake :: Natty m -> Vec (m :+ n) x -> Vec m x -- |BAD|
< vtake Zy      xs         =  V0
< vtake (Sy m)  (x :> xs)  =  x :> vtake m xs

but the resulting type error

{\scriptsize
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
          :> :: forall x (n :: Nat).
                  x -> Vec n x -> Vec ('S n) x,
        in an equation for `vtake'
      at NatVec.lhs:120:18-24
      `n2' is a rigid type variable bound by
           a pattern with constructor
             :> :: forall x (n :: Nat).
                     x -> Vec n x -> Vec ('S n) x,
           in an equation for `vtake'
           at NatVec.lhs:120:18
    Expected type: Vec (n1 :+ n0) x
      Actual type: Vec n2 x
    In the second argument of `vtake', namely `xs'
    In the second argument of `(:>)', namely `vtake m xs'
    In the expression: x :> vtake m xs
\end{verbatim}
}

\noindent
amounts to the fact that it is not clear how to instantiate |n| in the
recursive call. It takes sophisticated reasoning about addition to
realise that |(m :+)| is injective. To GHC, it is just an unknown
axiomatised function. The problem did not arise for |vchop|, because
relaying the suffix, |zs|, from the recursive output to the result
makes clear that the same |n| is needed in both places. This |n| is
not needed at run time, but without it there is no way to see that the
program makes sense.

The upshot is that there are data which, despite being static, must be
made explicit. One way to manifest them is via `proxy types', e.g.,

%format kappa = "\kappa"

> data Proxy :: kappa -> * where
>   Proxy :: Proxy i

As you can see, the only dynamic information in |Proxy i| is
definedness, which there is never the need to check. Kind polymorphism
allows us to declare the proxy type once and for all. The only point
of a proxy is to point out that it has the same type at its binding
and its usage sites.  Although it is compulsory to instantiate
quantifiers by inference, proxies let us rig the guessing game so that
GHC can win it. We repair the definition of |vtake| thus:

> vtake :: Natty m -> Proxy n -> Vec (m :+ n) x -> Vec m x
> vtake Zy      n  xs         =  V0
> vtake (Sy m)  n  (x :> xs)  =  x :> vtake m n xs

\begin{sloppypar}
Of course, when calling |vtake|, we need to get a proxy from somewhere. If
we do not already have one, we can write |(Proxy :: Proxy t)| for the
relevant type level expression |t|. The |ScopedTypeVariables|
extension allows us to write open types. If we already have some other
value with the same index, e.g. a singleton value, we can erase it to a
proxy with
\end{sloppypar}

%format proxy = "\F{proxy}"

> proxy :: f i -> Proxy i
> proxy _ = Proxy

The |vtake| example shows that Haskell's |forall|quantifier supports
abstraction over data which play a relevant and computational role in
static types but have no impact on run time execution and thus
erasable. Most dependently typed languages, with ATS~\cite{CuiDX05}
being a notable exception, do not offer such a quantifier, which seems
to us something of an oversight. Coq's program
extraction~\cite{Paulin89a} and Brady's compilation
method~\cite{brady-thesis} both erase components whose types show
that they cannot be needed in computation, but they do not allow us to
make the promise that ordinary data in types like |Nat| will not be
needed at run time.

Meanwhile, Agda has an `irrelevant' quantifier, abstracting over data
which will even be ignored by the definitional equality of the type
system. In effect, the erasure induced by `irrelevance' is static as
well as dynamic, and is thus more powerful but less applicable. The
Agda translation of |vtake| cannot make |n| an irrelevant argument,
because it is needed to compute the length of the input, which most
certainly is statically relevant.  In contemporary Agda, it seems that
this |n| must be present at run time.

A further example, showing implicit quantification over data used statically
to compute a type but erased at run time, applies an |n|-ary operator to
an |n|-vector of arguments.

%format varity = "\F{varity}"

> type family Arity (n :: Nat) (x :: *) :: *
> type instance Arity Z      x  =  x
> type instance Arity (S n)  x  =  x -> Arity n x

> varity :: Arity n x -> Vec n x -> x
> varity  x  V0         =  x
> varity  f  (x :> xs)  =  varity (f x) xs

Here, pattern matching on the vector delivers sufficient information
about its length to unfold the |Arity| computation. Once again, Agda
would allow |n| to remain implicit in source code, but insist on
retaining |n| at run time. Meanwhile, Brady's `detagging'
optimization~\cite{BradyMM03} would retain |n| but remove the
constructor tag from the representation of vectors, compiling the
above match on the vector to match instead on |n| then project from
the vector.

To sum up, we have distinguished Haskell's dependent static implicit
|forall|quantifier from the dependent dynamic explicit $\Pi$-types of
dependent type theory. We have seen how to make |forall| static and
explicit with a |Proxy|, and how to make it dynamic and explicit
whenever the singleton construction is possible. However, we have noted
that whilst Haskell struggles to simulate $\Pi$ with |forall|, the reverse
is the case in type theory. What is needed, on both sides, is a more
systematic treatment of the varieties of quantification.

%if False

> infixr 4 :>
> instance Show x => Show (Vec n x) where
>   show V0 = "V0"
>   show (x :> xs) = show x ++ " :> " ++ show xs

%endif

%%  LocalWords:  GADTs PolyKinds KindSignatures MultiParamTypeClasses
%%  LocalWords:  DataKinds FlexibleInstances RankNTypes TypeOperators
%%  LocalWords:  FlexibleContexts TypeFamilies NatVec Haskell's Eq ys
%%  LocalWords:  Ord generalized contrarian Vec Haskell functorial xs
%%  LocalWords:  intensional normalization associativity vappend GADT
%%  LocalWords:  commutativity vchop forall Zy Sy Agda zs vtake GHC
%%  LocalWords:  injective axiomatised definedness polymorphism Coq's
%%  LocalWords:  ScopedTypeVariables Brady's definitional ary Arity
%%  LocalWords:  varity detagging optimization infixr
