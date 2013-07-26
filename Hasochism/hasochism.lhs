\documentclass{sigplanconf}


% US Letter page size
\pdfpagewidth=8.5in
\pdfpageheight=11in

%include polycode.fmt
%include forall.fmt

\DeclareMathAlphabet{\mathkw}{OT1}{cmss}{bx}{n}
%subst keyword a = "\mathkw{" a "}"
%subst conid a = "\mathsf{" a "}"
%format where = "\;\mathkw{where}"
%format family = "\mathkw{family}"

%format * = "\star"
%format PRIME = "{}^{\prime}\!\!"
%format Prime = "{}^{\prime}"
%format PRIMEPRIME = "{}^{\prime\prime}\!\!"

%format :+ = ":\!\!+\,"
%format :- = ":\!\!-\,"

%format /+/ = "/\!\!+\!\!/"
%format /-/ = "/\!\!-\!\!/"

%format <$> = "<\!\!\mathord{\$}\!\!>"
%format <*> = "<\!\!\mathord{\star}\!\!>"

%format :**: = ":\!\!*\!*\!\!:"
%format :&&: = ":\!\!\&\!\&\!\!:"

%format :*: = ":\!\!*\!\!:"
%format :&: = ":\!\!\&\!\!:"

%format :-> = ":\to"
%%% ":\!\!-\!\!>"

%format (Pair (x) (y)) = Prime(x, y)

%format x1 = x "_1"
%format x2 = x "_2"
%format xn = x "_n"

%format y1 = y "_1"
%format y2 = y "_2"

%format w1 = w "_1"
%format w2 = w "_2"

%format h1 = h "_1"
%format h2 = h "_2"

%format wh1 = wh "_1"
%format wh2 = wh "_2"


%format b1 = b "_1"
%format b2 = b "_2"
%format b11 = b "_{11}"
%format b12 = b "_{12}"
%format b21 = b "_{21}"
%format b22 = b "_{22}"

%format p1 = p "_1"
%format p2 = p "_2"

%format EXISTS = "\exists\!"
%format DOT = "\!\!.\!\!"

%format ~ = "\sim"

%format BAD = "\hfill(\times)"

%format iota = "\iota"
%format kappa = "\kappa"


%format show = "\F{show}"

%format const = "\F{const}"
%format id = "\F{id}"

%format fst = "\F{fst}"
%format snd = "\F{snd}"

\newcommand{\F}{\mathsf}

\renewcommand{\hscodestyle}{\small}

\newcommand\todo[1]{\textbf{TODO: }{#1}}


\usepackage{amsmath}
\usepackage{xspace}
\usepackage{url}
\usepackage{hyperref}

\newcommand{\singletons}{\textsf{singletons}\xspace}

\begin{document}

\exclusivelicense
\conferenceinfo{Haskell~'13}{September 23--24, Boston, MA, USA} 
\copyrightyear{2013}
\copyrightdata{978-1-4503-2383-3/13/09}
\doi{2503778.2503786}

%% \titlebanner{banner above paper title}        % These are ignored unless
%% \preprintfooter{short description of paper}   % 'preprint' option specified.

\title{Hasochism}
\subtitle{The Pleasure and Pain of Dependently Typed Haskell Programming}

\authorinfo{Sam Lindley}
           {University of Strathclyde}
           {Sam.Lindley@@ed.ac.uk}
\authorinfo{Conor McBride}
           {University of Strathclyde}
           {conor.mcbride@@strath.ac.uk}

\maketitle

\begin{abstract}
Haskell's type system has outgrown its Hindley-Milner roots to the
extent that it now stretches to the basics of dependently typed
programming. In this paper, we collate and classify techniques for
programming with dependent types in Haskell, and contribute some new
ones. In particular, through extended examples---merge-sort and
rectangular tilings---we show how to exploit Haskell's constraint
solver as a theorem prover, delivering code which, as Agda
programmers, we envy.  We explore the compromises involved in
simulating variations on the theme of the dependent function space in
an attempt to help programmers put dependent types to work, and to
inform the evolving language design both of Haskell and of dependently
typed languages more broadly.
\end{abstract}

%% \category{CR-number}{subcategory}{third-level}

\category{D.1.1}{Applicative (Functional) Programming}{}
\category{D.3.2}{Language Classifications}{Applicative (functional) languages}
\category{D.3.3}{Language Constructs and Features}{}

%% \terms
%% term1, term2

\keywords
dependent types; singletons; data type promotion; proof search; invariants

\section{Introduction}
\label{sec:intro}

In the design of Standard ML, Milner and his colleagues achieved a remarkable
alignment of distinctions:
~\cite{Milner78,ML}\[\begin{array}{l||r@@{\quad}l}
\textrm{syntactic category}  & \textbf{terms}      &     \textbf{types} \\
\textrm{phase distinction}   & \textbf{dynamic}    &    \textbf{static} \\
\textrm{inference}           & \textbf{explicit}   &  \textbf{implicit} \\
\textrm{abstraction}         & \textbf{simple}     & \textbf{dependent} \\
\end{array}\]

The things you write are the things you run, namely terms, for which
abstraction (with an explicit $\lambda$) is simply typed---the bound
variable does not occur in the return type of the function. The things
which you leave to be inferred, namely polymorphic type schemes, exist
only at compile time and allow (outermost) dependent abstraction over
types, with implicit application at usage sites instantiating the
bound variables.

An unintended consequence of Milner's achievement is that we sometimes
blur the distinctions between these distinctions. We find it hard to
push them out of alignment because we lose sight of the very
possibility of doing so. For example, some have voiced objections to
the prospect of terms in types on the grounds that efficient
compilation relies on erasure to the dynamic fragment of the
language. However, renegotiating the term/type distinction need not
destroy the dynamic/static distinction, as shown by Coq's venerable
program extraction algorithm~\cite{Paulin89a}, erasing types and
proofs from dependently typed constructions.

Meanwhile, Haskell's type classes~\cite{WadlerB89} demonstrate the
value of dynamic components which are none the less
implicit---instance dictionaries. Indeed, type inference seems a timid
virtue once you glimpse the prospect of \emph{program} inference, yet
some are made nervous by the prospect of unwritten programs being
run. Similarly, Haskell's combination of higher kinds and constraints
means that sometimes static types must be given explicitly, in order
not only to check them, but also to drive the generation of invisible
boilerplate.

Milner's aligned distinctions have shifted apart, but Haskell persists
with one dependent quantifier for implicit abstraction over static
types. What counts as a `type' has begun to stretch.
%
Our \emph{Strathclyde Haskell Enhancement} (SHE)
preprocessor~\cite{she} systematized and sugared common constructions
for building the type level analogues of run time data, together with
run time witnesses to type level values. SHE then provided something
which resembles a dependent quantifier for explicit abstraction over
dynamic terms---the $\Pi$-type of dependent type theory---in domains
simple enough to admit the singleton construction.
%
Before long, Glasgow Haskell headquarters responded with a proper kind
system for `promoted' data types~\cite{YorgeyWCJVM12}, making possible
the \singletons library~\cite{EisenbergW12}. The arrival of data types
at the kind level necessitated polymorphism in kinds: Haskell is now a
dependently \emph{kinded} language, and although it is a nuisance that
the kind-level $\forall$ is compulsorily implicit, the fresh
abstractions it offers have yielded considerable simplification, e.g.,
in support of generic programming~\cite{Magalhaes12}.

So we decided to have some fun, motivated by the reliability benefits
of programming at a higher level of static precision, and the
experience of doing so in prototype dependently typed languages---in
our case, Epigram~\cite{McBrideM04} and Agda~\cite{norell:thesis}.
There is a real sense of comfort which comes from achieving a high
level of hygiene, and it is something which we want to bring with us
into practical programming in industrial strength languages like
Haskell.  Of course, reality intervenes at this point: some desirable
methods are harder to express than one might hope, but we can also
report some pleasant surprises.  We hope our experiments inform both
programming practice with current tools and the direction of travel
for Haskell's evolution.

Specifically, this paper contributes
\begin{itemize}
\item an analysis of how to achieve dependent quantification in Haskell, framed
  by the distinctions drawn above---we note that Agda and Haskell both have
  room for improvement;

\item practical techniques for dependently typed programming in
  Haskell, with a view to minimizing explicit proof in program texts;

\item an implementation of merge-sort guaranteeing the ordering invariant
  for its output, in which the proofs are \emph{silent};

\item an algebra for tiling size-indexed boxes, fitting with precision,
  leading to an implementation of a screen editor.
\end{itemize}

\paragraph{Overview}
Section~\ref{sec:natvec} explores variations on the theme of dependent quantification, through paradigmatic examples involving natural numbers and vectors.
 Section~\ref{sec:pies} focuses on the implicit/explicit distinction, whilst developing standard library functionality for vectors, identifying areas of concern. Section~\ref{sec:merge-sort} delivers merge-sort, using instance inference for proof search.
Section~\ref{sec:evidence} explores the use of data types to represent effective evidence. Section~\ref{sec:boxes} introduces an
algebra of size-indexed boxes, which is used to build a text editor in
Section~\ref{sec:editor}. Section~\ref{sec:conclusion} concludes.

\paragraph{Online code}
All of the Haskell source code for the developments in this paper are
available at \url{https://github.com/slindley/dependent-haskell/tree/master/Hasochism}.

\paragraph{Acknowledgements} This work was supported by EPSRC project
\emph{Haskell Types with Added Value}, grant EP/J014591/1. We are
grateful to be part of the long running conversation about Haskell's
type system, and in particular to Simon Peyton Jones, Stephanie
Weirich, Richard Eisenberg, Iavor Diatchki, Dimitrios Vytiniotis,
Jos{\'e} Pedro Magalh{\~a}es and our colleague Adam Gundry.

\section{A Variety of Quantifiers}
\label{sec:natvec}
%include NatVec.lhs

\section{Explicit and Implicit $\Pi$-Types}
\label{sec:pies}

%include Pies.lhs

\subsection{The NATTY-in-Natty Question}

%include NATTYInNatty.lhs

%% \section{Existentials}

%% %include Existentials.lhs

\section{An Ordered Silence}
\label{sec:merge-sort}

%include MergeSort.lhs

% \section{Evidence Combining Data with Proof}
\section{What are the Data that Go with Proofs?}
\label{sec:evidence}

%include Evidence.lhs

\section{Boxes}
\label{sec:boxes}

%include BoxPain.lhs

%include BoxPleasure.lhs

\section{An Editor}
\label{sec:editor}

%include Editor.lhs

\section{Conclusion}
\label{sec:conclusion}

We have constructed and explored the use of the
static-versus-dynamic/explicit-versus-implicit matrix of
value-dependent quantifiers in Haskell. We have observed the
awkwardness, but enjoyed the mere possibility, of dynamic
quantification and used it to build substantial examples of sorting
and box-tiling, where the establishment and maintenance of invariants
is based not just on propagation of static indices, but on dynamic
generation of evidence.

After some fairly hairy theorem proving, the worst of which we have
spared you, we learned how to package proofs which follow a similar
pattern inside GADTs of useful evidence. GHC's constraint solver is a
good enough automatic theorem prover to check the proof steps
corresponding to the recursion structure of the evidence-generating
program. Case analysis on the resulting evidence is sufficient to
persuade GHC that sorting invariants hold and that boxes snap
together. In this respect, Haskell handles simple proofs much more
neatly than Agda, where proving is as explicit as programming because
it is programming. There is still room for improvement: we do not yet
have a \emph{compositional} way to express just the \emph{fact} that
properties follow by a common proof pattern in a way that GHC will
silently check.

There is room for improvement also in the treatment of dependent
quantification, both in Haskell and in dependently typed programming
languages. Haskell naturally gives good support for quantifying over
data which are purely static, whilst Agda insists on retaining these
data at run time. Meanwhile, the singletons shenanigans required to
support the dynamic quantifiers are really quite painful, both
conceptually---with the explosion of |Nat|, |Natty|, |NATTY| and
|WNat|---and in the practicalities of shuffling between them, spending
effort on converting values into singletons and singletons into
dictionaries containing exact copies of those singletons. If we want
to build a scalable technology with the precision of indexing we have
shown in our examples, we had better look for foundations which allow
the elimination of this complexity, not just the encoding of it.

The key step which we must take is to move on from Milner's alignment
of coincidences and stop working as if a single dependent static
implicit quantifier over types is all we need. We have encoded
quantification over the same type in different ways by abstracting
over different types in the same way, and the result is predictably
and, we hope, preventably unpleasant. The Strathclyde team are
actively exploring the remedy---generalizing the quantifier to reflect
its true diversity, and allowing each type to be used unduplicated
wherever it is meaningful.  The best thing about banging your head off
a brick wall is \emph{stopping}.

% \newpage


%% \appendix
%% \section{Appendix Title}

%% This is the text of the appendix, if you need one.

%% \acks

%% Acknowledgments, if needed.

% We recommend abbrvnat bibliography style.

\begin{thebibliography}{27}
\providecommand{\natexlab}[1]{#1}
\providecommand{\url}[1]{\texttt{#1}}
\expandafter\ifx\csname urlstyle\endcsname\relax
  \providecommand{\doi}[1]{doi: #1}\else
  \providecommand{\doi}{doi: \begingroup \urlstyle{rm}\Url}\fi

\bibitem[Abel and Scherer(2012)]{AbelS12}
A.~Abel and G.~Scherer.
\newblock On irrelevance and algorithmic equality in predicative type theory.
\newblock \emph{Logical Methods in Computer Science}, 8\penalty0 (1), 2012.

\bibitem[Aitken and Reppy(1992)]{aitken.reppy}
W.~Aitken and J.~Reppy.
\newblock Abstract value constructors.
\newblock Technical Report TR 92-1290, Cornell University, 1992.

\bibitem[Barras and Bernardo(2008)]{BarrasB08}
B.~Barras and B.~Bernardo.
\newblock The implicit calculus of constructions as a programming language with
  dependent types.
\newblock In \emph{FoSSaCS}, volume 4962 of \emph{LNCS}, pages 365--379, 2008.

\bibitem[Brady(2005)]{brady-thesis}
E.~Brady.
\newblock \emph{Practical Implementation of a Dependently Typed Functional
  Programming Language}.
\newblock PhD thesis, University of Durham, 2005.

\bibitem[Brady et~al.(2003)Brady, McBride, and McKinna]{BradyMM03}
E.~Brady, C.~McBride, and J.~McKinna.
\newblock Inductive families need not store their indices.
\newblock In \emph{TYPES}, volume 3085 of \emph{LNCS}, pages 115--129.
  Springer, 2003.

\bibitem[Cui et~al.(2005)Cui, Donnelly, and Xi]{CuiDX05}
S.~Cui, K.~Donnelly, and H.~Xi.
\newblock {ATS}: A language that combines programming with theorem proving.
\newblock In \emph{FroCoS}, volume 3717 of \emph{LNCS}, pages 310--320.
  Springer, 2005.

\bibitem[Eisenberg and Weirich(2012)]{EisenbergW12}
R.~A. Eisenberg and S.~Weirich.
\newblock Dependently typed programming with singletons.
\newblock In \emph{Haskell}, pages 117--130. ACM, 2012.

\bibitem[Huet(1997)]{Huet97}
G.~P. Huet.
\newblock The {Z}ipper.
\newblock \emph{J. Funct. Program.}, 7\penalty0 (5):\penalty0 549--554, 1997.

\bibitem[Kiselyov and Shan(2007)]{Kiselyov07position:lightweight}
O.~Kiselyov and C.-c. Shan.
\newblock Lightweight static resources: Sexy types for embedded and systems
  programming.
\newblock In \emph{TFP}, 2007.

\bibitem[Magalh\~{a}es(2012)]{Magalhaes12}
J.~P. Magalh\~{a}es.
\newblock The right kind of generic programming.
\newblock In \emph{WGP}, pages 13--24. ACM, 2012.

\bibitem[McBride(2000)]{McBride00:case-talk}
C.~McBride.
\newblock A {C}ase {F}or {D}ependent {F}amilies.
\newblock Seminar at {LFCS}, Edinburgh.
  \url{http://www.strictlypositive.org/a-case/}, 2000.

\bibitem[McBride(2011)]{McBride11}
C.~McBride.
\newblock Kleisli arrows of outrageous fortune, 2011.
\newblock Accepted for publication. \\
  \url{https://personal.cis.strath.ac.uk/conor.mcbride/Kleisli.pdf}.

\vfill\eject

\bibitem[McBride(2013)]{she}
C.~McBride.
\newblock The {S}trathclyde {H}askell {E}nhancement.
\newblock \url{https://personal.cis.strath.ac.uk/conor.mcbride/pub/she/}, 2013.

\bibitem[McBride and McKinna(2004)]{McBrideM04}
C.~McBride and J.~McKinna.
\newblock The view from the left.
\newblock \emph{J. Funct. Program.}, 14\penalty0 (1):\penalty0 69--111, 2004.

\bibitem[McBride and Paterson(2008)]{McbrideP08}
C.~McBride and R.~Paterson.
\newblock Applicative programming with effects.
\newblock \emph{J. Funct. Program.}, 18\penalty0 (1):\penalty0 1--13, 2008.

\bibitem[Milner(1978)]{Milner78}
R.~Milner.
\newblock A theory of type polymorphism in programming.
\newblock \emph{J. Comput. Syst. Sci.}, 17\penalty0 (3):\penalty0 348--375,
  1978.

\bibitem[Milner et~al.(1990)Milner, Tofte, and Harper]{ML}
R.~Milner, M.~Tofte, and R.~Harper.
\newblock \emph{The Definition of standard {ML}}.
\newblock MIT Press, 1990.

\bibitem[Miquel(2001)]{Miquel01}
A.~Miquel.
\newblock The implicit calculus of constructions.
\newblock In \emph{TLCA}, LNCS, pages 344--359. Springer, 2001.

\bibitem[Monnier and Haguenauer(2010)]{MonnierH10}
S.~Monnier and D.~Haguenauer.
\newblock Singleton types here, singleton types there, singleton types
  everywhere.
\newblock In \emph{PLPV}, pages 1--8. ACM, 2010.

\bibitem[Norell(2007)]{norell:thesis}
U.~Norell.
\newblock \emph{Towards a practical programming language based on dependent
  type theory}.
\newblock PhD thesis, Department of Computer Science and Engineering, Chalmers
  University of Technology, September 2007.

\bibitem[Paulin-Mohring(1989)]{Paulin89a}
C.~Paulin-Mohring.
\newblock Extracting ${F}_{\omega}$'s programs from proofs in the {Calculus of
  Constructions}.
\newblock In \emph{POPL}. ACM, 1989.

\bibitem[Pollack(1990)]{Pollack90}
R.~Pollack.
\newblock Implicit syntax.
\newblock Informal Proceedings of First Workshop on Logical Frameworks,
  Antibes, 1990.

\bibitem[Reynolds(2002)]{Reynolds02}
J.~C. Reynolds.
\newblock Separation logic: A logic for shared mutable data structures.
\newblock In \emph{LICS}, pages 55--74. IEEE Computer Society, 2002.

\bibitem[Sulzmann et~al.(2007)Sulzmann, Chakravarty, Jones, and
  Donnelly]{SulzmannCJD07}
M.~Sulzmann, M.~M.~T. Chakravarty, S.~L.~P. Jones, and K.~Donnelly.
\newblock {System F} with type equality coercions.
\newblock In \emph{TLDI}, pages 53--66. ACM, 2007.

\bibitem[Wadler and Blott(1989)]{WadlerB89}
P.~Wadler and S.~Blott.
\newblock How to make ad-hoc polymorphism less ad-hoc.
\newblock In \emph{POPL}, pages 60--76. ACM, 1989.

\bibitem[Weirich et~al.(2013)Weirich, Hsu, and Eisenberg]{Weirich13}
S.~Weirich, J.~Hsu, and R.~A. Eisenberg.
\newblock Towards dependently typed {Haskell}: {System FC} with kind equality.
\newblock In \emph{ICFP}. ACM, 2013.

\bibitem[Yorgey et~al.(2012)Yorgey, Weirich, Cretin, {Peyton Jones},
  Vytiniotis, and Magalh{\~a}es]{YorgeyWCJVM12}
B.~A. Yorgey, S.~Weirich, J.~Cretin, S.~L. {Peyton Jones}, D.~Vytiniotis, and
  J.~P. Magalh{\~a}es.
\newblock Giving {H}askell a promotion.
\newblock In \emph{TLDI}, pages 53--66. ACM, 2012.

\end{thebibliography}


%% \bibliographystyle{abbrvnat}

%% \bibliography{hasochism}

% The bibliography should be embedded for final submission.

%% \begin{thebibliography}{}
%% \softraggedright

%% \bibitem[Smith et~al.(2009)Smith, Jones]{smith02}
%% P. Q. Smith, and X. Y. Jones. ...reference text...

%% \end{thebibliography}

\end{document}

%%  LocalWords:  Haskell Lindley Strathclyde Conor Haskell's Hindley
%%  LocalWords:  Milner tilings prover Agda Milner's Coq's kinded GHC
%%  LocalWords:  preprocessor systematized polymorphism minimizing EP
%%  LocalWords:  invariants GADTs GHC's compositional WNat scalable
%%  LocalWords:  preventably generalizing unduplicated hasochism Jos
%%  LocalWords:  EPSRC Peyton Weirich Eisenberg Iavor Diatchki Magalh
%%  LocalWords:  Dimitrios Vytiniotis Gundry
