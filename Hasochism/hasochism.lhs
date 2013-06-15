\documentclass[preprint]{sigplanconf}


% US Letter page size
%\pdfpagewidth=8.5in
%\pdfpageheight=11in

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

%format EXISTS = "\exists\!"
%format DOT = "\!\!.\!\!"

%format BAD = "\hfill(\times)"

%format show = "\F{show}"

\newcommand{\F}{\mathsf}

\renewcommand{\hscodestyle}{\small}

\newcommand\todo[1]{\textbf{TODO: }{#1}}


\usepackage{amsmath}
\usepackage{xspace}
\usepackage{url}

\newcommand{\singletons}{\textsf{singletons}\xspace}

\begin{document}

\conferenceinfo{Name}{Date, Address} 
\copyrightyear{Year} 
\copyrightdata{[to be supplied]} 

%% \titlebanner{banner above paper title}        % These are ignored unless
%% \preprintfooter{short description of paper}   % 'preprint' option specified.

\title{Hasochism}
\subtitle{The Pleasure and Pain of Dependently Typed Haskell Programming}

\authorinfo{Sam Lindley}
           {University of Strathclyde}
           {sam.lindley@@strath.ac.uk}
\authorinfo{Conor McBride}
           {University of Strathclyde}
           {conor.mcbride@@strath.ac.uk}

\maketitle

\begin{abstract}
Haskell's type system has outgrown its Hindley-Milner roots to the extent that it
now stretches to the basics of dependently typed programming. In this paper, we
collate and classify techniques for programming with dependent types in Haskell,
and contribute some new ones. In particular, through extended examples ---
merge sort and rectangular tilings --- we show how to exploit Haskell's constraint
solver as a theorem prover, delivering code which, as Agda programmers, we envy.
We explore the compromises involved in simulating variations on the theme of the
dependent function space in an attempt to help programmers put dependent
types to work, and to inform the evolving language design both of Haskell and of
dependently typed languages more broadly.
\end{abstract}

%% \category{CR-number}{subcategory}{third-level}

%% \terms
%% term1, term2

%% \keywords
%% keyword1, keyword2

\section{Introduction}
\label{sec:intro}

In the design of Standard ML, Milner and his colleagues achieved a remarkable
alignment of distinctions:
~\cite{Milner78,ML}\[\begin{array}{||l||||r||l||}
\hline
\textrm{syntactic category}  & \textbf{terms}      &     \textbf{types} \\
\textrm{phase distinction}   & \textbf{dynamic}    &    \textbf{static} \\
\textrm{inference}           & \textbf{explicit}   &  \textbf{implicit} \\
\textrm{abstraction}         & \textbf{simple}     & \textbf{dependent} \\
\hline
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
types. What counts as a `type' has begun to stretch. Our
\emph{Strathclyde Haskell Enhancement} preprocessor~\cite{she},
systematized and sugared common constructions for building the type
level analogues of run time data, together with run time witnesses to
type level values, allowing something which was made to look like a
dependent quantifier for explicit abstraction over dynamic terms---the
$\Pi$-type of dependent type theory---in domains simple enough to
admit the singleton construction. Before long, Glasgow Haskell
headquarters responded with a proper kind system for `promoted' data
types~\cite{YorgeyWCJVM12}, making possible the \singletons
library~\cite{EisenbergW12}. The arrival of data types at the kind
level necessitated polymorphism in kinds: Haskell is now a dependently
\emph{kinded} language, and although it is a nuisance that the
kind-level $\forall$ is compulsorily implicit, the fresh abstractions
it offers have yielded considerable simplification, e.g., in support
of generic programming~\cite{Magalhaes12}.

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
Section~\ref{sec:natvec} explores variation in forms of dependent Section~\ref{sec:pies}... Section~\ref{sec:merge-sort}...
Section~\ref{sec:evidence}... Section~\ref{sec:boxes} introduces an
algebra of size-indexed boxes, which is used to build a text editor in
Section~\ref{sec:editor}. Section~\ref{sec:conclusion} concludes.

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

\section{Evidence Combining Data with Proof}
\label{sec:evidence}

%include Evidence.lhs

\section{Boxes}
\label{sec:boxes}

%include BoxPain.lhs

%include BoxPleasure.lhs

\section{An editor}
\label{sec:editor}

%include Editor.lhs

\section{Conclusion}
\label{sec:conclusion}

The best thing about banging your head off a brick wall is \emph{stopping}.

\newpage


%% \appendix
%% \section{Appendix Title}

%% This is the text of the appendix, if you need one.

%% \acks

%% Acknowledgments, if needed.

% We recommend abbrvnat bibliography style.

\bibliographystyle{abbrvnat}

\bibliography{hasochism}

% The bibliography should be embedded for final submission.

%% \begin{thebibliography}{}
%% \softraggedright

%% \bibitem[Smith et~al.(2009)Smith, Jones]{smith02}
%% P. Q. Smith, and X. Y. Jones. ...reference text...

%% \end{thebibliography}

\end{document}
