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
\[\begin{array}{||l||||r||l||}
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

Meanwhile, Haskell's type classes demonstrate the value of dynamic
components which are none the less implicit---instance
dictionaries. Indeed, type inference seems a timid virtue once you
glimpse the prospect of \emph{program} inference, yet some are made
nervous by the prospect of unwritten programs being run. Similarly,
Haskell's combination of higher kinds and constraints means that
sometimes static types must be given explicitly, in order not only to
check them, but also to drive the generation of invisible boilerplate.


\todo{mention promotion~\cite{YorgeyWCJVM12}}

\todo{cite SHE~\cite{she} and \singletons library~\cite{EisenbergW12}}

\todo{mention ``The right kind of generic programming''
  \cite{Magalhaes12}}

\todo{Conor to work in motivations / contributions}

Motivations:
\begin{itemize}
\item For everyone. Dependent types. More precise types $\Rightarrow$ stronger
  static guaranteees $\Rightarrow$ more reliable programs.

\item For Haskell programmers. Explore techniques for practical
  dependently typed Haskell programming.

\item For compiler implementors. Identify improvements in light of
  hasochism.
\end{itemize}

Contributions:

\begin{itemize}
\item Comparison between Agda-style dependently typed programming and
  dependently typed programming in Haskell

\item Practical techniques for dependently typed programming in
  Haskell

\item MergeSort example

\item An algebra of size-indexed boxes including editor example
\end{itemize}

The rest of the paper is structured as follows...

\section{A Variety of Quantifiers}
\label{sec:natvec}
%include NatVec.lhs

\section{Explicit and Implicit $\Pi$-Types}
\label{sec:pies}

\todo{Cite ``Applicative programming with effects''~\cite{McbrideP08}
  somewhere in this section.}

%include Pies.lhs

\subsection{The NATTY-in-Natty Question}

%include NATTYInNatty.lhs

%% \section{Existentials}

%% %include Existentials.lhs

\section{Classes-as-relations --- silence is golden}
\label{sec:merge-sort}

%include MergeSort.lhs

\section{Evidence is data and proof}
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
