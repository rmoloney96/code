\documentclass[preprint,10pt]{llncs}

\usepackage{empheq}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{bussproofs}
\usepackage{graphicx} 
%\usepackage{tikz}
\usepackage{tabularx}
\usepackage{alltt} 
\usepackage{dsfont}
\usepackage[svgnames]{xcolor} 

%% To compile - run lagda


% \newenvironment{definition}[1][Definition]{\begin{trivlist}
% \item[\hskip \labelsep {\bfseries #1}]}{\end{trivlist}}
% \newenvironment{example}[1][Example]{\begin{trivlist}
% \item[\hskip \labelsep {\bfseries #1}]}{\end{trivlist}}
% \newenvironment{remark}[1][Remark]{\begin{trivlist}
% \item[\hskip \labelsep {\bfseries #1}]}{\end{trivlist}}

\include{syntax}

%include agda.fmt

\include{title}

\begin{document}

  \maketitle 
  
  \begin{abstract} 

  Proofs involving infinite structures can use corecursive functions
  as inhabitants of a corecursive type.  Admissibility of such
  functions in theorem provers such as Coq or Agda, requires that
  these functions are productive.  Typically this is proved by showing
  satisfaction of a guardedness condition.  The guardedness condition
  however is extremely restrictive and many programs which are in fact
  productive and therefore will not compromise soundness are
  nonetheless rejected.  Supercompilation is a family of program
  transformations which retain program equivalence.  Using
  supercompilation we can take programs whose productivity is
  suspected and transform them into programs for which guardedness is
  syntactically apparent.

  \end{abstract}

\section{Introduction} 
The Curry-Howard correspondence lets us take advantage of a close
correspondence between programs and proofs.  The idea is that
inhabitation of a type is given by demonstration of a type correct
program having that type.  In the traditional Curry-Howard regime type
inhabitation is given with terminating programs.  This requirement
avoids the difficulty that non-terminating programs might allow
unsound propositions to be proved.

This was extended by Coquand \cite{coquand1994infinite} to include
potentially infinite structures.  The notions of co-induction and
co-recursion allow infinite structures and infinite proofs to be
introduced without loss of soundness.

In the Agda and Coq theorem provers, the guardedness condition is the
condition checked to ensure admissibility of coinductive programs.
This condition ensures that the function is {\em productive} in the
sense that it will always produce a new constructor finitely.  The
guardedness condition has the advantage of only requiring a syntactic
check on the form of the program and is a sufficient condition for
productivity.  However, it suffers from being highly restrictive and
rejects many programs which {\em are} in fact productive.  Requiring
guards is a rather rigid approach to ensuring productivity.

The purpose of this paper is to suggest that theorem provers can use a
notion of pre-proofs\cite{BROTHERSTON05}, proofs for which the side
conditions which ensure soundness have not been demonstrated, which
can be transformed into a genuine proof using equational reasoning.
The main idea is that, if a program is type-correct after program
transformation using equational reasoning, it was correct prior to
transformation.  This was the main idea behind the paper by Danielsson
et al. \cite{danielsson06fastand}.

The approach has a number of advantages over the traditional syntactic
check or ad-hoc methods of extending the guardedness condition to
some larger class.  The number of programs which might be accepted
automatically can be increased simply by using automated program
transformers.  All but one of the examples given in this paper were
found by way of the supercompilation program transformation algorithm.
The approach also allows one to keep the chain of equational reasoning
present, allowing an audit trail of correctness.

This paper is structured as follows.  First we will present a number
of motivating examples.  We will give a bird's-eye view of
supercompilation followed by a description of cyclic proof and
transformations in this framework.  We will give a demonstration of
how one of the motivating examples can be transformed in this
framework.  Finally we will end with some possibilities for future
development.

\section{Examples}
 
In order to motivate program transformation as a means for showing
type inhabitation, we present a number of examples in the language
Agda.  First, we would like to work with the natural numbers which
include the point at infinity.  This we write as the codata
declaration with the familiar constructors of the Peano numbers.  We
also define the analogous codata for lists, allowing infinite streams.

%format Set = "{\color{Blue} Set }"
%format CoNat = "{\color{Blue} \mathbb{N}^{\infty} }"
%format CoList = "{\color{Blue} CoList }"
%format czero = "{\color{Purple} czero }"
%format csucc = "{\color{Purple} csucc }"
%format :: = "{\color{Purple} :: }"
\begin{code}
module Productive where

codata CoNat : Set where 
  czero : CoNat
  csucc : CoNat -> CoNat

codata CoList (A : Set) : Set where 
  [] : CoList A
  _::_ : A -> CoList A -> CoList A

infixr 40 _+_
_+_ : CoNat -> CoNat -> CoNat
czero     + y = y 
(csucc x) + y = csucc (x + y)

sumlen : CoList CoNat -> CoNat
sumlen []        = czero 
sumlen (x :: xs) = csucc (x + (sumlen xs))
\end{code}

When attempting to enter this program into a theorem prover, such as
Coq or Agda, the type checker will point out that this program does
not meet the guardedness condition.  This is due to the fact that
there is an intermediate application (of $+$) which might consume any
constructors which {\em sumlen} produces.  However, the program is in
fact productive and no such problem occurs in practice.  This becomes
evident after supercompiling the above term, where we arrive at the
following transformed term:

\begin{code}
mutual 
  sumlen_sc : CoList CoNat -> CoNat
  sumlen_sc []        = czero 
  sumlen_sc (x :: xs) = csucc (aux x xs) 
  
  aux : CoNat -> CoList CoNat -> CoNat
  aux czero     xs = sumlen_sc xs 
  aux (csucc x) xs = csucc (aux x xs)
\end{code}

This term will now be accepted by Agda's type checker.  We see that
we have basically unrolled the intermediate implication eliminations.
We will look more closely at this later in Section~\ref{sec:cyclic}.

In the above example we managed to remove some intermediate
applications for two functions which were both productive.  We can
also find similar results however by unrolling intermediate inductive
steps.  The following example, given by Komendaskaya and Bertot
\cite{bertot2008inductive}, relies on this {\em always eventually}
type behaviour.  That is, behaviour that will {\em always} be
productive, {\em eventually} after some finite process.  Here the
finite process is guaranteed by the inductive character of the natural
numbers.

%format Bool = "{\color{Blue} Bool }"
%format Stream = "{\color{Blue} Stream }"
%format Nat = "{\color{Blue} \mathbb{N} }"
%format zero = "{\color{Green} zero }"
%format succ = "{\color{Green} succ }"
%format true = "{\color{Green} true }"
%format false = "{\color{Green} false }"
\begin{code}
data Bool : Set where 
  true : Bool 
  false : Bool 

data Nat : Set where 
  zero : Nat 
  succ : Nat -> Nat

infix 5 if_then_else_
if_then_else_ : { A : Set } -> Bool -> 
                  A -> A -> A
if true then x else y = x
if false then x else y = y
infixr 40 _::_
codata Stream (A : Set) : Set where 
  _::_ : A -> Stream A -> Stream A
le : Nat -> Nat -> Bool 
le zero _ = true 
le _ zero = false 
le (succ x) (succ y) = le x y

pred : Nat -> Nat
pred zero = zero 
pred (succ x) = x

f : Stream Nat -> Stream Nat
f (x :: y :: xs) = if (le x y)
                   then (x :: (f (y :: xs)))
                   else (f ((pred x) :: y :: xs))
\end{code}

Again we have the problem that the type checker is unable to accept
$f$ as being productive as the else clause makes an unguarded call to
$f$ though the function is productive as we structurally descend on
the argument $x$ which is inductively defined.  However, after
supercompilation we arrive at the following program.

\begin{code}
mutual 
  f_sc : Stream Nat -> Stream Nat 
  f_sc (zero   :: y      :: xs) = zero :: (f_sc (y :: xs))
  f_sc (succ x :: zero   :: xs) = g x xs
  f_sc (succ x :: succ y :: xs) with le x y 
  ...                           | true  = (succ x) :: (f_sc ((succ y) :: xs))
  ...                           | false = h x y xs

  g : Nat -> Stream Nat -> Stream Nat
  g zero xs = zero :: (f_sc (zero :: xs))
  g (succ x) xs = g x xs

  h : Nat -> Nat -> Stream Nat -> Stream Nat
  h zero     y xs = zero :: (f_sc ((succ y) :: xs))
  h (succ x) y xs with le x y
  ...             | true  = (succ x)::(f_sc ((succ y) :: xs))
  ...             | false = h x y xs
\end{code}

Now we have a program which passes Agda's type checker.  The
intermediate computations have been turned into inductive loops and
the coinductive function now exhibits a guarded call.

With these motivating examples in hand, we would like to look a bit at
the method of program transformation which is used to produce these
final programs which are now acceptable by our type checker.

\section{Language}

The language we present is a functional programming language, which we
will call $\Lambda_{F}$ with a type system based on System $F$ with
recursive types.  The use of System $F$ typing allows us to ensure
that transitions can be found for any term.  Our term language will
follow closely on the one used by Abel \cite{DBLP:conf/csl/Abel09}.

\begin{figure}[htbp!]
  \input{grammar}
  \label{tab:language}
  \caption{Language}
\end{figure} 

In Figure~\ref{tab:language} we describe the syntax of the language.
The set $\set{TyCtx}$ describes {\em type variable contexts} which
holds the free type variables in a context.  The set $\set{Ctx}$
describes {\em variable contexts} which holds information about free
term variables, and what type they have.  The empty context is denoted
$\cdot$, and we extend contexts with variables of a type, or a type
variable using $\cup$.  The contexts are assumed to be sets.
 
The unit type is denoted $\one$ and is established as the type of the
unit term $\unit$.  Functions types, which are the result of a term
$\lam{x}{A}{t}$ where $t$ has type $B$ are given using $A \imp B$.
The type of a type abstraction $\Lam{X}{t}$ is given with the syntax
$\Forall{X}{A}$ in which the type variable $X$ may be present in the
type $A$ and the term $t$.  Sum types allow a term of one of two
types, $A$ and $B$, to be injected into a third type $A+B$.  We can
inject into this sum for terms of type $A$ using the left injection:
$\inl{t}{A+B}$ or for terms of type $B$ on the right using
$\inr{s}{A+B}$.  The pair type $A\times B$ is introduced with a
pairing term $(s,t)$ where $s$ has type $A$ and $t$ has type $B$.  We
introduce inductive types $\Mu{X}{A}$ with the term
$\foldmu{t}{\Mu{X}{A}}$.  Similarly for coinductive types $\Nu{X}{A}$
we introduce the term $\foldnu{t}{\Nu{X}{A}}$.  Similarly each type
(save for unit) is equiped with an elimination term, whose meaning
will be clear from the dynamic semantics.

Types are introduced by way of type formation rules such that a type
$A$ is well formed if we can derive $\tyformseq{\Delta}{A}$.  These
rules ensure that only types which are strictly positive in $\mu$ and
$\nu$ type variables are allowed, while universally quanitifed
variables are unrestricted.  This is achieved by segregating the type
variables introduced using $\nu$ and $\mu$ using a hat above the type
variable, $\pos{X}$.

\begin{figure}[htbp!]\small
    {\bf Term Substitution}\\
    \begin{tabular}{l l l}
      \hline\\
      $x [x:=t]$ & $\equiv$ & $t$ \\ 
      $x [y:=t]$ & $\equiv$ & $x$ if $x\neq y$ \\ 
      $\fun{f} [x:=t]$ & $\equiv$ & $\fun{f}$ \\
      $(r\;s) [x:=t]$ & $\equiv$ & $(r[x:=t])\;(s[x:=t])$ \\
      $(\lam{y}{A}{r})[x:=t]$ & $\equiv$ & $\lam{y}{A}{r[x:=t]}$ \\ 
      &            & Provided that $\lam{y}{A}{r}$ is $\alpha$-converted to use \\
      &            & a fresh variable if $y \in \s{x}\cup FV(t)$.\\
      $(\Lam{X}{r})[x:=t]$ & $\equiv$ & $\Lam{X}{r[x:=t]}$ \\ 
      $\foldalpha{s}{A}[x:=t]$ & $\equiv$ & $\foldalpha{s[x:=t]}{A}$\\
      $\unfoldalpha{s}{A}[x:=t]$ & $\equiv$ & $\unfoldalpha{s[x:=t]}{A}$\\
      $()[x:=t]$ & $\equiv$ & $()$\\
      $\inr{s}{A}[x:=t]$ & $\equiv$ & $\inr{s[x:=t]}{A}$ \\
      $\inl{s}{A}[x:=t]$ & $\equiv$ & $\inl{s[x:=t]}{A}$ \\
      $(s,u)[x:=t]$ & $\equiv$ & $(s[x:=t],u[x:=t])$ \\
      $\cas{r}{y}{s}{z}{u}[x:=t]$ & $\equiv$ & $\cas{r[x:=t]}{y}{s[x:=t]}{z}{u[x:=t]}$ \\
      &            & Provided that $\lam{y}{A}{s}$ or $\lam{z}{A}{u}$ \\ 
      &            & are $\alpha$-converted to use a fresh variable\\ 
      &            & if $y \in \s{x}\cup FV(t)$ \\
      &            & or $z \in \s{x}\cup FV(t)$ respectively.\\
      $\spit{r}{(y,z)}{u}[x:=t]$ & $\equiv$ & $\spit{r[x:=t]}{(y,z)}{u[x:=t]}$ \\
      &            & Provided that $\lam{y}{A}{\lam{z}{A}{u}}$ is \\ 
      &            & $\alpha$-converted to use a fresh variable for $y$ or $z$ \\
      &            & if $y \in \s{x}\cup FV(t)$\\
      &            & or $z \in \s{x}\cup FV(t)$ respectively.\\
    \end{tabular}
    \caption{Term Substitution}
    \label{table:term_substitution}
\end{figure}

\begin{figure}[htbp!]\small
    {\bf Type Substitution on Terms}\\  
    \begin{tabular}{l l l}
      \hline\\
      $x [X := A]$ & $\equiv$ & $x$\\
      $\fun{f} [X := A]$ & $\equiv$ & $\fun{f}$\\
      $\unit [X := A]$ & $\equiv$ & $()$\\
      $(\app{r}{s}) [X:=A]$ & $\equiv$ & $(r[X:=A])\;(s[X:=A])$\\
      $(\tapp{r}{A}) [X:=A]$ & $\equiv$ & $(r[X:=A])\;(A[X:=A])$\\
      $(\lam{x}{A}{r[X:=A]}$ & $\equiv$ & $\lam{x}{A[X:=A]}{r[X:=A]}$\\
      $\foldalpha{s}{B}[X:=A]$ & $\equiv$ & $\foldalpha{s[X:=A]}{B[X:=A]}$\\
      $\unfoldalpha{s}{B}[X:=A]$ & $\equiv$ & $\unfoldalpha{s[X:=A]}{B[X:=A]}$\\
      $\inr{s}{B}[X:=A]$ & $\equiv$ & $\inr{s[X:=A]}{B[X:=A]}$ \\
      $\inl{s}{B}[X:=A]$ & $\equiv$ & $\inl{s[X:=A]}{B[X:=A]}$ \\
      $(s,u)[X:=A]$ & $\equiv$ & $(s[X:=A],u[X:=A])$ \\
      $(\cas{r}{y}{s}{z}{u})[X:=A]$ & $\equiv$ & $\caslines{r[X:=A]}{y}{s[X:=A]}{z}{u[X:=A]}$ \\
      $(\spit{r}{(y,z)}{u})[X:=A]$ & $\equiv$ & $\spit{r[X:=A]}{(y,z)}{u[X:=A]}$ \\
    \end{tabular}\\\\
    {\bf Type Substitution on Types}\\  
    \begin{tabular}{l l l}
      \hline\\      
      $X [X := A]$ & $\equiv$ & $A$\\
      $X [Y := A]$ & $\equiv$ & $X$ if $X\neq Y$\\
      $\one [X := A]$ & $\equiv$ & $\one$\\
      $B+C [X := A]$ & $\equiv$ & $B [X:=A] + C[X:=A]$\\
      $B\times C [X := A]$ & $\equiv$ & $B [X:= A] \times C [X:=A]$\\
      $(B \imp C)[X:=A]$ & $\equiv$ & $B[X:=A] \imp C[X:=A]$\\
      $(\Forall{Y}{B})[X:=A]$ & $\equiv$ & $\Forall{Y}{B[X:=A]}$ \\
      &            & Provided that $(\Forall{Y}{B})$ is $\alpha$-converted to use \\
      &            & a fresh type-variable if $Y \in \s{X} \cup FV(A)$.\\
      $(\Lam{Y}{r})[X:=A]$ & $\equiv$ & $\Lam{Y}{r[X:=A]}$\\
      &            & Provided that $(\Lam{Y}{r})$ is $\alpha$-converted to use \\
      &            & a fresh type-variable if $Y \in \s{X} \cup FV(A)$.\\
      $(\Quant{\alpha}{Y}{r})[X:=A]$ & $\equiv$ & $\Quant{\alpha}{Y}{r[X:=A]}$, $\alpha \in \{\nu \com \mu \}$\\
      &            & Provided that $(\Quant{\alpha}{Y}{r})$ is $\alpha$-converted to use \\
      &            & a fresh type-variable if $Y \in \s{X} \cup FV(A)$.\\
    \end{tabular}
  \caption{Type Substitution}
 \label{table:type_substitution}
\end{figure}

% \begin{figure} 
% %%  \include{substitution}

%   \begin{tabular}{l l l}
%     {\bf Terms into terms}\\
%     \hline
%     $x [x := t]$ & $\equiv$ & $t$\\
%     $x [y := t]$ & $\equiv$ & $x$ if $x\neq y$\\
%     $(\lam{y}{A}{s}) [x :=t]$ & $\equiv$ & $\lam{y'}{A}{s'[x:=t]}$ \\
%     & & Where $y' = \fresh{\s{x} \cup \fv{t}}$ and $s' = s[y:=y']$. \\
%   \end{tabular}
% \\
%   \begin{tabular}{l l l}
%     $(\Lam{X}{s}) [x :=t] $ & $\equiv$ & $\Lambda X . s[x:=t]$\\
%     & & Where $X' = \fresh{\s{X}\cup \fv{t}}$ and $s' = s[X:=X']$. \\
%     $\inl{s}{A}[x :=t]$ & $\equiv$ & $\inl{s[x:=t]}{A}$ \\
%     $\inr{s}{A}[x :=t]$ & $\equiv$ & $\inr{s[x:=t]}{A}$ \\
%     $(s,t)[x :=u]$ & $\equiv$ & $(s[x:=u],t[x:=u])$ \\
%     $\unfoldalpha{s}{A}[x:=t]$& $\equiv$ & $\unfoldalpha{s[x:=t]}{A}$ \\
%     $\foldalpha{s}{A}[x:=t]$& $\equiv$ & $\foldalpha{s[x:=t]}{A}$ \\
%     &          & $\alpha \in \s{\mu,\nu}$\\
%   \end{tabular}
% \\
%   \begin{tabular}{l l}
%     $\spit{s}{(y,z)}{u}[x:=t]$& $\equiv$ \\
%   \end{tabular}\\
%   \begin{tabular}{c} 
%     $\;\;\;\spit{s[x:=t]}{(y,z)}{u[x:=t]}$\\
%   \end{tabular}\\
%   \begin{tabular}{l l}
%     $\cas{r}{y}{s}{z}{u}[x:=t]$& $\equiv$   \\
%   \end{tabular}\\
%   \begin{tabular}{l}
%     $\;\;\;\text{case}\;r[x:=t]\;\text{of}$ \\ 
%     $\;\;\;\;\;\;y\;\Rightarrow\; s[x:=t]\;||\;z\;\Rightarrow\;u[x:=t]$ \\\\
%   \end{tabular}\\

%   \begin{tabular}{l l l}
%     {\bf Types into types}\\
%     \hline
%     $X [X := A]$ & $\equiv$ & $A$\\
%     $X [Y := A]$ & $\equiv$ & $X$ if $X\neq Y$\\
%     $(A \imp B)[X:=C]$ & $\equiv$ & $A[X:=B] \imp A[X:=C]$\\
%     $(\forall Y . A)[X:=B]$ & $\equiv$ & $\forall Y' . A'[X:=B]$\\
%     & & Where $Y' = \fresh{\s{X}\cup \fv{B}}$ and $A' = A[Y:=Y']$. \\
%     $x [X := A]$ & $\equiv$ & $x$\\
%   \end{tabular}
%   \\
%   \begin{tabular}{l l l}
%     {\bf Types into terms}\\
%     \hline
%     $(\lam{x}{A}{r})[X:=B]$ & $\equiv$ & $\lam{x}{A[X:=B]}{r[X:=B]}$\\
%     $(\Lam{Y}{r})[X:=A]$ & $\equiv$ & $\Lambda Y. r[X:=A]$\\
%     & & Where $Y' = \fresh{\s{X}\cup \fv{B}}$ and $A' = A[Y:=Y']$. \\
%   \end{tabular}\\
%   \begin{tabular}{l l l}
%     $(\app{r}{s}) [X:=A]$ & $\equiv$ & $(r[X:=A])\;(s[X:=A])$\\
%     $(\tapp{r}{B}) [X:=A]$ & $\equiv$ & $\tapp{(r[X:=A])}{(B[X:=A])}$\\    
%   \end{tabular}

%   \caption{Substitution}
%   \label{table:substitution}
% \end{figure}


We describe {\em substitutions} which use a function $\fv{t}$ to
obtain the free type and term variables from a term.  We also choose
free variables to be {\em fresh}, meaning they are chosen from some
denumerable set such that they are not present in a given set of
variables.  A variable chosen in this way we will write as $x =
\fresh{S}$ if it is {\em fresh} with respect to the set $S$.
Substitutions of a single variable will be written $[X := A]$ or $[x
:= t]$ for type and term variables respectively.  The full operational
meaning of substitutions is given in Figure~\ref{table:term_substitution} and Figure~\ref{table:type_substitution}.

% \begin{figure}\small
%   \begin{center}
%     \begin{tabular}{c c} 
%       $\app{(\lam{x}{A}{r})}{s} \leadsto r[x:=s]$ & 
%       $\tapp{(\Lam{X}{r})}{A} \leadsto r[X:=A]$ \\\\
%     \end{tabular}\\
%     \begin{tabular}{c}
%       $\cas{(\inl{r}{A+B})}{x}{s}{y}{t} \leadsto s[x:=r]$ \\\\
%       $\cas{(\inr{r}{A+B})}{x}{s}{y}{t} \leadsto t[y:=r]$ \\\\
%       $\spit{(r,s)}{(x,y)}{t} \leadsto t[x:=r][y:=s]$ \\\\
%       $\unfoldalpha{\foldalpha{r}{U}}{U} \leadsto r$ \\\\
%     \end{tabular} \\
%     \begin{tabular}{c c c}
%       { \AxiomC{$r \leadsto r'$}
%         \UnaryInfC{$\app{r}{s} \leadsto \app{r'}{s}$} 
%         \DisplayProof} &
%       { \AxiomC{$r \leadsto r'$}
%         \UnaryInfC{$\tapp{r}{A} \leadsto \tapp{r'}{A}$} 
%         \DisplayProof} & 
%       { \AxiomC{$r \leadsto r'$} 
%         \UnaryInfC{$\unfoldalpha{r}{U} \leadsto \unfoldalpha{r'}{U}$} 
%         \DisplayProof}\\\\    
%     \end{tabular} \\
%     \begin{tabular}{c}
%       { \AxiomC{$r \leadsto r'$}
%         \UnaryInfC{$\cas{r}{x}{s}{y}{t} \leadsto \cas{r'}{x}{s}{y}{t}$}
%         \DisplayProof} \\\\
%       { \AxiomC{$r \leadsto r'$}
%         \UnaryInfC{$\spit{r}{(x,y)}{t} \leadsto \spit{r'}{(x,y)}{t}$}
%         \DisplayProof} \\\\ 
%     \end{tabular}\\
%     \begin{tabular}{c} 
%       { 
%         \AxiomC{$f \leadsto_\Prog \Prog(f)$}
%       \DisplayProof}\\\\
%     \end{tabular}
%     \end{center}
%   \label{table:evaluation}
%   \caption{Evaluation}
% \end{figure}


\begin{figure}[htbp!]\small
    {\bf Reduction Rules}\\  
    \begin{tabular}{l l} 
      \hline\\
      $(\lambda x:A.r)\;s \evalone r[x:=s]$ & 
      $(\Lambda X.r)\;A \evalone r[X:=A]$ \\\\
      $\unfoldalpha{\foldalpha{r}{U}}{U} \evalone r$ &       
      { \AxiomC{$\fun{f} \evalf \Prog(\fun{f})$} \DisplayProof} \\\\
    \end{tabular}\\
    \begin{tabular}{l}
      $\cas{\inl{r}{A+B}}{x}{s}{y}{t} \evalone s[x:=r]$ \\\\
      $\cas{\inr{r}{A+B}}{x}{s}{y}{t} \evalone t[y:=r]$ \\\\
      $\spit{(r,s)}{(x,y)}{t} \evalone t[x:=r][y:=s]$ \\\\
    \end{tabular}\\
    {\bf Structural Rules}\\
    \begin{tabular}{l l l l}
      \hline\\
      { \AxiomC{$r \rel{R} r'$}
        \UnaryInfC{$r \reltag{R}{s} r'$} 
        \DisplayProof} &
      { \AxiomC{$r \reltag{R}{s} r'$}
        \UnaryInfC{$r\;s \reltag{R}{s} r'\;s$} 
        \DisplayProof} &
      { \AxiomC{$r \reltag{R}{s} r'$}
        \UnaryInfC{$r\;A \reltag{R}{s} r'\;A$} 
        \DisplayProof} & 
      { \AxiomC{$r \reltag{R}{s} r'$} 
        \UnaryInfC{$\unfoldalpha{r}{U} \reltag{R}{s} \unfoldalpha{r'}{U}$} 
        \DisplayProof}\\\\
    \end{tabular} \\
    \begin{tabular}{l}
      { \AxiomC{$r \reltag{R}{s} r'$}
        \UnaryInfC{$\cas{r}{x}{s}{y}{t} \reltag{R}{s} \cas{r'}{x}{s}{y}{t}$}
        \DisplayProof} \\\\
      { \AxiomC{$r \reltag{R}{s} r'$}
        \UnaryInfC{$\spit{r}{(x,y)}{t} \reltag{R}{s} \spit{r'}{(x,y)}{t}$}
        \DisplayProof} \\\\ 
    \end{tabular}\\
    {\bf Evaluation Relations}\\
    \begin{tabular}{l c l}
      \hline\\
      $r \evaln s$ & $::=$ & $r \;\evalone^{s}\; s$\\
      $r \eval s$ & $::=$ & $r \;\evalf^{s}\; s \vee r \evaln s$\\
      $r\;R^+\;s$ & $::=$ & $r\;R\;s \vee (\exists r'. r\;R\;r' \wedge r'\;R^+\;s)$\\
      $r\;R^*\;s$ & $::=$ & $r = s \vee r\;R^+\;s$\\
%      $r \Downarrow s $ & $::=$ & $r \eval^* s \wedge s \in \Value$ \\
%      $r \Downarrow$ & $::=$ & $\exists s. r \Downarrow s$\\
%      $r \Uparrow$ & $::=$ & $\exists s. r \leadsto s \wedge s \Uparrow$\\
\end{tabular}

  \caption{Evaluation}
  \label{table:evaluation}
\end{figure}

We define the evaluation relation $\leadsto$ in
Figure~\ref{table:evaluation}.  This relation is the usual normal
order evaluation relation.  It is deterministic and so there is always
a unique redex.  We take the transitive closure of the relation to be
$\eval^{*}$.

We introduce recursive terms by way of function constants.  Although
it is possible to encoded these directly in System F, it simplifies
the presentation to provide them explicitly.  Function constants are
drawn from a set $\set{Fun}$.  We couple our terms with a function
$\Prog$ which associates a function constant $f$ with a term $t$,
$\Prog(f)=t$, where $t$ may itself contain any function constants in
the domain of $\Prog$.  We make use of this function in the $\eval$
relation which allows us to unfold recursively defined functions.

For a term $t$ with type $A$ in a context $\Delta ; \Gamma$ we write
$\tyseq{\Delta}{\Gamma}{t}{A}$.  A type derivation must be given using
the rules given in Figure~\ref{tab:systemfproof}.

\begin{figure}[!htbp]\small
\begin{center}
  \begin{tabular}{l l}
    { \AxiomC{$\Delta \vdash \ctx{\ext{\Gamma}{x}{A}}$}
      \RightLabel{$\VarIntro$}
      \UnaryInfC{$\tyseq{\Delta}{\ext{\Gamma}{x}{A}}{x}{A}$}
      \DisplayProof
    }
    &
    { 
      \AxiomC{\vphantom{$\{\}$}} 
      \RightLabel{$\UnitIntro$}
      \UnaryInfC{$\tyseq{\Delta}{\Gamma}{ \unit }{ \one }$} 
      \DisplayProof
    } 
    \\\\
    { 
      \AxiomC{$\tyseq{\tyext{\Delta}{X}}{\Gamma}{t}{A}$}
      \RightLabel{$\AllIntro$}
      \UnaryInfC{$\tyseq{\Delta}{\Gamma}{(\Lam{X}{t})}{\Forall{X}{A}}$}
      \DisplayProof
    }      
    &
    { 
      \AxiomC{$\tyseq{\Delta}{\Gamma}{t}{ \Forall{X}{A} }$}
        \AxiomC{$\tyformseq{\Delta}{B}$}
      \RightLabel{$\AllElim$}
      \BinaryInfC{$\tyseq{\Delta}{\Gamma}{ \tapp{t}{B} }{ A [X := B] }$}
      \DisplayProof
    }\\\\
    {      
      \AxiomC{$\tyseq{\Delta}{\ext{\Gamma}{x}{A}}{t}{B}$} 
      \RightLabel{$\ImpIntro$}
      \UnaryInfC{$\tyseq{\Delta}{\Gamma}{(\lam{x}{A}{t})}{A \imp B}$}
      \DisplayProof
    }
    &
    { 
      \AxiomC{$\tyseq{\Delta}{\Gamma}{r}{A \imp B}$}
      \AxiomC{$\tyseq{\Delta}{\Gamma}{s}{A}$}
      \RightLabel{$\ImpElim$}
      \BinaryInfC{$\tyseq{\Delta}{\Gamma}{(\app{r}{s})}{B}$}
      \DisplayProof
    }
    \\\\
    { 
      \AxiomC{$\Gamma \vdash \Prog(f) : A$}
      \RightLabel{$\FunIntro$}
      \UnaryInfC{$\tyseq{\Delta}{\Gamma}{f}{A} $}
      \DisplayProof
    }
    &
    { 
      \AxiomC{$\tyseq{\Delta}{\Gamma}{ r }{ A }$}
        \AxiomC{$\tyseq{\Delta}{\Gamma}{ s }{ B }$}
      \RightLabel{$\AndIntro$}
      \BinaryInfC{$\tyseq{\Delta}{\Gamma}{ (r,s) }{ (A \times B) }$}
      \DisplayProof
    } 
    \\\\
    { 
      \AxiomC{$\tyseq{\Delta}{\Gamma}{ t }{ A }$}
        \AxiomC{$\tyformseq{\Delta}{B}$}
      \RightLabel{\scriptsize I$^{+}_L$}
      \BinaryInfC{$\tyseq{\Delta}{\Gamma}{ \inl{t}{A+B} }{ (A+B) }$}
      \DisplayProof
    }
    &
    { 
      \AxiomC{$\tyseq{\Delta}{\Gamma}{ t }{ B }$}
        \AxiomC{$\tyformseq{\Delta}{A}$}
      \RightLabel{\scriptsize I$^{+}_R$}
      \BinaryInfC{$\tyseq{\Delta}{\Gamma}{ \inr{t}{A+B} }{ (A+B) }$}
      \DisplayProof
    }
    \\\\
  \end{tabular}
  \begin{tabular}{c}
    { 
      \AxiomC{$\tyseq{\Delta}{\Gamma}{ t }{ \Quant{\alpha}{\pos{X}}{A} }$}
      \AxiomC{$\alpha \in \s{\mu,\nu}$}
      \RightLabel{\scriptsize E$^\alpha$}
      \BinaryInfC{$\tyseq{\Delta}{\Gamma}{ \unfoldalpha{t}{\Quant{\alpha}{\pos{X}}{A} }}{ A [\pos{X} := \Quant{\alpha}{\pos{X}}{A}] }$}
      \DisplayProof
    }
    \\\\
    { 
      \AxiomC{$\tyseq{\Delta}{\Gamma}{ t }{ A [\pos{X} := \Quant{\alpha}{\pos{X}}{A}] }$}     
      \AxiomC{$\alpha \in \s{\mu,\nu}$}
      \RightLabel{\scriptsize I$^\alpha$}
      \BinaryInfC{$\tyseq{\Delta}{\Gamma }{ \foldalpha{t}{\Quant{\alpha}{\pos{X}}{A} }}{ \Quant{\alpha}{\pos{X}}{A} }$}
      \DisplayProof
    }
    \\\\
    {
      \AxiomC{$\tyseq{\Delta}{\Gamma}{ r }{ A+B }$}
       \AxiomC{$\tyseq{\Delta}{\ext{\Gamma}{x}{A}}{ t }{ C }$}
        \AxiomC{$\tyseq{\Delta}{\ext{\Gamma}{y}{B}}{ s }{ C }$}
      \RightLabel{$\OrElim$}
      \TrinaryInfC{$\tyseq{\Delta}{\Gamma}{ (\cas{r}{x}{t}{y}{s}) }{ C }$}
      \DisplayProof
    }\\\\
    {
      \AxiomC{$\tyseq{\Delta}{\Gamma}{ s }{ A \times B }$}
      \AxiomC{$\tyseq{\Delta}{\ext{\ext{\Gamma}{x}{A}}{y}{B}}{ t }{ C }$}
      \RightLabel{$\AndElim$}
      \BinaryInfC{$\tyseq{\Delta}{\Gamma}{(\spit{s}{(x,y)}{t})}{ C }$}
      \DisplayProof
    }
  \end{tabular} 
\end{center}
\caption{System F Proof Rules}
\label{tab:systemfproof}
\end{figure}

Without further restrictions, this type system is unsound.  First, the
Delta rule for function constants clearly allows non-termination given
$\Prog(f)=f : T$.  We will deal with this potentiality later when we
describe cyclic proof in Section~\ref{sec:cyclic}.

In addition, we will need a concept of a one-hole context. This allows
us to describe terms which are embedded in a surrounding term.  We
write this as $C[t]$ when we wish to say that the term t has a
surrounding context.

\section{Cyclic Proof} 
\label{sec:cyclic} 

Typically, in functional programming languages, type checking for
defined functions is done by use of a typing rule that assumes the
type of the function and proceeds to check the body.  This is the
familiar rule from programming languages such as Haskell
\cite{gordon1999similarity} \cite{pierce2002tapl}
\cite{jones92implementinglazy}.  An example of such a typing rule is
as follows:

\begin{center} 
  { 
    \AxiomC{$\tyseq{\Delta}{\ext{\Gamma}{f}{A \imp B}}{\Prog(f)}{A \imp B}$}
    \RightLabel{$FunRec$}
    \UnaryInfC{$\tyseq{\Delta}{\Gamma}{f}{A \imp B}$}
    \DisplayProof
  }
\end{center}

Coupled with guardedness or structural recursion and positivity
restrictions on the form of recursive types to ensure (co)termination,
this rule will be sound.  However, it is also {\em opaque}.  Any
transformation of this proof tree will be rigidly expressed in terms
of the original function declarations.

In order to allow more fluidity in the structure of our proof trees we
introduce a notion of a cyclic proof.  Cyclicity can be introduced
simply by allowing the type rules to be a coinductive type (in the
meta-logic) rather than an inductive one.  However, for us to produce
the cycles we are interested in, we need to add an additional term and
typing rule which allows explicit substitutions, and one derived rule
which makes use of the fact that we identify all proofs under the
reduction relation $\leadsto$ as being equivalent.  The explicit
substitutions will also require an additional evaluation rule which
transforms them into computed substitutions.  Explicit substitutions
can also be introduced at the level of type substitutions, but these
are not necessary for our examples.

The $\ConvRule$, $\Unfold$ and the $\SubIntro$ follow from theorems
about the calculus which can be established in the meta-logic and in fact
we have a formal proof of these theorems for the given calculus in Coq.

\begin{figure}[!htbp]\small
  {\bf Explicit Substitutions}\\
  \begin{tabular}{l@@{\hspace{1in}} l}
    \hline \\
    $\exsub{t}{x}{s}$ & \\
  \end{tabular} 
  \\\\\\
  {\bf Typing Rules}\\
  \begin{tabular}{l}
      \hline \\
    {
      \AxiomC{$\tyseq{\Delta}{\Gamma \cup \Gamma'}{u}{B}$}
        \AxiomC{$\tyseq{\Delta}{\Gamma \cup \{ x \isof B \}}{t}{A}$}
      \RightLabel{$\SubIntro$}
      \BinaryInfC{$\tyseq{\Delta}{\Gamma \cup \Gamma'}{\exsub{t}{x}{u}}{A}$}
      \DisplayProof
    }\\\\
    {
       \AxiomC{$\tyseq{\Delta}{\Gamma}{t}{A}$}
         \AxiomC{$t \leadsto^{*} s$}
       \RightLabel{$\ConvRule$}
       \BinaryInfC{$\tyseq{\Delta}{\Gamma}{s}{A}$}
         \DisplayProof}
    {
      \AxiomC{$\tyseq{\Delta}{\Gamma}{C[\Prog(f)]}{A}$}
      \RightLabel{$\Unfold$}
      \UnaryInfC{$\tyseq{\Delta}{\Gamma}{C[f]}{A}$}
      \DisplayProof
    }\\\\
  \end{tabular}
  \\
  {\bf Extended Evaluation}\\
  \begin{tabular}{l l}
    \hline\\
    {
      \AxiomC{$\exsub{t}{x}{u} \leadsto t[x:=u]$}
      \DisplayProof
    }
    {
      \AxiomC{$t \leadsto t'$}
      \UnaryInfC{$\exsub{t}{x}{u} \leadsto \exsub{t'}{x}{u}$}
      \DisplayProof
    }
  \end{tabular}\\
  {\bf Structural Ordering}\\
 
    \begin{tabular}{l l} \\
      \hline\\
    { 
      \AxiomC{$\cas{r}{x}{s}{y}{t}$}
      \UnaryInfC{$x\rel{S}r$}
      \DisplayProof
    }&
    { 
      \AxiomC{$\cas{r}{x}{s}{y}{t}$}
      \UnaryInfC{$y\rel{S}r$}
      \DisplayProof
    }\\\\ 
    { 
      \AxiomC{$\spit{r}{(x,y)}{t}$}
      \UnaryInfC{$x \rel{S}r$}
      \DisplayProof
    }& 
    { 
      \AxiomC{$\spit{r}{(x,y)}{t}$}
      \UnaryInfC{$y \rel{S} r$}
      \DisplayProof
    }\\\\ 
    {
      \AxiomC{$\unfoldalpha{t}{\Alpha{X}{A}}$}
      \UnaryInfC{$\unfoldalpha{t}{\Alpha{X}{A}} \rel{S} t $}
      \DisplayProof
    }&
    {      
      $\structless := S^*$ $\;\;$ Transitive closure of $S$       
    }\\\\
  \end{tabular}

\caption{Explicit Substitution and Structural Ordering} 
\label{tab:substitution}
\end{figure}


% \begin{figure}[htbp!] 
%   \small
% %  \begin{center}
%   {\bf Structural Ordering}\\
 
%     \begin{tabular}{l l} \\
%     { 
%       \AxiomC{$\cas{r}{x}{s}{y}{t}$}
%       \UnaryInfC{$x\rel{S}r$}
%       \DisplayProof
%     }&
%     { 
%       \AxiomC{$\cas{r}{x}{s}{y}{t}$}
%       \UnaryInfC{$y\rel{S}r$}
%       \DisplayProof
%     }\\\\ 
%     { 
%       \AxiomC{$\spit{r}{(x,y)}{t}$}
%       \UnaryInfC{$x \rel{S}r$}
%       \DisplayProof
%     }& 
%     { 
%       \AxiomC{$\spit{r}{(x,y)}{t}$}
%       \UnaryInfC{$y \rel{S} r$}
%       \DisplayProof
%     }\\\\ 
%     {
%       \AxiomC{$\unfoldalpha{t}{\Alpha{X}{A}}$}
%       \UnaryInfC{$\unfoldalpha{t}{\Alpha{X}{A}} \rel{S} t $}
%       \DisplayProof
%     }&
%     {      
%       $\structless := S^*$ $\;\;$ Transitive closure of $S$       
%     }\\\\
%   \end{tabular}
% %  \end{center}
%   % \begin{center}
%   %   \begin{tabular}{l l}
%   %     $\structless := S^*$ & Transitive closure of $S$ 
%   %   \end{tabular}
%   % \end{center}
%   \caption{Structural Ordering}
%   \label{table:structural_ordering}
% \end{figure} 

We will not prove general soundness conditions, but rely on prior work
showing that structural induction and the guardedness are sufficient
conditions \cite{gimenez1998structural}.  Once these conditions have
been satisfied, we can assume the correctness of the proof.

\begin{definition}[Structural Ordering]
  A term $t$ is said to be {\em less in the structural ordering} than
  a term $s$, or $t \structless s$ using the relation $\structless$
  given by the inductive definition in Figure~\ref{tab:substitution}.
\end{definition}

\begin{definition}[Structural Recursion]
  A derivation is said to be structurally recursive if for every
  sequent used in a $\SubIntro$ rule, there exists a privileged variable
  $x$ such that for all $\SubIntro$ rules, with substitution $\sigma_i$,
  using that sequent we have that $x \in dom(\sigma_i)$ and $\sigma(x) \structless x$.
\end{definition}

It should be mentioned that there is nothing in particular needed for
this definition aside from some guarantee that we are well founded.
As such this represents a particular implementation {\em strategy} and
we could very well have used a more liberal approach.  One such
approach is {\em size-change termination} as described by Neil Jones
et al. in \cite{Jones2001sizechange}. 

Similarly, we must produce a rule for coinductive types which ensures
that all terms of coinductive type are {\em productive}.  We here
develop a {\em guardedness} condition specific to our type theory of
cyclic proofs.  Essentially this condition ensures we encounter an
introduction of a constructor which can not be eliminated on all
coinductive cyclic paths.  The only intermediate terms must reduce
finitely through eliminations of finite or inductively defined terms,
ensuring that we will not compute indefinitely prior to producing a
constructor.

While structural recursion is focused on determining whether the
arguments of a recursive term are subterms of some previously
destructured term, the dual problem is of determining if a recursive
term's context ensures that the term grows.  This means we need ways of
describing the surrounding context of a term.  However, the contexts
we have developed thus far are structured in terms of {\em
  experiments}.  With coinductive terms we need exactly the opposite
variety of contexts, those surrounding terms which are {\em not}
experiments.

The key important features of the contexts we are interested in turns
out to be whether or not they introduce constructors, and whether they
are guaranteed not to remove them.  These properties are necessary in
the construction of our proof that guardedness leads to {\em
  productivity}.

We can describe the relevant features of the context by describing a
{\em path}.  This {\em path} is a series of constructors that allows
us to demonstrate which directions to take down a proof tree to arive
at a recurrence.

\begin{definition}[Path]
  A {\em path} is a finite sequence of pairs of a proof rule from
  Figure~\ref{tab:systemfproof} and an index denoting which
  antecedent it decends from.  This pair is described as a {\em
    rule-index-pair}.
\end{definition}

An example of such a path would be the following: 

\begin{center} 
  OrIntroL$^1$,AndIntro$^2$,ImpIntro$^1$ 
\end{center}

This denotes the context: 

\begin{center} 
  $\inl{(\lambda x : B . -,s)}{A}$
\end{center}

With some unknown (and for the purpose of proving productivity,
inconsequential) variable $x$, term $s$ and types $A$ and $B$.

With this in hand we can establish conditions for guardedness with 
recursive definitions based on constraints on paths.

\begin{definition}[Admissible]
  A path is called admissible if the first element $c$ of the path $p
  = c,p'$ is one of the rule-index-pairs OrIntroL$^1$, OrIntroR$^1$,
  AndIntro$^1$, AndIntro$^2$, AllIntro$^1$, $\alpha$Intro$^1$,
  ImpIntro$^1$, OrElim$^2$, OrElim$^3$, AndElim$^2$, AllElim$^1$,
  Delta$^1$ and $p'$ is an admissible path.
\end{definition}

\begin{definition}[Guardedness]
  A path is called guarded if it terminates at a Pointer rule, with
  the sequent having a coinductive type and the path can be
  partitioned such that $p = p',[c],p''$ where $c$ is one of the
  rule-index-pairs OrIntroL$^1$, OrIntroR$^1$, AndIntro$^1$,
  AndIntro$^2$, $\nu$Intro$^1$, ImpIntro$^1$ which we will call {\em
    guards} and $p'$ and $p''$ are admissible paths.
\end{definition}

The idea behind the guardedness condition is that we have to be
assured that as we take a cyclic path we produce an Intro rule which
will never be removed by the reduction relation.  The left hand-side
of an elimination rule will never cause the elimination of such an
introduction and so is {\em safe}.  However, the right hand side of an
elimination rule may in fact cause the removal of the introduction
rule when we use the evaluation relation.

% \begin{definition}[Path]
%   A path $<v_0,\cdots,v_n>$ is a sequence of vertices such that for
%   each $v_i$, $v_{i+1} \in s(v_i)$ or $r(v_i)$ is undefined and
%   $s(v_i)=s(v_{i+1})$ where $i<n$.
% \end{definition}

% \begin{definition}[Sub-term]
%   A sub-term of a term $t$ which has a derivation with root $v_0$, is
%   any term which has a derivation starting from $v_i$ which is in a
%   path from $v_0$, and which contains only introductions ($\ImpIntro$,
%   $\AllIntro$, $\OrIntroL$, $\OrIntroR$, $\AndIntro$, $\alphaIntro$).
% \end{definition}

% \begin{definition}[Structural Recursion]
%   A pre-proof with cycles will meet the structural recursion condition,
%   if every bud associated with a $\mu$ type is a derivation of a
%   sub-term of its companion.
% \end{definition}

% \begin{definition}[Guardedness]
%   A pre-proof will meet the guardedness condition if every path from
%   every companion to a bud follows a right branch of an elimination
%   ($\ImpElim$, $\AllElim$, $\OrElim$, $\AndElim$, and entirely excluding
%   $\alphaElim$ which has only one rule), includes an introduction rule
%   ($\ImpIntro$, $\AndIntro$, $\OrIntroL$, $\OrIntroR$, $\alphaIntro$) and has a fold.
% \end{definition}

\section{Program Transformation}

Supercompilation is a family of program transformation techniques.  It
essentially consists of {\em driving}, {\em information propagation},
{\em generalisation} and {\em folding}.

Driving is simply the unfolding and elimination of cuts.
Cut-elimination involves the removal of all intermediate
datastructures.  This includes anything that would be normalised by
evaluation in a language like Coq or Agda, including beta-elimination,
case elimination or pair selection.  Driving, as it removes cuts from
infinite proof objects, generates potentially infinite computations.

Information propagation is the use of meta-logical information about
eliminations such as case branches.  For example, when a meta-variable
is destructed in a case branch, the particular de-structuring may be
propagated into sub-terms.  This is achieved by an inversion on the
typing derivation. 

Folding is the search for recurrences in the driven program.  A
recurrence will be an expression which is a variable renaming of a
former expression.  Essentially, if a recurrence is found we can
create a new recursive function having the same body as the driven
expression with a recursive call at the recurrence.

Generalisation may be used in order to find opportunities for folding.
We can abstract away arguments which would cause further driving and
would not allow us to fold.

Our notion of equivalence of proofs must be quite strict if it is to
preserve the operational behaviour of the program.  The notion of
equivalence we use here is {\em contextual equivalence}.

\begin{definition}[Contextual Equivalence]
  For all terms $s,t$ and types $A$ and type derivations $\cdot \vdash
  s : A$ and $\cdot \vdash t : A$, and given any experiment $e$ such
  that $x : A \vdash e : B$ then we have that $e [x := s] \Downarrow $
  and $e [ x:=t] \Downarrow$ then $s \sqsubseteq t$.  If $s
  \sqsubseteq t$ and $t \sqsubseteq s$ then $s$ is contextually
  equivalent to $t$ or $ s\cong t$.
\end{definition}

In the examples, the relation between the original and transformed
proofs is simply either a compatible relation with the formation
rules, or the term is related up to beta-equivalence.  In the case of
unfolding, it's clear that no real change has taken place since the
unfolded pre-proof just extends the prefix of the potentially infinite
pre-proof, and is identical by definition.  The finite prefix is
merely a short hand for the infinite unfolding of the pre-proof.

Dealing with reduction under the evaluation relation is more subtle.
In order to establish equivalence here we need to show that if the
term reduces, it reduces to an outer-most term which will itself
reduce when an experiment is applied.  This is essentially a {\em head
  normal form}, that is, a term whose outermost step will not reduce
in any context.  This idea is essential to defining productivity,
since it is precisely the fact that we have {\em done something}
irrevocable which gives us productivity.

Folding is also somewhat complex as, in our case, we will require the
use of generalisation, which is essentially running the evaluation
relation backwards in order to find terms which will be equivalent
under reduction, and cycles in the proof which can lead to potential
unsoundess.  The key insight of this paper is that in fact, unsoundess
can not be introduced if the cycles themselves are productive or
inductive for coinduction and induction respectively.

Generally the program transformation technique itself is controlled by
using some additional termination method such as a depth bound or more
popularly the homeomorphic embedding.  This however does not influence
the correctness of the outcome.  If an algorithm in the
supercompilation family terminates, the final program is a faithful
bisimulation of the original.  

Since all of the examples given in this paper clearly follow the
fold/unfold generalise paradigm, and all examples are
inductive/productive, the correctness can be assumed.  In a future
work we hope to present the algorithm that was used to find these
examples in more detail, and to show that it will in general produce
contextually equivalent programs.  We will see how these elements are
applied in practice by using these techniques to work with cyclic
proofs.

\subsection{Reduction}

Previously we gave a bird's-eye view of supercompilation as being a
family of program transformations composed of driving, generalisation
and folding.  Cyclic proofs give us the tools necessary to justify
folding in the context of types and driving is simply the unfolding of
a cyclic pre-proof.  

In order to perform folding however, we need to be able to arrive at
nodes which are $\alpha$-renamings of former nodes.  In order to do
this in general we need to be able to generalise terms.  We can, using
generalisation, regenerate proofs which simply make reference to
recursive functions, by generalising to reproduce $\alpha$-renamings
of the function bodies and folding.  This ensures that we can produce
{\em at least} the proofs possible already using the original term.

For higher order functional languages, there are a potentially
infinite number of generalisations of two terms, and the least general
generalisation may itself consist of many incomparable terms
\cite{Pfenning1991Unification}.  For this reason, some heuristic
approach needs to be applied in order to find appropriate
generalisations.  We will not be concerned about the particular
heuristic approach used to determine generalisations as this is quite
a complex subject, but only that it meet the condition that the
generalisation can be represented as an elimination rule in the proof
tree and that will regenerate the original proof tree under
evaluation.

\section{Example Revisited}

With the notion of cyclic proof, we now have at our disposal the tools
necessary to transform pre-proofs into proofs.  We will revisit the
$sumlen$ example given as motivation for the present work and see how
we can represent the transformations.

We take again an example using the {\em co-natural numbers}
$\mathbb{N}^{\infty} \equiv \nu X. 1 + X$ and potentially infinite
lists $[A] \equiv \Lambda A. \nu X . 1 + (A\times X)$.  Here we take
$\Prog$ to be defined as:

\input{code}

\begin{figure}
\begin{center}
  \includegraphics[scale=.8]{sumlen.pdf}
\end{center} 

\begin{center}
  $\Large \Downarrow$
\end{center}

\begin{center}
  \includegraphics[scale=.75]{sumlen2.pdf}
\end{center} 

\begin{center}
  $\Large \Downarrow$
\end{center}

\begin{center}
  \includegraphics[scale=.75]{sumlen3.pdf}
\end{center} 

\begin{center}
  $\Large \Downarrow$
\end{center}

\begin{center}
  \includegraphics[width=\textwidth]{sumlen4.pdf}
\end{center} 

\begin{center}
  $\Large \Downarrow$
\end{center}

\begin{center}
  \includegraphics[width=\textwidth]{sumlen5.pdf}
\end{center} 

\caption{Sumlen Cyclic Proof}
\label{figure:proofs}
\end{figure}

We can now produce the type derivation by performing the successive
steps given explicitly in Figure~\label{figure:proofs}.  Here in the
final step we have driven the proof tree to the point that we can now
reference two previous nodes.  One of those is labelled with a
${\color{Green} \dagger}$, the other with a ${\color{Green} *}$. This
final pre-proof is now a proof because it satisfies the guardedness
condition.  We have taken the liberty of introducing a an additional
derived rule $\text{Cons}^{\stream{\conat}}$.  It is merely a
shorthand for the use of $\OrIntroR$ and $\nuIntro$, together with a
proof that these types admissible under the formation rules.

We can then produce a {\em residual} program from the cyclic proof.
This is simply a mutually recursive (or letrec) function definition
which makes any cycle into a recursive call.  The residual term will
be essentially the one given in agda above. 

\section{Related Work}

The present work uses a program transformation in the supercompilation
family.  This was first described by Turchin \cite{turchin86concept}
and later popularised by S{\o}rensen, Gl{\"u}ck and Jones
\cite{SORENSEN96}.  We essentially use the same algorithms with the
addition of the use of type information to guide folding.

The use of cylic proofs was developed by Brotherston
\cite{BROTHERSTON05}.  We extend this work by dealing also with
coinductive types and make use of it in a Curry-Howard settings.

The correspondence between cyclic proof and functional programs has
previously been described by Robin Cockett
\cite{cockett01deforestation}.  His work also makes a distinction
between inductive and coinductive types.  Our work differs in using
super compilation as a means of proving type inhabitation.

Various approaches to proving type inhabitation for coinductive types
have appeared in the literature.  Bertot and Komendanskaya give a
method in \cite{bertot2008inductive}.  A method is also given using
sized types is given by Abel in \cite{abel99terminationchecking}.  The
approach in this paper differs in that we use transformation of the
program rather than reasoning about the side conditions.

\section{Conclusion and Future Work}

The use of program transformation techniques for proofs of type
inhabitation is attractive for a number of reasons.  It gives us the
ability to mix programs which may or may not be type correct to arrive
at programs which are provably terminating.  We can keep an audit
trail of the reasoning by which the programs were transformed.  And we
can admit a larger number of programs by transformation to a form
which is syntactically correct, obviating the need for complex
arguments about termination behaviour.  For these reasons we feel that
this work could be of value to theorem provers in the future.  

To the best of the authors knowledge, no examples of a
supercompilation algorithm have yet been given for a dependently typed
language.  The authors hope to extend the theory to dependent types in
the future such that the algorithm might be of assistance to theorem
provers.

Currently work is being done on a complete automated proof of
correctness of a supercompilation algorithm for the term language
described in this paper in the proof assistant Coq.  The cyclic proofs
are represented using a coinductive data-type, rather than the usual
inductive description.

The technique as presented works well for many examples, however there
are some examples in which direct supercompilation is insufficient.
The following program tries to capture the notion of a semi-decidable
existential functional which takes a semi-decidable predicate over the
type $A$.  The usual way to write this in a functional language is to
use the Sierpinski type \cite{escardo2004synthetic}, the type of one
constructor.  Here truth is represented with termination, and
non-termination gives rise to falsehood.

%format S = "{\color{Blue} S }"
%format T = "{\color{Green} T }"
\begin{code}
data S : Set where 
  T : S
\end{code}

However since languages such as Coq and Agda will not allow us to
directly represent non-termination, we will embed the Sierpinski type in the delay monad.

%format Delay = "{\color{Blue} Delay }"
%format now = "{\color{Purple} now }"
%format later = "{\color{Purple} later }"
\begin{code}
codata Delay (A : Set) : Set where 
  now : A -> Delay A
  later : Delay A -> Delay A 
\end{code}

The clever reader might notice that this is in fact isomorphic to the
co-natural numbers and that join is simply the minimum of two
potentially infinite numbers.
 
\begin{code}
join : Delay S -> Delay S -> Delay S
join (now T) x = now T
join x (now T) = now T
join (later x) (later y) = later (join x y)

ex : { A : Set } -> (A -> Delay S) -> 
  Stream A -> Delay S
ex p (x :: xs) = join (p x) (ex p xs)
\end{code}

By unfolding $join$ and $ex$ we eventually arrive at a term:

\begin{code}
    -- join x' (join (p x) (ex p xs))
\end{code}

This term is a repetition of the original body of $ex$, with $p\;x$
abstracted, provided that join is associative.  Unfortunately, using
direct supercompilation, we are unable to derive a type correct term
automatically.  However, using ideas presented by Klyutchnikov and
Romanenko \cite{equiv2009klyuchnikov}, the technique might be extended
in such a way to provide an automated solution for this example as
well.  Using the fact that the recurrence is contextually equivalent,
we can fold the proof to obtain the following program, which is
productive, and admissible into Agda.

\begin{code}
mutual 
  ex_trans : { A : Set } -> 
    (A -> Delay S) -> Stream A -> 
    Delay S
  ex_trans p (x :: xs) = later (j (p x) p xs)

  j : { A : Set} -> 
    Delay S -> (A -> Delay S) -> 
    Stream A -> Delay S
  j (now T)     p _         = now T
  j (later n) p (x :: xs) = later (j (join n (p x)) p xs)
\end{code}

\bibliographystyle{plain}
\bibliography{master}
\end{document}
