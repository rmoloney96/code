\documentclass[svgnames]{beamer}
\include{bussproofs}

%include agda.fmt 

\author{Gavin Mendel-Gleason} 
\title{Productivity and Program Transformation} 

\subtitle{Development of the Productive Forces} 

\institute{Dublin City University\\ 
  LERO the Irish Software Engineering Research Centre}

\date[Par-2010]{Workshop on Partiality and Recursion in Interactive
Theorem Provers \\ 
  \small 15 July 2010, Edinburgh}

\usetheme{Boadilla} 

\begin{document} 

\begin{frame} 
  \titlepage
\end{frame} 

\section{The Problem}

\begin{frame}
  \frametitle{Proving Productivity}
  \begin{itemize} 

    \item Guardedness gives us a syntactic condition for determining
    co-termination.

    \item The condition is easy to check but very restrictive.
    
    \item Program transformation lets us keep the simple check and
    alter the code.

    \item The trick is that we preserve termination behaviour - if the
    final program is correct, so was the original.

  \end{itemize}
\end{frame} 

%format Set = "{\color{Blue} Set }"
%format CoNat = "{\color{Blue} \mathbb{N}^{\infty} }"
%format CoList = "{\color{Blue} CoList }"
%format czero = "{\color{Purple} czero }"
%format csucc = "{\color{Purple} csucc }"
%format (::) = "{\color{Purple} :: }"

\section{Examples}
\begin{frame} 
\begin{code} 
module Slides where

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
\end{frame}

\begin{frame} 
  \vskip0.8in
  \begin{center} {\em \Large ... and after supercompilation ...}
  \end{center}
\end{frame}

\begin{frame}
\begin{code} 
mutual 
  sumlen_sc : CoList CoNat -> CoNat
  sumlen_sc []        = czero 
  sumlen_sc (x :: xs) = csucc (aux x xs) 
  
  aux : CoNat -> CoList CoNat -> CoNat
  aux czero     xs = sumlen_sc xs 
  aux (csucc x) xs = csucc (aux x xs)
\end{code}
\end{frame}

%format Bool = "{\color{Blue} Bool }"
%format Stream = "{\color{Blue} Stream }"
%format Nat = "{\color{Blue} \mathbb{N} }"
%format zero = "{\color{Green} zero }"
%format succ = "{\color{Green} succ }"
%format true = "{\color{Green} true }"
%format false = "{\color{Green} false }"

\begin{frame}
\begin{code}
data Bool : Set where 
  true : Bool 
  false : Bool 

data Nat : Set where 
  zero : Nat 
  succ : Nat -> Nat

infix 5 if_then_else_
if_then_else_ : { A : Set } -> Bool -> A -> A -> A
if true then x else y = x
if false then x else y = y
infixr 40 _::_
codata Stream (A : Set) : Set where 
  _::_ : A -> Stream A -> Stream A
\end{code}
\end{frame} 

\begin{frame}
\begin{code}
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
\end{frame} 

\begin{frame} 
  \vskip0.8in
  \begin{center} {\em \Large ... and after supercompilation ...}
  \end{center}
\end{frame}

\begin{frame}
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
\end{frame} 

\section{Cyclic Proof}

\begin{frame}
  \begin{itemize}
    \frametitle{What is Going On?}

    \item We can think of the process as the transformation of cyclic
    proofs. 

    \item We take a cyclic pre-proof and transform it into a cyclic
    proof which meets guardedness (and structural induction).

    \item We use three tools which together are called
    supercompilation: driving, generalisation and folding.
  
  \end{itemize} 
\end{frame}

\begin{frame}
  \frametitle{Cyclic Proof}

  \begin{tabular}{l}
    In programming languages the usual typing rule \\
    for functions looks like: \\ 
    \\
    \includegraphics{typerule.pdf}\\
  \end{tabular}

  \begin{itemize}
    \item This proof rule is opaque.  We can't see inside the body of
    $f$ once it has been placed on the context. 

    \item Instead we'll simply unfold without placing f on the context, and 
    if we see a repeated derivation, we'll reference it - creating a cycle. 

    \item We can now eliminate intermediate cuts (driving) and synthesis new
    functions (generalisation and folding).

  \end{itemize}
\end{frame}

\begin{frame}
  \begin{itemize}
    \frametitle{Driving}

    \item Unfold function definitions
    \item Perform $\beta$-reduction to head normal form.
    \item Wash-rinse-repeat 
    \item Creates an infinite proof for (co)-recursive programs.
  \end{itemize}
\end{frame}

\begin{frame}
  \begin{itemize}
    \frametitle{Generalisation}

    \item Allows us to decompose a term into an application.\\
          \( f\;s \Rightarrow (\lambda x:T. f\;x)\;s \)
    \item This is a form of "cut introduction".

    \item We can now find cycles which would otherwise not be present
    - it potentiates folding.

  \end{itemize}
\end{frame}

\begin{frame}
  \frametitle{Folding}
    \begin{itemize}

      \item If we find a prior node in the graph, we simply reuse the
      proof from that node.  We can control folding by checking to see
      that we have descended through a destructuring of a formal
      parameter (inductive) - or by checking to see if a constructor
      was emitted (co-inductive).
      
      \item We use this to produce a finite representation of the
      (potentially) infinite proof produced by driving.

      \item We can {\em always} produce some new pre-proof since we
      can simply reuse the original pre-proof, but obviously we can't
      always generate a proof this way.

    \end{itemize} 
\end{frame}

\section{Cyclic Proof Example}

\begin{frame} 
  \begin{center}
   \includegraphics[width=\textwidth]{sumlen.pdf}
  \end{center}
\end{frame}

\begin{frame} 
  \begin{center}
   \includegraphics[width=\textwidth]{sumlen2.pdf}
  \end{center}
\end{frame}

\begin{frame} 
  \begin{center}
    \includegraphics[width=\textwidth]{sumlen3.pdf}
  \end{center}
\end{frame}

\begin{frame} 
  \begin{center}
    \includegraphics[width=\textwidth]{sumlen4.pdf}
  \end{center}
\end{frame}

\begin{frame} 
  \begin{center}
    \includegraphics[width=\textwidth]{sumlen5.pdf}
  \end{center}
\end{frame}

\section{Future Work}

\begin{frame} 
  \frametitle{Future Work}
  
  \begin{itemize} 

    \item Supercompilation works for some interesting examples.

    \item Doesn't work for others - but higher-level supercompilation
    can extend the class (Klutchnikov - Romanenko).
  
    \item The use of supercompilation hasn't been developed for a
    theory of dependent types, but it seems doable.

  \end{itemize}  
\end{frame}

%format S = "{\color{Blue} S }"
%format Delay = "{\color{Blue} Delay }"
%format T = "{\color{Green} T }"
%format now = "{\color{Purple} now }"
%format later = "{\color{Purple} later }"

\begin{frame} 
\begin{code}
data S : Set where 
  T : S

codata Delay (A : Set) : Set where 
  now : A -> Delay A
  later : Delay A -> Delay A 

join : Delay S -> Delay S -> Delay S
join (now T) x = now T
join x (now T) = now T
join (later x) (later y) = later (join x y)

ex : { A : Set } -> 
  (A -> Delay S) -> Stream A -> Delay S
ex p (x :: xs) = join (p x) (ex p xs)
\end{code} 
\end{frame}

\begin{frame}
  \frametitle{The Special Sauce}
  
  We can't do this transformation without a lemma.  Supercompilation
  can prove the lemma automatically (associativity of join) but we
  need to somehow know we should.\\
  
  \begin{code}
    -- join (p x) (ex p xs)
  \end{code} 

  \begin{code} 
    -- join x' (join (p x) (exist p xs))
  \end{code} 

\end{frame} 

\begin{frame} 
\begin{code}
mutual 
  ex_trans : { A : Set } -> 
    (A -> Delay S) -> Stream A -> Delay S
  ex_trans p (x :: xs) = later (j (p x) p xs)

  j : { A : Set} -> 
    Delay S -> (A -> Delay S) -> Stream A -> Delay S
  j (now T)     p _         = now T
  j (later n) p (x :: xs) = later (j (join n (p x)) p xs)
\end{code}
\end{frame} 

\end{document}