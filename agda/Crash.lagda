\documentclass{article}

%include agda.fmt

\begin{document}

We start with the module header:
\begin{code}
module Crash where

codata CoNat : Set where 
  czero : CoNat
  csucc : CoNat → CoNat

\end{code}

\end{document}
