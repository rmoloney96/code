\documentclass{llncs}


%%%%%%%%%%%%%%%%% Preamble %%%%%%%%%%%%%%%%%%%%%%%

%% Fix Margins 
%\usepackage[margin=1in]{geometry}

\usepackage{listings}
\usepackage{amsfonts}
\usepackage{xcolor}
\usepackage{graphicx}

% Equations
\usepackage{amsmath}

% Fonts
\usepackage{amssymb}
\usepackage{bbm}
\usepackage[greek,english]{babel}
\usepackage{textgreek}
\usepackage{stmaryrd}

%handles sizes
\usepackage{anyfontsize}

%% This handles the translation of unicode to latex:
%\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{autofe}

%% Some convenient shorthands
\newcommand{\AD}{\AgdaDatatype}
\newcommand{\AF}{\AgdaFunction}
\newcommand{\AB}{\AgdaBound}
\newcommand{\AIC}{\AgdaInductiveConstructor}
\newcommand{\AM}{\AgdaModule}
\newcommand{\AP}{\AgdaPrimitive}
\newcommand{\AS}{\AgdaString}
\newcommand{\AR}{\AgdaRecord}
\newcommand{\AK}{\AgdaKeyword}
\newcommand{\AO}{\AgdaOperator}
% Better use this one!

\usepackage{agda}
%include agda.fmt

\usepackage{bussproofs}

%% Lambda Calculus (should be a .sty at some point) 
\definecolor{typeColour}              {HTML}{0000CD}
\definecolor{judgementColour}         {HTML}{008B00}

\newcommand{\atype}[1]{\textcolor{typeColour}{#1}}

\newcommand{\ofty}[2]{{#1}{:}{#2}}
%\newcommand{\ofty}[2]{{#1}\colon\kern-.15em{#2}}
\newcommand{\bigofty}[2]{{#1} \textcolor{judgementColour}{\;:\;} { \atype{#2} }}
\newcommand{\lam}[3]{\lambda(\ofty{#1}{ \atype{#2} }).{#3}}
\newcommand{\app}[2]{{#1}\circ{#2}}
\newcommand{\bred}{\;\Rightarrow_{\beta}\;}
\newcommand{\subst}[2]{ [{#1} := {#2}] }

\newcommand{\seq}[3]{{#1} \textcolor{judgementColour}{\;\vdash\;} \bigofty{#2}{#3} }

\newcommand{\oseq}[2]{{#1} \textcolor{judgementColour}{\;\vdash\;} {#2}}

\newcommand{\imp}[2]{{#1} \rightarrow {#2}}

\newcommand{\impElim}{$E^{\rightarrow}$}


%% Some characters that are not automatically defined
%% (you figure out by the latex compilation errors you get),
%% and you need to define:
%
%\DeclareUnicodeCharacter{8988}{\ensuremath{\ulcorner}}
%\DeclareUnicodeCharacter{8989}{\ensuremath{\urcorner}}
%\DeclareUnicodeCharacter{8803}{\ensuremath{\overline{\equiv}}}
\DeclareUnicodeCharacter{8799}{\ensuremath{\stackrel{{!!}}{=}}}
\DeclareUnicodeCharacter{8759}{\ensuremath{\colon\colon}}
\DeclareUnicodeCharacter{7477}{\ensuremath{^{I}}}
\DeclareUnicodeCharacter{7472}{\ensuremath{^{D}}}
\DeclareUnicodeCharacter{7580}{\ensuremath{^{C}}}
\DeclareUnicodeCharacter{7488}{\ensuremath{^{T}}}
\DeclareUnicodeCharacter{7480}{\ensuremath{^{L}}}
\DeclareUnicodeCharacter{7486}{\ensuremath{^{P}}}
\DeclareUnicodeCharacter{7484}{\ensuremath{^{O}}}
\DeclareUnicodeCharacter{7584}{\ensuremath{^{F}}}
\DeclareUnicodeCharacter{7468}{\ensuremath{^{A}}}
\DeclareUnicodeCharacter{2208}{\ensuremath{\in}}
\DeclareUnicodeCharacter{956}{\ensuremath{\mu}}
%% Add more as you need them (shouldn’t happen often). 

%% Hyper ref for \url support
\usepackage{hyperref}

%%%%%%%%%%%%%%%%%%% Paper %%%%%%%%%%%%%%%%%%%%%%%%%%
\title{Model Checking the Semantic Web with the Modal μ-Calculus}
\author{Gavin Mendel-Gleason\\ 
Trinity College Dublin}

\begin{document}

\maketitle 

%% 1. Who are the intended readers(3-5 names)
%% 2. What did you do?(50 words)
%% 3. Why did you do that?(50 words) - why did it need to be done in the field?
%% 4. What happened when you did it? (50 words)
%% 5. What do the results mean in theory(50 words)
%% 6. What  do the results mean in practice(50 words)
%% 7. (NB most impt q) What is the key benefit for readers?(25 words)
%% 8. What remains unresolved (no word limit)

\begin{abstract}
Provided that we view triple-stores and linked data as transition systems then a number of well studied calculi can be used to specify properties of these graphs. A very expressive language of this type is the Modal μ-calculus.  We have implemented a denotational semantics of μ-calculus formulae. This can be used either as a query-language, finding all URIs which meet some formula, or as a {\em type checker}, which tells us if a given URI satisfies the formula of interest. This implementation was
\end{abstract}

\section{Introduction}



\section{Acknowledgement}

This research is partially supported by the European Union European Union's
Horizon 2020 research and innovation programme under grant agreement No
644055 (ALIGNED, \url{www.aligned-project.eu}).

\bibliographystyle{plain}
\bibliography{export.bib}

\end{document}

