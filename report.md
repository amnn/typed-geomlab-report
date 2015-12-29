---
title: Type Checking Geomlab
author: Ashok Menon
abstract: |
  Lorem Ipsum.
...

```{.haskell}
```

\section{Introduction}

Lorem Ipsum.

\section{Background}

\subsection{Source Language}
\begin{figure}[htbp]
  \caption{Examples of \textit{Geomlab}'s syntax.}\label{fig:geomlab-syntax}
  \input{aux/geomlab_syntax.tex}
\end{figure}

\textit{GeomLab} is a functional programming languge with a rich syntax (Figure\ \ref{fig:geomlab-syntax}), including nested pattern matching, guards, list comprehensions, ranges and operator sections. When parsing the source language, we generate an abstract syntax tree that faithfully represents all these high-level features (Figure\ \ref{fig:sugar_adt}).

\begin{figure}[htbp]
  \caption{\textit{GeomLab} Abstract Syntax Tree. The structure of literals are shared between that of patterns and of expressions, and so has been factored out.}\label{fig:sugar_adt}
  \input{aux/sugar.tex}
\end{figure}

The $\mathbf{Sugar}$ type is ideal for parsing due to its similarity to the syntax. But, many of the nodes in $\mathbf{Sugar}$ --- corresponding to syntactic sugar --- are, in a sense, "redundant" from a typechecker's perspective. These nodes are mechanically derivable from the composition of others in $\mathbf{Sugar}$, and so in turn, the definition of the typechecker at these "sugary" nodes is derivable from its definition at the constituent nodes. We avoid repeating this logic by \textit{desugaring} the input.

\subsection{Desugaring}

Desugaring involves replacing sugar with extensionally equivalent expressions from a restricted subset of the source language. We represent the AST after desugaring with a new type (Figure\ \ref{fig:expr_adt}) to ensure at compile-time that after desugaring, no sugar exists in the AST.

\begin{figure}[htbp]
  \caption{Type for the desugared AST.}\label{fig:expr_adt}
  \input{aux/expr.tex}
\end{figure}

List comprehensions, ranges and operator sections have been removed, and case expressions have been decoupled from function definitions into their own node (and the related \texttt{FailE} and \texttt{FallThroughE}). We also lift the restriction that only identifiers may be applied as functions. Finally, whilst in the source language patterns could be nested arbitrarily deep, in $\mathbf{Expr}$, each case expression only matches one layer (to reclaim the previous functionality, case expressions themselves are nested).

The procedure $\textit{desugar} : \mathbf{Sugar} \to \mathbf{Expr}$ treats operator sections, ranges and list comprehensions as in GeomLab's compiler\ \cite{GeomLab}, by converting to applications of helper functions provided by the runtime (Figure\ \ref{fig:standard-defs}), whilst the algorithm for desugaring case expressions draws inspiration from Lennart Augustsson's paper\ \cite{Augustsson:1985:CPM:5280.5303} on the techniques used to compile pattern matching in \textit{LML}, a lazy variant of \textit{ML}.

\begin{figure}
  \caption{Helper functions, as found in \textit{GeomLab}'s compiler.}\label{fig:standard-defs}
  \input{aux/standard_defs.tex}
\end{figure}

\subsection{de-Bruijn Indices}

$\mathbf{Expr}$ also alters the way local variables are introduced and denoted, using a notation referred to as \textit{de Bruijn} indices. $\mathbf{Expr}$ AST nodes that introduce new variables (like function definitions, let and case expressions) do not declare variable names, but instead simply declare how many local variables they introduce (functions introduce one for each formal parameter, let expressions always introduce one, and case expressions introduce one for every hole in the pattern). Then a reference to a local variable is denoted by the number of scopes between the reference and the scope introducing it (Figure\ \ref{fig:de_bruijn}).

\begin{figure}[htbp]
  \caption{Desugaring local variables to de-Bruijn indices.}\label{fig:de_bruijn}
  \input{aux/de_bruijn.tex}
\end{figure}

This notation has several advantages:

\begin{itemize}
  \item It tackles the issue of name shadowing (from variables inserted by the desugarer) without resorting to generating unique symbols, which requires side effectful operations.

  \item As a corollary to the first point, this makes \textit{desugar} a pure, deterministic function, which is better for testing.

  \item As the typechecker traverses the AST, it must create fresh \textit{type} variables for each local variable it encounters. These type variables can be stored in a stack, from which they can be efficiently retrieved using the local variable's de Bruijn index.

  \item When debugging output from the desugarer, free variables and bound variables are easily distinguishable in the AST.
\end{itemize}

\section{Hindley and Milner's Type System}

\subsection{Algorithm}

Lorem Ipsum.

\subsection{Implementation}

Lorem Ipsum.

\subsection{Applications}

Lorem Ipsum.

\subsection{Limitations}

Lorem Ipsum.

\section{Regular Tree Grammars}

Lorem Ipsum.

\section{Variance}

Lorem Ipsum.

\section{Type Errors}

Lorem Ipsum.

\section{References}

\bibliography{references}
