---
title: Structural Type Inference in a Functional Programming Language
author: Ashok Menon
abstract: |
  In this project we consider a range of extensions to Hindley and Milner's type system that allow us to specify the types found in previously dynamically typed functional programming languages. In particular, rather than simply inferring the types of parameters to composite data structures (The type of the elements in a list structure, for example), we aim to infer the shape of the structure itself as composed of atomic values, cons cells and nils --- In the case of a list, that it is either empty, or is an element, followed by a list containing more of the same type of element.
...

```{.haskell}
```

\section{Introduction}

In the majority of statically typed languages, data types are explicitly defined, whilst in dynamically typed languages, arbitrary data structures may be constructed from a relatively small set of constructors. Traditional type inference relies on such data definitions to aid in type assignment. For instance, in \textit{Haskell}:

```{.haskell}
data List a = Nil | Cons a (List a)

head (Cons x  _) = x
fst       (x, _) = x
```

Inference uses the fact that \texttt{Cons} is a constructor for $\mathbf{List}~\alpha$ and $(,)$ --- the pair constructor --- is a constructor for $(\alpha,\beta)$ to assign the types:
\begin{math}
  \arraycolsep=1pt
  \begin{array}{llll}
    \mathit{head} & : \forall \alpha       \ldotp & \mathbf{List}~\alpha & \to\alpha\\
    \mathit{fst}  & : \forall \alpha,\beta \ldotp & (\alpha,\beta)       & \to\alpha
  \end{array}
\end{math}
Dynamic languages --- especially of the \textsc{Lisp} tradition --- can treat these operations as the same: A non-empty list is just a pair of its first element and the rest of the list. This is not the case in \textit{Haskell} (as shown by the types) nor is it in many statically typed languages. Seemingly, the difference is that \texttt{head} can be applied to any list (even the empty list, \texttt{Nil}), but this is an artefact of the type system's limitations: \texttt{head Nil} evaluates to a runtime error!
Associating constructors with each other is injurious to the precision of our type system. By extending battle-hardened type systems, it is possible to work in a setting where, like terms in a dynamically typed language, types are built up from a small set of constructors. In such an environment, the functionality of both \texttt{head} and \texttt{fst} could be captured in a single function, applicable to both lists and pairs, in such a way that it would be a type error to apply it to an empty list.

Section\ \ref{sec:bg} introduces the source language, \textit{GeomLab}, and the type checker's internal representation of it. Section\ \ref{sec:hm} then describes an optimised implementation of the Hindley--Milner type system for \textit{GeomLab}. Finally, Sections\ \ref{sec:adhoc-adts},\ \ref{sec:recursive} and\ \ref{sec:tagged-variants} extend the type system to make the structure of types more compositional while losing neither expressivity nor type inference.

The resulting framework allows us to capture and infer the specifications programmers are used to maintaining themselves when programming in dynamic languages and enforce them statically.

\section{Background}\label{sec:bg}

In this project we use a subset of \textit{GeomLab} as our source language. A strict, dynamically typed, functional language offering a rich set of features such as higher-order functions, pattern matching with guards, operator sectioning, list comprehensions and ranges. We chose it as a compelling middle-ground between the $\lambda$ calculus, and most popular functional languages in use today, the implication being that if our techniques are applicable in this setting, with minimal effort we may move in either direction to serve both theory and practise. A full exposition of the syntax is available in Appendix\ \ref{app:lang}.

\subsection{Parsing}

\begin{figure}[htbp]
  \caption{\textit{GeomLab} Abstract Syntax Tree. The structure of literals are shared between that of patterns and of expressions, and so has been factored out.}\label{fig:sugar_adt}
  \input{aux/sugar.tex}
\end{figure}

We parse programs into abstract syntax trees of the $\mathbf{Sugar}$ type (Figure\ \ref{fig:sugar_adt}). But, many of the nodes in $\mathbf{Sugar}$ --- corresponding to syntactic sugar --- are, in a sense, "redundant" from a typechecker's perspective. These nodes are mechanically derivable from the composition of others in $\mathbf{Sugar}$, and so in turn, the definition of the typechecker at these "sugary" nodes is derivable from its definition at other nodes. We avoid repeating this logic by \textit{desugaring} the input.

A potential cost of this operation is that errors become hard to relate to the source program. By annotating the syntax tree with source locations and carefully carrying them over to the desugared representation, we can recover this relationship. Appendix\ \ref{app:errors} describes an implementation, using \textit{Haskell's} \textit{Applicative Functor} abstraction.

\subsection{Desugaring}

Desugaring involves replacing sugar with extensionally equivalent expressions from a restricted subset of the source language. We represent the AST after desugaring with a new type (Figure\ \ref{fig:expr_adt}) to ensure at compile-time that after desugaring, no sugar exists in the AST.

\begin{figure}[htbp]
  \caption{Type for the desugared AST.}\label{fig:expr_adt}
  \input{aux/expr.tex}
\end{figure}

List comprehensions, ranges and operator sections are removed, if expressions and pattern matching function definitions both become case expressions. We also lift the restriction that only identifiers may be applied as functions. Finally, whilst in the source language patterns could be nested arbitrarily deep, in $\mathbf{Expr}$, each case expression only matches one layer (to reclaim the previous functionality, case expressions themselves are nested).

The procedure $\textit{desugar} : \mathbf{Sugar} \to \mathbf{Expr}$ treats operator sections, ranges and list comprehensions as in \textit{GeomLab}'s compiler\ \cite{Geomlab}, by converting to applications of helper functions provided by the runtime (Figure\ \ref{fig:standard-defs}), whilst the algorithm for desugaring case expressions draws inspiration from Lennart Augustsson's paper\ \cite{Augustsson:1985:CPM:5280.5303} on the techniques used to compile pattern matching in \textit{LML}, a lazy variant of \textit{ML}.

\begin{figure}
  \caption{Helper functions, as found in \textit{GeomLab}'s compiler.}\label{fig:standard-defs}
  \input{aux/standard_defs.tex}
\end{figure}

\subsection{de Bruijn Indices}

$\mathbf{Expr}$ also denotes local variables with \textit{de Bruijn} indices. AST nodes that introduce new variables (function definitions, let and case expressions) do not declare variable names, but declare how many variables they introduce (functions introduce one for each formal parameter, let expressions always introduce one, and case expressions introduce one for every hole in the pattern). References to local variables are denoted by the number of scopes between the reference and the scope introducing it (Figure\ \ref{fig:de_bruijn}).

\begin{figure}[htbp]
  \caption{Desugaring local variables to de Bruijn indices.}\label{fig:de_bruijn}
  \input{aux/de_bruijn.tex}
\end{figure}

This notation has several advantages:

\begin{itemize}
  \item It avoid name shadowing (from variables inserted by the desugarer) without generating unique symbols, which requires side effects. This makes \textit{desugar} a pure, deterministic function, which is better for testing.

  \item As the typechecker traverses the AST, it must create fresh \textit{type} variables for each local variable it encounters. These type variables can be stored in a stack, from which they can be efficiently retrieved using the local variable's de Bruijn index.

  \item When debugging output from the desugarer, free variables and bound variables are easily distinguishable in the AST.
\end{itemize}

\subsection{Definitions}

Below are some basic definitions used when discussing type systems and their associated theory.

By convention, the lowercase Roman alphabet denotes terms, $r,s,t,\ldots$ (and variables $x,y,z,\ldots$), the lowercase Greek alphabet denotes types, $\rho,\sigma,\tau,\ldots$ (and type variables, $\alpha,\beta,\gamma,\ldots$), and the uppercase Greek alphabet denotes type contexts, $\Gamma,\Delta,\ldots$

\begin{definition}[Type Context]
  A context $\Gamma$ is a partial map from variables to types. Given a context $\Gamma$, variable $x$, and a type $\sigma$, we will write $\Gamma,x : \sigma$ to denote the map $\Gamma$ with its type for $x$ overwritten with $\sigma$.
\end{definition}

\begin{definition}[Type Judgement]
  $\Gamma\vdash t :\sigma$ is a type judgement stating that assuming context $\Gamma$ there exists a proof that $t$ inhabits type $\sigma$ (in some fixed type theory).
\end{definition}

\begin{definition}[Substitution]
  $\mathbb{S}\equiv[\tau_1/\alpha_1,\ldots,\tau_n/\alpha_n]\equiv[\tau_i/\alpha_i]$ is a type substitution that, when applied to a type $\sigma$ simultaneously replaces all free occurrences of $\alpha_i$ with $\tau_i$ in $\sigma$. Application of a substitution can be written as $\mathbb{S}(\sigma)$ or equivalently $\sigma[\tau_i/\alpha_i]$. Substitutions can also be applied to type contexts in which case they are applied to each type in the context in turn. We take $\varnothing$ to denote the identity substitution.
\end{definition}

\begin{definition}[Composition]
  Let $\mathbb{S}\equiv[\tau_i/\alpha_i,\sigma_j/\beta_j]$ and $\mathbb{T}\equiv[\rho_j/\beta_j,\pi_k/\gamma_k]$, then define their composition by $\mathbb{S}\mathbb{T}\equiv[\tau_i/\alpha_i,\mathbb{S}(\rho_j)/\beta_j,\mathbb{S}(\pi_k)/\gamma_k]$. Applying the composition of two substitutions has the same effect as applying one, and then the other. That is to say, for all types $\varphi$, $\mathbb{ST}(\varphi)\equiv\mathbb{S}(\mathbb{T}(\varphi))$.
\end{definition}

\begin{definition}[Instance]
  A type $\sigma$ is said to be an instance of another type $\tau$ iff there exists a substitution $\mathbb{S}$ s.t. $\mathbb{S}(\tau)\equiv\sigma$.
\end{definition}

\begin{definition}[Principal Type]
  Given a term $t$ in our language, we say that it has principal type $\tau$ when $\Gamma\vdash t : \tau$ for some context $\Gamma$, and if $\Delta\vdash t : \tau^{\prime}$ for some context $\Delta$, then $\tau^{\prime}$ is an instance of $\tau$.
\end{definition}

Exactly what constitutes a type and what constitutes a deduction of a type judgement differs between type theories, but the above definitions always apply.

\section{Hindley and Milner's Type System}\label{sec:hm}

We begin our search with the Hindley--Milner (henceforth HM) type system\ \cite{10.2307/1995158, MILNER1978348}. This theory forms the basis of many production quality type systems, including those found in \textit{Haskell} and the \textit{ML} family of languages.

HM builds on the types in the simply-typed $\lambda$ calculus by introducing \textit{universally quantified} variables in prenex form (Definition\ \ref{def:hm-types}). This allows us to describe the types of polymorphic functions. For example, the identity function \texttt{define id(x) = x;} has principal type $\forall\alpha\ldotp(\alpha)\to\alpha$.

\begin{definition}[Types in HM]\label{def:hm-types}
  Types in our adaptation of HM are defined by:
  \begin{align*}
    \sigma & \Coloneqq~\forall\alpha\ldotp\sigma~|~\tau
    \tag*{\scriptsize(types)}
    \\\tau & \Coloneqq~\alpha~|~\iota~|~[\,\tau\,]~|~(\,\pi\,)\to\tau
    \tag*{\scriptsize(quantifier-free types)}
    \\\iota & \Coloneqq~\mathbf{num}~|~\mathbf{str}~|~\mathbf{atom}~|~\mathbf{bool}
    \tag*{\scriptsize(base types)}
    \\\pi & \Coloneqq~\tau_1,\tau_2,\ldots,\tau_n
    \tag*{\scriptsize$n\geq 0$\quad(formal parameters)}
    \\\alpha & \Coloneqq~\alpha_1~|~\alpha_2~|~\cdots
    \tag*{\scriptsize(variables)}
  \end{align*}

\end{definition}

This type theory is a good starting point for many reasons: It has a reasonably efficient inference algorithm which has been proven sound and complete w.r.t. the type system, the ability to specify polymorphic types affords a greater degree of flexibility, and given only a term, it is possible to infer its most general (principal) type. The last point is of particular importance to us because our underlying language was originally dynamically typed, so there is no facility in the syntax to provide type annotations.

\subsection{Algorithm}\label{sec:hm-algorithm}

A clear exposition of a type inference algorithm for HM, Algorithm $\mathcal{W}$, is given in\ \cite{damas1982principal}, where it is described as operating on $\lambda$ terms augmented with \texttt{let} bindings. Given a context $\Gamma$, and a term $t$, the algorithm returns a substitution $\mathbb{S}$ and type $\tau$ such that $\mathbb{S}(\Gamma)\vdash t:\tau$ is a principal deduction of $t$, if such a deduction exists (i.e. If $t$ is typable).

As in\ \cite{damas1982principal}, we rely on Robinson's unification algorithm and the ability to produce the closure of a type w.r.t. a context.

\begin{definition}[Robinson's Unification Algorithm, $\mathcal{U}$]
  Given two types, $\tau$ and $\sigma$, $\mathcal{U}(\tau, \sigma) = \mathbb{U}$ where $\mathbb{U}(\tau)\equiv\mathbb{U}(\sigma)$ and $\forall\mathbb{S}\ldotp\mathbb{S}(\tau)\equiv\mathbb{S}(\sigma)\implies\exists~\mathbb{S}^\prime\ldotp\mathbb{S}\equiv\mathbb{S}^\prime\mathbb{U}$ if and only if such a most general unifier $\mathbb{U}$ exists.
\end{definition}

\begin{definition}[Closure]
  $\overline{\Gamma}(\tau) = \forall\alpha_1,\ldots,\alpha_n\ldotp\tau$ where $\alpha_1,\ldots,\alpha_n$ are all the variables that appear free in $\tau$ but do not appear in the domain of $\Gamma$.
\end{definition}

We extend the algorithm for our needs, to deal with literals, recursion, sequencing, conditionals, and case expressions. For the most part these extensions are the common ones used by most practical implementations of HM, so we touch on only a few below.

\textbf{Algorithm $\mathcal{W}$:}

$(\mathbb{S},\tau)\gets\mathcal{W}(\Gamma\vdash t)$ where
\begin{enumerate}[(i)]
  \item $t\equiv f(e_1,\ldots,e_k)$\hfill{\scriptsize(function applications)}
    \\[.5em] \begin{math}
      \arraycolsep=1.5pt
      \begin{array}{llll}
        \text{let} & (\mathbb{S}_0,\tau^\prime_0) & \gets & \mathcal{W}(\Gamma\vdash f)
        \\ & (\mathbb{S}_i,\tau^\prime_i) & \gets & \mathcal{W}(\mathbb{S}_{i-1}\ldots\mathbb{S}_{0}(\Gamma)\vdash e_i)
        \\ & \phantom{(}\mathbb{U} & \gets & \mathcal{U}(\mathbb{S}_k\ldots\mathbb{S}_1(\tau^\prime_0),~(\mathbb{S}_k\ldots\mathbb{S}_2(\tau^\prime_1),\ldots,\tau^\prime_k)\to\beta) \text{ ($\beta$ fresh)}
      \end{array}
    \end{math}
    \\[.5em] $\mathbb{S}\equiv\mathbb{U}\mathbb{S}_k\ldots\mathbb{S}_0$ and $\tau\equiv\mathbb{U}(\beta)$.
    \\[1em] Unlike languages such as \textit{Haskell} where the true arity of a function is hidden (and often very difficult to ascertain for compiler and programmer alike), \textit{GeomLab} separates functions of different arities by syntax. As such, it is now a type error to partially apply a function.

  \item $t\equiv \texttt{let $x$ = $e_1$ in $e_2$}$\hfill{\scriptsize(\textit{recursive} let expressions)}
    \\[.5em] \begin{math}
    \arraycolsep=1.5pt
    \begin{array}{llll}
      \text{let} & (\mathbb{S}_1,\tau_1) & \gets & \mathcal{W}(\Gamma,x:\beta\vdash e_1) \text{ ($\beta$ fresh)}
      \\ & \phantom{(}\mathbb{U} & \gets & \mathcal{U}(\mathbb{S}_1(\beta),~\tau_1)
      \\ & \phantom{(}\Gamma^\prime,~\tau^\prime_1 & \gets & \mathbb{US}_1(\Gamma),~\mathbb{U}(\tau_1)
      \\ & (\mathbb{S}_2, \tau_2) & \gets & \mathcal{W}(\Gamma^\prime,x:\overline{\Gamma^\prime}(\tau^\prime_1)\vdash e_2)
    \end{array}
    \end{math}
    \\[.5em] $\mathbb{S}\equiv\mathbb{S}_2\mathbb{US}_1$ and $\tau\equiv\tau_2$
    \\[1em] Bindings in \textit{let} expressions may be recursive, that is to say $e_1$ may refer to $x$. Accordingly, when inferring a type for $e_1$, we add $x : \beta$ to the type context, for a fresh type variable $\beta$. Following this, we ``tie the knot'' by unifying $\beta$ with $e_1$'s type.
    \\[1em] Also note that by type checking $e_2$ with $x : \overline{\Gamma^\prime}(\tau^\prime_1)$ in the context, free variables in the type we inferred for $x$ that do not appear in the context $\Gamma^{\prime}$ have been universally quantified, and each instance of $x$ in $e_2$ may substitute them with different variables.
    \\[1em] This means that $x$ may be treated \textit{polymorphically} in the body of the let expression, but monomorphically in its own definition. This is specifically to forbid \textit{polymorphic recursion} as type inference in its presence is known to be undecidable~\cite{henglein1993type}.

  \item $t\equiv \texttt{case $c$ of } pat_1\to e_1;\cdots ;pat_k\to e_k$\hfill{\scriptsize(case expressions)}
    \\[.5em] \begin{math}
    \arraycolsep=1.5pt
    \begin{array}{llll}
      \text{let} & \phantom{(}\tau_0 & \gets & \alpha \text{ ($\alpha$ fresh)}
      \\ & (\mathbb{S}_0,\tau^{\prime}) & \gets & \mathcal{W}(\Gamma\vdash c)
      \\ & (\mathbb{S}_i, \tau_i) & \gets & \mathcal{P}(pat_i, e_i)
      \\ & \phantom{(}\rho_i & \gets & \mathbb{S}_{i-1}\ldots\mathbb{S}_1(\tau^{\prime})
      \\ & \phantom{(}\Delta_i & \gets & \mathbb{S}_{i-1}\ldots\mathbb{S}_0(\Gamma)
    \end{array}
    \end{math}

    $\mathbb{S}\equiv\mathbb{S}_k\ldots\mathbb{S}_0$ and $\tau\equiv\tau_k$.
    \\[1em] As our desugaring procedure removes nested patterns in favour of nested case expressions, our rule here only needs to deal with patterns that are one constructor deep. For each such pattern, we create the smallest type that contains any expression that could match it ($\mathcal{P}$ defined below), and we unify all of these with the type of the case argument. To get the type of the expression, we unify the types of all the $e_i$'s.
    \\[1em] $\mathcal{P}(pat_i, e_i)$ is defined as:
    \begin{enumerate}[(a)]
    \item $pat_i$ a numeric, string, bool or atom pattern\hfill{\scriptsize(literal pattern)}
      \\[.2em] \begin{math}
        \arraycolsep=1.5pt
        \begin{array}{llll}
          \text{let} & \phantom{(}\mathbb{U} & \gets & \mathcal{U}(\rho_i,~\mathbf{num})\text{ ($\mathbf{str}$, $\mathbf{bool}$,  $\mathbf{atom}$ respectively)}
          \\ & (\mathbb{S}^\prime,\tau^\prime) & \gets & \mathcal{W}(\mathbb{U}(\Delta_i)\vdash e_i)
          \\ & \phantom{(}\mathbb{U}^\prime & \gets & \mathcal{U}(\mathbb{S}^\prime\mathbb{U}(\tau_{i-1}), \tau^\prime)
        \end{array}
      \end{math}
      \\[.2em] $\mathbb{S}_i\equiv\mathbb{U}^\prime\mathbb{S}^\prime\mathbb{U}$ and $\tau_i\equiv\mathbb{U}^\prime(\tau^\prime)$

    \item $pat_i\equiv v$\hfill{\scriptsize(variable pattern)}
      \\[.2em] \begin{math}
        \arraycolsep=1.5pt
        \begin{array}{llll}
          \text{let} & (\mathbb{S}^\prime,\tau^\prime) & \gets & \mathcal{W}(\Delta_i,v:\rho_i\vdash e_i)
        \end{array}
      \end{math}
      \\[.2em] $\mathbb{S}_i\equiv\mathbb{S}^\prime$ and $\tau_i\equiv\tau^{\prime}$

    \item $pat_i\equiv[\,]$\hfill{\scriptsize(nil pattern)}
      \\[.2em] \begin{math}
        \arraycolsep=1.5pt
        \begin{array}{llll}
          \text{let} & \phantom{(}\mathbb{U} & \gets & \mathcal{U}(\rho_i,~[\alpha])\text{ ($\alpha$ fresh) }
          \\ & (\mathbb{S}^\prime,\tau^\prime) & \gets & \mathcal{W}(\mathbb{U}(\Delta_i)\vdash e_i)
          \\ & \phantom{(}\mathbb{U}^\prime & \gets & \mathcal{U}(\mathbb{S}^\prime\mathbb{U}(\tau_{i-1}),~\tau^\prime)
        \end{array}
      \end{math}
      \\[.2em] $\mathbb{S}_i\equiv\mathbb{U}^\prime\mathbb{S}^\prime\mathbb{U}$ and $\tau_i\equiv\mathbb{U}^\prime(\tau^\prime)$

    \item $pat_i\equiv(h:t)$\hfill{\scriptsize(cons pattern)}
      \\[.2em] \begin{math}
        \arraycolsep=1.5pt
        \begin{array}{llll}
          \text{let} & \phantom{(}\mathbb{U} & \gets & \mathcal{U}(\rho_i,~[\alpha])\text{ ($\alpha$ fresh)}
          \\ & (\mathbb{S}^\prime,\tau^\prime) & \gets & \mathcal{W}(\mathbb{U}(\Delta_i,h:\alpha,t:[\alpha])\vdash e_i)
          \\ & \phantom{(}\mathbb{U}^\prime & \gets & \mathcal{U}(\mathbb{S}^\prime\mathbb{U}(\tau_{i-1}),~\tau^\prime)
        \end{array}
      \end{math}
      \\[.2em] $\mathbb{S}_i\equiv\mathbb{U}^\prime\mathbb{S}^\prime\mathbb{U}$ and $\tau_i\equiv\mathbb{U}^\prime(\tau^\prime)$
    \end{enumerate}
    Although this is a common type semantics for case expressions, it poses some problems. For instance, a pattern that expects only \texttt{[]} will also purport to accept cons cells, when doing so would cause an exception at runtime (The very thing a type system aims to avoid).
    \\[1em] In other languages, catching such errors is the job of \textit{exhaustiveness checking}, which verifies that if one of a type's constructors appears in a case expression as a pattern, then they must all be covered. This also relies on knowing which constructors belong to which types\footnote{Verifying exhaustiveness is also known to be an NP-Complete problem, so we are keen to avoid relying upon it.}. In Section~\ref{sec:adapt-hm}, we will suggest an alternative treatment that exposes exhaustiveness as a property of types, by changing their representation.
\end{enumerate}

\subsection{Implementation}

Inference for HM is known to be \textsc{DExpTime}--Complete\ \cite{kfoury90mlexptime}, but type assignment for typical programs written by human programmers does not tend to meet this bound. However, \text{na\"ive} implementations --- in which types are represented as strings and all operations are performed eagerly --- can still be greatly improved upon. Oleg Kiselyov's tutorial on the implementation of \textit{OCaml}'s type inference algorithm\ \cite{oleg13ocamltc} suggests changes that, in concert can bring the performance of type assignment, in the typical case, much closer to linear time. We explain the techniques we have employed in our own implementation in the following sections.

\subsubsection{Unification}\label{sec:unify-impl}

Algorithms $\mathcal{W}$ and $\mathcal{U}$ in Section\ \ref{sec:hm-algorithm} are expressed as pure functions working explicitly with substitutions. Whilst this presentation is useful to show their exact operation, when translated directly into an implementation, they introduce some inefficiencies:
\begin{enumerate}[(i)]
\item Applying a substitution often results in repeated work:
  \begin{align}\label{eqn:unify-same-op}
    ((\alpha\to\alpha)\to\alpha\to\alpha)[\mathbf{num}/\alpha]\equiv(\mathbf{num}\to\mathbf{num})\to\mathbf{num}\to\mathbf{num}
  \end{align}
  $\alpha$ is replaced by \textbf{num} in 4 separate instances when using a string representation.
\item Substitution copies the type, even though often we do not need to keep the original.
\item The programmer must work hard to ensure the substitutions are applied consistently, and in the correct order. This is a cognitive --- not runtime --- overhead, but is also important.
\end{enumerate}
These issues are addressed by representing types by directed acyclic graphs (DAGs), and modifying types in place instead of returning a unifier. To unify two non-variable types, we checking their outermost constructors match, then pairwise unify their children, and to unify a variable with another type, we replace the variable (in-place) with a forward pointer to the type. Using forward pointers is much cheaper than string substitution, and structural sharing also ensures that we will substitute each variable only once (Figure\ \ref{fig:type-dag}).

Long chains of forward pointers may form when unifying variables together. When a chain is traversed, we replace all the intermediary pointers with a pointer directly to the end of the path (Figure\ \ref{fig:path-compress}). This technique is analagous to \textit{path compression} in disjoint set data structures\ \cite[\S21]{Cormen:2001:IA:580470}.

\begin{figure}[htbp]
  \caption{Representing types as DAGs, to take advantage of structural sharing. The substitution in Equation~\ref{eqn:unify-same-op} now occurs at only one site, where the variable is replaced by a \textit{forward pointer}.}\label{fig:type-dag}
  \begin{center}
    \begin{tikzcd}[column sep=small]
      & \to \ar[ld] \ar[rd] & &&&&&&& & \to \ar[ld] \ar[rd] &\\
        \to \ar[rd, out=225, in=180,] \ar[rd] & & \to \ar[ld] \ar[ld, out=315, in=0]
      & \phantom{.}\ar[rrrr,Mapsto,"{[\mathbf{num}/\alpha]}"] &&&& \phantom{.} &
      & \to \ar[rd, out=225, in=180,] \ar[rd] & & \to \ar[ld] \ar[ld, out=315, in=0] \\
      & \alpha & &&&&&&& & \mathbf{\cdot} \ar[d, dashed] &\\
      &        & &&&&&&& & \mathbf{num} &
    \end{tikzcd}
  \end{center}
\end{figure}

\begin{figure}[htbp]
  \caption{Making chains of forward pointers and compressing them. (1) represents the type ${(\alpha\to\beta)\to\gamma\to\delta}$, (2) follows after applying the substitutions $[\beta/\alpha]$, $[\gamma/\beta]$, $[\delta/\gamma]$, $[\mathbf{num}/\delta]$ in that order. (3) follows after path compression.}\label{fig:path-compress}
  \begin{equation*}
    \begin{tikzcd}[column sep=1ex,row sep=tiny]
      &&& \to\ar[lld]\ar[rrd] &&& \\
      & \to\ar[ld]\ar[rd] &&(1)&& \to\ar[ld]\ar[rd] & \\
      \alpha && \beta && \gamma && \delta
    \end{tikzcd}
    \hspace{2em}
    \begin{tikzcd}[column sep=1ex,row sep=tiny]
      &&& \to\ar[lld]\ar[rrd] &&& \\
      & \to\ar[ld]\ar[rd] &&(2)&& \to\ar[ld]\ar[rd] & \\
      \cdot\ar[rr,dotted] && \cdot\ar[rr,dotted] && \cdot\ar[rr,dotted] && \cdot\ar[rr,dotted] && \mathbf{num}
    \end{tikzcd}
  \end{equation*}
  \begin{equation*}
    \begin{tikzcd}[column sep=1ex,row sep=tiny]
      &&& \to\ar[lld]\ar[rrd] &&& \\
      & \to\ar[ld]\ar[rd] &&(3)&& \to\ar[ld]\ar[rd] & \\
      \cdot\ar[rrrd,dotted] && \cdot\ar[rd,dotted] && \cdot\ar[ld,dotted] && \cdot\ar[llld,dotted]\\
      &&& \mathbf{num} &&&
    \end{tikzcd}
  \end{equation*}
\end{figure}

\subsubsection{Occurs Check}

A sub-routine of Robinson's unification algorithm is the \textit{occurs check}: Before substituting a type for a variable, we check that the variable does not occur anywhere in the type that is replacing it. This step prevents us from creating cyclic types, but by throwing caution to the wind and not doing it, we can improve performance, as it is such a common operation.

For the most part, type inference is run on correct programs\footnote{Even in undergraduate functional programming courses.}, and furthermore, most type errors are not due to cyclic types, so we expect the number of occurs check failures we will miss to be low. Nevertheless, we should make up for not performing the occurs check by detecting cyclic types in other parts of the program. We detect these lazily in functions that recurse over the structure of types by leaving breadcrumbs at every node we enter, and removing them before we leave. If we find a crumb at a node we have just entered, we know we have doubled back on ourselves (finding a cycle), so we throw an error.

\subsubsection{Generalisation}\label{sec:gen}

When type checking a \texttt{let} expression or top-level definition, $e$, after inferring a type for the expression being defined, we take its \textit{closure} by universally quantifying any remaining free type variables (see the algorithm above). This process is referred to as \textit{generalisation} and the variables quantified by it are said to be \textit{owned} by $e$.

A \text{na\"ive} algorithm traverses the entire type being closed over, searching for unbound variables. We can prune the traversal, by annotating each type with the \textit{level} of a \texttt{let} expression or definition, where a \texttt{let} expression's level increases with nesting (cf. de Bruijn indices). Variables are annotated with the level of the expression that owns them, and compound types are annotated with the max level of any variable they mention. Then when closing over a type for a definition at level $l$, we only traverse compound types with level $l^\prime$ if $l^\prime\geq l$.

\subsubsection{Instantiation}

We can extend this pruning approach to also deal with \textit{instantiation}: The process of replacing quantified (type) variables with fresh (type) variables, done when type checking a bound (term) variable; In some senses an inverse of \textit{generalisation}.

By annotating types with a flag that is true when the type contains a quantified variable, when traversing for instantiation, we need only look at types where this flag is set. In our implementation, instead of a flag we use a special level, call it $\top$, such that for all levels $l\in\mathbb{N}$, $l<\top$. As we generalise a type, every variable we touch has its level set to $\top$, and the rules for propogating levels to compound types takes care of the rest.

\subsubsection{Level Adjustments}

In Section\ \ref{sec:gen} we introduced levels, but we did not cover how to combine them when unifying two types. To motivate the discussion, let us see what happens if we ignore levels during unification:

\texttt{define$^0$ id(x) = let$^1$ y = x$^0$ in y$^1$;}

Initially, $x$ is introduced under the \texttt{define} with level $0$, whereas $y$ is introduced by the \texttt{let}, with level $1$. When we check the definition of $y$ we unify its type with $x$'s (say $x, y:\alpha$). Then, in generalising the type of $y$, we see that it is a variable with level $1$, and we are at level $1$, \textit{making it safe to universally quantify!}. In the body of the \texttt{let}, $y$ is used, and its universal type is instantiated with a fresh variable (call it $\beta$). This gives $id:\forall\alpha,\beta\ldotp\alpha\to\beta$, which is clearly unsound.

It was \textit{not} safe to universally quantify the type of $y$ because its type was shared with a variable from a lower level. To make sure this does not happen, given two types $\tau_1,\tau_2$ with levels $l_1,l_2$ respectively, we set their levels to $\min(l_1,l_2)$ after unification.

Because the level $l$ of a compound type $\tau$ is the max of its variables' levels, to adjust it to $l^{\prime}$ would involve traversing $\tau$ (Setting each variable's level to the $\min$ of its current value and $l^{\prime}$). Rather than do this eagerly, we put $(\tau,l,l^{\prime})$ in the $\mathit{delayed}$ set, to make note of the change.

\begin{para}
  When we wish to generalise the type $\tau$ of a definition at level $l$, we find
  \begin{align*}
    \{\sigma:(\sigma,l_o,l_n)\in\mathit{delayed},l_n < l \leq l_o\}
  \end{align*}
  and perform the adjustments on these and remove them from \textit{delayed}, because $\tau$ could share a variable with such a $\sigma$, and in performing the adjustment, the level of that variable will drop below $l$, stopping it from being generalised.
\end{para}

\subsection{Examples}

We now test our implementation on some small \textit{GeomLab} programs.

\clearpage
\subsubsection{\cmark~Basic Type Inference}

\HMExample{\texttt{(+10);}}{\input{aux/section_ast.tex}}{\texttt{num -> num}}

The algorithm arrives at the type for this expression by desugaring the operator section into an application of \texttt{\_rsect} applied to \texttt{+} and its second argument, when supplied with the appropriate types:

\texttt{%
  \_rsect :: (('a, 'b) -> 'c, 'b) -> 'a -> 'c\\
  + :: (num, num) -> num%
}

We provide these as part of the context in which every expression is typed, as they are built-in definitions.

\subsubsection{\xmark~Basic Type Error}

\ShortHMExample{\texttt{"foo"+"bar";}}{\ttfamily\footnotesize%

%TC:ignore
\textcolor{purple}{\underline{test/hm\_examples.geom:7:1: Error in the expression}}\newline

\qquad Failed to unify types:\newline
\-\qquad\qquad Expected: num\newline
\-\qquad\qquad Actual: \-\quad str\newline

\qquad Whilst trying to unify: \newline
\-\qquad\qquad\qquad\qquad\quad~(num, num) -> num \newline
\-\qquad\qquad\qquad with: (str, str) -> `a\newline

\textcolor{purple}{test/hm\_examples.geom:7:1: In the function application}\newline

\qquad ``foo''+``bar''
%TC:endignore
}

\textit{GeomLab} has separate operators for the numeric addition (\texttt{+}) and the string concatenation (\texttt{\^}). The assumption made by the programmer was that \texttt{+} is overloaded to deal with both, which the typechecker catches as a unification error (between \texttt{num} and \texttt{str}, which are not unifiable because they are distinct base types).

Without further context finding the source of the error is quite difficult. To help, we also provide the outermost types that were being unified at the time of the error, as these are usually what correspond to expressions in the source language. In this case, these are ${\texttt{(num, num) -> num}}$ --- the type of \texttt{+} --- and ${\texttt{(str, str) -> 'a}}$ --- a constraint on the type the programmer expected of \texttt{+}.

\subsubsection{\xmark~Arity Mismatch}

\ShortHMExample{\texttt{let k(x, y) = x in k(1);}}{\ttfamily\footnotesize%

%TC:ignore
\textcolor{purple}{\underline{test/hm\_examples.geom:11:1: Error in the expression}}\newline

\qquad Failed to unify types:\newline
\-\qquad\qquad Expected: ('d, 'e) -> 'd\newline
\-\qquad\qquad Actual: \-\quad num -> 'f\newline

\textcolor{purple}{test/hm\_examples.geom:11:20: In the body of the let expression}\newline

\qquad let k(x, y) = x in \textbf{\emph{\color{blue}k(1)}}
%TC:endignore
}

Unlike \textit{Haskell}, Multi-arity functions in \textit{GeomLab} are not curried by default, and as a result, they cannot be partially applied. The type system captures this constraint as a unification error.

\subsubsection{\xmark~Branch Unification}

\ShortHMExample{\texttt{if true then 1 else "foo";}}{\ttfamily\footnotesize%

%TC:ignore
\textcolor{purple}{\underline{test/hm\_examples.geom:9:1: Error in the expression}}\newline

\qquad Failed to unify types:\newline
\-\qquad\qquad Expected: num\newline
\-\qquad\qquad Actual: \-\quad str\newline

\textcolor{purple}{test/hm\_examples.geom:9:1: In the if expression}\newline

\qquad if true then 1 else "foo"
%TC:endignore
}

In order to assign a type to a conditional, we require that the \textit{then} and \textit{else} expression types are unifiable, but this is not \textit{necessary}. In this example, the condition is constantly \texttt{true}, so we know that we could safely assign the entire expression the type \texttt{num}. Unfortunately, we cannot take advantage of "degenerate" cases in general, because checking whether the condition is constant is not decidable (by a reduction from the halting problem).

Another possibility is that the types are not unifiable, but we condition on the resulting type at runtime:

\texttt{%
define a = if c then 0 else [];\\
define b = if numeric(a) then a + 1 else length(a) + 1;
}

HM has no way of describing ad-hoc type "unions", so there is no way to specify the type of \texttt{a}.

\subsubsection{\cmark~Higher-Order Functions}

\ShortHMExample{\texttt{define . (f, g) = function (x) f(g(x));}}{\texttt{. :: ('a -> 'b, 'c -> 'a) -> 'c -> 'b}}

Function composition is both polymorphic and higher-order: It will accept any two 1-ary functions where the domain of the first coincides with the co-domain of the second.

\subsubsection{\cmark~Patterns}

\HMExample{\input{aux/folds.tex}}{\input{aux/folds_ast.tex}}{\texttt{length :: ['a] -> num}}

Patterns used in case expressions are also used by the inference algorithm in constraining the types of formal parameters. Here, they are the only indication that \texttt{length} takes list parameters.

\subsubsection{\xmark~Lambda-Bound Polymorphism}

\ShortHMExample{%
  \texttt{define p(a, b) = function (c) c(a, b)}\newline
  \texttt{define f(j) = p(j(true), j(1));}\newline
  \texttt{f(function (x) x);}%
}{\ttfamily\footnotesize%

%TC:ignore
\textcolor{purple}{\underline{test/hm\_examples.geom:25:8: Error in the definition of 'f'}}\newline

\qquad Failed to unify types:\newline
\-\qquad\qquad Expected: bool\newline
\-\qquad\qquad Actual: \-\quad num\newline

\qquad Whilst trying to unify:\newline
\-\qquad\qquad\qquad\qquad\quad~bool -> 'f\newline
\-\qquad\qquad\qquad with: num -> 'g\newline

\textcolor{purple}{test/hm\_examples.geom:25:26: In the 2nd argument of the function application}\newline

\qquad p(j(true), \textbf{\emph{\color{blue}j(1)}})\newline

\textcolor{purple}{test/hm\_examples.geom:25:15: In the body of 'f'}\newline

\qquad p(j(true), j(1))
%TC:endignore
}

This valid \textit{GeomLab} program is untypable in HM. The issue is in the definition of \texttt{f}: Its parameter, \texttt{j}, is applied to both a \texttt{bool} and to a \texttt{num}, which causes a unification error. Whilst types may be polymorphic, within the body of a function its parameters may only be instantiated once.

Restricting the number of instantiations is equivalent to types being in \textit{prenex} form (all the universal quantifications outermost). With this restriction lifted, it is possible to assign a type to \texttt{f}: ${\forall\pi\ldotp(\forall\alpha\ldotp\alpha\to\alpha)\to((\mathbf{bool},\mathbf{num})\to\pi)\to\pi}$.

The theory supporting such types is referred to as \textit{System F}, and as can be seen, it is more expressive than HM. The downside to this expressivity is that inferring a most general type in \textit{System F} is undecidable\ \cite{wells1999typability}.

\subsubsection{\cmark~Let-Bound Polymorphism}

\ShortHMExample{%
  \texttt{let j(x) = x in p(j(true), j(1));}\newline
  \textit{NB.} \texttt{p} \textit{defined as above.}%
}{\texttt{((bool, num) -> 'a) -> 'a}}

This program stands in contrast to the above, as whilst it evaluates to the same value as the previous program, it \textit{is} typable. The reason for this is that polymorphic types bound to variables introduced by let-expressions \textit{can} be instantiated multiple times.

The fact that the latter program is typable and the former is not is of particular interest because in dynamically typed languages, $\mathbf{let}~x = e_1~\mathbf{in}~e_2$ is commonly implemented as sugar for $(\lambda x\ldotp e_2)e_1$.

\subsubsection{\xmark~Infinite Types}

\ShortHMExample{%
\texttt{define f(x) = f;}\newline
\texttt{define g(x) = g(g);}\newline
\texttt{define h(x) = p(h, h);}%
}{\ttfamily\footnotesize%

%TC:ignore
\textcolor{purple}{\underline{test/hm\_examples.geom:31:8: Error in the definition of 'f'}}\newline

\qquad Attempted to construct an infinite type!\newline
\-\qquad\qquad 'b -> '*\newline


\textcolor{purple}{\underline{test/hm\_examples.geom:32:8: Error in the definition of 'g'}}\newline

\qquad Attempted to construct an infinite type!\newline
\-\qquad\qquad '* -> 'c\newline


\textcolor{purple}{\underline{test/hm\_examples.geom:33:8: Error in the definition of 'h'}}\newline

\qquad Attempted to construct an infinite type!\newline
\-\qquad\qquad 'b -> (('*, '*) -> 'e) -> 'e
%TC:endignore
}

All these programs yield infinite types, which in our implementation are represented by cyclic data structures.
The implementation detects these cycles, and terminates, printing the types. When printing a cyclic type, if the (nominal) root node of the type is detected again, it is printed as the special variable \texttt{'*}.

\section{Ad-hoc Algebraic Data-types}\label{sec:adhoc-adts}

Often it is useful to "couple" data together. In many existing statically typed functional programming languages this is achieved by defining a new named data type, but a common technique in \textit{GeomLab} is to use \textit{lists}. For instance, to fully describe a rectangle requires two numbers:

```
define area([width, height]) = width * height;
```

Our existing typechecker infers the type ${\texttt{area :: [num] -> num}}$. The information that rectangles are \textit{pairs} of numbers has been lost. According to this type, \texttt{area} will accept a list of any size, but we know that it is only defined for lists of two elements.

This issue stems from our special treatment of \textit{nil} and \textit{cons}. Implicit in the definition of the algorithm is the assumption that they are used only to construct homogeneous lists (A list where every value has the same type). This precludes our idea of using lists to represent arbitrary product types.

We may also want to define \texttt{area}, not just for rectangles, but for other shapes too. Here we define it for squares represented by the length of their side (\texttt{s}).

```
define area([w, h]) = w * h
     | area(s)      = s * s;
```

\begin{wrapfigure}{r}{0.3\textwidth}
  \caption{A union type for shapes.}\label{fig:shape-union}
  \begin{center}
    $[\mathbf{num},\mathbf{num}]\cup\mathbf{num}$
  \end{center}
\end{wrapfigure}

In HM, we unify all parameter patterns together. This means to infer a type for \texttt{area}, we must unify \textit{num} and \textit{cons} patterns, which is not possible.

In this section, we will investigate extensions to HM that allow us to specify product and union types in an ad-hoc manner, thus lifting this restriction (Figure\ \ref{fig:shape-union}).

\subsection{Products}

As mentioned earlier, in the dynamically typed setting we have always had a way to couple data together through the use of the cons cell; it was only by introducing HM that we lost this ability!

We may make a bid to recover it now by freeing the nil (\texttt{[]}) and cons (\texttt{(:)}) constructors from the list type, so that each may inhabit its own type. This corresponds to a change in our type grammar, and the addition of some proof rules to our version of HM (\text{Figures~\ref{fig:prod-ty-grammar}\,\&\,\ref{fig:prod-ty-rules}}).

\begin{figure}[htbp]
  \caption{Modifications to the HM grammar for types (Definition~\ref{def:hm-types}) to separate the list type into its constituent constructors.}\label{fig:prod-ty-grammar}
  \begin{align*}
    \tau & \Coloneqq~\cdots~|~\cancel{[\,\tau\,]}~|~\tau_1:\tau_2
    \tag*{\scriptsize(quantifier-free types)}
    \\\iota & \Coloneqq~\cdots~|~[\,]
    \tag*{\scriptsize(base types)}
  \end{align*}
\end{figure}

\begin{figure}[htbp]
  \caption{New proof rules in HM for cons and nil types. Note that, as $:$ has now become overloaded to mean both the cons type constructor, and the separator in a type judgement, from now on, we will use $::$ to denote the latter.}\label{fig:prod-ty-rules}
  \begin{prooftree}
    \AXC{}
    \RightLabel{\scriptsize($[\,]$-intro)}
    \UIC{$\vdash [\,] :: [\,]$}
  \end{prooftree}
  \begin{prooftree}
    \AXC{$\Gamma\vdash t_1 :: \tau_1$}
    \AXC{$\Gamma\vdash t_2 :: \tau_2$}
    \RightLabel{\scriptsize($(:)$-intro)}
    \BIC{$\Gamma\vdash (t_1:t_2) :: (\tau_1:\tau_2)$}
  \end{prooftree}

  We also modify the \texttt{case}-intro rule, however, in Section~\ref{sec:hm-algorithm}, this is presented not in a natural deduction style, but as part of algorithm $\mathcal{W}$ and its sub-routine $\mathcal{P}$, so we show the changes to the latter here.\\[-.6em]

  $(\mathbb{S}_i,\tau_i)\gets\mathcal{P}(pat_i,e_i)$ where, when:
  \begin{enumerate}[(a)]
    \item $pat_i\equiv[\,]$\hfill{\scriptsize(nil pattern)}
      \\[.2em] \begin{math}
        \arraycolsep=1.5pt
        \begin{array}{llll}
          \text{let} & \phantom{(}\mathbb{U} & \gets & \mathcal{U}(\rho_i,[\,])
          \\ & (\mathbb{S}^\prime,\tau^\prime) & \gets & \mathcal{W}(\mathbb{U}(\Delta_i)\vdash e_i)
          \\ & \phantom{(}\mathbb{U}^\prime & \gets & \mathcal{U}(\mathbb{S}^\prime\mathbb{U}(\tau_{i-1},~\tau^\prime)
        \end{array}
      \end{math}
      \\[.2em] $\mathbb{S}_i\equiv\mathbb{U}^\prime\mathbb{S}^\prime\mathbb{U}$ and $\tau_i\equiv\mathbb{U}^\prime(\tau^\prime)$
    \item $pat_i\equiv(h:t)$\hfill{\scriptsize(cons pattern)}
      \\[.2em] \begin{math}
        \arraycolsep=1.5pt
        \begin{array}{llll}
          \text{let} & \phantom{(}\mathbb{U} & \gets & \mathcal{U}(\rho_i,\alpha:\beta)\text{ ($\alpha$, $\beta$ fresh)}
          \\ & (\mathbb{S}^\prime,\tau^\prime) & \gets & \mathcal{W}(\mathbb{U}(\Delta_i, h::\alpha,t::\beta)\vdash e_i)
          \\ & \phantom{(}\mathbb{U}^\prime & \gets & \mathcal{U}(\mathbb{S}^\prime\mathbb{U}(\tau_{i-1},~\tau^\prime)
        \end{array}
      \end{math}
      \\[.2em] $\mathbb{S}_i\equiv\mathbb{U}^\prime\mathbb{S}^\prime\mathbb{U}$ and $\tau_i\equiv\mathbb{U}^\prime(\tau^\prime)$
  \end{enumerate}
\end{figure}

Now, when the type checker sees either \texttt{[]} or \texttt{(:)}, it makes no assumptions as to the data structure being built. When faced with \texttt{area}:

```
define area([width, height]) = width * height;
```

It will happily assign it the type $(\mathbf{num}:(\mathbf{num}:[\,]))\to\mathbf{num}$, or, by lifting list literals to the type-level $[\mathbf{num}, \mathbf{num}]\to\mathbf{num}$.

Unfortunately, we have lost the ability to typecheck lists, for two reasons. Firstly, now that nil and cons inhabit distinct types, any case expression with both nil and cons patterns causes a unification error, because we enforce the rule that patterns of case expressions be unifiable. Secondly, if we define a recursive function over lists (e.g. \texttt{length}), it will cause the tail of the list to be unified with the list itself, creating a cyclic type; something else HM prohibits. The first of these issues is addressed immediately --- in \text{Section~\ref{sec:unions}} --- below, and the second will be dealt with in \text{Section~\ref{sec:recursive}}.

\subsection{Unions}\label{sec:unions}

Having split the list type apart, we now need a way to reconstitute it. Our first attempt involves adding a completely unrestricted union operator, ${\tau\Coloneqq\cdots~|~\tau_1\cup\tau_2~|~\cdots}$, and a typing rule that is referred to as \textit{subsumption}.

\begin{definition}[Subsumption]
  Subsumption is the rule that a term inhabits all the super-types of its type.
  \begin{prooftree}
    \AXC{$\Gamma\vdash e::\tau$}
    \AXC{$\tau\prec\sigma$}
    \RightLabel{\scriptsize(sub)}
    \BIC{$\Gamma\vdash e::\sigma$}
  \end{prooftree}
\end{definition}

Intrinsic to subsumption is the subtyping relation between types.

\begin{definition}[Subtyping relation ($\prec$)]\label{def:subtyping}
  $\cup$ is an associative, commutative, idempotent binary operator and $\prec$ is a reflexive, transitive relation, with the following interesting cases:\\
  \begin{minipage}[t]{.4\textwidth}
    \vspace{.5em}
    \begin{prooftree}
      \AXC{$\tau_1\prec\sigma_1$}
      \AXC{$\tau_2\prec\sigma_2$}
      \RightLabel{\scriptsize(cons)}
      \BIC{$(\tau_1:\tau_2)\prec(\sigma_1:\sigma_2)$}
    \end{prooftree}
  \end{minipage}
  \begin{minipage}[t]{.6\textwidth}
    \vspace{.5em}
    \begin{prooftree}
      \AXC{$\sigma_1\prec\tau_1$}
      \AXC{$\cdots$}
      \AXC{$\sigma_k\prec\tau_k$}
      \AXC{$\rho\prec\pi$}
      \RightLabel{\scriptsize(arr)}
      \QIC{$(\tau_1,\ldots,\tau_k)\to\rho~\prec~(\sigma_1,\ldots,\sigma_k)\to\pi$}
    \end{prooftree}
  \end{minipage}
  \begin{minipage}[t]{.33\textwidth}
    \vspace{1em}
    \begin{prooftree}
      \AXC{$\tau\prec\rho$}
      \AXC{$\sigma\prec\rho$}
      \RightLabel{\scriptsize($\cup$-left)}
      \BIC{$(\tau\cup\sigma)\prec\rho$}
    \end{prooftree}
  \end{minipage}
  \begin{minipage}[t]{.33\textwidth}
    \vspace{1em}
    \begin{prooftree}
      \AXC{$\tau\prec\sigma$}
      \RightLabel{\scriptsize($\cup$-right)}
      \UIC{$\tau\prec(\sigma\cup\rho)$}
    \end{prooftree}
  \end{minipage}
  \begin{minipage}[t]{.33\textwidth}
    \vspace{1em}
    \begin{prooftree}
      \AXC{\phantom{$\tau\prec\sigma$}}
      \RightLabel{\scriptsize(inst)}
      \UIC{$(\forall\alpha\ldotp\tau)\prec\tau[\sigma/\alpha]$}
    \end{prooftree}
  \end{minipage}
\end{definition}

These additions highlight some interesting interactions between existing features of the type system and subtyping. For instance, subtyping for function types is contravariant in parameter types, and covariant in the return type. This fits our intuition: it is safe to treat ${(\mathbf{num}\cup\mathbf{bool})\to\mathbf{num}}$ as though it were ${\mathbf{num}\to(\mathbf{num}\cup\mathbf{bool})}$, because, in words, we are promising to feed only numbers to a function that accepts numbers and booleans, and we are prepared to receive numbers (which it produces) and bools (which it does not) from it.

\begin{para}
  Also interesting (and encouraging) is the fact that HM's instantiation is a special case of subsumption:
  \begin{align*}
    \begin{mathprooftree}
      \AXC{$\Gamma\vdash t::\forall\alpha\ldotp\tau$}
      \LeftLabel{\scriptsize(instantiation)}
      \UIC{$\Gamma\vdash t::\tau[\sigma/\alpha]$}
    \end{mathprooftree}
    \triangleq
    \begin{mathprooftree}
      \AXC{$\Gamma\vdash t::\forall\alpha\ldotp\tau$}
      \AXC{}
      \RightLabel{\scriptsize(inst)}
      \UIC{$(\forall\alpha\ldotp\tau)\prec\tau[\sigma/\alpha]$}
      \RightLabel{\scriptsize(sub)}
      \BIC{$\Gamma\vdash t::\tau[\sigma/\alpha]$}
    \end{mathprooftree}
  \end{align*}
  But, consider the types $(\mathbf{num}\cup\mathbf{bool}):\mathbf{str}$ and $(\mathbf{num}:\mathbf{str})\cup(\mathbf{bool}:\mathbf{str})$. Intuitively, they are equivalent so it should hold that they are subtypes of each other, but while it is possible to prove that:
  \begin{align*}
    (\mathbf{num}:\mathbf{str})\cup(\mathbf{bool}:\mathbf{str})\prec(\mathbf{num}\cup\mathbf{bool}):\mathbf{str}
  \end{align*}
  The converse cannot be derived. To see why, let us have a look at an attempted proof (other attempted proofs will follow a similar pattern):
  \begin{prooftree}
    \AXC{$\vdots$}
    \UIC{$(\mathbf{num}\cup\mathbf{bool})\prec\mathbf{num}$}
    \AXC{}
    \RightLabel{\scriptsize(refl)}
    \UIC{$\mathbf{str}\prec\mathbf{str}$}
    \RightLabel{\scriptsize(cons)}
    \BIC{$(\mathbf{num}\cup\mathbf{bool}):\mathbf{str}\prec\mathbf{num}:\mathbf{str}$}
    \RightLabel{\scriptsize($\cup$-right)}
    \UIC{$(\mathbf{num}\cup\mathbf{bool}):\mathbf{str}\prec(\mathbf{num}:\mathbf{str})\cup(\mathbf{bool}:\mathbf{str})$}
  \end{prooftree}
  This example highlights a limitation of our $\prec$ rules. By inspecting a proof goal (an assertion that $\tau_1\prec\tau_2$), we want to determine which rule to apply --- in reverse --- to simplify it. The proof rules of simply typed $\lambda$ calculus and HM can both be used in such a goal-directed fashion\footnote{In both cases, the goal is directed by the syntax of the program, in turn.} to make efficient inference algorithms, and so can the current $\prec$ rules, but introducing new cases to describe how $(:)$ factors through $\cup$ to cover the case in our example adds ambiguity, and inefficiency in turn. Our solution will be to restrict ourselves to \textit{discriminative} unions \text{(Definition~\ref{def:discrim})} \cite{mishra1985declaration,cartwright1991soft}.
\end{para}

\begin{definition}[Discriminative Union]\label{def:discrim}
  A union type is considered discriminative when none of its summands are type variables and each of its inhabitting terms may be projected into one of the union's summands by looking only at its outermost data constructor's type. For the purposes of this discussion $\mathbf{num}$, $\mathbf{bool}$, and $\mathbf{atom}$ can be considered unary data constructors and $[\,]$ can be considered a nullary data constructor.
\end{definition}

$(\mathbf{num}:\mathbf{str})\cup(\mathbf{bool}:\mathbf{str})$ is not discriminative because both summands have a $(:)$ constructor outermost, but $(\mathbf{num}\cup\mathbf{bool}):\mathbf{str}$ is. In general, because we can no longer have two summands in a union with a $(:)$ constructor outermost, factoring is no longer a problem. Moreover, many useful terms have discriminative types, such as \texttt{area}:

```
define area([w, h]) = w * h
     | area(s)      = s * s;
```

with type $([\mathbf{num},\mathbf{num}]\cup\mathbf{num})\to\mathbf{num}$.

\subsection{R\'emy Encoding}\label{sec:remy}

It is possible to implement type assignment with discriminative union types just by changing the type representation. This idea was first expounded \text{in~\cite{cartwright1991soft}} as an adaptation of Didier \text{R\'emy's} encoding of record types\ \cite{Remy/records91}.

\begin{para}
  The encoding assumes that we have a finite number of constructors and this is not true in \textit{GeomLab}, in which functions of differing arities are considered to have different constructors. In \text{Section~\ref{sec:wildcard}} we will fix this limitation, but for now, we will restrict ourselves to functions with one parameter.

  Suppose we have
  \begin{align*}
    \mathcal{F} & = \{+,-\}
    \tag*{Flags}\\
    \mathcal{V} & = \{\alpha,\beta,\gamma,\ldots\}
    \tag*{Variables}\\
    \mathcal{C} & = \{\mathbf{num},~\mathbf{bool},~\mathbf{atom},~\mathbf{str},~[\,],~(:),~(\to)\}
    \tag*{Constructors}\\
    a_x & =
    \begin{cases}
      2 & \text{ if }x\in\{(:), (\to)\}\\
      0 & \text{ if }x\in\mathcal{C}\setminus\{(:), (\to)\}
    \end{cases}
    \tag*{Arities}
    \intertext{Then a R\'emy encoded type $\rho\in\mathcal{T}$ has the form:}
    \rho & = \mathcal{R}(f_{\mathbf{num}};~f_{\mathbf{bool}};~f_{\mathbf{atom}};~f_{\mathbf{str}};~f_{[\,]};~f_{(:)}, c^1_{(:)}, c^2_{(:)};~f_{(\to)}, c^1_{(\to)}, c^2_{(\to)})
    \tag{$\dagger$}\label{eqn:remy}
    \intertext{where}
    f_x & \in\mathcal{F}\cup\mathcal{V}
    \tag*{Flag parameter for constructor $x\in\mathcal{C}$.}\\
    c^i_x & \in\mathcal{T}\cup\mathcal{V}
    \tag*{$i^{\text{\tiny th}}$ Child type for constructor $x\in\mathcal{C}$.}
    \intertext{An instance of this encoding does not represent just one type, but instead describes a set of feasible types. Suppose $\tau$ is feasible w.r.t. $\rho$'s constraints, then, for any $x\in\mathcal{C}$,}
    f_x = + & \implies x(\gamma^1_x,\ldots,\gamma^{a_x}_x)\subseteq\tau\\
    f_x = - & \implies x(\gamma^1_x,\ldots,\gamma^{a_x}_x)\cap\tau = \varnothing\\
    \gamma^i_x & \text{ is feasible w.r.t. $c^i_x$'s constraints.}
  \end{align*}
  When a flag parameter $f_x$ is a variable, it indicates that $\rho$ does not constrain whether or not $x(\gamma^1_x,\ldots,\gamma^{a_x}_x)$ is in the type. Variables in child types have their usual meaning as type variables.
\end{para}

\subsubsection{Examples}

Suppose we wish to represent the supertypes of $\mathbf{num}\cup\mathbf{bool}$ using \text{R\'emy} encoding\footnote{$\star$ is a fresh variable whose symbol is not relevant, and changes at every instantiation.}:

\makebox[\textwidth][c]{%
\begin{math}
  \begin{array}{rrrrrrrrrrrrrl}
    && f_{\mathbf{num}} & f_{\mathbf{bool}} & f_{\mathbf{atom}} & f_{\mathbf{str}} & f_{[\,]} & f_{(:)} & c^1_{(:)} & c^2_{(:)} & f_{(\to)} & c^1_{(\to)} & c^2_{(\to)}\\
    \phantom{\varepsilon:} & \mathcal{R}( & +; & +; & \star; & \star; & \star; & \star & \star & \star; & \star & \star & \star & )\\
  \end{array}
\end{math}}

$f_{\mathbf{num}} = + = f_{\mathbf{bool}}$ indicates that satisfying types \textit{must} include $\mathbf{num}$ and $\mathbf{bool}$. Every other flag parameter is assigned a fresh variable because we \textit{do not care} whether other types are included: a supertype of $\mathbf{num}\cup\mathbf{bool}$ may or may not include $\mathbf{str}$, for example.

Similarly, subtypes of $(\mathbf{num}:\mathbf{bool})$ (Given by $\alpha$):

\makebox[\textwidth][c]{%
\begin{math}
  \begin{array}{rrrrrrrrrrrrrl}
    && f_{\mathbf{num}} & f_{\mathbf{bool}} & f_{\mathbf{atom}} & f_{\mathbf{str}} & f_{[\,]} & f_{(:)} & c^1_{(:)} & c^2_{(:)} & f_{(\to)} & c^1_{(\to)} & c^2_{(\to)}\\
    \alpha: & \mathcal{R}( & -; & -; & -; & -; & -; & \star & \beta & \gamma; & - & \star & \star & )\\
    \beta:  & \mathcal{R}( & \star; & -; & -; & -; & -; & - & \star & \star; & - & \star & \star & )\\
    \gamma: & \mathcal{R}( & -; & \star; & -; & -; & -; & - & \star & \star; & - & \star & \star & )\\
  \end{array}
\end{math}}

Concentrating on $\alpha$, we specify that for any ${x\in\mathcal{C}\setminus\{(:)\}}$, $x$ \textit{must not} be included in the type, by setting $f_x = -$. The child types of $(:)$ ensure that when $(\tau:\sigma)$ is included in the type, $\tau$ and $\sigma$ must satisfy $\beta$ and $\gamma$ respectively, and, $f_{(:)}$ is a fresh variable --- we \textit{do not care} whether $(\tau:\sigma)$ is included in the type --- because both $\varnothing$ (the empty type) and $\mathbf{num}\cup\mathbf{bool}$ are subtypes of $\mathbf{num}\cup\mathbf{bool}$.

Finally, the supertypes of the \texttt{area} function (Given by $\alpha$):

\makebox[\textwidth][c]{%
\begin{math}
  \begin{array}{rrrrrrrrrrrrrl}
    && f_{\mathbf{num}} & f_{\mathbf{bool}} & f_{\mathbf{atom}} & f_{\mathbf{str}} & f_{[\,]} & f_{(:)} & c^1_{(:)} & c^2_{(:)} & f_{(\to)} & c^1_{(\to)} & c^2_{(\to)}\\
    \alpha:      & \mathcal{R}( & \star; & \star; & \star; & \star; & \star; & \star & \star & \star; & + & \beta & \gamma & )\\
    \beta:       & \mathcal{R}( & \star; & -; & -; & -; & -; & \star & \delta & \varepsilon; & - & \star & \star & )\\
    \gamma:      & \mathcal{R}( & +; & \star; & \star; & \star; & \star; & \star & \star & \star; & \star & \star & \star & )\\
    \delta:      & \mathcal{R}( & \star; & -; & -; & -; & -; & - & \star & \star; & - & \star & \star & )\\
    \varepsilon: & \mathcal{R}( & -; & -; & -; & -; & -; & \star & \zeta & \eta; & - & \star & \star & )\\
    \zeta:       & \mathcal{R}( & \star; & -; & -; & -; & -; & - & \star & \star; & - & \star & \star & )\\
    \eta:        & \mathcal{R}( & -; & -; & -; & -; & \star; & - & \star & \star; & - & \star & \star & )\\
  \end{array}
\end{math}}

The return type ($\gamma$) of \texttt{area} is not satisfied just by $\mathbf{num}$ but also by any \textit{supertype} of $\mathbf{num}$. Conversely, the parameter type ($\beta$) is constrained to be a \textit{subtype} of $[\mathbf{num}, \mathbf{num}]\cup\mathbf{num}$. This fits our definition of subtyping between function types (Definition\ \ref{def:subtyping}): A supertype of \texttt{area} has a larger return type and a smaller parameter type.

\subsubsection{Notation}

Always dealing with \text{R\'emy} encodings in the form given in Equation\ \ref{eqn:remy} can be cumbersome, we adopt a more compact notation for typical cases. Again we use $\star$ to refer to fresh variables (each instance is distinct from all others).

Suppose we have \textit{distinct} constructors $\{x_1,\ldots,x_k\}=\mathcal{X}\subseteq\mathcal{C}$ and \text{R\'emy} encodings $\gamma_1^1,\ldots,\gamma_1^{a_{x_1}},\ldots,\gamma_k^{a_{x_k}}\in\mathcal{T}\cup\mathcal{V}$.

\begin{definition}[Supertype encoding]\label{def:super-encode}
  \begin{flalign*}
  \left[\bigcup_{i=1}^kx_i(\gamma_i^1,\ldots,\gamma_i^{a_x})\right]^{\uparrow} & = \rho\in\mathcal{T}&&
  \intertext{Suppose $\rho$ has the form in Equation~\ref{eqn:remy}, then}
  f_x & =
  \begin{cases}
    + & \text{ if } x\in\mathcal{X}\\
    \star & \text{ otherwise}
  \end{cases}&&\\
  c^j_x & =
  \begin{cases}
    \gamma_i^j & \text{ if } x = x_i\in\mathcal{X}\\
    \star & \text{ otherwise}
  \end{cases}&&\\
  \end{flalign*}
\end{definition}

\begin{definition}[Subtype encoding]\label{def:sub-encode}
  \begin{flalign*}
  \left[\bigcup_{i=1}^kx_i(\gamma_i^1,\ldots,\gamma_i^{a_x})\right]^{\downarrow} & = \rho\in\mathcal{T}&&
  \intertext{Suppose $\rho$ has the form in Equation~\ref{eqn:remy}, then}
  f_x & =
  \begin{cases}
    \star & \text{ if } x\in\mathcal{X}\\
    - & \text{ otherwise}
  \end{cases}&&\\
  c^j_x & =
  \begin{cases}
    \gamma_i^j & \text{ if } x = x_i\in\mathcal{X}\\
    \star & \text{ otherwise}
  \end{cases}&&\\
  \end{flalign*}
\end{definition}

This notation also interacts sensibly with the list literal syntax, so that $[\tau_1,\ldots,\tau_k]^{\uparrow}\equiv(\tau_1:\cdots:(\tau_k:[\,]^{\uparrow})^{\uparrow}\cdots)^{\uparrow}$, and similarly for the subset encoding.

The examples in the previous section now have much more compact, recognisable representations:
\begin{tabular}{l|l}
  Supertypes of $\mathbf{num}\cup\mathbf{bool}$ & $(\mathbf{num}\cup\mathbf{bool})^{\uparrow}$\\[.5em]
  Subtypes of $(\mathbf{num}:\mathbf{bool})$ & $(\mathbf{num}:\mathbf{bool})^{\downarrow}$\\[.5em]
  Supertypes of the \texttt{area} function & $(([\mathbf{num}, \mathbf{num}]\cup\mathbf{num})^{\downarrow}\to\mathbf{num}^{\uparrow})^{\uparrow}$ \\
\end{tabular}

\subsection{Adapting HM}\label{sec:adapt-hm}

The beauty of this encoding is that, if we treat $\mathcal{R}$ as a constructor, and flag parameters as types, then \text{R\'emy} encoded types may be combined using Robinson's unification algorithm: Two \text{R\'emy} types are unified by unifying their flag parameters and child types, whilst a variable $v$ is unified with another term $t$ (so long as $v$ appears free in $t$) by substituting $t$ for $v$.

All the necessary changes are in Algorithm $\mathcal{W}$: Previously, we assigned each expression its most general type. Now, we assign each expression a set of constraints over its type, so, we should ensure that these are, in some sense, the most general constraints. What follows is an adaption of Algorithm $\mathcal{W}$ that we will dub $\mathcal{W_R}$, we touch on only the cases which differ.

\textbf{Algorithm $\mathcal{W_R}$\footnote{Incidentally, the classes of expression mentioned in the new rules for $\mathcal{W_R}$ can be split into two groups: Constructing terms, such as literals and abstractions, and consuming terms, such as function applications and case expressions. In these rules, the former are bounded from below (through use of the supertype encoding) whilst the latter are bounded from above (using the subtype encoding).}:}

$(\mathbb{S},\tau)\gets\mathcal{W_R}(\Gamma\vdash t)$ where
\begin{enumerate}[(i)]
  \item
    \begin{enumerate}[(a)]
      \item $t$ a number, string, boolean, atom or nil literal\hfill{\scriptsize(literals)}
        \\[.5em] $\mathbb{S}\equiv\varnothing$ and \colorbox{lightgray}{$\tau\equiv\mathbf{num}^{\uparrow},\mathbf{str}^{\uparrow},\mathbf{bool}^{\uparrow},\mathbf{atom}^{\uparrow},[\,]^{\uparrow}$} respectively.
      \item $t\equiv(a:b)$\hfill{\scriptsize(cons cells)}
        \\[.5em] \begin{math}
          \arraycolsep=1.5pt
          \begin{array}{llll}
            \text{let} & (\mathbb{S}_1,\tau^\prime_1) & \gets & \mathcal{W_R}(\Gamma\vdash a)
            \\ & (\mathbb{S}_2,\tau^\prime_2) & \gets & \mathcal{W_R}(\mathbb{S}_1(\Gamma)\vdash b)
          \end{array}
        \end{math}
    \\[.5em] $\mathbb{S}\equiv\mathbb{S}_2\mathbb{S}_1$ and \colorbox{lightgray}{$\tau\equiv(\mathbb{S}_2(\tau^{\prime}_1):\tau^{\prime}_2)^{\uparrow}$}.
    \end{enumerate}
  \item $t\equiv \texttt{function}\;(x)~e$\hfill{\scriptsize(abstractions)}
    \\[.5em] \begin{math}
      \arraycolsep=1.5pt
      \begin{array}{llll}
        \text{let} & (\mathbb{S}_1,\tau^\prime_1) & \gets & \mathcal{W}(\Gamma,x:\alpha\vdash e) \text{ ($\alpha$ fresh)}
      \end{array}
    \end{math}
    \\[.5em] $\mathbb{S}\equiv\mathbb{S}_1$ and \colorbox{lightgray}{$\tau\equiv(\mathbb{S}_1(\alpha)\to\tau^{\prime}_1)^{\uparrow}$}.
  \item $t\equiv f(e)$\hfill{\scriptsize(function applications)}
    \\[.5em] \begin{math}
      \arraycolsep=1.5pt
      \begin{array}{llll}
        \text{let} & (\mathbb{S}_0,\tau^\prime_0) & \gets & \mathcal{W_R}(\Gamma\vdash f)
        \\ & (\mathbb{S}_1,\tau^\prime_1) & \gets & \mathcal{W_R}(\mathbb{S}_{0}(\Gamma)\vdash e)
        \\ & \phantom{(}\mathbb{U} & \gets & \mathcal{U}(\mathbb{S}_1(\tau^\prime_0),~\colorbox{lightgray}{$(\tau^\prime_1\to\beta)^{\downarrow}$}) \text{ ($\beta$ fresh)}
      \end{array}
    \end{math}
    \\[.5em] $\mathbb{S}\equiv\mathbb{U}\mathbb{S}_1\mathbb{S}_0$ and $\tau\equiv\mathbb{U}(\beta)$.
    \\[1em] We are restricted to functions with one parameter by the limitations of our current encoding.

  \item $t\equiv \texttt{case $c$ of } pat_1\to e_1;\cdots ;pat_k\to e_k$\hfill{\scriptsize(case expressions)}
    \\[.5em] \begin{math}
    \arraycolsep=1.5pt
    \begin{array}{llll}
      \text{let} & \phantom{(}\tau_0 & \gets & \colorbox{lightgray}{$\star$}
      \\ & (\mathbb{S}_0,\tau^{\prime}) & \gets & \mathcal{W_R}(\Gamma\vdash c)
      \\ & (\mathbb{S}_i,\tau_i) & \gets & \colorbox{lightgray}{$\mathcal{A}(pat_i,e_i)$}
      \\ & \phantom{(}\rho_i & \gets & \mathbb{S}_{i-1}\ldots\mathbb{S}_1(\tau^{\prime})
      \\ & \phantom{(}\Delta_i & \gets & \mathbb{S}_{i-1}\ldots\mathbb{S}_0(\Gamma)
      \\ & \phantom{(}\gamma & \gets & \colorbox{lightgray}{$\mathcal{C}(\{pat_1,\ldots,pat_k\})$}
      \\ & \phantom{(}\mathbb{U} & \gets & \colorbox{lightgray}{$\mathcal{U}(\rho_k,\gamma)$}
    \end{array}
    \end{math}

    $\mathbb{S}\equiv\mathbb{U}\mathbb{S}_k\ldots\mathbb{S}_0$ and $\tau\equiv\tau^{\prime}_k$.
    \\[1em] When type checking a case expression, first we unify together the types of each arm's body. This forms the type of the entire expression.
    \\[1em] $\mathcal{A}(pat_i, e_i)$ is defined as:
    \begin{enumerate}[(a)]
    \item $pat_i$ a numeric, string, bool, atom or nil pattern\hfill{\scriptsize(literal pattern)}
      \\[.2em] \begin{math}
        \arraycolsep=1.5pt
        \begin{array}{llll}
          \text{let} & (\mathbb{S}^\prime,\tau^\prime) & \gets & \mathcal{W_R}(\Delta_i\vdash e_i)
          \\ & \phantom{(}\mathbb{U} & \gets & \mathcal{U}(\mathbb{S}^\prime(\tau_{i-1}), \tau^\prime)
        \end{array}
      \end{math}
      \\[.2em] $\mathbb{S}_i\equiv\mathbb{U}\mathbb{S}^\prime$ and $\tau_i\equiv\mathbb{U}(\tau^\prime)$

    \item $pat_i\equiv v$\hfill{\scriptsize(variable pattern)}
      \\[.2em] \begin{math}
        \arraycolsep=1.5pt
        \begin{array}{llll}
          \text{let} & (\mathbb{S}^\prime,\tau^\prime) & \gets & \mathcal{W_R}(\Delta_i,v : \rho_i\vdash e_i)
          \\ & \phantom{(}\mathbb{U} & \gets & \mathcal{U}(\mathbb{S}^\prime(\tau_{i-1}), \tau^\prime)
        \end{array}
      \end{math}
      \\[.2em] $\mathbb{S}_i\equiv\mathbb{U}\mathbb{S}^\prime$ and $\tau_i\equiv\mathbb{U}(\tau^\prime)$

    \item $pat_i\equiv(h : t)$ \hfill{\scriptsize(cons pattern)}
      \\[.2em] \begin{math}
        \arraycolsep=1.5pt
        \begin{array}{llll}
          \text{let} & (\mathbb{S}^\prime,\tau^\prime) & \gets & \mathcal{W_R}(\Delta_i,h:\gamma^1_i, t:\gamma^2_i \vdash e_i) \text{ ($\gamma^1_i,\gamma^2_i$ fresh)}
          \\ & \phantom{(}\mathbb{U} & \gets & \mathcal{U}(\mathbb{S}^\prime(\tau_{i-1}), \tau^\prime)
        \end{array}
      \end{math}
      \\[.2em] $\mathbb{S}_i\equiv\mathbb{U}\mathbb{S}^\prime$ and $\tau_i\equiv\mathbb{U}(\tau^\prime)$
    \end{enumerate}

    Then, we constrain the type of the expression being matched upon by looking at each arm's pattern.
    \begin{flalign*}
      \mathcal{C}(pats) & = \left[ \bigcup_{x(\gamma^1,\ldots,\gamma^{a_x})\in\llbracket pats\rrbracket}x(\gamma^1,\ldots,\gamma^{a_x}) \right]^{\downarrow} &&\\
      \intertext{If there is a variable pattern, the case could match against an expression with any outermost constructor, otherwise, in the absence of a variable pattern, we may say that the matched term's outermost constructor must be one of those mentioned in the case.}
      \llbracket pats\rrbracket & =
      \begin{cases}
        \left\{ \overline{pat_i} : pat_i\in pats, pat_i\text{ not a variable} \right\}\oplus\mathcal{P} & \text{ if $v$ a variable, }v\in pats\\
        \left\{ \overline{pat_i} : pat_i\in pats\right\} & \text{ otherwise}
      \end{cases}&&\\
      \mathcal{P} & = \{\mathbf{num}, \mathbf{str}, \mathbf{bool}, \mathbf{atom}, [\,], (\star:\star),\star\to\star \} &&\\
      X\oplus Y & = \{ x(\gamma^1,\ldots,\gamma^{a_x}) : x\in\mathcal{C},\text{ if }x(\gamma^1,\ldots,\gamma^{a_x})\in X \text{ else if }x(\gamma^1,\ldots,\gamma^{a_x})\in Y\}
      \intertext{Note that $\overline{pat_i}$'s cons pattern branch uses type variables $\gamma^1_i$ and $\gamma^2_i$ which are introduced in $\mathcal{A}$'s cons pattern branch (above).}
      \overline{pat_i} & =
      \begin{cases}
        \mathbf{num} & \text{ if $pat_i$ is a numeric pattern}\\
        \mathbf{str} & \text{ if $pat_i$ is a string pattern}\\
        \mathbf{bool} & \text{ if $pat_i$ is a boolean pattern}\\
        \mathbf{atom} & \text{ if $pat_i$ is a atom pattern}\\
        [\,] & \text{ if $pat_i$ is a nil pattern}\\
        (\gamma^1_i:\gamma^2_i) & \text{ if $pat_i$ is a cons pattern}
      \end{cases}&&
    \end{flalign*}
\end{enumerate}

Recall the \texttt{head} function, from the introduction, and its desugaring:
```
define head(x:_) = x;

define head = function (xs)
  case xs of (x:y) -> x;
```
It is assigned the \text{R\'emy} encoding $\forall\alpha,\beta\ldotp((\alpha:\beta)^{\downarrow}\to\alpha)^{\uparrow}$. Rather than \textit{exhaustiveness checking} indicating that \texttt{head} should implement support for the $[\,]$ pattern, the parameter type has been bounded above to indicate that it is a type error to pass anything other than a cons cell to it: It is now the caller's responsibility to ensure that \texttt{head} is only applied to non-empty lists.

This does not obviate the need for exhaustiveness checking: If a case expression contains a numeric literal pattern (matching a single number), it still purports to support all numeric values because $\mathbf{num}$ is the smallest type that covers a numeric literal. But functions which are intended to work on only a part of a larger type (like \texttt{head}) are no longer considered partial.

\subsection{Case Types}\label{sec:case-types}

Discriminativity can be seen as a model by which the way terms are differentiated is lifted to the type level, but it is somewhat prescriptivist: If two types are structurally different, we must rush to make the difference known at the outermost constructor. Couple this with the fact that we have only finitely many constructors and we can already see that any union can have at most $\abs{\mathcal{C}}$ summands before we lose the ability to discriminate between them.

When faced with this simple (though contrived) function, Algorithm $\mathcal{W_R}$ runs into trouble:
```
define foo([b])    =  not b
     | foo([m, n]) = (m + n) > 0;

{ Desugared }
define foo = function (xs)
  case xs of
    (x:y) ->
    case y of
      []    -> not x
      (z:w) ->
      case w of
        []  -> x + z
```
\begin{para}
  \texttt{foo} accepts either a singleton list, whose element it treats as a boolean, or a two-element list whose elements it treats as numbers, and in both cases it returns a boolean, so the type we would like to assign is:
  \begin{align*}
    ([\mathbf{bool}]\cup[\mathbf{num}, \mathbf{num}])\to\mathbf{bool}
  \end{align*}
  Singleton lists and two-element are clearly structurally different, but all discriminativity looks at is the outermost constructor, which in both cases is $(:)$. If we attempt to force the situation and make the type discriminative, we may arrive at:
  \begin{align*}
    (((\mathbf{bool}\cup\mathbf{num})^{\downarrow}:([\,]\cup[\mathbf{num}])^{\downarrow})^{\downarrow}\to\mathbf{bool}^{\uparrow})^{\uparrow}
  \end{align*}
  But the parameter type is over-approximated to also include $[\mathbf{num}]$ and $[\mathbf{bool},\mathbf{num}]$: We have lost the property that the singleton list contains a boolean and the two-element list contains only numbers. In this section, we introduce a generalisation of \text{R\'emy} encoding that can express types with correlations without forgoing a discriminative representation.
\end{para}

Given a term $t :: [\mathbf{bool}]\cup[\mathbf{num},\mathbf{num}]$, we determine which summand it belongs to at runtime by deconstructing it using a case expression. For instance, in the desugaring of \texttt{foo}, when the type checker reaches the expression \texttt{not x} it has already been through two case expressions, so it knows that \texttt{xs} is a cons and \texttt{y} a nil. Similarly, when checking \texttt{x + z} we know that \texttt{xs} is a cons, \texttt{y} is a cons, and \texttt{w} is a nil: The type of \texttt{x} depends on whether \texttt{y} is a nil or a cons. We capture this idea by performing type inference and unification w.r.t. a \textit{case context} (Definition\ \ref{def:case-context}).

\begin{definition}[Case Context]\label{def:case-context}
  A case context $C$ is a partial mapping from type variables to constructors. Given a case context $C$, type variable $\alpha$ and constructor $c$, we write $C,\alpha\triangleright c$ to denote the map $C$ with its constructor for $\alpha$ overwritten with $c$. We use the uppercase Roman alphabet to refer to them, by convention.
\end{definition}

If types $\tau_1$ and $\tau_2$ are unified w.r.t. a context $C$, the implication is only that they are consistent with each other in $C$, and its sub-contexts (Definition\ \ref{def:sub-context}). This affords us the flexibility to treat a term as having different types in different contexts.

For example, in \texttt{foo} (desugared), supposing we refer to the types of variables as $\texttt{xs}::\alpha,\texttt{x}::\beta,\texttt{y}::\gamma,\texttt{w}::\varepsilon$, then it is no longer a type error to unify $\beta$ with $\mathbf{bool}$ in context $C\equiv\alpha\triangleright(:),\gamma\triangleright[\,]$ and also unify $\beta$ with $\mathbf{num}$ in context $D\equiv\alpha\triangleright(:),\gamma\triangleright(:),\varepsilon\triangleright[\,]$ because $C$ and $D$ disagree on $\gamma$ so are not sub-contexts of each other.

\begin{definition}[Sub Context]\label{def:sub-context}
  Given case contexts $C$ and $D$, we say that $D$ is a sub-context of $C$ when $D = C,\alpha_1\triangleright d_1,\ldots,\alpha_k\triangleright d_k$, for constructors $d_1,\ldots,d_k$, and type variables $\alpha_1,\ldots,\alpha_k$ \textit{free in }$C$, $k\geq 0$. This means that the context described by $D$ is nested within that described by $C$.
\end{definition}

We extend Algorithm $\mathcal{W_R}$ (Section\ \ref{sec:adapt-hm}) with case contexts to make $\mathcal{W_{RC}}$. The first modification introducing case contexts as a parameter to type assignment $\mathcal{W_{RC}}(\Gamma;C\vdash t)$. In most cases, this parameter is passed on to recursive calls unchanged. The exception to this rule is in the definition of $\mathcal{A}(pat_i,e_i)$ (concerned with the type checking the arms of a case expression):

\begin{enumerate}[(a)]
  \item $pat_i$ a numeric, string, bool, atom or nil pattern\hfill{\scriptsize(literal pattern)}
    \\[.2em] \begin{math}
      \arraycolsep=1.5pt
      \begin{array}{llll}
        \text{let} & (\mathbb{S}^\prime,\tau^\prime) & \gets & \colorbox{lightgray}{$\mathcal{W_{RC}}(\Delta_i;C,\rho_i\triangleright\mathbf{num}\vdash e_i)$ (\textbf{str}, \textbf{bool}, \textbf{atom}, $[\,]$ respectively)}
        \\ & \phantom{(}\mathbb{U} & \gets & \mathcal{U}(\mathbb{S}^\prime(\tau_{i-1}), \tau^\prime)
      \end{array}
    \end{math}
    \\[.2em] $\mathbb{S}_i\equiv\mathbb{U}\mathbb{S}^\prime$ and $\tau_i\equiv\mathbb{U}(\tau^\prime)$

  \item $pat_i\equiv v$\hfill{\scriptsize(variable pattern)}
    \\[.2em] \begin{math}
      \arraycolsep=1.5pt
      \begin{array}{llll}
        \text{let} & (\mathbb{S}^\prime,\tau^\prime) & \gets & \colorbox{lightgray}{$\mathcal{W_{RC}}(\Delta_i,v : \rho_i; C\vdash e_i)$}
        \\ & \phantom{(}\mathbb{U} & \gets & \mathcal{U}(\mathbb{S}^\prime(\tau_{i-1}), \tau^\prime)
      \end{array}
    \end{math}
    \\[.2em] $\mathbb{S}_i\equiv\mathbb{U}\mathbb{S}^\prime$ and $\tau_i\equiv\mathbb{U}(\tau^\prime)$

  \item $pat_i\equiv(h : t)$ \hfill{\scriptsize(cons pattern)}
    \\[.2em] \begin{math}
      \arraycolsep=1.5pt
      \begin{array}{llll}
        \text{let} & (\mathbb{S}^\prime,\tau^\prime) & \gets & \colorbox{lightgray}{$\mathcal{W_{RC}}(\Delta_i,h:\gamma^1_i, t:\gamma^2_i; C,\rho_i\triangleright(:) \vdash e_i)$}\text{ ($\gamma^1_i,\gamma^2_i$ fresh)}
        \\ & \phantom{(}\mathbb{U} & \gets & \mathcal{U}(\mathbb{S}^\prime(\tau_{i-1}), \tau^\prime)
      \end{array}
    \end{math}
    \\[.2em] $\mathbb{S}_i\equiv\mathbb{U}\mathbb{S}^\prime$ and $\tau_i\equiv\mathbb{U}(\tau^\prime)$
\end{enumerate}

In order to leverage the case contexts we have threaded through the algorithm, we must change the flag parameter representation (Definition\ \ref{def:flag-tree}) to allow us to represent the results of unification w.r.t. a context.

\begin{definition}[Flag Tree]\label{def:flag-tree}
  A represention of constraints in multiple contexts as a tree. Leaves are labelled as in Figure\ \ref{fig:flag-leaf} --- an extension of $\mathcal{F}$, whilst intermediate nodes are labelled by type variables and possess an edge for every constructor $c\in\mathcal{C}$. We use $\llbracket n\rrbracket$ to refer to a node's label and $\mathbb{E}(n, c)$ to refer to the target of the outgoing edge from intermediate node $n$ labelled by constructor $c$.
\end{definition}

\begin{figure}[htbp]
  \caption{Lattice of leaf flag values, (our new $\mathcal{F}$). $+$ and $-$ retain their meanings of \textit{must} and \textit{must not}, $\sim$ indicates no constraint (the join $+\sqcup-$), and $\bot$ indicates an inconsistent constraint or a type error (the meet $+\sqcap-$).}\label{fig:flag-leaf}
  \begin{center}
    \begin{tikzcd}
      & \sim \ar[ld, dash]\ar[rd, dash]&\\
      + \ar[rd, dash]&& - \ar[ld, dash]\\
      & \bot &
    \end{tikzcd}
  \end{center}
\end{figure}

\begin{definition}[Interpretation]\label{def:flag-tree-interp}
flag trees are interpreted as flag values $I(f)\in\mathcal{F}$, by joining the labels of their leaves:
\begin{align*}
  I(f) & =
  \begin{cases}
    \llbracket f\rrbracket & \text{ if $f$ is a leaf}\\
    \displaystyle\bigsqcup_{c\in\mathcal{C}} I(\mathbb{E}(f,c)) & \text{ otherwise}
  \end{cases}
\end{align*}
\end{definition}

\begin{definition}[Specialisation]\label{def:flag-tree-spec}
  A flag tree $f$ is specialised w.r.t. a context $C$:
\begin{align*}
  f\rvert_{C} & =
  \begin{cases}
  f & \text{ if $f$ is a leaf }\\
  \mathbb{E}(f, c)\rvert_C & \text{ if $\llbracket f\rrbracket\triangleright c\in C$}\\
  f^{\prime} & \text{ otherwise, where $\llbracket f^{\prime}\rrbracket\triangleq\llbracket f\rrbracket$ and $\mathbb{E}(f^{\prime}, c)\triangleq\mathbb{E}(f,c)\rvert_C$.}
  \end{cases}
\end{align*}
\end{definition}

Unification can no longer treat flag parameters like types. When unifying two non-variable flag parameters we \textit{merge} them (Definition\ \ref{def:flag-tree-merge}).

\begin{definition}[Merge]\label{def:flag-tree-merge}
  Merging flag trees $t_1$ and $t_2$ --- denoted $t_1\boxplus t_2$ --- produces a new tree $t_m$ that combines the information held in both. We make this precise by saying, for any context $C$, $I(t_m\rvert_C) = I(t_1\rvert_C)\sqcap I(t_2\rvert_C)$, and realise it in the definition:
\begin{enumerate}[(i)]
  \item If $t_1, t_2$ are leaves, then $t_m$ is a leaf s.t. $\llbracket t_m\rrbracket\triangleq\llbracket t_1\rrbracket\sqcap\llbracket t_2\rrbracket$.
  \item If w.l.o.g. $t_1$ is an intermediate node, then $t_m$ is an intermediate node s.t.
    \begin{align*}
      \llbracket t_m\rrbracket & \triangleq \llbracket t_1\rrbracket \\
      \mathbb{E}(t_m, c)       & \triangleq \mathbb{E}(t_1, c)\boxplus t_2\rvert_{\llbracket t_1\rrbracket\triangleright c}
    \end{align*}
\end{enumerate}
\end{definition}

Finally, introduced types must pay attention to context. For example, previously a numeric literal's type was constrained to be a supertype of \textbf{num}, now, it is a supertype of \textbf{num} w.r.t. $C$, the context it is being checked in. As all types are introduced using either the super- or sub-type encoding (Definitions\ \ref{def:super-encode},\ \ref{def:sub-encode}), we will alter them to incorporate a context. As the change is similar in both, we only show the new supertype encoding (Definition\ \ref{def:ctx-super-encode}).
\begin{definition}[Context-aware Supertype Encoding]\label{def:ctx-super-encode}
  \begin{flalign*}
  \left[\bigcup_{i=1}^kx_i(\gamma_i^1,\ldots,\gamma_i^{a_x})\right]^{\uparrow}_{\colorbox{lightgray}{$C$}} & = \rho\in\mathcal{T}&&
  \intertext{Suppose $\rho$ has the form in Equation~\ref{eqn:remy}, then}
  f_x & =
  \begin{cases}
    \colorbox{lightgray}{$t_0$} & \text{ if } x\in\mathcal{X}\\
    \star & \text{ otherwise}
  \end{cases}&&\\
  c^j_x & =
  \begin{cases}
    \gamma_i^j & \text{ if } x = x_i\in\mathcal{X}\\
    \star & \text{ otherwise}
  \end{cases}&&\\
  \intertext{Suppose we impose an arbitrary ordering on the case context,}
  C & = \alpha_0\triangleright c_1,\ldots,\alpha_{k-1}\triangleright c_{k-1}\\
  \intertext{Then, we define our flag tree by}
  \llbracket t_i\rrbracket & = \alpha_i \tag*{$0\leq i < k$}\\
  \llbracket t_k\rrbracket & = +\\
  \mathbb{E}(t_i, c) & =
  \begin{cases}
    t_{i+1} & \text{ if $0\leq i < k$ and $c = c_i$}\\
    l      & \text{ if $0\leq i < k$ where $\llbracket l\rrbracket =\;\sim$}
  \end{cases}
  \end{flalign*}
\end{definition}

\subsection{Decorrelation}

In some instances, correlations between types are undesirable. For example\footnote{\texttt{eq} uses features such as multi-arity functions (Section~\ref{sec:wildcard}) and recursive types (Section~\ref{sec:recursive}) which we have not properly covered yet. They are not immediately relevant to the discussion at hand.} (adapted from\ \cite{mishra1985declaration}):
```
define eq([],    [])    = true
     | eq([]:xs, []:ys) = eq(xs, ys);
```
Given two lists of nils, \texttt{eq} is supposed to return \texttt{true} if they are the same length and \texttt{false} otherwise. The definition we gave may appear to match this specification, but it is incomplete: It does not deal with the case where the two lists are of unequal length. A better definition might be\footnote{%
In a typical statically typed functional programming language, we may have written:
\begin{Verbatim}
define eq([], [])       = true
     | eq([]:xs, []:ys) = eq(xs, ys)
     | eq(_,     _)     = false;
\end{Verbatim}
But our type system says that this function accepts values of \textit{any} two types, and returns a boolean. This is technically true: The wildcard patterns will match terms of any type, but this generality hides the intent of the function. We restrict it by being more specific in our patterns.
}:
```
define eq([],    [])    = true
     | eq([]:_,  [])    = false
     | eq([],    []:_)  = false
     | eq([]:xs, []:ys) = eq(xs, ys);
```
In the first definition, the types that the second parameter (by convention) can inhabit rely upon those of the first parameter: The second parameter can only be $[\,]$ if the first parameter is, and likewise for the cons case. In the correct definition, this relationship is no longer present. Often, when parameter types are correlated, it is by accident.

It is also undesirable for a function's type to rely upon its parameters' types in recursive definitions. It is possible to write a function that is called recursively with different arities or return types in different contexts, but they are usually written in error, and we would rather catch these errors than say that the differences are permissible because they occur in different contexts.

To remove any relationships between types $\alpha$ and $\beta$, we \textit{decorrelate} (Definition\ \ref{def:decorrelation}) every flag parameter in $\alpha$'s encoding w.r.t. $\beta$ \textit{and any type reachable from $\beta$} and vice versa.

\begin{definition}[Decorrelation]\label{def:decorrelation}
  Given a flag tree $t$, and a type variable $\alpha$, the decorrelation of $t$ w.r.t. $\alpha$ --- $D(t,\alpha)$ --- is:
  \begin{align*}
    D(t,\alpha) & =
    \begin{cases}
      t
      & \text{ if $t$ is a leaf}\\
      \bigboxplus_{c\in\mathcal{C}}D(\mathbb{E}(t,c),\alpha)
      & \text{ if $t$ is a node and $\llbracket t \rrbracket=\alpha$}\\
      t^{\prime}
      & \text{ o/w, where $\llbracket t^{\prime}\rrbracket\triangleq\llbracket t\rrbracket$; $\mathbb{E}(t^{\prime}, c)\triangleq D(\mathbb{E}(t, c),\alpha)$}
    \end{cases}
  \end{align*}
  We stop the interpretation of $t$ from depending on $\alpha$ by replacing any node in the tree that conditions on $\alpha$'s constructors by the merge of all its children. The coherence condition met by this operation is that for any context $A$, $I(D(t,\alpha)\rvert_A) = \bigsqcap_{c\in\mathcal{C}}I(t\rvert_{A,\alpha\triangleright c})$.
\end{definition}

Algorithm $\mathcal{W_{RC}}$ employs decorrelation after assigning types to:
\begin{enumerate}[(i)]
\item Abstractions, to remove relationships between parameter types.
\item Recursive definitions, to prevent the definition's type relying on any type reachable from it. In this case, we do not decorrelate symmetrically as it is okay for a reachable type to rely on the definition's type.
\end{enumerate}

In the first definition of \texttt{eq}, the type of the second parameter was a subtype of $[\,]$ when the first parameter was $[\,]$, and a subtype of $(:)$ when the first parameter was $(:)$. After decorrelation, the second parameter type is constrained to be \textit{empty}. We do not treat empty types as errors, but an empty parameter type is suspicious: As there are no terms that inhabit this type, it is impossible to call the function!

\subsection{Optimisation}

\text{R\'emy} encodings represent constraints over types, not single types. Conversion to the latter is achieved through \textit{minimising substitution}\ \cite{cartwright1991soft}, but this is not always possible. For example:
```
define twice(f) = function (x) f(f(x));
```
Is assigned $((\alpha\to\alpha)^{\downarrow}\to(\alpha\to\alpha)^{\uparrow})^{\uparrow}$. Consequently, when applied to some $f$ constrained by $((\mathbf{num}\cup\mathbf{bool})^{\downarrow}\to\mathbf{num}^{\uparrow})^{\uparrow}$ unification yields constraints that are satisfied by both $(\mathbf{num}\cup\mathbf{bool})\to(\mathbf{num}\cup\mathbf{bool})$ and $\mathbf{num}\to\mathbf{num}$, which are incomparable. We have lost the ability to assign a principal type to every typable term, because the principal (most general) system of constraints of a typable term can include incomparable types.

\textit{Minimisation} and \textit{maximisation} are defined mutually recursively. Minimisation does nothing to variables, but to a \text{R\'emy} type, it minimises the flag parameters (in a sense that is made clear later), then minimises both children of $(:)$, maximises the left child of $(\to)$, and minimises its right child. The definition of maximisation is dual. Note, these processes can only produce optimal types when such optima exist, in practise, this has not been a considerable issue.

When flag parameters were just $+$, $-$ or variables, their minimisation amounted to replacing variables with $-$. Now they are trees, we must elaborate this algorithm: If the parameter is a variable, it is replaced with a leaf containing $-$, if it is a tree, every $\sim$ leaf is replaced with a $-$ leaf. Once again, maximisation of flag parameters is a dual process.

\subsection{Detecting Type Errors}

Suppose we have a flag parameter $f$ --- a tree --- and a context $C$ s.t. $I(f\rvert_C) = \bot$. We can infer that the subtype associated with $f$ is constrained inconsistently in context $C$. But this is not enough to suggest that there is a type error: it is possible that we may never find ourselves in context $C$. For example, consider the type-safe expression:
```
foo([true]);
```
\begin{para}
  Where \texttt{foo} is defined as in Section\ \ref{sec:case-types} (page\ \pageref{sec:case-types}). Before checking the application, the types appear as follows\footnote{Redundant contexts (such as $\alpha\triangleright(:)$) have been omitted from $\beta$ and $\gamma$ for brevity, and we take $\sim$ to be a unification operator.}:
  \begin{align*}
    \texttt{[true]} & :: [\mathbf{bool}^{\uparrow}]^{\uparrow} \\
    \texttt{foo}    & :: (\alpha\to\mathbf{bool}^{\uparrow})^{\uparrow} \\
    \alpha          & = (\beta:\gamma)^{\downarrow} \\
    \beta           & = \mathbf{bool}^{\downarrow}_{\gamma\triangleright[\,]}\sim\mathbf{num}^{\downarrow}_{\gamma\triangleright(:)} \\
    \gamma          & = ([\,]\cup[\mathbf{num}^{\downarrow}])^{\downarrow}
  \end{align*}
  Unifying the actual and formal parameters' types: $\alpha$ is constrained to be precisely $(\beta:\gamma)$ and $\gamma$ is constrained from below by $[\,]$ and above by $[\,]\cup[\mathbf{num}]$. Turning our attentions to $\beta$ --- unified with $\mathbf{bool}^{\uparrow}$ --- when $\gamma\triangleright[\,]$, $\beta$ is precisely $\mathbf{bool}$, but when $\gamma\triangleright(:)$, $\beta$ is lowerbounded by $\mathbf{bool}$ and upperbounded by $\mathbf{num}$. $f\rvert_{\gamma\triangleright(:)} = \bot$ where $f$ is the flag parameter associated with $\mathbf{bool}$ in $\beta$.
\end{para}

Type errors can no longer be discovered locally, but \textit{potential} type errors can. During unification, we make a note of any flag parameters whose trees contain inconsistent leaves. After we are done gathering constraints and optimising, we check whether any context resulting in an inconsistent constraint is realisable. In our example, after optimisation, $\gamma$ is precisely $[\,]$, so $\gamma\triangleright(:)$ is not realisable, meaning we are safe to ignore the inconsistency in $\beta$'s constraints as unreachable.

\subsection{Summary}

We began this section by dissociating constructors from each other (and from specific types). This allowed us to combine constructors how we pleased, which we facilitated using existing techniques\ \cite{cartwright1991soft,Remy/records91}. Type unions built in this way were required to be \textit{discriminative} (Definition\ \ref{def:discrim}). Unfortunately, many of the types we would have liked to combine, we could not, without violating discriminativity.

Every violating union is over-approximated by a discriminative type. For example, $(\mathbf{bool}:\mathbf{bool})\cup(\mathbf{num}:\mathbf{num})$ by $(\mathbf{bool}\cup\mathbf{num}):(\mathbf{bool}\cup\mathbf{num})$. But we cannot always replace one with the other --- over-approximating a function parameter's type could lead to the function being called on a value outside of its domain, so is in general, unsound.

As the example in the previous paragraph shows, over-approximation makes types discriminative by destroying correlations. We re-introduce them with \textit{case types}, which allow type constraints to be predicated upon the structure of other types. This information is maintained in a \textit{case context} (Definition\ \ref{def:case-context}) by looking at case expressions, drawing inspiration from how terms of differing structures are discriminated between at runtime.

It remains for us to tie a few loose ends. Firstly, by dissociating constructors from types, we lost the ability to type check recursive data structures! This is an egregious omission, which we will rectify immediately (Section\ \ref{sec:recursive}). Secondly, we required that our language have finitely many constructors to \text{R\'emy} encode its types. As it happens, this is neither true of \textit{GeomLab}, nor necessary for \text{R\'emy}'s encoding, so we can loosen this restriction (Section\ \ref{sec:tagged-variants}).

\section{Recursive Types}\label{sec:recursive}

In HM, the list was a recursive type that we had built in support for. We lost this support when we stopped treating $\texttt{[]}$ and $\texttt{(:)}$ as special, related constructors. Now, if we try to encode a list of type $\alpha$, we get: $[\,]\cup(\alpha:\lambda)$ where $\lambda$ refers back to the type we are defining, yielding an infinite (cyclic) type, which our typechecker balks at. Similarly, an attempt to construct a representation of binary trees using our existing machinery may look something like this:

```
[]        { Leaves }

[l, x, r] { Branch with datum `x`
          , left sub-tree `l`
          , and right sub-tree `r`
          }
```

But again, \texttt{l} and \texttt{r} are trees themselves. The ability to specify ad-hoc recursive types would make such expressions typable (Figure\ \ref{fig:rec-type}).

\begin{figure}[htbp]
  \caption{Types for lists and binary trees. $\mu$ introduces a recursive type such that $\mu x\ldotp\phi = \phi[(\mu x\,\ldotp\phi)/x]$.}\label{fig:rec-type}
  \begin{align*}
    \mu l & \ldotp[\,]\cup(\alpha:l) \\
    \mu t & \ldotp[\,]\cup[t,\alpha,t]
  \end{align*}
\end{figure}

\subsection{Circular Unification}

When we originally implemented unification (Section\ \ref{sec:unify-impl}) we explicitly forbade cyclic types, so, to a first degree approximation, our problem is resolved by removing the \textit{occurs check} and allowing unification to build circular types. In reality, the situation is not quite so simple. Consider the following example, adapted from\ \cite{colmerauer1982prolog}\footnote{For simplicity, we are not representing types by R\'emy encodings.}:

\begin{para}
  \abovedisplayskip=8pt
  \belowdisplayskip=8pt
  We start with type variables $\alpha, \beta, \gamma, \delta$ and unify $\alpha\sim[\gamma]$ and $\beta\sim[\delta]$:
  \begin{equation*}
    \begin{tikzcd}[sep=small]
             & \alpha\ar[d, dashed] &        &  &  &  &        & \beta\ar[d, dashed] & \\
             & (:)\ar[ld]\ar[rd]    &        &  &  &  &        & (:)\ar[ld]\ar[rd]   & \\
      \gamma &                      & {[\,]} &  &  &  & \delta &                     & {[\,]}
    \end{tikzcd}
  \end{equation*}
  Then we unify $\alpha\sim\delta$ and $\beta\sim\gamma$, creating a circular type.
  \begin{equation*}
    \begin{tikzcd}[sep=small]
                                      &                   & \alpha\ar[ld,dashed] \\
                                      & (:)\ar[ld]\ar[rd] &                      \\
      \gamma\ar[rdd,dashed]           &                   & {[\,]}               \\
                                      &                   & \beta\ar[ld,dashed]  \\
                                      & (:)\ar[ld]\ar[rd] &                      \\
      \delta\ar[uuuur,dashed,out=225] &                   & {[\,]}
    \end{tikzcd}
  \end{equation*}
  Now suppose we try to unify $\alpha\sim\beta$. Chasing forward pointers, this is tantamount to unifying $(\gamma:[\,])\sim(\delta:[\,])$. As this unification is between compound types with the same outermost constructor, we proceed to unify the children. $[\,]\sim[\,]$ is a trivial constraint, so we focus on $\gamma\sim\delta$. Another pointer chase shows that this is equivalent to $(\delta:[\,])\sim(\gamma:[\,])$, for which we must unify $\delta\sim\gamma$: Circular types have us going round in circles!

  To unify two distinct\footnote{\textit{Distinct} refers to pointer equality: $\tau_1$ is stored at a different location in memory to $\tau_2$.} compound types $\tau_1$ and $\tau_2$ with matching outermost constructor, we unify their children. If, however, after following all forwarding pointers, both types reside at the same memory location (are identical) then we know that we need not do any work. As we have seen, this check alone is not enough to stop unification diverging, but \text{G\'erard Huet} proposes an elegant solution\ \cite[\S5.7.2]{huet1976resolution}: \textit{Before} unifying the compound types' children replace one type with a forward pointer to the other. This is sound because, after unification, the two types will be identical in structure, and if the two types need to be unified again, the pointer equality check will stop us looping.

  When we attempt to unify $\alpha\sim\beta$ with the new algorithm, first we point $\beta$ to $\alpha$ (Left). Then we unify $\gamma\sim\delta$ as children of $\alpha$ and $\beta$ respectively, but noticing that they point to the same type, do nothing --- except compress $\gamma$'s path (Right):
  \begin{equation*}
    \begin{tikzcd}[sep=small]
      \beta\ar[d, dashed]             & \delta\ar[d, dashed] & \alpha\ar[ld, dashed] \\
      \cdot\ar[r, dashed, bend left]  & (:)\ar[ld]\ar[rd]    &                       \\
      \gamma\ar[u,dashed]             &                      & {[\,]}
    \end{tikzcd}
    \hspace{4em}
    \begin{tikzcd}[sep=small]
      \beta\ar[d, dashed]             & \delta\ar[d, dashed] & \alpha\ar[ld, dashed] \\
      \cdot\ar[r, dashed, bend left]  & (:)\ar[ld]\ar[rd]    &                       \\
      \gamma\ar[ur,dashed, bend left] &                      & {[\,]}
    \end{tikzcd}
  \end{equation*}
\end{para}

\section{Tagged Variants}\label{sec:tagged-variants}

In our \texttt{area} example, when we introduced squares, we were lucky that they had a different structure to our representation of rectangles (one number instead of a pair of numbers), but suppose now we wish to introduce circles, represented by their radius; How would we distinguish between circles and squares?

A common technique is to tag each kind of shape with a unique identifier, and check for these when matching patterns. For this we use \textit{GeomLab}'s atoms as their representation is legible to programmers, and their implementation yields fast equality checks:

```
define area([#rect, w, h]) = w * h
     | area([#square, s])  = s * s
     | area([#circle, r])  = PI * r * r;
```

The issue with this is \texttt{[\#square, s]} and \texttt{[\#circle, r]} both have a type of ${[\mathbf{atom}, \mathbf{num}]}$: Whilst squares and circles are distinguishable by their tags at the value level, they are not at the type level, so the function defined above would have the same type as this one:

```
define area([#rect, w, h]) = w * h
     | area([#square, s])  = s * s;
```

\begin{wrapfigure}[9]{l}{0.32\textwidth}
  \caption{Tagged union type for shapes.}\label{fig:shape-tagged}
  \begin{align*}
         & [\#\mathit{rect}, \mathbf{num}, \mathbf{num}] \\
    \cup & [\#\mathit{square}, \mathbf{num}] \\
    \cup & [\#\mathit{circle}, \mathbf{num}]
  \end{align*}
\end{wrapfigure}

This is not ideal, as the latter function will throw an error at runtime if applied to a circle. To get around this, we could lift atoms to the type level: Furnish every atom value with a corresponding type that only it inhabits. Then squares will have type $[\#\mathit{square}, \mathbf{num}]$, and circles $[\#\mathit{circle}, \mathbf{num}]$ (Figure\ \ref{fig:shape-tagged}).

\subsection{Wildcard Constructors}\label{sec:wildcard}

Lifting atoms to the type level creates an infinite family of constructors, which cannot be used in \text{R\'emy} encodings. However, we observe that any given program only mentions finitely many atom literals. Consequently, we adopt an encoding whereby a type splits infinite families into "constructors it has been exposed to" each with their own flag parameter and children, and "all other constructors" captured by a single \textit{wildcard} flag parameter.

When a type, $\tau$, is exposed to a new constructor from an infinite family (for example, through unification with another type), we update its flag parameter in $\tau$ by copying the appropriate wildcard and initialise its children in $\tau$ with fresh types (Figure\ \ref{fig:wildcard-unify}). Didier \text{R\'emy} employed this trick to cope with arbitrary record field names\ \cite{Remy/records91}, but it was not adopted by Cartwright and Fagan\ \cite{cartwright1991soft} like his simple (finite) encoding.

We have been implicitly dealing with a wildcard for \textbf{num}, \textbf{str}, \textbf{bool}, \textbf{atom}, $[\,]$, and $(:)$ until now. A number of details become neater in explicitly naming it: \textbf{any}.

Firstly, we have been overloading type variables, as both "any" types and pointers to types (to break up long or circular definitions, or in case contexts). The \textbf{any} constructor assumes the first role, leaving only the second for variables: A fresh type, is a new variable pointing to a \text{R\'emy} type containing only a leaf flag parameter labelled with $\sim$ for \textbf{any}.

Secondly, we can add constructors for each function arity with \textbf{any} as their wildcard, to restore support for multi-arity functions. On a similar vein, we can have a constructor for every atom, sharing the \textbf{atom} constructor's flag parameter as their wildcard, to support tagged variants.

\begin{figure}
  \caption{Exposing R\'emy types to new constructors in order to unify them.}\label{fig:wildcard-unify}
  \begin{center}
    \begin{math}
      \arraycolsep=1.5pt
      \begin{array}{rll}
        \mathcal{R}( & f_{\mathbf{atom}}:\,\sim, & f_{\#\mathit{foo}}:+) \\
        \mathcal{R}( & f_{\mathbf{atom}}:\,\sim, & f_{\#\mathit{bar}}:-)
      \end{array}
    \end{math}
  \end{center}
  First, we expose the types to each others' constructors:
  \begin{center}
    \begin{math}
      \arraycolsep=1.5pt
      \begin{array}{rlll}
        \mathcal{R}( & f_{\mathbf{atom}}:\,\sim, & f_{\#\mathit{bar}}:\,\sim, & f_{\#\mathit{foo}}:+) \\
        \mathcal{R}( & f_{\mathbf{atom}}:\,\sim, & f_{\#\mathit{bar}}:-, & f_{\#\mathit{foo}}:\,\sim) \\
      \end{array}
    \end{math}
  \end{center}
  And then perform the unification:
  \begin{center}
    \begin{math}
      \arraycolsep=1.5pt
      \begin{array}{rlll}
        \mathcal{R}( & f_{\mathbf{atom}}:\,\sim, & f_{\#\mathit{bar}}:-, & f_{\#\mathit{foo}}:+) \\
      \end{array}
    \end{math}
  \end{center}
\end{figure}

\section{Related Work}

Compositionality is a fundamental concern of type systems, mirroring the programs they specify. Being such a crucial facet to the design of a type system, it has received a great deal of attention both in practice and in the literature.

\textit{Haskell} has been built from the ground up with types in mind, with a \textit{nominative} --- as opposed to \textit{structural} --- type system. Types in \textit{Haskell} are equated by name, not by structure, consequently, some forms of composition do not come naturally. For example, (disjoint) unions are represented by \textbf{Either}:
```{.haskell}
data Either a b = Left a | Right b
```
At the term level, when constructing an instance of a union, we tag it with which summand of the union it belongs to (\textbf{Left}, or \textbf{Right}). In \textit{Haskell}, $(\mathbf{num}\cup\mathbf{bool}):\mathbf{str}$ and $(\mathbf{num}:\mathbf{str})\cup(\mathbf{bool}:\mathbf{str})$ are (approximately):

```{.haskell}
type X = (Either Int Bool, String)
type Y = Either (Int, String) (Bool, String)

xToY :: X -> Y
xToY (Left  n, s) = Left  (n, s)
xToY (Right b, s) = Right (b, s)

yToX :: Y -> X
yToX (Left  (n, s)) = (Left  n, s)
yToX (Right (b, s)) = (Right b, s)
```

Nominally, the two types are isomorphic, but converting between them comes at a runtime cost, must be done explicitly, and is purely boilerplate: only the tags move! But, this problem is rare in \textit{Haskell} programs. Having named types ensures that one of the isomorphic representations is chosen when a type is defined. What we cannot do is define (total) functions on part of a named type, which we have seen is useful at times.

Wouter Swierstra makes impressive use of \textit{Haskell's} type class machinery to model unions and subsumption\ \cite{swierstra2008data}. Unfortunately, the resulting framework, while compositional, was not amenable to type inference, and required the creation of ``smart constructors'' --- functions that were aware of a subsumption type class --- as well as a data declaration for every non-composite type. This paper stands as a testament to the expressiveness of \textit{Haskell's} type system, and introduces many useful techniques for writing modular \textit{Haskell} programs, but its examples take these ideas to an impractical extreme.

As early as 1985, Mishra and Reddy explored type inference in the absence of annotations in their Declaration--Free type system\ \cite{mishra1985declaration} (henceforth MR). Their language --- a typed $\lambda$ calculus with \textit{let} bindings, \textit{case} expressions, and data built from tagged arbitrary length tuples --- bears a resemblance to our desugaring of \textit{GeomLab}, and we may draw several comparisons between their techniques and ours.

\begin{para}
  Most notably, both systems rely on \textit{discriminative types} (Definition\ \ref{def:discrim}), although, MR is less encumbered by the restriction:
  \begin{align*}
   & \text{Where we write: } & [\#\mathit{square}, \mathbf{num}] &  & \text{and} &  & [\#\mathit{rect}, \mathbf{num}, \mathbf{num}] \\
   & \text{MR uses: }        & \#\mathit{square}[\mathbf{num}]   &  & \text{and} &  & \#\mathit{rect}[\mathbf{num}, \mathbf{num}]
  \end{align*}
  The union of our representations is not discriminative, but in MR they are because the outermost constructors are $\#\mathit{square}$ and $\#\mathit{rect}$.
\end{para}

Similarly, by describing tuples as composed of $(:)$ and $[\,]$, we could not describe discriminative unions of different sized tuples, whilst in MR, the issue is dispensed with by making tuples an indivisible construct, with a distinct ``tuple constructor'' for each size. Multi-arity functions are modelled by functions accepting tuples, in turn.

Types in MR are represented by a system of inequalities, fed to a constraint solver. Aiken and Wimmers\ \cite{aiken1993type} extend this idea by generalising HM, replacing equality constraints --- $\tau_1 = \tau_2$ --- resolved by unification, with subset constraints --- $\tau_1\subseteq\tau_2$. Their system introduces unions, intersections and a notion similar to negation. These extra constructs furnish it with principal types for every typable term that are at least as (if not more) general than the types produced by Hindley--Milner. For example, the function:

```
define twice(f, x) = f(f(x));
```

which we are used to seeing with the type $\forall\alpha\ldotp(\alpha\to\alpha)\to\alpha\to\alpha$, is given the more general type $\forall\alpha,\beta,\gamma\ldotp((\alpha\to\beta)\cap(\beta\to\gamma))\to\alpha\to\gamma$.

Aiken, Wimmers and Lakshman go on to extend this work\ \cite{aiken1994soft} to include \textit{conditional types}, aiming to fill the same need as \textit{case types} (Section\ \ref{sec:case-types}). A conditional type $\tau?\sigma$ is semantically equivalent to the empty type when $\sigma$ is the empty type, and is equivalent to $\tau$ otherwise.

We chose not to build upon this type system because compared to HM, there is less literature on its efficient implementation. Furthermore, in the spirit of \textit{GeomLab} being a teaching language, we wish to avoid introducing concepts like type intersection and negation whose benefits are perhaps not as great as product and union types for the programmer.

An attempt to build a type system for \textit{Erlang}\ \cite{marlow1997practical} builds on and simplifies the idea of inferring types by solving systems of constraints \cite{mishra1985declaration,aiken1993type,aiken1994soft}. In \textit{Erlang}, product types have a tagged tuple representation that resembles \textit{GeomLab's}, with the tag in the tuple's first slot. The proposed type system avoids the discriminativity problem pragmatically by treating those tagged tuples specially.

Finally, Cartwright and Fagan extend HM\ \cite{cartwright1991soft} to model constraints over types in a manner solvable by unification. Their goal was to create a \textit{soft} type system that introduces runtime checks when unification fails instead of rejecting programs. However, their techniques proved to be intuitive and easily extensible when applied to a traditional ``hard'' type system and were invaluable for our work.

\section{Future Work}

In this dissertation we extended Hindley and Milner's type system to statically capture the specifications programmers are used to maintaining in dynamic programming languages. We focused on the types of data structures. Noticing that they are usually built up from a small suite of base constructors, we sought to express their types as similarly compositional.

To this end, we presented a type assignment algorithm capable of inferring many common data structures, by inspecting how they are pattern matched on, using ``case types'' (Section\ \ref{sec:case-types}), a solution we have not been able to find replicated in the literature. However, the work presented thus far only develops core ideas. There are many avenues that must be explored in order to build a fully-fledged type system, a few of which we detail below.

\subsection{Errors}

Our solution for producing useful error messages from Algorithm $\mathcal{W}$ needs to be developed further for $\mathcal{W_{RC}}$, for two reasons.

Firstly, errors are detected after all the constraints for a particular definition have been captured. We can only detect \textit{possible} type errors locally. When we verify that they are true errors, we will no longer know the precise source locations they originated from. Previously, as soon as a unification error was found, we could throw an error, and as the stack unwound, add source locations to it for context. Work on the \textit{Helium} compiler for \textit{Haskell}\ \cite{heeren2003helium} addresses similar issues.

Secondly, errors occur w.r.t. a specific context. It is not immediately obvious how to convey this information to the programmer. We could relate the context to parts of the source program (namely case expressions and their arms), to the types they condition upon, or a combinition of the two.

\subsection{Annotations}

We chose to avoid \textit{type annotations} so that we could focus on inferring the types of programs as typically written in \textit{GeomLab}. But, they are a useful form of statically verified documentation, and in some cases, they are necessary. For instance:
```
define rect(w, h) = [#rect, w, h];
```
will be assigned $\texttt{rect}::\forall\alpha,\beta\ldotp\,((\alpha,\beta)\to[\#\mathit{rect},\alpha,\beta]^{\uparrow})^{\uparrow}$, because, looking at this definition in isolation, we cannot restrict its parameters. However, the programmer knows this constructor should only accept numbers, so could annotate it: $\texttt{rect}::(\mathbf{num},\mathbf{num})\to[\#\mathit{rect},\mathbf{num},\mathbf{num}]$.

\subsection{Aliases}
\begin{para}
  \textit{Type aliases} could also be introduced, to name commonly used structures, in annotations:
  \begin{align*}
    \mathbf{shape} \Coloneqq &~[\#\mathit{rect},\mathbf{num}, \mathbf{num}]
    \\ \cup &~[\#\mathit{square}, \mathbf{num}]
    \\ \cup &~[\#\mathit{circle}, \mathbf{num}] \\
    \mathbf{tree}(\alpha) \Coloneqq &~[\#\mathit{leaf}, \alpha]
    \\ \cup &~[\#\mathit{branch},\mathbf{tree}(\alpha),\alpha,\mathbf{tree}(\alpha)]
  \end{align*}

  When the checker prints a type, we may also wish to replace a structure with its alias. But, because our types are represented as directed graphs, this problem is NP--Hard, by a reduction from \textsc{Sub-graph Isomorphism}. By associating tags with the type aliases they are mentioned in (and only allowing a tag to be used in at most one alias), we may simplify this task, in effect, building \textit{Haskell}'s algebraic data type system on top of our own. This comes with its own set of limitations (many of which we were trying to avoid to begin with).
\end{para}

\textit{Generative types} --- aliases that generate new types --- offer a way to encapsulate representations. For instance, if we had a function with a \textbf{shape} parameter, it would be a type error to apply it to a $[\#\mathit{square},\mathbf{num}]$ term if the \textbf{shape} alias were generative. To support these, we would need to differentiate terms of the generative type from terms with just the same shape. Tagging would be insufficient because it does not hide representations.


\subsection{Ascription}

\textit{Type ascription patterns} --- $t :: \tau$ --- which match when the expression bound to $t$ has type $\tau$, would also improve expressivity. With ascriptions, the \texttt{rect} constructor, could be written:
```
define rect(w :: num, h :: num) = [#rect, w, h];
```
This feature also supersedes primitive type predicates such as $\texttt{numeric}::\forall\alpha\ldotp\,\alpha\to\mathbf{bool}$, which could now be user-defined:
```
define numeric(_ :: num)  = true
     | numeric(_)         = false;
```

\vbox {
  %TC:ignore
}

\section{References}

\bibliography{references}

\appendix

\section{Language}\label{app:lang}


\subsection{Comments}
```
{ A { nested } comment. }
```
\textit{Comments} are surrounded by curly braces and may be nested.

\subsection{Literals}
```
[1, "foo", #bar, [], 1:[], true, false, function (f, x) f(x)]
```
\begin{description}
  \item[numbers] Using a double-precision floating point representation. We sidestep the issue of operator overloading by not distinguishing between integer and floating point numbers.

  \item[strings] Finite sequences of UTF-8 encoded characters, surrounded by double quotes.

  \item[atoms] Short strings, with fast equality checks, distinguished from identiifiers by prefixing a \#.

  \item[nil] A distinguished value used to represent ``nothing'', denoted by $[]$, commonly used as the terminator for singly linked lists.

  \item[cons cells] Pairs of values $a$ and $b$, denoted by $a:b$. These form the building blocks for compound data structures. In statically typed functional programming languages, they tend to only be used to construct singly linked-lists, but in dynamically typed languages (including \textit{GeomLab}) they are used in the construction of all product types.

  \item[booleans] True/false values.

  \item[functions] First-class multi-arity functions.
\end{description}

The language also provides sugar for list literals: \texttt{[a, b, c]} desugars to \texttt{a:(b:(c:[]))}.

\subsection{The Top Level}
```
define n     = 1;
define id(x) = x;
id(n);
```
The top level of a \textit{GeomLab} program is a sequence of statements, each terminated by a semicolon. A statement is either a definition or an expression to be evaluated. All statements may refer to names bound by themselves (in the case of definitions, thus facilitating recursion) and all previous statements.

Syntactic sugar exists to define functions in this way, whereby the formal parameters to the function may appear to the left of the \texttt{=} and the body of the function to the right.

\subsection{Let Bindings and Closures}
```
let n    = 2     in
let f(x) = x + n in
let n    = 3     in
  f(1);
```
The \texttt{let} construct can be used to introduce bindings local to an expression. In the above example the definition of \texttt{n} exists only in the body of the \texttt{let}.

Furthermore, functions close over (and are evaluated in) the environment they were defined in, not the environment they are called in, so the value of \texttt{n} in \texttt{f} forever remains \texttt{2} despite being rebound. That is to say, \textit{GeomLab} implements lexical, not dynamic scoping.

\subsection{Functions}
```
define filter(p, x:xs) = x : filter(p, xs) when p(x)
     | filter(p, _:xs) =     filter(p, xs)
     | filter(_, [])   = [];
```

A function may have multiple bodies, each corresponding to its parameters matching a different \textit{pattern} and optionally a \textit{guard} expression introduced by the \texttt{when} keyword. When a function is applied to some arguments, the body that is evaluated is the first whose corresponding pattern matches \textit{and} guard evaluates to \texttt{true} (if it exists).

An idiosyncracy of the language is that only named functions may be applied.

\subsection{List Comprehensions}
```
[ 10*x + y | x <- [1..3], y <- [1..3] when (x+y) mod 2 = 0]
```

List comprehensions provide a domain-specific language for the combination of maps, concatenations and filters. They operate similarly to their counterparts in other programming languages such as \textit{Haskell}.

\subsection{Operator Sections}
```
(+10);
```
A shorthand for \texttt{function (x) x + 10}.

\subsection{Types}

Types returned by the typechecker will use identifiers prefixed by an apostrophe to denote type variables, all of which are implicitly universally quantified. Additionally, when there is only one parameter to a function, the parenthesese are omitted if the result is unambiguous, so $\forall\alpha\ldotp(\alpha)\to\alpha$ becomes ${\texttt{'a -> 'a}}$.

\subsection{Type Unions}
```
define area([w, h]) = w * h
     | area(s)    = s * s;

```
Unions between types are denoted using the binary operator, \texttt{+}:
```
area :: ([num, num] + num) -> num
```

\subsection{Recursive Types}
Recursive types are introduced by \texttt{(...)*} (Surrounded by parentheses, and suffixed by $\ast$). Within a recursive type, the recursive part of the type is accessed using de Bruijn indices, which take the form of a type variable with a numeric identifier: \texttt{'0} refers to the recursive type the variable is immediately nested, \texttt{'1} is the recursive type 1 scope higher, and so on\dots The type of binary trees takes the form:
```
([] + ['0,'a,'0])*
```
Lists and list-like structures receive special treatment:
```
['a,...,'z]* = ([] + ('a:...('z:'0)...))*
```

\subsection{Omitted Features}

\subsubsection{Unification patterns}
```
define eq(x, x) = true
     | eq(_, _) = false;
```
As the example suggests, such unification patterns only match when values bound to the identifier at both sites are equal. We omit this because it is not a common feature of most pattern matching systems, and it can be desugared to the following:
```
define eq(x1, x2) = true when x1 = x2
     | eq(_,  _)  = false;
```

\subsubsection{$n+k$ patterns}
$n+k$ patterns match numbers $m\geq k$, and bind $n\triangleq m-k$. These have also been omitted for similar reasons to the above.

\subsubsection{Reference cells and Hash Tables}
Whilst there are tried and tested methods by which HM may be extended to maintain soundness in languages with mutable state, we have removed all sources of it from our subset in an effort to maintain focus.

\subsubsection{Sequencing}
Without any side-effectful operations, we have no need for sequential composition

\section{Type Errors}\label{app:errors}

In Section\ \ref{sec:bg} we chose to \textit{desugar} the source language. This simplifies type assignment, but now we deal with the consequences as they pertain to type errors. By annotating the abstract syntax tree with source locations, and preserving them during desugaring, we can point to the part of the \textit{source} program from which a type error originates, even though the error was detected in the \textit{desugared} representation.

\subsection{Calculating Source Locations}

In order to provide type errors with accurate source locations, we label expressions with where they originated from in the source. The process starts at the lexer which labels each token it outputs (Figures\ \ref{fig:span},\ \ref{fig:located}).

\begin{figure}
  \caption{The \textbf{Span} type stores the source location as a line and column index (A \textbf{Point}), as well as a byte offset and width. In the event of an error the \textbf{Point} is presented to the user so they know where to look in the file, and the byte offset and width are used to slice the relevant part of the source out so that they know what to look for.}\label{fig:span}
  \input{aux/span.tex}
\end{figure}

\begin{figure}
  \caption{A $\mathbf{Located}~\alpha$ is an $\alpha$ labelled with a \textbf{Span}. It can be considered a container of $\alpha$'s, which we signify by implementing the \textbf{Foldable}, \textbf{Functor} and \textbf{Traversable} type classes. The lexer returns a \textbf{Located Token} stream.}\label{fig:located}
  \input{aux/located.tex}
\end{figure}

From \textbf{Located Token} streams, the parser builds \textbf{Located Sugar} ASTs. Previously, the parser built abstract syntax trees (ASTs), $t::\mathbf{Sugar}$, by combining sub-trees, $s_1,\ldots,s_k::\mathbf{Sugar}$, using a function $f::\mathbf{Sugar}\to\cdots\to\mathbf{Sugar}$, whereas now, we build labelled trees, $\overline{t}::\mathbf{Located~Sugar}$, from labelled sub-trees, $\overline{s}_1,\ldots,\overline{s}_k::\mathbf{Located~Sugar}$.

One solution would be to modify all constructing function to accept and return \textbf{Located Sugar} terms, but this leads to repeated logic. A better solution is to alter the notion of \textit{function application} to one where ``applying'' $f$ to labelled sub-trees, applies the function to the values --- in the canonical sense --- and uses a sensible operation (Figure\ \ref{fig:span-monoid}) to combine labels also.

\begin{figure}
  \caption{The combination of spans $s$ and $t$ starts at the lowest line/column/offset in the file of either $s$ or $t$, and ends at the highest offset. We make this operation \textit{monoidal}, by introducing a unit span, \textbf{Floating}, representing a location outside the source file. Combining \textbf{Floating} with any other span $t$, yields $t$.}\label{fig:span-monoid}
  \input{aux/span_monoid.tex}
\end{figure}

\begin{figure}
  \caption{An \textbf{Applicative} instance for the \textbf{Located} type constructor. \textit{pure} embeds an $\alpha$ without a label in $\mathbf{Located}~\alpha$, using the \textbf{Floating} span to signify the non-presence of a location. $\varoast$ (\texttt{<*>}), defines our meaning of function application, which also combines labels using the \texttt{<>} operator, a synonym of \texttt{mappend} (Figure~\ref{fig:span-monoid}).}\label{fig:located-ap}
  \input{aux/located_ap.tex}
\end{figure}

The \textit{Applicative Functor}\ \cite{mcbride2008functional} is an abstraction that allows us to change the meaning of function application (Figure\ \ref{fig:located-ap}), by making it explicit in the $\varoast$ operator (Figure\ \ref{fig:applicative}).
\begin{figure}[htbp]
  \caption{Applying a pure function $f$ to values $s_1,\ldots,s_k$ before and after they have been wrapped in a label, using \textit{pure} to embed the function into the labelled type.}\label{fig:applicative}
  \begin{equation*}
    \arraycolsep=2pt
    \begin{array}{rlllllll}
                    & C &          & s_1            &          & \cdots &          & s_k \\
      \mathit{pure} & C & \varoast & \overline{s}_1 & \varoast & \cdots & \varoast & \overline{s}_k
    \end{array}
  \end{equation*}
\end{figure}
\begin{para}
  In addition to \textit{pure} and $\varoast$, instances of the \textbf{Applicative} class, also have operators:
  \begin{equation*}
    \arraycolsep=2pt
    \begin{array}{lll}
      \triangleright & :: & \mathbf{Applicative}~\phi\Rightarrow \phi~\alpha\to\phi~\beta\to\phi~\beta\\
      \triangleleft  & :: & \mathbf{Applicative}~\phi\Rightarrow \phi~\alpha\to\phi~\beta\to\phi~\alpha
    \end{array}
  \end{equation*}
  $x\triangleright y$ combines the labels (in general, the effects) of both $x$ and $y$, but returns only $y$'s value, $x\triangleleft y$ acts complementarily. These are spelt \texttt{*>} and \texttt{<*} in \textit{Haskell's} Applicative Functor library. A good example of their use in the context of labelled ASTs is:
\end{para}

```{.haskell}
PattPrim ::             { Located Patt }
PattPrim : {- ... -}
         | '(' Patt ')' { $1 *> $2 <* $3 }
```

\begin{para}
  This rule parses a pattern surrounded by parentheses. In the production, \texttt{\$1} refers to the \texttt{'('} token, \texttt{\$2} refers to the pattern, and \texttt{\$3} refers to the \texttt{')'} token. We wish to indicate that the \textbf{Span} of this pattern covers the parentheses, which is achievable with $\varoast$:
  \begin{align*}
    \mathit{pure}~(\lambda\;\_\;p\;\_ \to p)\varoast\$1\varoast\$2\varoast\$3
  \end{align*}
  But, as the function being applied just selects the pattern value, and ignores the token values, $\triangleright$ and $\triangleleft$ convey the intention more clearly.
\end{para}

\subsection{Unobtrusive Annotations}

\textbf{Located} labels allow the parser to calculate the source span of an AST as it is built, but as soon as it becomes part of some larger tree, we lose this information, and only have the source span of the larger tree.

We may be tempted to systematically update \textbf{Sugar}, replacing sub-trees (\textbf{Sugar}) with labelled sub-trees (\textbf{Located Sugar}). This is undesirable, not just because it spreads responsibility for annotations everywhere, but also, when desugaring an expression whose structure changes, it is unclear which annotations should be preserved.

Instead, when parsing certain AST nodes, we use \texttt{reify} to embed source spans into the AST along with a label (a \texttt{String}) describing the node.
```{.haskell}
data Sugar = {- ... -} | LocS String (Located Sugar)

reify :: String -> Located Sugar -> Located Sugar
reify lbl ls@(L s _) = L s (LocS lbl ls)
```
We also add a corresponding node to the desugared AST type. During desugaring, we carry over the embedded labels faithfully.
```{.haskell}
data Expr = {- ... -} | LocE String (Located Expr)
```
Finally, to ``type check'' such a label, we type check its sub-tree (\texttt{check (dislocate le)}), and, in the event of a type error, add the string label and the expression's location to the error's context.
```{.haskell}
typeOf :: MonadInfer m => GloDef (World m) -> Expr -> m (TyRef (World m))
typeOf gloDefs = check
  where
    {- ... -}
    check (LocE lbl le) =
      catchError (check (dislocate le)) $ \e -> do
        throwError $ CtxE lbl (le *> pure e)
```
For example, desugaring this list comprehension:
```
[ x | x <- [1..2 + "3"] when x mod 2 = 0];
```
Yields an expression in which some parts have been moved, and other parts have been introduced\footnote{\texttt{\_mapa} and \texttt{\_range} defined in Figure~\ref{fig:standard-defs}, page~\pageref{fig:standard-defs}.}:
```
_mapa( function (x, res)
         if x mod 2 = 0 then
           x : res
         else
           res
     , _range(1, 2 + "3")
     , []
     );
```
But the type checker's output refers to features from the original expression:

\vbox{\ttfamily\footnotesize%

%TC:ignore
\vspace{1em}
\textcolor{purple}{\underline{test/list\_comp.geom:20:1: Error in the expression}}

\qquad Failed to unify types:\\
\-\qquad\qquad Expected: num\\
\-\qquad\qquad Actual:\-\qquad str

\qquad Whilst trying to unify:\\
\-\qquad\qquad Expected: (num, num) -> num\\
\-\qquad\qquad Actual:\-\qquad(num, str) -> 'i

\textcolor{purple}{test/list\_comp.geom:20:22: In the upperbound of the range}

\qquad[1..\textbf{\emph{\color{blue}2 + "3"}}]

\textcolor{purple}{test/list\_comp.geom:20:18: In the generator of the list comprehension}

\qquad[ x | x <- \textbf{\emph{\color{blue}[1..2 + "3"]}} when x mod 2 = 0]
%TC:endignore
}

\section{Listings}

Code for the parser, lexer, and type inference algorithm.

\section{Tests}

Accompanying unit tests.

\vbox{
  %TC:endignore
}
