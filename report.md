---
title: Structural Type Inference in a Functional Programming Language
author: Ashok Menon
abstract: |
  In this project we consider a range of extensions to Hindley and Milner's type system that allow us to specify the types found in previously dynamically typed functional programming languages. In particular, rather than simply inferring the types of parameters to composite data structures (The type of the elements in a list structure, for example), we aim to infer the shape of the structure itself as composed of atomic values, cons cells and nils --- In the case of a list, that it is either empty, or is an element, followed by a list containing more of the same type of element.
...

```{.haskell}
```

\section{Introduction}

In the majority of statically typed languages, data types must be declared and named before use, whilst in dynamically typed languages, data structures may be constructed on the fly from a relatively small set of constructors, with the caveat that the programmer must ensure the correct contracts and invariants are maintained in their use.

Whereas traditional type inference relies on such data definitions, in this project, we extend Hindley and Milner's type system, so that we may infer the shape of a data structure as composed of a few base constructors without having to explicitly declare it and give it a name. We do this in a way that aims to mirror the specifications programmers naturally follow when working with these composite types.

In Section\ \ref{sec:bg} we introduce the source language, \textit{GeomLab}, and the transformations it undergoes before being type checked. Section\ \ref{sec:hm} then describes an optimised implementation of the Hindley-Milner type system for \textit{GeomLab}.

The following Sections\ (\ref{sec:adhoc-adts},\ \ref{sec:tagged-variants}, and\ \ref{sec:recursive}) successively expand the type system so that it may specify more idiomatic programs, each section moving the system closer to the goal of being able to infer shape as well as type.

We finish with Section\ \ref{sec:errors} which discusses techniques for producing reasonable error outputs, by introducing source location annotations without perturbing the overall structure of the type checker.

\section{Background}\label{sec:bg}

In this project we use a subset of \textit{GeomLab} as our source language. This subset is a strict, dynamically typed, functional language offering a rich set of features such as higher-order functions, pattern matching with guards, operator sectioning, list comprehensions and ranges. We choose this language as it represents a compelling middle-ground between the $\lambda$ calculus, and most popular functional languages in use today, the implication being that if our techniques are applicable in this setting, with minimal effort we may move in either direction to serve both theory and practise. A full exposition of the syntax is available in Appendix\ \ref{app:lang}.

\subsection{Parsing}

\begin{figure}[htbp]
  \caption{\textit{Geomlab} Abstract Syntax Tree. The structure of literals are shared between that of patterns and of expressions, and so has been factored out.}\label{fig:sugar_adt}
  \input{aux/sugar.tex}
\end{figure}

We parse programs into abstract syntax trees of the $\mathbf{Sugar}$ type (Figure\ \ref{fig:sugar_adt}) which is ideal for parsing due to its similarity in structure to \textit{Geomlab}'s syntax. But, many of the nodes in $\mathbf{Sugar}$ --- corresponding to syntactic sugar --- are, in a sense, "redundant" from a typechecker's perspective. These nodes are mechanically derivable from the composition of others in $\mathbf{Sugar}$, and so in turn, the definition of the typechecker at these "sugary" nodes is derivable from its definition at other nodes. We avoid repeating this logic by \textit{desugaring} the input.

A potential cost of this operation is that errors may be hard to relate to the source text. In \text{Section~\ref{sec:errors}} we explore ways of maintaining contextual information (such as source location annotations) after desugaring to alleviate this issue.

\subsection{Desugaring}

Desugaring involves replacing sugar with extensionally equivalent expressions from a restricted subset of the source language. We represent the AST after desugaring with a new type (Figure\ \ref{fig:expr_adt}) to ensure at compile-time that after desugaring, no sugar exists in the AST.

\begin{figure}[htbp]
  \caption{Type for the desugared AST.}\label{fig:expr_adt}
  \input{aux/expr.tex}
\end{figure}

List comprehensions, ranges and operator sections have been removed, and case expressions have been decoupled from function definitions into their own node (and the related \texttt{FailE} and \texttt{FallThroughE}). We also lift the restriction that only identifiers may be applied as functions. Finally, whilst in the source language patterns could be nested arbitrarily deep, in $\mathbf{Expr}$, each case expression only matches one layer (to reclaim the previous functionality, case expressions themselves are nested).

The procedure $\textit{desugar} : \mathbf{Sugar} \to \mathbf{Expr}$ treats operator sections, ranges and list comprehensions as in \textit{Geomlab}'s compiler\ \cite{Geomlab}, by converting to applications of helper functions provided by the runtime (Figure\ \ref{fig:standard-defs}), whilst the algorithm for desugaring case expressions draws inspiration from Lennart Augustsson's paper\ \cite{Augustsson:1985:CPM:5280.5303} on the techniques used to compile pattern matching in \textit{LML}, a lazy variant of \textit{ML}.

\begin{figure}
  \caption{Helper functions, as found in \textit{Geomlab}'s compiler.}\label{fig:standard-defs}
  \input{aux/standard_defs.tex}
\end{figure}

\subsection{de Bruijn Indices}

$\mathbf{Expr}$ also alters the way local variables are introduced and denoted, using a notation referred to as \textit{de Bruijn} indices. $\mathbf{Expr}$ AST nodes that introduce new variables (like function definitions, let and case expressions) do not declare variable names, but instead simply declare how many local variables they introduce (functions introduce one for each formal parameter, let expressions always introduce one, and case expressions introduce one for every hole in the pattern). Then a reference to a local variable is denoted by the number of scopes between the reference and the scope introducing it (Figure\ \ref{fig:de_bruijn}).

\begin{figure}[htbp]
  \caption{Desugaring local variables to de Bruijn indices.}\label{fig:de_bruijn}
  \input{aux/de_bruijn.tex}
\end{figure}

This notation has several advantages:

\begin{itemize}
  \item It tackles the issue of name shadowing (from variables inserted by the desugarer) without resorting to generating unique symbols, which requires side effectful operations.

  \item As a corollary to the first point, this makes \textit{desugar} a pure, deterministic function, which is better for testing.

  \item As the typechecker traverses the AST, it must create fresh \textit{type} variables for each local variable it encounters. These type variables can be stored in a stack, from which they can be efficiently retrieved using the local variable's de Bruijn index.

  \item When debugging output from the desugarer, free variables and bound variables are easily distinguishable in the AST.
\end{itemize}

\subsection{Definitions}

Below are some basic definitions used when discussing type systems and their associated theory.

By convention, the lowercase roman alphabet denotes terms, $r,s,t,\ldots$ (and variables $x,y,z,\ldots$), the lowercase greek alphabet denotes types, $\rho,\sigma,\tau,\ldots$ (and type variables, $\alpha,\beta,\gamma,\ldots$), and the uppercase greek alphabet denotes type contexts, $\Gamma,\Delta,\ldots$

\begin{definition}[Type Context]
  A context $\Gamma$ is a partial map from variables to types. Given a context $\Gamma$, variable $x$, and a type $\sigma$, we will write $\Gamma,x : \sigma$ to denote the map $\Gamma$ with its type for $x$ overwritten with $\sigma$.
\end{definition}

\begin{definition}[Type Judgement]
  $\Gamma\vdash t :\sigma$ is a type judgement stating that assuming context $\Gamma$ there exists a proof that $t$ inhabits type $\sigma$ (in some fixed type theory).
\end{definition}

\begin{definition}[Substitution]
  $\mathbb{S}\equiv[\tau_1/\alpha_1,\ldots,\tau_n/\alpha_n]\equiv[\tau_i/\alpha_i]$ is a type substitution that, when applied to a type $\sigma$ simultaneously replaces all free occurrences of $\alpha_i$ with $\tau_i$ in $\sigma$. Application of a substitution can be written as $\mathbb{S}(\sigma)$ or equivalently $\sigma[\tau_i/\alpha_i]$.

  Substitutions can also be applied to type contexts in which case they are applied to each type in the context in turn.

  We take $\varnothing$ to denote the identity substitution.
\end{definition}

\begin{definition}[Composition]
  Let $\mathbb{S}\equiv[\tau_i/\alpha_i,\sigma_i/\beta_i]$ and $\mathbb{T}\equiv[\rho_i/\beta_i,\pi_i/\gamma_i]$, then define their composition by $\mathbb{S}\mathbb{T}\equiv[\tau_i/\alpha_i,\mathbb{S}(\rho_i)/\beta_i,\mathbb{S}(\pi_i)/\gamma_i]$.
\end{definition}

\begin{definition}[Instance]
  A type $\sigma$ is said to be an instance of another type $\tau$ iff there exists a substitution $\mathbb{S}$ s.t. $\mathbb{S}(\tau)\equiv\sigma$.
\end{definition}

\begin{definition}[Principal Type]
  Given a term $t$ in our language, we say that it has principal type $\tau$ when $\Gamma\vdash t : \tau$ for some context $\Gamma$, and if $\Delta\vdash t : \tau^{\prime}$ for some context $\Delta$, then $\tau^{\prime}$ is an instance of $\tau$.
\end{definition}

Exactly what constitutes a type and what constitutes a deduction of a type judgement differs between type theories, but the above definitions always apply.

\section{Hindley and Milner's Type System}\label{sec:hm}

We begin our search with the Hindley-Milner (henceforth HM) type system\ \cite{10.2307/1995158, MILNER1978348}. This theory forms the basis of many production quality type systems, including those found in \textit{Haskell} and the \textit{ML} family of languages.

HM builds on the types in the simply-typed $\lambda$ calculus by introducing \textit{universally quantified} variables in prenex form (Definition\ \ref{def:hm-types}). This allows us to describe the types of polymorphic functions. For example, the identity function \texttt{define id(x) = x;} has principal type $\forall\alpha\ldotp(\alpha)\to\alpha$.

\begin{definition}[Types in HM]\label{def:hm-types}
  Types in our adaptation of HM are defined by:
  \begin{align*}
    \sigma & \Coloneqq~\forall\alpha\ldotp\sigma~|~\tau
    \tag*{\scriptsize(types)}
    \\\tau & \Coloneqq~\alpha~|~\iota~|~[\,\tau\,]~|~(\,\pi\,)\to\tau~|~(\,)\to\tau
    \tag*{\scriptsize(quantifier-free types)}
    \\\iota & \Coloneqq~\mathbf{num}~|~\mathbf{str}~|~\mathbf{atom}~|~\mathbf{bool}
    \tag*{\scriptsize(base types)}
    \\\pi & \Coloneqq~\tau~|~\tau,\pi
    \tag*{\scriptsize(formal parameters)}
    \\\alpha & \Coloneqq~\alpha_1~|~\alpha_2~|~\cdots
    \tag*{\scriptsize(variables)}
  \end{align*}

\end{definition}

This type theory is a good starting point for many reasons: It has a reasonably efficient inference algorithm which has been proven sound and complete w.r.t the type system, the ability to specify polymorphic types affords a greater degree of flexibility, and given only a term, it is possible to infer its most general (principal) type. The last point is of particular import to us because our underlying language was originally dynamically typed, so there is no facility in the syntax to provide type annotations.

\subsection{Algorithm}\label{sec:hm-algorithm}

A clear exposition of a type inference algorithm for HM, Algorithm $\mathcal{W}$, is given in\ \cite{damas1982principal}, wherein it is described as operating on $\lambda$ terms augmented with \texttt{let} bindings. Given a context $\Gamma$, and a term $t$, the algorithm returns a substitution $\mathbb{S}$ and type $\tau$ such that $\mathbb{S}(\Gamma)\vdash t:\tau$ is a principal deduction of $t$, if such a deduction exists (i.e. If $t$ is typeable).

As in\ \cite{damas1982principal}, we rely on Robinson's unification algorithm and the ability to produce the closure of a type with respect to a context.

\begin{definition}[Robinson's Unification Algorithm, $\mathcal{U}$]
  Given two types, $\tau$ and $\sigma$, $\mathcal{U}(\tau, \sigma) = \mathbb{U}$ where $\mathbb{U}(\tau)\equiv\mathbb{U}(\sigma)$ and $\forall\mathbb{S}\ldotp\mathbb{S}(\tau)\equiv\mathbb{S}(\sigma)\implies\exists~\mathbb{S}^\prime\ldotp\mathbb{S}\equiv\mathbb{S}^\prime\mathbb{U}$ if and only if such a most general unifier $\mathbb{U}$ exists.
\end{definition}

\begin{definition}[Closure]
  $\overline{\Gamma}(\tau) = \forall\alpha_1,\ldots,\alpha_n\ldotp\tau$ where $\alpha_1,\ldots,\alpha_n$ are all the variables that appear free in $\tau$ but do not appear in the domain of $\Gamma$.
\end{definition}

We extend the algorithm, to deal with literals, recursion, sequencing, conditionals, and case expressions for our needs. For the most part these extensions are the common ones used by most practical implementations of HM, so we touch on only a few below.

$(\mathbb{S},\tau)\gets\mathcal{W}(\Gamma\vdash t)$ where
\begin{enumerate}[(i)]
  \item $t\equiv f(e_1,\ldots,e_k)$\hfill{\scriptsize(function applications)}
    \\[.5em] \begin{math}
      \arraycolsep=1.5pt
      \begin{array}{llll}
        \text{let} & (\mathbb{S}_0,\tau^\prime_0) & \gets & \mathcal{W}(\Gamma\vdash f)
        \\ & (\mathbb{S}_i,\tau^\prime_i) & \gets & \mathcal{W}(\mathbb{S}_{i-1}\ldots\mathbb{S}_{0}(\Gamma)\vdash e_i)
        \\ & \phantom{(}\mathbb{U} & \gets & \mathcal{U}(\mathbb{S}_k\ldots\mathbb{S}_1(\tau^\prime_0),~(\tau^\prime_1,\ldots,\tau^\prime_k)\to\beta) \text{ ($\beta$ fresh)}
      \end{array}
    \end{math}
    \\[.5em] $\mathbb{S}\equiv\mathbb{U}\mathbb{S}_k\ldots\mathbb{S}_0$ and $\tau\equiv\mathbb{U}(\beta)$.
    \\[1em] Unlike languages such as \textit{Haskell} where the true arity of a function is hidden (and often very difficult to ascertain for compiler and programmer alike), \textit{GeomLab} separates functions of different arities by syntax. As such, it is now a type error to partially apply a function.
    \\[1em] Complementarily, the inference rule for function abstraction produces function types of a statically fixed arity.

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
    \\[1em] Also note that by type checking $e_2$ with $x : \overline{\Gamma^\prime}(\tau^\prime_1)$ in the context, variables in the type we inferred for $x$ have been universally quantified, and each instantiation of $x$ in $e_2$ may substitute them with different variables.

  \item $t\equiv \texttt{case $c$ of } pat_1\to e_1;\cdots ;pat_k\to e_k$\hfill{\scriptsize(case expressions)}
    \\[.5em] \begin{math}
    \arraycolsep=1.5pt
    \begin{array}{llll}
      \text{let} & (\mathbb{S}_0,\tau_0) & \gets & \mathcal{W}(\Gamma\vdash c)
      \\ & (\mathbb{S}_i, \tau_i) & \gets & \mathcal{P}(pat_i, e_i)
      \\ & \phantom{(}\rho_i & \gets & \mathbb{S}_{i-1}\ldots\mathbb{S}_1(\tau_0)
      \\ & \phantom{(}\Delta_i & \gets & \mathbb{S}_{i-1}\ldots\mathbb{S}_1(\Gamma)
    \end{array}
    \end{math}

    $\mathbb{S}\equiv\mathbb{S}_k\ldots\mathbb{S}_1$ and $\tau\equiv\tau_k$.
    \\[1em] As our desugaring procedure removes nested patterns in favour of nested case expressions, our rule here only needs to deal with patterns that are one constructor deep. For each such pattern, we create the smallest type that contains any expression that could match it ($\mathcal{P}$ defined below), and we unify all of these with the type of the case argument. To get the type of the expression, we unify the types of all the $e_i$'s.
    \\[1em] Although this is a common type semantics for case expressions, it poses some problems. For instance, a pattern that expects only \texttt{[]} will also purport to accept cons cells, when doing so would cause an exception at run-time (The very thing a type system aims to avoid).
    \\[1em] $\mathcal{P}(pat_i, e_i)$ is defined as:
    \begin{enumerate}[(a)]
    \item $pat_i$ a numeric, string or atom literal pattern\hfill{\scriptsize(literal pattern)}
      \\[.2em] \begin{math}
        \arraycolsep=1.5pt
        \begin{array}{llll}
          \text{let} & \phantom{(}\mathbb{U} & \gets & \mathcal{U}(\rho_i,~\mathbf{num})\text{ ($\mathbf{str}$, $\mathbf{atom}$ respectively)}
          \\ & (\mathbb{S}^\prime,\tau^\prime) & \gets & \mathcal{W}(\mathbb{U}(\Delta_i)\vdash e_i)
          \\ & \phantom{(}\mathbb{U}^\prime & \gets & \mathcal{U}(\mathbb{S}^\prime\mathbb{U}(\tau_{i-1}), \tau^\prime)
        \end{array}
      \end{math}
      \\[.2em] $\mathbb{S}_i\equiv\mathbb{U}^\prime\mathbb{S}^\prime\mathbb{U}$ and $\tau_i\equiv\mathbb{U}^\prime(\tau^\prime)$

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
\end{enumerate}

\subsection{Implementation}

\text{Na\"ive} implementations of this algorithm --- in which types are represented as strings and all operations are performed eagerly --- tend to exhibit poor performance. Whilst inference for HM is known to be \textsc{DExpTime-Complete}\ \cite{kfoury90mlexptime}, such a worst-case running time can be avoided in all but the pathalogical cases. We use techniques from Oleg Kiselyov's tutorial on the implementation of \textit{OCaml}'s type inference algorithm\ \cite{oleg13ocamltc} to improve the performance of our algorithm in typical cases.

\subsubsection{Unification}

We represent types with acyclic graphs, and make unification a side-effectful operation, modifying types in place instead of returning a unifier. This allows for structural sharing, and makes unification cheaper: If we are unifying a variable in one type with another type, we replace the node representing the variable in the former with a forward pointer to the latter, a much cheaper operation than string substitution. Long chains of forward pointers that may arise are also compressed as they are traversed.

In this representation, cyclic types present as cycles of pointers. As a result, the algorithm is at risk of looping infinitely, unless we detect such features. We do so by leaving breadcrumbs at every node we enter and removing them once we make our way back. If we find a crumb at a node we have just entered, we know we have doubled back on ourselves. In such a situation, it is appropriate to throw an error as cyclic types are not valid in the HM theory.

\subsubsection{Generalisation}

Another target for improvement is \textit{generalisation}: When type checking a \texttt{let} expression or top-level definition, $e$, after inferring a type for the expression being defined, we take its \textit{closure} by universally quantifying any remaining free variables (see the algorithm above) --- The variables quantified by this process are said to be \textit{owned} by $e$.

A \text{na\"ive} algorithm traverses the entire type being closed over, searching for unbound variables. To prune the traversal, we annotate each type with a \textit{level}, associating it with a \texttt{let} expression or definition node: A \texttt{let} expression's level increases with nesting (cf. de Bruijn indices, but limited to other \texttt{let} expressions). Variables are annotated with the level of the expression that owns them, and compound types are annotated with the max level of any variable they mention. Then when closing over a type for a definition at level $l$, we only traverse compound types with level $l^\prime$ if $l^\prime\geq l$.

\subsubsection{Instantiation}

We can extend this pruning approach to also deal with \textit{instantiation}: The process of replacing quantified (type) variables with fresh (type) variables, done when type checking a bound (term) variable; In some senses an inverse of \textit{generalisation}.

By annotating types with a flag that is true when the type contains a quantified variable, when traversing for instantiation, we need only look at types where this flag is set. In our implementation, instead of a flag we use a special level, call it $\top$, such that for all levels $l\in\mathbb{N}$, $l<\top$. As we generalise a type, every variable we touch has its level set to $\top$, the rules for propogating levels to compound types takes care of the rest.

\subsubsection{Level Adjustments}

Unification can reduce the level of a type, which means we must work to keep levels consistent after unifications. For compound types, this would involve updating all mentioned variables with the lower level (if doing so lowers the variable's level), and propagating the change back up. Instead of doing this as we unify, we may instead perform this book-keeping lazily: If we unify a compound type we annotate it with the new level that should be propagated to its leaves, and push it onto a queue of types waiting to be adjusted. Just before we perform a generalisation, we force these waiting adjustments (as they could affect the generalisation outcome). Type variables, having no children, can still have their levels updated eagerly.

When we force waiting adjustments, we are doing so because a type whose level was once greater than the level we are generalising at could receive a lower level and escape being quantified. So, going a step further, we could force adjustments only when the type's current level is greater than the definition expression's level, and replace those at lower levels to be forced at a later stage.

\subsubsection{Type Syntax}

Our final consideration is not one of performance, but of formatting. Types as returned by our typechecker will use identifiers prefixed by an apostrophe to denote type variables, all of which are implicitly universally quantified. Additionally, when there is only one parameter to a function, the parenthesese are omitted for brevity, so $\forall\alpha\ldotp(\alpha)\to\alpha$ becomes ${\texttt{'a -> 'a}}$.

\subsection{Examples}

We now look at the action of our desugarer and typechecker on some small \textit{Geomlab} programs.

\subsubsection{\cmark~Basic Type Inference}

\HMExample{\texttt{(+10);}}{\input{aux/section_ast.tex}}{\texttt{num -> num}}

The algorithm arrives at the type for this expression by desugaring the operator section into an application of \texttt{\_rsect} applied to \texttt{+} and its second argument, when supplied with the appropriate types:

\texttt{%
  \_rsect :: (('a, 'b) -> 'c, 'b) -> 'a -> 'c\\
  + :: (num, num) -> num%
}

We provide these as part of the context in which every expression is typed, as they are built-in definitions.

\subsubsection{\xmark~Basic Type Error}

\HMExample{\texttt{"foo"+"bar";}}{\input{aux/string_add.tex}}{\input{aux/string_add_err.tex}}

\textit{Geomlab} has separate operators for the addition of numbers (\texttt{+}) and the concatenation of strings (\texttt{\^}). The assumption made by the programmer here is that \texttt{+} is overloaded to deal with both, which the typechecker catches as a unification error (in this case, between \texttt{num} and \texttt{str}, which are not unifiable because they are distinct base types).


Without further context finding the source of the error is quite difficult. To help, we also provide the outermost types that were being unified at the time of the error, as these are usually what correspond to expressions in the source language. In this case, these are ${\texttt{(num, num) -> num}}$ --- the type of \texttt{+} --- and ${\texttt{(str, str) -> 'a}}$ --- a constraint on the type the programmer expected of \texttt{+}.

\subsubsection{\xmark~Arity Mismatch}

\HMExample{\texttt{let k(x, y) = x in k(1);}}{\input{aux/arity_mismatch.tex}}{\input{aux/arity_mismatch_err.tex}}

Unlike \textit{Haskell}, Multi-arity functions in \textit{Geomlab} are not curried by default, and as a result, they cannot be partially applied. The type system captures this constraint as a unification error.

\subsubsection{\xmark~Branch Unification}

\HMExample{\texttt{if true then 1 else "foo";}}{\input{aux/branch_unify.tex}}{\input{aux/branch_unify_err.tex}}

In order to assign a type to a conditional, we require that the \textit{then} and \textit{else} expression types are unifiable, but this is not \textit{necessary}. In this example, the condition is constantly \texttt{true}, so we know that we could safely assign the entire expression the type \texttt{num}. Unfortunately, we cannot take advantage of such "degenerate" cases in general, because checking whether the condition is constant is not decidable (the proof of this follows by a reduction from the halting problem).

Another possibility is that the types are not unifiable, but we condition on the resulting type at runtime:

```
define a = if c then 0 else [];
define b = if numeric(a) then a + 1 else length(a) + 1;
```

HM has no way of describing such ad-hoc "unions" between types, so there is no way to specify the type of \texttt{a}. When we extend our system we will explore ways to remedy this.

\subsubsection{\cmark~Polymorphism}

\HMExample{\texttt{define id(x) = x;}}{\input{aux/id.tex}}{\texttt{id :: 'b -> 'b}}

\texttt{id} is a minimal example of an expression with a polymorphic type: Its type indicates that it may be applied to values of any type, to receive a value of the same type. This ability to abstract over parts of the structure of a type is very compelling and is something that we find in the theory of HM but not in the simply typed $\lambda$-calculus.

\subsubsection{\cmark~Higher-Order Functions}

\HMExample{\texttt{define . (f, g) = function (x) f(g(x));}}{\input{aux/compose.tex}}{\texttt{. :: ('e -> 'f, 'd -> 'e) -> 'd -> 'f}}

Function composition is also polymorphic, but inspite of this generality, we may constrain types in terms of each other. Here, the two parameters must be functions, and the domain of the first must coincide with the co-domain of the second.

This interaction between generality and unification is borne out of our use of the \textit{most general} unifier, which represents the minimal set of constraints required for the types to be correct.

\subsubsection{\cmark~Patterns}

\HMExample{\input{aux/folds.tex}}{\input{aux/folds_ast.tex}}{\texttt{length :: ['d] -> num}}

Patterns used in case expressions are also used by the inference algorithm in constraining the types of formal parameters. Here, they are the only indication that \texttt{length} takes list parameters.

\subsubsection{\xmark~Lambda-Bound Polymorphism}

\HMExample{%
  \texttt{define p(a, b) = function (c) c(a, b)}\newline
  \texttt{define f(j) = p(j(true), j(1));}\newline
  \texttt{f(function (x) x);}%
}{\input{aux/lambda_poly.tex}}{\input{aux/lambda_poly_err.tex}}

This valid \textit{Geomlab} program is untypeable in HM. As suggested by the type error, the issue is in the definition of \texttt{f}: Its parameter, \texttt{j}, is applied to both a \texttt{bool} and to a \texttt{num}, which causes a unification error. The trouble is that whilst types may be polymorphic, within the body of a function its parameters may only be instantiated once.

This restriction on the number of instantiations is equivalent to the restriction that types must be in \textit{prenex} form (with all the universal quantifications outermost). With this restriction lifted, it is possible to assign a type to \texttt{f}: ${\forall\pi\ldotp(\forall\alpha\ldotp\alpha\to\alpha)\to((\mathbf{bool},\mathbf{num})\to\pi)\to\pi}$.

The theory supporting such types is referred to as \textit{System F}, and as can be seen, it is more expressive than HM. The downside to this expressivity is that inferring a most general type in \textit{System F} is undecidable.

\subsubsection{\cmark~Let-Bound Polymorphism}

\HMExample{%
  \texttt{let j(x) = x in p(j(true), j(1));}\newline
  \textit{NB.} \texttt{p} \textit{defined as above.}%
}{\input{aux/let_poly.tex}}{\texttt{((bool, num) -> 'e) -> 'e}}

This program stands in contrast to the above, as whilst it evaluates to the same value as the previous program, it \textit{is} typeable. The reason for this is that polymorphic types bound to variables introduced by let-expressions \textit{can} be instantiated multiple times.

The fact that the latter program is typeable and the former is not is of particular interest because in dynamically typed languages, $\mathbf{let}~x = e_1~\mathbf{in}~e_2$ is commonly implemented as sugar for $(\lambda x\ldotp e_2)e_1$.

\subsubsection{\xmark~Infinite Types}

\HMExample{%
\texttt{define f(x) = f;}\newline
\texttt{define g(x) = g(g);}\newline
\texttt{define h(x) = p(h, h);}%
}{\input{aux/infinite.tex}}{\input{aux/infinite_err.tex}}

All these programs yield infinite types, which in our implementation are represented by cyclic data structures.
The implementation detects these cycles, and terminates, printing the types. When printing a cyclic type, if the (nominal) root node of the type is detected again, it is printed as the special variable \texttt{'*}.

\section{Ad-hoc Algebraic Data-types}\label{sec:adhoc-adts}

Often it is useful to "couple" data together. In many existing statically typed functional programming languages this is achieved by defining a new named data type, but a common technique in \textit{Geomlab} is to use \textit{lists}. For instance, to fully describe a rectangle requires two numbers:

```
define area([width, height]) = width * height;
```

Our existing typechecker infers the type ${\texttt{area :: [num] -> num}}$. The information that rectangles are \textit{pairs} of numbers has been lost. According to this type, \texttt{area} will accept a list of any size, but we know that it is only defined for lists of two elements.

This issue stems from our special treatment of nil and cons. Implicit in the definition of the algorithm is the assumption that they are used only to construct homogeneous, singly-linked lists (A list where every value has the same type). This precludes our idea of using lists to represent arbitrary product types.

We may also want to define \texttt{area}, not just for rectangles, but for other shapes too. Here we define it for squares represented by the length of their side (\texttt{s}).

```
define area([w, h]) = w * h
     | area(s)      = s * s;
```

\begin{wrapfigure}{r}{0.3\textwidth}
  \caption{A union type for shapes.}\label{fig:shape-union}
  \begin{center}
    \texttt{[num, num] + num}
  \end{center}
\end{wrapfigure}

In HM, we unify all parameter patterns together. This means to infer a type for \texttt{area}, we must unify \texttt{num} and cons patterns, which is not possible.

In this section, we will investigate extensions to HM that allow us to specify product and union types in an ad-hoc manner, thus lifting this restriction (Figure\ \ref{fig:shape-union}).

\subsection{Products}

As mentioned earlier, in the dynamically typed setting we have always had a way to couple data together through the use of the cons cell; it was only by introducing HM that we lost this ability!

We may make a bid to recover it now by freeing the nil (\texttt{[]}) and cons (\texttt{(:)}) constructors from the list type, so that each may inhabit its own type. This corresponds to a change in our type grammar, and the addition of some proof rules to our version of HM (\text{Figures~\ref{fig:prod-ty-grammar}\,\&\,\ref{fig:prod-ty-rules}}).

\begin{figure}[htbp]
  \caption{Modifications to the HM grammar for types to separate the list type into its constituent constructors.}\label{fig:prod-ty-grammar}
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

It will happily assign it the type $(\mathbf{num}:(\mathbf{num}:[\,]))\to\mathbf{num}$, or, by lifting list literals to the type-level \texttt{[num, num] -> num}.

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

\begin{definition}[Subtyping relation ($\prec$)]~\\
  \begin{minipage}[t]{.33\textwidth}
    \begin{prooftree}
      \AXC{\phantom{$\tau\sigma\prec\rho$}}
      \RightLabel{\scriptsize(refl)}
      \UIC{$\tau\prec\tau$}
    \end{prooftree}
  \end{minipage}
  \begin{minipage}[t]{.33\textwidth}
    \begin{prooftree}
      \AXC{$\tau\prec\sigma$}
      \AXC{$\sigma\prec\rho$}
      \RightLabel{\scriptsize(trans)}
      \BIC{$\tau\prec\rho$}
    \end{prooftree}
  \end{minipage}
  \begin{minipage}[t]{.33\textwidth}
    \begin{prooftree}
      \AXC{\phantom{$\tau\sigma\prec\rho$}}
      \RightLabel{\scriptsize(inst)}
      \UIC{$(\forall\alpha\ldotp\tau)\prec\tau[\sigma/\alpha]$}
    \end{prooftree}
  \end{minipage}
  \begin{minipage}[t]{.4\textwidth}
    \vspace{1em}
    \begin{prooftree}
      \AXC{$\tau_1\prec\sigma_1$}
      \AXC{$\tau_2\prec\sigma_2$}
      \RightLabel{\scriptsize(cons)}
      \BIC{$(\tau_1:\tau_2)\prec(\sigma_1:\sigma_2)$}
    \end{prooftree}
  \end{minipage}
  \begin{minipage}[t]{.6\textwidth}
    \vspace{1em}
    \begin{prooftree}
      \AXC{$\sigma_1\prec\tau_1$}
      \AXC{$\cdots$}
      \AXC{$\sigma_k\prec\tau_k$}
      \AXC{$\rho\prec\pi$}
      \RightLabel{\scriptsize(arr)}
      \QIC{$(\tau_1,\ldots,\tau_k)\to\rho~\prec~(\sigma_1,\ldots,\sigma_k)\to\pi$}
    \end{prooftree}
  \end{minipage}
  \begin{minipage}[t]{.5\textwidth}
    \vspace{1em}
    \begin{prooftree}
      \AXC{$\tau\prec\rho$}
      \AXC{$\sigma\prec\rho$}
      \RightLabel{\scriptsize($\cup$-left)}
      \BIC{$(\tau\cup\sigma)\prec\rho$}
    \end{prooftree}
  \end{minipage}
  \begin{minipage}[t]{.5\textwidth}
    \vspace{1em}
    \begin{prooftree}
      \AXC{$\phantom{\tau\sigma\rho\prec}$}
      \RightLabel{\scriptsize($\cup$-right)}
      \UIC{$\tau\prec(\tau\cup\sigma)$}
    \end{prooftree}
  \end{minipage}
\end{definition}

These additions are sound, and highlight some interesting interactions between existing features of the type system, and subtyping. For instance, note how subtyping for function types is contravariant in parameter types, and covariant in the return type, this fits our intuition: It is safe to treat ${(\mathbf{num}\cup\mathbf{bool})\to\mathbf{num}}$ as though it were ${\mathbf{num}\to(\mathbf{num}\cup\mathbf{bool})}$, because, in words, we are promising to feed only numbers to a function that accepts numbers and booleans, and we are prepared to receive numbers (which it produces) and bools (which it does not) from it.

Also interesting (and encouraging) is the fact that HM's instantiation is a special case of subsumption:

\newenvironment{mathprooftree}
  {\varwidth{.9\textwidth}\centering\leavevmode}
  {\DisplayProof\endvarwidth}
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

However, consider the types $(\alpha\cup\beta):\gamma$ and $(\alpha:\gamma)\cup(\beta:\gamma)$. Intuitively, they are equivalent so it should hold that they are subtypes of each other, but while it is possible to prove that $(\alpha:\gamma)\cup(\beta:\gamma)\prec(\alpha\cup\beta):\gamma$, the converse is not. To see why, let us have a look at an attempted proof:

\begin{prooftree}
  \AXC{$\vdots$}
  \UIC{$(\alpha\cup\beta)\prec\alpha$}
  \AXC{}
  \RightLabel{\scriptsize(refl)}
  \UIC{$\gamma\prec\gamma$}
  \RightLabel{\scriptsize(cons)}
  \BIC{$(\alpha\cup\beta):\gamma\prec\alpha:\gamma$}
  \AXC{$\vdots$}
  \UIC{$(\alpha\cup\beta)\prec\beta$}
  \AXC{}
  \RightLabel{\scriptsize(refl)}
  \UIC{$\gamma\prec\gamma$}
  \RightLabel{\scriptsize(cons)}
  \BIC{$(\alpha\cup\beta):\gamma\prec\beta:\gamma$}
  \RightLabel{\scriptsize($\cup$-right)}
  \BIC{$(\alpha\cup\beta):\gamma\prec(\alpha:\gamma)\cup(\beta:\gamma)$}
\end{prooftree}

This example highlights a limitation of the $\cup$-right rule. It is treating unions as \textit{disjoint}, meaning that if a term inhabits a union type, it either inhabits its left summand or its right, but not both. This is a convenient assumption to make for our implementation, but as we have seen, does not necessarily hold.

\subsubsection{Disjoint Unions}

As subtyping has received a great deal of attention in the literature, there are already a wealth of solutions to this problem. A popular approach is to enforce disjointness: In \textit{Haskell} this comes in the form of the \textbf{Either} type:

```{.haskell}
data Either a b = Left a | Right b
```

The idea being that, at the term level, when constructing an instance of the union type, we tag it with which summand of the union it belongs to (\textbf{Left}, or \textbf{Right}). With this extra information, type assignment can see that $\mathbf{Left}~1::\mathbf{Either}~\mathbf{Int}~\beta$\footnote{Haskell's type inference will actually infer the even more general type of ${\mathbf{Num}~\alpha\,\Rightarrow\,\mathbf{Either}~\alpha~\beta}$, but we will avoid muddying the waters by introducing type classes in this discussion.}

Translating the types that incited these worries in us into \textit{Haskell}, they are (approximately):

```{.haskell}
type X a b c = (Either a b, c)
type Y a b c = Either (a, c) (b, c)

xToY :: X a b c -> Y a b c
xToY (Left a, c)  = Left (a, c)
xToY (Right b, c) = Right (b, c)

yToX :: Y a b c -> X a b c
yToX (Left  (a, c)) = (Left a,  c)
yToX (Right (b, c)) = (Right b, c)
```

The two types are isomorphic, but converting between them comes at a runtime cost, and must be done explicitly. Ideally we would like to avoid this: We are trying to infer the types of programs without modifying them.

\subsubsection{Type Inclusion Constraints}

Aiken and Wimmers generalised HM \text{in~\cite{aiken1993type}} by replacing equality constraints --- $\tau_1 = \tau_2$ --- which are resolved by unification, with subset constraints --- $\tau_1\subseteq\tau_2$. As well as unions, this generalisation introduces \textit{intersection} types and a notion similar to \textit{negation}, and in so doing, mitigates some of our issues.

Whilst inclusion constraints are a generalisation of equality constraints, the algorithms used to resolve them are not an extension of unification, and if we look at the types of some common functions, such as:

```
define twice(f, x) = f(f(x));
```

which we are used to seeing with the type $\forall\alpha\ldotp(\alpha\to\alpha)\to\alpha\to\alpha$. We are given a more general type $\forall\alpha,\beta,\gamma\ldotp((\alpha\to\beta)\cap(\beta\to\gamma))\to\alpha\to\gamma$.

It is debatable whether this extra generality is useful, and as a consequence of it, the type system, type inference algorithm, and the types that are produced are much more complicated.

\subsubsection{Discriminative Types}

We will instead choose to relax disjointness to \textit{discriminativity}, as seen \text{in~\cite{mishra1985declaration}} \text{(Definition~\ref{def:discrim})}.

\begin{definition}[Discriminative Union]\label{def:discrim}
  A union type is considered discriminative when each of its inhabitants may be projected into one of the union's summands by looking only at its outermost constructor. For the purposes of this discussion $\mathbf{num}$, $\mathbf{bool}$, and $\mathbf{atom}$ can be considered unary constructors and $[\,]$ can be considered a nullary constructor.
\end{definition}

The intuition here is that, if terms already look different, then there is no need to tag them as distinct. If we are given a term with type $\mathbf{num}\cup\mathbf{bool}$, then we can tell which summand of the union it will belong to by inspecting its representation. If, however we are given a term of type $\mathbf{num}\cup\mathbf{num}$, we cannot, so we must tag them: $\mathit{kilometres}(\mathbf{num})\cup\mathit{miles}(\mathbf{num})$.

Unfortunately, neither $(\alpha:\gamma)\cup(\beta:\gamma)$ nor $(\alpha\cup\beta):\gamma$ are discriminative types. The former because $\alpha\cup\gamma$ and $\beta:\gamma$ both have a $(:)$ constructor outermost, and the latter because by substituting $\alpha$ and $\beta$ we could violate discriminativity. However, the type of the more complicated \texttt{area}:

```
define area([w, h]) = w * h
     | area(s)      = s * s;
```

is $([\mathbf{num},\mathbf{num}]\cup\mathbf{num})\to\mathbf{num}$, which is discriminative.

\subsection{R\'emy Encoding}

It is possible to implement type assignment with discriminative union types just by changing the representation of types. This idea was first expounded \text{in~\cite{cartwright1991soft}} as an adaptation of Didier \text{R\'emy's} encoding of record types \text{in~\cite{Remy/records91}}.

The encoding assumes that we have a finite number of constructors and this is not true in \textit{GeomLab}, in which functions of differing arities are considered to have different constructors. In \text{Section~\ref{sec:wildcard}} we will fix this limitation, but for now, we will restrict ourselves to functions with one parameter.
\begin{align*}
\intertext{Suppose we have}
\mathcal{F} & = \{+,-\}
\tag*{Flags}\\
\mathcal{V} & = \{\alpha,\beta,\gamma,\ldots\}
\tag*{Variables}\\
\mathcal{C} & = \{\mathbf{num},~\mathbf{bool},~\mathbf{atom},~[\,],~(:),~(\to)\}
\tag*{Constructors}\\
a_x & =
\begin{cases}
  2 & \text{ if }x\in\{(:), (\to)\}\\
  0 & \text{ if }x\in\mathcal{C}\setminus\{(:), (\to)\}
\end{cases}
\tag*{Arities}
\intertext{Then a R\'emy encoded type $\rho\in\mathcal{T}$ has the form:}
\rho & = \mathcal{R}(f_{\mathbf{num}};~f_{\mathbf{bool}};~f_{\mathbf{atom}};~f_{[\,]};~f_{(:)}, c^1_{(:)}, c^2_{(:)};~f_{(\to)}, c^1_{(\to)}, c^2_{(\to)})
\tag{$\star$}\label{eqn:remy}
\intertext{where}
f_x & \in\mathcal{F}\cup\mathcal{V}
\tag*{Flag parameter for constructor $x\in\mathcal{C}$.}\\
c^i_x & \in\mathcal{T}\cup\mathcal{V}
\tag*{$i^{\text{\tiny th}}$ Child type for constructor $x\in\mathcal{C}$.}
\intertext{An instance of this encoding does not represent just one type, but instead describes a set of feasible types. Suppose $\tau$ is feasible with respect to $\rho$'s constraints, then, for any $x\in\mathcal{C}$,}
f_x = + & \implies x(\gamma^1_x,\ldots,\gamma^{a_x}_x)\subseteq\tau\\
f_x = - & \implies x(\gamma^1_x,\ldots,\gamma^{a_x}_x)\cap\tau = \varnothing\\
\gamma^i_x & \text{ is feasible with respect to $c^i_x$'s constraints.}
\end{align*}

When a flag parameter $f_x$ is a variable, it indicates that $\rho$ does not constrain whether or not $x(\gamma^1_x,\ldots,\gamma^{a_x}_x)$ is in the type. Variables in child types have their usual meaning as type variables.

\subsubsection{Examples}

Suppose we wish to represent the supersets of $\mathbf{num}\cup\mathbf{bool}$ using \text{R\'emy} encoding, it would look like this ($\star$ represents a fresh variable whose symbol is not relevant):
\begin{math}
  \begin{array}{rrrrrrrrrrrrl}
    && f_{\mathbf{num}} & f_{\mathbf{bool}} & f_{\mathbf{atom}} & f_{[\,]} & f_{(:)} & c^1_{(:)} & c^2_{(:)} & f_{(\to)} & c^1_{(\to)} & c^2_{(\to)}\\
    \phantom{\varepsilon:} & \mathcal{R}( & +; & +; & \star; & \star; & \star & \star & \star; & \star & \star & \star & )\\
  \end{array}
\end{math}
Or, subsets of $(\mathbf{num}:\mathbf{bool})$ (Given by $\alpha$):
\begin{math}
  \begin{array}{rrrrrrrrrrrrl}
    && f_{\mathbf{num}} & f_{\mathbf{bool}} & f_{\mathbf{atom}} & f_{[\,]} & f_{(:)} & c^1_{(:)} & c^2_{(:)} & f_{(\to)} & c^1_{(\to)} & c^2_{(\to)}\\
    \alpha: & \mathcal{R}( & -; & -; & -; & -; & \star & \beta & \gamma; & - & \star & \star & )\\
    \beta:  & \mathcal{R}( & \star; & -; & -; & -; & - & \star & \star; & - & \star & \star & )\\
    \gamma: & \mathcal{R}( & -; & \star; & -; & -; & - & \star & \star; & - & \star & \star & )\\
  \end{array}
\end{math}
Or, the constraints of the \texttt{area} function's type (Given by $\alpha$):
\begin{math}
  \begin{array}{rrrrrrrrrrrrl}
    \alpha:      & \mathcal{R}( & -; & -; & -; & -; & - & \star & \star; & + & \beta & \gamma & )\\
    \beta:       & \mathcal{R}( & -; & -; & -; & -; & \star & \delta & \varepsilon; & - & \star & \star & )\\
    \gamma:      & \mathcal{R}( & +; & \star; & \star; & \star; & \star & \star & \star; & \star & \star & \star & )\\
    \delta:      & \mathcal{R}( & \star; & -; & -; & -; & - & \star & \star; & - & \star & \star & )\\
    \varepsilon: & \mathcal{R}( & -; & -; & -; & -; & \star & \zeta & \eta; & - & \star & \star & )\\
    \zeta:       & \mathcal{R}( & \star; & -; & -; & -; & - & \star & \star; & - & \star & \star & )\\
    \eta:        & \mathcal{R}( & -; & -; & -; & \star; & - & \star & \star; & - & \star & \star & )\\
    && f_{\mathbf{num}} & f_{\mathbf{bool}} & f_{\mathbf{atom}} & f_{[\,]} & f_{(:)} & c^1_{(:)} & c^2_{(:)} & f_{(\to)} & c^1_{(\to)} & c^2_{(\to)}\\
  \end{array}
\end{math}

Notice that the return type ($\gamma$) of \texttt{area} is not satisfied just by $\mathbf{num}$ but also by any supertype of $\mathbf{num}$. Conversely, the parameter type ($\beta$) is constrained to be a subset of $[\mathbf{num}, \mathbf{num}]$.

\subsection{Adapting HM}

In order to use \text{R\'emy} encoded types in HM, we must change how types are introduced: Before, we assigned each expression a specific type, which was its most general type. Now, we assign each expression a set of constraints over its type, so, we should ensure that these constraints are the most general constraints.

\begin{definition}[Superset encoding]
  Given a constructor $x\in\mathcal{C}$, and R\'emy encoded types $c^1_x,\ldots,c^{a_x}_x\in\mathcal{T}\cup\mathcal{V}$ let $x(c^1_x,\ldots,c^{a_x}_x)^{\uparrow}$.
\end{definition}

\begin{definition}[Subset encoding]
  Given a constructor $x\in\mathcal{C}$ let
\end{definition}


The beauty of this encoding is that, if we treat $\mathcal{R}$ as a constructor, and flag parameters as types, then \text{R\'emy} encoded types may be combined using Robinson's unification algorithm: Two \text{R\'emy} types are unified by unifying their flag parameters and child types, whilst a variable $v$ is unified with another term $t$ (so long as $v$ appears free in $t$) by substituting $t$ for $v$.

\subsection{Case Types}

Generalising flags in the \text{R\'emy} encoding to trees where internal nodes represent a choice of what the outer-most constructor is in another type, and leaf nodes represent possible values the flag could take.
Whilst some unions are not discriminative because they contain redundant subtypes --- like $\mathbf{num}\cup\mathbf{num}$ --- and some unions have equivalent discriminative representations --- like $(\alpha:\gamma)\cup(\beta:\gamma)$ --- $(\mathbf{num}:\mathbf{num})\cup(\mathbf{bool}:\mathbf{bool})$ is an example of a type with no discriminative representation.

If it is possible to discriminate between $\mathbf{bool}$ and $\mathbf{num}$, then it should also be possible to distinguish a pair of $\mathbf{bool}$s from a pair of $\mathbf{num}$s, but discriminative types do not accommodate this case.

\subsection{Optimisation}

\subsection{Rationalisation}

A discussion on decoding the \text{R\'emy} encoding back into a legible type, described in terms of rational trees.

\section{Tagged Variants}\label{sec:tagged-variants}

In our \texttt{area} example, when we introduced squares, we were lucky that they had a different structure to our representation of rectangles (one number instead of a pair of numbers), but suppose now we wish to introduce circles, represented by their radius; How would we distinguish between circles and squares?

A common technique is to tag each kind of shape with a unique identifier, and check for these when matching patterns. For this we use \textit{Geomlab}'s atoms as their representation is legible to programmers, and their implementation yields fast equality checks:

```
define area([#rect, w, h]) = w * h
     | area([#square, s])  = s * s
     | area([#circle, r])  = PI * r * r;
```

The issue with this is \texttt{[\#square, s]} and \texttt{[\#circle, r]} both have a type of ${\texttt{[atom, num]}}$: Whilst squares and circles are distinguishable by their tags at the value level, they are not at the type level, so the function defined above would have the same type as this one:

```
define area([#rect, w, h]) = w * h
     | area([#square, s])  = s * s;
```

\begin{wrapfigure}[9]{l}{0.32\textwidth}
  \caption{Tagged union type for shapes.}\label{fig:shape-tagged}
  \begin{Verbatim}
  [#rect, num, num]
+ [#square, num]
+ [#circle, num]
  \end{Verbatim}
\end{wrapfigure}

This is clearly not ideal, as the latter function will throw an error at runtime if applied to a circle. To get around this, we could lift atoms to the type level: Furnish every atom value with a corresponding type that only it inhabits. Then squares will have type \texttt{[\#square, num]}, and circles \texttt{[\#circle, num]} (Figure\ \ref{fig:shape-tagged}).

\subsection{Wildcard Constructors}\label{sec:wildcard}

A technique to get around the "finite constructor" limitation of the \text{R\'emy} encoding whereby if we have an infinite family of constructors (like multi-arity functions or atoms) we have a constructor for each member of the family, as well as a wildcard constructor to capture our knowledge about the rest of the constructors in the family.

\section{Recursive Types}\label{sec:recursive}

In HM, the list was a recursive type that we had built in support for. We lost this support when we stopped treating $\texttt{[]}$ and $\texttt{(:)}$ as special, related constructors. Now, if we try to encode the a list of type \texttt{'a}, we get: \texttt{[] + ('a':'l)} where \texttt{'l} refers back to the type we are defining, yielding an infinite (cyclic) type, which our typechecker balks at. Similarly, an attempt to construct a representation of binary trees using our existing machinery may look something like this:

```
#leaf              { Leaves }

[#branch, l, x, r] { Branch with datum `x`
                   , left sub-tree `l`
                   , and right sub-tree `r`
                   }
```

But again, \texttt{l} and \texttt{r} have the same type as the branch they are contained in. The ability to specify ad-hoc recursive types would make such expressions typeable (Figure\ \ref{fig:rec-type}).

\begin{figure}[htbp]
  \caption{Using ad-hoc recursive types. Fixed points are introduced by the \texttt{(...)*} operator, and we use de Bruijn indices to represent recursion sites.}\label{fig:rec-type}
  \begin{Verbatim}
list 'a ::= ([] + ('a:'0))*
tree 'a ::= ([#branch, '0, 'a, '0] + #leaf)*
  \end{Verbatim}
\end{figure}

\subsection{Circular Unification}

Recursive types can occur even without recursive definitions, this section will show an expression that does this, and the solution, in the form of Huet's circular unification algorithm.

\section{Type Errors}\label{sec:errors}

\subsection{Source Mapping}

Explaining the system used to annotate AST nodes with source locations.

\subsection{Unwinding}

The technique used to annotate exceptions with relevant AST locations as they travel back up through the stack.

\subsection{Formatting}

Converting chains of locations into a formatted error message. Talk about how to treat pairs of nested annotations that share the same location. (The outer one refers to the location as a child in its parent, the inner one refers to the element at that location as a parent).

\section{Related Work}

Aiken and Wimmers work on conditional types (A type $\tau?\sigma$ that is $\tau$ when $\sigma\neq\varnothing$ and is $\varnothing$ itself otherwise).

Mishra and Reddy's work on Declaration-free Typing (using discriminative unions).

Marlow and Wadler's work on a similar type system for Erlang (no higher-order functions).

W Swierstra's Data-types a la carte which builds a similar type system, using Haskell's type class machinery.

\section{Future Work}
Everything I didn't have time to fully flesh out:
\begin{itemize}
  \item Useful errors.
  \item Type level booleans.
  \item Type Aliasing
  \item Generative types (for encapsulation).
  \item Impredicative types.
\end{itemize}

\section{References}

\bibliography{references}

\vbox {
  %TC:ignore
}

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

  \item[cons cells] Pairs of values $a$ and $b$, denoted by $a:b$. These form the building blocks for compound data structures. In statically typed functional programming languages, they tend to only be used to construct singly linked-lists, but in dynamically typed languages (including \textit{Geomlab}) they are used in the construction of all product types.

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
The top level of a Geomlab program is a sequence of statements, each terminated by a semicolon. A statement is either a definition or an expression to be evaluated. All statements may refer to names bound by themselves (in the case of definitions, thus facilitating recursion) and all previous statements.

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

\section{Listings}

Code for the Parser, Lexer, and Type Inference algorithm.

\section{Tests}

Accompanying unit tests.

\vbox{
  %TC:endignore
}
