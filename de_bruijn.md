\begin{flalign*}
&\hspace{3em}{}_{(3-2=1)}\\
\texttt{define f(x$^1$)}  & \texttt{~=} \hspace{2.9em}\downarrow&&\\
\texttt{let g$^2$(y$^3$)} & \texttt{~= x in g;} &&\\
&\hspace{1.3em}\uparrow\\
&\hspace{0.3em}{}^{(4-1=3)}
\end{flalign*}
Parses and desugars to:
```{.haskell}
Def "f"
    (FnE 1
         (LetE (FnE 1 (VarE 3))
               (VarE 1)))
```
