\begin{Verbatim}[fontsize=\scriptsize]
test/hm_examples.geom:25:8: Error in the definition of 'f'

    Failed to unify types:
        Expected: bool
        Actual:   num

    Whilst trying to unify:
        Expected: bool -> 'f
        Actual:   num -> 'g

test/hm_examples.geom:25:26: In the 2nd argument of the function application

    p(j(true), j(1))

test/hm_examples.geom:25:15: In the body of 'f'

    p(j(true), j(1))
\end{Verbatim}
