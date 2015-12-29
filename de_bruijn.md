```
define f(x) =
  let g(y) = x in g;
```
Compiles and desugars to:
```{.haskell}
Def "f"
    (FnE 1
         (LetE (FnE 1 (VarE 3))
               (VarE 1)))
```
