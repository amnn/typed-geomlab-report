```{.haskell}
Eval
    (IfE (FreeE "true")
         (LitE (NumB 1.0))
         (LitE (StrB "foo")))
```
