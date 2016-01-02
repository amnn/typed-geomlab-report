```{.haskell}
Eval
    (AppE ( FreeE "+")
          [ LitE (StrB "foo")
          , LitE (StrB "bar")
          ])
```
