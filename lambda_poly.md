```{.haskell}
Def "f"
    (FnE 1 (AppE ( FreeE "p")
                 [ AppE (VarE 1) [FreeE "true"]
                 , AppE (VarE 1) [LitE (NumB 1.0)]
                 ]))
Eval (AppE (FreeE "f") [FnE 1 (VarE 1)])
```
