```{.haskell}
Def "length"
    (FnE 1 (CaseE ( VarE 1)
                  [ ( ValPB NilB
                    , LitE (NumB 0.0)
                    )
                  , ( ValPB (ConsB () ())
                    , AppE ( FreeE "+")
                           [ LitE (NumB 1.0)
                           , AppE (FreeE "length") [VarE 1]
                           ]
                    )
                  , ( VarPB "_", FailE)]))
```
