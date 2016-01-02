```{.haskell}
Def "foldr"
    (FnE 3 (CaseE (VarE 1)
                [ ( ValPB NilB, VarE 2)
                , ( ValPB (ConsB () ())
                  , AppE ( VarE 5)
                         [ VarE 2
                         , AppE (FreeE "foldr")
                                [VarE 5, VarE 4, VarE 1]
                         ]
                  )
                , ( VarPB "_", FailE)]))

Def "filter"
    (FnE 2 (LetE (FnE 2 (IfE (AppE (VarE 5) [VarE 2])
                             (AppE (FreeE ":") [VarE 2, VarE 1])
                             (VarE 1)))
           (AppE (FreeE "foldr")
                 [VarE 1, LitE NilB, VarE 2])))
```
