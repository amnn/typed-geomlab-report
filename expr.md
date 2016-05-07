```{.haskell}
data PattB a    = ValP (LitB a) | VarP Id
type SimplePatt = PattB ()

data Expr = LitE (LitB Expr)
          | VarE !Int | FreeE Id
          | CaseE Expr [(SimplePatt, Expr)]
          | FnE !Int Expr
          | AppE Expr [Expr]
          | LetE Expr Expr
```
