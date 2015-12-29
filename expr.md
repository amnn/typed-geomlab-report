```{.haskell}
data PattB a    = ValP (LitB a) | VarP Id
type SimplePatt = PattB ()

data Expr = LitE (LitB Expr)
          | VarE !Int
          | FreeE Id
          | IfE Expr Expr Expr
          | CaseE Expr [(SimplePatt, Expr)]
          | FnE !Int Expr
          | AppE Expr [Expr]
          | LetE Expr Expr
          | SeqE Expr Expr
          | FailE
          | FallThroughE
```
