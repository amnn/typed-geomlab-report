```{.haskell}
data Located a = L Span a deriving ( Eq, Show, Foldable
                                   , Functor, Traversable)
```
