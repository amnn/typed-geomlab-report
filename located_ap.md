```{.haskell}
instance Applicative Located where
  pure                = L Floating
  (L s f) <*> (L t x) = L (s <> t) (f x)
```
