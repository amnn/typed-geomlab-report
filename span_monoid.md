```{.haskell}
data Span = {- ... -} | Floating deriving Eq

instance Monoid Span where
  mempty = Floating

  mappend s Floating = s
  mappend Floating s = s

  mappend (S p m v) (S q o w) =
    S (p `min` q) off (end - off)
    where
      off = m `min` o
      end = (m + v) `max` (o + w)
```
