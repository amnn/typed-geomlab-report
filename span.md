```{.haskell}
data Point = P { line   :: !Int
               , col    :: !Int
               } deriving (Eq, Ord)

data Span  = S { start  :: !Point
               , offset :: !Int
               , width  :: !Int
               } deriving Eq
```
