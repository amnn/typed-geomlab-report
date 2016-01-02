```{.haskell}
Def "f" (FnE 1 (FreeE "f"))
Def "g" (FnE 1 (AppE (FreeE "g") [FreeE "g"]))
Def "h" (FnE 1 (AppE (FreeE "p") [FreeE "h", FreeE "h"]))
```
