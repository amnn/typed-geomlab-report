```{.haskell}
-- Top Level
data Para a = Def Id a | Eval a

-- Common Definitions
type Id = String

data LitB a   = NumB Double
              | StrB String
              | NilB
              | AtomB Id
              | ConsB a a

-- Patterns
data Patt     = ValP (LitB Patt) | VarP Id

data GenB a   = GenB Patt a | FilterB a
data FnArmB a = FnArm Id [Patt] a (Maybe a)

type Gen   = GenB Sugar
type FnArm = FnarmB Sugar

-- Expressions
data Sugar = LitS (LitB Sugar)
           | ListCompS Sugar [Gen]
           | RangeS Sugar Sugar
           | VarS Id
           | IfS Sugar Sugar Sugar
           | FnS [FnArm]
           | AppS Id [Sugar]
           | LSectS Sugar Id
           | RSectS Id Sugar
           | LetS Id Sugar Sugar
           | SeqS Sugar Sugar
```
