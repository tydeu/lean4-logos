import Gaea.Logic.Fun.Rules

namespace Gaea.Logic

syntax binderIdent := ident <|> "_"

-- Prop Binding

declare_syntax_cat binderPat
syntax binderIdent : binderPat
syntax "(" binderPat,+ ")" : binderPat

scoped syntax (name := assume) 
  "assume " (colGt binderPat)+ : tactic
macro_rules [assume]
  | `(tactic| assume $x:binderIdent) => 
    `(tactic| intro $(x[0]))
  | `(tactic| assume ($x)) => 
    `(tactic| assume $x)
  | `(tactic| assume ($x, $ys,*)) => 
    `(tactic| apply uncurry; assume $x; assume ($ys,*))
  | `(tactic| assume $x $y $zs*) => 
    `(tactic| assume $x; assume $y $zs*)

scoped syntax (name := uncurryTactic) 
  "uncurry " (colGt binderPat)* : tactic
macro_rules [uncurryTactic]
  | `(tactic| uncurry) => 
    `(tactic| apply uncurry)
  | `(tactic| uncurry $x) => 
    `(tactic| apply uncurry; assume $x)
  | `(tactic| uncurry $x $y $ys*) => 
    `(tactic| uncurry $x; uncurry $y $ys*)

end Gaea.Logic
