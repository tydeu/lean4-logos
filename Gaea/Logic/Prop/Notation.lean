open Lean

namespace Gaea.Logic

scoped infixr:25 " -> "  => $(mkIdent `larr)
scoped infixr:25 " ⇒ "   => $(mkIdent `larr)

scoped infix:20 " <-> "  => $(mkIdent `iff)
scoped infix:20 " ⇔ "   => $(mkIdent `iff)

scoped infixr:35 " /\\ " => $(mkIdent `conj)
scoped infixr:35 " ∧ "   => $(mkIdent `conj)
scoped infixr:30 " \\/ " => $(mkIdent `disj)
scoped infixr:30 " ∨ "   => $(mkIdent `disj)

scoped prefix:max "~"    => $(mkIdent `lneg)
scoped prefix:max "¬"    => $(mkIdent `lneg)

end Gaea.Logic
