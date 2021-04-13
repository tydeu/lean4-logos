import Gaea.Logic.Logic

namespace Gaea.Logic

def Judgment.{u,v} {P : Sort u}  (L : Logic.{u,v} P) (prop : P) : Sort v :=
  L.judgment prop

scoped infix:10 " |- " => Judgment
scoped infix:10 " ⊢ " => Judgment

end Gaea.Logic