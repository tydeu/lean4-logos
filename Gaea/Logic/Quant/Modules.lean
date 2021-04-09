import Gaea.Logic.Logic
import Gaea.Logic.Quant.Rules
import Gaea.Logic.Quant.Syntax

universes u v
variable {P : Sort u} {T : Sort v}

namespace Gaea.Logic

-- Forall

class MForall (L : Logic P) (T : Sort v) extends LForall P T :=
  toForallGen : UnivGen L toLForall.lForall
  toForallInst : UnivInst L toLForall.lForall

instance iMForall {L : Logic P} 
  [Fa : LForall P T] [G : UnivGen L Fa.lForall] [I : UnivInst L Fa.lForall] :
  MForall L T := {toLForall := Fa, toForallGen := G, toForallInst := I}

namespace MForall
abbrev Forall {L : Logic P} (K : MForall L T) 
  := K.toLForall.lForall
abbrev toUnivGen {L : Logic P} (K : MForall L T) 
  := K.toForallGen
abbrev forallGen {L : Logic P} (K : MForall L T) 
  := K.toForallGen.ug
abbrev gen {L : Logic P} (K : MForall L T) 
  {f} := K.forallGen f
abbrev intro {L : Logic P} (K : MForall L T) 
  {f} := K.forallGen f
abbrev toUnivInst {L : Logic P} (K : MForall L T) 
  := K.toForallInst
abbrev forallInst {L : Logic P} (K : MForall L T) 
  := K.toForallInst.ui
abbrev inst {L : Logic P} (K : MForall L T) 
  {f} := K.forallInst f
abbrev elim {L : Logic P} (K : MForall L T) 
  {f} := K.forallInst f
end MForall

instance iUnivGenOfMForall {L : Logic P} [K : MForall L T] :
  UnivGen L K.Forall := K.toForallGen

instance iUnivInstOfMForall {L : Logic P} [K : MForall L T] :
  UnivInst L K.Forall := K.toForallInst

-- Exists

class MExists (L : Logic P) (T : Sort v) extends LExists P T :=
  toExistsGen : ExstGen L toLExists.lExists
  toExistsInst : ExstInst L toLExists.lExists

namespace MExists
abbrev Exists {L : Logic P} (K : MExists L T) 
  := K.toLExists.lExists
abbrev existsGen {L : Logic P} (K : MExists L T) 
  := K.toExistsGen.xg
abbrev gen {L : Logic P} (K : MExists L T) 
  {f} := K.existsGen f
abbrev intro {L : Logic P} (K : MExists L T) 
  {f} := K.existsGen f
abbrev existsInst {L : Logic P} (K : MExists L T) 
  := K.toExistsInst.xi
abbrev inst {L : Logic P} (K : MExists L T) 
  {f} := K.existsInst f
abbrev elim {L : Logic P} (K : MExists L T) 
  {f} := K.existsInst f
end MExists

instance iMExists {L : Logic P} 
  [X : LExists P T] [G : ExstGen L X.lExists] [I : ExstInst L X.lExists] :
  MExists L T := {toLExists := X, toExistsGen := G, toExistsInst := I}

instance iExistsIntroOfMExists {L : Logic P} [K : MExists L T] :
  ExstGen L K.Exists := K.toExistsGen

instance iExistsElimOfMExists {L : Logic P} [K : MExists L T] :
  ExstInst L K.Exists := K.toExistsInst

end Gaea.Logic
