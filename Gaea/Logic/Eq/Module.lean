import Gaea.Logic.Eq.Rules

namespace Gaea.Logic

universes u v
variable {P : Sort u} 

class MEq (L : Logic P) (T : Sort v) extends LEq P T :=
  toEqRefl : EqRefl L toLEq
  toEqPredSubst : EqPredSubst L toLEq

variable {T : Sort v}

instance iMEq {L : Logic P} 
  [Q: LEq P T] [R : EqRefl L Q] [P : EqPredSubst L Q] : MEq L T 
  := {toLEq := Q, toEqRefl := R, toEqPredSubst := P}

instance iEqReflOfMEq {L : Logic P} 
  [K : MEq L T] : EqRefl L K.toLEq  
  := {eqRefl := K.toEqRefl.eqRefl}

instance iEqPredSubstOfMEq {L : Logic P}
  [K : MEq L T] : EqPredSubst L K.toLEq  
  := {eqPredSubst := K.toEqPredSubst.eqPredSubst}

namespace MEq
abbrev lEq {L : Logic P} (K : MEq L T) 
  := K.toLEq.lEq
abbrev eqRefl {L : Logic P} (K : MEq L T) 
  := K.toEqRefl.eqRefl
abbrev refl {L : Logic P} (K : MEq L T) 
  := K.eqRefl
abbrev eqPredSubst {L : Logic P} (K : MEq L T) 
  := K.toEqPredSubst.eqPredSubst
abbrev predSubst {L : Logic P} (K : MEq L T) 
  := K.eqPredSubst
end MEq

end Gaea.Logic