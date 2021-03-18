import Gaea.Logic.Eq.Rules

universes u v

namespace Gaea.Logic

class MEq {P : Sort u} (L : Logic P) (T : Sort v) extends LEq P T :=
  (toEqRefl : EqRefl L toLEq)
  (toEqPredSubst : EqPredSubst L toLEq)

instance {P : Sort u} {T : Sort v} {L : Logic P} 
  [Q: LEq P T] [R : EqRefl L Q] [P : EqPredSubst L Q] :
  MEq L T := {toLEq := Q, toEqRefl := R, toEqPredSubst := P}

instance {P : Sort u} {T : Sort v} {L : Logic P} 
  [K : MEq L T] : EqRefl L K.toLEq  
  := {eqRefl := K.toEqRefl.eqRefl}

instance {P : Sort u} {T : Sort v} {L : Logic P}
  [K : MEq L T] : EqPredSubst L K.toLEq  
  := {eqPredSubst := K.toEqPredSubst.eqPredSubst}

namespace MEq
abbrev eqRefl {P : Sort u} {T : Sort v} {L : Logic P} (K : MEq L T) 
  := K.toEqRefl.eqRefl
abbrev eqPredSubst {P : Sort u} {T : Sort v} {L : Logic P} (K : MEq L T) 
  := K.toEqPredSubst.eqPredSubst
end MEq

end Gaea.Logic