import Gaea.Logic.Eq.Rules
import Gaea.Logic.Eq.Module
import Gaea.Logic.Rel.Theorems

universes u v

namespace Gaea.Logic

instance iMEqFunSubst 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : MEq L T]
: EqFunSubst L Q.toLEq := 
{eqFunSubst := funSubstByReflPredSubst iReflOfEqRefl iPredSubstOfEqPredSubst}

instance iMEqSymm 
{P : Sort u} {T : Sort v} {L : Logic P} [Q : MEq L T]
: EqSymm L Q.toLEq := 
{eqSymm := symmByReflPredSubst iReflOfEqRefl iPredSubstOfEqPredSubst}

instance iMEqTrans
{P : Sort u} {T : Sort v} {L : Logic P} [Q : MEq L T]
: EqTrans L Q.toLEq := {eqTrans := transByPredSubst iPredSubstOfEqPredSubst}

end Gaea.Logic