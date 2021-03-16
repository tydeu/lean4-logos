import Gaea.Logic
import Gaea.Syntax
import Gaea.Peano.Rules
import Gaea.Peano.Eq.Rules

universes u v w

open Gaea.Logic
open Gaea.Syntax

namespace Gaea.Peano

-- (b = a) /\ (c = a) -> (b = c)

def eqNatLeftEuc_proof {P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [EqNatSymm L N Q] [EqNatTrans L N Q]
: (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
    (L |- b = a) -> (L |- c = a) -> (L |- b = c)
:= by
  intro a b c Na Nb Nc Qba Qca
  have Qac := eqNatSymm Nc Na Qca
  exact eqNatTrans Nb Na Nc Qba Qac

instance eqNatLeftEuc_inst {P : Sort u} {T : Type v} {L : Logic P}
  [N : IsNat P T] [Q : LEq P T] [EqNatSymm L N Q] [EqNatTrans L N Q]
  : EqNatLeftEuc L N Q := {eqNatLeftEuc := eqNatLeftEuc_proof}

-- (b = a) /\ (c = a) -> (b = c)

def eqNatRightEuc_proof {P : Sort u} {T : Type v} {L : Logic P}
[N : IsNat P T] [Q : LEq P T] [EqNatSymm L N Q] [EqNatTrans L N Q]
: (a b c : T) -> 
    (L |- nat a) -> (L |- nat b) -> (L |- nat c) -> 
    (L |- a = b) -> (L |- a = c) -> (L |- b = c)
:= by
  intro a b c Na Nb Nc Qab Qac
  have Qba := eqNatSymm Na Nb Qab
  exact eqNatTrans Nb Na Nc Qba Qac

instance eqNatRightEuc_inst {P : Sort u} {T : Type v} {L : Logic P}
  [N : IsNat P T] [Q : LEq P T] [EqNatSymm L N Q] [EqNatTrans L N Q]
  : EqNatRightEuc L N Q := {eqNatRightEuc := eqNatRightEuc_proof}

end Gaea.Peano