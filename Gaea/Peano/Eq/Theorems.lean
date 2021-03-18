import Gaea.Peano.Rules
import Gaea.Peano.Eq.Rules
import Gaea.Logic.Eq.Theorems

open Gaea.Logic

namespace Gaea.Peano 

-- (a = b) /\ (b = c) -> (a = c)

def eqTransNat_proof {P : Sort u} {T : Type v} 
{L : Logic P} [N : IsNat P T] [Q : LEq P T] [EqNatTrans L N Q] [NatEqNat L N Q]
: (a b c : T) -> (L |- nat c) -> (L |- a = b) -> (L |- b = c) -> (L |- a = c)
:= by
  intro a b c Nc Qab Qbc
  have Nb := natEq Nc Qbc
  have Na := natEq Nb Qab
  exact eqNatTrans Na Nb Nc Qab Qbc

instance eqTransNat_inst {P : Sort u} {T : Type v} 
{L : Logic P} [N : IsNat P T] [Q : LEq P T] [EqNatTrans L N Q] [NatEqNat L N Q]
: EqTransNat L N Q := {eqTransNat := eqTransNat_proof}

-- (b = a) /\ (c = a) -> (b = c)

def eqLeftEucNat_proof {P : Sort u} {T : Type v} 
{L : Logic P} [N : IsNat P T] [Q : LEq P T] [EqNatLeftEuc L N Q] [NatEqNat L N Q]
: (a b c : T) -> (L |- nat a) -> (L |- b = a) -> (L |- c = a) -> (L |- b = c)
:= by
  intro a b c Na Qba Qca
  have Nb := natEq Na Qba
  have Nc := natEq Na Qca
  exact eqNatLeftEuc Na Nb Nc Qba Qca

instance eqLeftEucNat_inst {P : Sort u} {T : Type v} 
{L : Logic P} [N : IsNat P T] [Q : LEq P T] [EqNatLeftEuc L N Q] [NatEqNat L N Q]
: EqLeftEucNat L N Q := {eqLeftEucNat := eqLeftEucNat_proof}

end Gaea.Peano
