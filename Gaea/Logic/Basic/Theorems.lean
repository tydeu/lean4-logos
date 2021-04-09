import Gaea.Logic.Rules
import Gaea.Logic.Basic.Rules
import Gaea.Logic.Basic.Modules
import Gaea.Logic.Basic.Tactics
import Gaea.Logic.Rel.Rules

namespace Gaea.Logic

universe u
variable {P : Sort u}

--------------------------------------------------------------------------------
-- Im
--------------------------------------------------------------------------------

-- Reflexitivity
-- p -> (p -> p)

def ifReflByAssump {L : Logic P} 
{Im : Imp P} (ByA : ByAssumption L Im.imp)
: (p : P) -> (L |- p -> p)
:= by
  intro p
  byAssumption Lp
  exact Lp 

instance iIfReflByAssump {L : Logic P} 
  [Im : Imp P] [ByA : ByAssumption L Im.imp] : LRefl L Im.imp 
  := {lRefl := ifReflByAssump ByA}

namespace MImp
abbrev toLRefl {L : Logic P} (K : MImp L) : LRefl L K.imp := iIfReflByAssump
abbrev toRefl {L : Logic P} (K : MImp L) : Refl L K.imp := iReflOfLRefl
abbrev ifRefl {L : Logic P} (K : MImp L) := K.toLRefl.lRefl
abbrev refl {L : Logic P} (K : MImp L) := K.ifRefl
abbrev toTaut {L : Logic P} (K : MImp L) : Taut L K.imp := iTautOfLRefl
abbrev ifTaut {L : Logic P} (K : MImp L) := K.toTaut.taut
abbrev taut {L : Logic P} (K : MImp L) {p} := K.ifTaut p
end MImp

-- Transitivity
-- (p -> q) -> (q -> r) -> (p -> r)

def ifTransByMpAssump {L : Logic P} 
{Im : Imp P} (ByA : ByAssumption L Im.imp) (Mp : ModusPonens L Im.imp)
: (p q r : P) -> (L |- p -> q) -> (L |- q -> r) -> (L |- p -> r)
:= by
  intro p q r LpTq LqTr
  byAssumption Lp
  mp LqTr (mp LpTq Lp) 

instance iIfTransByMpAssump {L : Logic P} 
[Im : Imp P] [ByA : ByAssumption L Im.imp] [Mp : ModusPonens L Im.imp]
: LTrans L Im.imp := {lTrans := ifTransByMpAssump ByA Mp}

namespace MImp
abbrev toLTrans {L : Logic P} (K : MImp L) : LTrans L K.imp := iIfTransByMpAssump
abbrev toTrans {L : Logic P} (K : MImp L) : Trans L K.imp := iTransOfLTrans
abbrev ifTrans {L : Logic P} (K : MImp L) := K.toLTrans.lTrans
abbrev trans {L : Logic P} (K : MImp L) {p q r} := K.ifTrans p q r
end MImp

--------------------------------------------------------------------------------
-- Contrapositive
--------------------------------------------------------------------------------

-- (~q -> ~p) -> (L |- p -> q)

def byContrapositionByIfDneNot 
{L : Logic P} {Im : Imp P} {Nt : LNot P}
(DnE : DblNegElim L Nt)
(ByA : ByAssumption L Im.imp)
(ByC : ByContradiction L Nt)
: (p q : P) -> ((L |- ~q) -> (L |- ~p)) -> (L |- p -> q)
:= by
  intro p q Nq_to_Np
  byAssumption Lp
  apply dblNegElim
  byContradiction LNq
  have LNp := Nq_to_Np LNq
  contradiction Lp LNp

instance iByContrapositionByIfDneNot
{L : Logic P} [Im : Imp P] [Nt : LNot P]
[DnE : DblNegElim L Nt]
[ByA : ByAssumption L Im.imp]
[ByC : ByContradiction L Nt]
: ByContraposition L Im.imp Nt :=
{byContraposition := byContrapositionByIfDneNot DnE ByA ByC}

-- (L |- p -> q) -> (L |- ~q -> ~p) 

def mtByMpContra
{L : Logic P} {Im : Imp P} {Nt : LNot P}
(Mp  : ModusPonens L Im.imp) 
(ByC : ByContradiction L Nt)
: (p q : P) -> (L |- p -> q) -> (L |- ~q) -> (L |- ~p)
:= by
  intro p q LpTq LNq
  byContradiction Lp
  have Lq := mp LpTq Lp
  contradiction Lq LNq

instance iModusTollensByMpContra 
{L : Logic P} [Im : Imp P] [Nt : LNot P]
[Mp  : ModusPonens L Im.imp]
[ByC : ByContradiction L Nt]
: ModusTollens L Im.imp Nt :=
{mt := mtByMpContra Mp ByC}

end Gaea.Logic