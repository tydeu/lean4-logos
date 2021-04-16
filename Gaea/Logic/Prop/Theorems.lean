import Gaea.Logic.Fun.Rules
import Gaea.Logic.Prop.Rules
import Gaea.Logic.Prop.Modules
import Gaea.Logic.Prop.Tactics
import Gaea.Logic.Rel.Rules

universe u
variable {P : Sort u}

namespace Gaea.Logic

instance iTautOfRefl {L : Logic P} {R} 
  [K : Refl L R] : Taut L R := {taut := fun p Lp => K.refl p}

--------------------------------------------------------------------------------
-- Implication
--------------------------------------------------------------------------------

-- Reflexivity
-- p -> (p -> p)

def impReflByImp {L : Logic P} 
{imp : Binar P} (ByI : Condition L imp)
: (p : P) -> (L |- p -> p)
:= by
  intro p
  condition Lp
  exact Lp 

instance iImpReflByImp {L : Logic P} 
{imp : Binar P} [ByI : Condition L imp] : Refl L imp 
:= {refl := impReflByImp ByI}

namespace MImp
abbrev Refl {L : Logic P} (K : MImp L) 
  : Refl L K.toFun := iImpReflByImp
abbrev refl {L : Logic P} (K : MImp L) := K.Refl.refl
abbrev rfl {L : Logic P} (K : MImp L) {p} := K.Refl.refl p
abbrev Taut {L : Logic P} (K : MImp L) 
  : Taut L K.toFun := iTautOfRefl
abbrev taut {L : Logic P} (K : MImp L) {p} := K.Taut.taut p
end MImp

-- Transitivity
-- (p -> q) -> (q -> r) -> (p -> r)

def impTransByImpMp {L : Logic P} 
{imp : Binar P} (ByI : Condition L imp) (Mp : ModusPonens L imp)
: (p q r : P) -> (L |- p -> q) -> (L |- q -> r) -> (L |- p -> r)
:= by
  intro p q r 
  assume LpTq LqTr
  condition Lp
  mp LqTr (mp LpTq Lp) 

instance iImpTransByImp {L : Logic P} 
{imp : Binar P} [ByI : Condition L imp] [Mp : ModusPonens L imp]
: Trans L imp := {trans := impTransByImpMp ByI Mp}

namespace MImp
abbrev Trans {L : Logic P} (K : MImp L) 
  : Trans L K.toFun := iImpTransByImp
abbrev trans {L : Logic P} (K : MImp L) {p q r} := K.Trans.trans p q r
end MImp

--------------------------------------------------------------------------------
-- Contraposition
--------------------------------------------------------------------------------

-- (~q -> ~p) -> (L |- p -> q)

def byContrapositionByDneImpContra 
{L : Logic P} {imp : Binar P} {lnot : Unar P}
(DnE : DblNegElim L lnot)
(ByI : Condition L imp)
(ByC : ByContradiction L lnot)
: (p q : P) -> ((L |- ~q) -> (L |- ~p)) -> (L |- p -> q)
:= by
  intro p q 
  assume LNq_to_LNp
  condition Lp
  dblNegElim
  byContradiction LNq
  have LNp := LNq_to_LNp LNq
  contradiction LNp Lp

instance iByContrapositionByDneImpContra 
{L : Logic P} {imp : Binar P} {lnot : Unar P}
[DnE : DblNegElim L lnot]
[ByI : Condition L imp]
[ByC : ByContradiction L lnot]
: ByContraposition L imp lnot :=
{byContraposition := byContrapositionByDneImpContra DnE ByI ByC}

-- (L |- p -> q) -> (L |- ~q -> ~p) 

def mtByMpContra
{L : Logic P} {imp : Binar P} {lnot : Unar P}
(Mp  : ModusPonens L imp) 
(ByC : ByContradiction L lnot)
: (p q : P) -> (L |- p -> q) -> (L |- ~q) -> (L |- ~p)
:= by
  intro p q 
  assume LpTq LNq
  byContradiction Lp
  have Lq := mp LpTq Lp
  contradiction LNq Lq

instance iModusTollensByMpContra 
{L : Logic P} {imp : Binar P} {lnot : Unar P}
[Mp  : ModusPonens L imp]
[ByC : ByContradiction L lnot]
: ModusTollens L imp lnot :=
{mt := mtByMpContra Mp ByC}

end Gaea.Logic