import Gaea.Logic.Fun.Rules
import Gaea.Logic.Prop.Rules
import Gaea.Logic.Prop.Modules
import Gaea.Logic.Prop.Tactics
import Gaea.Logic.Rel.Rules

namespace Gaea.Logic

universe u
variable {P : Sort u}

--------------------------------------------------------------------------------
-- Implication
--------------------------------------------------------------------------------

-- Reflexivity
-- p -> (p -> p)

def impReflByImp {L : Logic P} 
{imp : Binar P} (ByI : ByImplication L imp)
: (p : P) -> (L |- p -> p)
:= by
  intro p
  byImplication Lp
  exact Lp 

instance iImpReflByImp {L : Logic P} 
{imp : Binar P} [ByI : ByImplication L imp] : Refl L imp 
:= {refl := impReflByImp ByI}

namespace MImp
abbrev toRefl {L : Logic P} (K : MImp L) : Refl L K.imp := iImpReflByImp
abbrev impRefl {L : Logic P} (K : MImp L) := K.toRefl.refl
abbrev refl {L : Logic P} (K : MImp L) := K.impRefl
-- abbrev toTaut {L : Logic P} (K : MImp L) : Taut L K.imp := iTautOfLRefl
-- abbrev impTaut {L : Logic P} (K : MImp L) := K.toTaut.taut
-- abbrev taut {L : Logic P} (K : MImp L) {p} := K.impTaut p
end MImp

-- Transitivity
-- (p -> q) -> (q -> r) -> (p -> r)

def impTransByImpMp {L : Logic P} 
{imp : Binar P} (ByI : ByImplication L imp) (Mp : ModusPonens L imp)
: (p q r : P) -> (L |- p -> q) -> (L |- q -> r) -> (L |- p -> r)
:= by
  intro p q r 
  intro LpTq LqTr
  byImplication Lp
  mp LqTr (mp LpTq Lp) 

instance iImpTransByImp {L : Logic P} 
{imp : Binar P} [ByI : ByImplication L imp] [Mp : ModusPonens L imp]
: Trans L imp := {trans := impTransByImpMp ByI Mp}

namespace MImp
abbrev toTrans {L : Logic P} (K : MImp L) : Trans L K.imp := iImpTransByImp
abbrev impTrans {L : Logic P} (K : MImp L) := K.toTrans.trans
abbrev trans {L : Logic P} (K : MImp L) {p q r} := K.impTrans p q r
end MImp

--------------------------------------------------------------------------------
-- Contraposition
--------------------------------------------------------------------------------

-- (~q -> ~p) -> (L |- p -> q)

def byContrapositionByDneImpContra 
{L : Logic P} {imp : Binar P} {lnot : Unar P}
(DnE : DblNegElim L lnot)
(ByI : ByImplication L imp)
(ByC : ByContradiction L lnot)
: (p q : P) -> ((L |- ~q) -> (L |- ~p)) -> (L |- p -> q)
:= by
  intro p q 
  intro Nq_to_Np
  byImplication Lp
  dblNegElim
  byContradiction LNq
  have LNp := Nq_to_Np LNq
  contradiction LNp Lp

instance iByContrapositionByDneImpContra 
{L : Logic P} {imp : Binar P} {lnot : Unar P}
[DnE : DblNegElim L lnot]
[ByI : ByImplication L imp]
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
  intro LpTq LNq
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