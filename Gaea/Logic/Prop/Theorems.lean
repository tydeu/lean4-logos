import Gaea.Logic.Fun.Rules
import Gaea.Logic.Prop.Rules
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
-- p -> (|- p -> p)

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

-- Right Tautology
-- p -> (|- q) -> (|- p -> q)

def impRightTautByImp {L : Logic P} 
{imp : Binar P} (ByI : Condition L imp)
: (p q : P) -> (L |- q) -> (L |- p -> q)
:= by
  intro p q
  assume Lq
  condition Lp
  exact Lq 

instance iImpRightTautByImp {L : Logic P} 
{imp : Binar P} [ByI : Condition L imp] : RightTaut L imp 
:= {rightTaut := impRightTautByImp ByI}

-- Transitivity
-- (|- p -> q) -> (|- q -> r) -> (|- p -> r)

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

--------------------------------------------------------------------------------
-- Contraposition
--------------------------------------------------------------------------------

-- ((|- ~q) -> (|- ~p)) -> (|- p -> q)

def byContrapositionByDneImpContra 
{L : Logic P} {imp : Binar P} {lneg : Unar P}
(DnE : DblNegElim L lneg)
(ByI : Condition L imp)
(ByC : ByContradiction L lneg)
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
{L : Logic P} {imp : Binar P} {lneg : Unar P}
[DnE : DblNegElim L lneg]
[ByI : Condition L imp]
[ByC : ByContradiction L lneg]
: ByContraposition L imp lneg :=
{byContraposition := byContrapositionByDneImpContra DnE ByI ByC}

-- (|- p -> q) -> (|- ~q) -> (|- ~p) 

def mtByMpContra
{L : Logic P} {imp : Binar P} {lneg : Unar P}
(Mp  : ModusPonens L imp) 
(ByC : ByContradiction L lneg)
: (p q : P) -> (L |- p -> q) -> (L |- ~q) -> (L |- ~p)
:= by
  intro p q 
  assume LpTq LNq
  byContradiction Lp
  have Lq := mp LpTq Lp
  contradiction LNq Lq

instance iModusTollensByMpContra 
{L : Logic P} {imp : Binar P} {lneg : Unar P}
[Mp  : ModusPonens L imp]
[ByC : ByContradiction L lneg]
: ModusTollens L imp lneg :=
{mt := mtByMpContra Mp ByC}

end Gaea.Logic