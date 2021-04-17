import Gaea.Logic.Rel.Rules
import Gaea.Logic.Fun.Rules
import Gaea.Logic.Unit.Rules
import Gaea.Logic.Dual.Rules
import Gaea.Logic.Unit.Tactics
import Gaea.Logic.Dual.Tactics

universe u
variable {P : Sort u}

namespace Gaea.Logic

--------------------------------------------------------------------------------
-- Contraposition
--------------------------------------------------------------------------------

-- ((|- ~q) -> (|- ~p)) -> (|- p -> q)

def byContrapositionByDneImpContra 
{L : Logic P} {larr : Binar P} {lneg : Unar P}
(DnE : DblNegElim L lneg)
(Cnd : Condition L larr)
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
{L : Logic P} {larr : Binar P} {lneg : Unar P}
[DnE : DblNegElim L lneg]
[Cnd : Condition L larr]
[ByC : ByContradiction L lneg]
: ByContraposition L larr lneg :=
{byContraposition := byContrapositionByDneImpContra DnE Cnd ByC}

-- (|- p -> q) -> (|- ~q) -> (|- ~p) 

def mtByMpContra
{L : Logic P} {larr : Binar P} {lneg : Unar P}
(Mp  : ModusPonens L larr) 
(ByC : ByContradiction L lneg)
: (p q : P) -> (L |- p -> q) -> (L |- ~q) -> (L |- ~p)
:= by
  intro p q 
  assume LpTq LNq
  byContradiction Lp
  have Lq := mp LpTq Lp
  contradiction LNq Lq

instance iModusTollensByMpContra 
{L : Logic P} {larr : Binar P} {lneg : Unar P}
[Mp  : ModusPonens L larr]
[ByC : ByContradiction L lneg]
: ModusTollens L larr lneg :=
{mt := mtByMpContra Mp ByC}

end Gaea.Logic