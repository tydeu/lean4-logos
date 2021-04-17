import Gaea.Logic.Dual.Rules

universes u
variable {P : Sort u}

namespace Gaea.Logic

--------------------------------------------------------------------------------
-- False
--------------------------------------------------------------------------------

-- False -> (|- falsum)

class ImportFalse (L : Logic P) (falsum : P) := 
  importFalse : False -> (L |- falsum) 

abbrev importFalse {L : Logic P} {falsum}
  [K : ImportFalse L falsum] := K.importFalse

instance iImportFalse {L : Logic P} {p} 
  : ImportFalse L p := {importFalse := False.elim}

-- (|- falsum) -> False

class ExportFalse (L : Logic P) (falsum : P) := 
  exportFalse : (L |- falsum) -> False

abbrev exportFalse {L : Logic P} {falsum}
  [K : ExportFalse L falsum] := K.exportFalse

instance iExFalsumOfExportFalse {L : Logic P} {falsum}
  [K : ExportFalse L falsum] : ExFalsum L falsum 
  := {exFalsum := fun p Lf => False.elim (K.exportFalse Lf)}

--------------------------------------------------------------------------------
-- Not
--------------------------------------------------------------------------------

-- Not p -> (|- ~p)

class ImportNot (L : Logic.{u,0} P) (lneg : Unar P) := 
  importNot : (p : P) -> Not (L |- p) -> (L |- lneg p) 

abbrev importNot {L : Logic.{u,0} P} {lneg}
  [K : ImportNot L lneg] {p} := K.importNot p

instance iImportNotOfAdFalso 
  {L : Logic.{u,0} P} {lneg} [K : ImportNot L lneg] : AdFalso L lneg := 
  {adFalso := K.importNot}

instance iAdFalsoOfImportNot 
  {L : Logic.{u,0} P} {lneg} [K : AdFalso L lneg] : ImportNot L lneg := 
  {importNot := K.adFalso}

-- (|- ~p) -> Not p

class ExportNot (L : Logic.{u,0} P) (lneg : Unar P) := 
  exportNot : (p : P) -> (L |- lneg p) -> Not (L |- p) 

abbrev exportNot {L : Logic.{u,0} P} {lneg}
  [K : ExportNot L lneg] {p} := K.exportNot p

instance iExportNotOfNoncontradiction 
  {L : Logic.{u,0} P} {lneg} [K : ExportNot L lneg] : Noncontradiction L lneg := 
  {noncontradiction := K.exportNot}

instance iNoncontradictionOfExportNot
  {L : Logic.{u,0} P} {lneg} [K : Noncontradiction L lneg] : ExportNot L lneg := 
  {exportNot := K.noncontradiction}
  
end Gaea.Logic