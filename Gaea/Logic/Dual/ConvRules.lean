import Gaea.Logic.Dual.Rules

universes u
variable {P : Sort u}

namespace Gaea.Logic

--------------------------------------------------------------------------------
-- False
--------------------------------------------------------------------------------

-- False -> (|- falsum)

class ImportFalse (L : Logic P) (falsum : P) := 
  toFun : False -> (L |- falsum) 

abbrev importFalse {L : Logic P} {falsum}
  [K : ImportFalse L falsum] := K.toFun

instance iImportFalse {L : Logic P} {p} 
  : ImportFalse L p := {toFun := False.elim}

-- (|- falsum) -> False

class ExportFalse (L : Logic P) (falsum : P) := 
  toFun : (L |- falsum) -> False

abbrev exportFalse {L : Logic P} {falsum}
  [K : ExportFalse L falsum] := K.toFun

instance iExFalsumOfExportFalse {L : Logic P} {falsum}
  [K : ExportFalse L falsum] : ExFalsum L falsum 
  := {toFun := fun p Lf => False.elim (K.toFun Lf)}

--------------------------------------------------------------------------------
-- Not
--------------------------------------------------------------------------------

-- Not p -> (|- ~p)

class ImportNot (L : Logic.{u,0} P) (lneg : Unar P) := 
  toFun : (p : P) -> Not (L |- p) -> (L |- lneg p) 

abbrev importNot {L : Logic.{u,0} P} {lneg}
  [K : ImportNot L lneg] {p} := K.toFun p

instance iImportNotOfAdFalso {L : Logic.{u,0} P} {lneg} 
  [K : ImportNot L lneg] : AdFalso L lneg :=  {toFun := K.toFun}

instance iAdFalsoOfImportNot {L : Logic.{u,0} P} {lneg} 
  [K : AdFalso L lneg] : ImportNot L lneg :=  {toFun := K.toFun}

-- (|- ~p) -> Not p

class ExportNot (L : Logic.{u,0} P) (lneg : Unar P) := 
  toFun : (p : P) -> (L |- lneg p) -> Not (L |- p) 

abbrev exportNot {L : Logic.{u,0} P} {lneg}
  [K : ExportNot L lneg] {p} := K.toFun p

instance iExportNotOfNoncontradiction {L : Logic.{u,0} P} {lneg} 
  [K : ExportNot L lneg] : Noncontradiction L lneg := {toFun := K.toFun}

instance iNoncontradictionOfExportNot {L : Logic.{u,0} P} {lneg} 
  [K : Noncontradiction L lneg] : ExportNot L lneg := {toFun := K.toFun}
