import Gaea.Logic.Prop.Rules

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

class ImportNot (L : Logic.{u,0} P) (lnot : Unar P) := 
  importNot : (p : P) -> Not (L |- p) -> (L |- lnot p) 

abbrev importNot {L : Logic.{u,0} P} {lnot}
  [K : ImportNot L lnot] {p} := K.importNot p

instance iImportNotOfAdFalso 
  {L : Logic.{u,0} P} {lnot} [K : ImportNot L lnot] : AdFalso L lnot := 
  {adFalso := K.importNot}

instance iAdFalsoOfImportNot 
  {L : Logic.{u,0} P} {lnot} [K : AdFalso L lnot] : ImportNot L lnot := 
  {importNot := K.adFalso}

-- (|- ~p) -> Not p

class ExportNot (L : Logic.{u,0} P) (lnot : Unar P) := 
  exportNot : (p : P) -> (L |- lnot p) -> Not (L |- p) 

abbrev exportNot {L : Logic.{u,0} P} {lnot}
  [K : ExportNot L lnot] {p} := K.exportNot p

instance iExportNotOfNoncontradiction 
  {L : Logic.{u,0} P} {lnot} [K : ExportNot L lnot] : Noncontradiction L lnot := 
  {noncontradiction := K.exportNot}

instance iNoncontradictionOfExportNot
  {L : Logic.{u,0} P} {lnot} [K : Noncontradiction L lnot] : ExportNot L lnot := 
  {exportNot := K.noncontradiction}

--------------------------------------------------------------------------------
-- Prod/PProd/And
--------------------------------------------------------------------------------

-- Prod p q -> (|- p /\ q)

class ImportProd (L : Logic P) (conj : Binar P) := 
  importProd : (p q : P) -> Prod (L |- p) (L |- q) -> (L |- p /\ q)

abbrev importProd {L : Logic P} {conj} 
  [K : ImportProd L conj] {p q} := K.importProd p q

instance iConjunctionOfImportProd {L : Logic P} {conj} 
  [K : ImportProd L conj] : Conjunction L conj := 
  {conjoin := fun p q Lp Lq => K.importProd p q (Prod.mk Lp Lq)}

instance iImportProdOfConjunction {L : Logic P} {conj} 
  [K : Conjunction L conj] : ImportProd L conj := 
  {importProd := fun p q Ppq => K.conjoin p q Ppq.fst Ppq.snd}

-- PProd p q -> (|- p /\ q)

class ImportPProd (L : Logic P) (conj : Binar P) := 
  importPProd : (p q : P) -> PProd (L |- p) (L |- q) -> (L |- p /\ q)

abbrev importPProd {L : Logic P} {conj} 
  [K : ImportPProd L conj] {p q} := K.importPProd p q

instance iConjunctionOfImportPProd {L : Logic P} {conj} 
  [K : ImportPProd L conj] : Conjunction L conj := 
  {conjoin := fun p q Lp Lq => K.importPProd p q (PProd.mk Lp Lq)}

instance iImportPProdOfConjunction {L : Logic P} {conj} 
  [K : Conjunction L conj] : ImportPProd L conj := 
  {importPProd := fun p q Ppq => K.conjoin p q Ppq.fst Ppq.snd}

instance iImportProdOfImportPProd {L : Logic P} {conj} 
  [K : ImportPProd L conj] : ImportProd L conj := 
  {importProd := fun p q Ppq => K.importPProd p q (PProd.mk (Ppq.fst) (Ppq.snd))}

-- And p q -> (|- p /\ q)

class ImportAnd (L : Logic.{u,0} P) (conj : Binar P) := 
  importAnd : (p q : P) -> ((L |- p) /\ (L |- q)) -> (L |- p /\ q)

abbrev importAnd {L : Logic.{u,0} P} {conj} 
  [K : ImportAnd L conj] {p q} := K.importAnd p q

instance iConjunctionOfAnd {L : Logic P} {conj} 
  [K : ImportAnd L conj] : Conjunction L conj := 
  {conjoin := fun p q Lp Lq => K.importAnd p q (And.intro Lp Lq)}

instance iImportAndOfConjunction {L : Logic P} {conj} 
  [K : Conjunction L conj] : ImportAnd L conj := 
  {importAnd := fun p q Apq => K.conjoin p q Apq.left Apq.right}

-- (|- p /\ q) -> Prod p q

class ExportProd (L : Logic P) (conj : Binar P) := 
  exportProd : (p q : P) -> (L |- p /\ q) -> Prod (L |- p) (L |- q)

abbrev exportProd {L : Logic P} {conj} 
  [K : ExportProd L conj] {p q} := K.exportProd p q

instance iExportProdOfLeftRight {L : Logic P} {conj}
  [CjL : LeftSimp L conj] [CjR : RightSimp L conj] : ExportProd L conj := 
  {exportProd := fun p q LpCq => Prod.mk (leftSimp LpCq) (rightSimp LpCq)}

instance iLeftSimpOfExportProd {L : Logic P} {conj}
  [K : ExportProd L conj] : LeftSimp L conj := 
  {leftSimp := fun p q LpCq => Prod.fst (K.exportProd p q LpCq)}

instance iRightSimpOfExportProd {L : Logic P} {conj}
  [K : ExportProd L conj] : RightSimp L conj := 
  {rightSimp := fun p q LpCq => Prod.snd (K.exportProd p q LpCq)}

-- (|- p /\ q) -> PProd p q

class ExportPProd (L : Logic P) (conj : Binar P) := 
  exportPProd : (p q : P) -> (L |- p /\ q) -> PProd (L |- p) (L |- q)

abbrev exportPProd {L : Logic P} {conj} 
  [K : ExportPProd L conj] {p q} := K.exportPProd p q

instance iExportPProdOfLeftRight {L : Logic P} {conj}
  [CjL : LeftSimp L conj] [CjR : RightSimp L conj] : ExportPProd L conj := 
  {exportPProd := fun p q LpCq => PProd.mk (leftSimp LpCq) (rightSimp LpCq)}

instance iLeftSimpOfExportPProd {L : Logic P} {conj}
  [K : ExportPProd L conj] : LeftSimp L conj := 
  {leftSimp := fun p q LpCq => PProd.fst (K.exportPProd p q LpCq)}

instance iRightSimpOfExportPProd {L : Logic P} {conj}
  [K : ExportPProd L conj] : RightSimp L conj := 
  {rightSimp := fun p q LpCq => PProd.snd (K.exportPProd p q LpCq)}

instance iExportProdOfPProd {L : Logic P} {conj}
  [K : ExportPProd L conj] : ExportProd L conj := 
  {exportProd := fun p q LpCq => Prod.mk (leftSimp LpCq) (rightSimp LpCq)}

-- (|- p /\ q) -> And p q

class ExportAnd (L : Logic.{u,0} P) (conj : Binar P) := 
  exportAnd : (p q : P) -> (L |- p /\ q) -> (L |- p) /\ (L |- q)

abbrev exportAnd {L : Logic.{u,0} P} {conj} 
  [K : ExportAnd L conj] {p q} := K.exportAnd p q

instance iExportAndOfLeftRight {L : Logic P} {conj}
  [CjL : LeftSimp L conj] [CjR : RightSimp L conj] : ExportAnd L conj := 
  {exportAnd := fun p q LpCq => And.intro (leftSimp LpCq) (rightSimp LpCq)}

instance iLeftSimpOfExportAnd {L : Logic P} {conj}
  [K : ExportAnd L conj] : LeftSimp L conj := 
  {leftSimp := fun p q LpCq => And.left (K.exportAnd p q LpCq)}

instance iRightSimpOfExportAnd {L : Logic P} {conj}
  [K : ExportAnd L conj] : RightSimp L conj := 
  {rightSimp := fun p q LpCq => And.right (K.exportAnd p q LpCq)}

--------------------------------------------------------------------------------
-- Sum/PSum/Or
--------------------------------------------------------------------------------

-- Sum p q -> (|- p \/ q)

class ImportSum (L : Logic P) (disj : Binar P) := 
  importSum : (p q : P) -> Sum (L |- p) (L |- q) -> (L |- p \/ q)

abbrev importSum {L : Logic P} {disj} 
  [K : ImportSum L disj] {p q} := K.importSum p q

instance iImportSumOfLeftRightTaut {L : Logic P} {disj} 
  [DiL : LeftTaut L disj] [DiR : RightTaut L disj] : ImportSum L disj := 
  {importSum := fun p q Spq => match Spq with 
    | Sum.inl Lp => leftTaut Lp | Sum.inr Lq => rightTaut Lq}

instance iLeftTautOfImportSum {L : Logic P} {disj} 
  [K : ImportSum L disj] : LeftTaut L disj := 
  {leftTaut := fun p q Lp => K.importSum p q (Sum.inl Lp)}

instance iRightTautOfImportSum {L : Logic P} {disj} 
  [K : ImportSum L disj] : RightTaut L disj := 
  {rightTaut := fun p q Lq => K.importSum p q (Sum.inr Lq)}

-- PSum p q -> (|- p \/ q) 

class ImportPSum (L : Logic P) (disj : Binar P) := 
  importPSum : (p q : P) -> PSum (L |- p) (L |- q) -> (L |- p \/ q)

abbrev importPSum {L : Logic P} {disj} 
  [K : ImportPSum L disj] {p q} := K.importPSum p q

instance iImportPSumOfLeftRightTaut {L : Logic P} {disj} 
  [DiL : LeftTaut L disj] [DiR : RightTaut L disj] : ImportPSum L disj := 
  {importPSum := fun p q Spq => match Spq with 
    | PSum.inl Lp => leftTaut Lp | PSum.inr Lq => rightTaut Lq}

instance iLeftTautOfImportPSum {L : Logic P} {disj} 
  [K : ImportPSum L disj] : LeftTaut L disj := 
  {leftTaut := fun p q Lp => K.importPSum p q (PSum.inl Lp)}

instance iRightTautOfImportPSum {L : Logic P} {disj} 
  [K : ImportPSum L disj] : RightTaut L disj := 
  {rightTaut := fun p q Lq => K.importPSum p q (PSum.inr Lq)}

-- Or p q -> (|- p \/ q) 

class ImportOr (L : Logic.{u,0} P) (disj : Binar P) := 
  importOr : (p q : P) -> ((L |- p) \/ (L |- q)) -> (L |- p \/ q)

abbrev importOr {L : Logic.{u,0} P} {disj} 
  [K : ImportOr L disj] {p q} := K.importOr p q

instance iImportOrOfLeftRightTaut {L : Logic P} {disj} 
  [DiL : LeftTaut L disj] [DiR : RightTaut L disj] : ImportOr L disj := 
  {importOr := fun p q Spq => match Spq with 
    | Or.inl Lp => leftTaut Lp | Or.inr Lq => rightTaut Lq}

instance iLeftTautOfImportOr {L : Logic P} {disj} 
  [K : ImportOr L disj] : LeftTaut L disj := 
  {leftTaut := fun p q Lp => K.importOr p q (Or.inl Lp)}

instance iRightTautOfImportOr {L : Logic P} {disj} 
  [K : ImportOr L disj] : RightTaut L disj := 
  {rightTaut := fun p q Lq => K.importOr p q (Or.inr Lq)}

-- (|- p \/ q) -> Sum p q 

class ExportSum (L : Logic P) (disj : Binar P) := 
  exportSum : (p q : P) -> (L |- p \/ q) -> Sum (L |- p) (L |- q)

abbrev exportSum {L : Logic P} {disj} 
  [K : ExportSum L disj] {p q} := K.exportSum p q

instance iExportSumOfByEither {L : Logic P} {disj} 
  [K : ByEither L disj] : ExportSum L disj := 
  {exportSum := fun p q LpDq => K.byEither _ p q LpDq Sum.inl Sum.inr}

instance iByEitherOfExportSum {L : Logic P} {disj} 
  [K : ExportSum L disj] : ByEither L disj := 
  {byEither := fun a p q LpDq fpa fqa => match K.exportSum p q LpDq with
    | Sum.inl Lp => fpa Lp | Sum.inr Lq => fqa Lq}

-- (|- p \/ q) -> PSum p q 

class ExportPSum (L : Logic P) (disj : Binar P) := 
  exportPSum : (p q : P) -> (L |- p \/ q) -> PSum (L |- p) (L |- q)

abbrev exportPSum {L : Logic P} {disj} 
  [K : ExportPSum L disj] {p q} := K.exportPSum p q

instance iExportPSumOfByEither {L : Logic P} {disj} 
  [K : ByEither L disj] : ExportPSum L disj := 
  {exportPSum := fun p q LpDq => K.byEither _ p q LpDq PSum.inl PSum.inr}

instance iByEitherOfExportPSum {L : Logic P} {disj} 
  [K : ExportPSum L disj] : ByEither L disj := 
  {byEither := fun a p q LpDq fpa fqa => match K.exportPSum p q LpDq with
    | PSum.inl Lp => fpa Lp | PSum.inr Lq => fqa Lq}

-- (|- p \/ q) -> Or p q 

class ExportOr (L : Logic.{u,0} P) (disj : Binar P) := 
  exportOr : (p q : P) -> (L |- p \/ q) -> (L |- p) \/ (L |- q)

abbrev exportOr {L : Logic.{u,0} P} {disj} 
  [K : ExportOr L disj] {p q} := K.exportOr p q

instance iExportOrOfByEither {L : Logic P} {disj} 
  [K : ByEither L disj] : ExportOr L disj := 
  {exportOr := fun p q LpDq => K.byEither _ p q LpDq Or.inl Or.inr}

instance iByEitherOfExportOr {L : Logic P} {disj} 
  [K : ExportOr L disj] : ByEither L disj := 
  {byEither := fun (a : Prop) p q LpDq fpa fqa => match K.exportOr p q LpDq with
    | Or.inl Lp => fpa Lp | Or.inr Lq => fqa Lq}

end Gaea.Logic