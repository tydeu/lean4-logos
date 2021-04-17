import Gaea.Logic.Unit.Rules

universes u
variable {P : Sort u}

namespace Gaea.Logic

--------------------------------------------------------------------------------
-- Prod/PProd/And
--------------------------------------------------------------------------------

-- Prod p q -> (|- F p q)

class ImportProd (L : Logic P) (F : Binar P) := 
  importProd : (p q : P) -> Prod (L |- p) (L |- q) -> (L |- F p q)

abbrev importProd {L : Logic P} {F} 
  [K : ImportProd L F] {p q} := K.importProd p q

instance iConjoinOfImportProd {L : Logic P} {F} 
  [K : ImportProd L F] : Conjoin L F := 
  {conjoin := fun p q Lp Lq => K.importProd p q (Prod.mk Lp Lq)}

instance iImportProdOfConjoin {L : Logic P} {F} 
  [K : Conjoin L F] : ImportProd L F := 
  {importProd := fun p q Ppq => K.conjoin p q Ppq.fst Ppq.snd}

-- PProd p q -> (|- p /\ q)

class ImportPProd (L : Logic P) (F : Binar P) := 
  importPProd : (p q : P) -> PProd (L |- p) (L |- q) -> (L |- F p q)

abbrev importPProd {L : Logic P} {F} 
  [K : ImportPProd L F] {p q} := K.importPProd p q

instance iConjoinOfImportPProd {L : Logic P} {F} 
  [K : ImportPProd L F] : Conjoin L F := 
  {conjoin := fun p q Lp Lq => K.importPProd p q (PProd.mk Lp Lq)}

instance iImportPProdOfConjoin {L : Logic P} {F} 
  [K : Conjoin L F] : ImportPProd L F := 
  {importPProd := fun p q Ppq => K.conjoin p q Ppq.fst Ppq.snd}

instance iImportProdOfImportPProd {L : Logic P} {F} 
  [K : ImportPProd L F] : ImportProd L F := 
  {importProd := fun p q Ppq => K.importPProd p q (PProd.mk (Ppq.fst) (Ppq.snd))}

-- And p q -> (|- p /\ q)

class ImportAnd (L : Logic.{u,0} P) (F : Binar P) := 
  importAnd : (p q : P) -> ((L |- p) /\ (L |- q)) -> (L |- F p q)

abbrev importAnd {L : Logic.{u,0} P} {F} 
  [K : ImportAnd L F] {p q} := K.importAnd p q

instance iConjoinOfAnd {L : Logic P} {F} 
  [K : ImportAnd L F] : Conjoin L F := 
  {conjoin := fun p q Lp Lq => K.importAnd p q (And.intro Lp Lq)}

instance iImportAndOfConjoin {L : Logic P} {F} 
  [K : Conjoin L F] : ImportAnd L F := 
  {importAnd := fun p q Apq => K.conjoin p q Apq.left Apq.right}

-- (|- p /\ q) -> Prod p q

class ExportProd (L : Logic P) (F : Binar P) := 
  exportProd : (p q : P) -> (L |- F p q) -> Prod (L |- p) (L |- q)

abbrev exportProd {L : Logic P} {F} 
  [K : ExportProd L F] {p q} := K.exportProd p q

instance iExportProdOfLeftRight {L : Logic P} {F}
  [CjL : LeftSimp L F] [CjR : RightSimp L F] : ExportProd L F := 
  {exportProd := fun p q LpCq => Prod.mk (leftSimp LpCq) (rightSimp LpCq)}

instance iLeftSimpOfExportProd {L : Logic P} {F}
  [K : ExportProd L F] : LeftSimp L F := 
  {leftSimp := fun p q LpCq => Prod.fst (K.exportProd p q LpCq)}

instance iRightSimpOfExportProd {L : Logic P} {F}
  [K : ExportProd L F] : RightSimp L F := 
  {rightSimp := fun p q LpCq => Prod.snd (K.exportProd p q LpCq)}

-- (|- p /\ q) -> PProd p q

class ExportPProd (L : Logic P) (F : Binar P) := 
  exportPProd : (p q : P) -> (L |- F p q) -> PProd (L |- p) (L |- q)

abbrev exportPProd {L : Logic P} {F} 
  [K : ExportPProd L F] {p q} := K.exportPProd p q

instance iExportPProdOfLeftRight {L : Logic P} {F}
  [CjL : LeftSimp L F] [CjR : RightSimp L F] : ExportPProd L F := 
  {exportPProd := fun p q LpCq => PProd.mk (leftSimp LpCq) (rightSimp LpCq)}

instance iLeftSimpOfExportPProd {L : Logic P} {F}
  [K : ExportPProd L F] : LeftSimp L F := 
  {leftSimp := fun p q LpCq => PProd.fst (K.exportPProd p q LpCq)}

instance iRightSimpOfExportPProd {L : Logic P} {F}
  [K : ExportPProd L F] : RightSimp L F := 
  {rightSimp := fun p q LpCq => PProd.snd (K.exportPProd p q LpCq)}

instance iExportProdOfPProd {L : Logic P} {F}
  [K : ExportPProd L F] : ExportProd L F := 
  {exportProd := fun p q LpCq => Prod.mk (leftSimp LpCq) (rightSimp LpCq)}

-- (|- p /\ q) -> And p q

class ExportAnd (L : Logic.{u,0} P) (F : Binar P) := 
  exportAnd : (p q : P) -> (L |- F p q) -> And (L |- p) (L |- q)

abbrev exportAnd {L : Logic.{u,0} P} {F} 
  [K : ExportAnd L F] {p q} := K.exportAnd p q

instance iExportAndOfLeftRight {L : Logic P} {F}
  [CjL : LeftSimp L F] [CjR : RightSimp L F] : ExportAnd L F := 
  {exportAnd := fun p q LpCq => And.intro (leftSimp LpCq) (rightSimp LpCq)}

instance iLeftSimpOfExportAnd {L : Logic P} {F}
  [K : ExportAnd L F] : LeftSimp L F := 
  {leftSimp := fun p q LpCq => And.left (K.exportAnd p q LpCq)}

instance iRightSimpOfExportAnd {L : Logic P} {F}
  [K : ExportAnd L F] : RightSimp L F := 
  {rightSimp := fun p q LpCq => And.right (K.exportAnd p q LpCq)}

--------------------------------------------------------------------------------
-- Sum/PSum/Or
--------------------------------------------------------------------------------

-- Sum p q -> (|- p \/ q)

class ImportSum (L : Logic P) (F : Binar P) := 
  importSum : (p q : P) -> Sum (L |- p) (L |- q) -> (L |- F p q)

abbrev importSum {L : Logic P} {F} 
  [K : ImportSum L F] {p q} := K.importSum p q

instance iImportSumOfLeftRightTaut {L : Logic P} {F} 
  [DiL : LeftTaut L F] [DiR : RightTaut L F] : ImportSum L F := 
  {importSum := fun p q Spq => match Spq with 
    | Sum.inl Lp => leftTaut Lp | Sum.inr Lq => rightTaut Lq}

instance iLeftTautOfImportSum {L : Logic P} {F} 
  [K : ImportSum L F] : LeftTaut L F := 
  {leftTaut := fun p q Lp => K.importSum p q (Sum.inl Lp)}

instance iRightTautOfImportSum {L : Logic P} {F} 
  [K : ImportSum L F] : RightTaut L F := 
  {rightTaut := fun p q Lq => K.importSum p q (Sum.inr Lq)}

-- PSum p q -> (|- p \/ q) 

class ImportPSum (L : Logic P) (F : Binar P) := 
  importPSum : (p q : P) -> PSum (L |- p) (L |- q) -> (L |- F p q)

abbrev importPSum {L : Logic P} {F} 
  [K : ImportPSum L F] {p q} := K.importPSum p q

instance iImportPSumOfLeftRightTaut {L : Logic P} {F} 
  [DiL : LeftTaut L F] [DiR : RightTaut L F] : ImportPSum L F := 
  {importPSum := fun p q Spq => match Spq with 
    | PSum.inl Lp => leftTaut Lp | PSum.inr Lq => rightTaut Lq}

instance iLeftTautOfImportPSum {L : Logic P} {F} 
  [K : ImportPSum L F] : LeftTaut L F := 
  {leftTaut := fun p q Lp => K.importPSum p q (PSum.inl Lp)}

instance iRightTautOfImportPSum {L : Logic P} {F} 
  [K : ImportPSum L F] : RightTaut L F := 
  {rightTaut := fun p q Lq => K.importPSum p q (PSum.inr Lq)}

-- Or p q -> (|- p \/ q) 

class ImportOr (L : Logic.{u,0} P) (F : Binar P) := 
  importOr : (p q : P) -> ((L |- p) \/ (L |- q)) -> (L |- F p q)

abbrev importOr {L : Logic.{u,0} P} {F} 
  [K : ImportOr L F] {p q} := K.importOr p q

instance iImportOrOfLeftRightTaut {L : Logic P} {F} 
  [DiL : LeftTaut L F] [DiR : RightTaut L F] : ImportOr L F := 
  {importOr := fun p q Spq => match Spq with 
    | Or.inl Lp => leftTaut Lp | Or.inr Lq => rightTaut Lq}

instance iLeftTautOfImportOr {L : Logic P} {F} 
  [K : ImportOr L F] : LeftTaut L F := 
  {leftTaut := fun p q Lp => K.importOr p q (Or.inl Lp)}

instance iRightTautOfImportOr {L : Logic P} {F} 
  [K : ImportOr L F] : RightTaut L F := 
  {rightTaut := fun p q Lq => K.importOr p q (Or.inr Lq)}

-- (|- p \/ q) -> Sum p q 

class ExportSum (L : Logic P) (F : Binar P) := 
  exportSum : (p q : P) -> (L |- F p q) -> Sum (L |- p) (L |- q)

abbrev exportSum {L : Logic P} {F} 
  [K : ExportSum L F] {p q} := K.exportSum p q

instance iExportSumOfByEither {L : Logic P} {F} 
  [K : ByEither L F] : ExportSum L F := 
  {exportSum := fun p q LpDq => K.byEither _ p q LpDq Sum.inl Sum.inr}

instance iByEitherOfExportSum {L : Logic P} {F} 
  [K : ExportSum L F] : ByEither L F := 
  {byEither := fun a p q LpDq fpa fqa => match K.exportSum p q LpDq with
    | Sum.inl Lp => fpa Lp | Sum.inr Lq => fqa Lq}

-- (|- p \/ q) -> PSum p q 

class ExportPSum (L : Logic P) (F : Binar P) := 
  exportPSum : (p q : P) -> (L |- F p q) -> PSum (L |- p) (L |- q)

abbrev exportPSum {L : Logic P} {F} 
  [K : ExportPSum L F] {p q} := K.exportPSum p q

instance iExportPSumOfByEither {L : Logic P} {F} 
  [K : ByEither L F] : ExportPSum L F := 
  {exportPSum := fun p q LpDq => K.byEither _ p q LpDq PSum.inl PSum.inr}

instance iByEitherOfExportPSum {L : Logic P} {F} 
  [K : ExportPSum L F] : ByEither L F := 
  {byEither := fun a p q LpDq fpa fqa => match K.exportPSum p q LpDq with
    | PSum.inl Lp => fpa Lp | PSum.inr Lq => fqa Lq}

-- (|- p \/ q) -> Or p q 

class ExportOr (L : Logic.{u,0} P) (F : Binar P) := 
  exportOr : (p q : P) -> (L |- F p q) -> Or (L |- p) (L |- q)

abbrev exportOr {L : Logic.{u,0} P} {F} 
  [K : ExportOr L F] {p q} := K.exportOr p q

instance iExportOrOfByEither {L : Logic P} {F} 
  [K : ByEither L F] : ExportOr L F := 
  {exportOr := fun p q LpDq => K.byEither _ p q LpDq Or.inl Or.inr}

instance iByEitherOfExportOr {L : Logic P} {F} 
  [K : ExportOr L F] : ByEither L F := 
  {byEither := fun (a : Sort 0) p q LpDq fpa fqa => match K.exportOr p q LpDq with
    | Or.inl Lp => fpa Lp | Or.inr Lq => fqa Lq}

end Gaea.Logic
