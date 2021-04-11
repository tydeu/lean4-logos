import Gaea.Logic.Fun.Types
import Gaea.Logic.Judgment
import Gaea.Logic.Prop.Syntax
import Gaea.Logic.Prop.Notation

universes u v w
variable {P : Sort u} {T : Sort v}

namespace Gaea.Logic

--------------------------------------------------------------------------------
-- Postulate
--------------------------------------------------------------------------------

class Postulate (L : Logic P) (p : P) := 
  postulate : L |- p 

abbrev postulate {L : Logic P} {p}
  [K : Postulate L p] := K.postulate

--------------------------------------------------------------------------------
-- Implication (if)
--------------------------------------------------------------------------------

-- Conditional Proof
-- (p |- q) -> (|- p -> q) 

class ByImplication (L : Logic P) (imp : Binar P) := 
  byImplication : (p q : P) -> ((L |- p) -> (L |- q)) -> (L |- p -> q) 

abbrev byImplication {L : Logic P} {imp} 
  [K : ByImplication L imp] {p q} := K.byImplication p q

--------------------------------------------------------------------------------
-- Contraposition
--------------------------------------------------------------------------------

-- Proof by Contraposition
-- (~q |- ~p) -> (|- p -> q)

class ByContraposition (L : Logic P) (imp : Binar P) (lnot : Unar P) :=
  byContraposition : (p q : P) -> ((L |- ~q) -> (L |- ~p)) -> (L |- p -> q) 

abbrev byContraposition {L : Logic P} {imp lnot}
  [K : ByContraposition L imp lnot] {p q} := K.byContraposition p q

--------------------------------------------------------------------------------
-- Biconditional (iff)
--------------------------------------------------------------------------------

-- Biconditional Introduction
-- (p |- q) -> (q |- p) -> (|- p <-> q)

class Bicondition (L : Logic P) (iff : Binar P) := 
  bicondition : (p q : P) -> 
    ((L |- p) -> (L |- q)) -> ((L |- q) -> (L |- p)) -> (L |- p <-> q)

abbrev bicondition {L : Logic P} {iff}
  [K : Bicondition L iff] {p q} := K.bicondition p q

--------------------------------------------------------------------------------
-- Modus Ponens
--------------------------------------------------------------------------------

-- p <-> q, p |- q

class ModusPonens (L : Logic P) (iff : Binar P) := 
  mp : (p q : P) -> (L |- p <-> q) -> (L |- p) -> (L |- q)

abbrev mp {L : Logic P} {iff} 
  [K : ModusPonens L iff] {p q} := K.mp p q

abbrev mpl {L : Logic P} {iff} 
  [K : ModusPonens L iff] {p q} := K.mp p q

-- p <-> q, q |- p

class ModusPonensRev (L : Logic P) (iff : Binar P) := 
  mp : (p q : P) -> (L |- p <-> q) -> (L |- q) -> (L |- p)

abbrev mpr {L : Logic P} {iff} 
  [K : ModusPonensRev L iff] {p q} := K.mp p q

--------------------------------------------------------------------------------
-- Modus Tollens
--------------------------------------------------------------------------------

-- p <-> q, ~q |- ~p 

class ModusTollens (L : Logic P) (iff : Binar P) (lnot : Unar P) :=
  mt : (p q : P) -> (L |- p <-> q) -> (L |- ~q) -> (L |- ~p)

abbrev mt {L : Logic P} {iff lnot} 
  [K : ModusTollens L iff lnot] {p q} := K.mt p q

abbrev mtr {L : Logic P} {iff lnot} 
  [K : ModusTollens L iff lnot] {p q} := K.mt p q

-- p <-> q, ~p |- q 

class ModusTollensRev (L : Logic P) (iff : Binar P) (lnot : Unar P) :=
  mt : (p q : P) -> (L |- p <-> q) -> (L |- ~p) -> (L |- ~q) 

abbrev mtl {L : Logic P} {iff lnot} 
  [K : ModusTollensRev L iff lnot] {p q} := K.mt p q

--------------------------------------------------------------------------------
-- Conjunction
--------------------------------------------------------------------------------

-- p, q |- p /\ q

class Conjunction (L : Logic P) (C : Binar P) := 
  conjoin : (p q : P) -> (L |- p) -> (L |- q) -> (L |- C p q) 

abbrev conjoin {L : Logic P} {C} 
  [K : Conjunction L C] {p q} := K.conjoin p q

--------------------------------------------------------------------------------
-- Simplification
--------------------------------------------------------------------------------

-- C p p |- p

class Simplification (L : Logic P) (C : Binar P)  :=
  simp : (p : P) -> (L |- C p p) -> (L |- p)

abbrev simp {L : Logic P} {C} 
  [K : Simplification L C] {p} := K.simp p

-- C p q |- p

class LeftSimp (L : Logic P) (C : Binar P) := 
  leftSimp : (p q : P) -> (L |- C p q) -> (L |- p)

abbrev leftSimp {L : Logic P} {conj} 
  [K : LeftSimp L conj] {p q} := K.leftSimp p q

instance iSimpOfLeft {L : Logic P} {conj}
  [K : LeftSimp L conj] : Simplification L conj := 
  {simp := fun p LpCq => K.leftSimp p p LpCq}

-- C p q |- q

class RightSimp (L : Logic P) (C : Binar P) := 
  rightSimp : (p q : P) -> (L |- C p q) -> (L |- q)

abbrev rightSimp {L : Logic P} {conj} 
  [K : RightSimp L conj] {p q} := K.rightSimp p q

instance iSimpOfRight {L : Logic P} {conj}
  [K : RightSimp L conj] : Simplification L conj := 
  {simp := fun p LpCq => K.rightSimp p p LpCq}

--------------------------------------------------------------------------------
-- Currying
--------------------------------------------------------------------------------

-- (p /\ q -> a) -> (p -> q -> a)

class Curry (L : Logic P) (C : Binar P) :=
  curry : (r : Sort w) -> (p q : P) -> 
    ((L |- C p q) -> r) -> ((L |- p) -> (L |- q) -> r)

abbrev curry {L : Logic P} {C} 
  [K : Curry L C] {r p q} := K.curry r p q

instance iCurryOfConjunction {L : Logic P} {C}
  [K : Conjunction L C] : Curry L C := 
  {curry := fun a p q fpCq Lp Lq  => fpCq (conjoin Lp Lq)}

instance iConjunctionOfCurry {L : Logic P} {C}
  [K : Curry L C] : Conjunction L C := 
  {conjoin := fun p q => K.curry _ p q id}

-- (p -> q -> a) -> (p /\ q -> a)

class Uncurry (L : Logic P) (conj : Binar P) :=
  uncurry : (r : Sort w) -> (p q : P) -> 
    ((L |- p) -> (L |- q) -> r) -> ((L |- p /\ q) -> r)

abbrev uncurry {L : Logic P} {conj} 
  [K : Uncurry L conj] {r p q} := K.uncurry r p q

instance iUncurryOfLeftRightSimp {L : Logic P} {conj}
  [CjL : LeftSimp L conj] [CjR : RightSimp L conj] : Uncurry L conj := 
  {uncurry := fun a p q fpq LpCq => fpq (leftSimp LpCq) (rightSimp LpCq)}

instance iLeftSimpOfUncurry {L : Logic P} {conj}
  [K : Uncurry L conj] : LeftSimp L conj := 
  {leftSimp := fun p q => K.uncurry _ p q (fun Lp Lq => Lp)}

instance iRightSimpOfUncurry {L : Logic P} {conj}
  [K : Uncurry L conj] : RightSimp L conj := 
  {rightSimp := fun p q => K.uncurry _ p q (fun Lp Lq => Lq)}

--------------------------------------------------------------------------------
-- Prod/PProd/And Import/Export
--------------------------------------------------------------------------------

-- Prod p q -> p /\ q 

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

-- PProd p q -> p /\ q 

class ConjOfPProd (L : Logic P) (conj : Binar P) := 
  importPProd : (p q : P) -> PProd (L |- p) (L |- q) -> (L |- p /\ q)

abbrev importPProd {L : Logic P} {conj} 
  [K : ConjOfPProd L conj] {p q} := K.importPProd p q

instance iConjunctionOfImportPProd {L : Logic P} {conj} 
  [K : ConjOfPProd L conj] : Conjunction L conj := 
  {conjoin := fun p q Lp Lq => K.importPProd p q (PProd.mk Lp Lq)}

instance iImportPProdOfConjunction {L : Logic P} {conj} 
  [K : Conjunction L conj] : ConjOfPProd L conj := 
  {importPProd := fun p q Ppq => K.conjoin p q Ppq.fst Ppq.snd}

instance iImportProdOfImportPProd {L : Logic P} {conj} 
  [K : ConjOfPProd L conj] : ImportProd L conj := 
  {importProd := fun p q Ppq => K.importPProd p q (PProd.mk (Ppq.fst) (Ppq.snd))}

-- And p q -> p /\ q 

class ImportAnd (L : Logic.{u,0} P) (conj : Binar P) := 
  importAnd : (p q : P) -> (L |- p) /\ (L |- q) -> (L |- p /\ q)

abbrev importAnd {L : Logic.{u,0} P} {conj} 
  [K : ImportAnd L conj] {p q} := K.importAnd p q

instance iConjunctionOfAnd {L : Logic P} {conj} 
  [K : ImportAnd L conj] : Conjunction L conj := 
  {conjoin := fun p q Lp Lq => K.importAnd p q (And.intro Lp Lq)}

instance iImportAndOfConjunction {L : Logic P} {conj} 
  [K : Conjunction L conj] : ImportAnd L conj := 
  {importAnd := fun p q Apq => K.conjoin p q Apq.left Apq.right}

-- p /\ q -> Prod p q

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

-- p /\ q -> PProd p q

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

-- p /\ q -> And p q

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
-- Disjunction
--------------------------------------------------------------------------------

-- Proof by Cases
-- (|- p \/ q) -> ((|- p) -> r) -> ((|- q) -> r) -> r

class ByEither (L : Logic P) (disj : Binar P) := 
  byEither : (r : Sort w) -> (p q : P) -> 
    (L |- p \/ q) -> ((L |- p) -> r) -> ((L |- q) -> r) -> r

abbrev byEither {L : Logic P} {disj}
  [K : ByEither L disj] {r p q} := K.byEither r p q

--------------------------------------------------------------------------------
-- Tautology
--------------------------------------------------------------------------------

-- p |- D p p

class Tautology (L : Logic P) (D : Binar P)  :=
  taut : (p : P) -> (L |- p) -> (L |- D p p)

abbrev taut {L : Logic P} {D} 
  [K : Tautology L D] {p} := K.taut p

-- p |- D p q

class LeftTaut (L : Logic P) (D : Binar P)  := 
  leftTaut : (p q : P) -> (L |- p) -> (L |- D p q) 

abbrev leftTaut {L : Logic P} {D} 
  [K : LeftTaut L D] {p q} := K.leftTaut p q

instance iTautOfLeft {L : Logic P} {D}
  [K : LeftTaut L D] : Tautology L D := 
  {taut := fun p Lp => K.leftTaut p p Lp}

-- q |- D p q

class RightTaut (L : Logic P) (D : Binar P)  := 
  rightTaut : (p q : P) -> (L |- q) -> (L |- D p q) 

abbrev rightTaut {L : Logic P} {D} 
  [K : RightTaut L D] {p q} := K.rightTaut p q

instance iTautOfRight {L : Logic P} {D}
  [K : RightTaut L D] : Tautology L D := 
  {taut := fun p Lp => K.rightTaut p p Lp}

--------------------------------------------------------------------------------
-- Modus Tollendo Ponens / Disjunctive Syllogism / Disjuntive Elimination
--------------------------------------------------------------------------------

-- p \/ q, ~p |- q

class LeftNeg (L : Logic P) (D : Binar P) (lnot : Unar P) := 
  leftNeg : (p q : P) -> (L |- D p q) -> (L |- ~p) -> (L |- q)

abbrev leftNeg {L : Logic P} {D} {lnot : Unar P} 
  [K : LeftNeg L D lnot] {p q} := K.leftNeg p q

-- p \/ q, ~q |- p

class RightNeg (L : Logic P) (D : Binar P) (lnot : Unar P) := 
  rightNeg : (p q : P) -> (L |- D p q) -> (L |- ~q) -> (L |- p)

abbrev rightNeg {L : Logic P} {D} {lnot : Unar P} 
  [K : RightNeg L D lnot] {p q} := K.rightNeg p q

--------------------------------------------------------------------------------
-- Sum/PSum/Or Import/Export
--------------------------------------------------------------------------------

-- Sum p q -> p \/ q 

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

-- PSum p q -> p \/ q  

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

-- Or p q -> p \/ q 

class ImportOr (L : Logic.{u,0} P) (disj : Binar P) := 
  importOr : (p q : P) -> (L |- p) \/ (L |- q) -> (L |- p \/ q)

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

-- p \/ q -> Sum p q 

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

-- p \/ q -> PSum p q 

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

-- p \/ q -> Or p q 

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

--------------------------------------------------------------------------------
-- Not
--------------------------------------------------------------------------------

-- ((|- p) -> False) -> (|- ~p)

class AdFalso (L : Logic P) (lnot : Unar P) := 
  adFalso : (p : P) -> ((L |- p) -> False) -> (L |- ~p) 

abbrev adFalso {L : Logic.{u,0} P} {lnot}
  [K : AdFalso L lnot] {p} := K.adFalso p

-- not |- p, ~p

class Noncontradiction (L : Logic P) (lnot : Unar P) := 
  noncontradiction : (p : P) -> (L |- ~p) -> (L |- p) -> False

abbrev noncontradiction {L : Logic P} {lnot} 
  [K : Noncontradiction L lnot] {p} := K.noncontradiction p

-- Not p -> (|- ~p)

class ImportNot (L : Logic.{u,0} P) (lnot : Unar P) := 
  importNot : (p : P) -> Not (L |- p) -> (L |- lnot p) 

abbrev importNot {L : Logic P} {lnot}
  [K : ImportNot L lnot] {p} := K.importNot p

-- (|- ~p) -> Not p

class ExportNot (L : Logic.{u,0} P) (lnot : Unar P) := 
  exportNot : (p : P) -> (L |- lnot p) -> Not (L |- p) 

abbrev exportNot {L : Logic.{u,0} P} {lnot}
  [K : ExportNot L lnot] {p} := K.exportNot p

--------------------------------------------------------------------------------
-- Double Negation
--------------------------------------------------------------------------------

-- p |- ~~p

class DblNegIntro (L : Logic P) (lnot : Unar P) :=
  dblNegIntro : (p : P) -> (L |- p) -> (L |- ~~p)

abbrev dblNegIntro {L : Logic P} {lnot}
  [K : DblNegIntro L lnot] {p} := K.dblNegIntro p

-- ~~p |- p

class DblNegElim (L : Logic P) (lnot : Unar P) :=
  dblNegElim : (p : P) -> (L |- ~~p) -> (L |- p)

abbrev dblNegElim {L : Logic P} {lnot}
  [K : DblNegElim L lnot] {p} := K.dblNegElim p

--------------------------------------------------------------------------------
-- Contradiction
--------------------------------------------------------------------------------

def Contradiction (L : Logic P) (lnot : Unar P) :=
  PSigma fun (p : P) => PProd (L |- lnot p) (L |- p) 

def contradiction {L : Logic P} {lnot}
  {p} (LNp : L |- lnot p) (Lp : L |- p) : Contradiction L lnot := 
    PSigma.mk p (PProd.mk LNp Lp)

class ByContradiction (L : Logic P) (lnot : Unar P) :=
  byContradiction : (p : P) ->
     ((L |- p) -> Contradiction L lnot) -> (L |- lnot p)

abbrev byContradiction {L : Logic P} {lnot}
  [K : ByContradiction L lnot] {p} := K.byContradiction p

--------------------------------------------------------------------------------
-- Falsum
--------------------------------------------------------------------------------

-- (p |- falsum) -> (|- ~p)

class AdFalsum (L : Logic P) (falsum : P) (lnot : Unar P) :=
  adFalsum : (p : P) -> ((L |- p) -> (L |- falsum)) -> (L |- ~p)

abbrev adFalsum {L : Logic P} {falsum : P} {lnot : Unar P}
  [K : AdFalsum L falsum lnot] {p} := K.adFalsum p

-- (|- falsum) -> (|- p)

class ExFalsum (L : Logic P) (falsum : P) :=
  exFalsum : (p : P) -> (L |- falsum) -> (L |- p)

abbrev exFalsum {L : Logic P} {falsum}
  [K : ExFalsum L falsum] {p} := K.exFalsum p

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

end Gaea.Logic