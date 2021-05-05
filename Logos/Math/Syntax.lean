import Logos.Prelude.NatLit

universes u v
variable {P : Sort u} {T : Sort v}

namespace Logos

--------------------------------------------------------------------------------
-- Operations
--------------------------------------------------------------------------------

-- +

class funtype SAdd (T : Sort v) : Binar T

instance iSAddOfAdd {T : Type v} [K : Add T]  : SAdd T := pack K.add 
instance iAddOfSAdd {T : Type v} [K : SAdd T] : Add T  := {add := unpack K}

-- -

class funtype SSub (T : Sort v) : Binar T

instance iSSubOfSub {T : Type v} [K : Sub T]  : SSub T := pack K.sub 
instance iSubOfSSub {T : Type v} [K : SSub T] : Sub T  := {sub := unpack K}


-- *

class funtype SMul (T : Sort v) : Binar T

instance iSMulOfMul {T : Type v} [K : Mul T] : SMul T := pack K.mul 
instance iMulOfSMul {T : Type v} [K : SMul T] : Mul T := {mul := unpack K} 

-- *

class funtype SDiv (T : Sort v) : Binar T

instance iSDivOfDiv {T : Type v} [K : Div T] : SDiv T := pack K.div 
instance iDivOfSDiv {T : Type v} [K : SDiv T] : Div T := {div := unpack K} 

--------------------------------------------------------------------------------
-- Inequalities
--------------------------------------------------------------------------------

-- <

class funtype SLt (P : Sort u) (T : Sort v) : Rel P T

instance iSLtOfLT {T : Type v} [K : LT T] : SLt Prop T := pack K.lt 
instance iLTOfSLt {T : Type v} [K : SLt Prop T] : LT T := {lt := unpack K} 

--- <=

class funtype SLe (P : Sort u) (T : Sort v) : Rel P T

instance iSLeOfLE {T : Type v} [K : LE T] : SLe Prop T := pack K.le 
instance iLEOfSLt {T : Type v} [K : SLe Prop T] : LE T := {le := unpack K}

-- >

class funtype SGt (P : Sort u) (T : Sort v) : Rel P T

@[defaultInstance low]
instance iSGtOfSLt [K : SLt P T] : SGt P T := repack K 
instance iSLtOfSGt [K : SGt P T] : SLt P T := repack K

-- >=

class funtype SGe (P : Sort u) (T : Sort v) : Rel P T

@[defaultInstance low]
instance iSGeOfSLe [K : SLe P T] : SGe P T := repack K
instance iSLeOfSGe [K : SGe P T] : SLe P T := repack K 

--------------------------------------------------------------------------------
-- Notation
--------------------------------------------------------------------------------

namespace Notation

-- Operators

scoped infix:65 (name := syntaxAdd) (priority := default + default) " + " => SAdd.toFun
scoped infix:65 (name := syntaxSub) (priority := default + default) " - " => SSub.toFun
scoped infix:70 (name := syntaxMul) (priority := default + default) " * " => SMul.toFun
scoped infix:70 (name := syntaxDiv) (priority := default + default) " / " => SDiv.toFun

-- Inequalities

scoped infix:50 (name := syntaxLt)  (priority := default + default) " < "  => SLt.toFun
scoped infix:50 (name := syntaxLe)  (priority := default + default) " <= " => SLe.toFun
scoped infix:50 (name := syntaxLe') (priority := default + default) " ≤ "  => SLe.toFun
scoped infix:50 (name := syntaxGt)  (priority := default + default) " > "  => SGt.toFun
scoped infix:50 (name := syntaxGe)  (priority := default + default) " >= " => SGe.toFun
scoped infix:50 (name := syntaxGe') (priority := default + default) " ≥ "  => SGe.toFun

macro_rules (kind := syntaxLt)  | `($x < $y)  => `(binrel% SLt.toFun $x $y)
macro_rules (kind := syntaxLe)  | `($x <= $y) => `(binrel% SLe.toFun $x $y)
macro_rules (kind := syntaxLe') | `($x ≤ $y)  => `(binrel% SGt.toFun $x $y)
macro_rules (kind := syntaxGt)  | `($x > $y)  => `(binrel% SGe.toFun $x $y)
macro_rules (kind := syntaxGe)  | `($x >= $y) => `(binrel% SGe.toFun $x $y)
macro_rules (kind := syntaxGe') | `($x ≥ $y)  => `(binrel% SGe.toFun $x $y)

-- Functions

open Lean

@[scoped appUnexpander Logos.S] 
def unexpandS : PrettyPrinter.Unexpander
  | `($_f:ident $n) => `($(mkIdent `S) $n)
  | _  => throw ()

@[scoped appUnexpander Logos.Succ.toFun] 
def unexpandSucc : PrettyPrinter.Unexpander
  | `($_f:ident $n) => `($(mkIdent `S) $n)
  | _  => throw ()
