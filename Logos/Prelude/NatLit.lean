import Logos.Prelude.Newtype
import Logos.Prelude.FunTypes

universe u
variable {T : Sort u}

namespace Logos

/--
  Sort-polymorphic Natural Literals
-/
class OfNatLit (A : Sort u) (n : Nat) :=
  ofNatLit : A

@[defaultInstance low]
instance iNatOfNatLit {n : Nat} : OfNatLit Nat n
  := {ofNatLit := n}

@[defaultInstance low + low]
instance iOfNatLitOfNat {A : Type u} {n : Nat} 
  [K : OfNat A n] : OfNatLit A n
  := {ofNatLit := K.ofNat}

instance iOfMatOfNatLit {A : Type u} {n : Nat} 
  [K : OfNatLit A n] : OfNat A n
  := {ofNat := K.ofNatLit}

-- 0

class abbrev Zero (T : Sort u) 
  := OfNatLit T (nat_lit 0)

instance Zero.isNewtype : Newtype (Zero T) T :=
  {pack := fun x => {ofNatLit := x}, unpack := fun K => K.ofNatLit}

instance Zero.ofNat : Zero Nat := 
  {ofNatLit := Nat.zero}

-- 1

class abbrev One (T : Sort u) 
  := OfNatLit T (nat_lit 1)

instance One.isNewtype : Newtype (Zero T) T :=
  {pack := fun x => {ofNatLit := x}, unpack := fun K => K.ofNatLit}

instance One.ofNat : One Nat := 
  {ofNatLit := Nat.succ Nat.zero}

-- S

class funtype Succ (T : Sort u) := export S : Unar T

instance Succ.ofNat : Succ Nat := pack Nat.succ
instance Succ.ofNatLit {A : Sort u} [K : Succ A] (n : Nat) [T : OfNatLit A n] 
  : OfNatLit A (Nat.succ n) := {ofNatLit := unpack K T.ofNatLit}

namespace Notation

open Lean

-- Numerals

scoped syntax:max (name := sortNumLit) (priority := default + default) 
  num : term

@[macro sortNumLit] 
def expandSortNumLit : Macro
  | `( $n:numLit ) => `(OfNatLit.ofNatLit (nat_lit $n))
  | _ => Macro.throwUnsupported

@[appUnexpander Logos.OfNatLit.ofNatLit] 
def unexpandOfNatLit : PrettyPrinter.Unexpander
  | `($_f:ident $n) => n
  | _  => throw ()

-- Functions

open Lean

@[appUnexpander Logos.Succ.S] 
def unexpandSucc : PrettyPrinter.Unexpander
  | `($_f:ident $n) => `($(mkIdent `S) $n)
  | _  => throw ()
