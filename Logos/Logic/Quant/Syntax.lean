import Logos.Prelude.Newtype
import Logos.Prelude.FunTypes

universes u v
variable {P : Sort u} {T : Sort v}

namespace Logos

class funtype SForall (P : Sort u) (T : Sort v) : Quant P T
class funtype SExists (P : Sort u) (T : Sort v) : Quant P T

instance iPropForall : SForall Prop T := pack fun f => forall x, f x
instance iPropExists : SExists Prop T := pack Exists

abbrev lForall [K : SForall P T] := K.toFun
abbrev lExists [K : SExists P T] := K.toFun

namespace Notation

open Lean

scoped macro "∀ " xs:explicitBinders " => " b:term : term => 
  expandExplicitBinders ``SForall.toFun xs b
scoped macro "forall " xs:explicitBinders " => " b:term : term => 
  expandExplicitBinders ``SForall.toFun xs b

scoped macro "∃ " xs:explicitBinders " => " b:term : term => 
  expandExplicitBinders ``SExists.toFun xs b
scoped macro "exists " xs:explicitBinders " => " b:term : term => 
  expandExplicitBinders ``SExists.toFun xs b

@[appUnexpander Logos.SForall.toFun] 
def unexpandSForall : Lean.PrettyPrinter.Unexpander
  | `($_f:ident fun $x:ident => ∀ $xs:binderIdent* => $b)
    => `(∀ $x:ident $xs:binderIdent* => $b)
  | `($_f:ident fun $x:ident => $b)
    => `(∀ $x:ident => $b)
  | `($_f:ident fun ($x:ident : $t) => $b)              
    => `(∀ ($x:ident : $t) => $b)
  | _  => throw ()

@[appUnexpander Logos.SExists.toFun] 
def unexpandSExists : Lean.PrettyPrinter.Unexpander
  | `($_f:ident fun $x:ident => ∃ $xs:binderIdent* => $b)
    => `(∃ $x:ident $xs:binderIdent* => $b)
  | `($_f:ident fun $x:ident => $b)          
    => `(∃ $x:ident => $b)
  | `($_f:ident fun ($x:ident : $t) => $b)
    => `(∃ ($x:ident : $t) => $b)
  | _ => throw ()

