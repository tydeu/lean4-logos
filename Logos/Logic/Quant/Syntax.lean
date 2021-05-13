import Logos.Prelude.Newtype
import Logos.Prelude.FunTypes

universes u v
variable {P : Sort u} {T : Sort v}

namespace Logos

class funtype SForall (P : Sort u) (T : Sort v) := export Forall : Quant P T
class funtype SExists (P : Sort u) (T : Sort v) := export Exists : Quant P T

@[defaultInstance low] 
instance iForallOfProp : SForall Prop T := pack fun f => forall x, f x

@[defaultInstance low] 
instance iExistsOfProp : SExists Prop T := pack _root_.Exists

namespace Notation

open Lean

scoped macro "∀ " xs:explicitBinders " => " b:term : term => 
  expandExplicitBinders ``Forall xs b
scoped macro "forall " xs:explicitBinders " => " b:term : term => 
  expandExplicitBinders ``Forall xs b

scoped macro "∃ " xs:explicitBinders " => " b:term : term => 
  expandExplicitBinders ``Exists xs b
scoped macro "exists " xs:explicitBinders " => " b:term : term => 
  expandExplicitBinders ``Exists xs b

@[appUnexpander Logos.SForall.Forall] 
def unexpandSForall : Lean.PrettyPrinter.Unexpander
  | `($_f:ident fun $x:ident => ∀ $xs:binderIdent* => $b)
    => `(∀ $x:ident $xs:binderIdent* => $b)
  | `($_f:ident fun $x:ident => $b)
    => `(∀ $x:ident => $b)
  | `($_f:ident fun ($x:ident : $t) => $b)              
    => `(∀ ($x:ident : $t) => $b)
  | _  => throw ()

@[appUnexpander Logos.SExists.Exists] 
def unexpandSExists : Lean.PrettyPrinter.Unexpander
  | `($_f:ident fun $x:ident => ∃ $xs:binderIdent* => $b)
    => `(∃ $x:ident $xs:binderIdent* => $b)
  | `($_f:ident fun $x:ident => $b)          
    => `(∃ $x:ident => $b)
  | `($_f:ident fun ($x:ident : $t) => $b)
    => `(∃ ($x:ident : $t) => $b)
  | _ => throw ()
