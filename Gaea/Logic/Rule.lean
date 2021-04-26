import Gaea.FunTypes
import Gaea.Logic.Judgment

open Lean Syntax

namespace Gaea

def mkDepArrows (binders : Array Syntax) (term : Syntax) : MacroM Syntax :=
  binders.foldrM (fun binder tail => 
      `( $binder:bracketedBinder -> $tail:term)) term

def mkRuleDecl
  (id : Syntax) (clsParams : Array Syntax) 
  (typeArgs : Array Syntax) (varBinders : Array Syntax) 
  (funType : Syntax) : MacroM Syntax
:= do
  let name := id[0]
  let ruleType := mkApp name typeArgs
  let funTypeName := mkIdent `funType
  `(
  class $id:declId $clsParams* := 
    ($(mkIdent `toFun) : $funType)
  namespace $name:ident
  variable $varBinders:bracketedBinder* 
  abbrev $funTypeName ($(mkIdent `K) : $ruleType) := $funType
  instance : CoeFun $ruleType $funTypeName := {coe := fun K => K.toFun} 
  end $name:ident
  )

def expandRuleDeclAux 
  (id : Syntax) (clsParams : Array Syntax) (funType : Syntax) : MacroM Syntax
:= do
  -- Parse Class Params
  let mut typeArgs := #[]
  let mut varBinders := #[]
  for binder in clsParams do
    match binder with
    | `(bracketedBinder| ( $ids:ident* $[: $type:term]? ) ) =>
      typeArgs := typeArgs ++ ids
      varBinders := varBinders.push 
        (← `(bracketedBinder| { $ids:ident* $[: $type:term ]? }) )
    | `(bracketedBinder| { $ids:ident* $[: $type:term ]? } ) =>
      varBinders := varBinders.push binder
    | `(bracketedBinder| [ $[$id:ident :]? $type:term ] ) =>
      varBinders := varBinders.push binder
    | _ => 
      Macro.throwErrorAt binder "unknown parameter binder in `rule` declaration"
  -- Construct Declaration
  mkRuleDecl id clsParams typeArgs varBinders funType

scoped syntax (name := ruleDecl)
  "rule " declId bracketedBinder* (":" bracketedBinder+)? "=>" term : command

@[scoped macro ruleDecl]
def expandRuleDecl : Macro
| `(rule $id:declId $params:bracketedBinder* $[: $args:bracketedBinder*]? => $ret:term) =>
  do expandRuleDeclAux id params (<- mkDepArrows (args.getD #[]) ret)
| _ => Macro.throwUnsupported
