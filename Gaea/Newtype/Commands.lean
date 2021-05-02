import Gaea.Newtype.Basic

open Lean Syntax

namespace Gaea

--------------------------------------------------------------------------------
-- Newtype
--------------------------------------------------------------------------------

def paramsToVars (params : Array Syntax)
: MacroM (Prod (Array Syntax) (Array Syntax)) := do
  let mut args := #[]
  let mut varBinders := #[]
  for binder in params do
    match binder with
    | `(bracketedBinder| ( $ids:ident* $[: $type:term]? ) ) =>
      args := args ++ ids
      varBinders := varBinders.push 
        (← `(bracketedBinder| { $ids:ident* $[: $type:term ]? }) )
    | `(bracketedBinder| { $ids:ident* $[: $type:term ]? } ) =>
      varBinders := varBinders.push binder
    | `(bracketedBinder| [ $[$id:ident :]? $type:term ] ) =>
      varBinders := varBinders.push binder
    | _ => 
      Macro.throwErrorAt binder "unknown binder"
  return (args, varBinders)

def mkNewtypeStructDecl 
  (isClass : Bool) (declId : Syntax) 
  (params : Array Syntax) (fieldId : Syntax) (type : Syntax) 
: MacroM Syntax :=
  if isClass then 
    `(class $declId:declId $params* := $fieldId:ident : $type:term)
  else
    `(structure $declId:declId $params* := $fieldId:ident : $type:term)

def mkNewtypeDecl 
  (isClass : Bool) (declId : Syntax) 
  (params : Array Syntax) (fieldId? : Option Syntax) (type : Syntax) 
: MacroM Syntax := do
  let name := declId[0]
  let fieldId := fieldId?.getD (mkIdent `val) 
  let decl <- mkNewtypeStructDecl isClass declId params fieldId type
  let (args, vars) <- paramsToVars params
  let ntype := mkApp name args
  let nvar := mkIdent `K
  let valId := mkIdent (`K ++ fieldId.getId)
  `(
  $decl:command
  namespace $name:ident
  variable $vars:bracketedBinder* 
  instance $(mkIdent `isNewtype):ident : Newtype $ntype $type := 
    {pack := $(mkIdent `mk), unpack := fun $nvar => $valId:ident} 
  end $name:ident
  )

scoped syntax (name := newtypeDecl)
  "class "? "newtype " declId bracketedBinder* 
    (":=" ident)? ":" term : command

@[macro newtypeDecl]
def expandNewtypeDecl : Macro
| `(newtype $id:declId $ps:bracketedBinder* $[:= $f:ident]? : $t:term) =>
  mkNewtypeDecl false id ps f t
| `(class newtype $id:declId $ps:bracketedBinder* $[:= $f:ident]? : $t:term) =>
  mkNewtypeDecl true id ps f t
| _ => Macro.throwUnsupported

--------------------------------------------------------------------------------
-- Funtype
--------------------------------------------------------------------------------

def mkDepArrows (binders : Array Syntax) (term : Syntax) : MacroM Syntax :=
  binders.foldrM (fun binder tail => 
      `( $binder:bracketedBinder -> $tail:term)) term

def paramsToApp (params : Array Syntax)
: MacroM (Prod (Array Syntax) (Array Syntax)) := do
  let mut args := #[]
  let mut explicitParams := #[]
  for binder in params do
    match binder with
    | `(bracketedBinder| ( $ids:ident* $[: $type:term]? ) ) =>
      args := args ++ ids
      explicitParams := explicitParams.push binder
    | `(bracketedBinder| { $ids:ident* $[: $type:term ]? } ) =>
      args := args ++ ids
      explicitParams := explicitParams.push
        (← `(bracketedBinder| ( $ids:ident* $[: $type:term ]? ) ))
    | `(bracketedBinder| [ $id:ident : $type:term ] ) =>
      args := args.push id
      explicitParams := explicitParams.push
        (← `(bracketedBinder| ( $id:ident : $type:term ) ))
    | `(bracketedBinder| [ $type:term ] ) =>
      Macro.throwErrorAt binder 
        "`class fun` does not support unnamed instance binders in function params"
    | _ => 
      Macro.throwErrorAt binder "unknown binder"
  return (args, explicitParams)

def mkFuntypeDecl 
  (isClass : Bool) (declId : Syntax) 
  (typeParams : Array Syntax) (fieldId? : Option Syntax) 
  (applyParams : Array Syntax) (fnRet : Syntax) 
: MacroM Syntax := do
  let name := declId[0]
  let applyType <- mkDepArrows applyParams fnRet
  let (applyArgs, fnParams) <- paramsToApp applyParams
  let fnType <- mkDepArrows fnParams fnRet
  let fieldId := fieldId?.getD (mkIdent `val)
  let decl <- mkNewtypeStructDecl isClass declId typeParams fieldId fnType
  let (typeArgs, vars) <- paramsToVars typeParams
  let ntype := mkApp name typeArgs
  let nvar := mkIdent `K
  let valId := mkIdent (`K ++ fieldId.getId)
  let funId := mkIdent `toFun
  let applyId := mkIdent `apply
  let applyFunId := mkIdent `toApplyFun
  `(
  $decl:command
  namespace $name:ident
  variable $vars:bracketedBinder* 
  abbrev $funId ($nvar : $ntype) := $valId
  abbrev $applyId [$nvar : $ntype] $applyParams* := $valId $applyArgs*
  abbrev $applyFunId ($nvar : $ntype) $applyParams* := $valId $applyArgs*
  instance $(mkIdent `isFuntype):ident : Funtype $ntype $fnType $applyType := 
    {pack := $(mkIdent `mk), unpack := $funId, apply := $applyFunId} 
  end $name:ident
  )

scoped syntax (name := funtypeDecl)
  "class "? "funtype " declId bracketedBinder* 
    (":=" ident ? bracketedBinder*)? ":" term : command

@[macro funtypeDecl]
def expandFuntypeDecl : Macro
| `(funtype $id:declId $ps:bracketedBinder* $[:= $[$f:ident]? $fps:bracketedBinder*]? : $t:term) =>
  mkFuntypeDecl false id ps (f.getD none) (fps.getD #[]) t
| `(class funtype $id:declId $ps:bracketedBinder* $[:= $[$f:ident]? $fps:bracketedBinder*]? : $t:term) =>
  mkFuntypeDecl true id ps (f.getD none) (fps.getD #[]) t
| _ => Macro.throwUnsupported

