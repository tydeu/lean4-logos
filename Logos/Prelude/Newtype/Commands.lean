import Logos.Prelude.Newtype.Basic

open Lean Syntax

namespace Logos

--------------------------------------------------------------------------------
-- Util
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

def mkDepArrow (binder : Syntax) (term : Syntax) : MacroM Syntax :=
  `( $binder:bracketedBinder -> $term:term )

def mkDepArrows (binders : Array Syntax) (term : Syntax) : MacroM Syntax :=
  binders.foldrM mkDepArrow term

/--
  Extracts the pair `(ident, universe vars)` from a `declId`.
-/
def expandDeclId (id : Syntax) : Syntax × Array Syntax :=
  (id[0], id[1][1].getArgs.getEvenElems)

--------------------------------------------------------------------------------
-- Newtype
--------------------------------------------------------------------------------

def mkNewtypeStructDecl 
  (isClass : Bool) (declId : Syntax) 
  (params : Array Syntax) (fieldId : Syntax) (type : Syntax) 
: MacroM Syntax :=
  if isClass then 
    `(class $declId:declId $params* := $fieldId:ident : $type:term)
  else
    `(structure $declId:declId $params* := $fieldId:ident : $type:term)

def mkNewtypeDecl 
  (isClass : Bool) (declId : Syntax) (params : Array Syntax) 
  (exportField : Bool) (fieldId? : Option Syntax) (type : Syntax) 
: MacroM Syntax := do
  let (name, uvars) := expandDeclId declId
  let fieldId := fieldId?.getD (mkIdent `val) 
  let decl <- mkNewtypeStructDecl isClass declId params fieldId type
  let exprt := ite exportField (<- `(export $name ($fieldId))) mkNullNode
  let (args, vars) <- paramsToVars params
  let ntype := mkApp name args
  let kvar := mkIdent `self
  let kval := mkIdent (`self ++ fieldId.getId)
  `(
  $decl:command
  $exprt:command
  namespace $name:ident
  universes $uvars:ident*
  variable $vars:bracketedBinder* 
  instance $(mkIdent `isNewtype):ident : Newtype $ntype $type := 
    {pack := $(mkIdent `mk), unpack := fun $kvar => $kval} 
  end $name:ident
  )

scoped syntax (name := newtypeDecl)

  "class "? "newtype " declId bracketedBinder* 
    (":=" "export "? ident)? ":" term : command

@[macro newtypeDecl]
def expandNewtypeDecl : Macro
| `(newtype $id $params* $[:= $fId:ident]? : $t) =>
  mkNewtypeDecl false id params false fId t
| `(newtype $id $params* $[:= export $fId:ident]? : $t) =>
  mkNewtypeDecl false id params true fId t
| `(class newtype $id $params* $[:= $fId:ident]? : $t) =>
  mkNewtypeDecl true id params false fId t
| `(class newtype $id $params* $[:= export $fId:ident]? : $t) =>
  mkNewtypeDecl true id params true fId t
| _ => Macro.throwUnsupported

--------------------------------------------------------------------------------
-- Funtype
--------------------------------------------------------------------------------

def mkFuntypeDecl 
  (isClass : Bool) (declId : Syntax) (typeParams : Array Syntax) 
  (exportField : Bool) (fieldId? : Option Syntax) 
  (applyParams : Array Syntax) (fnRet : Syntax) 
: MacroM Syntax := do
  let (name, uvars) := expandDeclId declId
  let applyType <- mkDepArrows applyParams fnRet
  let (applyArgs, fnParams) <- paramsToApp applyParams
  let fnType <- mkDepArrows fnParams fnRet
  let fnId := mkIdent `toFun
  let fieldId := fieldId?.getD fnId
  let decl <- mkNewtypeStructDecl isClass declId typeParams fieldId fnType
  let exprt := ite exportField (<- `(export $name ($fieldId))) mkNullNode
  let (typeArgs, vars) <- paramsToVars typeParams
  let ntype := mkApp name typeArgs
  let kvar := mkIdent `self
  let kfn := mkIdent (`self ++ fieldId.getId)
  let fnAbbrev := ite fieldId?.isSome 
    (<- `(abbrev $fnId ($kvar : $ntype) := $kfn)) mkNullNode
  let apply := mkIdent `apply
  let applyFn := mkIdent `applyFn
  `(
  $decl:command
  $exprt:command
  namespace $name:ident
  universes $uvars:ident*
  variable $vars:bracketedBinder* 
  $fnAbbrev:command
  set_option checkBinderAnnotations false in
  abbrev $apply [$kvar : $ntype] $applyParams* := $kfn $applyArgs*
  abbrev $applyFn ($kvar : $ntype) $applyParams* := $kfn $applyArgs*
  instance $(mkIdent `isFuntype):ident : Funtype $ntype $fnType $applyType := 
    {pack := $(mkIdent `mk), unpack := fun $kvar => $kfn, apply := $applyFn} 
  end $name:ident
  )

scoped syntax (name := funtypeDecl)
  "class "? "funtype " declId bracketedBinder* 
    (":=" ("export "? ident)? bracketedBinder*)? ":" term : command

@[macro funtypeDecl]
def expandFuntypeDecl : Macro
| `(funtype $id $params* $[:= $[$fId:ident]? $fparams*]? : $t) =>
  mkFuntypeDecl false id params false (fId.getD none) (fparams.getD #[]) t
| `(funtype $id $params* $[:= $[export $fId:ident]? $fparams*]? : $t) =>
  let fId := fId.getD none
  mkFuntypeDecl false id params fId.isSome fId (fparams.getD #[]) t
| `(class funtype $id $params* $[:= $[$fId:ident]? $fparams*]? : $t) =>
  mkFuntypeDecl true id params false (fId.getD none) (fparams.getD #[]) t
| `(class funtype $id $params* $[:= $[export $fId:ident]? $fparams*]? : $t) =>
  let fId := fId.getD none
  mkFuntypeDecl true id params fId.isSome fId (fparams.getD #[]) t
| _ => Macro.throwUnsupported
