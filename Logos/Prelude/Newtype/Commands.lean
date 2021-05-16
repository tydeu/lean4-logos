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
        "unnamed instance binders are unsupported here"
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
  (mods : Syntax) (id : Syntax) 
  (params : Array Syntax) (fieldId : Syntax) (type : Syntax) 
  (isClass := false)
: MacroM Syntax :=
  if isClass then 
    `($mods:declModifiers class $id $params* where $fieldId:ident : $type)
  else
    `($mods:declModifiers structure $id $params* where $fieldId:ident : $type)

def mkNewtypeDecl 
  (mods : Syntax) (id : Syntax) (params : Array Syntax) 
  (exportField : Bool) (fieldId? : Option Syntax) (type : Syntax)
  (isClass := false) 
: MacroM Syntax := do
  let (name, uvars) := expandDeclId id
  let fieldId := fieldId?.getD (mkIdent `val) 
  let decl <- mkNewtypeStructDecl mods id params fieldId type isClass
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

syntax classTk := "class "
syntax newtypeTk := "newtype "
syntax whereTk := " := " <|> " where "
syntax exportTk := "export "

scoped syntax (name := newtypeDecl)
  declModifiers (classTk)? newtypeTk declId bracketedBinder* 
    (whereTk (exportTk)? ident)? ":" term : command

@[macro newtypeDecl]
def expandNewtypeDecl : Macro
| `($mods:declModifiers $[$clsTk?:classTk]? newtype $id $params* 
      $[$_w:whereTk $[$expTk??:exportTk]? $fId?:ident]? : $t) =>
  mkNewtypeDecl (isClass := clsTk?.isSome) 
    mods id params (expTk??.getD none).isSome fId? t
| _ => Macro.throwUnsupported

--------------------------------------------------------------------------------
-- Funtype
--------------------------------------------------------------------------------

def mkFuntypeDecl 
  (mods : Syntax) (id : Syntax) (typeParams : Array Syntax) 
  (exportField : Bool) (fieldId? : Option Syntax) 
  (applyParams : Array Syntax) (fnRet : Syntax) 
  (isClass := false)
: MacroM Syntax := do
  let (name, uvars) := expandDeclId id
  let applyType <- mkDepArrows applyParams fnRet
  let (applyArgs, fnParams) <- paramsToApp applyParams
  let fnType <- mkDepArrows fnParams fnRet
  let fnId := mkIdent `toFun
  let fieldId := fieldId?.getD fnId
  let decl <- mkNewtypeStructDecl mods id typeParams fieldId fnType isClass
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

syntax funtypeTk := "funtype "
scoped syntax (name := funtypeDecl)
  declModifiers (classTk)? funtypeTk declId bracketedBinder* 
    (whereTk ((exportTk)? ident)? bracketedBinder*)? ":" term : command

@[macro funtypeDecl]
def expandFuntypeDecl : Macro
| `($mods:declModifiers $[$clsTk?:classTk]? funtype $id $params* 
      $[$_w:whereTk $[$[$expTk???:exportTk]? $fId??:ident]? $fparams?*]? : $t) =>
  let shouldExport := ((expTk???.getD none).getD none).isSome
  mkFuntypeDecl (isClass := clsTk?.isSome) 
    mods id params shouldExport (fId??.getD none) (fparams?.getD #[]) t
| _ => Macro.throwUnsupported
