"""
Sole place where Lean 4 syntax is hard‑coded.
If you later refine the target syntax you only patch here.
"""
# INDUCTIVE_TMPL = """inductive {name} where\n| mk : {name}"""

STRUCTURE_TMPL  = """structure {lemma}_{sense} {type_params} where
{fields}"""

NON_CORE_PRED_TMPL = """structure {lemma} (E T : Type) where
  event: E
  value: T"""

NON_CORE_ROLE_PRED_TMPL = """def {noncore_name}ROLE {{D E A : Type}} (d : D) (e : E) (a : A) : Prop := 
  d.event = e ∧ d.value = a"""

# INSTANCE_TMPL   = "def {var} : {type} := {value}"
INSTANCE_TMPL   = 'def {var} : {type} :=  ⟨"{text}"⟩'

MODIFIER_INST_TMPL = 'def {name} := ⟨"{modifier_name}" {modifyee}⟩'

AXIOM_TMPL      = "axiom {label} : {event_pred} ({type}) {var}"



# EVENT_FUN_DEFS = """\
# def Veridical    (X : Type) (x : X) : Prop := True
# def NonVeridical (X : Type) (x : X) : Prop := True
# def Approx       (X : Type) (x : X) : Prop := True
# def E4C (X : Type) (x : X) : Prop := True  -- exists entity for connector proposition
# """


GENERIC_STRUCT_TMPL = """structure {name} {type_params} where
{fields}"""

SPECIAL_ENTITY_TMPL = """structure {name} where
{fields}"""


COMPOUND_TMPL = 'let {name} := Compound{ent_or_event} ConnectorType.{connector_type} [{e_list}]'

ROLE_ASSIGN_STRU_TMPL = "{indent}let {role_id} := {role} {pred} {arg}"

ROLE_ASSIGN_PRED_TMPL = "{indent}{role} {role_id} {pred} {arg}"

CONST_LET_DECLARE_TMPL = '{indent}let {concept} : {type} := ⟨"{concept_name}"⟩'

# inductive ConnectorType where
#   | And | Or
#   deriving DecidableEq, Repr

# structure CompoundEntity where
#   connector : ConnectorType
#   items : List Entity

# structure CompoundEvent where
#   connector : ConnectorType
#   items : List Event

ROLE_PREDS = '''\
import Lean

open Lean Elab Command Meta

structure Entity where
  name : String

structure Event where
  name : String

structure Modifier where 
  name : String

structure Connector where
  name : String

syntax (name := genRoleTag) "#genRoleTag" ident,+ : command

@[command_elab genRoleTag]
def elabGenRoleTag : CommandElab
| `( #genRoleTag $idents:ident,* ) => do
  let ctorList := (idents.getElems.map (·.getId.toString)).toList
  let joined := " | ".intercalate ctorList
  let src := s!"inductive RoleTag where\n  | {{joined}}\n  deriving DecidableEq, Repr"
  match Parser.runParserCategory (← getEnv) `command src with
  | Except.ok stx => elabCommand stx
  | Except.error err => throwError "parser error in macro expansion: {{err}}"
| _ => throwUnsupportedSyntax

#genRoleTag {roles}
-- Reusable role assignment structure
structure RoleAssignment (E T : Type) where
  role : RoleTag
  event : E
  value : T

-- Generic predicate for checking role assignment
def bindsTo {{E T : Type}} (r : RoleAssignment E T) (e : E) (t : T) (tag : RoleTag) : Prop :=
  r.event = e ∧ r.value = t ∧ r.role = tag

-- === Macro ===

syntax (name := defRoleHelpers) "#genRoleHelpers" "[" ident,+ "]" : command

@[command_elab defRoleHelpers]
def elabRoleHelpers : CommandElab
| `(command| #genRoleHelpers [ $ids:ident,* ]) => do
  for id in ids.getElems do
    let roleName : Name := id.getId
    let ctorName := Name.mkSimple roleName.toString.toLower
    let binderName := Name.mkSimple roleName.toString.toUpper
    let ctorIdent := mkIdent ctorName
    let binderIdent := mkIdent binderName

    -- Use explicit qualified name for RoleTag constructor
    let roleCtor := mkIdent (``RoleTag ++ roleName)

    let ctor ← `(def $ctorIdent {{E T : Type}} (e : E) (x : T) : RoleAssignment E T :=
      {{ role := $roleCtor, event := e, value := x }})

    let binder ← `(def $binderIdent {{E T : Type}} (r : RoleAssignment E T) (e : E) (x : T) : Prop :=
      bindsTo r e x $roleCtor)

    elabCommand ctor
    elabCommand binder
| _ => throwUnsupportedSyntax

#genRoleHelpers [{roles}]
'''
