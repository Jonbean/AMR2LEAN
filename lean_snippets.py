"""
Sole place where Lean 4 syntax is hard‑coded.
If you later refine the target syntax you only patch here.
"""
INDUCTIVE_TMPL = """inductive {name} where\n| mk : {name}"""

NON_CORE_PRED_TMPL = """structure {lemma} (E T : Type) where
  event: E
  value: T"""

NON_CORE_ROLE_PRED_TMPL = """def {noncore_name}ROLE {{D E A : Type}} (d : D) (e : E) (a : A) : Prop := 
  d.event = e ∧ d.value = a"""

INSTANCE_TMPL   = "def {var} : {type} := {value}"

ABBREV_TMPL = "abbrev {abbrev_name} : {type_sig}"

AXIOM_TMPL      = "axiom {label} : {event_pred} ({type}) {var}"

# NON_CORE_PRED_TMPL = "def {name} {{E F : Type}} (e : E) (f : F) : Prop := True"

EVENT_FUN_DEFS = """\
def Veridical    (X : Type) (x : X) : Prop := True
def NonVeridical (X : Type) (x : X) : Prop := True
def Approx       (X : Type) (x : X) : Prop := True
def E4C (X : Type) (x : X) : Prop := True  -- exists entity for connector proposition
"""


# GENERIC_STRUCT_TMPL = """structure {name} {type_params} where
# {fields}"""

GENERIC_STRUCT_TMPL = """structure {name} where
{fields}"""

SPECIAL_ENTITY_TMPL = """structure {name} where
{fields}"""

COMPOUND_EVENT_TMPL = """structure compound_event_{N} {type_params} where
{fields}"""

COMPOUND_TMPL = """structure compound_{N} {type_params} where
{fields}"""

COMPOUND_ENT_TMPL = """structure compound_ent_{N} {type_params} where
{fields}"""
MODIFIER_INST_TMPL = 'def {name} {type_sig} := ⟨{instants}⟩'

NON_CORE_ROLE_AXIOM_TMPL = 'axiom {role_name} : {modifiee_type} → {modifier_type} → Prop '
NON_CORE_ROLE_PRED_TMPL = '{indent}{role_name} {modifiee_var} {modifier_var}'
# LITERAL_EDGE_TMPL = 'def {pred} {{E : Type}} (e : E) (val : String) : Prop := True'
# NUMERIC_MOD_TMPL  = 'def {name} {{Q : Type}} (q : Q) : Prop := True'
# BINARY_REL_TMPL   = 'def {name} {{E F : Type}} (x : E) (y : F) : Prop := True'
# TERNARY_REL_TMPL  = 'def {name} {{E F G : Type}} (x : E) (y : F) (z : G) : Prop := True'

# -----------------------------------------------------------------------------
#  Generic modifier universe  — extend by adding new constructors
# -----------------------------------------------------------------------------
# MODIFIER_SNIPPET = """
# inductive Modifier : Type 1 where
# | eventAdj     {E : Type} (ev : E)
# | entityAdj     {E : Type} (ev : E)
# | literalAdj   (rel : String) (val : String)   -- :degree "really", :mode "imp"
# | binaryRel    {X Y : Type} (rel : String) (x : X) (y : Y) -- :source boat river
# | nameAdj      (nm: String)
# | modeAdj      (nm: String)
# """
# MODIFIED_CONC_SNIPPET = """
# structure ModifiedConcept (Core : Type) where
#   (head : Core)
#   (mods : List Modifier)
# """

# CHOICE_SNIPPET = """
# structure Choice (α : Type) where
#   (options   : List α)
#   (exclusive : Bool)     -- True = XOR, False = inclusive OR/AND
# """

CONST_LET_DECLARE_ENTITY_TMPL = '{indent}let {concept} : {type} := ⟨"{concept_name}"⟩'
CONST_LET_DECLARE_STRUCT_TMPL = '{indent}let {concept} : {type} := {{ {arg_str} }}'
QUANT_DECLARE_STRUCT_TMPL = '{indent}{pred_var} = {{ {arg_str} }}'