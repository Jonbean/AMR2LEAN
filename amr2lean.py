# frame centric AMR-to-Lean translation module

from __future__ import annotations
import re, textwrap, itertools
from collections import defaultdict, OrderedDict
from typing import Dict, List, Tuple


from propbank_interface import PropbankCatalogue, Roleset
from amr_special_frames import AMRSpecialFrames
from amr_toolbox.AMRgraph import PenmanAMRTree, AMRNode, name_collapser
from amr_special_entities import AMRSpecialEntities
from amr_special_preps import PrepInventory

from collections import deque
import copy 
import math 
from lean_snippets import *
from amr_patterns import *
from utils import *
import utils

def _is_noun_lemma(lemma: str) -> bool:
    if lemma in ALWAYS_ENTITY:  return True
    if lemma in ALWAYS_MOD:     return False
    synsets = wn.synsets(lemma, pos=wn.NOUN)
    return any(lemma.lower() == s.name().split('.')[0] for s in synsets)

def _is_number(lemma: str) -> str | None:
    try:
        f = float(lemma)
        if not math.isfinite(f):
            return None
        if f.is_integer():
            return "int"
        return "float"
    except ValueError:
        return None

def _is_mod(lemma: str) -> bool:
    if lemma in ALWAYS_MOD:     return True
    if _is_number(lemma.strip()): return True
    synsets = wn.synsets(lemma)
    if len(synsets) > 0:
        for synset in synsets[:max(3, len(synsets))]:
            if synset.name().split('.')[0] == lemma.lower() and synset.pos() != 'n':
                return True

    return False
# --------------------------------------------------------------------------- #
#  Main Lean module container
# --------------------------------------------------------------------------- #
class LeanModule:
    def __init__(self, import_semantic_gadgets=False):
        self.inductives : Dict[str,str] = {'Entity': GENERIC_STRUCT_TMPL.format(name="Entity", fields='  name : String'), 'Prep': GENERIC_STRUCT_TMPL.format(name="Prep", fields='  name : String')}
        self.structs    : Dict[str,str] = {}
        self.instances  : List[str] = []
        self.exist_axioms : List[str] = []      # new: quantifier axioms
        self.axioms     : List[str] = []
        self.noncore_preds : Dict[str,str] = {}   # edge → template line
        self.noncore_axioms: List[str] = []
        self.import_semantic_gadgets = import_semantic_gadgets
        self.roles_inventory : Set[str] = set()

        # ----- for multi-sentence ordered emission -----
        self.statements_in_order : List[str] = []  # each item is a full Lean declaration text

    def update_inventory(self, new_inventory):
        self.roles_inventory.update(new_inventory)

    def render(self) -> str:
        if self.import_semantic_gadgets:
            parts = [
                "import AMRGadgets",
                *self.inductives.values(),
                "", *self.structs.values(),
                "", *self.noncore_axioms,
                "", *self.axioms,
                ]
        else:            
            parts = [
                *self.inductives.values(),
                "", *self.structs.values(),
                "", *self.noncore_axioms,
                "", *self.axioms,
                
                ]
        print('-'*80)
        print('self.inductives: ', self.inductives)
        print('-'*80)
        print('self.structs: ', self.structs)
        print('-'*80)
        print('self.noncore_axioms: ', self.noncore_axioms)
        print('-'*80)
        print('self.axioms: ', self.axioms)
        print('-'*80)
        
        
        return "\n\n".join(parts)

    def theorem_render(self, negation=False):
        if negation:
            negated_axioms = ['\n'.join(axiom.split('\n')[:1] + [' ¬ ('] + [' '+axiom_line for axiom_line in axiom.split('\n')[1:]] + [' )']) for axiom in self.axioms]

            new_theorems = [re.sub(r'^(\s*)axiom\s+([^\s:]+)(\s*:)', r'\1theorem \2_t\3', axiom, flags=re.MULTILINE)+':= by\n sorry' for axiom in negated_axioms]

        else:
            new_theorems = [re.sub(r'^(\s*)axiom\s+([^\s:]+)(\s*:)', r'\1theorem \2_t\3', axiom, flags=re.MULTILINE)+':= by\n sorry' for axiom in self.axioms]

        theorem_str = "\n\n".join(new_theorems)
        parts = [
            "", *self.structs.values(),
            "", *self.noncore_axioms,
            theorem_str
            ]
        return "\n\n".join(parts)

    # NEW: add an ordered statement (axiom/lemma/theorem), with optional negation wrapper
    def add_statement(self, kind: str, name: str, body: str, negate: bool = False):
        """
        kind ∈ {'axiom','lemma','theorem'}
        name: Lean identifier
        body: the proposition lines (already formatted/indented)
        """
        prop = body
        if negate:
            prop = f"  ¬ (\n{body}\n  )"

        if kind == 'axiom':
            txt = f"{kind} {name}:\n{prop}"
        elif kind in {'lemma', 'theorem'}:
            knowledge_insert_pl = '-- [Optional knowledge insertion point: extra axioms may be added here if needed]\n\n'
            thm_lemma_bdy = f"{kind} {name}:\n{prop}\n:= by\n  sorry"
            txt = knowledge_insert_pl + thm_lemma_bdy
        else:
            raise ValueError(f"Unknown statement kind: {kind}")
        self.statements_in_order.append(txt)

    # NEW: boilerplate-only rendering (no statements)
    def render_boilerplate(self) -> str:
        parts = []
        if self.import_semantic_gadgets:
            parts.append("import AMRGadgets")

        # inductives then structs
        parts.extend(self.inductives.values())
        if self.structs:
            parts.append("")
            parts.extend(self.structs.values())

        # dedupe non-core axioms while preserving order
        if self.noncore_axioms:
            parts.append("")
            seen = set()
            deduped = []
            for line in self.noncore_axioms:
                if line not in seen:
                    seen.add(line)
                    deduped.append(line)
            parts.extend(deduped)

        return "\n\n".join(p for p in parts if p.strip() != "")

    # NEW: final renderer for multi-sentence sequence
    def render_sequence(self) -> str:
        top = self.render_boilerplate()
        stmts = "\n\n".join(self.statements_in_order)
        if top and stmts:
            return top + "\n\n" + stmts
        return top or stmts

    # NEW: merge helper (if need to merge modules)
    def merge_from(self, other:"LeanModule"):
        self.inductives.update(other.inductives)
        for k, v in other.structs.items():
            if k not in self.structs:
                self.structs[k] = v
        # dedupe non-core axioms
        merged = []
        seen = set()
        for line in self.noncore_axioms + other.noncore_axioms:
            if line not in seen:
                seen.add(line)
                merged.append(line)
        self.noncore_axioms = merged
        self.roles_inventory.update(other.roles_inventory)

MOD_CACHE = set()   # keep at module level

# --------------------------------------------------------------------------- #
#  Translator
# --------------------------------------------------------------------------- #
class AMR2LeanTranslator:
    """Call translate(amr_str) -> Lean source string."""
    def __init__(self, propbank_catelog, import_semantic_gadgets:bool=False):
        self.pb = propbank_catelog
        self.ent = AMRSpecialEntities("special_entities.json")
        self.M  = LeanModule(import_semantic_gadgets)
        self.import_semantic_gadgets = import_semantic_gadgets
        self.sf = AMRSpecialFrames("special_frames.json")
        self.preps = PrepInventory("special_preps.json")
        self.struct_arg_order: Dict[str, List[int]] = {}   # e.g. "new_02" → [1, 2]
        self.node_type = {}
        self.node_inst_name = {}
        self._pred_sig : Dict[str, str] = {}
        self.node_deps : Dict[AMRNode, set] = {}
        self.node_order : List[AMRNode] = []
        self.let_bound_vars = set()

    @staticmethod
    def _is_predicate(node:AMRNode) -> bool:
        return bool(SENSE_RE.search(node.text.strip()))
    
    @staticmethod
    def _is_attribute(node: AMRNode) -> bool:
        """True for nodes whose var_name starts with 'attr-' (AMR attributes)."""
        return bool(ATTR_RE.match(node.var_name))
    
    @staticmethod
    def _filter_i(nodes:Dict[str,AMRNode]):
        # filter the node where the variable name and concept name are both 'i', confuses lean

        for nvar, node in nodes.items():
            if nvar == 'i' and node.text == 'i':
                node.var_name = 'ii'

    def categorize_node(self, node):
        # Rule 0: connectives
        if node.text in CONNECTOR:
            if len(node.children) > 0:
                return "compound-ent"
            else:
                return "term-noun"

        # Rule 1: Special Frame
        if self.sf.get(node.text):
            return "special-frame"

        # Rule 2: Predicate
        if SENSE_RE.search(node.text):
            return "predicate"

        # Rule 3: Special Entity
        if self.ent.get(node.text):
            return "special-entity"

        # Rule 4: Attribute leaf
        if node.var_name.startswith("attr-"):
            number_type = _is_number(node.text)
            if number_type:
                return number_type
            return "string"

        # Rule 5: Terminal node(non-attribute)
        if not node.children:
            if _is_mod(node.text):
                return "term-mod"
            elif _is_noun_lemma(node.text):
                return "term-noun"
            else:
                return "term-other"

        # Rule 6: Preposition (if in preposition dict or any :op children)
        if self.preps.get(node.text):
            return "inter-prep-mod"

        # Rule 7: Adjective intermediate nodes
        if _is_mod(node.text) and not _is_noun_lemma(node.text):
            return "inter-mod"
        if node.text == "name":
            first_rel = next(iter(node.children.values()))
            if first_rel.startswith(":op"):
                return "name"

        return "inter-noun"

    # ---------- public entry ----------
    def translate(self, amr_str, sid='') -> str:
        tree = PenmanAMRTree(amr_str, remove_alignmark=True)

        if sid != '':
            tree.add_sent_mark(sid)
        self._filter_i(tree.node_dict)
        self._prop_cache = {}
        # reinit records banks 
        self.struct_arg_order = {}   # e.g. "new_02" → [1, 2]
        self._skip_instantiation = set()
        self._pred_sig = {}
        self.noncore_roles = set()
        self.M = LeanModule(self.import_semantic_gadgets)

        # --- MUST happen first! ---
        self._annotate_meta(tree.node_dict)
        self.node_deps, depth, self.noncore_roles = self._annotate_node_category(tree)
        print('meta: ')
        print({varname: node.meta for varname, node in tree.node_dict.items()})
        print('-'*80)
        print_tree(self.node_deps, indent=1)
        print('-'*80)
        self.node_order = topo_sort_amr(self.node_deps, depth)
        self.node_order.reverse()
        print('self.node_order: ', [(node.var_name, node.text) for node in self.node_order])
        print('-'*80)
        self._annotate_attributives(tree.node_dict)

        # Now every node has a .meta dict, so these are safe:
        self._emit_types()

        self._emit_axioms(tree.top)
        # ------------------------------------------------------------------

        return self.M.render()

    # ------------------------------------------------------------------ #
    #  Phase 0 : annotate graph with meta flags
    # ------------------------------------------------------------------ #
    def _annotate_meta(self, nodes:Dict[str,AMRNode]):
        # 6. non-veridical = child reached via :content
        
        for n in nodes.values():
            for child, rel in n.children.items():
                if rel == ":content":
                    child.meta["nonveridical"] = True
                elif rel == ":content-of":          # ← new
                    n.meta["nonveridical"] = True
                
        # 7. definiteness
        for n in nodes.values():
            if self._is_attribute(n):
                continue
            if self._is_predicate(n):        # only concepts matter
                continue
            if has_child(n, ":definite", "+"):
                n.meta["definite"] = "+"
            elif has_child(n, ":definite", "-"):
                n.meta["definite"] = "-"
            else:
                n.meta["definite"] = None
            # 8. plural
            if has_child(n, ":plural", "+"):
                n.meta["plural"] = True
        # print('n.meta: ', [(n.text, n.var_name, n.meta) for n in nodes.values()])
        self._propagate_nonveridical(nodes)

    def _propagate_nonveridical(self, nodes):
        queue = [n for n in nodes.values() if n.meta.get("nonveridical")]
        while queue:
            cur = queue.pop()
            for ch, rel in cur.children.items():
                # print('ch: ', ch.var_name, '|', ch.text)
                if not ch.meta.get("nonveridical"):
                    ch.meta["nonveridical"] = True
                    queue.append(ch)
    

    def _annotate_attributives(self, nodes):
        for child in nodes.values():
            for parent, rel in child.parents.items():
                m = ATTR_OF_RE.match(rel)
                if m:
                    child.meta["attributive"] = int(m.group(1))   # which arg slot
                    child.meta["attr_head"]   = parent


    def _annotate_node_category(self, tree):

        deps = defaultdict(set)
        depth = {}
        visited = set()
        queue = deque([(tree.top, 0)])
        noncore_roles = set()

        while queue:
            node, d = queue.popleft()
            if node in visited:
                continue
            visited.add(node)
            depth[node] = d

            node.meta["category"] = self.categorize_node(node)

            for child, rel in node.children.items():
                queue.append((child, d+1))

                if rel.endswith('-of') and rel not in NON_CORE_EDGES:
                    # this means the role is an inverted one
                    deps[node].add(child)
                
                else:
                    deps[child].add(node)

                deps.setdefault(node, set())
                deps.setdefault(child, set())

                # record non core role for later structure emit 
                rel_lower = rel.lower()
                if not rel_lower.startswith(':arg'):
                    noncore_triple = (node.var_name, rel_lower, child.var_name)
                    if  noncore_triple not in noncore_roles:
                        noncore_roles.add(noncore_triple)

        return deps, depth, noncore_roles
    # ------------------------------------------------------------------ #
    #  Phase 1 :  inductive & structure boiler-plate                     #
    # ------------------------------------------------------------------ #

    def _node_norm_name(self, node):
        node_cat = node.meta['category']
        type_sig_str = None
        norm_name = node.text.replace('-', '_')+'_'+node.var_name
        if node_cat == 'compound-ent':
            total_ops = 0
            for child, op_rel in node.children.items():
                total_ops += 1

            type_sig_str = f"Connector{total_ops}_{node.var_name}"
        
        if node_cat in ['predicate', 'special-frame']:
            parts = node.text.rsplit('-', 1)
            lemma, sense = parts + [''] * (2 - len(parts))
            type_sig_str = f"{lemma.replace('-','_')}_{sense}_{node.var_name}" 

        elif node_cat == 'special-entity':
            type_sig_str = norm_name

        elif node_cat == 'attribute':
            if _is_number(node.text):
                # only the most primative category of node can specify the type signature immediately.
                type_sig_str = "Float"
            else:
                type_sig_str = "String"

        elif node_cat in ['term-noun', 'inter-noun', 'term-other']:
            type_sig_str = "Entity"
            
        elif node_cat in ['inter-prep-mod', 'inter-mod']:
            type_sig_str = "Prep"
        else:
            type_sig_str = "String"

        return type_sig_str

    def _mk_noncore_axioms(self, key: str, node: AMRNode) -> List(str):
        # non core roles are typically decorator or modifier roles. We use binary predicative axiom to encode these relations.

        non_core_axioms = []
        for c, rel_ in node.children.items():
            rel = rel_.lower()
            inversed_role = False
            if rel.endswith('-of') and rel not in OF_SPECIAL_ROLE:
                rel = rel[:-3]
                inversed_role = True
            if not (rel.startswith(':arg') 
                or (rel in INDICATOR_NONCORE_RELS)
                or node.text in CONNECTOR):
                norm_rel = NON_CORE_EDGES.get(rel, rel[1:].replace('-', ''))

                c_var = c.var_name.replace('-', '_')
                n_var = node.var_name.replace('-', '_')
                role_name = f"{n_var}_{norm_rel}_{c_var}"

                modifiee_type = self._pred_sig.get(node.var_name, self._node_norm_name(node))
                modifier_type = self._pred_sig.get(c.var_name, self._node_norm_name(c))

                if inversed_role:
                    role_name = f"{c_var}_{norm_rel}_{n_var}"
                    non_core_axioms.append(NON_CORE_ROLE_AXIOM_TMPL.format(role_name=role_name, modifiee_type=modifier_type, modifier_type=modifiee_type))
                else:
                    non_core_axioms.append(NON_CORE_ROLE_AXIOM_TMPL.format(role_name=role_name, modifiee_type=modifiee_type, modifier_type=modifier_type))
        return non_core_axioms


    def _mk_pred_struct(self, key, node):
        # retrieve propbank role sets as template
        rs = self.pb.get_roleset(node.text)   # may be None
        # print('n.text: ', n.text)
        # print('rs: ', rs)
        # print('-'*80)
        if not (rs == None 
            or '91' in node.text
            or '92' in node.text):
            print('mk_pred_struct, key: ', key)
            structure_str = self._mk_pb_struct(key, rs, node)
            print('structure_str: ', structure_str)
            self.M.structs[key] = structure_str
        else:
            # ----- check AMR special-frame catalogue -----
            spec_roles = self.sf.get(node.text)
            print('key for spec_roles: ', key)
            if spec_roles is not None:
                # Build structure with named fields from JSON
                self.M.structs[key] = self._mk_spec_frame_struct(key, spec_roles, node)
            else:
                # fallback: generic arg0, arg1, … this case is AMR newly added frames not covered by propbank yet. 
                # 1. collect roles ad-hoc from AMR
                self.M.structs[key] = self._mk_generic_pred_struct(key, node)

                # self.M.structs[key] = self._mk_generic_struct(key, idx_set)

    def _predicate_norm_name(self, node):
        parts = node.text.rsplit('-', 1)
        lemma, sense = parts + [''] * (2 - len(parts))
        key = f"{lemma.replace('-','_')}_{sense}"
        return key
    def _handle_etc(self, node):
        p = list(node.parents.keys())[0]
        print('p: ', p.text)
        if p.text in ['and', 'or', 'multisentence']:
            any_other_c = None
            for c in p.children.keys():
                if c.var_name != node.var_name:
                    any_other_c = c
                    break

            print('any_other_c.var_name: ', any_other_c.var_name, '|any_other_c.text: ',any_other_c.text)
            if any_other_c:
                self._pred_sig[node.var_name] = self._pred_sig[any_other_c.var_name]


    def _emit_types(self):
        etc_nodes = []

        for n in self.node_order:
            print('-----------emit-types------------')

            node_cat = n.meta['category']
            print('n.var_name: ', n.var_name, '|n.text: ', n.text, '|ncat: ', node_cat)
            # ---------- connector lemmas ----------
            if n.text.strip() == "et-cetera":
                etc_nodes.append(n)
                print('etc n.text: ', n.text)

            if node_cat == 'compound-ent':
                # check how many ops 
                total_ops = 0
                for child, op_rel in n.children.items():
                    total_ops += 1

                type_sig_str = f"Connector{total_ops}_{n.var_name}"
                self._pred_sig[n.var_name] = type_sig_str
                # M.tructs should be ready if the topological sort ordering is correct.
                ops = []
                realized_vars = []
                for child, rel in n.children.items():
                    if rel.startswith(':op'):
                        op_type = self._pred_sig.get(child.var_name, self._node_norm_name(child))

                        child_val = self._type_dependent_arg_value(op_type, child)

                        ops.append((rel[1:].lower(), op_type, child_val))



                arguments = "\n".join(['  '+key+' : '+arg_type for key, arg_type, arg_val in ops])
                realized_r_vars = {key: arg_val for key, arg_type, arg_val in ops}
                # self.M.structs[type_sig_str] = self._mk_generic_struct(type_sig_str, arguments)
                self.M.structs[type_sig_str] = GENERIC_STRUCT_TMPL.format(name=type_sig_str, fields=arguments)
                self.struct_arg_order[n.var_name] = realized_r_vars

                continue
            

            # for all predicate nodes, we generate structures to hold data
            if node_cat == 'predicate' or node_cat == 'special-frame':
                parts = n.text.rsplit('-', 1)
                lemma, sense = parts + [''] * (2 - len(parts))
                key = f"{lemma.replace('-','_')}_{sense}_{n.var_name}" 
                
                self._pred_sig[n.var_name] = key
                # M.structs may not be ready, wait until the we resolved all of the simple types 

                self._mk_pred_struct(key, n)
                self.M.noncore_axioms += self._mk_noncore_axioms(key, n)

            else:
                # not a predicates or special frame, then, it could be noun nodes or special entity node or prep node
                norm_name = n.text.replace('-', '_')+'_'+n.var_name
                
                if node_cat == 'special-entity':
                    # --- declare fixed-field structure once
                    spec_ent = self.ent.get(n.text)

                    if norm_name not in self.M.structs:
                        self.M.structs[norm_name] = self._mk_spec_entity_struct(norm_name, spec_ent)
                        # M.structs is ready since spec_entity children are all terminal pr constant, wait until the we resolved all of the simple types 
                        self.node_type[n.var_name] = norm_name
                    self._pred_sig[n.var_name] = norm_name

                elif node_cat == ['string', 'attribute']:
                    self._pred_sig[n.var_name] = "String"
                elif node_cat in ['float', 'int']:
                    self._pred_sig[n.var_name] = "Float"
                elif node_cat in ['term-noun', 'inter-noun', 'term-other']:
                    self._pred_sig[n.var_name] = "Entity"
                    self.M.noncore_axioms += self._mk_noncore_axioms(norm_name, n)
                elif node_cat in ['inter-prep-mod', 'inter-mod']:
                    self._pred_sig[n.var_name] = "Prep"
                    self.M.noncore_axioms += self._mk_noncore_axioms(norm_name, n)
                else:
                    self._pred_sig[n.var_name] = "String"


        
        # second pass to re-decide et-cetera node
        
        for etcn in etc_nodes:
            self._handle_etc(etcn)
            print('etcn.var_name: ', etcn.var_name, '|etcn.text: ', etcn.text)
            print('self._pred_sig[etcn.var_name]: ', self._pred_sig[etcn.var_name])


    # ------------------------------------------------------------------ #
    #  generic struct for special entities such as rate-quantity
    # ------------------------------------------------------------------ #
    def _mk_spec_entity_struct(self, spec_ent_name: str, spec_ent: List[EntityField]) -> str:
        field_lines = "\n".join(f"  ({f.role[1:]} : Option {f.ty})" for f in spec_ent)
        return SPECIAL_ENTITY_TMPL.format(name=spec_ent_name, fields=field_lines)

    def _type_dependent_arg_value(self, lean_type, node):
        if lean_type == "String":
            return f'"{node.text}"'
        elif lean_type in ["Float", "Int"]:
            return f'{node.text}'
        else:
            return f'{node.var_name}'

    def _roleset_construction(self, node):
        idx_set = {}
   
        for cn, rel in node.children.items():
            m = re.match(r"^:arg(\d+)$", rel, re.I)
            if m:
                pred_sig = self._pred_sig.get(cn.var_name, self._node_norm_name(cn))
                
                arg_value = self._type_dependent_arg_value(pred_sig, cn)
                idx_set[rel[1:].lower()] = (pred_sig, arg_value)

        # incoming :argk-of
        for pn, rel in node.parents.items():
            m = re.match(r":arg(\d+)-of", rel, re.I)
            if m: 
                pred_sig = self._pred_sig.get(pn.var_name, self._node_norm_name(pn))
                arg_value = self._type_dependent_arg_value(pred_sig, pn)
                idx_set[f'arg{int(m.group(1))}'] = (pred_sig, arg_value)
                
        return idx_set

    def _mk_pb_struct(self, struct_name: str, rs:Roleset, node:AMRNode) -> str:
        # print('rs.roles: ', [(r.idx, r.fun) for r in rs.roles])
        roles = sorted(rs.roles, key=lambda r: int(r.idx))   # 0,1,2,…

        roles_types = {f'arg{r.idx}': f'Option Entity' for r in roles}
   
        idx_set = self._roleset_construction(node)

        print('-'*80)
        print(node.children)
        print('idx_set: ', idx_set)
        arg_lines = []
        for role in roles:
            arg_type = idx_set.get(f'arg{role.idx}', ['Entity'])
            arg_line = f"  (arg{role.idx} : Option {arg_type[0]}) -- {role.fun}"
            arg_lines.append(arg_line)

        fields  = "\n".join(arg_lines)

        # collects realized vars
        realized_r_vars = {f'arg{r.idx}': 'none' for r in roles}
        for r, arg_type_var in idx_set.items():
            realized_r_vars[r] = f'some {arg_type_var[1]}'
        self.struct_arg_order[node.var_name] = realized_r_vars
        print('mk_pb_struct realized_args: ', realized_r_vars)
        
        return GENERIC_STRUCT_TMPL.format(name=struct_name, fields=fields)

    # ------------------------------------------------------------------ #
    #  generic struct for AMR-only frames  (non PropBank entry)
    # ------------------------------------------------------------------ #



    def _mk_generic_pred_struct(self, pred: str, node: AMRNode) -> str:
        # sorted list, e.g. [1,2]  (arg1, arg2) since generic frames also use index arguments.
        # pred already replaced `-` with underscore
        idx_set = self._roleset_construction(node)
        
        # if still empty, default to {0} arguments structure
        if len(idx_set) == 0:
            return ''

        fields  = "\n".join(
            f"  ({arg_idx} : {arg_type_tp[0]})"
            for arg_idx, arg_type_tp in idx_set.items())

        self.struct_arg_order[node.var_name] = {arg_idx: arg_type_tp[1] for arg_idx, arg_type_tp in idx_set.items()}

        return GENERIC_STRUCT_TMPL.format(
            name=pred, fields=fields)

    def _mk_spec_frame_struct(self, spec_frame_name: str, spec_roles: List[SpecialRole], node: AMRNode) -> str:
        # tparams = " ".join(f"(t{i+1} : Type)" for i in range(len(spec_roles)))

        idx_set = self._roleset_construction(node)
        arg_lines = []
        for spec_role in spec_roles:
            arg_type = idx_set.get(f'arg{spec_role.idx}', ['Entity'])
            print('spec_frame_struct, arg_type : ', arg_type)
            arg_line = f"  (arg{spec_role.idx} : Option {arg_type[0]}) -- {spec_role.name}"
            arg_lines.append(arg_line)

        fields  = "\n".join(arg_lines)

        # collects realized vars
        realized_r_vars = {f'arg{r.idx}': 'none' for r in spec_roles}
        for cn, arg_role in node.children.items():
            if arg_role.lower().startswith(':arg') and '-' not in arg_role:
                real_arg_name = arg_role.lower()[1:]
                # roles_types[real_arg_name] = f'Option {self._pred_sig[cn.var_name]}'
                cn_type = self._pred_sig.get(cn.var_name, self._node_norm_name(cn))

                realized_r_vars[real_arg_name] = f'some {self._type_dependent_arg_value(cn_type, cn)}'

        self.struct_arg_order[node.var_name] = realized_r_vars
        return  GENERIC_STRUCT_TMPL.format(
            name=spec_frame_name, fields=fields)

    # ------------------------------------------------------------------ #
    #  Phase 3 :  concrete constants / structures
    # ------------------------------------------------------------------ #

    # ----------  name helper  ----------

    def plan_declarations(self, root):
        """
        First pass: find, for every AMR variable, the *shallowest*
        node (nearest-to-root) that dominates all occurrences.
        The result is stored in self.decl_plan[var]['level'].
        """
        self.decl_plan: dict[str, dict] = {}

        # For each var we keep the *current* LCA path (root … lca_node)
        lca_paths:  dict[str, List["AMRNode"]] = {}
        meta_nodes: dict[str, "AMRNode"]       = {}   # first node we met → metas/type
        visited_nodes: set["AMRNode"] = set()

        def walk(node: "AMRNode", path: List["AMRNode"]):
            """DFS through the graph, updating the running LCA per var."""
            var = node.var_name
            full_path = path + [node]           # path to *this* occurrence (root … node)

            if var not in lca_paths:
                # First time we see the var – initialise its path and stash meta info
                lca_paths[var] = full_path
                meta_nodes[var] = node
            else:
                # Compute the common prefix of the existing LCA path
                # and this new occurrence's path ⇒ new (possibly shorter) LCA path
                lca = []
                for n1, n2 in zip(lca_paths[var], full_path):
                    if n1 is n2:
                        lca.append(n1)
                    else:
                        break
                lca_paths[var] = lca           # update running LCA

            # Recurse on children if not visited
            # Only recurse if we haven’t seen this node before
            if node in visited_nodes:
                return
            visited_nodes.add(node)

            for child, _ in node.children.items():
                walk(child, full_path)

        # Kick off the DFS.  Root is depth = 1 by convention
        walk(root, [])
        print('+'*80)
        print('lca_paths: ', lca_paths)
        # Finalise decl_plan
        for var, lca_path in lca_paths.items():
            lca_node = lca_path[-1] if lca_path else root
            level    = len(lca_path) or 1       # depth counting root as 1
            template = meta_nodes[var]          # first-seen node gives us meta

            # Work out quantifier once
            quant = '∃'
            if template.meta.get('definite') == '+':
                quant = 'const'
            elif template.meta.get('universal'):
                quant = '∀'
            elif var.startswith('attr-'):
                quant = 'const'
                lca_node = template

            self.decl_plan[var] = {
                'type'      : self._pred_sig.get(var, self._node_norm_name(meta_nodes[var])),
                'quantifier': quant,
                'node'      : lca_node,
                'level'     : level
            }

        # create a by level dictionary for lifting declarations 
        self.decl_dependents = defaultdict(list)
        for v, entry in self.decl_plan.items():
            decl_node = entry['node']
            original_node = meta_nodes[v]

            if decl_node is not original_node:
                decl_var = decl_node.var_name
                self.decl_dependents[decl_var].append(original_node)

            # if entry['node'].var_name != v:
            #     # lca not itself
            #     print(meta_nodes[v].var_name, '|', meta_nodes[v].text, '|', meta_nodes[v].type)
            #     lca_var = entry['node'].var_name
            #     self.decl_dependents[lca_var] += [meta_nodes[v]]
        print('+'*80)
        print({v: [n.var_name for n in ns] for v, ns in self.decl_dependents.items()})
        print('+'*80)
        print(self.decl_plan)
        print('+'*80)


    def special_ent_declare(self, c, root, role_id, indent, let_bindings, prop_lines):
        all_roles = self.ent.get(c.text)
        filled_roles = {ent_field.role: 'none' for ent_field in all_roles}
        for cc, crel_ in c.children.items():
            if crel_ in filled_roles:
                if cc.meta['category'] in ['float', 'int']:
                    filled_roles[crel_] = cc.text
                else:
                    filled_roles[crel_] = f'"{cc.text}"'
        spec_ent_fields = []
        for fname, fvalue in filled_roles.items():
            if fvalue != 'none':
                spec_ent_fields.append(f'{fname[1:]} := some {fvalue}')
            else:
                spec_ent_fields.append(f'{fname[1:]} := none')

        # spec_ent_fields = [f'{fname[1:]} := some {fvalue}' for fname, fvalue in filled_roles.items() if fvalue != 'none' else f'{fname[1:]} := none']
        fields_assignment = ", ".join(spec_ent_fields)
        c_type = c.text.replace('-', '_')+'_'+c.var_name
        let_bindings.append(f"{indent}let {c.var_name} : {c_type} := " + "{ " + fields_assignment + " }")
        # let_bindings.append(f"{indent}let {root.var_name}_{c.var_name} := {role_name.lower()} {root.var_name} {c.var_name}")
        # prop_lines.append(f"{indent}{role_name.upper()} {role_id} {root.var_name} {c.var_name}")
        self.let_bound_vars.add(c.var_name)


    def _quantify(self, node, declared_vars, quant_lines, prop_lines, indent, quantifier):
        quant_lines.append(f"{indent}{quantifier} {node.var_name} : {self._pred_sig.get(node.var_name, self._node_norm_name(node))}")
        if self._pred_sig.get(node.var_name, self._node_norm_name(node)) in ['Entity', 'Prep']:
            prop_lines.append(f'{indent}{node.var_name}.name = "{node.text}"')
        declared_vars.add(node.var_name)        

    def _try_quantify(self, node, declared_vars, quant_lines, prop_lines, indent, quantifier):
        if node.var_name not in declared_vars and node.var_name not in self.let_bound_vars:
            self._quantify(node, declared_vars, quant_lines, prop_lines, indent, quantifier)

    def _role_name_retrieve(self, roles_dict, rel):
        # consult pb see which semantic role this is defining
        role_name = None
        m = re.match(r":arg(\d+)$", rel, re.I)   #  ← changed line
        if m:
            # rel_idx = m.group(1)
            rel_idx = rel[1:]
            # 1. pb roles or special roles
            role_name = roles_dict.get(rel_idx, None)
            
            if role_name == None:
                # 3. must be out of the scope of both inventory, need to construct from AMR directly
                role_name = f'ROLE_{rel_idx}'
        elif rel.lower() == ":content":
            role_name = roles_dict.get('1', None)
            if role_name == None:
                role_name = "CONTENT"
        elif rel in NON_CORE_EDGES:
            role_name = NON_CORE_EDGES[rel]
        elif rel.lower().startswith(':prep-'):
            print('starts with prep:', rel.lower())
            role_name = f'Prep{rel[6:].capitalize()}'
            print('role_name: ', role_name)
        else:
            role_name = rel[1:].capitalize()

        return role_name

    def _let_bound(self, node, declared_vars, let_bindings, indent):
        if node.meta['category'] in ['predicate', 'compound-ent']:
            # arg_str = self._role_name_retrieve()
            realized_args = self.struct_arg_order.get(node.var_name)
            args_str = ", ".join([f"{arg_idx}:={arg_var}"for arg_idx, arg_var in realized_args.items()])
            let_line = CONST_LET_DECLARE_STRUCT_TMPL.format(indent=indent, concept=node.var_name, type=self._pred_sig.get(node.var_name, self._node_norm_name(node)), arg_str=args_str)
        elif node.meta['category'] == 'special-entity':
            self.special_ent_declare(c, root, role_id, indent, let_bindings, prop_lines)
        else:
            let_line = CONST_LET_DECLARE_ENTITY_TMPL.format(indent=indent, concept=node.var_name, type=self._pred_sig.get(node.var_name, self._node_norm_name(node)), concept_name=node.text)
        let_bindings.append(let_line)
        self.let_bound_vars.add(node.var_name)

    def _try_let_bound(self, node, declared_vars, let_bindings, indent):
        if node.var_name not in declared_vars and node.var_name not in self.let_bound_vars:
            self._let_bound(node, declared_vars, let_bindings, indent)

    def _declare_variable(self, meta, node, declared_vars, let_bindings, quant_lines, prop_lines, indent):
        # Lift it to this level
        if meta['quantifier'] == 'const':
            self._try_let_bound(node, declared_vars, let_bindings, indent)
        else:

            self._try_quantify(node, declared_vars, quant_lines, prop_lines, indent, meta['quantifier'])
        declared_vars.add(node.var_name)

    def _handles_lifted_declare(self, root, declared_vars, let_bindings, quant_lines, prop_lines, indent):
        if len(self.decl_dependents[root.var_name]) > 0:
            # need to declare lifted ones
            print('lift method')
            for dep_n in self.decl_dependents[root.var_name]:
                # if dep_n.var_name not in declared_vars and dep_n.var_name not in self.let_bound_vars:
                meta = self.decl_plan.get(dep_n.var_name)
                print('dep_n.var_name: ', dep_n.var_name, '| dep_n.text: ', dep_n.text, '| meta: ', meta)
                print('before: ')
                print('prop_lines: ', prop_lines)
                print('let_bindings: ', let_bindings)
                print('quant_lines: ', quant_lines)
                if meta['quantifier'] == 'const':
                    self._let_bound(dep_n, declared_vars, let_bindings, indent)
                else:
                    self._quantify(dep_n, declared_vars, quant_lines, prop_lines, indent, meta['quantifier'])
                declared_vars.add(dep_n.var_name)
                # self._declare_variable(meta, dep_n, declared_vars, let_bindings, quant_lines, prop_lines, indent)
                print('after:')
                print('prop_lines: ', prop_lines)
                print('let_bindings: ', let_bindings)
                print('quant_lines: ', quant_lines)

    def _rerank_const_in_lets(self, let_bindings):
        new_let_bindings = []
        for let_binding in let_bindings:
            if '{' in let_binding or '⟨' in let_binding:
                new_let_bindings.insert(0, let_binding)
            else:
                new_let_bindings.append(let_binding)
        return new_let_bindings

    def _declare_category(self, c, root, role_id, role_name, indent, let_bindings, prop_lines, declared_vars, inversed_role):
        c_cat = c.meta['category']
        child_pred_var_tuple = None
        role_filler_flag = False
        if c_cat in ['special-entity']:
            self.special_ent_declare(c, root, role_id, indent, let_bindings, prop_lines)
            print('special-entity: ', c.text, '|', c.var_name)
            child_pred_var_tuple = (c.text.replace('-', '_'), c.var_name)
        elif c_cat == 'name':
            name_str = "_".join([cc.text.replace('"', '') for cc, _ in c.children.items()])
            # self.regular_let_prop_declare(inversed_role, root.var_name, f'"{name_str}"', indent, role_id, role_name, let_bindings, prop_lines)
            print('name: ', c.text, '|', c.var_name)
            child_pred_var_tuple = ("String", f'"{name_str}"')

        elif c_cat in ['float', 'int']:

            print('num: ', c.text, '|', c.var_name)
            child_pred_var_tuple = (c_cat.capitalize(), c.text)
        elif c_cat == 'attribute':
            
            print('attr: ', c.text, '|', c.var_name)
            child_pred_var_tuple = ("String", f'"{c.text}"')

        elif c_cat in ['term-mod']:
            # self.regular_let_prop_declare(inversed_role, root.var_name, f'"{c.text}"', indent, role_id, role_name, let_bindings, prop_lines)
            print('term-mod: ', c.text, '|', c.var_name)
            child_pred_var_tuple = ("String", f'"{c.text}"')
        else:
            if self._pred_sig.get(c.var_name, None) == "String":

                # self.regular_let_prop_declare(inversed_role, root.var_name, f'"{c.text}"', indent, role_id, role_name, let_bindings, prop_lines)
                print('term string: ', c.text, '|', c.var_name)
                declared_vars.add(c.var_name)
                child_pred_var_tuple = ("String", f'"{c.text}"')
            else:
                # self.regular_let_prop_declare(inversed_role, root.var_name, c.var_name, indent, role_id, role_name, let_bindings, prop_lines)
                # role_filler_nodes.append(c)
                role_filler_flag = True
                print('regular node: ', c.text, '|', c.var_name)
                child_pred_var_tuple = (c.text.replace('-', '_'), c.var_name)
        return child_pred_var_tuple, role_filler_flag

    def _structure_pred_prop(self, root, indent):
        if self._pred_sig.get(root.var_name, self._node_norm_name(root)) not in ['Entity', 'String', 'Float', 'Int', 'Prep']:

            # args_str = ", ".join([f'{rel[1:].lower()} := some {arg_tuple[1]}' for rel, arg_tuple in children_types.items()])
            print('in fields_assignment: ', root.var_name)
            print('self.struct_arg_order.get(root.var_name): ', self.struct_arg_order.get(root.var_name))

            args_str = ", ".join([f'{rel} := {c_var}' for rel, c_var in self.struct_arg_order.get(root.var_name, {}).items()])
            print('args_str:', args_str)
            root_prop_line = QUANT_DECLARE_STRUCT_TMPL.format(indent=indent, pred_var=root.var_name, arg_str=args_str)
            return root_prop_line
        else:
            return None

    def _mk_event_axiom(self, root, level=1, root_named=False, declared_vars=None, visited_nodes=None):
            
        if root in visited_nodes:
            return ""  # Prevent infinite loop on re-entrance
        visited_nodes.add(root)
        indent = ' ' * level
        next_indent = ' ' * (level + 2)
        c_quant = {}
        let_bindings = []
        prop_lines = []
        noncore_prop_lines = []
        subformulas = []
        quant_lines = []

        root_cat = root.meta['category']
        polarity_neg_flag = False
        print('-'*80)
        print('mk_event_axiom call, root.var_name: ', root.var_name)
        # 1. Declare root quantifier at current level
        # if root.var_name not in declared_vars and root.var_name not in self.let_bound_vars and root_cat not in ['compound-event', 'compound-ent', 'inter-mod', 'inter-prep-mod']:
        if root.var_name not in declared_vars:
            # quant = '∀' if root.meta.get('universal') else '∃'
            meta = self.decl_plan.get(root.var_name)
            if meta['quantifier'] == 'const':
                self._try_let_bound(root, declared_vars, let_bindings, indent)
            else:
                self._try_quantify(root, declared_vars, quant_lines, prop_lines, indent, meta['quantifier'])
            print(indent+'1. root.var_name: ', root.var_name, 'meta: ', meta)

        # roles_dict = self._role_dict_retrieve(root)
        roles_dict = self.struct_arg_order.get(root.var_name, {})
        print('roles_dict: ', roles_dict)


        role_filler_nodes = []
        print('2. regular children')
        # step 2: Regular children
        # do special entity check and stop further calls over children
        children_types = {}
        for c, rel_ in root.children.items():
            rel = rel_.lower().strip()

            if rel == ":quant" and c.text in UNIVERSAL_QUANR:
                # universal quantifier
                continue

            if rel in [':plural', ':definite']:
                # marker roles , not need to translate 
                continue 

            if rel == ':polarity' and c.text == '-':    
                polarity_neg_flag = True
                print('polarity_neg_flag = True')
                print('rel: ', rel)
                continue

            if rel == ':content-of':
                rel = ':arg1-of'


                # ----------------------------------------
            # handle inversed role edge
            role_name = None
            # inversed_role flag is for later ordering decisions
            inversed_role = False
            if re.match(r':arg\d-of', rel):
                inversed_role = True
            elif rel.endswith('-of') and rel not in OF_SPECIAL_ROLE:
                inversed_role = True
            else:
                inversed_role = False
            
            if role_name is None:
                # polarity_neg_flag = True
                role_name = rel[1:]

            print('inversed_role: ', inversed_role, '|', role_name, '|', rel)
            if role_name == "example":
                role_name = "examples"
            # if not re.match(r'op\d', role_name):
            self.M.roles_inventory.add(role_name.upper())
            role_id = f"{root.var_name}_{c.var_name}"
            c_cat = c.meta['category']

            # self._check_terminal_declaration(inversed_role, indent, root, c, role_id, role_name, let_bindings, prop_lines, inter_mod_nodes, role_filler_nodes)
            # handle single negation of the child
            if len(c.children) == 1 and list(c.children.items())[0][1] == ':polarity' and list(c.children.items())[0][0].text == '-':
                polarity_neg_flag = True 

            print('c_cat: ', c_cat)
            filler_flag = False
            # construct noncore assertion
            if not (rel.startswith(':arg') or root.text in CONNECTOR or rel in INDICATOR_NONCORE_RELS):
                # this must be a non-core relation, we directly declare this role with the root node as predicate through axiom invoking. 
                child_pred_var_tuple, filler_flag = self._declare_category(c, root, role_id, role_name, indent, let_bindings, prop_lines, declared_vars, inversed_role)
                
                # declare axiom predicate
                modifier_var = c.var_name
                modifiee_var = root.var_name

                root_var = root.var_name.replace('-', '_')
                c_var = c.var_name.replace('-', '_')
                norm_rel = NON_CORE_EDGES.get(rel, rel[1:].replace('-', ''))
                role_axiom_name = f'{root_var}_{norm_rel}_{c_var}'


                if child_pred_var_tuple[0] in ["String", "Float", "Int"]:
                    modifier_var = child_pred_var_tuple[1]

                prop_line = NON_CORE_ROLE_PRED_TMPL.format(indent=indent, role_name=role_axiom_name, modifiee_var=modifiee_var, modifier_var=modifier_var)
                if inversed_role:
                    norm_rel = NON_CORE_EDGES.get(rel[:-3], rel[1:-3].replace('-', ''))
                    role_axiom_name = f'{c_var}_{norm_rel}_{root_var}'
                    prop_line = NON_CORE_ROLE_PRED_TMPL.format(indent=indent, role_name=role_axiom_name, modifiee_var=modifier_var, modifier_var=modifiee_var)

                noncore_prop_lines.append(prop_line)

            else:
                children_types[rel_], filler_flag = self._declare_category(c, root, role_id, role_name, indent, let_bindings, prop_lines, declared_vars, inversed_role)
            print('c.var_name: ', c.var_name, ' | c.text: ', c.text, 'filler_flag: ', filler_flag)
            if filler_flag:
                role_filler_nodes.append(c)
            
        # 3. Declare child variables at this level (lift from deeper levels if needed)
        print('role_filler_nodes: ', [n.var_name for n in role_filler_nodes])
        print('---------bound loop----------')
        for c in role_filler_nodes:
            v = c.var_name
            print('var_name: ', v)
            if v in declared_vars or v in self.let_bound_vars:
                print('in declared_vars or self.let_bound_vars, skip')
                continue

            meta = self.decl_plan.get(v)
            if meta['level'] >= level:
               
                self._declare_variable(meta, c, declared_vars, let_bindings, quant_lines, prop_lines, indent)
        
        self._handles_lifted_declare(root, declared_vars, let_bindings, quant_lines, prop_lines, indent)

        # finally declare the root structure if not purely noncore
        print('right before fields_assignment, ', root.var_name, ' | ', root.text)
        root_prop_line = self._structure_pred_prop(root, indent)
        if root_prop_line:
            prop_lines.append(root_prop_line)
        # 4. Recurse into children for logical body (not for variable declarations)
        for c in role_filler_nodes :
            if len(c.children) > 0:
                print('recurse into children, c: ', c.var_name, '|', c.text)
                sub = self._mk_event_axiom(c, level=level + 1, root_named=True, declared_vars=declared_vars, visited_nodes=visited_nodes)
                if sub.strip():
                    subformulas.append(f"{indent}(\n{sub}\n{indent})")
            else:
                c_prop_line = self._structure_pred_prop(c, indent)
                if c_prop_line:
                    prop_lines.append(c_prop_line)

            
        # self._handles_lifted_declare(root, declared_vars, let_bindings, quant_lines, prop_lines, indent)


        # Final block structure
        quant_block = ",\n".join(quant_lines)
        reranked_lets = self._rerank_const_in_lets(let_bindings)
        let_block = "\n".join(reranked_lets)
        prop_block = " ∧\n".join(prop_lines + noncore_prop_lines + subformulas)

        

        if not (let_block or prop_block or subformulas):
            print('quant_lines: ', quant_lines)
            print('let_block: ', let_block, '| prop_block: ', prop_block, '|subformulas: ', subformulas)
            return ""
        # Polarity
        print('polarity_neg_flag check: ', polarity_neg_flag)
        print('root.var_name: ', root.var_name, '|root.text: ', root.text)
        if polarity_neg_flag:
            prop_block = f"{indent}¬ (\n{prop_block}\n{indent})"

        # Combine all blocks with appropriate spacing
        all_lines = []
        if quant_block:
            all_lines.append(quant_block + ",")
        if let_block:
            all_lines.append(let_block)
        all_lines.append(prop_block)
        # if polarity_neg_flag:
        #     all_lines_block = "\n".join(all_lines)
        #     return f"{indent}¬ (\n{all_lines_block}\n{indent})"

        return "\n".join(all_lines)

    def _emit_axioms(self, root):
        self.plan_declarations(root)
        declared_vars = set()
        visited_nodes = set()
        print('in _emit_axioms: self.decl_dependents: ', self.decl_dependents)
        ax_body = self._mk_event_axiom(root, level=1, root_named=False, declared_vars=declared_vars, visited_nodes=visited_nodes)
        self.M.axioms.append(f"axiom ax_{root.var_name}:\n{ax_body}")


    def translate_as_prop(self, amr_str: str, sid: str = '', reuse_module: LeanModule | None = None) -> Tuple[str, str]:
        """
        Returns (prop_body_str, root_var_name) for this AMR.
        Side-effect: updates self.M (shared or fresh) with any newly needed boilerplate.
        It DOES NOT append into self.M.axioms (so the caller can decide axiom/lemma/theorem).
        """
        tree = PenmanAMRTree(amr_str, remove_alignmark=True)
        if sid:
            tree.add_sent_mark(sid)
        self._filter_i(tree.node_dict)
        self._prop_cache = {}

        # If a shared module is provided, use it so boilerplate accumulates across sentences.
        if reuse_module is not None:
            self.M = reuse_module
        else:
            # fresh (single-sentence) behavior
            self.M = LeanModule(self.import_semantic_gadgets)

        # --- MUST happen first (same as the translate method) ---
        self.struct_arg_order = {}
        self._skip_instantiation = set()
        self._pred_sig = {}
        self.noncore_roles = set()

        self._annotate_meta(tree.node_dict)
        self.node_deps, depth, self.noncore_roles = self._annotate_node_category(tree)
        self.node_order = topo_sort_amr(self.node_deps, depth)
        self.node_order.reverse()
        self._annotate_attributives(tree.node_dict)

        # Emit all types/structs/non-core declarations into self.M (shared across sentences)
        self._emit_types()

        # Build the proposition body but DO NOT push an axiom
        self.plan_declarations(tree.top)
        declared_vars = set()
        visited_nodes = set()
        body = self._mk_event_axiom(tree.top, level=1, root_named=False,
                                    declared_vars=declared_vars, visited_nodes=visited_nodes)
        return body, tree.top.var_name

class AMR2LeanSequenceTranslator:
    """
    Orchestrates multi-sentence translation:
    - preserves input order
    - shares boilerplate (inductives/structs/non-core axioms) across sentences
    - emits statements as axiom/lemma/theorem, with optional negation
    """
    def __init__(self, propbank_catalog: PropbankCatalogue, import_semantic_gadgets: bool = False):
        self.pb = propbank_catalog
        self.import_semantic_gadgets = import_semantic_gadgets
        self.M = LeanModule(import_semantic_gadgets=import_semantic_gadgets)
        self.counter = 0

    def add(self, amr_str: str, kind: str = 'axiom', negate: bool = False, sid: str = '', name: str | None = None):
        """
        kind ∈ {'axiom','lemma','theorem'}
        negate: wrap body with ¬( ... ) for 'negated theorem' use-cases
        sid: optional sentence id for stable naming
        name: override the default generated identifier
        """
        t = AMR2LeanTranslator(propbank_catelog=self.pb, import_semantic_gadgets=self.import_semantic_gadgets)
        # Share the same LeanModule so boilerplate accumulates
        body, root_var = t.translate_as_prop(amr_str, sid=sid, reuse_module=self.M)

        # Create a stable ordered name if not provided
        self.counter += 1
        base = f"{sid}_" if sid else ""
        default_name = {
            'axiom'   : f"ax_{base}{root_var}",
            'lemma'   : f"lem_{base}{root_var}",
            'theorem' : f"thm_{base}{root_var}",
        }.get(kind, f"stmt_{base}{root_var}")
        stmt_name = name or default_name

        # Store the statement in order
        self.M.add_statement(kind=kind, name=stmt_name, body=body, negate=negate)

    def render(self) -> str:
        """Boilerplate first, then the statements in the exact order added."""
        return self.M.render_sequence()
# ---------------------------------------------------------------------------
# Script entry‑point
# ---------------------------------------------------------------------------
if __name__ == "__main__":
    
    # demo_amr = r"""
    # (c / close-10
    #    :ARG1 (i / i)
    #    :ARG2 (p / point
    #             :mod (b / break-01
    #                     :ARG1 i))
    #    :degree (v / very))
    # """
    pb_catalog = PropbankCatalogue("/Users/jonzcai/Documents/ComputerScience/NLP/data/datasets/propbank-frames/frames/")
    t = AMR2LeanTranslator(pb_catalog)
    # print(t.translate(demo_amr))


    # demo_amr3 = r"""
    # (d / drive-01
    #      :arg0 (p / person)
    #      :arg1 (c / car)
    #      :source (s / city :name (n / name :op1 "Denver"))
    #      :destination (l / city :name (n2 / name :op1 "Boulder")))
    # """

    # print(t.translate(demo_amr2))

    # demo_amr3 = r"""
    # (k / know-01~3
    #    :ARG0 (i / i~0)
    #    :ARG1 (o / or~7
    #             :op1 (t / thing~6
    #                     :ARG1-of (d / do-02~6
    #                                 :ARG0 i))
    #             :op2 (t2 / thing~8
    #                      :manner-of (h / help-01~10
    #                                    :ARG0 i
    #                                    :ARG1 (h2 / happy-01~13
    #                                              :ARG1 i
    #                                              :mod (a / again~14))
    #                                    :ARG2 i)))
    #    :degree (r / really~1)
    #    :polarity -~2)
    # """

    demo_amr3 = r"""
    (l / love-01~1
       :ARG0 (i / i~0)
       :ARG1 (g / girl~4
                :ARG1-of (s / same-01~3))
       :duration (a / about~6
                    :op1 (t / temporal-quantity~7,8
                            :quant 6~7,8
                            :unit (y / year~7,8))))
    """

    # demo_amr3 = r"""
    # (l / learn-01~1
    #    :ARG0 (y / you~1)
    #    :ARG1 (s / skill~4
    #             :ARG1-of (n / new-02~5)
    #             :ARG1-of (e / exemplify-01~3
    #                         :ARG0 (o / or~13
    #                                  :op1 (p / play-11~7
    #                                          :ARG2 (i / instrument~9))
    #                                  :op2 (d / draw-01~10)
    #                                  :op3 (t / try-01~11
    #                                          :ARG1 (s2 / sport~14
    #                                                    :ARG1-of (n2 / new-02~17
    #                                                                 :definite -)))
    #                                  :op4 (d2 / design-01~16
    #                                           :ARG1 (w / web~15))
    #                                  :op5 (e2 / et-cetera~10
    #                                           :definite -))
    #                         :content-of (p2 / possible-01~3))
    #             :definite -)
    #    :mode (i2 / imperative~1))
    # """

    # demo_amr3 = r"""
    # (a / and~10
    #    :op1 (f / find-01~0
    #            :ARG0 (y / you~3)
    #            :ARG1 (a2 / activity-06~2
    #                      :ARG1-of (l / like-01~4
    #                                  :ARG0 y)
    #                      :definite -)
    #            :mode (i / imperative~0))
    #    :op2 (s / set-02~5
    #            :ARG0 y
    #            :ARG1 (g / goal~7
    #                     :quant some)
    #            :mode (i2 / imperative~5))
    #    :op3 (s3 / stick-01~8,9
    #             :ARG0 y
    #             :ARG2 g
    #             :mode (i3 / imperative~8,9
    #                       :plural +)))
    # """

#     demo_amr3 = r'''
# (p / possible-01~0
#    :content (m / make-01~1
#                :ARG0 (y / you~1)
#                :ARG1 (p2 / playlist~4
#                          :ARG1-of (n / new-01~3)
#                          :consist-of (m2 / music~11
#                                          :ARG1-of (h / happy-01~10)
#                                          :example (a / and~12
#                                                      :op1 (m3 / music~17
#                                                               :ARG1-of (a2 / author-01~16
#                                                                            :ARG0 (o / organization~15
#                                                                                     :name (n3 / name~15
#                                                                                               :op1 "Fleetwood"~15
#                                                                                               :op2 "Mac"~15)))
#                                                               :name (n2 / name~17
#                                                                         :op1 "Don't"~17
#                                                                         :op2 "Stop"~17))
#                                                      :op2 (e / et-cetera~13)))
#                          :definite -)
#                :ARG2-of (s / start-01~8
#                            :ARG0 y
#                            :plural +)
#                :medium (p3 / product~6
#                            :name (n4 / name~6
#                                      :op1 "iTunes"~6))))
# #     '''

#     demo_amr3 = r'''
# (s9h / have-condition-91~28
#      :ARG1 (s9b / break-down-11~27
#                 :ARG0 (s9i / i~7)
#                 :manner (s9j / just~26))
#      :ARG2 (s9c / come-on-08~5,6
#                 :ARG1 (s9o / or~16
#                            :op1 (s9s / song~1
#                                      :domain (s9s2 / song~12
#                                                    :location (s9w / world~15)
#                                                    :mod (s9e / every~11
#                                                              :degree (s9p / pretty-much~23)))
#                                      :topic (s9l / love~3)
#                                      :definite -)
#                            :op2 (s9s3 / song~18
#                                       :ARG0-of (s9r / remind-01~20
#                                                     :ARG1 (s9s4 / she~25)
#                                                     :ARG2 s9i
#                                                     :definite -))
#                            :definite +)
#                 :medium (s9p2 / product~8
#                               :name (s9n / name~8
#                                          :op1 "iTunes"~8)
#                               :poss s9i)))

#     '''
    demo_amr3 = r'''
(i / imaginary
    :polarity -
    :domain (n / number
        :ARG1-of (r / real-04)))
    '''
    leancode = t.translate(demo_amr3)
    print(leancode)
    # new_leancode = reorder_choice_blocks(leancode)

    # print(new_leancode)