from __future__ import annotations
import re, textwrap, itertools
from collections import defaultdict
from typing import Dict, List, Tuple, Set 


from propbank_interface import PropbankCatalogue, Roleset
from amr_special_frames import AMRSpecialFrames
from amr_toolbox.AMRgraph import PenmanAMRTree, AMRNode, name_collapser
from amr_special_entities import AMRSpecialEntities
from amr_special_preps import PrepInventory

from collections import deque
import copy 
import math 
from lean_snippets2 import *
from amr_patterns import *
from utils import *


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
        for synset in synsets:
            if synset.name().split('.')[0] == lemma.lower() and synset.pos() != 'n':
                return True

    return False
# --------------------------------------------------------------------------- #
#  Main Lean module container
# --------------------------------------------------------------------------- #
class LeanModule:
    def __init__(self, import_semantic_gadgets=False):
        self.inductives : Dict[str,str] = {}
        self.structs    : Dict[str,str] = {}
        self.instances  : List[str] = []
        self.exist_axioms : List[str] = []      # new: quantifier axioms
        self.axioms     : List[str] = []
        self.noncore_preds : Dict[str,str] = {}   # edge → template line
        self.noncore_axioms: List[str] = []
        self.import_semantic_gadgets = import_semantic_gadgets
        self.roles_inventory : Set[str] = set()

    def render(self) -> str:
        if self.import_semantic_gadgets:
            parts = [
                "import AMRGadgets",
                *self.inductives.values(),
                "", *self.structs.values(),
                # "", *self.instances,
                # "", *self.noncore_preds.values(),
                # "", *self.exist_axioms,             # quantifier axioms before events
                "", *self.axioms,
                
                # "", *self.noncore_axioms
                ]
        else:            
            parts = [
                ROLE_PREDS.format(roles=", ".join(list(self.roles_inventory))),
                "",
                *self.inductives.values(),
                "", *self.structs.values(),
                # "", *self.instances,
                # "", *self.noncore_preds.values(),
                # "", *self.exist_axioms,             # quantifier axioms before events
                "", *self.axioms,
                
                # "", *self.noncore_axioms]
                ]
        return "\n\n".join(parts)

MOD_CACHE = set()   # keep at module level

# --------------------------------------------------------------------------- #
#  Translator
# --------------------------------------------------------------------------- #
default_propbank_root = "/Users/jonzcai/Documents/ComputerScience/NLP/data/datasets/propbank-frames/frames/"
pb_catalog = PropbankCatalogue(default_propbank_root)
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
                # cn = next((k for k, v in node.children.items() if v == ":op1"), None)
                
                # if SENSE_RE.search(cn.text):
                #     return "compound-event"
                # else:
                #     return "compound-ent"
                return "compound-e"
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
            return "attribute"

        # Rule 5: Terminal node(non-attribute)
        if not node.children:
            if _is_noun_lemma(node.text):
                return "term-noun"
            elif _is_mod(node.text):
                return "term-mod"
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
    def translate(self, amr_str:str) -> str:
        tree = PenmanAMRTree(amr_str, remove_alignmark=True)
        # print(amr_str)
        print([(var_name, n.var_name, n.text) for var_name, n in tree.node_dict.items()])
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
        print('self.node_order: ', [node.var_name for node in self.node_order])
        print('-'*80)
        self._annotate_attributives(tree.node_dict)

        # Now every node has a .meta dict, so these are safe:
        self._emit_types(tree.node_dict)
        
        # self._emit_instances(tree.node_dict)
        # self._emit_role_assign(tree.top)
        # self._emit_noncore(self.noncore_roles)
        # -- Phase B: build role predicate axioms
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
            # 9 universal quantifier
            if has_any_child(n, ":quant", UNIVERSAL_QUANR) :
                n.meta["universal"] = True
            if has_child(n, ":quant", "some"):
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
                    deps[node].add(node)
                
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
    #  Phase 1 :  inductive & structure boiler-plate
    # ------------------------------------------------------------------ #
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

    def _emit_types(self, nodes:Dict[str,AMRNode]):
        etc_nodes = []
        for n in nodes.values():
            print('-----------emit-types------------')

            node_cat = n.meta['category']
            print('n.var_name: ', n.var_name, '|n.text: ', n.text, '|ncat: ', node_cat)
            # ---------- connector lemmas ----------
            if n.text.strip() == "et-cetera":
                etc_nodes.append(n)
                print('etc n.text: ', n.text)


            # if n.meta['category'].startswith("compound"):
            #     # tname = CONNECTOR[n.text]
            #     event_or_entity = n.meta['category'].split()[-1]
                
            #     self._pred_sig[n.var_name] = f'Compound{event_or_entity.capitalize()}'
            if node_cat == 'compound-e':

                # self._pred_sig[n.var_name] = f"Compound{event_or_entity}"
                self._pred_sig[n.var_name] = "Connector"

                continue

            # for all predicate nodes, we generate structures to hold data
            if node_cat == 'predicate' or node_cat == 'special-frame':
                parts = n.text.rsplit('-', 1)
                lemma, sense = parts + [''] * (2 - len(parts))
                key = f"{lemma.replace('-','_')}_{sense}" 
                
                self._pred_sig[n.var_name] = "Event"
          

            else:
                # not a predicates or special frame, then, it could be noun nodes or special entity node or prep node
                norm_name = n.text.replace('-', '_')
                
                if node_cat == 'special-entity':
                    # --- declare fixed-field structure once
                    spec_ent = self.ent.get(n.text)

                    if norm_name not in self.M.structs:
                        self.M.structs[norm_name] = self._mk_spec_entity_struct(norm_name, spec_ent)
                        self.node_type[n.var_name] = norm_name
                    self._pred_sig[n.var_name] = norm_name

                elif node_cat == 'attribute':
                    if _is_number(n.text):
                        # only the most primative category of node can specify the type signature immediately.
                        self._pred_sig[n.var_name] = "Float"
                    else:
                        self._pred_sig[n.var_name] = "String"
                    continue
                elif node_cat in ['term-noun', 'inter-noun', 'term-other']:
                    self._pred_sig[n.var_name] = "Entity"
                elif node_cat in ['inter-prep-mod', 'inter-mod']:
                    self._pred_sig[n.var_name] = "Event"
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

    def _mk_pb_struct(self, rs:Roleset) -> str:
        # print('rs.roles: ', [(r.idx, r.fun) for r in rs.roles])
        roles = sorted(rs.roles, key=lambda r: int(r.idx))   # 0,1,2,…

        tparams = " ".join(f"(t{i+1} : Type)" for i,_ in enumerate(roles))

        fields  = "\n".join(
            f"  ({r.fun.lower()} : t{j+1}) -- arg{r.idx}"
            for j, r in enumerate(roles)      # j is the *position*, not r.idx
        )
        rslemma = copy.deepcopy(rs.lemma)
        normed_lemma = rslemma.replace('-', '_')
        self.struct_arg_order[f"{normed_lemma}_{rs.sense}"] = {int(r.idx): r.fun for r in roles}
        # print('self.struct_arg_order: ', self.struct_arg_order)
        return STRUCTURE_TMPL.format(
            lemma=normed_lemma, sense=rs.sense,
            type_params=tparams, fields=fields)
    
    # ------------------------------------------------------------------ #
    #  generic struct for AMR-only frames  (non PropBank entry)
    # ------------------------------------------------------------------ #
    def _mk_generic_struct(self, pred: str, indices: set[int]) -> str:
        # sorted list, e.g. [1,2]  (arg1, arg2) since generic frames also use index arguments.
        # pred already replaced `-` with underscore
        idxs = sorted(indices)
        tparams = " ".join(f"(t{i+1} : Type)" for i,_ in enumerate(idxs))
        fields  = "\n".join(
            f"  (arg{idx} : t{j+1})"
            for j, idx in enumerate(idxs))

        self.struct_arg_order[pred] = {idx: idx for idx in idxs}
        return GENERIC_STRUCT_TMPL.format(
            name=pred, type_params=tparams, fields=fields)

    def _mk_spec_frame_struct(self, spec_frame_name: str, spec_roles: List[SpecialRole]) -> str:
        tparams = " ".join(f"(t{i+1} : Type)" for i in range(len(spec_roles)))
        fields  = "\n".join(
            f"  ({role.name} : t{tidx+1}) -- arg{role.idx}"
            for tidx, role in enumerate(spec_roles))
        self.struct_arg_order[spec_frame_name] = {int(r.idx):r.name for r in spec_roles}
        return  GENERIC_STRUCT_TMPL.format(
            name=spec_frame_name, type_params=tparams, fields=fields)

    # ------------------------------------------------------------------ #
    #  Phase 3 :  concrete constants / structures
    # ------------------------------------------------------------------ #

    # def _emit_instances(self, nodes: Dict[str, AMRNode]): 
    #     defs = []               # all pred-like defs

    #     print('in _emit_instances:')
    #     print('-'*80)
    #     # ── Phase 1: handle non-predicates (nouns, special entities, connectors) ──
    #     for n in self.node_order:
    #         print(f'n: {n.var_name} | {n.text} | ', n.meta)
            
    #         node_cat = n.meta['category']

    #         norm_name = n.text.replace("-", "_")

    #         # 1a) skip pure attributes, since they will be instantiated as values directly
    #         if node_cat in ['attribute', 'float', 'int'] :
    #             # both are treated as string for the value field of structure
    #             self._pred_sig[n.var_name] = "String" if node_cat == 'attribute' else node_cat.capitalize()
    #             continue

    #          # 1b) bare nouns / concepts
    #         if node_cat in ['term-noun', 'inter-noun']:
    #             self._pred_sig[n.var_name] = "Entity"
    #             defs.append(
    #                 INSTANCE_TMPL.format(
    #                     var=n.var_name,
    #                     type="Entity",
    #                     text=f"{n.text}") +
    #                 (" -- definite" if n.meta.get("definite")=="+"
    #                  else " -- indefinite / plural"))
    #             continue


    #         # 1c) prep-like internal nodes are similar but more primitive than special entity
    #         if node_cat == 'compound-e':
                
    #             self._pred_sig[n.var_name] = "Connector"

    #             children_vars = [cn.var_name for cn, rel in n.children.items()]
    #             child_vars_str = ", ".join(children_vars)

    #             connector_type_str = "And" if n.text == "and" else "Or"


    #             defs.append(
    #                 COMPOUND_TMPL.format(
    #                     name=n.var_name, 
    #                     ent_or_event=event_or_entity, 
    #                     connector_type=connector_type_str, 
    #                     e_list=child_vars_str)
    #                 )

    #             continue

    #         if node_cat in ['inter-prep-mod', 'inter-mod']:
    #             '''
    #             (...
    #                 :quant (a / about
    #                     :op1 (t / temporal-quantity
    #                         ...))
    #             )
    #             '''
    #             # like about node; will also be defined as special frame with a single op in it
    #             prep_type = node.text.lower()
    #             # attributive_head = node.meta['attributive_head']
    #             child_node_var = list(n.children.keys())[0].var_name
    #             child_node_type = self.node_type[child_node_var]
                
    #             # attr_hd_stru_name = self.node_type[attributive_head]
    #             inst_name = f'{prep_type}_{n.var_name}_{child_node_type}'
                
    #             type_sig_str = f'Modifier {child_node_type}'
                
    #             instans_str = list(n.children.keys())[0].var_name
    #             defs.append(
    #                 MODIFIER_INST_TMPL.format(name=inst_name, modifier_name=prep_type, modifyee=child_node_var)
    #                 )

    #             self._pred_sig[n.var_name] = type_sig_str
    #             continue
            
    #         if node_cat == 'special-entity':
    #             spec_ent = self.ent.get(n.text)
    #             kvs = []
    #             for f in spec_ent:
    #                 # f means field
    #                 # c is the child node of the special entity node that corresponds to the f field
    #                 c = next((c for c,r in n.children.items() if r==f.role), None)
    #                 if c is None:
    #                     # no fields of this special entity was provided from AMR
    #                     kvs.append(f"{f.name} := _")
    #                 elif f.ty == "String":
    #                     ctext = c.text.strip('"')
    #                     kvs.append(f'{f.name} := "{ctext}"')
    #                 else:
    #                     if c.meta['category'] in ['/', 'flat', 'int']:
    #                         kvs.append(f"{f.name} := {c.text}")
    #                     else:
    #                         kvs.append(f"{f.name} := {c.var_name}")

    #             rec = "{ " + ", ".join(kvs) + " }"
                
    #             # record its type sig exactly as its structure name
    #             self._pred_sig[n.var_name] = norm_name
    #             defs.append(
    #                 INSTANCE_TMPL.format(var=n.var_name,
    #                                      type=norm_name,
    #                                      text=rec))
    #             continue

    #         if node_cat in ['special-frame', 'predicate']:

    #             self._pred_sig[n.var_name] = "Event"

    #             defs.append(
    #                 INSTANCE_TMPL.format(var=n.var_name, type="Event", text=n.text))
       
    #     # -- Phase 5: glue together ---------------------------------------
    #     self.M.instances.extend(defs)

    def _role_dict_retrieve(self, root):
        root_cat = root.meta['category']
        roles_dict = {}
        if root_cat == 'predicate':
            roles = self.pb.get_roleset(root.text)
            if roles == None:
                roles_dict = DEFAULT_ROLES
            roles_dict = {role.idx: role.fun for role in roles.roles}
        elif root_cat == 'special-frame':
            roles = self.sf.get(root.text)
            roles_dict = {role.idx: role.name for role in roles}
        else:
            # must be a non-core concept
            print('non-core axiom, root.text: ', root.text)

        return roles_dict

    def _role_name_retrieve(self, roles_dict, rel):
        # consult pb see which semantic role this is defining
        role_name = None
        m = re.match(r":arg(\d+)$", rel, re.I)   #  ← changed line
        if m:
            rel_idx = m.group(1)
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


    def _collect_arg_info(self, pred_node:AMRNode):
        """
        Returns
            arg_pairs  : list[(idx_str, varname)]
            ty_params  : list[str]      -- in the same order
        with :content coerced to arg1, because in PropBank the 'content'
        argument is ARG1 and signals non-veridicality.
        """
        # def arg_value(node):
        #     if node.var_name.startswith('attr-'):
        #         return node.text
        #     else:
        #         return node.var_name

        arg_pairs, ty_params = [], []

        for child, rel in pred_node.children.items():
            m = re.match(r":arg(\d+)$", rel, re.I)   #  ← changed line
            if m:
                idx = m.group(1)                           # "0", "1", …
            elif rel == ":content":                       # our special rule
                idx = "1"                                 # maps to ARG1
            else:
                continue                                  # ignore modifiers etc.

            # arg_v = arg_value(child)
            arg_pairs.append((idx, child))
            ty_params.append(self._lean_type_of(child))


        # add this loop to pick up reversed roles
        for parent, rel in pred_node.parents.items():
            m = re.match(r":arg(\d+)-of", rel, re.I)
            if not m: continue
            idx = m.group(1)
            # arg_v = arg_value(parent)
            arg_pairs.append((idx, parent))
            ty_params.append(self._lean_type_of(parent))

        # keep Lean record fields deterministic
        arg_pairs.sort(key=lambda p: int(p[0]))
        return arg_pairs, ty_params

    def _lean_type_of(self, node: AMRNode) -> str:
        name = node.text.replace("-", "_")
        # 1) connector subgraphs stay as Choice Prop
        if node.text in CONNECTOR:
            return "(Choice Prop)"
        # 2) any predicate → saturated form
        if self._is_predicate(node):
            return f"({self._sat(name)})"
        # 3) any inductive (no params) → just name
        if name in self.M.inductives:
            return name
        # 4) any struct type (PropBank or special) → saturated with Units
        if name in self.struct_arg_order:
            # self._sat will pad missing slots with Unit
            return f"({self._sat(name)})"
        
        if _is_number(name):
            return "Float"
        # 5) everything else (e.g. bare nouns) → name
        return name
    
    def _sat(self, pred_name: str) -> str:
        idxs = self.struct_arg_order.get(pred_name)
        if idxs is None:
            return pred_name
        # pad every missing type‐param with "Unit"
        parts = []
        for _ in idxs:
            # look up a known concrete type (if you stored one), otherwise "Unit"
            # but since we now saturate **in** _lean_type_of, it's fine to always "Unit"
            parts.append("_")  
        # replace those "_" with actual Units?  or better, skip and do:
        return pred_name + " " + " ".join("Unit" for _ in idxs)
    
    # ----------  name helper  ----------
    def _name_literal(self, name_node: AMRNode) -> str | None:
        """
        For  (n / name :op1 "Denver" :op2 "International" …)
        return "Denver International …".  Returns None if pattern not matched.
        """
        if name_node.text != "name":
            return None
        parts = []
        for child, rel in name_node.children.items():
            if rel.startswith(":op"):
                # leaf nodes in your AMRs are attr-k / "String"
                parts.append(child.text.strip('"'))
        return " ".join(parts) if parts else None

    # ------------------------------------------------------------------ #
    #  Phase 4 : Event axioms  (∃-wrapping, modifiers, polarity)
    # ------------------------------------------------------------------ #
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
                'type'      : self._pred_sig[var],
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

    def _inverse_role_flip(self, inversed_role, pred, arg):
        return (arg, pred) if inversed_role else (pred, arg)

    def _mk_assign_lines(self, indent, role_id, pred_var, arg_var, role_name):
        let_line = ROLE_ASSIGN_STRU_TMPL.format(indent=indent, role_id=role_id, pred=pred_var, arg=arg_var, role=role_name.lower())
        prop_line = ROLE_ASSIGN_PRED_TMPL.format(indent=indent, role=role_name.upper(), role_id=role_id, pred=pred_var, arg=arg_var)
        return let_line, prop_line

    def regular_let_prop_declare(self, inversed_role, pred, arg, indent, role_id, role_name, let_bindings, prop_lines):
        pred_var, arg_var = self._inverse_role_flip(inversed_role, pred, arg)
        let_line, prop_line = self._mk_assign_lines(indent, role_id, pred_var, arg_var, role_name)
        print('='*30)
        print('regular_let_prop_declare: ')
        print(let_line)
        print(prop_line)
        print('='*30)
        let_bindings.append(let_line)
        prop_lines.append(prop_line)

    def special_ent_declare(self, c, root, role_id, role_name, indent, let_bindings, prop_lines):
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
        c_type = c.text.replace('-', '_')
        let_bindings.append(f"{indent}let {c.var_name} : {c_type} := " + "{ " + fields_assignment + " }")
        let_bindings.append(f"{indent}let {root.var_name}_{c.var_name} := {role_name.lower()} {root.var_name} {c.var_name}")
        prop_lines.append(f"{indent}{role_name.upper()} {role_id} {root.var_name} {c.var_name}")
        self.let_bound_vars.add(c.var_name)

    def _quantify(self, node, declared_vars, quant_lines, prop_lines, indent, quantifier):
        quant_lines.append(f"{indent}{quantifier} {node.var_name} : {self._pred_sig[node.var_name]}")
        
        prop_lines.append(f'{indent}{node.var_name}.name = "{node.text}"')
        declared_vars.add(node.var_name)        

    def _try_quantify(self, node, declared_vars, quant_lines, prop_lines, indent, quantifier):
        if node.var_name not in declared_vars and node.var_name not in self.let_bound_vars:
            self._quantify(node, declared_vars, quant_lines, prop_lines, indent, quantifier)

    def _let_bound(self, node, declared_vars, let_bindings, indent):
        let_line = CONST_LET_DECLARE_TMPL.format(indent=indent, concept=node.var_name, type=self._pred_sig[node.var_name], concept_name=node.text)
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

    def _mk_event_axiom(self, root, level=1, root_named=False, declared_vars=None, visited_nodes=None):
            
        if root in visited_nodes:
            return ""  # Prevent infinite loop on re-entrance
        visited_nodes.add(root)
        indent = ' ' * level
        next_indent = ' ' * (level + 2)
        c_quant = {}
        let_bindings = []
        prop_lines = []
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

        roles_dict = self._role_dict_retrieve(root)
        print('roles_dict: ', roles_dict)


        role_filler_nodes = []
        print('2. regular children')
        # step 2: Regular children
        # do special entity check and stop further calls over children
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

            # handle inversed role edge
            role_name = None
            # inversed_role flag is for later ordering decisions
            inversed_role = False
            if re.match(r':arg\d-of', rel):
                c_roles_dict = self._role_dict_retrieve(c)
                role_name = self._role_name_retrieve(c_roles_dict, rel[:-3])
                inversed_role = True
            elif rel.endswith('-of') and rel not in OF_SPECIAL_ROLE:
                role_name = self._role_name_retrieve(roles_dict, rel[:-3])
                inversed_role = True
            else:
                role_name = self._role_name_retrieve(roles_dict, rel)
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
            if c_cat in ['special-entity']:
                self.special_ent_declare(c, root, role_id, role_name,indent, let_bindings, prop_lines)
                print('special-entity: ', c.text, '|', c.var_name)

            elif c_cat == 'name':
                name_str = "_".join([cc.text.replace('"', '') for cc, _ in c.children.items()])
                self.regular_let_prop_declare(inversed_role, root.var_name, f'"{name_str}"', indent, role_id, role_name, let_bindings, prop_lines)
                print('name: ', c.text, '|', c.var_name)
            elif c_cat in ['float', 'int', 'attribute']:
                role_id = f"{root.var_name}_{c.var_name[5:]}"
                c_value = c.text if c_cat in ['float', 'int'] else f'"{c.text}"'

                self.regular_let_prop_declare(inversed_role, root.var_name, c_value, indent, role_id, role_name, let_bindings, prop_lines)
                print('num attr: ', c.text, '|', c.var_name)
                
            elif c_cat in ['term-mod']:
                self.regular_let_prop_declare(inversed_role, root.var_name, f'"{c.text}"', indent, role_id, role_name, let_bindings, prop_lines)
                print('term-mod: ', c.text, '|', c.var_name)

            else:
                if self._pred_sig.get(c.var_name, None) == "String":

                    self.regular_let_prop_declare(inversed_role, root.var_name, f'"{c.text}"', indent, role_id, role_name, let_bindings, prop_lines)
                    print('term string: ', c.text, '|', c.var_name)
                    declared_vars.add(c.var_name)
                else:
                    self.regular_let_prop_declare(inversed_role, root.var_name, c.var_name, indent, role_id, role_name, let_bindings, prop_lines)
                    role_filler_nodes.append(c)
                    print('regular node: ', c.text, '|', c.var_name)


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
        # 4. Recurse into children for logical body (not for variable declarations)
        for c in role_filler_nodes :
            if len(c.children) > 0:
                print('recurse into children, c: ', c.var_name, '|', c.text)
                sub = self._mk_event_axiom(c, level=level + 1, root_named=True, declared_vars=declared_vars, visited_nodes=visited_nodes)
                if sub.strip():
                    subformulas.append(f"{indent}(\n{sub}\n{indent})")
            
        # self._handles_lifted_declare(root, declared_vars, let_bindings, quant_lines, prop_lines, indent)


        # Final block structure
        quant_block = ",\n".join(quant_lines)
        reranked_lets = self._rerank_const_in_lets(let_bindings)
        let_block = "\n".join(reranked_lets)
        prop_block = " ∧\n".join(prop_lines + subformulas)

        

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
 
# -------------------------------------------------------------------------
# Script entry‑point
# -------------------------------------------------------------------------
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


    demo_amr3 = r"""
    (d / drive-01
         :arg0 (p / person)
         :arg1 (c / car)
         :source (s / city :name (n / name :op1 "Denver"))
         :destination (l / city :name (n2 / name :op1 "Boulder")))
    """

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

    # demo_amr3 = r"""
    # (l / love-01~1
    #    :ARG0 (i / i~0)
    #    :ARG1 (g / girl~4
    #             :ARG1-of (s / same-01~3))
    #    :duration (a / about~6
    #                 :op1 (t / temporal-quantity~7,8
    #                         :quant 6~7,8
    #                         :unit (y / year~7,8))))
    # """

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

    # demo_amr3 = r'''
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
    # '''

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
#     '''

    # demo_amr3 = r'''
    # (c / close-10~2,3
    #    :ARG1 (i / i~1)
    #    :ARG2 (p / point~5
    #             :mod (b / break-01~4
    #                     :ARG1 i))
    #    :degree (v / very~1))
    # '''
    # demo_amr3 = r'''
    # (s3a / and~1
    #      :op1 (s3k / keep-01~1
    #                :ARG0 (s3i / i~15)
    #                :ARG1 (s3i2 / it~2)
    #                :duration (s3f / forever~5))
    #      :op2 (s3t / tell-01~7
    #                :ARG0 s3i
    #                :content s3i2
    #                :ARG1-of (s3c / cause-01~14
    #                              :ARG0 (s3p2 / possible-01~17
    #                                          :content (s3c2 / cope-01~18
    #                                                         :ARG0 s3i
    #                                                         :time (s3a2 / anymore~19))
    #                                          :mod (s3j / just~16)
    #                                          :polarity -~17)
    #                              :plural +)
    #                :ARG2 (s3p / person~9
    #                           :ARG0-of (s3h / have-rel-role-91~9
    #                                         :ARG1 s3i
    #                                         :ARG2 (s3f2 / friend~9)))
    #                :time (s3b / before~13
    #                           :op1 (s3n / now~13)
    #                           :quant (s3f3 / few~11
    #                                        :op1 (s3t2 / temporal-quantity~12
    #                                                   :quant 1~12
    #                                                   :unit (s3m / month~12))
    #                                        :definite -))
    #                :time (s3t3 / then~6)))
    # '''

#     demo_amr3 = r'''
# (w / want-01
#     :ARG0 (b / boy
#         :definite +)
#     :ARG1 (b1 / believe-01
#         :ARG0 (g / girl
#             :definite +)
#         :ARG1 (a / and
#             :op1 (e / eat-01
#                 :ARG0 b
#                 :ARG1 (p / pizza))
#             :op2 (d / drink-01
#                 :ARG0 b 
#                 :ARG1 (c / coke)))
#         :frequency ( r2 / rate-entity-91
#                :ARG1 2
#                :ARG2 ( t4 / temporal-quantity :quant 1
#                      :unit ( y / year )))))
#     '''
    demo_amr3 = r'''
(s6m / multi-sentence~26
     :snt1 (s6a / and~7
                :op1 (s6k / know-01~3
                          :ARG0 (s6i / i~0)
                          :ARG1 (s6t / thing~6
                                     :ARG1-of (s6d / do-02~6
                                                   :ARG0 s6i))
                          :mod (s6s / simple~1)
                          :polarity -~2)
                :op2 (s6f / follow-through-07~17,18
                          :ARG0 s6i
                          :ARG1 (s6t3 / thing~12
                                      :ARG1-of (s6d2 / do-02~14
                                                     :ARG0 s6i)
                                      :plural +)
                          :polarity -~16
                          :time (s6t2 / think-01~10,11
                                      :ARG0 s6i
                                      :ARG1 s6t3)
                          :time (s6e / ever~20)))
     :snt2 (s6a2 / and~26
                 :op1 (s6s2 / say-01~23
                            :ARG0 (s6p / person~21
                                       :ARG0-of (s6h / have-rel-role-91~21
                                                     :ARG1 (s6i2 / i~24)
                                                     :ARG2 (s6f2 / friend~21)))
                            :content (s6l / lazy~25
                                          :domain s6i2)
                            :frequency (s6o / often~22))
                 :op2 (s6p2 / possible-01~28
                            :content (s6d3 / disagree-01~29
                                           :ARG0 s6i2
                                           :time (s6t4 / time~48
                                                       :quant (s6l2 / lot~31)))
                            :polarity -~28))
     :snt3 (s6a3 / and~47
                 :op1 (s6f3 / feel-01~36,37
                            :ARG0 (s6i3 / i~35)
                            :ARG1 (s6t5 / thing~34
                                        :ARG1-of (s6r / resemble-01~34
                                                      :content (s6t6 / try-01~34
                                                                     :ARG0 (s6p3 / person~44)
                                                                     :ARG1 (s6e2 / thing~38
                                                                                 :ARG1-of (s6d4 / do-02~41
                                                                                                :ARG0 (s6a4 / anyone~39)
                                                                                                :content-of (s6p4 / possible-01~40)
                                                                                                :ARG2 (s6h2 / help-01~43
                                                                                                            :ARG0 s6a4)
                                                                                                :definite +)
                                                                                 :definite -
                                                                                 :quant every~38)))))
                 :op2 (s6f4 / fail-01~53
                            :ARG1 s6i3
                            :mod (s6a5 / again~51
                                       :op1 (s6t7 / time~46)
                                       :op2 (s6t8 / time~50))
                            :plural +)))

    '''

    demo_amr3 = '''
(xv0 / and
      :op1 (xv4 / wear-01
            :ARG1 (xv1 / clothes
                  :ARG1-of (xv5 / white-02)))
      :op2 (xv2 / dance-01
            :ARG0 (xv3 / girl
                  :ARG0-of xv4)))
    '''
    leancode = t.translate(demo_amr3)
    print(leancode)
    # new_leancode = reorder_choice_blocks(leancode)

    # print(new_leancode)