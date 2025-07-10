from __future__ import annotations
from typing import Dict, List, Tuple
import re
from amr_toolbox.AMRgraph import AMRNode
from nltk.corpus import wordnet as wn
from collections import deque, defaultdict


SENSE_RE = re.compile(r"-(\d\d)$")
ATTR_RE = re.compile(r"^attr-\d+$")
ATTR_OF_RE = re.compile(r"^:arg(\d+)-of$", re.IGNORECASE)
_OP_RE = re.compile(r":(?:op|snt)(\d+)")

# --------------------------------------------------------------------------- #
#  Helper utilities
# --------------------------------------------------------------------------- #
def has_child(node:AMRNode, rel:str, val:str|None=None) -> bool:
    """True if node --rel--> child  (and child's .text == val if given)"""
    for ch, r in node.children.items():
        if r == rel and (val is None or ch.text == val):
            return True
    return False


def has_any_child(node:AMRNode, rel:str, vals:List[str]) -> bool:
    for ch, r in node.children.items():
        if r == rel and ch.text in vals:
            return True
    return False

    # return any(lemma.lower() == s.name().split('.')[0] and s.pos() != 'n' for s in synsets)

    
def _ordered_children(node: AMRNode) -> List[AMRNode]:
    items = []
    for ch, rel in node.children.items():
        m = _OP_RE.match(rel)
        if m: items.append((int(m.group(1)), ch))
    return [ch for _, ch in sorted(items)]



def reorder_choice_blocks(lean_code: str) -> str:
    # 1) split into blocks on two-or-more newlines
    blocks = re.split(r'\n{2,}', lean_code)
    
    # 2) pull out all the Choice Prop blocks
    choice_blocks = {}
    kept_blocks   = []
    for blk in blocks:
        m = re.match(r'def\s+(\w+)\s*:\s*Choice\s+Prop\b', blk)
        if m:
            var = m.group(1)
            choice_blocks[var] = blk
        else:
            kept_blocks.append(blk)
    
    # 3) re‐insert each choice block just before the first block that mentions its var
    final_blocks = []
    for blk in kept_blocks:
        # for each pending choice var, if this block mentions it, prepend its choice block
        for var in list(choice_blocks):
            if re.search(r'\b{}\b'.format(re.escape(var)), blk):
                final_blocks.append(choice_blocks.pop(var))
        final_blocks.append(blk)
    
    # 4) any leftover choice blocks go at the end
    for blk in choice_blocks.values():
        final_blocks.append(blk)
    
    # re‐join with double‐newlines
    return "\n\n".join(final_blocks)

def topo_sort(deps):

    order = []
    indegree = {k: len(v) for k, v in deps.items()}
    dq = deque([k for k, deg in indegree.items() if deg == 0])

    while dq:
        node = dq.popleft()
        order.append(node)
        for dependent in deps:
            if node in deps[dependent]:
                deps[dependent].remove(node)
                indegree[dependent] -= 1
                if indegree[dependent] == 0:
                    dq.append(dependent)

    if any(deps[n] for n in deps):
        print("Warning: Cycle detected, partial order returned.")
        for n in deps:
            if deps[n]:
                order.append(n)
    return order

def topo_sort_amr(deps, depth):
    from collections import deque

    order = []
    indegree = {node: len(deps[node]) for node in deps}
    dq = deque([n for n, deg in indegree.items() if deg == 0])

    while dq:
        node = dq.popleft()
        order.append(node)
        for other in deps:
            if node in deps[other]:
                deps[other].remove(node)
                indegree[other] -= 1
                if indegree[other] == 0:
                    dq.append(other)

    # If cycles remain, resolve re-entrancies
    unresolved = {n for n in deps if deps[n]}
    if unresolved:
        print("Re-entrancy detected, resolving by depth.")
        for node in unresolved:
            for dep in list(deps[node]):
                if depth.get(dep, 0) < depth.get(node, 0):
                    # Keep the dependency if dep is deeper (e.g., break-01 > close-10)
                    continue
                else:
                    # Remove the dependency if dep is shallower
                    print(f"Removed reentrant edge: {node} depends on {dep}")
                    deps[node].remove(dep)
                    indegree[node] -= 1
                    if indegree[node] == 0:
                        dq.append(node)

        # Resume sorting
        while dq:
            node = dq.popleft()
            if node not in order:
                order.append(node)
            for other in deps:
                if node in deps[other]:
                    deps[other].remove(node)
                    indegree[other] -= 1
                    if indegree[other] == 0:
                        dq.append(other)

    # Add any stragglers
    for node in deps:
        if node not in order:
            order.append(node)

    return order

def print_tree(d, indent=0):
    for key, value in d.items():
        # Print the var_name of the key object
        print('  ' * indent + str(getattr(key, 'var_name', str(key))))
        if isinstance(value, dict):
            print_tree(value, indent + 1)