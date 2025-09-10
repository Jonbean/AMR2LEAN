#!/usr/bin/env python3
# ccg2lean_pipeline.py
# Multi-sentence -> depccg (CCG + ccg2lambda FOL) -> Lean 4 file
# Ordered emission, PIT -> {axiom, lemma, theorem}, shared decls.

import argparse
import json
import os
import pathlib
import re
import subprocess
import sys
import xml.etree.ElementTree as ET
from typing import Dict, List, Tuple, Optional, Set

# ---------- config / env quieting ----------
os.environ.setdefault("PYTHONWARNINGS", "ignore")
os.environ.setdefault("TF_CPP_MIN_LOG_LEVEL", "3")

# ---------- depccg runners ----------

XML_START_RE = re.compile(
    rb"<\?xml|<\s*(root|document|corpus|sentences|jigg)\b", re.IGNORECASE
)

def _extract_xml_payload(raw: bytes) -> bytes:
    m = XML_START_RE.search(raw)
    return raw[m.start():] if m else b""

def run_depccg_xml(sentences: List[str], model="elmo", annotator="spacy") -> ET.Element:
    cmd = [
        "depccg_en", "-m", model, "--annotator", annotator,
        "--tokenize", "--format", "jigg_xml_ccg2lambda",
    ]
    p = subprocess.run(
        cmd,
        input=("\n".join(sentences) + "\n").encode("utf-8"),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    out, err = p.stdout, p.stderr
    if p.returncode != 0:
        sys.stderr.write(err.decode("utf-8", "ignore"))
        raise RuntimeError("depccg_en failed (non-zero exit). See stderr above.")

    payload = _extract_xml_payload(out)
    if not payload:
        sys.stderr.write("[info] No XML start found on stdout; will try text fallback.\n")
        raise ET.ParseError("No XML payload")

    try:
        return ET.fromstring(payload.decode("utf-8"))
    except ET.ParseError as e:
        sys.stderr.write(f"[info] XML parse failed: {e}. Will try text fallback.\n")
        raise

def run_depccg_text(sentences: List[str], model="elmo", annotator="spacy") -> List[str]:
    """Ask depccg for plain ccg2lambda output and heuristically harvest one FOL per sentence."""
    cmd = ["depccg_en", "-m", model, "--annotator", annotator, "--tokenize", "--format", "ccg2lambda"]
    p = subprocess.run(
        cmd,
        input=("\n".join(sentences) + "\n").encode("utf-8"),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if p.returncode != 0:
        sys.stderr.write(p.stderr.decode("utf-8", "ignore"))
        raise RuntimeError("depccg_en failed in text mode.")
    lines = [ln.rstrip() for ln in p.stdout.decode("utf-8", "ignore").splitlines()]

    # Group blocks separated by blank lines
    blocks, cur = [], []
    for ln in lines:
        if not ln.strip():
            if cur:
                blocks.append(" ".join(cur))
                cur = []
        else:
            cur.append(ln.strip())
    if cur: blocks.append(" ".join(cur))

    # From each block, keep the substring that looks like a formula
    FOL_START = re.compile(
        r"(forall|exists|all|some|\bnot\b|\band\b|\bor\b|->|[-&|()]|[A-Za-z_][A-Za-z0-9_:\-]*\s*\([^()]*\))"
    )
    fols: List[str] = []
    for blk in blocks:
        # Remove obvious prefix noise like "ID=..., log probability=..."
        blk = re.sub(r"\bID=\d+[^A-Za-z(]+", " ", blk)
        m = FOL_START.search(blk)
        if m:
            fols.append(blk[m.start():].strip())
    return fols

# ---------- FOL harvesting from XML (per sentence, preserve order) ----------

def _local(tag: str) -> str:
    if tag.startswith("{"):
        return tag.split("}", 1)[1]
    if ":" in tag:
        return tag.split(":", 1)[1]
    return tag

def _first_formula_in(el: ET.Element) -> Optional[str]:
    # Prefer <...sem> descendants
    for d in el.iter():
        if _local(d.tag).lower().endswith("sem"):
            txt = (d.text or "").strip()
            if txt:
                return txt
    # Then attributes likely to carry formulas
    for d in el.iter():
        for k, v in d.attrib.items():
            if k.lower() in {"sem", "ccg2lambda", "formula", "lf"} and v.strip():
                return v.strip()
    # Then nodes named 'lf' or 'logic'
    for d in el.iter():
        if _local(d.tag).lower() in {"lf", "logic"} and (d.text or "").strip():
            return d.text.strip()
    return None

def extract_fols_per_sentence_from_xml(doc: ET.Element, num_inputs: int) -> List[str]:
    sents = []
    for el in doc.iter():
        if _local(el.tag).lower() == "sentence":
            sents.append(el)
    fols: List[str] = []
    for s in sents:
        f = _first_formula_in(s)
        if f: fols.append(f)
    if len(fols) != num_inputs:
        flat: List[str] = []
        for el in doc.iter():
            if _local(el.tag).lower().endswith("sem"):
                txt = (el.text or "").strip()
                if txt:
                    flat.append(txt)
        if len(flat) >= num_inputs:
            fols = flat[:num_inputs]
    return fols

# ---------- FOL -> Lean mapping ----------

CALL_RE = re.compile(r"([A-Za-z_][A-Za-z0-9_:\-]*)\s*\(([^()]*)\)")
EQ_FUNC_RE = re.compile(r"([A-Za-z_][A-Za-z0-9_:\-]*)\s*\(\s*([A-Za-z0-9_]+)\s*\)\s*=\s*([A-Za-z0-9_]+)")
EQ_FUNC_REV_RE = re.compile(r"([A-Za-z0-9_]+)\s*=\s*([A-Za-z_][A-Za-z0-9_:\-]*)\s*\(\s*([A-Za-z0-9_]+)\s*\)")

def is_event_var(v: str) -> bool:
    return v.startswith("e")  # heuristic: e, e0, e1, ...

def sort_of_var(v: str) -> str:
    return "ε" if is_event_var(v) else "ι"

RESERVED: Set[str] = {
    "all", "some", "if", "then", "else", "match", "with", "end",
    "theorem", "lemma", "axiom", "by", "have", "let", "in",
    "Type", "Sort", "Prop", "fun", "True", "False", "Eq",
    "and", "or", "not", "forall", "exists", "Acc"
}

def clean_name(name: str) -> str:
    name = name.lstrip("_")
    name = re.sub(r"[^A-Za-z0-9_]", "_", name)
    if not name:
        return "P"
    if name in RESERVED:
        name = f"p_{name}"
    return name

def tokenize_calls(f: str) -> List[Tuple[str, List[str]]]:
    calls = []
    tmp = f
    while True:
        m = CALL_RE.search(tmp)
        if not m: break
        name = clean_name(m.group(1))
        args = [a.strip() for a in m.group(2).split(",") if a.strip()]
        calls.append((name, args))
        tmp = tmp[:m.start()] + " " * (m.end()-m.start()) + tmp[m.end():]
    return calls

def infer_signatures(formulas: List[str]) -> Dict[str, Tuple[str, ...]]:
    """
    Build a map name -> signature tuple.
    Predicates: (arg_sorts..., 'Prop')
    Functions (from equality): (arg_sort, codomain_sort)
    """
    sig: Dict[str, Tuple[str, ...]] = {}

    # 1) equality-driven function typing: F(e) = x  ⇒  F : ε → ι
    for fol in formulas:
        for m in EQ_FUNC_RE.finditer(fol):
            f, a, b = clean_name(m.group(1)), m.group(2), m.group(3)
            sig[f] = (sort_of_var(a), sort_of_var(b))
        for m in EQ_FUNC_REV_RE.finditer(fol):
            a, f, b = m.group(1), clean_name(m.group(2)), m.group(3)
            sig[f] = (sort_of_var(b), sort_of_var(a))

    # 2) predicate typing from calls (skip quantifier words, and functions already typed)
    QUANTIFIERS = {"forall", "exists", "all", "some"}
    for fol in formulas:
        for name, args in tokenize_calls(fol):
            if name in QUANTIFIERS:
                continue
            if name in sig and len(sig[name]) == 2 and sig[name][-1] in ("ι", "ε"):
                continue
            sorts = tuple(sort_of_var(a) for a in args) + ("Prop",)
            if name in sig:
                if len(sig[name]) != len(sorts):
                    if len(sorts) > len(sig[name]):
                        sig[name] = sorts
            else:
                sig[name] = sorts
    return sig

# ccg2lambda variants: words and symbols
KW = [
    (r"\bforall\b", "∀"), (r"\ball\b", "∀"),
    (r"\bexists\b", "∃"), (r"\bsome\b", "∃"),
    (r"\bnot\b", "¬"),
    (r"\band\b", "∧"), (r"\bor\b", "∨"),
    (r"->", "→"),
    (r"\|", "∨"), (r"&", "∧"),   # symbol forms
]

# support depccg variants that emit: forall x., all x., exists x., some x.
QF_RE = re.compile(r"\b(forall|all|exists|some)\b\s*([A-Za-z0-9_]+)\s*[\.:\)]")

def annotate_binders(s: str) -> str:
    def rep(m):
        q, v = m.group(1), m.group(2)
        sym = "∀" if q in {"forall", "all"} else "∃"
        sort = "ε" if is_event_var(v) else "ι"
        return f"{sym} ({v} : {sort}), "
    return QF_RE.sub(rep, s)

def to_curried_apps(s: str) -> str:
    out = s
    while True:
        m = CALL_RE.search(out)
        if not m: break
        name = clean_name(m.group(1))
        args = [a.strip() for a in m.group(2).split(",") if a.strip()]
        out = out[:m.start()] + (name + (" " + " ".join(args) if args else "")) + out[m.end():]
    return out

TRUE_PATTERNS = [
    # local neutral eliminations
    (re.compile(r"\(\s*True\s*∧\s*"), "("),
    (re.compile(r"\s*∧\s*True\s*\)"), ")"),
    (re.compile(r"\bTrue\s*∧\s*"), ""),     # True ∧ A -> A
    (re.compile(r"\s*∧\s*True\b"), ""),     # A ∧ True -> A
    (re.compile(r"\bTrue\s*→\s*"), ""),     # True → A -> A
]

def prune_trivial_true(s: str) -> str:
    prev = None
    out = s
    # iterate to a fixed point to clean nested cases
    while prev != out:
        prev = out
        for rx, repl in TRUE_PATTERNS:
            out = rx.sub(repl, out)
        # clean accidental empty parens
        out = re.sub(r"\(\s*\)", "", out)
        out = re.sub(r"\s+", " ", out).strip()
    return out

# Turn unary '-' (as used by ccg2lambda for negation) into '¬'
# Examples handled: -∃, -∀, -( ... ), -Pred(x), - P x
# We avoid touching numbers like -1 by requiring the next token to be (∀|∃|(|letter)
NEG_UNARY_RE = re.compile(r'(^|[^0-9A-Za-z_])-\s*(?=(∀|∃|\(|[A-Za-z_]))')

def normalize_unary_negation(s: str) -> str:
    # Replace with ¬, preserving the preceding char (group 1)
    return NEG_UNARY_RE.sub(r'\1¬', s)

def fol_to_lean_prop(f: str) -> str:
    s = f

    # 1) Quantifiers first (prevents CALL_RE from grabbing "all(...)" etc.)
    s = annotate_binders(s)

    # 2) Logical connectives / arrows / symbol forms
    for a, b in KW:
        s = re.sub(a, b, s)

    # 3) Normalize punctuation that sometimes shows after binders
    s = s.replace(".(", "(").replace(").", ")")
    s = re.sub(r"\s*\.\s+", " ", s)

    # 4) Fix unary '-' negation (e.g., -∃, -( ... ), -Pred x)
    s = normalize_unary_negation(s)

    # 5) Turn f(a,b,c) into curried apps "f a b c"
    s = to_curried_apps(s)

    # 6) Prune neutral True clutter
    s = prune_trivial_true(s)

    # 7) Whitespace finalization
    s = re.sub(r"\s+", " ", s).strip()
    return s

# ---------- Lean emission ----------

PRELUDE = """\
import Mathlib.Logic.Basic
open Classical

universe u
axiom ι : Type u   -- individuals
axiom ε : Type u   -- events
"""

def decl_from_sig(name: str, sig: Tuple[str, ...]) -> str:
    if not sig:
        return f"axiom {name} : Prop"
    if sig[-1] == "Prop":
        return f"axiom {name} : " + (" → ".join(sig[:-1]) + " → Prop" if len(sig) > 1 else "Prop")
    # function: s1 → s2
    return f"axiom {name} : " + " ".join(["→".join(sig)])  # Lean parser ok with spaces around arrows

# ---------- PIT mapping & IO ----------

LABEL_MAP = {
    "premise": "axiom",
    "assumption": "axiom",
    "definition": "axiom",
    "def": "axiom",
    "fact": "axiom",
    "rule": "axiom",
    "explicit-knowledge-claim": "axiom",
    "axiom": "axiom",
    "lemma": "lemma",
    "conclusion": "theorem",
    "theorem": "theorem",
    "thm": "theorem",
    "negated-theorem": "negated-theorem",
}

def norm_label(label: Optional[str]) -> str:
    if not label: return "axiom"
    key = label.strip().lower()
    return LABEL_MAP.get(key, key if key in {"axiom","lemma","theorem","negated-theorem"} else "axiom")

def load_items_from_json(path: pathlib.Path) -> List[Dict]:
    raw = path.read_text(encoding="utf-8").strip()
    items: List[Dict] = []
    try:
        obj = json.loads(raw)
        if isinstance(obj, dict):
            obj = [obj]
        if isinstance(obj, list):
            items = obj
    except json.JSONDecodeError:
        items = [json.loads(ln) for ln in raw.splitlines() if ln.strip()]
    out = []
    for i, it in enumerate(items, 1):
        text = it.get("text") or it.get("sentence")
        if not text:
            raise ValueError(f"JSON item {i} missing 'text'.")
        out.append({
            "text": text.strip(),
            "label": norm_label(it.get("label")),
            "name": it.get("name"),
            "negated": bool(it.get("negated", False)),
        })
    return out

def load_items_from_plain(sent_path: Optional[pathlib.Path], labels_path: Optional[pathlib.Path]) -> List[Dict]:
    if sent_path:
        sentences = [s.strip() for s in sent_path.read_text(encoding="utf-8").splitlines() if s.strip()]
    else:
        sentences = [s.strip() for s in sys.stdin.read().splitlines() if s.strip()]
    if not sentences:
        sys.exit("No sentences provided.")
    if labels_path and labels_path.exists():
        labels = [norm_label(s) for s in labels_path.read_text(encoding="utf-8").splitlines()]
        if len(labels) < len(sentences):
            labels += ["axiom"] * (len(sentences) - len(labels))
        else:
            labels = labels[:len(sentences)]
    else:
        labels = ["axiom"] * len(sentences)
    items = []
    for i, (txt, lab) in enumerate(zip(sentences, labels), 1):
        neg = (lab == "negated-theorem")
        base = lab if lab != "negated-theorem" else "theorem"
        items.append({"text": txt, "label": base, "name": None, "negated": neg})
    return items

def default_name(kind: str, idx: int) -> str:
    if kind == "axiom": return f"axiom_{idx}"
    if kind == "lemma": return f"lemma_{idx}"
    return f"theorem_{idx}"

# ---------- Free constant harvesting (pronouns etc.) ----------

FREE_INDIV_RE = re.compile(r"\b_[A-Za-z][A-Za-z0-9_]*\b")

def harvest_free_individuals(formulas: List[str]) -> List[str]:
    names: Set[str] = set()
    for f in formulas:
        for m in FREE_INDIV_RE.finditer(f):
            names.add(m.group(0))  # keep underscore; Lean allows identifiers like _they
    return sorted(names)

# ---------- Build Lean from items ----------

def build_lean_from_items(items: List[Dict], all_formulas: List[str]) -> str:
    # Map each item to one formula (already ordered). Attach Lean proposition strings.
    lean_props = [fol_to_lean_prop(f) for f in all_formulas]
    for idx, (it, prop) in enumerate(zip(items, lean_props), 1):
        it["prop"] = prop
        if not it.get("name"):
            it["name"] = default_name(it["label"], idx)

    # Shared declarations (once) from all formulas
    sigs = infer_signatures(all_formulas)
    decls = "\n".join(sorted(decl_from_sig(n, sigs[n]) for n in sigs))

    # Free individual constants like _they
    free_inds = harvest_free_individuals(all_formulas)
    free_decl = "\n".join(f"axiom {n} : ι" for n in free_inds)

    # Ordered emission: keep original input order
    stmts: List[str] = []
    for it in items:
        kind = it["label"]
        name = clean_name(it["name"])
        body = it["prop"]
        if kind == "axiom":
            stmts.append(f"-- [axiom] {name}\naxiom {name} : {body}")
        elif kind == "lemma":
            stmts.append(f"-- [lemma] {name}\nlemma {name} : {body} := by\n  sorry")
        else:  # theorem
            if it.get("negated", False):
                stmts.append(f"-- [theorem] {name} (negated)\ntheorem {name} : ¬({body}) := by\n  sorry")
            else:
                stmts.append(f"-- [theorem] {name}\ntheorem {name} : {body} := by\n  sorry")

    sections = [PRELUDE]
    if free_decl:
        sections.append(free_decl)
    if decls:
        sections.append(decls)
    sections.append("\n\n".join(stmts))
    return "\n\n".join(sections) + "\n"

# ---------- CLI ----------

def main():
    ap = argparse.ArgumentParser(description="Sentence(s) -> depccg (ccg2lambda FOL) -> Lean 4 (with PITs).")
    src = ap.add_mutually_exclusive_group(required=False)
    src.add_argument("-i", "--input", help="Text file with one sentence per line (default: stdin)")
    src.add_argument("--json", help="JSON or NDJSON of items: {text, label?, name?, negated?}")
    ap.add_argument("--labels", help="Optional labels file (one label per line) for --input mode")
    ap.add_argument("-o", "--out", default="sentences.lean", help="Output Lean file")
    ap.add_argument("--model", default="elmo", help="depccg model (default: elmo)")
    ap.add_argument("--annotator", default="spacy", help="depccg annotator (default: spacy)")
    args = ap.parse_args()

    # Load items
    if args.json:
        items = load_items_from_json(pathlib.Path(args.json))
    else:
        sent_path = pathlib.Path(args.input) if args.input else None
        labels_path = pathlib.Path(args.labels) if args.labels else None
        items = load_items_from_plain(sent_path, labels_path)

    sentences = [it["text"] for it in items]
    if not sentences:
        sys.exit("No sentences provided.")

    # Get per-sentence formulas, preserve order
    fols: List[str] = []
    try:
        xml = run_depccg_xml(sentences, args.model, args.annotator)
        fols = extract_fols_per_sentence_from_xml(xml, num_inputs=len(sentences))
        if len(fols) != len(sentences):
            sys.stderr.write("[info] XML did not yield one formula per sentence; trying text fallback.\n")
            fols = run_depccg_text(sentences, args.model, args.annotator)
    except Exception:
        fols = run_depccg_text(sentences, args.model, args.annotator)

    if not fols:
        sys.exit("No formulas found (XML or text).")
    if len(fols) != len(sentences):
        sys.stderr.write(f"[warn] Found {len(fols)} formulas for {len(sentences)} sentences; truncating to min.\n")
    n = min(len(fols), len(sentences))
    items = items[:n]
    fols = fols[:n]

    lean_src = build_lean_from_items(items, fols)
    pathlib.Path(args.out).write_text(lean_src, encoding="utf-8")
    print(f"Wrote Lean file: {args.out}")

if __name__ == "__main__":
    main()