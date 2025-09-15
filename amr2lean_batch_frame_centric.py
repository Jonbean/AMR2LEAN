
# frame centric approach for CoT translation
from propbank_interface import PropbankCatalogue
from amr_toolbox.AMRLoader import AMRLoader
from typing import Dict, List, Tuple
from amr2lean import AMR2LeanSequenceTranslator

class AMR2LeanBatch:
    """
    Multi-AMR driver:
      - preserves order,
      - shares boilerplate,
      - maps human labels -> {axiom | lemma | theorem},
      - optional negation per item (or inferred if label is 'contradiction').
    """
    def __init__(self, propbank_catalog: PropbankCatalogue, import_semantic_gadgets: bool = False,
                 label_map: Dict[str, str] = None, include_nl_comment: bool = False):
        self.pb = propbank_catalog
        self.import_semantic_gadgets = import_semantic_gadgets
        # default mapping (you can override by passing label_map)
        self.label_map = (label_map or {
            "premise": "axiom",
            "support": "lemma",
            "lemma": "lemma",
            "conclusion": "theorem",
            "theorem": "theorem",
            "hypothesis": "theorem",
            "claim": "theorem",
        })
        self.include_nl_comment = include_nl_comment

    def _to_kind_and_neg(self, label: str) -> Tuple[str, bool]:
        lab = (label or "").strip().lower()
        negate = lab in {"contradiction", "negated", "neg"}
        base = lab.replace("contradiction", "conclusion").replace("negated", "conclusion").strip()
        kind = self.label_map.get(base, "axiom")
        return kind, negate

    def translate_many(self, items: List[Dict[str, str]]) -> str:
        """
        items: list of dicts with keys:
          - "amr" (str)     : required AMR string
          - "label" (str)   : e.g., 'premise', 'conclusion'
          - "name"  (str)   : desired Lean identifier (optional but recommended)
          - "negate"(bool)  : optional explicit negation
          - "sid"   (str)   : optional sentence id/stable tag
        """
        seq = AMR2LeanSequenceTranslator(self.pb, import_semantic_gadgets=self.import_semantic_gadgets, include_nl_comment=self.include_nl_comment)

        for idx, item in enumerate(items, start=1):
            amr = item["amr"]
            label = item.get("label", "premise")
            name = item.get("name", None)
            sid  = item.get("sid", f"s{idx}")
            nl_body = item.get("text", '')
            kind, inferred_neg = self._to_kind_and_neg(label)
            negate = bool(item.get("negate", inferred_neg))

            seq.add(amr_str=amr, kind=kind, name=name, negate=negate, sid=sid, nl_body=nl_body)

        code = seq.render()

        return code

if __name__ == '__main__':
    pb_catalog = PropbankCatalogue("/Users/jj/data/datasets/propbank-frames/frames/")

    batch = AMR2LeanBatch(pb_catalog, import_semantic_gadgets=False, label_map=None, include_nl_comment=True)

    amr1 = r'''
    (n / number
        :domain (n2 / number
            :ARG1-of (r / real-04)
            :mod (e / every)))
    '''
    amr2 = r'''
    (i / imaginary
        :domain (n / number
            :mod (c / complex)
            :mod (e / each)))
    '''
    amr3 = r'''
    (i / imaginary
        :polarity -
        :domain (n / number
            :ARG1-of (r / real-04)))
    '''

    lean_code = batch.translate_many([
        {"amr": amr1, "label": "premise",    "name": "Prem_1", "text": "some test body1"},
        {"amr": amr2, "label": "premise",    "name": "Prem_2", "text": "some test body2"},
        {"amr": amr3, "label": "conclusion", "name": "Thm_3", "text": "some test body3"}
    ])

    with open("./CoT/cot-test2.lean", "w") as f:
        f.write(lean_code)