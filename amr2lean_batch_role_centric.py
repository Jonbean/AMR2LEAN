# role centric translation
from amr2lean2 import AMR2LeanTranslator
from propbank_interface import PropbankCatalogue
from typing import Dict, List, Tuple, Set 

class AMR2LeanBatch:
    def __init__(self, propbank_catalog: PropbankCatalogue,
                 import_semantic_gadgets: bool = False,
                 label_map: Dict[str,str] = None,
                 shorter_variant: bool = False,
                 include_nl_comment: bool = False ):
        self.tr = AMR2LeanTranslator(propbank_catalog, import_semantic_gadgets, shorter_variant, include_nl_comment)
        self.label_map = label_map or {
            "premise": "axiom",
            "implicit-assumption": "axiom",
            "lemma": "lemma",
            "rule": "lemma",
            "conclusion": "theorem",
            "hypothesis": "theorem",
            "axiom": "axiom",
            "theorem": "theorem",
        }

    def _kind(self, label: str) -> str:
        return self.label_map.get(label.lower().strip(), "axiom")

    def translate_many(self, items: List[Dict[str, str]]) -> str:
        """
        items in desired order; each item supports:
          { "amr": <penman>,
            "label": <string>,         # maps to axiom/lemma/theorem
            "name": Optional[str],     # lean identifier suffix
            "sid": Optional[str],      # AMR sentence id (if used by your loader)
            "negate": Optional[bool],  # only used when kind == "theorem"
          }
        """
        for it in items:
            kind   = self._kind(it.get("label", "axiom"))
            negate = bool(it.get("negate", False)) and (kind == "theorem")
            self.tr.translate_one_as(
                amr_str = it["amr"],
                kind    = kind,
                name    = it.get("name"),
                sid     = it.get("sid", ""),
                nl_body = it.get("text", ""),
                negate  = negate
            )
        return self.tr.M.render()


if __name__ == '__main__':
    pb_catalog = PropbankCatalogue("/Users/jonzcai/Documents/ComputerScience/NLP/data/datasets/propbank-frames/frames/")

    batch = AMR2LeanBatch(pb_catalog, import_semantic_gadgets=False, label_map=None, shorter_variant=True, include_nl_comment=True)

    amr1 = '''
(n / number
    :domain (n2 / number
        :ARG1-of (r / real-04)
        :mod (e / every)))
    '''
    amr2 = '''
(i / imaginary
    :domain (n / number
        :mod (c / complex)
        :mod (e / each)))
    '''
    amr3 = '''
(i / imaginary
    :polarity -
    :domain (n / number
        :ARG1-of (r / real-04)))
    '''
    lean_code = batch.translate_many([
        {"amr": amr1, "label": "premise",   "name": "Prem_1", "text": "test body text1" },
        {"amr": amr2, "label": "premise",   "name": "Prem_2", "text": "test body text2"},
        {"amr": amr3, "label": "conclusion","name": "Thm_3",  "text": "test body text3"}
    ])

    with open("./CoT/cot-test1.lean", "w") as f:
        f.write(lean_code)