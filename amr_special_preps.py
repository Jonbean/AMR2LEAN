import json, re
from pathlib import Path

class PrepSpec:
    def __init__(self, stem: str, category: str, arity: int):
        self.stem, self.category, self.arity = stem, category, arity

class PrepInventory:
    """Maps every spelling variant to a single PrepSpec."""
    def __init__(self, path="special_preps.json"):
        raw = json.loads(Path(path).read_text())
        self.map = {}
        for lemma, spec in raw.items():
            entry = PrepSpec(spec["stem"], spec["category"], spec["arity"])
            for key in [lemma] + spec.get("aliases", []):
                self.map[key] = entry

    def get(self, lemma: str):
        return self.map.get(lemma)          # PrepSpec | None