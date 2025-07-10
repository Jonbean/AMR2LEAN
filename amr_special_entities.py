import json
from pathlib import Path
from typing import Dict, List

class EntityField:            # holds one field spec
    def __init__(self, role: str, name: str, ty: str):
        self.role = role      # ":quant", ":unit", …
        self.name = name      # Lean field label
        self.ty   = ty        # "Nat", "String", …

class AMRSpecialEntities:
    def __init__(self, json_path: str):
        raw = json.loads(Path(json_path).read_text())
        self.frames: Dict[str, List[EntityField]] = {}
        for frame_name, spec in raw.items():
            fields = [
                EntityField(f["role"], f["name"], f["type"])
                for f in spec["fields"]
            ]
            self.frames[frame_name] = fields

    def get(self, frame_name: str):
        """Return list[EntityField] or None."""
        return self.frames.get(frame_name)