import json, re
from pathlib import Path
from typing import Dict, List

ROLE_RE = re.compile(r"^(\d+)$")

class SpecialRole:
    def __init__(self, idx: str, name: str):
        self.idx  = idx
        self.name = name

class AMRSpecialFrames:
    def __init__(self, json_path: str):
        self._frames: Dict[str, List[SpecialRole]] = {}
        self._load(json_path)

    def _load(self, path: str):
        data = json.loads(Path(path).read_text())
        for frame_name, spec in data.items():
            roles = [SpecialRole(r["index"], r["name"]) for r in spec["roles"]]
            self._frames[frame_name] = roles

    def get(self, frame_name: str):
        """Return list[SpecialRole] or None if unknown."""
        return self._frames.get(frame_name)