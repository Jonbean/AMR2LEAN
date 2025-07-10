"""
Tiny façade so the rest of the translator never touches PropbankFrames
directly.  Feel free to expand (e.g. cache frames on disk).
"""
import re
from pathlib import Path
from amr_toolbox.propbank_loader import PropbankFrames   # <-- adjust import path

SENSE_RE = re.compile(r"-(\d\d)$")
DEFAULT_ROLES = {'0': 'PAG', '1': 'PPT', '2': 'GOL', '3': 'PRD', '4': 'MNR'}

class Roleset:
    """Lightweight view needed for code‑gen."""
    def __init__(self, lemma: str, sense: str, roles):
        self.lemma = lemma               # want …
        self.sense = sense               # … 01
        self.roles = roles               # list[Role]

class Role:
    def __init__(self, idx: str, fun: str):
        self.idx = idx                  # "0", "1", …
        self.fun = fun                  # "ARG0", "ARG1"  or PB tag e.g. "PAG"

class PropbankCatalogue:
    def __init__(self, frame_dir: str, version="Propbank"):
        self._frames = PropbankFrames(Path(frame_dir), version=version)
        self._frames.load()
        self._frames.roleset_dict()
        self._default_roles = {'0': 'PAG', '1': 'PPT', '2': 'GOL', '3': 'PRD', '4': 'MNR'}

    def get_roleset(self, amr_pred_name: str) -> Roleset:
        # "want-01"  ->  "want.01"
        last_dash_index = amr_pred_name.rfind('-')
        if last_dash_index == -1:
            return None
        else:
            lookup = amr_pred_name[:last_dash_index].replace('-', '_') + '.' + amr_pred_name[last_dash_index+1:]

            
            if lookup not in self._frames.rolesets:
                default_roles = [Role(index, func_tag) for index, func_tag in self._default_roles.items()]

                sense = SENSE_RE.search(amr_pred_name).group(1)
                lemma = lookup.split('.')[0]
                return Roleset(lookup, sense, default_roles)
            rs = self._frames.rolesets[lookup]
            lemma, sense = rs.root_predicate, SENSE_RE.search(amr_pred_name).group(1)
            roles = [Role(r.index, r.function) for r in rs.roles if r.index.isnumeric()]
            
            return Roleset(lemma, sense, roles)