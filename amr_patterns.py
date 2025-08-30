
NON_CORE_EDGES = {
    ":source":       "Source",
    ":destination":  "Destination",
    ":direction":    "Direction",
    ":beneficiary":  "Beneficiary",
    ":extent":       "Extent",
    ":instrument":   "Instrument",
    ":medium":       "Medium",
    ":manner":       "Manner",
    ":purpose":      "Purpose",     # event ↔︎ event
    ":cause":        "Cause",
    ":concession":   "Concession",
    ":condition":    "Condition",
    ":topic":        "Topic",
    ":mod":          "Modifier",
    ":part-of":      "PartOf",
    ":subevent-of":  "SubeventOf",
    ":consist-of":   "ConsistOf",
    ":duration":     "Duration",
    ":subset":       "SubSet",
    ":superset":     "SuperSet",
    ":name":         "Name",
    ":poss":         "Possessive",
    ":degree":       "Degree",
    ":mode":         "Mode",
    ":mod":          "Mod",
    ":content":      "NonVeridical",
    ":time":         "Time",
    ":plural":       "Plural",
    ":frequency":    "Frequency",
    ":polarity-of":  "PolarityOf",
    ":location":     "Location",
    ":example":      "Examples"
}

ALWAYS_ENTITY = {"imperative", "you", "i", "he", "she", "they", "them", "et-cetera", "it", "we", "this", "that"}
ALWAYS_MOD    = {"again", "really", "+", "-", "then", "after", "while"}  # extend as needed
OF_SPECIAL_ROLE = [':part-of', ':subevent-of', ':consist-of', ':polarity-of']
CONNECTOR = {
    "and": "and_concept",
    "or":  "or_concept",
    "multisentence": "ms_concept"
}

UNIVERSAL_QUANR = ["all", "every", "each"]

INDICATOR_NONCORE_RELS = [':plural', ':definite', ':polarity', ':content']