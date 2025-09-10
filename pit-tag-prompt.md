You are a logical annotator. Your task has TWO parts: 

1. **Segmentation**: Split the reasoning text ("Rationales") into clear statements, each containing one logical step. Do not merge multiple logical moves into one. 
2. **PIT Tagging**: Assign a proof-intent tag (PIT) to each statement. 

Available PIT tags:
- premise (facts from the question/problem statement)
- new definition (introducing variables or concepts)
- rule/explicit-knowledge-claim (general truths, background knowledge)
- implicit assumption resurfacing (unstated but necessary assumptions made explicit)
- lemma (derived intermediate steps, calculations, simplifications)
- conclusion (final step or statement that delivers the answer)

### Format:
Output the results as a list of dictionaries in json format. For each statement, write:
```
[
    {'index': 0, 'text': `<statement0>`, 'PIT': `<PIT tag>`},
    {'index': 1, 'text': `<statement1>`, 'PIT': `<PIT tag>`},
    ...
]
```
---

### Example 1 (Math word problem)

**Question**: Anna spent 1/4 of her money, and now she has $24 left. How much did she have originally?  
**Rationales (raw)**: Let X be the amount Anna had originally she spent X*1/4 and has X - X*1/4 = 24 left combining like terms gives X*3/4 = 24 dividing both sides by 3/4 we get X = 32 so the answer is 32

**Output**:
```
[
	{'index: 0, 'text': 'Let X be the amount Anna had originally', 'PIT': 'new definition'},
	{'index: 1, 'text': 'She spent X*1/4.', 'PIT': 'lemma'},
	{'index: 2, 'text': 'She has X - X*1/4 = 24 left.', 'PIT': 'lemma'},
	{'index: 3, 'text': 'Combining like terms gives X*3/4 = 24.', 'PIT': 'lemma'},
	{'index: 4, 'text': 'Dividing both sides by 3/4 we get X = 32.', 'PIT': 'conclusion'},
	{'index: 5, 'text': 'The answer is 32.', 'PIT': 'conclusion'}
]
```

---

### Example 2 (Knowledge reasoning)

**Input (raw rationales)**: every animal is multicellular each invertebrate is an animal protostomes are invertebrates every arthropod is a protostome insects are arthropods insects are six-legged each lepidopteran is an insect butterflies are lepidopterans each painted lady is a butterfly rex is a painted lady  

**Output**:
```
[
	{'index': 0, 'text': 'Every animal is multicellular.', 'PIT': 'rule/explicit-knowledge-claim'},
	{'index': 1, 'text': 'Each invertebrate is an animal.', 'PIT': 'rule/explicit-knowledge-claim'},
	{'index': 2, 'text': 'Protostomes are invertebrates.', 'PIT': 'rule/explicit-knowledge-claim'},
	{'index': 3, 'text': 'Every arthropod is a protostome.', 'PIT': 'rule/explicit-knowledge-claim'},
	{'index': 4, 'text': 'Insects are arthropods.', 'PIT': 'rule/explicit-knowledge-claim'},
	{'index': 5, 'text': 'Insects are six-legged.', 'PIT': 'rule/explicit-knowledge-claim'},
	{'index': 6, 'text': 'Each lepidopteran is an insect.', 'PIT': 'rule/explicit-knowledge-claim'},
	{'index': 7, 'text': 'Butterflies are lepidopterans.', 'PIT': 'rule/explicit-knowledge-claim'},
	{'index': 8, 'text': 'Each painted lady is a butterfly.', 'PIT': 'rule/explicit-knowledge-claim'},
	{'index': 9, 'text': 'Rex is a painted lady.', 'PIT': 'conclusion'}
]
```

---

Now apply this process to the following question and rationales:
**Question**: <insert question here>  
**Rationales (raw)**: <insert unsegmented rationales here>