You are a logical annotator. Your task has TWO parts: 

1. **Segmentation**: Split the given text into atomic statements, each containing exactly one logical move. Apply this to both:
	•	The problem description (if any exists in the input).
	•	The rationales (solution steps or reasoning text).
	> If no explicit problem description is provided (the input only has raw rationales), just segment the rationales.
2. **PIT Tagging**: Assign a proof-intent tag (PIT) to each statement. 

Available PIT tags:
- premise (facts from the question/problem statement)
- question — the final question being asked in the problem statement.
- new definition (introducing variables or concepts)
- rule/explicit-knowledge-claim (general truths, background knowledge)
- implicit assumption resurfacing (unstated but necessary assumptions made explicit)
- lemma (derived intermediate steps, calculations, simplifications)
- conclusion (final step or statement that delivers the answer)

### Output Format:
Produce a single JSON list of objects:
```
[
  {'index': 0, 'text': `<statement0>`, 'PIT': `<tag>`},
  {'index': 1, 'text': `<statement1>`, 'PIT': `<tag>`},
  ...
]
```
	•	Maintain order: problem description (if any) first, then rationales.
	•	Use premise for factual parts of the description, and question for the final query.
	•	If no description exists, begin directly with the rationale statements.
---

### Example 1 (Math word problem)

**Question**: Anna spent 1/4 of her money, and now she has $24 left. How much did she have originally?  
**Rationales (raw)**: Let X be the amount Anna had originally she spent X*1/4 and has X - X*1/4 = 24 left combining like terms gives X*3/4 = 24 dividing both sides by 3/4 we get X = 32 so the answer is 32

**Output**:
```
[
  {"index": 0, "text": "Anna spent 1/4 of her money.", "PIT": "premise"},
  {"index": 1, "text": "Anna has $24 left.", "PIT": "premise"},
  {"index": 2, "text": "How much did she have originally?", "PIT": "question"},
  {"index": 3, "text": "Let X be the amount Anna had originally.", "PIT": "new definition"},
  {"index": 4, "text": "She spent X * 1/4.", "PIT": "lemma"},
  {"index": 5, "text": "She has X - X*1/4 = 24 left.", "PIT": "lemma"},
  {"index": 6, "text": "Combining like terms gives X*3/4 = 24.", "PIT": "lemma"},
  {"index": 7, "text": "Dividing both sides by 3/4 gives X = 32.", "PIT": "conclusion"},
  {"index": 8, "text": "The answer is 32.", "PIT": "conclusion"}
]
```

---

### Example 2 (Knowledge reasoning)

**Input (raw)**: {"context": "Every animal is multicellular. Each invertebrate is an animal. Protostomes are invertebrates. Every arthropod is a protostome. Each arthropod is not bony. Insects are arthropods. Insects are six-legged. Each lepidopteran is an insect. Every whale is bony. Butterflies are lepidopterans. Each painted lady is a butterfly. Rex is a painted lady."
"query": Rex is not bony, "answer": "True"}

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
	{'index': 9, 'text': 'Rex is a painted lady.', 'PIT': 'rule/explicit-knowledge-claim'},
	{'index': 10, 'text': 'Rex is not bony', 'PIT': 'conclusion'}
]
```

---

Now apply this process to the following question and rationales:
**Question**: <insert question here>  
**Rationales (raw)**: <insert unsegmented rationales here>