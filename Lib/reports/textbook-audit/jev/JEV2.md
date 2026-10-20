# Jev, second run: ten criteria per file, verdict computed by code — 2026-09-20

Files: 445; model jev-1.13.0; input tokens 1,765,898. Questions in `classify2.py` (state adds per-statement [doc]/[nodoc] tags, docstring coverage, universe pins, `Type*` vs `Type` binder counts, citation facts). Answers `results2.jsonl`.

## Per-criterion signal against the auditors

AUC of each criterion as a detector of the auditors' verdict being C-or-D (0.5 = no signal; criteria signed so that higher = worse):

| criterion | AUC vs C-or-D | AUC vs D | mean (A files) | mean (B) | mean (C) | mean (D) |
|---|---:|---:|---:|---:|---:|---:|
| cites_textbook | 0.37 | 0.50 | 0.14 | 0.21 | 0.41 | 0.17 |
| docstring_accurate | 0.71 | 0.59 | 0.84 | 0.77 | 0.64 | 0.65 |
| docstrings_complete | 0.53 | 0.66 | 0.74 | 0.72 | 0.74 | 0.47 |
| names_standard | 0.77 | 0.57 | 0.82 | 0.77 | 0.61 | 0.62 |
| generality | 0.73 | 0.67 | 1.04 | 1.14 | 1.56 | 1.56 |
| project_vocabulary | 0.68 | 0.63 | 0.18 | 0.20 | 0.33 | 0.41 |
| single_topic | 0.77 | 0.61 | 0.94 | 0.91 | 0.83 | 0.81 |
| preamble_clean | 0.62 | 0.51 | 0.69 | 0.61 | 0.48 | 0.49 |
| redundant_with_mathlib | 0.29 | 0.41 | 0.25 | 0.21 | 0.14 | 0.21 |
| proof_specific | 0.72 | 0.69 | 0.12 | 0.15 | 0.22 | 0.26 |

## Verdicts

### Rubric rule over the ten answers (no fitted numbers; `rule()` in compare2.py)

exact 240/445 = 54%; within one letter 418/445 = 94%

| auditors \ Jev | A | B | C | D |
|---|---:|---:|---:|---:|
| A | 1 | 27 | 14 | 3 |
| B | 1 | 128 | 83 | 3 |
| C | 0 | 47 | 110 | 3 |
| D | 0 | 7 | 17 | 1 |

### Weighted sum with thresholds, weights and thresholds fitted per fold (5-fold cross-validation, predictions on held-out folds)

exact 278/445 = 62%; within one letter 430/445 = 97%

| auditors \ Jev | A | B | C | D |
|---|---:|---:|---:|---:|
| A | 5 | 36 | 4 | 0 |
| B | 7 | 173 | 35 | 0 |
| C | 0 | 58 | 98 | 4 |
| D | 0 | 11 | 12 | 2 |

### First run for comparison: one direct verdict question

exact 192/445 = 43%; within one letter 405/445 = 91%

| auditors \ Jev | A | B | C | D |
|---|---:|---:|---:|---:|
| A | 35 | 9 | 1 | 0 |
| B | 120 | 57 | 37 | 1 |
| C | 27 | 34 | 99 | 0 |
| D | 5 | 6 | 13 | 1 |

## Reading

- direct question 43% → rubric rule 54% → cross-validated fit 62% exact agreement with the auditors (chance for the auditors' letter distribution is about 38%; the auditors' own inter-rater agreement on the `ModuleCat.{0} ℤ` pin was two groups C, one group B).
- The fitted weights (printed by the script) say which criteria carry the verdict; a weight of 0 means the criterion adds nothing beyond the others on this data.
- Weights fitted on all data (coordinate ascent, integer weights 0–2): docstring_accurate 2, names_standard 2, generality 2, project_vocabulary 1, single_topic 1, preamble_clean 1, redundant_with_mathlib 1, proof_specific 1; cites_textbook and docstrings_complete 0. The per-fold weights agree on the first three.
- `cites_textbook` and `redundant_with_mathlib` have AUC below 0.5: Jev's answer to them runs *against* the auditors (C files cite textbooks more often than A files, because the sheaf and Hurewicz files cite Hatcher and Godement and are C for universe pins). These two criteria need facts Jev does not have (Mathlib's contents) or measure something the auditors did not weigh.
- The remaining gap to the auditors is the B/C boundary (58 auditor-C files predicted B, 35 the other way): the auditors' C is often a `ModuleCat.{0} ℤ` or `TopCat.{0}` pin read off one statement, which the sampled statement heads do not always show.
