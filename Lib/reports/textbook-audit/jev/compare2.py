#!/usr/bin/env python3
"""Turn the ten criteria (results2.jsonl) into A–D verdicts and compare with the auditors."""
import json, os, re, glob, collections, itertools, random
D = os.path.dirname(os.path.abspath(__file__)); A = os.path.join(D, '..')
audit = json.load(open(A + '/audit.json')); ORD = {'A': 0, 'B': 1, 'C': 2, 'D': 3}
rows = [json.loads(l) for l in open(D + '/results2.jsonl') if l.strip()]
rows = [r for r in rows if 'answers' in r['response'] and r['path'] in audit]
def vec(r):
    a = r['response']['answers']
    return {k: (a[k]['score'] if a[k]['type'] == 'score' else a[k]['noul']) for k in a}
X = {r['path']: vec(r) for r in rows}; Y = {r['path']: audit[r['path']]['verdict'] for r in rows}
CRIT = list(next(iter(X.values())).keys())

def rule(v):
    """The rubric, read off the ten answers; no fitted numbers."""
    if v['redundant_with_mathlib'] >= 0.6 or (v['proof_specific'] >= 0.6 and v['generality'] >= 2.0): return 'D'
    if v['generality'] >= 1.5 or v['project_vocabulary'] >= 0.5 or v['single_topic'] < 0.4 or v['proof_specific'] >= 0.5: return 'C'
    if min(v['cites_textbook'], v['docstring_accurate'], v['docstrings_complete'], v['names_standard'], v['preamble_clean']) >= 0.5 and v['generality'] < 0.8: return 'A'
    return 'B'

def auc(pairs):
    pos = [p for l, p in pairs if l]; neg = [p for l, p in pairs if not l]
    return sum((p > q) + 0.5 * (p == q) for p in pos for q in neg) / (len(pos) * len(neg)) if pos and neg else float('nan')

def report(pred, name):
    n = len(pred); ag = sum(pred[p] == Y[p] for p in pred); adj = sum(abs(ORD[pred[p]] - ORD[Y[p]]) <= 1 for p in pred)
    conf = collections.Counter((Y[p], pred[p]) for p in pred)
    L = [f'### {name}', '', f'exact {ag}/{n} = {ag/n:.0%}; within one letter {adj}/{n} = {adj/n:.0%}', '', '| auditors \\ Jev | A | B | C | D |', '|---|---:|---:|---:|---:|']
    L += [f'| {h} | ' + ' | '.join(str(conf[(h, j)]) for j in 'ABCD') + ' |' for h in 'ABCD']
    return L, ag / n

# fitted variant: ordinal thresholds on a weighted sum, weights from a coarse grid, 5-fold CV
random.seed(0); paths = sorted(X); random.shuffle(paths); folds = [paths[i::5] for i in range(5)]
SIGN = {'cites_textbook': -1, 'docstring_accurate': -1, 'docstrings_complete': -1, 'names_standard': -1, 'generality': 1, 'project_vocabulary': 1, 'single_topic': -1, 'preamble_clean': -1, 'redundant_with_mathlib': 1, 'proof_specific': 1}
def score(v, w): return sum(w[k] * SIGN[k] * (v[k] / 3 if k == 'generality' else v[k]) for k in CRIT)
def thresholds(tr, w):
    """Three 1-D scans on the sorted scores: A|rest, AB|CD, ABC|D."""
    s = sorted((score(X[p], w), ORD[Y[p]]) for p in tr); th = []
    for cut in (1, 2, 3):
        best = (-1, 0.0)
        for i in range(len(s) + 1):
            t = s[i][0] if i < len(s) else s[-1][0] + 1
            ok = sum((y >= cut) == (x >= t) for x, y in s)
            if ok > best[0]: best = (ok, t)
        th.append(best[1])
    return th
def predict(v, w, th):
    x = score(v, w); return 'A' if x < th[0] else 'B' if x < th[1] else 'C' if x < th[2] else 'D'
def fit(tr):
    """Coordinate ascent over integer weights in {0,1,2}, three passes."""
    w = {k: 1 for k in CRIT}; th = thresholds(tr, w)
    def acc(w, th): return sum(predict(X[p], w, th) == Y[p] for p in tr)
    cur = acc(w, th)
    for _ in range(3):
        for k in CRIT:
            for cand in (0, 1, 2):
                w2 = dict(w); w2[k] = cand; th2 = thresholds(tr, w2); a = acc(w2, th2)
                if a > cur: w, th, cur = w2, th2, a
    return w, th
cv_pred = {}
for i, te in enumerate(folds):
    tr = [p for f in folds if f is not te for p in f]; w, th = fit(tr)
    for p in te: cv_pred[p] = predict(X[p], w, th)
    print('fold', i, 'weights', {k: v for k, v in w.items() if v}, 'thresholds', [round(t, 2) for t in th], flush=True)
w_all, th_all = fit(paths); print('weights on all data', {k: v for k, v in w_all.items() if v}, flush=True)

L = ['# Jev, second run: ten criteria per file, verdict computed by code — 2026-09-20', '',
     f'Files: {len(rows)}; model {rows[0]["response"]["model"]}; input tokens {sum(r["response"]["usage"]["input_tokens"] for r in rows):,}. Questions in `classify2.py` (state adds per-statement [doc]/[nodoc] tags, docstring coverage, universe pins, `Type*` vs `Type` binder counts, citation facts). Answers `results2.jsonl`.', '',
     '## Per-criterion signal against the auditors', '',
     'AUC of each criterion as a detector of the auditors\' verdict being C-or-D (0.5 = no signal; criteria signed so that higher = worse):', '',
     '| criterion | AUC vs C-or-D | AUC vs D | mean (A files) | mean (B) | mean (C) | mean (D) |', '|---|---:|---:|---:|---:|---:|---:|']
for k in CRIT:
    pairs = [(ORD[Y[p]] >= 2, SIGN[k] * X[p][k]) for p in X]; pd = [(Y[p] == 'D', SIGN[k] * X[p][k]) for p in X]
    means = [sum(X[p][k] for p in X if Y[p] == h) / max(1, sum(1 for p in X if Y[p] == h)) for h in 'ABCD']
    L.append(f'| {k} | {auc(pairs):.2f} | {auc(pd):.2f} | ' + ' | '.join(f'{m:.2f}' for m in means) + ' |')
L += ['', '## Verdicts', '']
r1, a1 = report({p: rule(X[p]) for p in X}, 'Rubric rule over the ten answers (no fitted numbers; `rule()` in compare2.py)'); L += r1 + ['']
r2, a2 = report(cv_pred, 'Weighted sum with thresholds, weights and thresholds fitted per fold (5-fold cross-validation, predictions on held-out folds)'); L += r2 + ['']
one = {json.loads(l)['path']: json.loads(l)['response']['answers']['verdict']['choice'] for l in open(D + '/results.jsonl') if l.strip()}
r0, a0 = report({p: one[p] for p in X if p in one}, 'First run for comparison: one direct verdict question'); L += r0 + ['']
L += ['## Reading', '', f'- direct question {a0:.0%} → rubric rule {a1:.0%} → cross-validated fit {a2:.0%} exact agreement with the auditors (chance for the auditors\' letter distribution is about {sum((collections.Counter(Y.values())[h]/len(Y))**2 for h in "ABCD"):.0%}; the auditors\' own inter-rater agreement on the `ModuleCat.{{0}} ℤ` pin was two groups C, one group B).',
      '- The fitted weights (printed by the script) say which criteria carry the verdict; a weight of 0 means the criterion adds nothing beyond the others on this data.']
open(D + '/JEV2.md', 'w').write('\n'.join(L) + '\n'); print('\n'.join(L))
