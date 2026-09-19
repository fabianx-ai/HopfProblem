#!/usr/bin/env python3
"""Compare Jev's answers (results.jsonl) with the ten auditors' entries (audit.json, group-*.log)."""
import json, re, os, glob, collections
D = os.path.dirname(os.path.abspath(__file__)); A = os.path.join(D, '..')
audit = json.load(open(A + '/audit.json'))
# keyword labels from the auditors' finding lines, per file
KW = {
 'residue': re.compile(r'finrank|Mathoverflow1973|W4W1|native|SixSphere|Threefold|_mo1973|dimension-6|index[- ]2|index[- ]3|project (data|object|vocabulary)', re.I),
 'docs_stale': re.compile(r'promis|stale|does not exist|do not exist|lives in|live in|elsewhere|nowhere|describes (another|a different)|not among|exists nowhere|is in [A-Z]', re.I),
 'multi_topic': re.compile(r'unrelated|monolith|mixes|mixed with|topics|split (it|out|by)|namespaces|subjects', re.I),
 'mathlib_has': re.compile(r'Mathlib (already )?(has|provides|already)|already (has|in Mathlib|exists)|duplicates? Mathlib|Mathlib\'s [`A-Za-z]|exists in Mathlib|verbatim cop', re.I),
 'pinned': re.compile(r'ModuleCat\.\{0\}|AddCommGrpCat\.\{0\}|TopCat\.\{0\}|Category\.\{0\}|universe[- ]0|universe `?Type|: Type\b|pinned|specialis', re.I),
}
findings = {}
for g in glob.glob(A + '/group-*.log'):
    txt = open(g, encoding='utf-8').read()
    for m in re.finditer(r'^## (\S+).*?\n(.*?)(?=^## |\Z)', txt, re.S | re.M):
        findings[m.group(1)] = m.group(2)
labels = {p: {k: bool(r.search(f)) for k, r in KW.items()} for p, f in findings.items()}
rows = [json.loads(l) for l in open(D + '/results.jsonl') if l.strip()]
ORD = {'A': 0, 'B': 1, 'C': 2, 'D': 3}
conf = collections.Counter(); n = agree = adj = 0; hi = hi_agree = 0; toks = 0
score_gap = []; nouls = {k: [] for k in KW}
for r in rows:
    p = r['path']; a = r['response'].get('answers');
    if not a or p not in audit: continue
    toks += r['response']['usage']['input_tokens']
    h = audit[p]['verdict']; j = a['verdict']['choice']; c = a['verdict']['confidence']
    n += 1; conf[(h, j)] += 1; agree += (h == j); adj += (abs(ORD[h] - ORD[j]) <= 1)
    if c >= 0.5: hi += 1; hi_agree += (h == j)
    score_gap.append(a['readiness']['score'] - ORD[h])
    for k in KW: nouls[k].append((labels.get(p, {}).get(k, False), a[k]['noul']))
L = ['# Jev (TypeSafe System One, `jev-1.13.0`) against the ten auditors — 2026-09-20', '',
     f'Files compared: {n}; input tokens: {toks:,}. Script `classify.py` (state = path, module docstring, preamble, statement heads, counted facts; 7 questions per file), answers `results.jsonl`.', '',
     '## Verdict letter', '',
     f'- exact agreement: {agree}/{n} = {agree/n:.0%}; within one letter: {adj}/{n} = {adj/n:.0%}',
     f'- at Jev confidence ≥ 0.5 ({hi} files): exact agreement {hi_agree}/{hi} = {hi_agree/max(hi,1):.0%}',
     f'- mean of (Jev readiness score − auditor ordinal): {sum(score_gap)/len(score_gap):+.2f} (0 = same scale; negative = Jev more lenient)', '',
     '| auditors \\ Jev | A | B | C | D |', '|---|---:|---:|---:|---:|']
for h in 'ABCD': L.append(f'| {h} | ' + ' | '.join(str(conf[(h, j)]) for j in 'ABCD') + ' |')
L += ['', '## Yes/no judgments against keyword labels from the auditors\' findings', '',
      'Labels are keyword matches on the finding lines (approximate). For each judgment: how often the auditors\' findings mention it, Jev\'s mean probability when they do and when they do not, and a threshold-0.5 accuracy.', '',
      '| judgment | auditors mention it | Jev mean p (mentioned) | Jev mean p (not) | accuracy@0.5 |', '|---|---:|---:|---:|---:|']
for k, v in nouls.items():
    pos = [p for l, p in v if l]; neg = [p for l, p in v if not l]
    acc = sum((p >= 0.5) == l for l, p in v) / len(v)
    L.append(f'| {k} | {len(pos)}/{len(v)} | {sum(pos)/max(len(pos),1):.2f} | {sum(neg)/max(len(neg),1):.2f} | {acc:.0%} |')
# biggest disagreements
dis = sorted(((abs(ORD[audit[r["path"]]["verdict"]] - ORD[r["response"]["answers"]["verdict"]["choice"]]), r["path"], audit[r["path"]]["verdict"], r["response"]["answers"]["verdict"]["choice"], r["response"]["answers"]["verdict"]["confidence"]) for r in rows if r["response"].get("answers") and r["path"] in audit), reverse=True)
L += ['', '## Two-letter disagreements', '', '| file | auditors | Jev | Jev confidence |', '|---|---|---|---:|']
L += [f'| `{p}` | {h} | {j} | {c:.2f} |' for d, p, h, j, c in dis if d >= 2]
open(D + '/JEV.md', 'w').write('\n'.join(L) + '\n'); print('\n'.join(L[:22]))
