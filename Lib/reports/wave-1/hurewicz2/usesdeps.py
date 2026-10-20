#!/usr/bin/env python3
"""exact inter-piece dependencies from the dump's `uses` (with _proof_n edges dropped)"""
import json, sys, re
plan = json.load(open(sys.argv[1]))
rows = {}
for l in open(plan['dump']):
    r = json.loads(l)
    if r['module'] == plan['module']: rows[r['name']] = r
def piece_of(ln):
    h = [p['name'] for p in plan['pieces'] if any(a <= ln <= b for a, b in p['ranges'])]
    return h[0] if len(h) == 1 else None
where = {n: piece_of(r['range'][2]) for n, r in rows.items() if r['range']}
# rangeless constants (match_n, _proof_n, ...) : attribute to parent by name prefix
for n, r in rows.items():
    if n not in where:
        base = re.sub(r'\.(_proof_\d+|match_\d+|proof_\d+|_aux_.*|eq_\d+|_eq_\d+)$', '', n)
        where[n] = where.get(base)
deps = {p['name']: {} for p in plan['pieces']}
for n, r in rows.items():
    pn = where.get(n)
    if not pn: continue
    for u in r['uses']:
        if u in rows and where.get(u) and where[u] != pn and not re.search(r'_proof_\d+$', u):
            deps[pn].setdefault(where[u], set()).add(u.split('.')[-1])
for p in plan['pieces']:
    print(p['name'], '<-', {k: sorted(v)[:4] for k, v in deps[p['name']].items()}, '| imports', [m.split('.')[-1] for m in p['imports']])
