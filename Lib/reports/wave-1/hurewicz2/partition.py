#!/usr/bin/env python3
"""check that the receipts of a plan partition the module's ranged constants; print the cut table"""
import json, sys
plan = json.load(open(sys.argv[1]))
rows = {}
for l in open(plan['dump']):
    r = json.loads(l)
    if r['module'] == plan['module'] and r['range']: rows[r['name']] = r
seen = {}
print('| piece | lines moved (of the original) | declarations (units) | ranged constants |')
print('|---|---|---|---|')
for p in plan['pieces']:
    rec = json.load(open(f"{sys.argv[2]}/{plan['stem']}_{p['name']}.json"))
    units = [u for u in rec['units'] if u.get('class') == 'move']
    nlines = sum(u['lines'][1] - u['lines'][0] + 1 for u in units)
    ncons = 0
    for u in units:
        for n in u['names']:
            seen.setdefault(n, []).append(p['name']); ncons += 1
    print(f"| `{p['name']}` | {nlines} | {len(units)} | {ncons} |")
missing = [n for n in rows if n not in seen]
dup = {n: v for n, v in seen.items() if len(v) != 1}
extra = [n for n in seen if n not in rows]
print('ranged constants:', len(rows), 'moved once:', sum(1 for n in rows if len(seen.get(n, [])) == 1), 'missing:', missing, 'dup:', dup, 'extra:', extra)
