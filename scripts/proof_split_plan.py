#!/usr/bin/env python3
"""proof_split_plan: split every Hopf/ module into a stock part (stays) and a proof part (Hopf/Proof/).

CHARGED adapter for the HopfProblem repository around lean-agent-ide's FREE `dump`, `split_module`
and `envdiff`. Classification: a declaration stays iff its name matches scripts/lib_stock_prefixes.txt
AND its dependency closure inside Hopf/ contains only such declarations (iterated). Everything else
moves to Hopf/Proof/<same path>. Modules with no staying declaration move wholesale (git mv).
Imports: stock chain and proof chain follow the original linear import order; each proof module imports
its own stock module. Writes plan.json and one receipt per module under Lib/reports/proof-split/.

Usage: python3 scripts/proof_split_plan.py --dump <dump.jsonl> [--apply]
"""
import json, re, sys, os, subprocess, argparse, collections
sys.path.insert(0, os.path.join(os.path.dirname(__file__)))
import lib_stock_census as C

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TOOL = '/home/goblin/lean-agent-ide/tools/split_module.py'
ap = argparse.ArgumentParser(); ap.add_argument('--dump', required=True); ap.add_argument('--apply', action='store_true')
a = ap.parse_args()
prefixes = C.load_prefixes(os.path.join(ROOT, 'scripts/lib_stock_prefixes.txt'))
rows = {r['name']: r for r in map(json.loads, open(a.dump))}
hopf = {n: r for n, r in rows.items() if r['module'].startswith('Hopf.') and r['module'] != 'Hopf.LibShims'}
withrange = {n for n, r in hopf.items() if r['range']}
def parent(n):
    if n in withrange: return n
    parts = n.split('.')
    for k in range(len(parts) - 1, 0, -1):
        p = '.'.join(parts[:k])
        if p in withrange and rows[p]['module'] == rows[n]['module']: return p
    m = re.match(r'_private\.[\w.₀-₉]+?\.0\.(.*)', n)
    if m and m.group(1) in withrange: return m.group(1)
    return None
def path(mod): return mod.replace('.', '/') + '.lean'
def short(n):
    n = re.sub(r'^_private\.[\w.₀-₉]+?\.0\.', '', n)
    return n[len('Mathoverflow1973.'):] if n.startswith('Mathoverflow1973.') else n
stock = {n for n in withrange if any(C.match_entry(e, path(hopf[n]['module']), short(n)) for e in prefixes)}
deps = collections.defaultdict(set)
for n, r in hopf.items():
    p = parent(n)
    if p is None: continue
    for u in r['uses']:
        if u in hopf:
            q = parent(u)
            if q and q != p: deps[p].add(q)
keep = set(stock); changed = True
while changed:
    changed = False
    for p in list(keep):
        if any(q not in keep for q in deps[p]): keep.discard(p); changed = True
demoted = stock - keep
# chain order from the import graph (each module imports LibShims and one predecessor)
mods = sorted({r['module'] for r in hopf.values()})
imports = {}; other_imports = {}
for m in mods:
    src = open(os.path.join(ROOT, path(m)), encoding='utf-8').read()
    allimp = re.findall(r'^import ([\w.]+)$', src, re.M)
    imports[m] = [x for x in allimp if x.startswith('Hopf.') and x != 'Hopf.LibShims']
    other_imports[m] = [x for x in allimp if not x.startswith('Hopf.')]
# private constants used by a declaration of the other class must lose `private`
expose = collections.defaultdict(set)
for n, r in hopf.items():
    p = parent(n)
    if p is None: continue
    for u in r['uses']:
        if u.startswith('_private.') and u in withrange:
            if (u in keep) != (p in keep): expose[rows[u]['module']].add(u)
# Lib modules used by each module's declarations (by class)
lib_used = collections.defaultdict(lambda: {'keep': set(), 'move': set()})
for n, r in hopf.items():
    p = parent(n)
    if p is None: continue
    c = 'keep' if p in keep else 'move'
    for u in r['uses']:
        if u in rows and rows[u]['module'].startswith('Lib.'): lib_used[r['module']][c].add(rows[u]['module'])
order = []; rem = set(mods)
while rem:
    nxt = [m for m in rem if all(i in order or i not in mods for i in imports[m])]
    if not nxt: sys.exit('cycle in Hopf imports?')
    order.extend(sorted(nxt)); rem -= set(nxt)
def proof_mod(m): return 'Hopf.Proof.' + m[len('Hopf.'):]
plan = {'order': order, 'modules': {}}
prev_keep = None; prev_move = None
for m in order:
    names = [n for n in withrange if hopf[n]['module'] == m]
    k = sorted(n for n in names if n in keep); mv = sorted(n for n in names if n not in keep)
    seen = [x for mm in order[:order.index(m) + 1] for x in other_imports[mm]]
    union = sorted(set(seen), key=seen.index)
    entry = {'keep': k, 'move': mv, 'demoted': sorted(n for n in names if n in demoted), 'expose': sorted(expose[m]),
             'keep_extra_imports': [x for x in union if x not in other_imports[m]] + sorted(lib_used[m]['keep'] - set(union)),
             'move_extra_imports': [x for x in union if x not in other_imports[m]] + sorted((lib_used[m]['keep'] | lib_used[m]['move']) - set(union)),
             'keep_path': path(m) if k else None, 'move_path': path(proof_mod(m)), 'move_module': proof_mod(m),
             'wholesale': not k, 'keep_import': prev_keep, 'move_imports': ([m] if k else []) + ([prev_move] if prev_move else [])}
    plan['modules'][m] = entry
    if k: prev_keep = m
    prev_move = proof_mod(m)
os.makedirs(os.path.join(ROOT, 'Lib/reports/proof-split'), exist_ok=True)
json.dump(plan, open(os.path.join(ROOT, 'Lib/reports/proof-split/plan.json'), 'w'), indent=1)
print('stock', len(stock), 'keep', len(keep), 'demoted', len(demoted))
for m in order:
    e = plan['modules'][m]; print(f"  {m:32s} keep {len(e['keep']):5d} move {len(e['move']):5d} demoted {len(e['demoted']):4d} expose {len(e['expose'])} +imports {len(e['keep_extra_imports'])}/{len(e['move_extra_imports'])} {'WHOLESALE' if e['wholesale'] else ''}")
if not a.apply: sys.exit(0)

def rewrite_imports(p, drop, add):
    src = open(p, encoding='utf-8').read().split('\n')
    out = []; inserted = False
    for l in src:
        mm = re.match(r'^import (Hopf\.[\w.]+)$', l)
        if mm and mm.group(1) in drop:
            if not inserted:
                out.extend(f'import {x}' for x in add); inserted = True
            continue
        out.append(l)
    if not inserted and add:
        idx = max(i for i, l in enumerate(out) if l.startswith('import ')) + 1
        out[idx:idx] = [f'import {x}' for x in add]
    open(p, 'w', encoding='utf-8').write('\n'.join(out))

for m in order:
    e = plan['modules'][m]; src = os.path.join(ROOT, path(m)); dst = os.path.join(ROOT, e['move_path'])
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    drop = set(imports[m])
    if e['wholesale']:
        subprocess.run(['git', '-C', ROOT, 'mv', path(m), e['move_path']], check=True)
        rewrite_imports(dst, drop, e['move_imports'] + e['move_extra_imports'])
        json.dump({'module': m, 'wholesale': True, 'moved_to': e['move_module']}, open(os.path.join(ROOT, f'Lib/reports/proof-split/{m}.json'), 'w'))
        print(f'{m}: moved wholesale to {e["move_module"]}')
        continue
    stayf = os.path.join(ROOT, f'Lib/reports/proof-split/{m}.stay.txt'); open(stayf, 'w').write('\n'.join(e['keep']) + '\n')
    doc = f"/-! Proof-specific part of `{m}` (split by lean-agent-ide `split_module`); the stock part that is\nstill to be moved into `Lib/` stays in `{path(m)}`. Declarations, names and namespaces are unchanged. -/"
    exposef = os.path.join(ROOT, f'Lib/reports/proof-split/{m}.expose.txt'); open(exposef, 'w').write('\n'.join(e['expose']) + '\n')
    subprocess.run(['python3', TOOL, '--dump', a.dump, '--module', m, '--source', src, '--stay', stayf, '--expose', exposef,
                    '--keep-out', src, '--move-out', dst, '--move-doc', doc,
                    '--receipt', os.path.join(ROOT, f'Lib/reports/proof-split/{m}.json')], check=True)
    rewrite_imports(src, drop, ([e['keep_import']] if e['keep_import'] else []) + e['keep_extra_imports'])
    rewrite_imports(dst, drop, e['move_imports'] + e['move_extra_imports'])
    subprocess.run(['git', '-C', ROOT, 'add', e['move_path']], check=True)
# consumers outside Hopf/
for f in ['Solution.lean', 'Hopf.lean']:
    p = os.path.join(ROOT, f)
    if os.path.exists(p):
        s = open(p, encoding='utf-8').read()
        for m in order:
            if plan['modules'][m]['wholesale']: s = re.sub(rf'^import {re.escape(m)}$', f'import {proof_mod(m)}', s, flags=re.M)
        open(p, 'w', encoding='utf-8').write(s)
print('applied')
