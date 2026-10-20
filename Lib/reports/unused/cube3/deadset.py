"""Dead set of the seven CubeBoundaryThreeCells pieces over a dump.
A ranged declaration is dead if no constant outside the pieces reaches it backwards
(auxiliaries X._proof_n, X.eq_n, X._simp_..., X.match_n etc. count as part of their
ranged parent X).  Usage: deadset.py DUMP"""
import json, sys
D = sys.argv[1] if len(sys.argv) > 1 else '/home/goblin/.claude/jobs/06995e68/tmp/head3/dump_head.jsonl'
P = 'Lib.Topology.Dimension.CubeBoundaryThreeCells.'
PIECES = ['Lattice','Cells','Faces','Coverage','RelInterior','SquareBoundary','Separation']
rows = {}
for l in open(D):
    r = json.loads(l); rows[r['name']] = r
ours = {n for n, r in rows.items() if r['module'].startswith(P)}
ranged = {n for n in ours if rows[n]['range']}
import re
def strip(n): return re.sub(r'^_private\..*?\.0\.', '', n)
def parent(n):
    if n in ranged: return n
    best = None
    for m in ranged:
        if strip(n).startswith(strip(m) + '.') and (best is None or len(m) > len(best)): best = m
    return best
par = {n: parent(n) for n in ours}
orphans = [n for n in ours if par[n] is None]
# grouped graph on ranged parents
guses = {m: set() for m in ranged}
for n in ours:
    for u in rows[n].get('uses', []):
        if u in ours and par[u] != par[n]: guses[par[n]].add(par[u])
seeds = set(); outside_users = {}
for n, r in rows.items():
    if n in ours: continue
    for u in r.get('uses', []):
        if u in ours:
            seeds.add(par[u]); outside_users.setdefault(par[u], set()).add(r['module'])
live = set(seeds); st = list(seeds)
while st:
    x = st.pop()
    for u in guses[x]:
        if u not in live: live.add(u); st.append(u)
dead = sorted(ranged - live, key=lambda n: (PIECES.index(rows[n]['module'][len(P):]), rows[n]['range'][0]))
short = lambda n: n.split('.')[-1]
print('constants', len(ours), 'ranged', len(ranged), 'orphan auxiliaries', len(orphans))
assert not orphans, orphans
print('live ranged', len(live), 'dead ranged', len(dead))
for n in dead:
    print(rows[n]['module'][len(P):], rows[n]['kind'], short(n), rows[n]['range'][0]+1, rows[n]['range'][2]+1)
# live declarations whose only users in OTHER pieces are dead
print('--- live declarations with other-piece users, where all other-piece users are dead:')
for m in sorted(live):
    pm = rows[m]['module']
    others = {par[n] for n in ours if rows[n]['module'] != pm and any(par.get(u) == m for u in rows[n].get('uses', []) if u in ours)}
    if others and others <= set(dead) and m not in outside_users:
        print(' ', short(m), pm[len(P):], 'used by dead', sorted(short(o) for o in others))
