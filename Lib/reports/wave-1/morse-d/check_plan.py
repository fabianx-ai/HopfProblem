#!/usr/bin/env python3
"""Check the cut plan against the dump: coverage, backwards closure from other Lib modules,
no Lib piece depending on a Hopf piece, per-piece imports from `uses`, Hopf consumers."""
import json, re, sys, collections
sys.path.insert(0, '/home/goblin/.claude/jobs/06995e68/tmp/wave1/morse-d')
from plan import PIECES, OC, SC, path_of

DUMP = sys.argv[1] if len(sys.argv) > 1 else '/home/goblin/.claude/jobs/06995e68/tmp/wave1/dump_head.jsonl'
MODS = {OC, SC}
UNMANGLE = re.compile(r'^_private\.(?:[^.]+\.)+?\d+\.')
AUX = re.compile(r'\._proof_\d+(?:_\d+)*$|\._simp_\d+(?:_\d+)*$|\.match_\d+(?:_\d+)*$|\.eq_\d+$|\.eq_def$|\._aux_.*$|\.proof_\d+(?:_\d+)*$')

rows = {}          # name -> row (all modules)
by_mod = collections.defaultdict(list)
for l in open(DUMP, encoding='utf-8'):
    r = json.loads(l)
    rows[r['name']] = r
    by_mod[r['module']].append(r['name'])

def user(n): return UNMANGLE.sub('', n)

def parent(n):
    """map an auxiliary constant to its parent declaration name (same module), else itself"""
    m = AUX.search(n)
    while m:
        n = n[:m.start()]
        m = AUX.search(n)
    return n

# ---- plan tables
piece_of = {}      # dump name -> piece module
cls_of_piece = {}
for mod, cls, src, names, doc in PIECES:
    cls_of_piece[mod] = cls
    for short in names:
        cands = [n for n in by_mod[src] if rows[n]['range'] and (n == short or user(n) == short)]
        if len(cands) != 1:
            print('PLAN NAME NOT UNIQUE/FOUND', src, short, cands); sys.exit(1)
        if cands[0] in piece_of:
            print('PLAN NAME TWICE', short); sys.exit(1)
        piece_of[cands[0]] = mod

ranged = {m: [n for n in by_mod[m] if rows[n]['range']] for m in MODS}
for m in MODS:
    missing = [n for n in ranged[m] if n not in piece_of]
    if missing:
        print('UNCOVERED', m, missing); sys.exit(1)
    print(m, 'ranged', len(ranged[m]), 'covered', sum(1 for n in ranged[m] if n in piece_of))

def class_of_name(n):
    p = parent(n)
    if p in piece_of: return cls_of_piece[piece_of[p]]
    return None

# ---- backwards closure from other Lib modules
mine = {n for m in MODS for n in by_mod[m]}
needed = set()
frontier = []
for n, r in rows.items():
    if r['module'].startswith('Lib') and r['module'] not in MODS:
        for u in r['uses']:
            if u in mine and u not in needed:
                needed.add(u); frontier.append((u, n))
first_user = {u: n for u, n in frontier}
queue = list(needed)
while queue:
    u = queue.pop()
    for v in rows[u]['uses']:
        if v in mine and v not in needed:
            needed.add(v); queue.append(v)
needed_decls = {parent(n) for n in needed}
print('backwards closure from other Lib modules:', len(needed_decls), 'declarations')
bad = [n for n in needed_decls if class_of_name(n) == 'hopf']
if bad:
    print('CLOSURE VIOLATION (Hopf-bound but used by Lib):')
    for n in bad: print('  ', n, 'first user', first_user.get(n))
    sys.exit(1)
print('closure ok; kept-for-closure:', sorted(user(n) for n in needed_decls))

# ---- Lib piece must not use Hopf piece
viol = []
for n, mod in piece_of.items():
    if cls_of_piece[mod] != 'lib': continue
    for u in rows[n]['uses']:
        if u in mine and class_of_name(u) == 'hopf':
            viol.append((user(n), user(u)))
if viol:
    print('LIB PIECE USES HOPF PIECE:', viol); sys.exit(1)
print('no Lib piece uses a Hopf piece')

# ---- per-piece imports and internal order
piece_uses_mod = collections.defaultdict(set)   # piece -> set of modules (Lib) or pieces
piece_deps = collections.defaultdict(set)
for n, mod in piece_of.items():
    for u in list(rows[n]['uses']) + [n]:
        if u not in rows: continue
        um = rows[u]['module']
        if um in MODS:
            pu = parent(u)
            if pu in piece_of:
                if piece_of[pu] != mod: piece_deps[mod].add(piece_of[pu])
            else:
                print('  note: aux without parent in plan', n, '->', u)
        elif um.startswith('Lib'):
            piece_uses_mod[mod].add(um)
        elif um.startswith('Hopf'):
            print('  WARNING uses Hopf constant', n, u)
# topological order of pieces
order = []
seen = set()
def visit(p, stack=()):
    if p in seen: return
    if p in stack: print('CYCLE', stack, p); sys.exit(1)
    for q in sorted(piece_deps[p]): visit(q, stack + (p,))
    seen.add(p); order.append(p)
for mod, *_ in PIECES: visit(mod)
print('\npiece order and imports:')
result = {}
for p in order:
    # drop Lib modules already imported transitively by a sibling piece? keep explicit; fine.
    imports = sorted(piece_uses_mod[p]) + sorted(piece_deps[p])
    result[p] = {'class': cls_of_piece[p], 'imports': imports,
                 'names': [n for n, m in piece_of.items() if m == p]}
    print(p, cls_of_piece[p], len(result[p]['names']))
    for i in imports: print('    import', i)

# ---- Hopf consumers of moved (hopf-bound) names
consumers = collections.defaultdict(set)
for n, r in rows.items():
    if r['module'].startswith('Hopf') or r['module'] in ('Solution', 'S6', 'S6Shortcuts', 'Challenge'):
        for u in r['uses']:
            if u in mine and class_of_name(u) == 'hopf':
                consumers[r['module']].add(piece_of[parent(u)])
print('\nHopf consumers of moved names:')
for m in sorted(consumers): print(' ', m, '->', sorted(consumers[m]))
# also Hopf consumers of any of my names (for import completeness)
allcons = collections.defaultdict(set)
for n, r in rows.items():
    if not r['module'].startswith('Lib'):
        for u in r['uses']:
            if u in mine: allcons[r['module']].add(piece_of[parent(u)] if parent(u) in piece_of else '?')
print('\nnon-Lib modules using any of my declarations:')
for m in sorted(allcons): print(' ', m, len(allcons[m]))
json.dump({'order': order, 'pieces': result, 'piece_of': piece_of,
           'needed': sorted(needed_decls), 'consumers': {k: sorted(v) for k, v in consumers.items()}},
          open('/home/goblin/.claude/jobs/06995e68/tmp/wave1/morse-d/plan_resolved.json', 'w'), indent=1)
print('\nwrote plan_resolved.json')
