import json, re, sys, collections
D='/home/goblin/.claude/jobs/06995e68/tmp/wave2/dump_head.jsonl'
MOD='Lib.Geometry.Manifold.Morse.Cubic'
rows=[json.loads(l) for l in open(D)]
byname={}
for r in rows: byname.setdefault(r['name'],r)
cub={r['name']:r for r in rows if r['module']==MOD}
print('constants in module:',len(cub), 'ranged:',sum(1 for r in cub.values() if r['range']))
# external users
ext=collections.defaultdict(set)   # cubic const -> set of (module) of external users
for r in rows:
    if r['module']==MOD: continue
    for u in r['uses']:
        if u in cub:
            ext[u].add(r['module'])
print('cubic constants used directly outside module:',len(ext))
mods=collections.Counter()
for c,ms in ext.items():
    for m in ms: mods[m]+=1
for m,n in sorted(mods.items()): print('  ',m,n)
# backward closure within cubic from Lib externals
def closure(seed):
    seen=set(seed); stack=list(seed)
    while stack:
        c=stack.pop()
        for u in cub[c]['uses']:
            if u in cub and u not in seen:
                seen.add(u); stack.append(u)
    return seen
libseed={c for c,ms in ext.items() if any(m.startswith('Lib.') for m in ms)}
hopfseed={c for c,ms in ext.items() if any(not m.startswith('Lib.') for m in ms)}
libcl=closure(libseed); hopfcl=closure(hopfseed)
print('Lib-needed closure size:',len(libcl),' Hopf/Solution-needed closure size:',len(hopfcl))
ranged=sorted([r for r in cub.values() if r['range']], key=lambda r:r['range'][0])
def parent(n):
    # map to ranged parent: name prefix
    return n
with open(sys.argv[1],'w') as f:
    for r in ranged:
        tag=('L' if r['name'] in libcl else '-')+('H' if r['name'] in hopfcl else '-')
        f.write(f"{r['range'][0]:5d}-{r['range'][2]:5d} {tag} {r['kind']:9s} {r['name']}\n")
print('Lib-needed ranged:',sum(1 for r in ranged if r['name'] in libcl),'of',len(ranged))
print('free (neither):',sum(1 for r in ranged if r['name'] not in libcl and r['name'] not in hopfcl))
# rangeless needed
for r in cub.values():
    if not r['range'] and r['name'] in libcl: print('rangeless lib-needed:',r['name'])
