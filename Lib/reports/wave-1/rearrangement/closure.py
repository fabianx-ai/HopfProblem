import json,collections,sys
D='/home/goblin/.claude/jobs/06995e68/tmp/wave1/dump_head.jsonl'
MOD='Lib.Geometry.Manifold.Morse.Rearrangement'
moved=['MorseCancellation.exists_sheet_arc_tube','MorseCancellation.exists_clean_two_sheet_arc_avoiding',
       'AdaptedWindows.pathConnectedSpace_middle_level','AdaptedWindows.pathConnectedSpace_index_three_upper_level']
rows={}
for l in open(D):
    r=json.loads(l); rows[r['name']]=r
rev=collections.defaultdict(set)
for n,r in rows.items():
    for u in r['uses']: rev[u].add(n)
seed={n for n in rows if any(n==m or n.startswith(m+'.') for m in moved)}
print('seed constants:',sorted(seed))
seen=set(seed); stack=list(seed)
while stack:
    x=stack.pop()
    for y in rev.get(x,()):
        if y not in seen: seen.add(y); stack.append(y)
users=sorted((rows[n]['module'],n) for n in seen-seed)
print('transitive users:',len(users))
libother=[(m,n) for m,n in users if m.startswith('Lib.') and m!=MOD]
print('Lib users outside the module:',libother)
byatt=collections.Counter(m for m,n in users)
for m,c in sorted(byatt.items()): print('  ',m,c)
# also: every constant of the module reachable backwards from any constant of another Lib module must stay
stay=set()
for n,r in rows.items():
    if r['module'].startswith('Lib.') and r['module']!=MOD:
        for u in r['uses']:
            if rows.get(u,{}).get('module')==MOD: stay.add(u)
# close under uses within the module
stack=list(stay)
while stack:
    x=stack.pop()
    for u in rows[x]['uses']:
        if rows.get(u,{}).get('module')==MOD and u not in stay: stay.add(u); stack.append(u)
print('module constants required by other Lib modules (closed):',len(stay),'of',sum(1 for r in rows.values() if r['module']==MOD))
print('moved ∩ required:',sorted(stay & seed))
