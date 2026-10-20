import json,collections
D='/home/goblin/.claude/jobs/06995e68/tmp/wave2/dump_head.jsonl'
MOD='Lib.Geometry.Manifold.Whitney.RankThreeModel'
rows=[json.loads(l) for l in open(D)]
mine={r['name']:r for r in rows if r['module']==MOD}
seeds=set()
for r in rows:
    if r['module']!=MOD and r['module'].startswith('Lib'):
        seeds|={u for u in r['uses'] if u in mine}
need=set(); st=list(seeds)
while st:
    n=st.pop()
    if n in need: continue
    need.add(n); st+= [u for u in mine[n]['uses'] if u in mine]
ranged=[n for n in mine if mine[n]['range']]
free=sorted([n for n in ranged if n not in need], key=lambda n: mine[n]['range'][0])
print('seeds',sorted(seeds)); print('ranged',len(ranged),'needed',len([n for n in ranged if n in need]))
for n in free: print('FREE',mine[n]['range'][0],n)
