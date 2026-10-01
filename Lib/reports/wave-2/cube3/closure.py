import json,sys
M='Lib.Topology.Dimension.CubeBoundaryThreeCells'
D='/home/goblin/.claude/jobs/06995e68/tmp/wave2/dump_head.jsonl'
mod={};uses={}
for l in open(D):
    r=json.loads(l); mod[r['name']]=r['module']; uses[r['name']]=r.get('uses',[])
ours={n for n,m in mod.items() if m==M}
# seeds: uses from constants in other Lib modules
need=set()
users={}
for n,m in mod.items():
    if m.startswith('Lib.') and m!=M:
        for u in uses[n]:
            if u in ours: need.add(u); users.setdefault(u,set()).add(m)
stack=list(need)
while stack:
    x=stack.pop()
    for u in uses.get(x,[]):
        if u in ours and u not in need: need.add(u); stack.append(u)
# Hopf users
hop={}
for n,m in mod.items():
    if not m.startswith('Lib.'):
        for u in uses[n]:
            if u in ours: hop.setdefault(u,set()).add(m)
print('ours',len(ours),'need',len(need))
print('direct Lib users:',sorted({m for s in users.values() for m in s}))
print('direct seeds',len(users))
print('Hopf users',sorted({m for s in hop.values() for m in s}))
ranged=lambda n: True
open('/home/goblin/.claude/jobs/06995e68/tmp/wave2/cube3/need.txt','w').write('\n'.join(sorted(need)))
open('/home/goblin/.claude/jobs/06995e68/tmp/wave2/cube3/notneed.txt','w').write('\n'.join(sorted(ours-need)))
