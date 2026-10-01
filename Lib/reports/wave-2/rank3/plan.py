import json,collections,sys
D='/home/goblin/.claude/jobs/06995e68/tmp/wave2/dump_head.jsonl'
MOD='Lib.Geometry.Manifold.Whitney.RankThreeModel'
PIECES={
 'GraphMotion':[(44,465)],
 'Model':[(466,611),(2490,2511),(2596,2606),(2889,2926)],
 'SheetRetiming':[(936,1089),(2233,2262)],
 'SheetCorrection':[(1192,1361)],
 'TangentAdaptedChart':[(728,935),(1090,1191)],
 'CorrectedCoordinates':[(1362,1974)],
 'SheetRecognition':[(2173,2232),(2358,2489)],
 'SheetParametrizedChart':[(1975,2172),(2263,2357),(2513,2595)],
 'CompatibleChart':[(2608,2738),(2927,3002)],
 'ModelGraphMotion':[(612,727),(2739,2837)],
 'IntersectionRemoval':[(2838,2888)],
 'Cancellation':[(3003,3100)],
}
rows=[json.loads(l) for l in open(D)]
mine={r['name']:r for r in rows if r['module']==MOD}
def piece_of(line):
    for p,rs in PIECES.items():
        for a,b in rs:
            if a<=line<=b: return p
assign={n:piece_of(r['range'][0]) for n,r in mine.items() if r['range']}
un=[n for n,p in assign.items() if p is None]
if un: print('UNASSIGNED',un); sys.exit(1)
def parent(n):
    parts=n.split('.')
    for i in range(len(parts)-1,0,-1):
        p='.'.join(parts[:i])
        if p in assign: return p
full=dict(assign)
for n in mine:
    if n not in full:
        p=parent(n)
        if p: full[n]=assign[p]
deps=collections.defaultdict(set)
for n,r in mine.items():
    if n not in full: continue
    for u in r['uses']:
        if u in full and full[u]!=full[n]: deps[full[n]].add(full[u])
for p in PIECES: print(p,'->',sorted(deps[p]))
def reach(p,seen):
    for q in deps[p]:
        if q not in seen: seen.add(q); reach(q,seen)
    return seen
for p in PIECES:
    if p in reach(p,set()): print('CYCLE',p)
cnt=collections.Counter(assign.values()); print(dict(cnt), sum(cnt.values()))
for p in PIECES:
    with open(f'{sys.argv[1]}/stay_{p}.txt','w') as f:
        f.write('\n'.join(sorted(n for n,q in assign.items() if q!=p))+'\n')
json.dump(assign,open(f'{sys.argv[1]}/assign.json','w'),indent=0)
