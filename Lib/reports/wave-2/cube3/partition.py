import json,sys
S='/home/goblin/.claude/jobs/06995e68/tmp/wave2/cube3/'
M='Lib.Topology.Dimension.CubeBoundaryThreeCells'
P='_private.'+M+'.0.'
PIECES=[('Lattice',[(31,129),(1076,1224)]),
 ('Cells',[(130,455),(575,621),(645,757),(759,778)]),
 ('Faces',[(456,573),(623,643),(784,1074)]),
 ('Coverage',[(1226,1406)]),
 ('RelInterior',[(1408,1498)]),
 ('SquareBoundary',[(1500,1827)]),
 ('Separation',[(1829,2337)])]
rows={}
for l in open('/home/goblin/.claude/jobs/06995e68/tmp/wave2/dump_head.jsonl'):
    r=json.loads(l)
    if r['module']==M: rows[r['name']]=r
def piece_of_line(L):
    for p,rs in PIECES:
        for a,b in rs:
            if a<=L<=b: return p
    return None
pc={}
for n,r in rows.items():
    if r.get('range'):
        p=piece_of_line(r['range'][0]); pc[n]=p
        if p is None: print('UNASSIGNED',n,r['range'])
# auxiliaries: assign by parent prefix
def owner(u):
    if u in pc: return pc[u]
    # strip suffixes
    parts=u.split('.')
    for i in range(len(parts)-1,0,-1):
        c='.'.join(parts[:i])
        if c in pc: return pc[c]
    return None
order=[p for p,_ in PIECES]
cross={}; edges=set()
for n,r in rows.items():
    p=owner(n)
    for u in r.get('uses',[]):
        if u in rows:
            q=owner(u)
            if q and p and q!=p:
                edges.add((p,q))
                if order.index(q)>order.index(p): print('BACKEDGE',n,'->',u)
                base=u
                cross.setdefault(base,set()).add(p)
print(sorted(edges))
need_pub=sorted(set(u for u in cross))
privs=[u for u in need_pub if u.startswith(P)]
print('cross-used',len(need_pub),'of which private',len(privs))
for u in privs: print('  ',u[len(P):], rows[u]['kind'], owner(u),'->',sorted(cross[u]))
json.dump({n:p for n,p in pc.items()},open(S+'piece_of.json','w'),indent=0)
