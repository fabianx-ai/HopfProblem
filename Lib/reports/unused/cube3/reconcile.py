"""Reconcile the 36 moved declarations between the head dump and the after dump by
demangled name and typeHashPublic, and list the auxiliaries of the moved parents.
reconcile.py HEAD_DUMP AFTER_DUMP"""
import json, re, sys
dm = lambda n: re.sub(r'^_private\..*?\.0\.', '', n)
def load(f):
    r = {}
    for l in open(f):
        d = json.loads(l); r.setdefault(dm(d['name']), []).append(d)
    return r
H, A = load(sys.argv[1]), load(sys.argv[2])
NS = 'TopologicalSpace.CubeBoundaryThree.'
dead = [l.split()[2] for l in open('Lib/reports/unused/cube3/deadset.out') if len(l.split()) == 5]
same = 0
for n in dead:
    h, a = H[NS + n], A[NS + n]
    assert len(h) == 1 and len(a) == 1, n
    h, a = h[0], a[0]
    ok = h['typeHashPublic'] == a['typeHashPublic'] and a['module'] == 'Unused.Topology.Dimension.CubeBoundaryThreeCells'
    same += ok
    if not ok: print('DIFF', n, h['typeHashPublic'], a['typeHashPublic'], a['module'])
    priv = (h['name'].startswith('_private'), a['name'].startswith('_private'))
    if priv[0] != priv[1]: print('visibility', n, 'private before/after', priv)
print(f'moved parents: {len(dead)}, same demangled name + typeHashPublic, now in Unused: {same}')
print('private before:', sum(H[NS+n][0]['name'].startswith('_private') for n in dead), 'private after:', sum(A[NS+n][0]['name'].startswith('_private') for n in dead))
aux = lambda D: {k: [(d['module'].split('.')[-1], d['typeHashPublic']) for d in v] for k, v in D.items()
                 if any(k.startswith(NS + n + '.') for n in dead)}
ha, aa = aux(H), aux(A)
for k in sorted(set(ha) | set(aa)):
    print('aux', k[len(NS):], 'head', ha.get(k), 'after', aa.get(k))
