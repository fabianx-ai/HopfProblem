"""Declaration blocks of the dead set: docstring/attribute lines above the dump range + the range.
blocks.py ROOT DEADSET_OUT -> json list of {piece,name,start,end,lines} (1-based inclusive)."""
import json, sys
root, out = sys.argv[1], sys.argv[2]
P = root + '/Lib/Topology/Dimension/CubeBoundaryThreeCells/'
res = []
for l in open(out):
    t = l.split()
    if len(t) != 5: continue
    piece, kind, name, s, e = t[0], t[1], t[2], int(t[3]) - 1, int(t[4]) - 1  # deadset.out printed range+1; Lean ranges are 1-based and include docstring/attributes
    L = open(P + piece + '.lean').read().split('\n')
    a = s  # 1-based first line (docstring)
    assert L[a - 1].startswith('/--'), (name, L[a-1])
    # extend upward over a docstring /-- ... -/ and attribute / `set_option ... in` lines
    while True:
        prev = L[a - 2]
        if prev.rstrip().endswith('-/'):
            b = a - 1
            while not L[b - 1].lstrip().startswith('/--'):
                b -= 1
                assert not L[b - 1].lstrip().startswith('/-!'), (name, b)
            a = b
        elif prev.startswith('@[') or (prev.startswith('set_option') and prev.rstrip().endswith(' in')):
            a -= 1
        else:
            break
    assert a == s, (name, a, s)
    res.append(dict(piece=piece, name=name, start=a, end=e, lines=L[a - 1:e]))
json.dump(res, sys.stdout, ensure_ascii=False, indent=0)
