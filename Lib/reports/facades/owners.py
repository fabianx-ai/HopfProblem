import json
from plan import *
plan = json.load(open(D + '/plan.json'))
own = {}
memo = {}
for X, v in plan.items():
    own[X] = {}
    facs = [i for i, p in old_imports(X) if i in FACS]
    for m, pub, why in v['new']:
        direct = [f for f in facs if m.startswith(f + '.')]
        cover = [f for f in facs if m in exports(old_imps_fn, f, memo)]
        o = (direct or cover)
        assert o, (X, m)
        own[X][m] = o[0]
json.dump(own, open(D + '/owners.json', 'w'), indent=1)
import collections
print(collections.Counter(o for d in own.values() for o in d.values()))
