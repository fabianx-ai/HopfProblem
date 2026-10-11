"""Rewrite the project import lines of the given modules per plan.json.
Non-project import lines (Mathlib, `import all Mathlib.*`) stay verbatim and in place; retained project
imports keep their position and text; new project imports go after the last retained/removed project line,
sorted. Usage: apply.py MOD [MOD ...]"""
import json, re, os, sys
ROOT = '/home/goblin/hopf-trim'
S = '/home/goblin/.claude/jobs/06995e68/tmp/trim'
plan = json.load(open(os.environ.get('PLAN', S + '/plan.json')))
IMP = re.compile(r'^(public\s+)?import\s+(\S+)\s*$')
for X in sys.argv[1:]:
    p = os.path.join(ROOT, X.replace('.', '/') + '.lean')
    lines = open(p, encoding='utf-8').read().split('\n')
    v = plan[X]; before = set(v['before']); after = v['after']
    pub = 'public ' if v['module'] else ''
    out = []; last = None; kept = set()
    for l in lines:
        m = IMP.match(l)
        if m and m.group(2) in before:
            if m.group(2) in after:
                out.append(l); kept.add(m.group(2))
            last = len(out)
            continue
        out.append(l)
    new = [pub + 'import ' + i for i in sorted(set(after) - kept)]
    if new:
        assert last is not None, X
        out[last:last] = new
    open(p, 'w', encoding='utf-8').write('\n'.join(out))
    print(X, len(before), '->', len(after), 'new:', new)
