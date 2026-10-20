"""Apply plan.json: reroute consumers, rewrite Lib.lean, delete facades, write READMEs.
Usage: apply.py [facade ...]  (default: all). Only the given facades are dissolved."""
import json, re, os, sys
R = '/home/goblin/hopf-facades'
D = '/home/goblin/.claude/jobs/06995e68/tmp/facades'
plan = json.load(open(D + '/plan.json'))
FAC = [l.strip() for l in open(D + '/real.txt') if l.strip()]
todo = sys.argv[1:] or FAC
IMP = re.compile(r'^(public\s+)?import\s+(\S+)\s*$')
path = lambda m: os.path.join(R, m.replace('.', '/') + '.lean')

def pieces(f):
    d = path(f)[:-5]
    return sorted(os.path.relpath(os.path.join(dp, x), R)[:-5].replace('/', '.')
                  for dp, _, fs in os.walk(d) for x in fs if x.endswith('.lean'))

def is_module(text): return re.search(r'^module\s*$', text, re.M) is not None

def reroute(X, facs):
    p = path(X) if not X.startswith('Lib.reports') else os.path.join(R, X.replace('.', '/') + '.lean')
    if not os.path.exists(p):  # module names with '-' (reports)
        p = os.path.join(R, X.replace('.', '/') + '.lean')
    text = open(p, encoding='utf-8').read()
    lines = text.split('\n')
    mod = is_module(text)
    have = {IMP.match(l).group(2) for l in lines if IMP.match(l)}
    # modules to add for these facades: plan entries whose module lies in the facade's pieces or region
    entries = plan[X]['new']
    out = []; first = None; removed = []
    for i, l in enumerate(lines):
        m = IMP.match(l)
        if m and m.group(2) in facs:
            removed.append(l)
            if first is None: first = len(out)
            continue
        out.append(l)
    if not removed: return None
    # assign plan entries to the facades of this batch: an entry belongs to the batch if it is
    # a piece of a batch facade or (non-piece) carried by a batch facade's exports
    add = []
    for mname, pub, why in entries:
        owner = entry_owner(X, mname)
        if owner in facs and mname not in have:
            add.append(('public import ' if (pub and mod) else 'import ') + mname)
    add = sorted(set(add), key=lambda s: s.split()[-1])
    out[first:first] = add
    open(p, 'w', encoding='utf-8').write('\n'.join(out))
    return removed, add

OWN = json.load(open(D + '/owners.json')) if os.path.exists(D + '/owners.json') else {}
def entry_owner(X, mname):
    return OWN[X][mname]

def lib_lean(facs):
    p = os.path.join(R, 'Lib.lean'); lines = open(p).read().split('\n')
    have = {IMP.match(l).group(2) for l in lines if IMP.match(l)}
    out = []
    for l in lines:
        m = IMP.match(l)
        if m and m.group(2) in facs:
            out += ['import ' + q for q in pieces(m.group(2)) if q not in have]
            continue
        out.append(l)
    open(p, 'w').write('\n'.join(out))

DOC = re.compile(r'/-!(.*?)-/', re.S)
def delete_facade(f):
    p = path(f); text = open(p, encoding='utf-8').read()
    m = DOC.search(text)
    body = m.group(1).strip('\n') if m else ''
    body = '\n'.join(l for l in body.split('\n'))
    readme = os.path.join(p[:-5], 'README.md')
    assert not os.path.exists(readme)
    ps = pieces(f)
    s = body.rstrip() + '\n\n## Modules\n\n' \
        + 'This directory replaces the former facade module `' + f + '` (deleted; its module docstring is the text\n' \
        + 'above, verbatim). Import the pieces directly:\n\n' + ''.join('* `' + q + '`\n' for q in ps)
    open(readme, 'w', encoding='utf-8').write(s)
    os.remove(p)

if __name__ == '__main__':
    facs = set(todo)
    rep = {}
    for X in plan:
        if X in FAC: continue
        r = reroute(X, facs)
        if r: rep[X] = r
    lib_lean(facs)
    for f in todo: delete_facade(f)
    json.dump(rep, open(D + '/applied-' + ('all' if len(todo) > 1 else todo[0]) + '.json', 'a'), indent=1)
    print(len(rep), 'consumers rerouted for', len(todo), 'facades')
