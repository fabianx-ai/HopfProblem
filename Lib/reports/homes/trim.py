"""Import trim plan for the better-homes modules.

Visibility model (strict, as Lib/reports/facades/plan.py, with the review correction): a module sees its
direct imports plus what they re-export; a `module` file re-exports only its `public import`s, a legacy
file re-exports every import. Non-project modules (Mathlib, packages) are leaves: they never import project
modules, and the dump only records project constants, so U(X) never contains them.
U(X) = defining modules of the constants used by X's declarations (dump `uses`), generated auxiliaries mapped
to their parent; plus names read from the text of #check / #print axioms / `example := @name` files.

For each scope module X (one at a time, in the order given, cumulative):
  need(X) = U(X) ∪ {m : some project file Y ≠ X misses m when X's project imports are removed}
  new(X)  = antichain of need(X) (drop m if another kept import re-exports it, under X's own public flag)
  non-project import lines (Mathlib, `import all Mathlib.*`) are kept verbatim.
Usage: trim.py plan  -> writes plan.json (per module: before, after, reasons)
"""
import json, re, sys, os, collections, functools
ROOT = '/home/goblin/hopf-trim'
S = '/home/goblin/.claude/jobs/06995e68/tmp/trim'
IMP = re.compile(r'^(public\s+)?(meta\s+)?import\s+(all\s+)?(\S+)', re.M)

def strip_comments(s):
    s = re.sub(r'/-.*?-/', '', s, flags=re.S)
    return re.sub(r'--.*', '', s)

def project_files():
    out = {}
    for d, ds, fs in os.walk(ROOT):
        if '/.lake' in d or '/.git' in d: continue
        for f in fs:
            if f.endswith('.lean'):
                rel = os.path.relpath(os.path.join(d, f), ROOT)
                out[rel[:-5].replace('/', '.')] = rel
    return out
FILES = project_files()

INFO = {}
def parse(m):
    if m not in INFO:
        t = strip_comments(open(os.path.join(ROOT, FILES[m]), encoding='utf-8').read())
        is_mod = re.search(r'^module\s*$', t, re.M) is not None
        INFO[m] = (is_mod, [(g.group(4), bool(g.group(1))) for g in IMP.finditer(t)])
    return INFO[m]
def is_module(m): return parse(m)[0]
def proj_imports(m): return [(i, p) for i, p in parse(m)[1] if i in FILES]

# ---- dump
mod_of = {}; uses_of = collections.defaultdict(set)
GEN = re.compile(r'\.(eq_\d+|eq_def|match_\d+|_proof_\d+(_\d+)?|proof_\d+|congr_simp|sizeOf_spec|injEq|inj|_sunfold|_unary|_mutual|splitter|eq_spec|fun_cases|induct|_cstage\d|_lambda_\d+|_closed_\d+|_unsafe_rec)$')
for l in open(os.environ.get('DUMP', S + '/dump_base.jsonl'), encoding='utf-8'):
    r = json.loads(l); mod_of[r['name']] = r['module']; uses_of[r['module']].update(r['uses'])
def parent(n):
    while True:
        m = GEN.search(n)
        if not m: return n
        n = n[:m.start()]
@functools.lru_cache(None)
def U(X):
    out = set()
    for c in uses_of.get(X, ()):
        for n in {c, parent(c)}:
            m = mod_of.get(n)
            if m and m != X: out.add(m)
    p = FILES.get(X)
    if p:
        s = open(os.path.join(ROOT, p), encoding='utf-8').read()
        names = re.findall(r'^#(?:print axioms|check)\s+(\S+)', s, re.M) + \
                re.findall(r'^example\s*:=\s*@([^\s{]+)', s, re.M)
        for n in names:
            m = mod_of.get(n)
            if m and m != X: out.add(m)
    return frozenset(out)

# ---- visibility over an override map {X: [(imp, public)]}
def mk(over):
    def imps(X): return over[X] if X in over else proj_imports(X)
    memo = {}
    def exports(X):
        if X in memo: return memo[X]
        memo[X] = {X}
        s = {X}; legacy = not is_module(X)
        for i, p in imps(X):
            if p or legacy: s |= exports(i)
        memo[X] = s; return s
    def visible(X):
        s = set()
        for i, p in imps(X): s |= exports(i)
        return s
    return imps, exports, visible

ALL = sorted(FILES)
BASE_BAD = {}
def violations(over, only=None):
    imps, exports, visible = mk(over)
    bad = {}
    for Y in (only or ALL):
        miss = set(U(Y)) - visible(Y) - {Y} - BASE_BAD.get(Y, set())
        if miss: bad[Y] = miss
    return bad

def importers_closure(X):
    """project files that can see X under the current graph (all, ignoring visibility) -- candidates."""
    rev = collections.defaultdict(set)
    for Y in ALL:
        for i, _ in proj_imports(Y): rev[i].add(Y)
    seen = set(); st = [X]
    while st:
        z = st.pop()
        for y in rev[z]:
            if y not in seen: seen.add(y); st.append(y)
    return seen

def plan_one(X, over):
    pub = is_module(X)  # module files: every project import public (as before: all were public)
    old = proj_imports(X)
    assert all(p == pub for _, p in old) or not pub, (X, old)
    down = sorted(importers_closure(X))
    need = set(U(X)); why = {m: 'use' for m in need}
    for it in range(100):
        # candidate import list: antichain of need under the candidate graph itself
        cand = sorted(need)
        over2 = dict(over); over2[X] = [(m, pub) for m in cand]
        _, exports, _ = mk(over2)
        keep = list(cand)
        for m in sorted(cand, key=lambda m: len(exports(m))):  # try dropping smallest first
            others = [k for k in keep if k != m]
            cov = set()
            for k in others: cov |= exports(k)
            if m in cov: keep.remove(m)
        over2[X] = [(m, pub) for m in keep]
        bad = violations(over2, down)
        if not bad: return keep, why, over2
        # downstream Y misses m: X must re-export m (only if X previously did, i.e. m visible via X)
        _, oexp, _ = mk(over)
        added = False
        for Y, miss in sorted(bad.items()):
            for m in sorted(miss):
                if m in oexp(X) and m not in need:
                    need.add(m); why[m] = 'reexport:' + Y; added = True
        if not added:
            raise SystemExit('UNRESOLVED %s %s' % (X, sorted(bad.items())[:5]))
    raise SystemExit('no fixpoint ' + X)

if __name__ == '__main__':
    scope = [l.strip() for l in open(S + '/scope.txt') if l.strip()]
    base_bad = violations({}); BASE_BAD.update(base_bad)
    print('base strict violations:', len(base_bad), list(base_bad.items())[:5], file=sys.stderr)
    over = {}; out = {}
    for X in scope:
        keep, why, over = plan_one(X, over)
        out[X] = {'module': is_module(X), 'before': [i for i, _ in proj_imports(X)], 'after': keep,
                  'why': {m: why.get(m, '') for m in keep},
                  'U': sorted(U(X))}
        print(X, len(out[X]['before']), '->', len(keep), file=sys.stderr)
    print('final violations:', len(violations(over)), file=sys.stderr)
    json.dump(out, open(os.environ.get('PLAN', S + '/plan.json'), 'w'), indent=1)
