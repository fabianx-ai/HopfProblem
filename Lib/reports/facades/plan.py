"""Compute the reroute plan: for every consumer of a facade, the replacement imports.

Semantics of visibility (strict): a module sees its direct imports and, recursively, what they
export; a module file exports its `public import`s, a legacy (non-module) file exports all imports.
U(X) = defining modules of the constants used by X's declarations (dump `uses`), generated
auxiliaries realized in X mapped to their parent constant.
"""
import json, re, sys, collections
from graph import Graph, modname
D = '/home/goblin/.claude/jobs/06995e68/tmp/facades'
g = Graph()
FAC = [l.strip() for l in open(D + '/real.txt') if l.strip()]
FACS = set(FAC)
CONS = [modname(l.strip()) for l in open(D + '/consumers.txt') if l.strip()]
SPECIAL = {'Lib'}  # Lib.lean handled separately (imports every piece)

# ---- dump
mod_of = {}; uses_of = collections.defaultdict(set); ranged = set()
GEN = re.compile(r'\.(eq_\d+|eq_def|match_\d+|_proof_\d+|proof_\d+|congr_simp|sizeOf_spec|injEq|inj|_sunfold|_unary|_mutual|splitter|eq_spec|fun_cases|induct|_cstage\d|_lambda_\d+|_closed_\d+|_unsafe_rec)$')
for l in open(D + '/dump_base.jsonl', encoding='utf-8'):
    r = json.loads(l); mod_of[r['name']] = r['module']
    if r['range']: ranged.add(r['name'])
    uses_of[r['module']].update(r['uses'])
def parent(n):
    while True:
        m = GEN.search(n)
        if not m: return n
        n = n[:m.start()]
def used_modules(X):
    out = set()
    for c in uses_of.get(X, ()):
        for n in {c, parent(c)}:
            m = mod_of.get(n)
            if m and m != X: out.add(m)
    return out
# AxiomAudit-style files: names after #print axioms / #check
def textual_uses(X):
    p = g.files.get(X)
    if not p: return set()
    s = open('/home/goblin/hopf-facades/' + p, encoding='utf-8').read()
    out = set()
    names = re.findall(r'^#(?:print axioms|check)\s+(\S+)', s, re.M) + re.findall(r'^example\s*:=\s*@([^\s.{]+(?:\.[^\s.{]+)*)', s, re.M)
    for n in names:
        m = mod_of.get(n)
        if m and m != X: out.add(m)
    return out
U = {}
def Uof(X):
    if X not in U: U[X] = used_modules(X) | textual_uses(X)
    return U[X]

# ---- graphs
def is_module(X): return g.get(X)[0]
def old_imports(X): return [(i, pub) for i, pub, meta in g.get(X)[1] if i in g.files]

new_extra = collections.defaultdict(dict)   # consumer -> {module: public?}
reason = collections.defaultdict(dict)      # consumer -> {module: 'use'|'reexport:<X>'}
import os as _os
PIECES = {}
for f in FAC:
    d = '/home/goblin/hopf-facades/' + f.replace('.', '/')
    PIECES[f] = sorted(_os.path.relpath(_os.path.join(dp, x), '/home/goblin/hopf-facades')[:-5].replace('/', '.')
                       for dp, _, fs in _os.walk(d) for x in fs if x.endswith('.lean'))
for f in FAC:
    for p in PIECES[f]: new_extra['Lib'][p] = False
def new_imports(X):
    if X in FACS: return []
    imps = [(i, p) for i, p in old_imports(X) if i not in FACS]
    have = {i for i, _ in imps}
    imps += [(m, p) for m, p in new_extra[X].items() if m not in have]
    return imps
def exports(imps_fn, X, memo):
    # set of modules X exports (re-exports) to importers, including X itself
    if X in memo: return memo[X]
    memo[X] = {X}
    legacy = not is_module(X)
    s = {X}
    for i, p in imps_fn(X):
        if p or legacy: s |= exports(imps_fn, i, memo)
    memo[X] = s; return s
def visible(imps_fn, X, memo):
    s = set()
    for i, p in imps_fn(X): s |= exports(imps_fn, i, memo)
    return s
def old_imps_fn(X): return old_imports(X)

def facade_region(X):
    """modules X saw through a facade import, with public flag (public if any public facade edge covers)."""
    memo = {}; reg = {}
    for i, p in old_imports(X):
        if i in FACS:
            for m in exports(old_imps_fn, i, memo):
                if m in FACS: continue
                reg[m] = reg.get(m, False) or p or not is_module(X)
    return reg

if __name__ == '__main__':
    omemo = {}
    # sanity: old graph satisfies U under strict semantics?
    allmods = [m for m in g.files if m in uses_of or m in CONS]
    viol = [(X, sorted(Uof(X) - visible(old_imps_fn, X, omemo))[:3]) for X in allmods if Uof(X) - visible(old_imps_fn, X, omemo)]
    print('old-graph strict violations:', len(viol), viol[:5], file=sys.stderr)
    REG = {X: facade_region(X) for X in CONS if X not in SPECIAL}
    # initial: each consumer imports modules it uses from its facade region not visible otherwise
    for it in range(50):
        nmemo = {}
        changed = False
        for X in CONS:
            if X in SPECIAL: continue
            vis = visible(new_imports, X, nmemo)
            for m in sorted(Uof(X) - vis):
                if m in REG[X]:
                    new_extra[X][m] = REG[X][m]; reason[X][m] = 'use'; changed = True
        if changed: continue
        # downstream re-export needs
        for Y in [m for m in g.files if m not in FACS and m not in SPECIAL]:
            miss = Uof(Y) - visible(new_imports, Y, nmemo) - {Y}
            for m in sorted(miss):
                # find a rerouted consumer on Y's old export path that lost m
                cands = []
                for i, p in new_imports(Y):
                    for Z in exports(new_imports, i, nmemo):
                        if Z in REG and REG[Z].get(m):  # public facade edge carrying m
                            cands.append(Z)
                if not cands:
                    print('UNRESOLVED', Y, m, file=sys.stderr); continue
                Z = sorted(cands)[0]
                new_extra[Z][m] = True; reason[Z][m] = 'reexport:' + Y; changed = True
            if changed: break
        if not changed: break
    # minimize: drop m from X's additions if covered by X's other new imports with adequate export
    nmemo = {}
    for X in list(new_extra):
        for m in sorted(new_extra[X], key=lambda m: -len(exports(new_imports, m, nmemo))):
            p = new_extra[X][m]
            others = [(i, q) for i, q in new_imports(X) if i != m]
            memo2 = {}
            cov = set()
            for i, q in others:
                if (q or not is_module(X)) or not p: cov |= exports(new_imports, i, memo2)
            if m in cov:
                del new_extra[X][m]; nmemo = {}
    # final check
    nmemo = {}
    bad = [(Y, sorted(Uof(Y) - visible(new_imports, Y, nmemo) - {Y})) for Y in g.files if Y not in FACS and Y not in SPECIAL and Uof(Y) - visible(new_imports, Y, nmemo) - {Y}]
    print('final violations', len(bad), bad[:5], file=sys.stderr)
    json.dump({X: {'old': [[i, p] for i, p in old_imports(X) if i in FACS],
                   'new': [[m, new_extra[X][m], reason[X].get(m, '')] for m in sorted(new_extra[X])]}
               for X in CONS if X not in SPECIAL}, open(D + '/plan.json', 'w'), indent=1)
