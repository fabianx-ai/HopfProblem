"""Recompute the proof-split demotion with and without dependency edges that run through another
declaration's `_proof_n` auxiliary constants (Lean reuses identical abstracted proofs within a
module, so such an edge is not a use of the other declaration)."""
import json,re,sys,os,collections
sys.path.insert(0,'<worktree>/scripts')
import lib_stock_census as C
ROOT='<worktree>'
prefixes=C.load_prefixes(os.path.join(ROOT,'scripts/lib_stock_prefixes.txt'))
rows={r['name']:r for r in map(json.loads,open(sys.argv[1]))}
hopf={n:r for n,r in rows.items() if r['module'].startswith('Hopf.') and r['module']!='Hopf.LibShims'}
withrange={n for n,r in hopf.items() if r['range']}
def parent(n):
    if n in withrange: return n
    parts=n.split('.')
    for k in range(len(parts)-1,0,-1):
        p='.'.join(parts[:k])
        if p in withrange and rows[p]['module']==rows[n]['module']: return p
    m=re.match(r'_private\.[\w.₀-₉]+?\.0\.(.*)',n)
    if m and m.group(1) in withrange: return m.group(1)
    return None
def path(mod): return mod.replace('.','/')+'.lean'
def short(n):
    n=re.sub(r'^_private\.[\w.₀-₉]+?\.0\.','',n)
    return n[len('Mathoverflow1973.'):] if n.startswith('Mathoverflow1973.') else n
stock={n for n in withrange if any(C.match_entry(e,path(hopf[n]['module']),short(n)) for e in prefixes)}
AUX=re.compile(r'\._proof_\d+$')
def run(skip_proof_aux):
    deps=collections.defaultdict(set)
    for n,r in hopf.items():
        p=parent(n)
        if p is None: continue
        for u in r['uses']:
            if u in hopf:
                if skip_proof_aux and AUX.search(u): continue
                q=parent(u)
                if q and q!=p: deps[p].add(q)
    keep=set(stock); changed=True
    while changed:
        changed=False
        for p in list(keep):
            if any(q not in keep for q in deps[p]): keep.discard(p); changed=True
    return keep, stock-keep, deps
k1,d1,_=run(False); k2,d2,deps2=run(True)
print('stock',len(stock),'| with _proof_n edges: keep',len(k1),'demoted',len(d1),'| without: keep',len(k2),'demoted',len(d2))
freed=sorted(d1-d2); print('freed by dropping _proof_n edges:',len(freed))
json.dump({'freed':freed,'still_demoted':sorted(d2)},open('$T/int4_redemote.json','w'),indent=1)
# how many of the still-demoted bind only through _proof edges of stock decls? (for information)
fam=collections.Counter(short(n).split('.')[0] for n in freed); print('freed by family:',fam.most_common(12))
fam2=collections.Counter(short(n).split('.')[0] for n in d2); print('still demoted by family:',fam2.most_common(12))
