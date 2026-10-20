# usage: vis.py SRC OUT pub.txt expose.txt  -- add `public ` / `@[expose] public ` to declaration lines
import re,sys
src,out,pubf,expf=sys.argv[1:5]
pub=set(l.split()[0] for l in open(pubf) if l.strip())
exp=set(l.split()[0] for l in open(expf) if l.strip())
L=open(src).read().split('\n'); done=set()
for i,s in enumerate(L):
    m=re.match(r'^(public |private )?((?:noncomputable )?)(theorem|def|lemma|abbrev) ([^\s:({\[]+)',s)
    if not m: continue
    n=m.group(4)
    if n in pub or n in exp:
        if m.group(1)=='public ':
            assert n in exp and n not in pub, (n,s); L[i]='@[expose] '+s
        else:
            assert m.group(1) is None, (n,s)
            L[i]=('@[expose] ' if n in exp else '')+'public '+s
        done.add(n)
miss=(pub|exp)-done
if miss: print('NOT FOUND',miss); sys.exit(1)
open(out,'w').write('\n'.join(L)); print('patched',len(done))
