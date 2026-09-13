"""Build the rename map new-name -> base-name from the base dump (wrapper spelling) and the raw
new dump (wrapper stripped, Lattice -> PeriodLattice). Names are compared user-facing (private
mangling removed). Prints unmapped base names (expected: the rows deleted or renamed)."""
import json,re,sys
UNM=re.compile(r'^_private\.(?:[^.]+\.)+?\d+\.')
def names(p):
    s=set()
    for l in open(p):
        s.add(UNM.sub('',json.loads(l)['name']))
    return s
base=names(sys.argv[1]); new=names(sys.argv[2]); out=open(sys.argv[3],'w')
P='Mathoverflow1973.'
mapped=unmapped=same=0; um=[]
for b in sorted(base):
    if not b.startswith(P):
        same+=1; continue
    s=b[len(P):]
    cands=[s]
    if s=='Lattice' or s.startswith('Lattice.'): cands.append('PeriodLattice'+s[len('Lattice'):])
    cands.append(s.replace('.Lattice.','.PeriodLattice.'))
    hit=next((c for c in cands if c in new),None)
    if hit is None: unmapped+=1; um.append(b); continue
    if hit!=b:
        out.write(f'{hit} {b}\n'); mapped+=1
print('base names',len(base),'new names',len(new),'unprefixed',same,'mapped',mapped,'unmapped base names',unmapped)
open(sys.argv[3]+'.unmapped','w').write('\n'.join(um))
# names in new that are not the image of any base name (new declarations / generated)
img=set(); 
for b in base:
    if b.startswith(P):
        s=b[len(P):]; img.update([s,'PeriodLattice'+s[len('Lattice'):] if s=='Lattice' or s.startswith('Lattice.') else s, s.replace('.Lattice.','.PeriodLattice.')])
    else: img.add(b)
extra=sorted(new-img); print('new names with no base preimage',len(extra))
open(sys.argv[3]+'.newonly','w').write('\n'.join(extra))
