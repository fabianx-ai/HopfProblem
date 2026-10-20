import re,sys,subprocess,os,collections
sys.path.insert(0,'$T')
from decl_blocks import blocks
root='<worktree>'; base='27f8e7f5'
strip=lambda t: re.sub(r'_mo1973_\d+','',t.replace('Mathoverflow1973.','').replace('PeriodLattice','Lattice')).replace('namespace Mathoverflow1973\n','').replace('end Mathoverflow1973\n','')
files=[f for f in subprocess.run(['git','-C',root,'ls-files','Hopf/'],capture_output=True,text=True).stdout.split() if f.endswith('.lean') and f!='Hopf/LibShims.lean']
def stmt(b):
    m=re.search(r':=|\bwhere\b',b); s=b[:m.start()] if m else b
    return re.sub(r'\s+',' ',s).strip()
n=lambda s: re.sub(r'\s+',' ',s).strip()
tot=0;new=[];chg=[];chg_proof=[];deleted=[]
for f in files:
    br=strip(open(os.path.join(root,f),encoding='utf-8').read())
    bs=strip(subprocess.run(['git','-C',root,'show',f'{base}:{f}'],capture_output=True,text=True).stdout)
    bb=blocks(br); bsb=blocks(bs)
    for name in bsb:
        if name not in bb: deleted.append((f,name))
    for name,blks in bb.items():
        tot+=len(blks)
        if name not in bsb: new.append((f,name)); continue
        for b in blks:
            if n(b) in [n(x) for x in bsb[name]]: continue
            if stmt(b) in [stmt(x) for x in bsb[name]]: chg_proof.append((f,name))
            else: chg.append((f,name))
# Lib names (last component and full)
lib=subprocess.run(['grep','-rhoE',r'^(theorem|lemma|def|abbrev|structure|inductive|instance|class|noncomputable def|@\[[^]]*\] (theorem|lemma|def|abbrev|instance)) [A-Za-z_][\w.\'!?]*','Lib','--include=*.lean'],capture_output=True,text=True,cwd=root).stdout.split('\n')
libnames=set(l.split()[-1] for l in lib if l.strip())
liblast=set(x.split('.')[-1] for x in libnames)
missing=[(f,nm) for f,nm in deleted if nm.split('.')[-1] not in liblast]
print('declarations in Hopf/:',tot); print('new:',len(new)); print('changed proof, same statement:',len(chg_proof)); print('CHANGED STATEMENT:',len(chg))
print('deleted from Hopf/:',len(deleted),'by file:',collections.Counter(f for f,_ in deleted))
print('deleted and no Lib declaration with same last name:',len(missing))
for x in new[:30]: print('  NEW',x)
for x in chg[:60]: print('  CHG',x)
for x in missing[:40]: print('  MISSING',x)
print('changed-proof by file:',collections.Counter(f for f,_ in chg_proof))
open('$T/int4_deleted.txt','w').write('\n'.join(f'{f}\t{nm}' for f,nm in deleted))
open('$T/int4_chg.txt','w').write('\n'.join(f'{f}\t{nm}' for f,nm in chg))
