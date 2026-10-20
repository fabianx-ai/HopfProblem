import re,sys
HEAD=re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+|nonrec\s+)*(theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque)\s+([A-Za-z_][\w.!?\']*)')
CMD=re.compile(r'^(?:@\[|/--|/-!|theorem |lemma |def |abbrev |instance |structure |inductive |class |opaque |private |protected |noncomputable |unsafe |nonrec |open |section|end |namespace |set_option |attribute |universe |variable |scoped |local |macro|syntax|notation|#|/-)')
def units(path):
    L=open(path).read().split('\n'); n=len(L)
    starts=[i for i,l in enumerate(L) if HEAD.match(l)]
    out={}
    for k,i in enumerate(starts):
        name=HEAD.match(L[i]).group(2)
        # extend up over attributes, docstring, blank
        s=i
        j=i-1
        while j>=0:
            l=L[j]
            if l.strip()=='' : j-=1; continue
            if l.startswith('@[') or l.startswith('attribute [') and l.rstrip().endswith(' in'):
                s=j; j-=1; continue
            if l.rstrip().endswith('-/'):
                # find docstring start
                jj=j
                while jj>=0 and not L[jj].startswith('/--'): jj-=1
                if jj>=0 and not L[jj].startswith('/-!'): s=jj; j=jj-1; continue
                break
            break
        # forward to next top-level command
        e=i+1
        while e<n and not CMD.match(L[e]): e+=1
        # trim trailing blank lines
        while e-1>s and L[e-1].strip()=='': e-=1
        out[name]=(s,e,'\n'.join(L[s:e]))
    return L,out
def stmt(block):
    # statement = text up to ':= ' / ' where' / ':= by' at top level, minus docstring
    b=re.sub(r'/--.*?-/\s*','',block,flags=re.S)
    m=re.search(r':=\s*by\b|:=|\bwhere\b',b)
    return re.sub(r'\s+',' ',b[:m.start()] if m else b).strip()
if __name__=='__main__':
    _,w=units('Lib/Topology/MappingTorus/Wang.lean'); _,c=units('Lib/AlgebraicTopology/SingularHomology/CirclePaths.lean')
    ov=sorted(set(w)&set(c))
    same_stmt=same_all=0
    for nme in ov:
        a,b=w[nme][2],c[nme][2]
        if stmt(a)==stmt(b): same_stmt+=1
        else: print('STATEMENT DIFFERS:',nme); print(' W:',stmt(a)[:200]); print(' C:',stmt(b)[:200])
        if re.sub(r'\s+',' ',re.sub(r'/--.*?-/\s*','',a,flags=re.S))==re.sub(r'\s+',' ',re.sub(r'/--.*?-/\s*','',b,flags=re.S)): same_all+=1
    print('overlap',len(ov),'same statement',same_stmt,'same body (docstring-insensitive)',same_all)
