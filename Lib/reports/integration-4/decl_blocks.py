import re,sys,subprocess,os
DECL=re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|public|scoped)\s+)*(theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque)\s+([^\s:(\[{]+)')
START=re.compile(r'^(?:@\[|attribute \[|theorem |lemma |def |abbrev |instance |structure |inductive |class |opaque |private |protected |noncomputable |nonrec |public |scoped |open |set_option |universe |namespace |end |section |variable |import |/-|--|#)')
def blocks(text):
    """return dict name -> block text (from first attribute/decl line to next top-level start)"""
    lines=text.split('\n'); out={}; i=0; n=len(lines)
    cur_name=None; cur=[]
    pending=[]  # attribute lines preceding decl
    def flush():
        nonlocal cur_name,cur
        if cur_name:
            out.setdefault(cur_name,[]).append('\n'.join(cur).rstrip())
        cur_name=None; cur=[]
    for l in lines:
        m=DECL.match(l)
        if m:
            flush()
            cur_name=m.group(2); cur=pending+[l]; pending=[]
        elif l.startswith('attribute [local instance') and l.rstrip().endswith(' in') or (l.startswith('attribute [') and l.rstrip().endswith(' in')):
            flush(); pending=[l]
        elif l and not l[0].isspace() and START.match(l) and not l.startswith('attribute'):
            # top-level non-decl line ends the block
            flush(); pending=[]
        else:
            if cur_name is not None: cur.append(l)
            elif pending: pending.append(l)
    flush()
    return out
if __name__=='__main__':
    root=sys.argv[1]; base=sys.argv[2]
    files=subprocess.run(['git','-C',root,'ls-files','Hopf/'],capture_output=True,text=True).stdout.split()
    files=[f for f in files if f.endswith('.lean') and f!='Hopf/LibShims.lean']
    changed=[];missing_in_base=[];total=0
    for f in files:
        br=open(os.path.join(root,f),encoding='utf-8').read()
        bs=subprocess.run(['git','-C',root,'show',f'{base}:{f}'],capture_output=True,text=True).stdout
        bb=blocks(br); bsb=blocks(bs)
        for name,blks in bb.items():
            total+=len(blks)
            if name not in bsb:
                missing_in_base.append((f,name)); continue
            for b in blks:
                norm=lambda s: re.sub(r'\s+',' ',s).strip()
                if norm(b) not in [norm(x) for x in bsb[name]]:
                    changed.append((f,name,b,bsb[name][0]))
    print("declarations in branch Hopf/:",total)
    print("not present in base Hopf/ (same file):",len(missing_in_base))
    for f,n in missing_in_base[:40]: print("  NEW?",f,n)
    print("blocks differing from base:",len(changed))
    for f,n,b,ob in changed[:30]:
        print("=== CHANGED",f,n)
        import difflib
        for l in difflib.unified_diff(ob.split('\n'),b.split('\n'),lineterm='',n=1): print("   ",l)
