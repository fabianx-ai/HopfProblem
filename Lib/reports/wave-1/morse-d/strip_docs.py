#!/usr/bin/env python3
"""Write docstring-free copies of the Lib pieces to $S/stripped/ and verify every moved unit's
receipt sha256 against the stripped text (verbatimness check)."""
import re, sys, os, json, hashlib
S='/home/goblin/.claude/jobs/06995e68/tmp/wave1/morse-d'; sys.path.insert(0,S)
from plan import PIECES, path_of
from docstrings_oc import DOCS as D1
from docstrings_sc import DOCS as D2
DOCS={**D1,**D2}; ROOT='/home/goblin/hopf-w1-morse-d'
DECL = re.compile(r'^(?:private |protected |noncomputable )*(?:theorem|lemma|def|abbrev|instance|structure) ([^\s:({\[]+)')
os.makedirs(f'{S}/stripped', exist_ok=True)
sha=lambda s: hashlib.sha256(s.encode()).hexdigest()
for mod, cls, src, names, doc in PIECES:
    path=f'{ROOT}/{path_of(mod)}'; lines=open(path).read().split('\n')
    if cls=='lib':
        out=[]; i=0
        while i<len(lines):
            m=DECL.match(lines[i])
            if m and m.group(1) in DOCS and m.group(1) in names:
                j=len(out)
                while j>0 and out[j-1].startswith('@['): j-=1
                k=j-1
                assert out[k].rstrip().endswith('-/'), (mod, m.group(1))
                t=k
                while not out[t].startswith('/--'): t-=1
                del out[t:k+1]
            out.append(lines[i]); i+=1
        lines=out
    text='\n'.join(lines)
    open(f'{S}/stripped/{mod}.lean','w').write(text)
    rec=json.load(open(f'{S}/receipts/{mod}.json'))
    for u in rec['units']:
        if u.get('class')!='move': continue
        # unit text as written by the tool: find it verbatim in the stripped file
    # verify by sha of each unit chunk from the ORIGINAL source (git show base) equals receipt, and chunk ⊂ stripped text
    import subprocess
    orig=subprocess.run(['git','-C',ROOT,'show',f'e669bc93:{path_of(src)}'],capture_output=True,text=True).stdout.split('\n')
    ok=0
    for u in rec['units']:
        if u.get('class')!='move': continue
        a,b=u['lines']; chunk='\n'.join(orig[a-1:b])+'\n'
        assert sha(chunk)==u['sha256'], (mod,u['names'])
        assert chunk in text+'\n', (mod,u['names'])
        ok+=1
    print(mod, 'units verified', ok)
