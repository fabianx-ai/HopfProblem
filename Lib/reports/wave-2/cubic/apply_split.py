#!/usr/bin/env python3
"""Run split_module once per piece from the ORIGINAL source (git show base), stay = everything else;
then rewrite the piece header and drop foreign section headers (context lines only); write the facade.
Verifies each moved unit's text is a verbatim substring of the piece."""
import json, os, re, subprocess, sys, hashlib
S='/home/goblin/.claude/jobs/06995e68/tmp/wave2/cubic'; sys.path.insert(0,S)
from plan import PIECES, MOD, ORIG, FACADE_DOC
ROOT='/home/goblin/hopf-w2-cubic'; DUMP='/home/goblin/.claude/jobs/06995e68/tmp/wave2/dump_head.jsonl'
TOOL='/home/goblin/lean-agent-ide/tools/split_module.py'
SRC=f'{S}/Cubic.orig.lean'
open(SRC,'w').write(subprocess.run(['git','-C',ROOT,'show','3760f829:Lib/Geometry/Manifold/Morse/Cubic.lean'],capture_output=True,text=True,check=True).stdout)
src_lines=open(SRC).read().split('\n')
ranged=[]
for l in open(DUMP):
    r=json.loads(l)
    if r['module']==MOD and r['range']: ranged.append((r['range'][0],r['name']))
ranged.sort()
def piece_of(line):
    for stem,rngs,*_ in PIECES:
        for a,b in rngs:
            if a<=line<=b: return stem
    raise SystemExit(f'line {line} in no piece')
assign={n:piece_of(l) for l,n in ranged}
json.dump(assign,open(f'{S}/plan_resolved.json','w'),indent=1)
HEADER="""/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

"""
CTX="""
open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

"""
os.makedirs(f'{ROOT}/Lib/Geometry/Manifold/Morse/Cubic',exist_ok=True)
total=0; summary=[]
for stem,rngs,sib,libs,impall,doc in PIECES:
    stay=[n for _,n in ranged if assign[n]!=stem]
    sf=f'{S}/receipts/{stem}.stay.txt'; open(sf,'w').write('\n'.join(stay)+'\n')
    tmp=f'{S}/discard/{stem}.move.lean'; rec=f'{S}/receipts/split_{stem}.json'
    p=subprocess.run(['python3',TOOL,'--dump',DUMP,'--module',MOD,'--source',SRC,'--stay',sf,'--keep-out',f'{S}/discard/{stem}.keep.lean','--move-out',tmp,'--receipt',rec],capture_output=True,text=True)
    print(stem,p.stdout.strip(),p.stderr.strip())
    if p.returncode: sys.exit(1)
    R=json.load(open(rec)); moved=[u for u in R['units'] if u.get('class')=='move']
    names={n for u in moved for n in u['names']}
    want={n for n in assign if assign[n]==stem}
    assert names==want,(stem,names^want)
    text=open(tmp).read()
    i=text.index('@[expose] public noncomputable section\n')+len('@[expose] public noncomputable section\n')
    body=text[i:]
    body=re.sub(r'^/-! ### [^\n]* -/\n','',body,flags=re.M)
    body=re.sub(r'\n{3,}','\n\n',body).strip('\n')+'\n'
    libs_=ORIG if libs is None else libs
    imports=['public import Mathlib']+[f'public import {m}' for m in libs_]+[f'public import {MOD}.{s}' for s in sib]
    if impall: imports.append('import all Mathlib.Geometry.Manifold.LocalDiffeomorph')
    new=HEADER+'\n'.join(imports)+'\n\n'+doc+'\n'+CTX+body
    # verbatim check
    for u in moved:
        a,b=u['lines']; t='\n'.join(src_lines[a-1:b])
        assert hashlib.sha256((t+'\n').encode()).hexdigest()==u['sha256'] or hashlib.sha256(t.encode()).hexdigest()==u['sha256'],(stem,u['names'][0])
        assert t in new,(stem,u['names'][0])
    open(f'{ROOT}/Lib/Geometry/Manifold/Morse/Cubic/{stem}.lean','w').write(new)
    n=len(moved); ln=sum(u['lines'][1]-u['lines'][0]+1 for u in moved); total+=n
    summary.append((stem,n,ln))
fac=HEADER+''.join(f'public import {MOD}.{s}\n' for s,*_ in PIECES)+'\n'+FACADE_DOC+'\n'
open(f'{ROOT}/Lib/Geometry/Manifold/Morse/Cubic.lean','w').write(fac)
json.dump(summary,open(f'{S}/split_summary.json','w'),indent=1)
for s in summary: print(s)
print('total units',total)
