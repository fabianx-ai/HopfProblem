#!/usr/bin/env python3
"""Apply the cut: run split_module once per piece from the ORIGINAL source (stay = everything
except the piece), rewrite the piece header (imports from `uses`, module docstring), write the
facades.  Receipts under $S/receipts/."""
import json, os, re, subprocess, sys, hashlib
S = '/home/goblin/.claude/jobs/06995e68/tmp/wave1/morse-d'
sys.path.insert(0, S)
from plan import PIECES, OC, SC, FACADE_DOC, path_of
ROOT = '/home/goblin/hopf-w1-morse-d'
DUMP = sys.argv[1] if len(sys.argv) > 1 else '/home/goblin/.claude/jobs/06995e68/tmp/wave1/dump_head.jsonl'
TOOL = '/home/goblin/lean-agent-ide/tools/split_module.py'
res = json.load(open(f'{S}/plan_resolved.json'))
piece_of = res['piece_of']
os.makedirs(f'{S}/receipts', exist_ok=True)
os.makedirs(f'{S}/discard', exist_ok=True)

# all ranged names per source module (dump names)
ranged = {OC: [], SC: []}
for l in open(DUMP, encoding='utf-8'):
    r = json.loads(l)
    if r['module'] in ranged and r['range']:
        ranged[r['module']].append(r['name'])

HEADER = """/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
"""
orig_text = {m: open(f'{ROOT}/{path_of(m)}', encoding='utf-8').read() for m in (OC, SC)}
# the original module docstring block (context copied by the tool into every piece)
def orig_doc_block(text):
    m = re.search(r'\n/-!.*?-/\n', text, re.S)
    return m.group(0)
orig_doc = {m: orig_doc_block(orig_text[m]) for m in (OC, SC)}

summary = []
for mod, cls, src, names, doc in PIECES:
    stay = [n for n in ranged[src] if piece_of.get(n) != mod]
    stay_file = f'{S}/receipts/{mod}.stay.txt'
    open(stay_file, 'w').write('\n'.join(stay) + '\n')
    out = f'{ROOT}/{path_of(mod)}'
    os.makedirs(os.path.dirname(out), exist_ok=True)
    receipt = f'{S}/receipts/{mod}.json'
    cmd = ['python3', TOOL, '--dump', DUMP, '--module', src, '--source', f'{ROOT}/{path_of(src)}',
           '--stay', stay_file, '--keep-out', f'{S}/discard/{mod}.keep.lean', '--move-out', out,
           '--receipt', receipt]
    p = subprocess.run(cmd, capture_output=True, text=True)
    print(mod, p.stdout.strip(), p.stderr.strip())
    if p.returncode != 0:
        sys.exit(f'split_module failed for {mod}')
    rec = json.load(open(receipt))
    moved = [u for u in rec['units'] if u.get('class') == 'move']
    moved_names = {n for u in moved for n in u['names']}
    want = {n for n, pm in piece_of.items() if pm == mod}
    assert moved_names == want, (mod, moved_names ^ want)
    # ---- rewrite header: copyright, imports, blank, module doc; drop original imports and doc block
    text = open(out, encoding='utf-8').read()
    assert text.startswith(HEADER), mod
    body = text[len(HEADER):]
    body = re.sub(r'^(import [^\n]*\n)+', '', body, count=1)
    assert orig_doc[src] in body, mod
    body = body.replace(orig_doc[src], '\n', 1)
    imports = ['Mathlib'] + res['pieces'][mod]['imports']
    header = HEADER + ''.join(f'import {i}\n' for i in imports) + '\n' + doc + '\n'
    body = body.lstrip('\n')
    new = header + body
    new = re.sub(r'\n{3,}', '\n\n', new)
    open(out, 'w', encoding='utf-8').write(new)
    summary.append((mod, cls, len(moved), sum(u['lines'][1] - u['lines'][0] + 1 for u in moved)))

# ---- facades
for src in (OC, SC):
    pieces = [mod for mod, cls, s, *_ in PIECES if s == src and cls == 'lib']
    text = HEADER + ''.join(f'import {m}\n' for m in pieces) + '\n' + FACADE_DOC[src] + '\n'
    open(f'{ROOT}/{path_of(src)}', 'w', encoding='utf-8').write(text)
    print('facade', src, len(pieces), 'imports')
json.dump(summary, open(f'{S}/split_summary.json', 'w'), indent=1)
for s in summary: print(s)
