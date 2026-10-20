#!/usr/bin/env python3
"""Drive split_module.py once per piece over the ORIGINAL source (dump anchored to it), then
post-process each move file: drop the original header/module docstring/open lines, drop section
headers with no declaration under them, prepend the piece header. Verifies every moved unit's text
(receipt sha256) occurs verbatim in the final piece file."""
import json, sys, os, subprocess, hashlib, re
plan = json.load(open(sys.argv[1]))
S = os.path.dirname(os.path.abspath(sys.argv[1]))
dump, module, source = plan['dump'], plan['module'], plan['source']
rows = {}
for l in open(dump):
    r = json.loads(l)
    if r['module'] == module and r['range']:
        rows[r['name']] = r
print(f'{len(rows)} ranged constants in {module}')
def piece_of(line):
    hits = [p['name'] for p in plan['pieces'] if any(a <= line <= b for a, b in p['ranges'])]
    return hits
assign = {}
bad = []
for n, r in rows.items():
    l1, l2 = r['range'][0], r['range'][2]
    # the dump range starts at the docstring; the end line lies in the declaration body, so assign by it
    p2 = piece_of(l2)
    if len(p2) != 1:
        bad.append((n, r['range'], p2))
    else:
        assign[n] = p2[0]
if bad:
    for b in bad: print('UNASSIGNED/SPANNING', b)
    sys.exit(1)
counts = {}
for n, p in assign.items(): counts[p] = counts.get(p, 0) + 1
print('per piece:', counts)
lines = open(source, encoding='utf-8').read().split('\n')
def header(p):
    h = ['/-', 'Copyright (c) 2026 Fabian Franz. All rights reserved.',
         'Released under Apache 2.0 license as described in the file LICENSE.',
         'Authors: Fabian Franz', '-/']
    h += [f'import {m}' for m in p['imports']]
    h += ['', p['doc'].rstrip('\n'), '', '']
    h += plan['preamble']
    return h
for p in plan['pieces']:
    stayf = f"{S}/tmp/stay_{p['name']}.txt"
    with open(stayf, 'w') as f:
        for n, q in assign.items():
            if q != p['name']: f.write(n + '\n')
    move = f"{S}/tmp/move_{p['name']}.lean"; keep = f"{S}/tmp/keep_{p['name']}.lean"
    rec = f"{S}/receipts/{plan['stem']}_{p['name']}.json"
    cmd = ['python3', '/home/goblin/lean-agent-ide/tools/split_module.py', '--dump', dump, '--module', module,
           '--source', source, '--stay', stayf, '--keep-out', keep, '--move-out', move, '--receipt', rec]
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode != 0:
        print('split_module failed for', p['name'], r.stdout, r.stderr); sys.exit(2)
    receipt = json.load(open(rec))
    units = [u for u in receipt['units'] if u.get('class') == 'move'] if isinstance(receipt, dict) and 'units' in receipt else [u for u in receipt if isinstance(u, dict) and u.get('class') == 'move']
    out = open(move, encoding='utf-8').read().split('\n')
    # 1. drop everything up to and including the original preamble (first line after the last preamble line)
    # find the first line index that is the start of a moved unit
    unit_starts = set()
    unit_texts = []
    for u in units:
        a, b = u['lines']
        txt = '\n'.join(lines[a-1:b]) + '\n'
        assert hashlib.sha256(txt.encode()).hexdigest() == u['sha256'], ('sha mismatch', u['names'])
        unit_texts.append(txt)
    # locate the preamble end in the move output: the line index of the last preamble line
    pre = plan['orig_preamble']
    idx = None
    for i in range(len(out) - len(pre) + 1):
        if out[i:i+len(pre)] == pre:
            idx = i + len(pre); break
    assert idx is not None, 'preamble not found in move output'
    body = out[idx:]
    # 2. drop section headers `/-! ### ... -/` (single-line) that have no declaration before the next header/EOF
    res = []
    i = 0
    hdr = re.compile(r'^/-! (##+) .*-/$')
    while i < len(body):
        s = body[i]
        if hdr.match(s):
            j = i + 1
            has_decl = False
            while j < len(body) and not hdr.match(body[j]):
                if body[j].strip() and not body[j].startswith('--'):
                    has_decl = True; break
                j += 1
            if not has_decl:
                i = j; continue
        res.append(s); i += 1
    text = '\n'.join(header(p) + res)
    text = re.sub(r'\n{3,}', '\n\n', text).rstrip('\n') + '\n'
    for txt in unit_texts:
        assert txt in text, ('unit text lost in post-processing', p['name'])
    os.makedirs(os.path.dirname(p['out']), exist_ok=True)
    open(p['out'], 'w', encoding='utf-8').write(text)
    print(f"{p['name']}: {len(units)} units, {text.count(chr(10))} lines -> {p['out']}")
