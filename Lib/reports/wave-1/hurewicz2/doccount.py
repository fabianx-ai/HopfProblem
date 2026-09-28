#!/usr/bin/env python3
"""count non-private declarations and those lacking a docstring, per file (text heuristic)"""
import re, sys
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:(private|protected|noncomputable|nonrec)\s+)*(theorem|lemma|def|abbrev|structure|instance|inductive|class|opaque)\s+(\S+)')
for f in sys.argv[1:]:
    lines = open(f).read().split('\n')
    total = undoc = 0; missing = []
    for i, l in enumerate(lines):
        m = DECL.match(l)
        if not m: continue
        if 'private' in l.split(m.group(2))[0]: continue
        total += 1
        # look upward over attribute/modifier lines for a docstring end
        j = i - 1
        while j >= 0 and (lines[j].startswith('@[') or lines[j].startswith('attribute') or (lines[j].startswith(' ') and lines[j].strip()) ):
            j -= 1
        if j < 0 or not lines[j].rstrip().endswith('-/'):
            undoc += 1; missing.append((i + 1, m.group(3)))
    print(f'{f}: {total} public declarations, {undoc} without docstring')
    for m in missing: print('   ', m)
