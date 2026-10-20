#!/usr/bin/env python3
"""Lint for Lib/: hygiene checks for the textbook-extraction tree."""
import sys, re, glob, os
sys.path.insert(0, '/home/glm/s6-notes/hopf-lib-a')
from declmap import decls

FAIL = 0
def fail(msg):
    global FAIL
    FAIL += 1
    print('FAIL:', msg)

for f in sorted(glob.glob('Lib/**/*.lean', recursive=True)) + ['Lib.lean']:
    is_audit = 'AxiomAudit' in f
    is_root = f == 'Lib.lean'
    text = open(f).read()
    lines = text.split('\n')
    for i, l in enumerate(lines, 1):
        if re.search(r'\b(sorry|admit)\b', l) and not l.strip().startswith('--'):
            fail(f'{f}:{i}: sorry/admit')
        if not is_audit and re.match(r'^#(check|eval|print)', l):
            fail(f'{f}:{i}: command debris')
        if len(l) > 120 and 'http' not in l and not l.strip().startswith('--'):
            fail(f'{f}:{i}: line >120 chars')
        if l != l.rstrip():
            fail(f'{f}:{i}: trailing whitespace')
        if '\t' in l:
            fail(f'{f}:{i}: tab character')
    if not is_root and not is_audit:
        if not any(l.startswith('/-!') for l in lines[:80]):
            fail(f'{f}: missing module docstring')
        if re.search(r'^import (Hopf|S6|Challenge|Solution)', text, re.M):
            fail(f'{f}: forbidden import')
        auto = [d['name'] for d in decls(f)
                if not d.get('priv') and re.search(r'_mo1973_\d+', d['name'])]
        for a in auto:
            fail(f'{f}: public auto-named declaration {a}')

print(f'lib_lint: {FAIL} finding(s)')
sys.exit(1 if FAIL else 0)
