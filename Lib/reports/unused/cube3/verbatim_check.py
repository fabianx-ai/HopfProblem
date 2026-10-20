"""Verbatim and complement checks for the cube3 move to Unused.
Run from the repository root: python3 Lib/reports/unused/cube3/verbatim_check.py BASE TIP
(1) Independent of the move script: comment-stripped declaration blocks of the 36 dead names
    at BASE (the seven Lib pieces) and at TIP (the Unused file) are compared as multisets;
    visibility modifiers (`public`, `private`, `@[expose]`) are reported, not hidden.
(2) Complement: every line of a Lib piece at BASE that is not at TIP (line diff) lies inside a
    moved block, or is a listed context line; every TIP line not at BASE is a listed edit."""
import re, subprocess, sys, difflib, collections
BASE, TIP = sys.argv[1], sys.argv[2]
D = 'Lib/Topology/Dimension/CubeBoundaryThreeCells/'
PIECES = ['Lattice', 'Cells', 'Faces', 'Coverage', 'RelInterior', 'SquareBoundary', 'Separation']
U = 'Unused/Topology/Dimension/CubeBoundaryThreeCells.lean'
dead = [l.split()[2] for l in open('Lib/reports/unused/cube3/deadset.out') if len(l.split()) == 5]
show = lambda rev, f: subprocess.run(['git', 'show', f'{rev}:{f}'], capture_output=True, text=True, check=True).stdout
def strip_comments(s):
    out, i, depth = [], 0, 0
    while i < len(s):
        if s.startswith('/-', i): depth += 1; i += 2; continue
        if depth and s.startswith('-/', i): depth -= 1; i += 2; continue
        if depth: 
            if s[i] == '\n': out.append('\n')
            i += 1; continue
        if s.startswith('--', i):
            j = s.find('\n', i); i = len(s) if j < 0 else j; continue
        out.append(s[i]); i += 1
    return ''.join(out)
HEAD = re.compile(r'^(@\[|public |private |protected |noncomputable |theorem |lemma |def |abbrev |instance |structure |inductive |class |set_option .* in$|namespace |end |open |section|#print)')
def blocks(text):
    lines = [l.rstrip() for l in strip_comments(text).split('\n')]
    bs, cur = [], None
    for l in lines:
        if HEAD.match(l) and not (cur and cur[-1].startswith('@[') ) and not (cur and cur[-1].endswith(' in') and cur[-1].startswith('set_option')):
            cur = [l]; bs.append(cur)
        elif cur is not None and l != '':
            cur.append(l)
    return ['\n'.join(b) for b in bs]
NAME = re.compile(r'\b(?:theorem|lemma|def|abbrev)\s+(\S+)')
def named(bs):
    r = {}
    for b in bs:
        m = NAME.search(b)
        if m and m.group(1) in dead: r.setdefault(m.group(1), []).append(b)
    return r
base = {}
for p in PIECES: 
    for k, v in named(blocks(show(BASE, D + p + '.lean'))).items(): base.setdefault(k, []).extend(v)
tip = named(blocks(show(TIP, U)))
VIS = re.compile(r'^(@\[expose\] )?(public |private )?', re.M)
same = vis = 0; bad = []
for n in dead:
    assert len(base.get(n, [])) == 1 and len(tip.get(n, [])) == 1, (n, len(base.get(n, [])), len(tip.get(n, [])))
    a, b = base[n][0], tip[n][0]
    if a == b: same += 1
    elif VIS.sub('', a, 1) == VIS.sub('', b, 1):
        vis += 1; print('visibility only:', n, '|', a.split('\n')[0][:60], '->', b.split('\n')[0][:60])
    else: bad.append(n)
# names in Lib at TIP: none of the dead names left
left = [n for p in PIECES for n in named(blocks(show(TIP, D + p + '.lean')))]
print(f'(1) blocks: {len(dead)} names, identical {same}, visibility-only {vis}, other differences {len(bad)} {bad}; dead names still in Lib pieces at tip: {left}')
# (2) complement
ranges = collections.defaultdict(list)
import json
for b in json.load(open('Lib/reports/unused/cube3/blocks_base.json')):
    ranges[b['piece']].append((b['start'], b['end']))
ctx = {(p, i) for p, i, _ in json.load(open('Lib/reports/unused/cube3/ctx_removed.json'))}
EDIT = {('Cells', 'public theorem square_zero_mem (h : ℝ) (v : Ambient) (j k : Fin 3) : v ∈ squareGeom h v j k := by',
         'theorem square_zero_mem (h : ℝ) (v : Ambient) (j k : Fin 3) : v ∈ squareGeom h v j k := by')}
removed_in_block = 0; problems = []; edits = []; blank_out = collections.Counter()
for p in PIECES:
    a = show(BASE, D + p + '.lean').split('\n'); b = show(TIP, D + p + '.lean').split('\n')
    sm = difflib.SequenceMatcher(None, a, b, autojunk=False)
    for op, i1, i2, j1, j2 in sm.get_opcodes():
        if op == 'equal': continue
        if op == 'replace' and (p, '\n'.join(a[i1:i2]), '\n'.join(b[j1:j2])) in EDIT:
            edits.append((p, a[i1])); continue
        if op in ('insert', 'replace'): problems.append(('added', p, b[j1:j2]))
        for i in range(i1 + 1, i2 + 1):
            if any(s <= i <= e for s, e in ranges[p]): removed_in_block += 1
            elif a[i - 1].strip() == '': blank_out[p] += 1
            else: problems.append(('removed', p, i, a[i - 1]))
# blank lines are interchangeable for the line diff: compare counts per piece with the listed ones
listed = collections.Counter(p for p, i in ctx)
for p in set(listed) | set(blank_out):
    if listed[p] != blank_out[p]: problems.append(('blank count', p, blank_out[p], listed[p]))
removed_ctx = sum(blank_out.values())
print(f'(2) complement: removed lines inside moved blocks {removed_in_block} '
      f'(block lines total {sum(e - s + 1 for v in ranges.values() for s, e in v)}), listed blank context lines {removed_ctx}, '
      f'listed edits {len(edits)} {[e[1][:40] for e in edits]}, unexplained {len(problems)} {problems[:5]}')
# (3) raw text including docstrings: each base block (lines from the dump range) occurs in the Unused file at TIP
u = show(TIP, U)
fix = lambda t: VIS.sub('', t)
raw_ok = sum(1 for b in json.load(open('Lib/reports/unused/cube3/blocks_base.json')) if '\n'.join(b['lines']) in u)
raw_vis = sum(1 for b in json.load(open('Lib/reports/unused/cube3/blocks_base.json')) if '\n'.join(b['lines']) not in u and fix('\n'.join(b['lines'])) in fix(u))
print(f'(3) raw blocks with docstrings found verbatim in the Unused file: {raw_ok}, after removing visibility modifiers: {raw_vis} more')
