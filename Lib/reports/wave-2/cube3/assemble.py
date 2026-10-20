# assemble.py SPLITDIR OUTDIR : turn split/<P>.raw.lean into Lib pieces with own header and docstring.
# Context edits only: header (module, imports, docstring, options, namespace) rewritten; the stray
# plain comment "Coordinate evaluation/extensionality ...", the empty `end`/`namespace` pair and the
# `/-! ## Enclosure of a boundary point by a cell -/` section comment are dropped.
import sys, re, os
SD, OUT = sys.argv[1:3]
NS = 'TopologicalSpace.CubeBoundaryThree'
BASE = 'Lib.Topology.Dimension.CubeBoundaryThreeCells'
IMPORTS = {
 'Lattice': ['Lib.Topology.Dimension.CubeBoundaryThree', 'Mathlib.Analysis.Convex.Segment', 'Mathlib.Data.Int.Interval'],
 'Cells': [BASE + '.Lattice'],
 'Faces': [BASE + '.Cells'],
 'Coverage': [BASE + '.Faces'],
 'RelInterior': [BASE + '.Faces'],
 'SquareBoundary': [BASE + '.Cells'],
 'Separation': [BASE + '.Faces'],
}
DOCS = {}
exec(open(os.path.join(os.path.dirname(__file__), 'docs.py')).read())
for P in IMPORTS:
    L = open(f'{SD}/{P}.raw.lean').read().split('\n')
    # drop prefix through end of module docstring
    i = L.index('/-!'); j = i
    while L[j] != '-/': j += 1
    body = L[j + 1:]
    txt = '\n'.join(body)
    txt = txt.replace('/- Coordinate evaluation/extensionality, set transport,\nreal order/cancellation, half-mesh positivity, absolute-value/sign, maximum, and Fin 3 cases. -/\n', '')
    txt = re.sub(r'/-! ## Enclosure of a boundary point by a cell\n.*?-/\n', '', txt, flags=re.S)
    txt = txt.replace(f'end {NS}\n\nnamespace {NS}\n', '')
    txt = re.sub(r'\n{3,}', '\n\n', txt).strip('\n')
    assert txt.endswith(f'end {NS}'), P
    assert txt.count(f'end {NS}') == 1 and f'namespace {NS}' not in txt, P
    head = ['module', ''] + [f'public import {m}' for m in IMPORTS[P]] + ['', DOCS[P].strip(), '',
            'set_option warningAsError true', 'set_option autoImplicit false', '', 'open Set', '',
            f'namespace {NS}', '', '']
    open(f'{OUT}/{P}.lean', 'w').write('\n'.join(head) + txt + '\n')
    print(P, 'ok')
