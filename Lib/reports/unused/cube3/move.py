"""Move the dead blocks (blocks_base.json) out of the Lib pieces into the Unused file.
Removed from the pieces: the block lines; then runs of blank lines created by the removal
are collapsed to one (the extra blank lines are logged as removed context)."""
import json, sys
root = sys.argv[1]
B = json.load(open('blocks_base.json'))
P = root + '/Lib/Topology/Dimension/CubeBoundaryThreeCells/'
ORDER = ['Lattice', 'Cells', 'Faces', 'Coverage', 'SquareBoundary']
ctx_removed = []
pieces_out = {}
for piece in ORDER:
    bs = [b for b in B if b['piece'] == piece]
    L = open(P + piece + '.lean').read().split('\n')
    rm = set()
    for b in bs: rm.update(range(b['start'], b['end'] + 1))
    keep = []
    for i, line in enumerate(L, 1):
        if i in rm: continue
        if line.strip() == '' and keep and keep[-1][1].strip() == '' and any(j in rm for j in range(keep[-1][0], i)):
            ctx_removed.append((piece, i, line)); continue
        keep.append((i, line))
    open(P + piece + '.lean', 'w').write('\n'.join(l for _, l in keep))
    # Unused part: blocks in source order; a blank line between two blocks iff the source had a gap
    out = []
    prev_end = None
    for b in bs:
        if prev_end is not None and b['start'] != prev_end + 1: out.append('')
        out.extend(b['lines']); prev_end = b['end']
    pieces_out[piece] = out
json.dump(ctx_removed, open('ctx_removed.json', 'w'))
hdr = open('unused_header.lean').read()
body = []
for piece in ORDER:
    body.append(f'/-! ### From `Lib.Topology.Dimension.CubeBoundaryThreeCells.{piece}` -/')
    body.append('')
    body.extend(pieces_out[piece]); body.append('')
open(root + '/Unused/Topology/Dimension/CubeBoundaryThreeCells.lean', 'w').write(hdr + '\n'.join(body) + 'end TopologicalSpace.CubeBoundaryThree\n')
print('context lines removed', ctx_removed)
