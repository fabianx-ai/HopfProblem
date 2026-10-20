"""For each dead name: every word-grep hit over the project lies inside a dead declaration's line range."""
import re, subprocess, sys
root = sys.argv[1]; out = sys.argv[2]
P = 'Lib/Topology/Dimension/CubeBoundaryThreeCells/'
dead = [l.split() for l in open(out) if len(l.split()) == 5]
ranges = [(P + p + ".lean", int(a) - 1, int(b) - 1) for p, k, n, a, b in dead]
bad = 0
for p, k, n, a, b in dead:
    r = subprocess.run(['grep', '-rnw', n, 'Lib', 'Hopf', 'Solution.lean', 'S6.lean', 'S6Shortcuts.lean', 'Challenge.lean', '--include=*.lean'], cwd=root, capture_output=True, text=True).stdout
    for line in r.splitlines():
        f, ln = line.split(':')[:2]; ln = int(ln)
        if not any(f == g and x <= ln <= y for g, x, y in ranges):
            print('LIVE HIT', n, f, ln); bad += 1
print('names', len(dead), 'hits outside dead ranges', bad)
