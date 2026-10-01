#!/usr/bin/env python3
"""manual_append.py SRC_COMMIT SRC_PATH DEST_PATH : append the lines SRC_COMMIT adds to SRC_PATH
(pure-addition patch at end of file) to DEST_PATH in the int7 worktree, verbatim."""
import subprocess, sys
c, src, dest = sys.argv[1:4]
d = subprocess.run(["git", "-C", "/home/goblin/hopf", "diff", f"{c}^", c, "--", src],
                   stdout=subprocess.PIPE, check=True).stdout.decode()
added, removed, hunks, in_h = [], [], 0, False
for l in d.split("\n"):
    if l.startswith("@@"):
        hunks += 1; in_h = True; continue
    if not in_h: continue
    if l.startswith("+"): added.append(l[1:])
    elif l.startswith("-"): removed.append(l[1:])
assert hunks == 1 and not removed, (hunks, removed)
p = "/home/goblin/hopf-int7/" + dest
t = open(p).read()
assert t.endswith("\n")
open(p, "w").write(t + "\n".join(added) + "\n")
print(f"appended {len(added)} lines to {dest}")
