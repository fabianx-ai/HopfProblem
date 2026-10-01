#!/usr/bin/env python3
"""manual_commit.py SRC_COMMIT METHOD [NOTE ...]: commit the staged/dirty tracked changes as the replay of SRC_COMMIT."""
import sys, importlib.util
spec = importlib.util.spec_from_file_location("replay", "/home/goblin/.claude/jobs/06995e68/tmp/int7/replay.py")
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
c = r.out("rev-parse", sys.argv[1]).strip()
r.git("add", "-u")
new = r.commit(c, sys.argv[3:])
commits = [l.strip() for l in open(f"{r.S}/commits.txt") if l.strip()]
r.log(f"[{commits.index(c)+1}] {c} -> {new} | {sys.argv[2]}")
