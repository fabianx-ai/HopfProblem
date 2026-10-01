#!/usr/bin/env python3
"""Integration 7: replay the Lib/ + Lib.lean commits of center-solution (bcf711d6..8ea19482) onto
int7/replay, one commit per commit.  Usage: replay.py FROM TO   (1-based, inclusive).
Method per commit: `git cherry-pick --no-commit`; if only Lib.lean / Lib/AxiomAudit.lean conflict,
resolve by the append rule (HEAD version + lines the patch adds, patch order, duplicates skipped);
any other conflict stops.  Commits listed in MANUAL are refused (handled by hand)."""
import os, subprocess, sys

WT = "/home/goblin/hopf-int7"
S = "/home/goblin/.claude/jobs/06995e68/tmp/int7"
LOG = f"{S}/replay-methods.log"
APPEND_FILES = {"Lib.lean", "Lib/AxiomAudit.lean"}
MANUAL = {"b3f08b95", "e238166c"}
TRAILERS = ("Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n"
            "Claude-Session: https://claude.ai/code/session_01VZt4JDgce67x5QTThwQ3E2\n")
ENV = dict(os.environ, GIT_CONFIG_COUNT="1", GIT_CONFIG_KEY_0="safe.directory", GIT_CONFIG_VALUE_0="*")

def git(*args, check=True):
    r = subprocess.run(["git", *args], cwd=WT, env=ENV, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if check and r.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)} failed ({r.returncode}):\n{r.stderr.decode(errors='replace')}")
    return r

def out(*args, **kw):
    return git(*args, **kw).stdout.decode()

def log(msg):
    print(msg, flush=True)
    with open(LOG, "a") as f:
        f.write(msg + "\n")

def patch_add_remove(c, path):
    d = out("diff", f"{c}^", c, "--", path)
    added, removed, in_hunk = [], [], False
    for line in d.split("\n"):
        if line.startswith("@@"):
            in_hunk = True; continue
        if not in_hunk:
            continue
        if line.startswith("+"):
            added.append(line[1:])
        elif line.startswith("-"):
            removed.append(line[1:])
    return added, removed

def resolve_append(c, path):
    head = out("show", f"HEAD:{path}")
    lines = head.split("\n")
    if head.endswith("\n"):
        lines = lines[:-1]
    added, removed = patch_add_remove(c, path)
    if removed:
        raise RuntimeError(f"{path}: patch removes lines {removed!r}; append rule does not apply")
    to_add = []
    for a in added:
        if a.strip() != "" and (a in lines or a in to_add):
            continue
        to_add.append(a)
    if path == "Lib.lean":
        last = max(i for i, l in enumerate(lines) if l.startswith("import "))
        lines = lines[:last + 1] + to_add + lines[last + 1:]
    else:
        lines = lines + to_add
    with open(os.path.join(WT, path), "w") as f:
        f.write("\n".join(lines) + "\n")
    git("add", "--", path)
    return len(to_add), len(added) - len(to_add)

def commit(c, notes):
    an, ae, ad = out("log", "-1", "--format=%an%n%ae%n%aI", c).split("\n")[:3]
    body = out("log", "-1", "--format=%B", c).rstrip("\n") + "\n"
    msg = body + "\n" + f"(cherry picked from commit {c})\n"
    for n in notes:
        msg += f"Integration note: {n}\n"
    msg += "\n" + TRAILERS
    with open(f"{S}/msg.txt", "w") as f:
        f.write(msg)
    git("commit", "--quiet", "--no-verify", f"--author={an} <{ae}>", f"--date={ad}", "-F", f"{S}/msg.txt")
    return out("rev-parse", "HEAD").strip()

def main():
    commits = [l.strip() for l in open(f"{S}/commits.txt") if l.strip()]
    a, b = int(sys.argv[1]), int(sys.argv[2])
    for i in range(a, b + 1):
        c = commits[i - 1]
        if c[:8] in MANUAL:
            log(f"[{i}] {c[:8]} is MANUAL; stopping"); return 3
        if out("status", "--porcelain", "--untracked-files=no").strip():
            log(f"[{i}] tree dirty before {c[:8]}; stopping"); return 2
        r = git("cherry-pick", "--no-commit", c, check=False)
        method, notes = "cherry-pick", []
        if r.returncode != 0:
            unmerged = sorted(set(out("diff", "--name-only", "--diff-filter=U").split()))
            if not unmerged or not set(unmerged) <= APPEND_FILES:
                log(f"[{i}] {c[:8]} CONFLICT unmerged={unmerged}\n{r.stderr.decode(errors='replace')}")
                log("STOPPED; tree left in conflicted state"); return 2
            parts = []
            for u in unmerged:
                na, nd = resolve_append(c, u)
                parts.append(f"{u}(+{na} dup{nd})")
            method = "cherry-pick + append rule " + " ".join(parts)
        if out("diff", "--name-only", "--diff-filter=U").strip():
            log(f"[{i}] {c[:8]} still unmerged; STOP"); return 2
        new = commit(c, notes)
        log(f"[{i}] {c} -> {new} | {method}")
    return 0

if __name__ == "__main__":
    sys.exit(main())
