#!/usr/bin/env python3
"""Replay the Lib/ + Lib.lean history of center-solution onto lib/integration, one commit per commit."""
import os, subprocess, sys

WT = "/home/goblin/hopf-lib-integration"
JOB = "/home/goblin/.claude/jobs/06995e68/tmp"
COMMITS = f"{JOB}/int6_commits.txt"
CLASS = f"{JOB}/int6_class.txt"
OUT = f"{JOB}/int6-replay"
LOG = f"{OUT}/replay.log"
APPEND_FILES = {"Lib.lean", "Lib/AxiomAudit.lean"}

ENV = dict(os.environ, GIT_CONFIG_COUNT="1", GIT_CONFIG_KEY_0="safe.directory", GIT_CONFIG_VALUE_0="*")

logf = open(LOG, "a")
def log(msg):
    print(msg, flush=True)
    logf.write(msg + "\n"); logf.flush()

def git(*args, check=True, input=None, env=None, binary=False):
    r = subprocess.run(["git", *args], cwd=WT, env=env or ENV, input=input,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if check and r.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)} failed ({r.returncode}):\n{r.stderr.decode(errors='replace')}")
    return r if binary else r

def gitout(*args, **kw):
    return git(*args, **kw).stdout.decode()

def patch_add_remove(c, path):
    """Lines added / removed to `path` by commit c (content only, patch order)."""
    d = gitout("diff", f"{c}^", c, "--", path)
    added, removed = [], []
    in_hunk = False
    for line in d.split("\n"):
        if line.startswith("@@"):
            in_hunk = True; continue
        if not in_hunk:
            continue
        if line.startswith("diff --git"):
            in_hunk = False; continue
        if line.startswith("+"):
            added.append(line[1:])
        elif line.startswith("-"):
            removed.append(line[1:])
    return added, removed

def resolve_append(c, path):
    head = gitout("show", f"HEAD:{path}")
    lines = head.split("\n")
    trailing_nl = head.endswith("\n")
    if trailing_nl:
        lines = lines[:-1]
    added, removed = patch_add_remove(c, path)
    n_removed = 0
    for r in removed:
        if r in lines:
            lines.remove(r); n_removed += 1
    to_add = []
    for a in added:
        if a.strip() != "" and (a in lines or a in to_add):
            continue
        to_add.append(a)
    if path == "Lib.lean":
        last_import = max((i for i, l in enumerate(lines) if l.startswith("import ")), default=-1)
        lines = lines[:last_import + 1] + to_add + lines[last_import + 1:]
    else:
        lines = lines + to_add
    text = "\n".join(lines) + "\n"
    with open(os.path.join(WT, path), "w") as f:
        f.write(text)
    git("add", "--", path)
    return len(to_add), n_removed, len(added) - len(to_add)

def unmerged_status():
    """{path: XY} for unmerged entries."""
    out = {}
    for l in gitout("status", "--porcelain", "--untracked-files=no").split("\n"):
        if len(l) > 3 and ("U" in l[:2] or l[:2] == "AA" or l[:2] == "DD"):
            out[l[3:]] = l[:2]
    return out

AA_NOTE_380 = ("Lib/Topology/MappingTorus/Basic.lean kept as on 22d23761 (added/added: the 22d23761 file is "
               "the superset the merge b1179031 itself kept)")

def main():
    commits = [l.strip() for l in open(COMMITS) if l.strip()]
    cls = {}
    for l in open(CLASS):
        parts = l.split()
        if parts:
            cls[parts[0]] = (parts[1], parts[2:])
    start = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    in_progress = "--in-progress" in sys.argv   # commits[start] is already applied and sitting unmerged
    stats = {"replayed": 0, "merge": 0, "empty": 0, "noop": 0, "append": {}, "dedup": {}, "aa": []}
    log(f"=== replay start at index {start}, HEAD={gitout('rev-parse','HEAD').strip()}")
    for idx, c in enumerate(commits):
        if idx < start:
            continue
        kind, extra = cls[c]
        short = c[:8]
        if kind == "MERGE":
            log(f"[{idx+1}/{len(commits)}] {short} MERGE skipped")
            stats["merge"] += 1
            continue
        patch = git("diff", "--binary", f"{c}^", c, "--", "Lib", "Lib.lean").stdout
        if not patch.strip():
            log(f"[{idx+1}/{len(commits)}] {short} EMPTY Lib diff, skipped")
            stats["empty"] += 1
            continue
        if in_progress and idx == start:
            class R: returncode = 1; stderr = b"(resumed in-progress conflict)"
            r = R()
        else:
            r = git("apply", "-3", "--index", check=False, input=patch)
        used_append = []
        notes = []
        if r.returncode != 0:
            st = unmerged_status()
            unmerged = sorted(st)
            # added/added rule: keep ours (HEAD) and note it
            for u in list(unmerged):
                if st[u] == "AA":
                    git("checkout", "--ours", "--", u)
                    git("add", "--", u)
                    note = AA_NOTE_380 if (c.startswith("380ddd11") and u == "Lib/Topology/MappingTorus/Basic.lean") \
                        else f"{u} kept as on lib/integration HEAD (added/added conflict: ours kept)"
                    notes.append(note)
                    stats["aa"].append(f"{short}:{u}")
                    unmerged.remove(u)
            if unmerged and not set(unmerged) <= APPEND_FILES:
                log(f"[{idx+1}/{len(commits)}] {short} CONFLICT outside append files or apply failure; unmerged={unmerged}")
                log("git apply stderr:\n" + r.stderr.decode(errors="replace"))
                for u in unmerged:
                    log(f"--- conflict markers in {u} ---")
                    log(subprocess.run(["grep", "-n", "-A3", "-E", "^(<<<<<<<|=======|>>>>>>>)", u], cwd=WT,
                                       stdout=subprocess.PIPE).stdout.decode(errors="replace"))
                log("STOPPED; tree left in conflicted state")
                return 2
            for u in unmerged:
                na, nr, nd = resolve_append(c, u)
                used_append.append(f"{u}(+{na} -{nr} dup{nd})")
                stats["append"][u] = stats["append"].get(u, 0) + 1
                stats["dedup"][u] = stats["dedup"].get(u, 0) + nd
        # sanity: nothing unmerged, nothing unstaged in Lib
        if gitout("diff", "--name-only", "--diff-filter=U").strip():
            log(f"[{idx+1}] {short} still unmerged after resolution; STOP"); return 2
        if git("diff", "--cached", "--quiet", check=False).returncode == 0:
            log(f"[{idx+1}/{len(commits)}] {short} NOOP (diff non-empty but no staged change), skipped")
            stats["noop"] += 1
            continue
        an, ae, aI, cI = gitout("log", "-1", "--format=%an%n%ae%n%aI%n%cI", c).split("\n")[:4]
        body = gitout("log", "-1", "--format=%B", c).rstrip("\n") + "\n"
        msg = body + "\n" + f"(cherry picked from commit {c})\n"
        if kind == "MIXED":
            msg += "Lib paths only; the original commit also changed: " + " ".join(extra) + "\n"
        for note in notes:
            msg += note + "\n"
        msgfile = f"{OUT}/msg.txt"
        with open(msgfile, "w") as f:
            f.write(msg)
        env = dict(ENV, GIT_COMMITTER_DATE=cI)
        git("commit", "--quiet", "--no-verify", f"--author={an} <{ae}>", f"--date={aI}", "-F", msgfile, env=env)
        new = gitout("rev-parse", "--short", "HEAD").strip()
        stats["replayed"] += 1
        log(f"[{idx+1}/{len(commits)}] {short} {kind} -> {new}" + (f" append-rule: {' '.join(used_append)}" if used_append else "") + (f" AA-rule: {notes}" if notes else ""))
    log(f"=== done: {stats}")
    log(f"HEAD={gitout('rev-parse','HEAD').strip()}")
    return 0

if __name__ == "__main__":
    sys.exit(main())
