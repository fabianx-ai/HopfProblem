#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Ratchet counter for generic ("stock") mathematics still living under `Hopf/`.

Rule (lean-protocol.md, Stage 4): general textbook mathematics is FREE and belongs under
`Lib/`; a project directory holds only project data and thin CHARGED adapters.  Until the
recognition tail is fully extracted, `Hopf/` still contains generic declarations.  This
script counts them and enforces that the count may only go down.

What is counted.  Every top-level declaration (`theorem|lemma|def|abbrev|structure|
class|inductive|instance|opaque`, possibly prefixed by attributes/`private`/`protected`/
`noncomputable`/`nonrec`) in every `Hopf/**/*.lean` file whose dotted name starts with one
of the *stock prefixes* listed in `scripts/lib_stock_prefixes.txt` (one entry per line,
`#` comments allowed).  An entry is either a namespace prefix `Smale` (matches `Smale.*`),
a deeper prefix `CuspRetraction.Patching` (matches `CuspRetraction.Patching.*` only), or a
file-scoped prefix `Hopf/SphereTopology.lean:CuspCentralHomology` (matches only in that
file; used when one namespace name is generic in one slice and project-specific in another).
Matching is on whole dotted components, so `Smale` does not match `SmaleX.foo`.  The prefixes are the top-level namespaces which the census in
`Lib/EXTRACTION_PLAN.md` classified GENERIC-TEXTBOOK or GENERIC-BUT-SPECIALIZED; they are
the natural unit because the `Hopf/` files carry no `section`/`namespace` structure and
no docstrings — the declaration-name prefix is the only block marker.

Ratchet.  `scripts/lib_stock_baseline.txt` holds one integer: the committed stock count.
With `--check` the script FAILS (exit 1) when the current count exceeds the baseline
(generic mathematics was added to `Hopf/`, or a stock prefix was re-used for new project
code) and PASSES otherwise.  With `--update` the baseline is rewritten to the current count
only when the count decreased; growing the baseline by hand must be justified in the commit
message.  Without either flag the script only reports.  A second, independent guard
FAILS when any `Lib/**/*.lean` file imports a `Hopf.*`, `S6.*`, `S6Shortcuts`, `Challenge`
or `Solution` module (Lib may never depend on the project).

Run from the repository root:

    python3 scripts/lib_stock_census.py             # report count + Lib import guard
    python3 scripts/lib_stock_census.py --check     # CI/ratchet step: fail if count > baseline
    python3 scripts/lib_stock_census.py --update    # lower the baseline if the count fell
    python3 scripts/lib_stock_census.py --by-file   # ... and print the per-file/per-prefix table
"""
from __future__ import annotations

import argparse
import collections
import os
import re
import sys

DECL_RE = re.compile(
    r'^(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+)*'
    r'(theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque)\s+([^\s:({\[]+)',
    re.M)
IMPORT_RE = re.compile(r'^(?:public\s+)?import\s+([A-Za-z0-9_.]+)', re.M)
FORBIDDEN_LIB_IMPORTS = ('Hopf.', 'S6.', 'S6Shortcuts', 'Challenge', 'Solution')
PREFIX_FILE = os.path.join('scripts', 'lib_stock_prefixes.txt')
BASELINE_FILE = os.path.join('scripts', 'lib_stock_baseline.txt')


def lean_files(root: str, top: str) -> list[str]:
    out: list[str] = []
    for dirpath, _dirs, files in os.walk(os.path.join(root, top)):
        for f in files:
            if f.endswith('.lean'):
                out.append(os.path.join(dirpath, f))
    return sorted(out)


def strip_comments(src: str) -> str:
    src = re.sub(r'/-.*?-/', '', src, flags=re.S)
    return re.sub(r'--[^\n]*', '', src)


def load_prefixes(path: str) -> list[str]:
    if not os.path.exists(path):
        sys.exit(f'FAIL: missing prefix list {path}')
    with open(path, encoding='utf-8') as f:
        return [l.strip() for l in f if l.strip() and not l.startswith('#')]


def match_entry(entry: str, rel: str, name: str) -> bool:
    """Does declaration `name` in file `rel` match the prefix-list entry?"""
    if ':' in entry:
        scope, entry = entry.split(':', 1)
        if rel != scope:
            return False
    comps = name.split('.')
    want = entry.split('.')
    return comps[:len(want)] == want and len(comps) > len(want)


def stock_count(root: str, prefixes: list[str]):
    """Return (total, per_file_entry_counter, unmatched_entries)."""
    table: dict[str, collections.Counter] = collections.defaultdict(collections.Counter)
    seen: set[str] = set()
    for path in lean_files(root, 'Hopf'):
        with open(path, encoding='utf-8') as f:
            src = strip_comments(f.read())
        rel = os.path.relpath(path, root)
        for _kind, name in DECL_RE.findall(src):
            for entry in prefixes:
                if match_entry(entry, rel, name):
                    table[rel][entry] += 1
                    seen.add(entry)
                    break   # count each declaration at most once
    total = sum(sum(c.values()) for c in table.values())
    return total, table, [p for p in prefixes if p not in seen]


def lib_import_guard(root: str) -> list[str]:
    bad: list[str] = []
    for path in lean_files(root, 'Lib'):
        with open(path, encoding='utf-8') as f:
            for mod in IMPORT_RE.findall(f.read()):
                if mod.startswith(FORBIDDEN_LIB_IMPORTS):
                    bad.append(f'{os.path.relpath(path, root)} imports {mod}')
    return bad


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--root', default='.', help='repository root (default: cwd)')
    ap.add_argument('--check', action='store_true', help='fail if the count exceeds the baseline')
    ap.add_argument('--update', action='store_true', help='lower the baseline if the count fell')
    ap.add_argument('--by-file', action='store_true', help='print the per-file table')
    ap.add_argument('--prefixes', default=None, help=f'prefix list (default: {PREFIX_FILE})')
    ap.add_argument('--baseline', default=None, help=f'baseline file (default: {BASELINE_FILE})')
    args = ap.parse_args()
    root = os.path.abspath(args.root)

    prefixes = load_prefixes(args.prefixes or os.path.join(root, PREFIX_FILE))
    total, table, unmatched = stock_count(root, prefixes)
    if args.by_file:
        for rel in sorted(table):
            row = ', '.join(f'{p}:{c}' for p, c in table[rel].most_common())
            print(f'{rel:40s} {sum(table[rel].values()):6d}  {row}')
    print(f'stock declarations under Hopf/: {total}  (prefixes: {len(prefixes)}, '
          f'prefixes now absent from Hopf/: {len(unmatched)})')
    for p in unmatched:
        print(f'  extracted (no longer under Hopf/): {p}')

    status = 0
    bad = lib_import_guard(root)
    for b in bad:
        print(f'FAIL: Lib depends on project: {b}')
        status = 1

    bpath = args.baseline or os.path.join(root, BASELINE_FILE)
    if os.path.exists(bpath):
        with open(bpath, encoding='utf-8') as f:
            baseline = int(f.read().strip() or '0')
        if total > baseline:
            print(f'{"FAIL" if args.check else "WARN"}: stock count {total} exceeds committed '
                  f'baseline {baseline} ({BASELINE_FILE}); generic mathematics may only leave '
                  f'Hopf/, never enter it')
            if args.check:
                status = 1
        elif total < baseline and args.update:
            with open(bpath, 'w', encoding='utf-8') as f:
                f.write(f'{total}\n')
            print(f'baseline lowered {baseline} -> {total}')
        else:
            print(f'ratchet {"PASS" if args.check else "OK"}: {total} <= baseline {baseline}')
    else:
        if args.update:
            os.makedirs(os.path.dirname(bpath), exist_ok=True)
            with open(bpath, 'w', encoding='utf-8') as f:
                f.write(f'{total}\n')
            print(f'baseline created: {total}')
        else:
            print(f'WARN: no {BASELINE_FILE}; run with --update to create it')
    return status


if __name__ == '__main__':
    sys.exit(main())
