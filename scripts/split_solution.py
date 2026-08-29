#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Conservative, idempotent splitter for HopfProblem/Solution.lean.

The default mode is read-only validation.  `--emit-dir` creates a preview
outside the repository.  `--apply` is deliberately explicit and refuses any
source state except the pinned monolith or its own exact generated output.

The generated modules form a linear import chain.  Every theorem body is an
exact byte slice of the pinned source.  Attribute commands are classified from
their complete, possibly multiline header spans.  In this pinned source all
2,543 attribute commands end in `in` and are command-scoped wrappers, so no
file-local attribute state is replayed across imports.
"""

from __future__ import annotations

import argparse
import collections
import hashlib
import json
import os
import re
import tempfile
from dataclasses import dataclass
from pathlib import Path


SOURCE_SHA256 = "fda66f602707b290cf7fba9111506b39d72b2f509f9ebb44a1901471c69dec49"
LAKEFILE_SHA256 = "8b8b1ab4cf880b0b1977e6b98810ec3a3c5635e63ba250358d96f648e613f77d"
UPSTREAM_COMMIT = "9ac8a456b526527837d7082ff775213ca8bc9809"
EXPECTED_SPLIT_MANIFEST_SHA256 = "e424041bd1dc229874a16e4d691ec474b5dab29165bcdc42534445ef36b321b6"
EXPECTED_GENERATED_SHA256 = {
    "Hopf/DifferentialTopology.lean": "8c39ad7cd7f551aa29b14410402902f244185357cd0406b0d3bdefd7b127c922",
    "Hopf/Final.lean": "728de3345426f7d6e2d10f2fb3207d86acdc1b05f415f185c9115f34316ba3f8",
    "Hopf/FiniteCore.lean": "34bf3a36cb788afdacad34065c35a1594df1b8d454275d21d560c3f659ebf57e",
    "Hopf/Hurewicz.lean": "fb194b3f5e5fd4247b3e282085eba680bc9b14b41cecc3e40babd203684ae35d",
    "Hopf/LCP/AnalyticFillings.lean": "627f2ab8ff5f003077d00e9e04655af4eafa0acedf3238ed8dd5ce8fc6199721",
    "Hopf/LCP/BoundaryTopology.lean": "f7b85cf9e4f59ae4b9b2b432c1903e128d10c52bf3fabc0566123787810148b4",
    "Hopf/LCP/CuspFilling.lean": "91bdb09bb2a1361aa87602139a16682b59ae77f6654c40e04d3bb7f128359a11",
    "Hopf/LCP/GlobalAssembly.lean": "d23810d02de5a29cd42e2fe23541a3c6c1f4e2267c1eb50d0f0877607bea759d",
    "Hopf/LCP/IntegralHomology.lean": "16b31d6ff7fa6e4be546008d206f10fe4a01a28c848cd8abb20b57bd4f274ce2",
    "Hopf/LCP/LocalModels.lean": "f93d3e452afd5003dd7b09fcb585ebd3efd5a4fb87b6165140bdd007ea0e569a",
    "Hopf/LCP/PeriodConstruction.lean": "c378614b97dc1c4debf070674850ea663a7683acb354205874755f28f3d46207",
    "Hopf/LCP/Specialization.lean": "925e2b49ce6644ddcedcd54e04b7a122bf9d948cbc145753291542b99cd2ca6a",
    "Hopf/Recognition.lean": "b838dc050ba96186ce0e33fc958e928f15b9b4be4caf89d33dd955a4a069c6e8",
    "Hopf/SingularHomology.lean": "aeb93564943a02a093586d5ed8b39b2ca518e3d353e72757a1cde15482c28a16",
    "Hopf/SphereTopology.lean": "53994c834e931b04f17cf4bb8d516ee0bdf576d89fa8f0cac1f28d09f7130a1f",
    "PROVENANCE.md": "a5e9c8e7090aa5c38e9391fdab80124ce59c9ba0c29578e317494b49610aa99b",
    "Solution.lean": "384bee90125b548b4e4a521ea4bbc40bef26cb16ecd519c2b59c197a20973186",
    "lakefile.toml": "632af117709008f93551f251d61994e35ef8a25b64cd146c99377dd97f7f7960",
}

PROVENANCE = f"""# Provenance

This tree is a move-only reorganization of
[`plby/HopfProblem`](https://github.com/plby/HopfProblem) at commit
`{UPSTREAM_COMMIT}` (Apache-2.0).

The original `Solution.lean` had SHA-256 `{SOURCE_SHA256}`.  Its declaration
body, original lines 80--248811 inclusive, is partitioned into the `Hopf/`
modules listed in `SPLIT_MANIFEST.json`.  Each listed body is an exact byte
slice of that pinned source; no proof body or theorem statement is edited by
the extraction.  Module wrappers and imports are the only generated Lean text
outside those slices.  All 2,543 original attribute commands are command-scoped
wrappers and remain inside their exact body slices.

The full original attribution/license header is retained in every extracted
Lean module and in the public root aggregator.  `Solution.lean` imports
`Hopf.Final`.  The original `Challenge.lean`, `LICENSE`, and comparator
configuration are not changed by the splitter.  Mathematical equivalence must
additionally be certified by a green `lake build`, unchanged Comparator
verdict, and unchanged per-theorem axiom audit before committing the
reorganization.

The audited splitter is retained on the split branch as
`scripts/split_solution.py`.  It intentionally remains outside its own
generated-state hash map, avoiding circular self-authentication; Git and the
external attestation receipt pin the script itself.  A second run validates
all generator-owned output and leaves the script untouched.
""".encode()


@dataclass(frozen=True)
class Part:
    module: str
    first: int
    last: int

    @property
    def relpath(self) -> Path:
        return Path(*self.module.split(".")).with_suffix(".lean")


@dataclass(frozen=True)
class AttributeHeader:
    """The header portion of a top-level `attribute ... [in]` command.

    If `scoped` is true, the following command is the body governed by the
    trailing `in`; that body is deliberately not included in this span.
    """

    first: int
    last: int
    scoped: bool
    kind: str
    targets: tuple[str, ...]
    raw: bytes

    @property
    def lines(self) -> int:
        return self.last - self.first + 1


PARTS = (
    Part("Hopf.DifferentialTopology", 80, 31127),
    Part("Hopf.SingularHomology", 31128, 62391),
    Part("Hopf.SphereTopology", 62392, 81182),
    Part("Hopf.Hurewicz", 81183, 104759),
    Part("Hopf.FiniteCore", 104760, 105221),
    Part("Hopf.LCP.LocalModels", 105222, 115134),
    Part("Hopf.LCP.CuspFilling", 115135, 133801),
    Part("Hopf.LCP.Specialization", 133802, 148196),
    Part("Hopf.LCP.PeriodConstruction", 148197, 168788),
    Part("Hopf.LCP.AnalyticFillings", 168789, 182554),
    Part("Hopf.LCP.GlobalAssembly", 182555, 187882),
    Part("Hopf.LCP.BoundaryTopology", 187883, 211735),
    Part("Hopf.LCP.IntegralHomology", 211736, 237524),
    Part("Hopf.Recognition", 237525, 248758),
    Part("Hopf.Final", 248759, 248811),
)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def source_lines(data: bytes) -> list[bytes]:
    lines = data.splitlines(keepends=True)
    if len(lines) != 248818 or not data.endswith(b"\n"):
        raise SystemExit(f"unexpected source shape: {len(lines)} lines; final newline={data.endswith(b'\\n')}")
    return lines


def line_slice(lines: list[bytes], first: int, last: int) -> bytes:
    return b"".join(lines[first - 1 : last])


def ends_in_token(line: bytes) -> bool:
    """Whether the final non-comment token on a physical line is `in`."""
    code = line.split(b"--", 1)[0].strip()
    return bool(code) and code.split()[-1] == b"in"


def attribute_headers(lines: list[bytes]) -> list[AttributeHeader]:
    """Parse complete top-level attribute header spans from this source.

    Lean permits the target list and terminal `in` to continue on indented
    physical lines.  A header ends at its terminal `in`, or (for a genuinely
    persistent command) before the next blank/unindented line.  This parser is
    intentionally source-shaped and is pinned by a complete census below.
    """
    answer = []
    for index, first_line in enumerate(lines):
        if not first_line.startswith(b"attribute "):
            continue
        last = index
        while not ends_in_token(lines[last]):
            following = last + 1
            if following >= len(lines):
                break
            continuation = lines[following]
            if not continuation.strip() or not continuation[:1].isspace():
                break
            last = following
        raw = b"".join(lines[index : last + 1])
        raw_lines = raw.splitlines(keepends=True)
        if sum(ends_in_token(line) for line in raw_lines) > 1:
            raise SystemExit(
                f"attribute header has multiple terminal `in` lines at {index + 1}"
            )
        for continuation in raw_lines[1:]:
            if not re.fullmatch(rb"[ \t]+[A-Za-z0-9_.' ]+(?:in)?[ \t]*\r?\n?", continuation):
                raise SystemExit(
                    f"unexpected attribute continuation syntax at line {index + 2}"
                )
        normalized = b" ".join(raw.split())
        left = normalized.find(b"[")
        right = normalized.find(b"]", left + 1)
        if left < 0 or right < 0:
            raise SystemExit(f"malformed attribute header at line {index + 1}")
        kind = normalized[left + 1 : right].decode()
        tail = normalized[right + 1 :].split()
        scoped = bool(tail) and tail[-1] == b"in"
        if scoped:
            tail = tail[:-1]
            following = last + 1
            if (
                following >= len(lines)
                or not lines[following].strip()
                or lines[following][:1].isspace()
            ):
                raise SystemExit(
                    f"scoped attribute at lines {index + 1}--{last + 1} "
                    "does not immediately wrap an unindented command"
                )
        if not tail:
            raise SystemExit(f"attribute header has no target at line {index + 1}")
        answer.append(
            AttributeHeader(
                first=index + 1,
                last=last + 1,
                scoped=scoped,
                kind=kind,
                targets=tuple(token.decode() for token in tail),
                raw=raw,
            )
        )
    return answer


def attribute_census(headers: list[AttributeHeader]) -> dict:
    span_lengths = collections.Counter(header.lines for header in headers)
    kinds = collections.Counter(header.kind for header in headers)
    scoped = [header for header in headers if header.scoped]
    persistent = [header for header in headers if not header.scoped]
    first_line_scoped = sum(ends_in_token(header.raw.splitlines(keepends=True)[0]) for header in scoped)
    target_occurrences = sum(len(header.targets) for header in headers)
    by_start = {header.first: header for header in headers}
    nested_starts = {
        header.last + 1 for header in headers if header.last + 1 in by_start
    }
    chain_lengths = []
    for header in headers:
        if header.first in nested_starts:
            continue
        length = 1
        current = header
        while current.last + 1 in by_start:
            current = by_start[current.last + 1]
            length += 1
        chain_lengths.append(length)
    chain_length_counts = collections.Counter(chain_lengths)
    summary = {
        "total_attribute_commands": len(headers),
        "command_scoped": len(scoped),
        "persistent": len(persistent),
        "header_physical_lines": sum(header.lines for header in headers),
        "header_span_length_counts": {str(k): v for k, v in sorted(span_lengths.items())},
        "attribute_kind_counts": dict(sorted(kinds.items())),
        "terminal_in_on_first_line": first_line_scoped,
        "terminal_in_on_continuation": len(scoped) - first_line_scoped,
        "target_occurrences": target_occurrences,
        "distinct_targets": len({target for header in headers for target in header.targets}),
        "distinct_normalized_commands": len(
            {b" ".join(header.raw.split()) for header in headers}
        ),
        "immediately_wraps_another_attribute": len(nested_starts),
        "wrapper_chains": len(chain_lengths),
        "wrapper_chain_length_counts": {
            str(k): v for k, v in sorted(chain_length_counts.items())
        },
    }
    expected = {
        "total_attribute_commands": 2543,
        "command_scoped": 2543,
        "persistent": 0,
        "header_physical_lines": 4174,
        "header_span_length_counts": {"1": 1181, "2": 1148, "3": 176, "4": 21, "5": 17},
        "attribute_kind_counts": {
            "local instance": 2135,
            "local instance 100": 396,
            "local irreducible": 12,
        },
        "terminal_in_on_first_line": 1181,
        "terminal_in_on_continuation": 1362,
        "target_occurrences": 4312,
        "distinct_targets": 83,
        "distinct_normalized_commands": 103,
        "immediately_wraps_another_attribute": 179,
        "wrapper_chains": 2364,
        "wrapper_chain_length_counts": {"1": 2205, "2": 139, "3": 20},
    }
    if summary != expected:
        raise SystemExit(
            "attribute-command census mismatch; refusing extraction:\n"
            + json.dumps({"expected": expected, "actual": summary}, indent=2)
        )
    return summary


ENVIRONMENT_START = re.compile(
    rb"^(?:"
    rb"import\b|set_option\b|open\b|universe\b|noncomputable\s+section\b|"
    rb"namespace\b|section(?:\s|$)|end(?:\s|$)|"
    rb"local\s+(?:notation|infixr?|prefix|postfix|syntax|macro|instance|attribute)\b|"
    rb"(?:notation|infixr?|prefix|postfix|syntax|macro|macro_rules|elab|elab_rules)\b|"
    rb"(?:scoped|export|variable|variables|include|omit|initialize|builtin_initialize|"
    rb"register_option|declare_syntax_cat)\b|#print\b"
    rb")"
)


def environment_census(lines: list[bytes]) -> dict:
    """Inventory every non-attribute top-level environment-shaped command."""
    commands = []
    for index, line in enumerate(lines):
        if line[:1].isspace() or not ENVIRONMENT_START.match(line):
            continue
        last = index
        # The only multiline command in this pinned inventory is `open scoped`,
        # but consume its full indented header rather than assuming a line count.
        if line.startswith(b"open scoped "):
            while (
                last + 1 < len(lines)
                and lines[last + 1].strip()
                and lines[last + 1][:1].isspace()
            ):
                last += 1
        normalized = b" ".join(b"".join(lines[index : last + 1]).split()).decode()
        if line.startswith(b"open scoped "):
            kind = "open scoped"
        elif line.startswith(b"noncomputable section"):
            kind = "noncomputable section"
        elif line.startswith(b"local infix"):
            kind = "local infix"
        elif line.startswith(b"local notation"):
            kind = "local notation"
        else:
            kind = line.split(maxsplit=1)[0].decode()
        commands.append(
            {
                "kind": kind,
                "first": index + 1,
                "last": last + 1,
                "normalized": normalized,
            }
        )
    expected = [
        {"kind": "import", "first": 59, "last": 59, "normalized": "import Mathlib"},
        {
            "kind": "set_option",
            "first": 61,
            "last": 61,
            "normalized": "set_option maxSynthPendingDepth 3",
        },
        {
            "kind": "open",
            "first": 63,
            "last": 63,
            "normalized": "open Set Function Filter Manifold Topology",
        },
        {
            "kind": "open scoped",
            "first": 65,
            "last": 68,
            "normalized": (
                "open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate "
                "ContDiff ContinuousMap Convolution ENNReal EuclideanSpace Fin.NatCast "
                "InnerProductSpace Interval Matrix MatrixGroups Modular NNReal Pointwise "
                "RealInnerProductSpace TensorProduct UniformConvergence Uniformity "
                "UpperHalfPlane"
            ),
        },
        {"kind": "universe", "first": 70, "last": 70, "normalized": "universe u v"},
        {
            "kind": "noncomputable section",
            "first": 72,
            "last": 72,
            "normalized": "noncomputable section",
        },
        {
            "kind": "namespace",
            "first": 74,
            "last": 74,
            "normalized": "namespace Mathoverflow1973",
        },
        {
            "kind": "local infix",
            "first": 76,
            "last": 76,
            "normalized": 'local infixr:80 " ≫ₚ " => Path.trans',
        },
        {
            "kind": "local notation",
            "first": 78,
            "last": 78,
            "normalized": 'local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f',
        },
        {
            "kind": "#print",
            "first": 248813,
            "last": 248813,
            "normalized": "#print axioms mathoverflow_1973",
        },
        {
            "kind": "end",
            "first": 248816,
            "last": 248816,
            "normalized": "end Mathoverflow1973",
        },
        {"kind": "end", "first": 248818, "last": 248818, "normalized": "end"},
    ]
    if commands != expected:
        raise SystemExit(
            "top-level environment-command census mismatch; refusing extraction:\n"
            + json.dumps({"expected": expected, "actual": commands}, indent=2)
        )
    context = line_slice(lines, 61, 78)
    return {
        "commands": commands,
        "repeated_module_context_first": 61,
        "repeated_module_context_last": 78,
        "repeated_module_context_lines": 18,
        "repeated_module_context_sha256": digest(context),
        "environment_state_commands_after_line_78_before_diagnostic": 0,
        "later_local_notation_macro_export_variable_commands": 0,
        "attribute_commands_audited_separately": 2543,
    }


def persistent_local_attributes(headers: list[AttributeHeader], before: int) -> bytes:
    """Replay complete persistent local-attribute headers active at `before`."""
    selected = []
    for header in headers:
        if header.first >= before:
            break
        if header.last >= before:
            raise SystemExit(f"module boundary {before} splits attribute header at {header.first}")
        if not header.scoped and header.kind.startswith("local "):
            selected.append(header.raw)
    return b"".join(selected)


def extraction_header(part: Part) -> bytes:
    return (
        "/-\n"
        f"Move-only extraction from HopfProblem Solution.lean at {UPSTREAM_COMMIT}.\n"
        f"Original source lines {part.first}--{part.last}; see PROVENANCE.md.\n"
        "-/\n\n"
    ).encode()


def generated_files(monolith: bytes, lakefile: bytes) -> dict[Path, bytes]:
    if digest(monolith) != SOURCE_SHA256:
        raise SystemExit(f"refusing unpinned Solution.lean sha256={digest(monolith)}")
    if digest(lakefile) != LAKEFILE_SHA256:
        raise SystemExit(f"refusing unpinned lakefile.toml sha256={digest(lakefile)}")
    lines = source_lines(monolith)
    attributes = attribute_headers(lines)
    attribute_census(attributes)
    environment_census(lines)
    common = line_slice(lines, 61, 78) + b"\n"
    close = b"\nend Mathoverflow1973\n\nend\n"
    files: dict[Path, bytes] = {}
    previous = "Mathlib"
    for part in PARTS:
        header = line_slice(lines, 1, 58) + extraction_header(part)
        replay = persistent_local_attributes(attributes, part.first)
        if replay:
            replay += b"\n"
        files[part.relpath] = (
            header
            + f"import {previous}\n\n".encode()
            + common
            + replay
            + line_slice(lines, part.first, part.last)
            + close
        )
        previous = part.module

    # Keep the upstream legal/provenance header and diagnostic at the public root.
    files[Path("Solution.lean")] = (
        line_slice(lines, 1, 58)
        + b"import Hopf.Final\n\n"
        + b"#print axioms Mathoverflow1973.mathoverflow_1973\n"
        + line_slice(lines, 248814, 248814)
    )
    files[Path("PROVENANCE.md")] = PROVENANCE

    marker = b'[[lean_lib]]\nname = "Hopf"\n\n'
    if marker in lakefile:
        new_lakefile = lakefile
    else:
        anchor = b'[[lean_lib]]\nname = "Challenge"\n\n'
        if lakefile.count(anchor) != 1:
            raise SystemExit("lakefile Challenge library anchor not unique")
        new_lakefile = lakefile.replace(anchor, marker + anchor)
    files[Path("lakefile.toml")] = new_lakefile
    return files


def manifest(original: bytes, files: dict[Path, bytes]) -> dict:
    lines = source_lines(original)
    attributes = attribute_headers(lines)
    return {
        "upstream_commit": UPSTREAM_COMMIT,
        "source_sha256": digest(original),
        "body_ranges_are_one_based_inclusive": True,
        "attribute_command_audit": attribute_census(attributes),
        "generated_local_attribute_replays": {
            "commands": 0,
            "physical_lines": 0,
        },
        "top_level_environment_state_audit": environment_census(lines),
        "parts": [
            {
                "module": p.module,
                "path": str(p.relpath),
                "first": p.first,
                "last": p.last,
                "body_sha256": digest(b"".join(lines[p.first - 1 : p.last])),
                "generated_sha256": digest(files[p.relpath]),
                "persistent_local_attribute_commands_replayed": 0,
                "persistent_local_attribute_lines_replayed": 0,
            }
            for p in PARTS
        ],
        "generated": {str(path): digest(data) for path, data in sorted(files.items(), key=lambda x: str(x[0]))},
    }


def check_partition(original: bytes) -> None:
    lines = source_lines(original)
    assert PARTS[0].first == 80
    assert PARTS[-1].last == 248811
    for a, b in zip(PARTS, PARTS[1:]):
        if a.last + 1 != b.first:
            raise SystemExit(f"gap or overlap: {a} then {b}")
    rebuilt = b"".join(line_slice(lines, p.first, p.last) for p in PARTS)
    expected = line_slice(lines, 80, 248811)
    if rebuilt != expected:
        raise SystemExit("body reconstruction mismatch")


def write_preview(dest: Path, files: dict[Path, bytes], mf: dict) -> None:
    if dest.exists() and any(dest.iterdir()):
        raise SystemExit(f"preview directory is not empty: {dest}")
    dest.mkdir(parents=True, exist_ok=True)
    for rel, data in files.items():
        path = dest / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)


def validate_generated_state(repo: Path) -> None:
    receipt_path = repo / "SPLIT_MANIFEST.json"
    if not receipt_path.is_file():
        raise SystemExit("source is not the monolith and SPLIT_MANIFEST.json is absent")
    receipt_bytes = receipt_path.read_bytes()
    actual_receipt_hash = digest(receipt_bytes)
    if actual_receipt_hash != EXPECTED_SPLIT_MANIFEST_SHA256:
        raise SystemExit(
            "generated-state manifest mismatch: expected "
            f"{EXPECTED_SPLIT_MANIFEST_SHA256}, got {actual_receipt_hash}"
        )
    receipt = json.loads(receipt_bytes)
    if receipt.get("generated") != EXPECTED_GENERATED_SHA256:
        raise SystemExit("pinned manifest generated-path/hash map mismatch")
    failures = []
    for rel_text, expected in EXPECTED_GENERATED_SHA256.items():
        path = repo / rel_text
        actual = digest(path.read_bytes()) if path.is_file() else "MISSING"
        if actual != expected:
            failures.append(f"{rel_text}: expected {expected}, got {actual}")
    expected_hopf = {
        rel for rel in EXPECTED_GENERATED_SHA256 if rel.startswith("Hopf/")
    }
    hopf_dir = repo / "Hopf"
    actual_hopf = (
        {
            str(path.relative_to(repo))
            for path in hopf_dir.rglob("*")
            if path.is_file()
        }
        if hopf_dir.is_dir()
        else set()
    )
    if actual_hopf != expected_hopf:
        failures.append(
            "Hopf/ owned-file set mismatch: expected "
            f"{sorted(expected_hopf)}, got {sorted(actual_hopf)}"
        )
    obsolete_preview_receipt = repo / "split-manifest.json"
    if obsolete_preview_receipt.exists():
        failures.append("unexpected obsolete split-manifest.json")
    if failures:
        raise SystemExit("generated-state mismatch:\n" + "\n".join(failures))


def apply(repo: Path, files: dict[Path, bytes]) -> None:
    # A mixed state is never repaired implicitly.
    hopf_dir = repo / "Hopf"
    if hopf_dir.exists():
        raise SystemExit("refusing mixed state: Hopf/ already exists but generated state does not match")
    if digest((repo / "Solution.lean").read_bytes()) != SOURCE_SHA256:
        raise SystemExit("refusing to overwrite non-baseline Solution.lean")
    if digest((repo / "lakefile.toml").read_bytes()) != LAKEFILE_SHA256:
        raise SystemExit("refusing to overwrite non-baseline lakefile.toml")
    with tempfile.TemporaryDirectory(prefix="hopf-split-", dir=repo) as temp_name:
        temp = Path(temp_name)
        for rel, data in files.items():
            path = temp / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        # Validate every staged byte before making the explicit replacements.
        for rel, data in files.items():
            if (temp / rel).read_bytes() != data:
                raise SystemExit(f"staging verification failed: {rel}")
        # Install imported modules first and the public aggregator last.
        order = sorted(
            files,
            key=lambda p: (
                p == Path("Solution.lean"),
                p == Path("lakefile.toml"),
                str(p),
            ),
        )
        for rel in order:
            target = repo / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            os.replace(temp / rel, target)
    print("split applied")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("repo", type=Path)
    modes = ap.add_mutually_exclusive_group()
    modes.add_argument("--emit-dir", type=Path)
    modes.add_argument("--apply", action="store_true")
    args = ap.parse_args()
    repo = args.repo.resolve()
    original = (repo / "Solution.lean").read_bytes()
    lakefile = (repo / "lakefile.toml").read_bytes()
    # In generated state the original is no longer present.  Verification there
    # is hash-based and needs the original receipt emitted during the first run.
    if digest(original) != SOURCE_SHA256:
        validate_generated_state(repo)
        print("already split exactly; no-op")
        return
    check_partition(original)
    files = generated_files(original, lakefile)
    mf = manifest(original, files)
    files[Path("SPLIT_MANIFEST.json")] = (json.dumps(mf, indent=2) + "\n").encode()
    if args.emit_dir:
        write_preview(args.emit_dir.resolve(), files, mf)
        print(args.emit_dir.resolve())
    elif args.apply:
        apply(repo, files)
    else:
        print(json.dumps(mf, indent=2))


if __name__ == "__main__":
    main()
