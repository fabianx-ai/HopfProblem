#!/usr/bin/env python3
"""Round 7 preamble cleanup: remove stock copied preamble lines from Lib/*.lean.

Four categories, one per invocation.  Nothing but whole lines is ever deleted;
no declaration is added, removed or edited.  See RECEIPT.md for the rules.

    usage: preamble_clean.py {synth,openscoped,universe,notation} [--apply]
Without --apply the script only reports what it would do.
"""
import pathlib, re, sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
LIB = ROOT / "Lib"

# ---------------------------------------------------------------- helpers ---
def lean_files():
    return sorted(p for p in LIB.rglob("*.lean"))

def drop(lines, idxs):
    """Delete the given line indices; also drop one trailing blank line when
    that would otherwise leave two consecutive blank lines."""
    idxs = set(idxs)
    extra = set()
    for i in sorted(idxs):
        j = i + 1
        while j in idxs:
            j += 1
        if (j < len(lines) and lines[j].strip() == ""
                and i - 1 >= 0 and lines[i - 1].strip() == ""
                and j not in idxs and j not in extra):
            extra.add(j)
    kill = idxs | extra
    return [l for k, l in enumerate(lines) if k not in kill]

def word(n):
    return r"(?<![A-Za-z0-9_₀-₉'])" + re.escape(n) + r"(?![A-Za-z0-9_₀-₉'])"

# ------------------------------------------------------- (a) set_option ---
SYNTH = re.compile(r"^set_option\s+maxSynthPendingDepth\s+\d+\s*$")

def cat_synth(text):
    lines = text.split("\n")
    hit = [i for i, l in enumerate(lines) if SYNTH.match(l)]
    return hit, lines

# ------------------------------------------------------ (b) open scoped ---
STOCK_OPEN = [
    "open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap",
    "  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups",
    "  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity",
    "  UpperHalfPlane",
]

def cat_openscoped(text):
    lines = text.split("\n")
    n = len(STOCK_OPEN)
    for i in range(len(lines) - n + 1):
        if lines[i:i + n] == STOCK_OPEN:
            return list(range(i, i + n)), lines
    return [], lines

# --------------------------------------------------------- (c) universe ---
UNIV = re.compile(r"^universe\s+([A-Za-z_][A-Za-z0-9_'₀-₉]*"
                  r"(?:\s+[A-Za-z_][A-Za-z0-9_'₀-₉]*)*)\s*$")

def universe_used(name, rest):
    b = word(name)
    pats = [
        r"(?:Type|Sort)\s*" + b,             # Type u / Sort v
        r"\.\s*\{[^}]*" + b + r"[^}]*\}",    # C.{u} / Type.{u, v}
        r"\b[im]?max\b[^\n]{0,80}?" + b,     # max u v / imax u v
        r"(?:Type|Sort)\s*\([^)\n]*" + b,    # Type (max u v)
        b + r"\s*\+\s*\d",                   # u + 1
        r"universe\b[^\n]*" + b,             # another universe command
    ]
    return any(re.search(p, rest) for p in pats)

def cat_universe(text):
    lines = text.split("\n")
    hit = []
    for i, l in enumerate(lines):
        m = UNIV.match(l)
        if not m:
            continue
        names = m.group(1).split()
        rest = "\n".join(x for j, x in enumerate(lines) if j != i)
        if all(not universe_used(n, rest) for n in names):
            hit.append(i)
    return hit, lines

# --------------------------------------------------------- (d) notation ---
NOTA = re.compile(r"^local\s+(?:notation|infix|infixr|infixl|prefix|postfix)\b")

def cat_notation(text):
    lines = text.split("\n")
    hit = []
    for i, l in enumerate(lines):
        if not NOTA.match(l):
            continue
        lhs = l.split("=>")[0]
        lits = [s.strip() for s in re.findall(r'"([^"]*)"', lhs)]
        lits = [s for s in lits if s]
        if not lits:
            continue
        tok = max(lits, key=len)          # the distinguishing token
        rest = "\n".join(x for j, x in enumerate(lines) if j != i)
        if tok not in rest:
            hit.append(i)
    return hit, lines

CATS = {"synth": cat_synth, "openscoped": cat_openscoped,
        "universe": cat_universe, "notation": cat_notation}

def main():
    cat = sys.argv[1]
    apply = "--apply" in sys.argv[2:]
    fn = CATS[cat]
    nf = nl = 0
    for f in lean_files():
        text = f.read_text(encoding="utf-8")
        hit, lines = fn(text)
        if not hit:
            continue
        nf += 1
        nl += len(hit)
        print(f"{f.relative_to(ROOT)}: {len(hit)} line(s): " +
              " | ".join(lines[i].strip()[:60] for i in hit))
        if apply:
            f.write_text("\n".join(drop(lines, hit)), encoding="utf-8")
    print(f"TOTAL {cat}: {nf} files, {nl} lines" + ("" if apply else " (dry run)"))

main()
