#!/usr/bin/env python3
"""Replace the stock 4-line `open scoped` block by the minimised namespace list
computed per file (see RECEIPT.md, category (b))."""
import json, pathlib, sys
ROOT = pathlib.Path('/home/goblin/hopf-r7-preamble')
STOCK = [
 "open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap",
 "  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups",
 "  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity",
 "  UpperHalfPlane",
]
data = json.load(open(sys.argv[1]))
n = len(STOCK)
for rel, v in sorted(data.items()):
    keep = v["keep"]
    assert keep, rel
    f = ROOT / rel
    lines = f.read_text(encoding='utf-8').split('\n')
    for i in range(len(lines) - n + 1):
        if lines[i:i+n] == STOCK:
            lines[i:i+n] = ["open scoped " + " ".join(keep)]
            f.write_text("\n".join(lines), encoding='utf-8')
            print(f"{rel}: open scoped {' '.join(keep)}")
            break
    else:
        raise SystemExit("stock block not found: " + rel)
