#!/bin/bash
cd /home/ox-alpha/HopfProblem
export PATH=/tmp/shared-lean-copy/toolchain-v4.33.0/bin:$PATH
export LEAN_PATH=/tmp/shared-lean-copy/packages/Cli/.lake/build/lib/lean:/tmp/shared-lean-copy/packages/lean4export/.lake/build/lib/lean:/tmp/shared-lean-copy/packages/batteries/.lake/build/lib/lean:/tmp/shared-lean-copy/packages/Qq/.lake/build/lib/lean:/tmp/shared-lean-copy/packages/aesop/.lake/build/lib/lean:/tmp/shared-lean-copy/packages/proofwidgets/.lake/build/lib/lean:/tmp/shared-lean-copy/packages/importGraph/.lake/build/lib/lean:/tmp/shared-lean-copy/packages/LeanSearchClient/.lake/build/lib/lean:/tmp/shared-lean-copy/packages/plausible/.lake/build/lib/lean:/tmp/shared-lean-copy/packages/Comparator/.lake/build/lib/lean:/tmp/shared-lean-copy/packages/mathlib/.lake/build/lib/lean:/home/ox-alpha/HopfProblem/.lake/build/lib/lean
LOGD=/tmp/sidekick-modconv-batch3-1789272770/cone
FILES="Lib/AlgebraicTopology/Hurewicz/SimplexCube.lean
Lib/AlgebraicTopology/Hurewicz/CubeTriangulation.lean
Lib/AlgebraicTopology/Hurewicz/HomotopyExtension.lean
Lib/AlgebraicTopology/Hurewicz/PrismOperator.lean
Lib/AlgebraicTopology/Hurewicz/Subdivision.lean
Lib/AlgebraicTopology/Hurewicz/CubeGluing.lean
Lib/AlgebraicTopology/Hurewicz/Degree.lean
Lib/AlgebraicTopology/Hurewicz/CubeChainDecomposition.lean
Lib/AlgebraicTopology/Hurewicz/Straightening.lean
Lib/AlgebraicTopology/Hurewicz/CubeSphere.lean
Lib/AlgebraicTopology/Hurewicz/HopfDegree.lean
Lib/AlgebraicTopology/SingularHomology/LocalContributions.lean
Lib/AlgebraicTopology/SingularHomology/Naturality.lean
Lib/Topology/Homotopy/CellAttachment.lean
Lib/Topology/Homotopy/LocalCollapse.lean
Hopf/LibShims.lean
Hopf/DifferentialTopology.lean
Lib/AlgebraicTopology/FundamentalGroup/VanKampen.lean
Hopf/SingularHomology.lean
Lib/Algebra/Module/IntegerPresentation.lean
Hopf/SphereTopology.lean
Hopf/Hurewicz.lean
Lib/LinearAlgebra/SquareZero.lean
Hopf/LCP/CuspFilling.lean"
echo "$FILES" | while read f; do
  [ -z "$f" ] && continue
  base=$(basename "$f" .lean)
  o=".lake/build/lib/lean/${f%.lean}.olean"
  i=".lake/build/lib/lean/${f%.lean}.ilean"
  c=".lake/build/ir/${f%.lean}.c"
  mkdir -p "$(dirname "$o")" "$(dirname "$c")"
  echo "=== BUILD $f ==="
  lean "$f" -o "$o" -i "$i" -c "$c" > "$LOGD/$base.log" 2>&1
  rc=$?
  echo "EXIT $rc $f"
  [ $rc -ne 0 ] && { echo "STOP at $f"; exit $rc; }
done
echo "ALL DONE"
