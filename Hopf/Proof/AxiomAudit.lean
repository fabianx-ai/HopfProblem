/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Hopf.Proof.Analysis.Complex.RiemannMapping.SectorRoots

/-!
# Axiom probes for declarations outside the final theorem's closure

Compile this file directly; nothing imports it, because `#print axioms` is an evidence
command rather than library content.

`Solution.lean` prints the axioms of `Mathoverflow1973.mathoverflow_1973`, which covers every
declaration in the dependency closure of that theorem, and `Lib/AxiomAudit.lean` probes the
reusable library.  Neither covers declarations that live under `Hopf/Proof` and are *not* in
the dependency closure of the final theorem; those are probed here.

Currently that is the wedge reversal of the rotated fourth root in
`Hopf/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean`,
`RiemannBoundary.rotatedPrincipalRootFour_reverse_of_wedge`, which no declaration in the
dependency closure of the final theorem uses.  The probes of the center construction's
declarations under `Center/Proof` are in `Center/Proof/AxiomAudit.lean`.

The `Solution.lean` probe therefore says nothing about it.
-/

/-! ## `Hopf.Proof.Analysis.Complex.RiemannMapping.SectorRoots` -/

#check RiemannBoundary.rotatedPrincipalRootFour_reverse_of_wedge
#print axioms RiemannBoundary.rotatedPrincipalRootFour_reverse_of_wedge
