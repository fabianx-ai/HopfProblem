/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Hopf.Proof.Topology.Sheaves.Cohomology.SphereTwo

/-!
# Axiom probes for declarations outside the final theorem's closure

Compile this file directly; nothing imports it, because `#print axioms` is an evidence
command rather than library content.

`Solution.lean` prints the axioms of `Mathoverflow1973.mathoverflow_1973`, which covers every
declaration in the dependency closure of that theorem, and `Lib/AxiomAudit.lean` probes the
reusable library.  Neither covers declarations that live under `Hopf/Proof` and are *not* in
the dependency closure of the final theorem; those are probed here.

Currently that is the four two-sphere vanishing theorems of
`Hopf/Proof/Topology/Sheaves/Cohomology/SphereTwo.lean`, whose manuscript consumers live on a
different branch: `Hopf/Proof/Final.lean` imports the module, but no declaration reachable
from `Mathoverflow1973.mathoverflow_1973` mentions them, so the `Solution.lean` probe says
nothing about them.
-/

/-! ## `Hopf.Proof.Topology.Sheaves.Cohomology.SphereTwo` -/

#check @TopCat.Sheaf.derivedGlobalSections_isZero_of_homeomorph_sphereTwo
#print axioms TopCat.Sheaf.derivedGlobalSections_isZero_of_homeomorph_sphereTwo
#check @TopCat.Sheaf.hasProjectiveDimensionLT_three_of_homeomorph_sphereTwo
#print axioms TopCat.Sheaf.hasProjectiveDimensionLT_three_of_homeomorph_sphereTwo
#check @TopCat.Sheaf.higherDirectImage_derivedGlobalSections_isZero_of_homeomorph_sphereTwo
#print axioms TopCat.Sheaf.higherDirectImage_derivedGlobalSections_isZero_of_homeomorph_sphereTwo
#check @TopCat.Sheaf.higherDirectImage_one_derivedGlobalSections_three_four_isZero_of_homeomorph_sphereTwo
#print axioms TopCat.Sheaf.higherDirectImage_one_derivedGlobalSections_three_four_isZero_of_homeomorph_sphereTwo
