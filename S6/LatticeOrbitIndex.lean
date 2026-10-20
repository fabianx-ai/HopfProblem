import Lib.LinearAlgebra.FreeModule.Finite.CardQuotient
import S6Shortcuts

/-!
# Concrete lattice-orbit certificate

This proof-owned adapter supplies the lattice/orbit interpretation and specializes the reusable
`Matrix` cokernel-cardinality theorem to the certified matrix `B0`.

The final specialization uses only the finite integral certificate `B0`; it makes no assertion about
the analytic package or about a complex structure on the six-sphere.
-/

namespace S6.LatticeOrbitIndex

section ConcreteCertificate

open S6Shortcuts

/-- The integral linear map whose range is the column lattice of `B`. -/
abbrev latticeMap {r : ℕ} (B : Matrix (Fin r) (Fin r) ℤ) :
    (Fin r → ℤ) →ₗ[ℤ] (Fin r → ℤ) := Matrix.toLin' B

/-- The proof-specific orbit set, identified with the quotient by the column lattice. -/
abbrev LatticeOrbits {r : ℕ} (B : Matrix (Fin r) (Fin r) ℤ) :=
  (Fin r → ℤ) ⧸ LinearMap.range (latticeMap B)

/-- The certified local matrix is unimodular. -/
theorem B0_det_natAbs : B0.det.natAbs = 1 := by
  norm_num [B0, Matrix.det_fin_two]

/-- The local orbit quotient for `B0` has exactly one element. -/
theorem natCard_B0_latticeOrbits : Nat.card (LatticeOrbits B0) = 1 := by
  rw [← Matrix.natAbs_det_eq_natCard_quotient_range_toLin' B0
    (by norm_num [B0, Matrix.det_fin_two])]
  exact B0_det_natAbs

/-- Equivalently, every integral lattice point lies in the same `B0` translation orbit. -/
theorem B0_latticeOrbits_subsingleton : Subsingleton (LatticeOrbits B0) :=
  (Nat.card_eq_one_iff_unique.mp natCard_B0_latticeOrbits).1

end ConcreteCertificate

end S6.LatticeOrbitIndex
