/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib

/-!
# The long exact homology sequence of a short exact sequence of chain complexes

For a short exact sequence `S` of `ℕ`-indexed chain complexes of `ℤ`-modules, the homology
maps `homologyLinearMap f n : H_n K →ₗ[ℤ] H_n L` of chain maps and the connecting homomorphism
`connectingMap hS n : H_{n+1}(S.X₃) →ₗ[ℤ] H_n(S.X₁)` form the long exact sequence
`… → H_{n+1}(X₃) → H_n(X₁) → H_n(X₂) → H_n(X₃) → …`, stated as three range-equals-kernel
identities (`exact_at_leftHomology`, `exact_at_middleHomology`, `exact_at_rightHomology`),
with surjectivity of the last map in degree `0`, naturality of the connecting map, and its value
on the class of a cycle (`connectingMap_homologyClassOfCycle`: lift the cycle to `X₂`, take the
boundary, pull back to `X₁`).  These are the `ℤ`-linear readings of Mathlib's
`CategoryTheory.ShortComplex.ShortExact.homology_exact₁/₂/₃` and `δ_apply`
(cf. Hatcher, *Algebraic Topology*, §2.1, the long exact sequence of a short exact sequence of
chain complexes).
-/

open Set Function Filter Topology

open scoped CategoryTheory

@[expose] public noncomputable section

universe u

/-! ### Homology of the short complex -/

/-- The homology map induced by a chain map. -/
abbrev SingularMayerVietoris.homologyLinearMap {K L : ChainComplex (ModuleCat.{u} ℤ) ℕ}
    (f : K ⟶ L) (n : ℕ) : K.homology n →ₗ[ℤ] L.homology n :=
  (HomologicalComplex.homologyMap f n).hom

/-- Homology maps compose. -/
theorem SingularMayerVietoris.homologyLinearMap_comp {K L M : ChainComplex (ModuleCat.{u} ℤ) ℕ}
    (f : K ⟶ L) (g : L ⟶ M) (n : ℕ) :
    homologyLinearMap (f ≫ g) n = (homologyLinearMap g n).comp (homologyLinearMap f n) :=
  congrArg ModuleCat.Hom.hom (HomologicalComplex.homologyMap_comp f g n)

/-- The homology map of a negated chain map is negated. -/
@[simp]
theorem SingularMayerVietoris.homologyLinearMap_neg {K L : ChainComplex (ModuleCat.{u} ℤ) ℕ}
    (f : K ⟶ L) (n : ℕ) : homologyLinearMap (-f) n = -homologyLinearMap f n :=
  congrArg ModuleCat.Hom.hom (HomologicalComplex.homologyMap_neg f n)

/-- The connecting homomorphism of the short complex. -/
def SingularMayerVietoris.connectingMap
    {S : CategoryTheory.ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ)} (hS : S.ShortExact)
    (n : ℕ) : S.X₃.homology (n + 1) →ₗ[ℤ] S.X₁.homology n :=
  (hS.δ (n + 1) n (by simp)).hom

/-- Exactness at the left homology term. -/
theorem SingularMayerVietoris.exact_at_leftHomology
    {S : CategoryTheory.ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ)} (hS : S.ShortExact)
    (n : ℕ) : LinearMap.range (connectingMap hS n) = LinearMap.ker (homologyLinearMap S.f n) :=
  (hS.homology_exact₁ (n + 1) n (by simp)).moduleCat_range_eq_ker

/-- Exactness at the middle homology term. -/
theorem SingularMayerVietoris.exact_at_middleHomology
    {S : CategoryTheory.ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ)} (hS : S.ShortExact)
    (n : ℕ) :
    LinearMap.range (homologyLinearMap S.f n) = LinearMap.ker (homologyLinearMap S.g n) :=
  (hS.homology_exact₂ n).moduleCat_range_eq_ker

/-- Exactness at the right homology term. -/
theorem SingularMayerVietoris.exact_at_rightHomology
    {S : CategoryTheory.ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ)} (hS : S.ShortExact)
    (n : ℕ) :
    LinearMap.range (homologyLinearMap S.g (n + 1)) = LinearMap.ker (connectingMap hS n) :=
  (hS.homology_exact₃ (n + 1) n (by simp)).moduleCat_range_eq_ker

/-- The degree-zero right map is surjective. -/
theorem SingularMayerVietoris.homologyLinearMap_second_zero_surjective
    {S : CategoryTheory.ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ)} (hS : S.ShortExact) :
    Function.Surjective (homologyLinearMap S.g 0) := by
  have := hS.epi_g
  have := HomologicalComplex.epi_homologyMap_of_epi_of_not_rel S.g 0 (by intro j; simp)
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

/-- The connecting map is natural in the short exact sequence. -/
theorem SingularMayerVietoris.connectingMap_naturality
    {S T : CategoryTheory.ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ)} (hS : S.ShortExact)
    (φ : S ⟶ T) (hT : T.ShortExact) (n : ℕ) :
    (homologyLinearMap φ.τ₁ n).comp (connectingMap hS n) =
      (connectingMap hT n).comp (homologyLinearMap φ.τ₃ (n + 1)) :=
  congrArg ModuleCat.Hom.hom
    (HomologicalComplex.HomologySequence.δ_naturality φ hS hT (n + 1) n (by simp))

/-- The homology class of a cycle element. -/
def SingularMayerVietoris.homologyClassOfCycle (K : ChainComplex (ModuleCat.{u} ℤ) ℕ) {i : ℕ}
    (z : K.X i) (j : ℕ) (hj : (ComplexShape.down ℕ).next i = j) (hz : (K.d i j).hom z = 0) :
    K.homology i :=
  (K.homologyπ i).hom (K.cyclesMk z j hj hz)

/-- The chosen lift of a connecting preimage is a cycle. -/
theorem SingularMayerVietoris.connectingMap_lift_is_cycle
    {S : CategoryTheory.ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ)} (hS : S.ShortExact)
    (n : ℕ) (z₂ : S.X₂.X (n + 1)) (z₁ : S.X₁.X n)
    (hz₁ : (S.f.f n).hom z₁ = (S.X₂.d (n + 1) n).hom z₂) (k : ℕ) : (S.X₁.d n k).hom z₁ = 0 :=
  hS.d_eq_zero_of_f_eq_d_apply (n + 1) n z₂ z₁ hz₁ k

/-- The connecting map computes on cycle classes. -/
theorem SingularMayerVietoris.connectingMap_homologyClassOfCycle
    {S : CategoryTheory.ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ)} (hS : S.ShortExact)
    (n : ℕ) (z₃ : S.X₃.X (n + 1)) (hz₃ : (S.X₃.d (n + 1) n).hom z₃ = 0) (z₂ : S.X₂.X (n + 1))
    (hz₂ : (S.g.f (n + 1)).hom z₂ = z₃) (z₁ : S.X₁.X n)
    (hz₁ : (S.f.f n).hom z₁ = (S.X₂.d (n + 1) n).hom z₂) :
    connectingMap hS n
        (homologyClassOfCycle S.X₃ z₃ n ((ComplexShape.down ℕ).next_eq' (by simp)) hz₃) =
      homologyClassOfCycle S.X₁ z₁ ((ComplexShape.down ℕ).next n) rfl
        (connectingMap_lift_is_cycle hS n z₂ z₁ hz₁ _) :=
  hS.δ_apply (n + 1) n (by simp) z₃ hz₃ z₂ hz₂ z₁ hz₁ _ rfl
