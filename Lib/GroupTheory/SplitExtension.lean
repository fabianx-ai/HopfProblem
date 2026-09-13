/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
/-!
# Split extensions of groups

  Split extensions of groups: a short exact sequence 1 -> N -> E -> H -> 1 that
  splits is equivalent to a semidirect product `N semidirect[phi] H`, via the
  map induced by a section `s : H ->* E` conjugating `N` (Weibel, An
  Introduction to Homological Algebra, Exercise 6.1; Robinson, A Course in the
  Theory of Groups, 10.1).
-/



set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-! ### The semidirect product of a split extension -/

/-- The map `N ⋊[φ] H → E` induced by compatible inclusion and section. -/
def SplitGroupExtension.hom {N E H : Type*} [Group N] [Group E] [Group H] (i : N →* E)
    (s : H →* E) (φ : H →* MulAut N) (hconj : ∀ h n, i (φ h n) = s h * i n * (s h)⁻¹) :
    N ⋊[φ] H →* E :=
  SemidirectProduct.lift i s
    (fun h => by
      ext n
      exact hconj h n)

/-- The semidirect homomorphism computes `i n · s h`. -/
@[simp]
theorem SplitGroupExtension.hom_apply {N E H : Type*} [Group N] [Group E] [Group H] (i : N →* E)
    (s : H →* E) (φ : H →* MulAut N) (hconj : ∀ h n, i (φ h n) = s h * i n * (s h)⁻¹)
    (x : N ⋊[φ] H) : hom i s φ hconj x = i x.left * s x.right :=
  rfl

/-- The inclusion lands in the projection kernel. -/
theorem SplitGroupExtension.projection_inclusion {N E H : Type*} [Group N] [Group E] [Group H]
    (i : N →* E) (p : E →* H) (hex : i.range = p.ker) (n : N) : p (i n) = 1 := by
  apply MonoidHom.mem_ker.mp
  rw [← hex]
  exact ⟨n, rfl⟩

/-- The projection splits the section. -/
theorem SplitGroupExtension.projection_section {E H : Type*} [Group E] [Group H] (p : E →* H)
    (s : H →* E) (hs : p.comp s = MonoidHom.id H) (h : H) : p (s h) = h :=
  DFunLike.congr_fun hs h

/-- The projection of the semidirect map is the `H` component. -/
theorem SplitGroupExtension.projection_hom {N E H : Type*} [Group N] [Group E] [Group H]
    (i : N →* E) (p : E →* H) (s : H →* E) (φ : H →* MulAut N) (hs : p.comp s = MonoidHom.id H)
    (hex : i.range = p.ker) (hconj : ∀ h n, i (φ h n) = s h * i n * (s h)⁻¹) (x : N ⋊[φ] H) :
    p (hom i s φ hconj x) = x.right := by
  rw [hom_apply, map_mul, projection_inclusion i p hex, projection_section p s hs, one_mul]

/-- The semidirect map is injective for an exact split extension. -/
theorem SplitGroupExtension.hom_injective {N E H : Type*} [Group N] [Group E] [Group H]
    (i : N →* E) (p : E →* H) (s : H →* E) (φ : H →* MulAut N) (hi : Function.Injective i)
    (hs : p.comp s = MonoidHom.id H) (hex : i.range = p.ker)
    (hconj : ∀ h n, i (φ h n) = s h * i n * (s h)⁻¹) : Function.Injective (hom i s φ hconj) := by
  intro x y hxy
  have hr : x.right = y.right := by
    simpa only [projection_hom i p s φ hs hex hconj] using congrArg p hxy
  have hl : i x.left = i y.left := by
    rw [hom_apply, hom_apply, hr] at hxy
    exact mul_right_cancel hxy
  exact SemidirectProduct.ext (hi hl) hr

/-- The semidirect map is surjective for an exact split extension. -/
theorem SplitGroupExtension.hom_surjective {N E H : Type*} [Group N] [Group E] [Group H]
    (i : N →* E) (p : E →* H) (s : H →* E) (φ : H →* MulAut N) (hs : p.comp s = MonoidHom.id H)
    (hex : i.range = p.ker) (hconj : ∀ h n, i (φ h n) = s h * i n * (s h)⁻¹) :
    Function.Surjective (hom i s φ hconj) := by
  intro e
  have he : e * (s (p e))⁻¹ ∈ i.range := by
    rw [hex, MonoidHom.mem_ker, map_mul, map_inv, projection_section p s hs]
    exact mul_inv_cancel (p e)
  obtain ⟨n, hn⟩ := he
  refine ⟨⟨n, p e⟩, ?_⟩
  change i n * s (p e) = e
  rw [hn, inv_mul_cancel_right]

/-- The semidirect map is bijective. -/
theorem SplitGroupExtension.hom_bijective {N E H : Type*} [Group N] [Group E] [Group H]
    (i : N →* E) (p : E →* H) (s : H →* E) (φ : H →* MulAut N) (hi : Function.Injective i)
    (hs : p.comp s = MonoidHom.id H) (hex : i.range = p.ker)
    (hconj : ∀ h n, i (φ h n) = s h * i n * (s h)⁻¹) : Function.Bijective (hom i s φ hconj) :=
  ⟨hom_injective i p s φ hi hs hex hconj, hom_surjective i p s φ hs hex hconj⟩

/-- A split extension is the semidirect product. -/
def SplitGroupExtension.mulEquiv {N E H : Type*} [Group N] [Group E] [Group H] (i : N →* E)
    (p : E →* H) (s : H →* E) (φ : H →* MulAut N) (hi : Function.Injective i)
    (hs : p.comp s = MonoidHom.id H) (hex : i.range = p.ker)
    (hconj : ∀ h n, i (φ h n) = s h * i n * (s h)⁻¹) : N ⋊[φ] H ≃* E :=
  MulEquiv.ofBijective (hom i s φ hconj) (hom_bijective i p s φ hi hs hex hconj)

/-- The equivalence sends `inl n` to `i n`. -/
@[simp]
theorem SplitGroupExtension.mulEquiv_inl {N E H : Type*} [Group N] [Group E] [Group H]
    (i : N →* E) (p : E →* H) (s : H →* E) (φ : H →* MulAut N) (hi : Function.Injective i)
    (hs : p.comp s = MonoidHom.id H) (hex : i.range = p.ker)
    (hconj : ∀ h n, i (φ h n) = s h * i n * (s h)⁻¹) (n : N) :
    mulEquiv i p s φ hi hs hex hconj (SemidirectProduct.inl n) = i n := by
  change hom i s φ hconj (SemidirectProduct.inl n) = _
  simp

/-- The equivalence sends `inr h` to `s h`. -/
@[simp]
theorem SplitGroupExtension.mulEquiv_inr {N E H : Type*} [Group N] [Group E] [Group H]
    (i : N →* E) (p : E →* H) (s : H →* E) (φ : H →* MulAut N) (hi : Function.Injective i)
    (hs : p.comp s = MonoidHom.id H) (hex : i.range = p.ker)
    (hconj : ∀ h n, i (φ h n) = s h * i n * (s h)⁻¹) (h : H) :
    mulEquiv i p s φ hi hs hex hconj (SemidirectProduct.inr h) = s h := by
  change hom i s φ hconj (SemidirectProduct.inr h) = _
  simp

/-- The inverse sends `i n` to `inl n`. -/
@[simp]
theorem SplitGroupExtension.mulEquiv_symm_inclusion {N E H : Type*} [Group N] [Group E] [Group H]
    (i : N →* E) (p : E →* H) (s : H →* E) (φ : H →* MulAut N) (hi : Function.Injective i)
    (hs : p.comp s = MonoidHom.id H) (hex : i.range = p.ker)
    (hconj : ∀ h n, i (φ h n) = s h * i n * (s h)⁻¹) (n : N) :
    (mulEquiv i p s φ hi hs hex hconj).symm (i n) = SemidirectProduct.inl n := by
  apply (mulEquiv i p s φ hi hs hex hconj).injective
  rw [MulEquiv.apply_symm_apply, mulEquiv_inl]

/-- The inverse sends `s h` to `inr h`. -/
@[simp]
theorem SplitGroupExtension.mulEquiv_symm_section {N E H : Type*} [Group N] [Group E] [Group H]
    (i : N →* E) (p : E →* H) (s : H →* E) (φ : H →* MulAut N) (hi : Function.Injective i)
    (hs : p.comp s = MonoidHom.id H) (hex : i.range = p.ker)
    (hconj : ∀ h n, i (φ h n) = s h * i n * (s h)⁻¹) (h : H) :
    (mulEquiv i p s φ hi hs hex hconj).symm (s h) = SemidirectProduct.inr h := by
  apply (mulEquiv i p s φ hi hs hex hconj).injective
  rw [MulEquiv.apply_symm_apply, mulEquiv_inr]
end Mathoverflow1973
