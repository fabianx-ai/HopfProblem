/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Lib.Algebra.Group.Filtration
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Unit-transgression bookkeeping

This proof-owned adapter records the low-degree filtration data used in Lemma 6.11. The collapse of
its nested additive subgroups is delegated to the reusable filtration API. No spectral-sequence or
analytic existence assertion is introduced here.
-/

@[expose] public section

namespace S6.UnitTransgression

noncomputable section

/-- The normalized integral transgression, multiplication by `p`. -/
abbrev transgressionMap (p : ℤ) : ℤ →ₗ[ℤ] ℤ := LinearMap.lsmul ℤ ℤ p

/-- The kernel piece of a normalized transgression. -/
abbrev TransgressionKernel (p : ℤ) := LinearMap.ker (transgressionMap p)

/-- The cokernel piece of a normalized transgression. -/
abbrev TransgressionCokernel (p : ℤ) := ℤ ⧸ AddSubgroup.zmultiples p

/-- The normalized transgression really sends `z` to `p * z`. -/
@[simp]
theorem transgressionMap_apply (p z : ℤ) : transgressionMap p z = p * z := rfl

/-- A nonzero normalized transgression has zero kernel. -/
theorem transgressionKernel_subsingleton {p : ℤ} (hp : p ≠ 0) :
    Subsingleton (TransgressionKernel p) := by
  change Subsingleton ↥(LinearMap.ker (LinearMap.lsmul ℤ ℤ p))
  rw [LinearMap.ker_lsmul hp]
  infer_instance

/-- The cokernel of multiplication by `p` is the cyclic group `ZMod |p|`. -/
def transgressionCokernelEquivZMod (p : ℤ) :
    TransgressionCokernel p ≃+ ZMod p.natAbs :=
  Int.quotientZMultiplesEquivZMod p

set_option linter.checkUnivs false in
/--
The low-degree abutment filtration after the spectral-sequence page calculation has been performed.
The three occurrences of `TransgressionKernel`/`TransgressionCokernel` use the same normalized map,
encoding the compatible-generator hypothesis that all three differentials multiply by `p`.
-/
structure LowDegreeFiltration (p : ℤ) where
  H1 : Type*
  H2 : Type*
  H3 : Type*
  [h1AddCommGroup : AddCommGroup H1]
  [h2AddCommGroup : AddCommGroup H2]
  [h3AddCommGroup : AddCommGroup H3]
  h1Graded : H1 ≃+ TransgressionKernel p
  h2F2 : AddSubgroup H2
  h2F1 : AddSubgroup H2
  h2F2_le_h2F1 : h2F2 ≤ h2F1
  h2Survivor : h2F2 ≃+ TransgressionCokernel p
  h2MiddleVanishes : Subsingleton (h2F1 ⧸ h2F2.addSubgroupOf h2F1)
  h2TopVanishes : Subsingleton (H2 ⧸ h2F1)
  h3F2 : AddSubgroup H3
  h3F1 : AddSubgroup H3
  h3F2_le_h3F1 : h3F2 ≤ h3F1
  h3Survivor : h3F2 ≃+ TransgressionCokernel p
  h3MiddleVanishes : Subsingleton (h3F1 ⧸ h3F2.addSubgroupOf h3F1)
  h3TopVanishes : Subsingleton (H3 ⧸ h3F1)

attribute [instance] LowDegreeFiltration.h1AddCommGroup
  LowDegreeFiltration.h2AddCommGroup LowDegreeFiltration.h3AddCommGroup

/-- The sole surviving filtration subgroup in degree two is the whole abutment group. -/
theorem h2F2_eq_top {p : ℤ} (D : LowDegreeFiltration p) : D.h2F2 = ⊤ :=
  AddSubgroup.eq_top_of_le_of_quotient_subsingleton D.h2F2 D.h2F1 D.h2F2_le_h2F1
    D.h2MiddleVanishes D.h2TopVanishes

/-- The sole surviving filtration subgroup in degree three is the whole abutment group. -/
theorem h3F2_eq_top {p : ℤ} (D : LowDegreeFiltration p) : D.h3F2 = ⊤ :=
  AddSubgroup.eq_top_of_le_of_quotient_subsingleton D.h3F2 D.h3F1 D.h3F2_le_h3F1
    D.h3MiddleVanishes D.h3TopVanishes

/-- The degree-one abutment vanishes when `p` is nonzero. -/
theorem h1_subsingleton {p : ℤ} (D : LowDegreeFiltration p) (hp : p ≠ 0) :
    Subsingleton D.H1 := by
  let _ := transgressionKernel_subsingleton hp
  exact ⟨fun x y => D.h1Graded.injective (Subsingleton.elim _ _)⟩

/-- The degree-two abutment is the cokernel `ZMod |p|`. -/
def h2EquivZMod {p : ℤ} (D : LowDegreeFiltration p) : D.H2 ≃+ ZMod p.natAbs := by
  let e := D.h2Survivor
  rw [h2F2_eq_top D] at e
  exact AddSubgroup.topEquiv.symm.trans (e.trans (transgressionCokernelEquivZMod p))

/-- The degree-three abutment is the cokernel `ZMod |p|`. -/
def h3EquivZMod {p : ℤ} (D : LowDegreeFiltration p) : D.H3 ≃+ ZMod p.natAbs := by
  let e := D.h3Survivor
  rw [h3F2_eq_top D] at e
  exact AddSubgroup.topEquiv.symm.trans (e.trans (transgressionCokernelEquivZMod p))

/-- Unit defect kills the degree-two abutment. -/
theorem h2_subsingleton_of_isUnit {p : ℤ} (D : LowDegreeFiltration p) (hp : IsUnit p) :
    Subsingleton D.H2 := by
  have _ : Subsingleton (ZMod p.natAbs) :=
    ZMod.subsingleton_iff.mpr (Int.natAbs_of_isUnit hp)
  exact ⟨fun x y => (h2EquivZMod D).injective (Subsingleton.elim _ _)⟩

/-- Unit defect kills the degree-three abutment. -/
theorem h3_subsingleton_of_isUnit {p : ℤ} (D : LowDegreeFiltration p) (hp : IsUnit p) :
    Subsingleton D.H3 := by
  have _ : Subsingleton (ZMod p.natAbs) :=
    ZMod.subsingleton_iff.mpr (Int.natAbs_of_isUnit hp)
  exact ⟨fun x y => (h3EquivZMod D).injective (Subsingleton.elim _ _)⟩

/-- If the common transgression integer is a unit, all three low-degree groups vanish. -/
theorem all_subsingleton_of_isUnit {p : ℤ} (D : LowDegreeFiltration p) (hp : IsUnit p) :
    Subsingleton D.H1 ∧ Subsingleton D.H2 ∧ Subsingleton D.H3 :=
  ⟨h1_subsingleton D hp.ne_zero, h2_subsingleton_of_isUnit D hp,
    h3_subsingleton_of_isUnit D hp⟩

end

end S6.UnitTransgression
