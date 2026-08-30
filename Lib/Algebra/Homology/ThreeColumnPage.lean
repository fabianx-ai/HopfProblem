/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Lib.Algebra.Group.Filtration
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Normalized three-column page bookkeeping

This file contains algebraic data and consequences for three parallel maps between rank-one
modules.  It does not construct a spectral sequence, identify a page with cohomology, or supply a
convergence theorem.  A value of `ThreeColumnPage.FilteredAbutment` is independent input asserting
the relevant filtered-object identifications.
-/

@[expose] public section

namespace LinearMap

universe u v w

variable {R : Type u} [CommRing R]
variable {M : Type v} {N : Type w}
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Chosen rank-one coordinates on the source and target of a linear map. -/
structure RankOneNormalization (f : M →ₗ[R] N) where
  source : M ≃ₗ[R] R
  target : N ≃ₗ[R] R

namespace RankOneNormalization

variable {f : M →ₗ[R] N} (C : f.RankOneNormalization)

/-- The map `f` written in the chosen rank-one coordinates. -/
def normalized : R →ₗ[R] R :=
  C.target.toLinearMap.comp (f.comp C.source.symm.toLinearMap)

/-- The coefficient of `f` in the chosen rank-one coordinates. -/
def coefficient : R := C.normalized 1

/-- Every endomorphism of the rank-one module `R` is multiplication by its value at `1`. -/
theorem normalized_eq_lsmul : C.normalized = LinearMap.lsmul R R C.coefficient := by
  apply LinearMap.ext
  intro r
  change C.target (f (C.source.symm r)) = C.coefficient * r
  have hr : C.source.symm r = r • C.source.symm 1 := by
    rw [← C.source.symm.map_smul]
    simp
  rw [hr, f.map_smul, C.target.map_smul]
  simp [coefficient, normalized, mul_comm]

/-- A map with chosen rank-one coordinates is zero exactly when its normalized coefficient is
zero. -/
theorem map_eq_zero_iff : f = 0 ↔ C.coefficient = 0 := by
  constructor
  · rintro rfl
    simp [coefficient, normalized]
  · intro hc
    apply LinearMap.ext
    intro x
    apply C.target.injective
    have hx := LinearMap.congr_fun C.normalized_eq_lsmul (C.source x)
    simpa [normalized, hc] using hx

/-- A map with chosen rank-one coordinates is nonzero exactly when its normalized coefficient is
nonzero. -/
theorem map_ne_zero_iff : f ≠ 0 ↔ C.coefficient ≠ 0 :=
  not_congr C.map_eq_zero_iff

/-- Over a domain, a map with chosen rank-one coordinates is injective exactly when its normalized
coefficient is nonzero. -/
theorem injective_iff_coefficient_ne_zero [IsDomain R] :
    Function.Injective f ↔ C.coefficient ≠ 0 := by
  constructor
  · intro hf hc
    have hn : Function.Injective C.normalized :=
      C.target.injective.comp (hf.comp C.source.symm.injective)
    exact (one_ne_zero : (1 : R) ≠ 0) (hn (by
      rw [C.normalized_eq_lsmul, hc]
      simp))
  · intro hc x y hxy
    have hn : Function.Injective C.normalized := by
      rw [C.normalized_eq_lsmul]
      exact LinearMap.lsmul_injective hc
    apply C.source.injective
    apply hn
    show C.normalized (C.source x) = C.normalized (C.source y)
    simp [normalized, hxy]

include C

/-- Over a domain, a map between modules with chosen rank-one coordinates is injective exactly
when it is nonzero. -/
theorem injective_iff_ne_zero [IsDomain R] : Function.Injective f ↔ f ≠ 0 :=
  (injective_iff_coefficient_ne_zero C).trans (map_ne_zero_iff C).symm

/-- Chosen source coordinates identify the kernel of `f` with the kernel of its normalized map. -/
def kernelEquivNormalized : LinearMap.ker f ≃ₗ[R] LinearMap.ker C.normalized where
  toFun x := ⟨C.source x, by simp [normalized]⟩
  invFun x := ⟨C.source.symm x, by
    apply C.target.injective
    simpa [normalized] using x.property⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- The kernel of `f` is the kernel of multiplication by its normalized coefficient. -/
def kernelEquiv :
    LinearMap.ker f ≃ₗ[R] LinearMap.ker (LinearMap.lsmul R R C.coefficient) :=
  C.kernelEquivNormalized.trans
    (LinearEquiv.ofEq _ _ (congrArg LinearMap.ker C.normalized_eq_lsmul))

/-- Chosen target coordinates identify the cokernel of `f` with that of its normalized map. -/
def cokernelEquivNormalized :
    (N ⧸ LinearMap.range f) ≃ₗ[R] (R ⧸ LinearMap.range C.normalized) := by
  apply Submodule.Quotient.equiv _ _ C.target
  ext y
  constructor
  · rintro ⟨x, ⟨m, rfl⟩, rfl⟩
    exact ⟨C.source m, by simp [normalized]⟩
  · rintro ⟨r, rfl⟩
    exact ⟨f (C.source.symm r), ⟨C.source.symm r, rfl⟩, by simp [normalized]⟩

/-- The cokernel of `f` is the cokernel of multiplication by its normalized coefficient. -/
def cokernelEquiv :
    (N ⧸ LinearMap.range f) ≃ₗ[R]
      (R ⧸ LinearMap.range (LinearMap.lsmul R R C.coefficient)) :=
  C.cokernelEquivNormalized.trans
    (Submodule.quotEquivOfEq _ _ (congrArg LinearMap.range C.normalized_eq_lsmul))

/-- A map between normalized rank-one modules is bijective exactly when its coefficient is a unit. -/
theorem bijective_iff_isUnit : Function.Bijective f ↔ IsUnit C.coefficient := by
  rw [IsUnit.isUnit_iff_mulLeft_bijective]
  change Function.Bijective f ↔ Function.Bijective (LinearMap.lsmul R R C.coefficient)
  rw [← C.normalized_eq_lsmul]
  constructor
  · intro hf
    exact C.target.bijective.comp (hf.comp C.source.symm.bijective)
  · intro hnormalized
    have h := C.target.symm.bijective.comp (hnormalized.comp C.source.bijective)
    simpa [normalized, Function.comp_def] using h

end RankOneNormalization

end LinearMap

namespace ThreeColumnPage

universe u v w

variable (R : Type u) [CommRing R]

/--
The lower part of an abstract three-column page.

Only entries used by the three maps `(0,b+1) → (2,b)` and the two relevant middle-column
entries are recorded by structure fields.  The name `Data` denotes page-shaped algebra, not a
spectral-sequence realization.
-/
structure Data where
  E : Fin 3 → Fin 4 → Type v
  [addCommGroup : ∀ a b, AddCommGroup (E a b)]
  [module : ∀ a b, Module R (E a b)]
  differential : ∀ i : Fin 3, E 0 i.succ →ₗ[R] E 2 i.castSucc
  source : ∀ i : Fin 3, E 0 i.succ ≃ₗ[R] R
  target : ∀ i : Fin 3, E 2 i.castSucc ≃ₗ[R] R
  middle : ∀ j : Fin 2, Subsingleton (E 1 j.succ.castSucc)

attribute [instance] Data.addCommGroup Data.module

namespace Data

variable {R} (P : Data R)

/--
The standard normalized three-column page attached to three coefficients.

Its two outer columns are copies of `R`, its middle column is zero, and its three lower
differentials are scalar multiplication by the supplied coefficients.  This is a page-shaped
algebraic object, not a spectral-sequence realization.
-/
def ofCoefficients (c : Fin 3 → R) : Data R where
  E := fun a _ ↦ Fin.cases R (Fin.cases (Fin 0 → R) (fun _ ↦ R)) a
  addCommGroup a _ :=
    Fin.cases (inferInstanceAs (AddCommGroup R))
      (fun a ↦ Fin.cases (inferInstanceAs (AddCommGroup (Fin 0 → R)))
        (fun _ ↦ inferInstanceAs (AddCommGroup R)) a) a
  module a _ :=
    Fin.cases (inferInstanceAs (Module R R))
      (fun a ↦ Fin.cases (inferInstanceAs (Module R (Fin 0 → R)))
        (fun _ ↦ inferInstanceAs (Module R R)) a) a
  differential i := LinearMap.lsmul R R (c i)
  source _ := LinearEquiv.refl R R
  target _ := LinearEquiv.refl R R
  middle _ := inferInstanceAs (Subsingleton (Fin 0 → R))

/-- The chosen normalization of the `i`th lower differential. -/
def normalization (i : Fin 3) : (P.differential i).RankOneNormalization where
  source := P.source i
  target := P.target i

/-- The coefficient of the `i`th lower differential in the chosen coordinates. -/
def coefficient (i : Fin 3) : R := (P.normalization i).coefficient

/-- The standard page has the coefficients from which it was built. -/
@[simp]
theorem ofCoefficients_coefficient (c : Fin 3 → R) (i : Fin 3) :
    (ofCoefficients c).coefficient i = c i := by
  change c i * 1 = c i
  exact mul_one _

/-- The kernel graded piece belonging to the `i`th differential. -/
abbrev Kernel (i : Fin 3) := LinearMap.ker (P.differential i)

/-- The cokernel graded piece belonging to the `i`th differential. -/
abbrev Cokernel (i : Fin 3) := P.E 2 i.castSucc ⧸ LinearMap.range (P.differential i)

/-- The `i`th typed kernel is the kernel of multiplication by its normalized coefficient. -/
def kernelEquiv (i : Fin 3) :
    P.Kernel i ≃ₗ[R] LinearMap.ker (LinearMap.lsmul R R (P.coefficient i)) :=
  (P.normalization i).kernelEquiv

/-- The `i`th typed cokernel is the cokernel of multiplication by its normalized coefficient. -/
def cokernelEquiv (i : Fin 3) :
    P.Cokernel i ≃ₗ[R]
      (R ⧸ LinearMap.range (LinearMap.lsmul R R (P.coefficient i))) :=
  (P.normalization i).cokernelEquiv

/-- The `i`th typed differential is bijective exactly when its coefficient is a unit. -/
theorem differential_bijective_iff_isUnit (i : Fin 3) :
    Function.Bijective (P.differential i) ↔ IsUnit (P.coefficient i) :=
  (P.normalization i).bijective_iff_isUnit

/-- A lower differential between the page's normalized rank-one modules is injective exactly when
it is nonzero. -/
theorem differential_injective_iff_ne_zero [IsDomain R] (i : Fin 3) :
    Function.Injective (P.differential i) ↔ P.differential i ≠ 0 :=
  (P.normalization i).injective_iff_ne_zero

end Data

/--
An independently supplied three-step filtration with graded pieces identified with the kernels and
cokernels of a `Data` value.

Constructing this record is the convergence/abutment obligation.  No `Data` value manufactures one.
-/
structure FilteredAbutment {R : Type u} [CommRing R] (P : Data R) where
  H : Fin 3 → Type w
  [addCommGroup : ∀ n, AddCommGroup (H n)]
  degreeOne : H 0 ≃+ P.Kernel 0
  bottom : ∀ j : Fin 2, AddSubgroup (H j.succ)
  middle : ∀ j : Fin 2, AddSubgroup (H j.succ)
  bottom_le_middle : ∀ j, bottom j ≤ middle j
  bottomGraded : ∀ j, bottom j ≃+ P.Cokernel j.castSucc
  middleGraded : ∀ j,
    (middle j ⧸ (bottom j).addSubgroupOf (middle j)) ≃+ P.E 1 j.succ.castSucc
  topGraded : ∀ j, (H j.succ ⧸ middle j) ≃+ P.Kernel j.succ

attribute [instance] FilteredAbutment.addCommGroup

namespace FilteredAbutment

variable {R : Type u} [CommRing R] {P : Data R} (A : FilteredAbutment P)

private theorem injective_iff_kernel_subsingleton {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    Function.Injective f ↔ Subsingleton (LinearMap.ker f) :=
  LinearMap.ker_eq_bot.symm.trans Submodule.subsingleton_iff_eq_bot.symm

private theorem surjective_iff_cokernel_subsingleton {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    Function.Surjective f ↔ Subsingleton (N ⧸ LinearMap.range f) :=
  LinearMap.range_eq_top.symm.trans Submodule.Quotient.subsingleton_iff.symm

/--
For the supplied filtration, vanishing in total degrees one through three is equivalent to the
first two lower differentials being bijective and the third being injective.
-/
theorem all_subsingleton_iff :
    (Subsingleton (A.H 0) ∧ Subsingleton (A.H 1) ∧ Subsingleton (A.H 2)) ↔
      (Function.Bijective (P.differential 0) ∧
        Function.Bijective (P.differential 1) ∧
        Function.Injective (P.differential 2)) := by
  constructor
  · rintro ⟨hH0, hH1, hH2⟩
    have hk0 : Subsingleton (P.Kernel 0) :=
      A.degreeOne.toEquiv.subsingleton_congr.mp hH0
    have hc0 : Subsingleton (P.Cokernel 0) := by
      have hbottom : Subsingleton (A.bottom 0) :=
        @Function.Injective.subsingleton _ _ _ Subtype.val_injective hH1
      exact (A.bottomGraded 0).toEquiv.subsingleton_congr.mp hbottom
    have hk1 : Subsingleton (P.Kernel 1) := by
      have hquot : Subsingleton (A.H 1 ⧸ A.middle 0) :=
        @Function.Surjective.subsingleton _ _ _ hH1
          (QuotientAddGroup.mk'_surjective (A.middle 0))
      exact (A.topGraded 0).toEquiv.subsingleton_congr.mp hquot
    have hc1 : Subsingleton (P.Cokernel 1) := by
      have hbottom : Subsingleton (A.bottom 1) :=
        @Function.Injective.subsingleton _ _ _ Subtype.val_injective hH2
      exact (A.bottomGraded 1).toEquiv.subsingleton_congr.mp hbottom
    have hk2 : Subsingleton (P.Kernel 2) := by
      have hquot : Subsingleton (A.H 2 ⧸ A.middle 1) :=
        @Function.Surjective.subsingleton _ _ _ hH2
          (QuotientAddGroup.mk'_surjective (A.middle 1))
      exact (A.topGraded 1).toEquiv.subsingleton_congr.mp hquot
    exact
      ⟨⟨(injective_iff_kernel_subsingleton (P.differential 0)).mpr hk0,
          (surjective_iff_cokernel_subsingleton (P.differential 0)).mpr hc0⟩,
        ⟨⟨(injective_iff_kernel_subsingleton (P.differential 1)).mpr hk1,
            (surjective_iff_cokernel_subsingleton (P.differential 1)).mpr hc1⟩,
          (injective_iff_kernel_subsingleton (P.differential 2)).mpr hk2⟩⟩
  · rintro ⟨hd0, hd1, hd2⟩
    have hk0 : Subsingleton (P.Kernel 0) :=
      (injective_iff_kernel_subsingleton (P.differential 0)).mp hd0.1
    have hc0 : Subsingleton (P.Cokernel 0) :=
      (surjective_iff_cokernel_subsingleton (P.differential 0)).mp hd0.2
    have hk1 : Subsingleton (P.Kernel 1) :=
      (injective_iff_kernel_subsingleton (P.differential 1)).mp hd1.1
    have hc1 : Subsingleton (P.Cokernel 1) :=
      (surjective_iff_cokernel_subsingleton (P.differential 1)).mp hd1.2
    have hk2 : Subsingleton (P.Kernel 2) :=
      (injective_iff_kernel_subsingleton (P.differential 2)).mp hd2
    have higherSubsingleton (j : Fin 2) (hc : Subsingleton (P.Cokernel j.castSucc))
        (hk : Subsingleton (P.Kernel j.succ)) : Subsingleton (A.H j.succ) := by
      have hbottom : Subsingleton (A.bottom j) :=
        (A.bottomGraded j).toEquiv.subsingleton_congr.mpr hc
      have htop : Subsingleton (A.H j.succ ⧸ A.middle j) :=
        (A.topGraded j).toEquiv.subsingleton_congr.mpr hk
      have hmiddle : Subsingleton
          (A.middle j ⧸ (A.bottom j).addSubgroupOf (A.middle j)) :=
        (A.middleGraded j).toEquiv.subsingleton_congr.mpr (P.middle j)
      have hbottomTop : A.bottom j = ⊤ :=
        AddSubgroup.eq_top_of_le_of_quotient_subsingleton (A.bottom j) (A.middle j)
          (A.bottom_le_middle j) hmiddle htop
      rw [hbottomTop] at hbottom
      exact AddSubgroup.topEquiv.toEquiv.subsingleton_congr.mp hbottom
    exact ⟨A.degreeOne.toEquiv.subsingleton_congr.mpr hk0,
      higherSubsingleton 0 hc0 hk1, higherSubsingleton 1 hc1 hk2⟩

/--
If all three normalized coefficients are a common scalar, the supplied low-degree abutment
vanishes exactly when that scalar is a unit.
-/
theorem all_subsingleton_iff_isUnit_of_coefficients_eq (p : R)
    (hcoeff : ∀ i, P.coefficient i = p) :
    (Subsingleton (A.H 0) ∧ Subsingleton (A.H 1) ∧ Subsingleton (A.H 2)) ↔ IsUnit p := by
  rw [A.all_subsingleton_iff]
  constructor
  · intro h
    have hunit := (P.differential_bijective_iff_isUnit 0).mp h.1
    rwa [hcoeff 0] at hunit
  · intro hp
    have hunit : ∀ i, IsUnit (P.coefficient i) := fun i ↦ by simpa [hcoeff i] using hp
    exact ⟨(P.differential_bijective_iff_isUnit 0).mpr (hunit 0),
      (P.differential_bijective_iff_isUnit 1).mpr (hunit 1),
      ((P.differential_bijective_iff_isUnit 2).mpr (hunit 2)).1⟩

end FilteredAbutment

end ThreeColumnPage
