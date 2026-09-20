/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The two-step Ext transgression of a cochain complex

This file constructs the composite of the two genuine connecting maps associated to

`0 → ZⁿK → Kⁿ → Bⁿ⁺¹K → 0`

and

`0 → Bⁿ⁺¹K → Zⁿ⁺¹K → Hⁿ⁺¹K → 0`.

It is pure homological algebra.  In particular, it does not construct a spectral sequence or
identify the resulting transgression with a differential of one.

## References

* [C. A. Weibel, *An introduction to homological algebra*][weibel94], §1.3 and §2.4
  (the two canonical short exact sequences of a complex and the connecting maps they give).
* [H. Cartan, S. Eilenberg, *Homological algebra*][cartanEilenberg56], Chapter V.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CategoryTheory.Abelian.ExtTransgression

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- An exact sequence `0 → F → X₁ → X₂ → H → 0`, represented by its middle
short complex. -/
structure TwoStepResolution where
  F : C
  complex : ShortComplex C
  ι : F ⟶ complex.X₁
  zero : ι ≫ complex.f = 0
  initial_exact : (ShortComplex.mk ι complex.f zero).Exact
  exact : complex.Exact
  mono_ι : Mono ι
  epi_g : Epi complex.g

namespace TwoStepResolution

variable (R : TwoStepResolution (C := C))

attribute [instance] mono_ι epi_g

/-- The intermediate boundary object: the kernel of the last arrow. -/
abbrev boundary : C := kernel R.complex.g

/-- The first middle arrow, with codomain restricted to the boundary object. -/
def toBoundary : R.complex.X₁ ⟶ R.boundary :=
  kernel.lift R.complex.g R.complex.f R.complex.zero

/-- Composing `toBoundary` with the kernel inclusion recovers the first middle arrow. -/
@[simp] theorem toBoundary_ι :
    R.toBoundary ≫ kernel.ι R.complex.g = R.complex.f :=
  kernel.lift_ι _ _ _

/-- The augmentation followed by `toBoundary` vanishes. -/
theorem ι_toBoundary : R.ι ≫ R.toBoundary = 0 := by
  rw [← cancel_mono (kernel.ι R.complex.g), Category.assoc, toBoundary_ι,
    R.zero, zero_comp]

/-- The first short exact sequence of a two-step resolution. -/
abbrev first : ShortComplex C :=
  ShortComplex.mk R.ι R.toBoundary R.ι_toBoundary

/-- The second short exact sequence of a two-step resolution. -/
abbrev second : ShortComplex C :=
  ShortComplex.mk (kernel.ι R.complex.g) R.complex.g (kernel.condition R.complex.g)

/-- The sequence `0 ⟶ F ⟶ X₁ ⟶ ker g ⟶ 0` is short exact. -/
theorem first_shortExact : R.first.ShortExact where
  exact := by
    let φ : R.first ⟶ ShortComplex.mk R.ι R.complex.f R.zero :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := kernel.ι R.complex.g
        comm₁₂ := by simp [first]
        comm₂₃ := by simp [first] }
    have : Epi φ.τ₁ := inferInstanceAs (Epi (𝟙 R.F))
    have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 R.complex.X₁))
    have : Mono φ.τ₃ := inferInstanceAs (Mono (kernel.ι R.complex.g))
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr R.initial_exact
  mono_f := R.mono_ι
  epi_g := R.exact.epi_kernelLift

/-- The sequence `0 ⟶ ker g ⟶ X₂ ⟶ X₃ ⟶ 0` is short exact. -/
theorem second_shortExact : R.second.ShortExact where
  exact := R.second.exact_of_f_is_kernel (kernelIsKernel R.complex.g)
  mono_f := by dsimp [second]; infer_instance
  epi_g := R.epi_g

variable [HasExt.{w} C]

/-- The composite of the two covariant Ext connecting maps of a two-step resolution. -/
def connectingTwo (P : C) : Ext.{w} P R.complex.X₃ 0 →+ Ext.{w} P R.F 2 :=
  (R.first_shortExact.extClass.postcomp P rfl).comp
    (R.second_shortExact.extClass.postcomp P rfl)

end TwoStepResolution

section CochainComplex

variable (K : CochainComplex C ℕ) (n : ℕ)

/-- The short complex from the original differential into cycles and the homology quotient. -/
def cyclesComplex : ShortComplex C :=
  ShortComplex.mk (K.toCycles n (n + 1)) (K.homologyπ (n + 1))
    (K.toCycles_comp_homologyπ n (n + 1))

/-- The short complex `Kⁿ ⟶ Zⁿ⁺¹K ⟶ Hⁿ⁺¹K` is exact: the homology projection is the cokernel
of the map into cycles. -/
theorem cyclesComplex_exact : (cyclesComplex K n).Exact :=
  (cyclesComplex K n).exact_of_g_is_cokernel
    (K.homologyIsCokernel n (n + 1) (CochainComplex.prev_nat_succ n))

/-- The homology projection out of the cycles is an epimorphism. -/
instance cyclesComplex_epi_g : Epi (cyclesComplex K n).g :=
  inferInstanceAs (Epi (K.homologyπ (n + 1)))

/-- The composite `ZⁿK ⟶ Kⁿ ⟶ Zⁿ⁺¹K` vanishes. -/
@[simp] theorem iCycles_toCycles :
    K.iCycles n ≫ K.toCycles n (n + 1) = 0 := by
  rw [← cancel_mono (K.iCycles (n + 1)), Category.assoc, K.toCycles_i, zero_comp]
  exact K.iCycles_d n (n + 1)

/-- The short complex `ZⁿK ⟶ Kⁿ ⟶ Zⁿ⁺¹K` is exact. -/
theorem cyclesInitial_exact :
    (ShortComplex.mk (K.iCycles n) (K.toCycles n (n + 1)) (iCycles_toCycles K n)).Exact := by
  let S := ShortComplex.mk (K.iCycles n) (K.toCycles n (n + 1)) (iCycles_toCycles K n)
  let T := ShortComplex.mk (K.iCycles n) (K.d n (n + 1)) (K.iCycles_d n (n + 1))
  let φ : S ⟶ T :=
    { τ₁ := 𝟙 (K.cycles n)
      τ₂ := 𝟙 (K.X n)
      τ₃ := K.iCycles (n + 1)
      comm₁₂ := by simp [S, T]
      comm₂₃ := by simp [S, T] }
  have : Epi φ.τ₁ := inferInstanceAs (Epi (𝟙 (K.cycles n)))
  have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 (K.X n)))
  have : Mono φ.τ₃ := inferInstanceAs (Mono (K.iCycles (n + 1)))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr
    (T.exact_of_f_is_kernel
      (K.cyclesIsKernel n (n + 1) (CochainComplex.next ℕ n)))

/-- The native two-step cycles resolution
`0 → ZⁿK → Kⁿ → Zⁿ⁺¹K → Hⁿ⁺¹K → 0`. -/
def cyclesResolution : TwoStepResolution (C := C) where
  F := K.cycles n
  complex := cyclesComplex K n
  ι := K.iCycles n
  zero := iCycles_toCycles K n
  initial_exact := cyclesInitial_exact K n
  exact := cyclesComplex_exact K n
  mono_ι := inferInstanceAs (Mono (K.iCycles n))
  epi_g := cyclesComplex_epi_g K n

-- The Ext universe is pinned to the hom universe `v` here: `cochainTransgression` compares the
-- literal group `P ⟶ Hⁿ⁺¹K`, which lives in `AddCommGrpCat.{v}`, with a group of Ext classes.
variable [HasExt.{v} C]

/-- The two-step Ext transgression from morphisms into degree `n+1` cohomology to degree-two
Ext of degree `n` cycles. -/
def cochainTransgression (P : C) :
    AddCommGrpCat.of (P ⟶ K.homology (n + 1)) ⟶
      AddCommGrpCat.of (Ext.{v} P (K.cycles n) 2) :=
  (Ext.addEquiv₀ (X := P) (Y := K.homology (n + 1))).toAddCommGrpIso.inv ≫
    AddCommGrpCat.ofHom ((cyclesResolution K n).connectingTwo P)

end CochainComplex

end CategoryTheory.Abelian.ExtTransgression
