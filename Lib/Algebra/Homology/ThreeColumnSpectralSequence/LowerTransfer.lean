/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Lib.Algebra.Homology.ThreeColumnPage.LowerDifferentials
public import Lib.Algebra.Homology.ThreeColumnSpectralSequence.ThreeColumnPage

/-!
# Lower differentials of a convergent three-column spectral sequence

This file extracts the three lower-differential conditions from genuine convergence and
abutment vanishing.  The page-three objects at the left and right edges are the homology of the
actual page-two complex: their vanishing makes the outgoing `d₂` injective and the incoming `d₂`
surjective, respectively.

No middle-column vanishing is assumed.  The adapter's two middle-column fields continue to be
derived from degree-two and degree-three abutment vanishing.  When two adjacent abutment groups
vanish, the resulting bijection also transports a chosen rank-one coordinate from either edge to
the other.

## References

* [C. A. Weibel, *An introduction to homological algebra*][weibel94], §5.2 (edge maps of a
  spectral sequence supported in finitely
  many columns).

-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace ThreeColumnSpectralSequence

universe u v w

variable {R : Type u} [CommRing R]

namespace Raw

variable (P : Raw.{u, v} R)

/-- No page-two differential enters the left edge. -/
theorem left_dTo_eq_zero (q : ℕ) :
    (P.spectralSequence.page 2).dTo (0, q) = 0 := by
  apply (P.spectralSequence.page 2).dTo_eq_zero
  intro h
  rw [ComplexShape.spectralSequenceNat_rel_iff] at h
  omega

/-- No page-two differential leaves the right edge. -/
theorem right_dFrom_eq_zero (q : ℕ) :
    (P.spectralSequence.page 2).dFrom (2, q) = 0 := by
  by_cases h :
      (ComplexShape.spectralSequenceNat ⟨2, 1 - 2⟩).Rel
        (2, q) ((ComplexShape.spectralSequenceNat ⟨2, 1 - 2⟩).next (2, q))
  · have hp : 3 ≤ ((ComplexShape.spectralSequenceNat ⟨2, 1 - 2⟩).next (2, q)).1 := by
      rw [ComplexShape.spectralSequenceNat_rel_iff] at h
      omega
    exact (P.isZero_E₂_of_three_le _ _ hp).eq_of_tgt _ _
  · exact (P.spectralSequence.page 2).dFrom_eq_zero h

/-- If the page-three object on the left edge vanishes, the outgoing `d₂` is injective. -/
theorem d₂_injective_of_subsingleton_Einf (q : ℕ)
    (hEinf : Subsingleton (P.Einf 0 (q + 1))) :
    Function.Injective (P.d₂ 0 q).hom := by
  let _ : Subsingleton (P.Einf 0 (q + 1)) := hEinf
  have hpage3 : IsZero (P.Einf 0 (q + 1)) :=
    ModuleCat.isZero_of_subsingleton _
  have hhomology :
      IsZero ((P.spectralSequence.page 2).homology (0, q + 1)) :=
    IsZero.of_iso hpage3 (P.spectralSequence.iso 2 3 (0, q + 1))
  have hexact : (P.spectralSequence.page 2).ExactAt (0, q + 1) :=
    ((P.spectralSequence.page 2).exactAt_iff_isZero_homology (0, q + 1)).2 hhomology
  have : Mono ((P.spectralSequence.page 2).dFrom (0, q + 1)) :=
    hexact.mono_g (P.left_dTo_eq_zero (q + 1))
  have hrel :
      (ComplexShape.spectralSequenceNat ⟨2, 1 - 2⟩).Rel (0, q + 1) (2, q) := by
    rw [ComplexShape.spectralSequenceNat_rel_iff]
    omega
  apply (ModuleCat.mono_iff_injective (P.d₂ 0 q)).1
  change Mono ((P.spectralSequence.page 2).d (0, q + 1) (2, q))
  rw [← (P.spectralSequence.page 2).dFrom_comp_xNextIso hrel]
  infer_instance

/-- If the page-three object on the right edge vanishes, the incoming `d₂` is surjective. -/
theorem d₂_surjective_of_subsingleton_Einf (q : ℕ)
    (hEinf : Subsingleton (P.Einf 2 q)) :
    Function.Surjective (P.d₂ 0 q).hom := by
  let _ : Subsingleton (P.Einf 2 q) := hEinf
  have hpage3 : IsZero (P.Einf 2 q) :=
    ModuleCat.isZero_of_subsingleton _
  have hhomology : IsZero ((P.spectralSequence.page 2).homology (2, q)) :=
    IsZero.of_iso hpage3 (P.spectralSequence.iso 2 3 (2, q))
  have hexact : (P.spectralSequence.page 2).ExactAt (2, q) :=
    ((P.spectralSequence.page 2).exactAt_iff_isZero_homology (2, q)).2 hhomology
  have : Epi ((P.spectralSequence.page 2).dTo (2, q)) :=
    hexact.epi_f (P.right_dFrom_eq_zero q)
  have hrel :
      (ComplexShape.spectralSequenceNat ⟨2, 1 - 2⟩).Rel (0, q + 1) (2, q) := by
    rw [ComplexShape.spectralSequenceNat_rel_iff]
    omega
  apply (ModuleCat.epi_iff_surjective (P.d₂ 0 q)).1
  change Epi ((P.spectralSequence.page 2).d (0, q + 1) (2, q))
  rw [← (P.spectralSequence.page 2).xPrevIso_comp_dTo hrel]
  infer_instance

end Raw

namespace Convergence

variable {P : Raw.{u, v} R} (A : Convergence.{u, v, w} R P)

/-- Vanishing of `H^(q+1)` makes the `q`th lower `d₂` injective. -/
theorem d₂_injective_of_subsingleton (q : ℕ)
    (hH : Subsingleton (A.H (q + 1))) :
    Function.Injective (P.d₂ 0 q).hom := by
  apply P.d₂_injective_of_subsingleton_Einf q
  exact A.Einf_subsingleton 0 (q + 1) (by simpa using hH)

/-- Vanishing of `H^(q+2)` makes the `q`th lower `d₂` surjective. -/
theorem d₂_surjective_of_subsingleton (q : ℕ)
    (hH : Subsingleton (A.H (q + 2))) :
    Function.Surjective (P.d₂ 0 q).hom := by
  apply P.d₂_surjective_of_subsingleton_Einf q
  exact A.Einf_subsingleton 2 q (by simpa [Nat.add_comm] using hH)

/-- Vanishing of the two adjacent abutment groups makes the `q`th lower `d₂` bijective. -/
theorem d₂_bijective_of_subsingleton (q : ℕ)
    (hH₁ : Subsingleton (A.H (q + 1)))
    (hH₂ : Subsingleton (A.H (q + 2))) :
    Function.Bijective (P.d₂ 0 q).hom :=
  ⟨A.d₂_injective_of_subsingleton q hH₁,
    A.d₂_surjective_of_subsingleton q hH₂⟩

/-- A rank-one coordinate on the target of a bijective lower `d₂` induces one on its source. -/
noncomputable def sourceNormalizationOfTarget (q : ℕ)
    (hH₁ : Subsingleton (A.H (q + 1)))
    (hH₂ : Subsingleton (A.H (q + 2)))
    (target : P.E₂ 2 q ≃ₗ[R] R) :
    P.E₂ 0 (q + 1) ≃ₗ[R] R :=
  (LinearEquiv.ofBijective (P.d₂ 0 q).hom
    (A.d₂_bijective_of_subsingleton q hH₁ hH₂)).trans target

/-- A rank-one coordinate on the source of a bijective lower `d₂` induces one on its target. -/
noncomputable def targetNormalizationOfSource (q : ℕ)
    (hH₁ : Subsingleton (A.H (q + 1)))
    (hH₂ : Subsingleton (A.H (q + 2)))
    (source : P.E₂ 0 (q + 1) ≃ₗ[R] R) :
    P.E₂ 2 q ≃ₗ[R] R :=
  (LinearEquiv.ofBijective (P.d₂ 0 q).hom
    (A.d₂_bijective_of_subsingleton q hH₁ hH₂)).symm.trans source

/-- Assemble all six outer coordinates from coordinates on the three alternating edges, using
adjacent abutment vanishing to transport across the lower differentials. -/
noncomputable def outerNormalizationOfAlternatingCoordinates
    (hH₁ : Subsingleton (A.H 1))
    (hH₂ : Subsingleton (A.H 2))
    (hH₃ : Subsingleton (A.H 3))
    (hH₄ : Subsingleton (A.H 4))
    (target₀ : P.E₂ 2 0 ≃ₗ[R] R)
    (source₁ : P.E₂ 0 2 ≃ₗ[R] R)
    (source₂ : P.E₂ 0 3 ≃ₗ[R] R) :
    OuterNormalization R P where
  source := Fin.cases
    (A.sourceNormalizationOfTarget 0 (by simpa using hH₁) (by simpa using hH₂) target₀)
    (Fin.cases source₁ (Fin.cases source₂ (fun i => Fin.elim0 i)))
  target := Fin.cases target₀
    (Fin.cases
      (A.targetNormalizationOfSource 1 (by simpa using hH₂) (by simpa using hH₃) source₁)
      (Fin.cases
        (A.targetNormalizationOfSource 2 (by simpa using hH₃) (by simpa using hH₄) source₂)
        (fun i => Fin.elim0 i)))

/-- Abutment vanishing in degrees one through three makes the first two page-two differentials
bijective and the third nonzero. -/
theorem lowerDifferentialsBijectiveAndNeZero [Nontrivial R] (N : OuterNormalization R P)
    (hH₁ : Subsingleton (A.H 1)) (hH₂ : Subsingleton (A.H 2))
    (hH₃ : Subsingleton (A.H 3)) :
    ThreeColumnPage.LowerDifferentialsBijectiveAndNeZero (A.toThreeColumnPageData N hH₂ hH₃) := by
  rw [ThreeColumnPage.LowerDifferentialsBijectiveAndNeZero]
  simp only [toThreeColumnPageData_differential]
  refine ⟨⟨A.d₂_injective_of_subsingleton 0 (by simpa using hH₁),
      A.d₂_surjective_of_subsingleton 0 (by simpa using hH₂)⟩,
    ⟨A.d₂_injective_of_subsingleton 1 (by simpa using hH₂),
      A.d₂_surjective_of_subsingleton 1 (by simpa using hH₃)⟩, ?_⟩
  have hsource : Nontrivial (P.E₂ 0 ((2 : Fin 3).val + 1)) := by
    simpa using (N.source 2).toEquiv.nontrivial
  let _ := hsource
  apply LinearMap.ne_zero_of_injective
  simpa using A.d₂_injective_of_subsingleton 2 (by simpa using hH₃)

end Convergence

end ThreeColumnSpectralSequence
