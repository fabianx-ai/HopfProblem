/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Three-column cohomological spectral sequences

This file records the raw page and convergence data for a first-quadrant cohomological spectral
sequence whose `E₂` page is supported in columns `0`, `1`, and `2`.  In particular, the raw
structure does not assume that the middle column vanishes.

The spectral-sequence field is Mathlib's `E₂CohomologicalSpectralSequenceNat`, so its pages are
actual homological complexes and its successor pages are identified with their homology.  The
convergence field uses an explicit finite filtration by submodules; its graded pieces are genuine
successive quotients.

## References

* [C. A. Weibel, *An introduction to homological algebra*][weibel94], §5.2 (spectral sequences
  supported in finitely many columns and their degeneration).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace ThreeColumnSpectralSequence

universe u v w

variable (R : Type u) [CommRing R]

/-- A first-quadrant `E₂`-cohomological spectral sequence supported in its first three columns.

Only support of the `E₂` page is input.  Support on later pages is a consequence of the
homology isomorphisms of the spectral sequence, rather than extra page data. -/
structure Raw where
  spectralSequence : E₂CohomologicalSpectralSequenceNat (ModuleCat.{v} R)
  isZero_E₂_of_three_le : ∀ (p q : ℕ), 3 ≤ p →
    IsZero ((spectralSequence.page 2).X (p, q))

namespace Raw

variable {R} (P : Raw.{u, v} R)

/-- The object in bidegree `(p,q)` on page `r`. -/
abbrev E (r : ℤ) (hr : 2 ≤ r) (p q : ℕ) : ModuleCat.{v} R :=
  (P.spectralSequence.page r hr).X (p, q)

/-- The object in bidegree `(p,q)` on the `E₂` page. -/
abbrev E₂ (p q : ℕ) : ModuleCat.{v} R := P.E 2 (by omega) p q

/-- The actual `d₂ : E₂^(p,q+1) ⟶ E₂^(p+2,q)` differential. -/
abbrev d₂ (p q : ℕ) : P.E₂ p (q + 1) ⟶ P.E₂ (p + 2) q :=
  (P.spectralSequence.page 2).d (p, q + 1) (p + 2, q)

/-- The page used for the limiting page of a three-column sequence.

The permanence theorem proves that all page transitions from page three onward are isomorphisms
in the supported columns. -/
abbrev Einf (p q : ℕ) : ModuleCat.{v} R := P.E 3 (by omega) p q

/-- Page `n+2`, indexed by its offset from the initial page. -/
abbrev offsetPage (n : ℕ) :=
  P.spectralSequence.page ((n : ℤ) + 2) (by omega)

/-- Three-column support propagates from the `E₂` page to every later page. -/
theorem isZero_offsetPage_of_three_le (n p q : ℕ) (hp : 3 ≤ p) :
    IsZero ((P.offsetPage n).X (p, q)) := by
  induction n with
  | zero =>
      change IsZero ((P.spectralSequence.page 2).X (p, q))
      exact P.isZero_E₂_of_three_le p q hp
  | succ n ih =>
      have hhomology : IsZero ((P.offsetPage n).homology (p, q)) :=
        ((P.offsetPage n).sc (p, q)).isZero_homology_of_isZero_X₂ ih
      exact IsZero.of_iso hhomology
        (P.spectralSequence.iso ((n : ℤ) + 2) ((n + 1 : ℕ) + 2) (p, q) (by omega)).symm

/-- No differential on page `n+2` enters column one. -/
theorem middle_dTo_eq_zero (n q : ℕ) :
    (P.offsetPage n).dTo (1, q) = 0 := by
  apply (P.offsetPage n).dTo_eq_zero
  intro h
  rw [ComplexShape.spectralSequenceNat_rel_iff] at h
  omega

/-- No differential on page `n+2` leaves column one. -/
theorem middle_dFrom_eq_zero (n q : ℕ) :
    (P.offsetPage n).dFrom (1, q) = 0 := by
  by_cases h :
      (ComplexShape.spectralSequenceNat
        ⟨(n : ℤ) + 2, 1 - ((n : ℤ) + 2)⟩).Rel
          (1, q) ((ComplexShape.spectralSequenceNat
            ⟨(n : ℤ) + 2, 1 - ((n : ℤ) + 2)⟩).next (1, q))
  · have hp : 3 ≤ ((ComplexShape.spectralSequenceNat
        ⟨(n : ℤ) + 2, 1 - ((n : ℤ) + 2)⟩).next (1, q)).1 := by
      rw [ComplexShape.spectralSequenceNat_rel_iff] at h
      omega
    exact (P.isZero_offsetPage_of_three_le n _ _ hp).eq_of_tgt _ _
  · exact (P.offsetPage n).dFrom_eq_zero h

/-- The middle-column object is unchanged from page `n+2` to page `n+3`. -/
noncomputable def middlePageSuccIso (n q : ℕ) :
    (P.offsetPage n).X (1, q) ≅ (P.offsetPage (n + 1)).X (1, q) :=
  ((ShortComplex.HomologyData.ofZeros ((P.offsetPage n).sc (1, q))
      (P.middle_dTo_eq_zero n q) (P.middle_dFrom_eq_zero n q)).left.homologyIso).symm ≪≫
    P.spectralSequence.iso ((n : ℤ) + 2) ((n + 1 : ℕ) + 2) (1, q) (by omega)

/-- Column one is permanent: its `E₂` object is isomorphic to every later page. -/
noncomputable def middlePageIso (q n : ℕ) :
    P.E₂ 1 q ≅ (P.offsetPage n).X (1, q) :=
  Nat.rec (motive := fun n ↦ P.E₂ 1 q ≅ (P.offsetPage n).X (1, q))
    (Iso.refl _) (fun n e ↦ e ≪≫ P.middlePageSuccIso n q) n

/-- The column-one `E₂` object is the corresponding stable-page object. -/
noncomputable def middlePermanenceIso (q : ℕ) :
    P.E₂ 1 q ≅ P.Einf 1 q :=
  P.middlePageIso q 1

/-- From page three onward, no differential enters any of the supported columns. -/
theorem stable_dTo_eq_zero (n : ℕ) (p : Fin 3) (q : ℕ) :
    (P.offsetPage (n + 1)).dTo (p, q) = 0 := by
  apply (P.offsetPage (n + 1)).dTo_eq_zero
  intro h
  rw [ComplexShape.spectralSequenceNat_rel_iff] at h
  have hp : p.1 ≤ 2 := by omega
  omega

/-- From page three onward, no differential leaves any of the supported columns. -/
theorem stable_dFrom_eq_zero (n : ℕ) (p : Fin 3) (q : ℕ) :
    (P.offsetPage (n + 1)).dFrom (p, q) = 0 := by
  by_cases h :
      (ComplexShape.spectralSequenceNat
        ⟨(n : ℤ) + 3, 1 - ((n : ℤ) + 3)⟩).Rel
          (p, q) ((ComplexShape.spectralSequenceNat
            ⟨(n : ℤ) + 3, 1 - ((n : ℤ) + 3)⟩).next (p, q))
  · have hp : 3 ≤ ((ComplexShape.spectralSequenceNat
        ⟨(n : ℤ) + 3, 1 - ((n : ℤ) + 3)⟩).next (p, q)).1 := by
      rw [ComplexShape.spectralSequenceNat_rel_iff] at h
      omega
    exact (P.isZero_offsetPage_of_three_le (n + 1) _ _ hp).eq_of_tgt _ _
  · exact (P.offsetPage (n + 1)).dFrom_eq_zero h

/-- Every supported object is unchanged across one page transition after page three. -/
noncomputable def stablePageSuccIso (n : ℕ) (p : Fin 3) (q : ℕ) :
    (P.offsetPage (n + 1)).X (p, q) ≅ (P.offsetPage (n + 2)).X (p, q) :=
  ((ShortComplex.HomologyData.ofZeros ((P.offsetPage (n + 1)).sc (p, q))
      (P.stable_dTo_eq_zero n p q) (P.stable_dFrom_eq_zero n p q)).left.homologyIso).symm ≪≫
    P.spectralSequence.iso (((n + 1 : ℕ) : ℤ) + 2) (((n + 2 : ℕ) : ℤ) + 2)
      (p, q) (by omega)

/-- Page three is a stable page in every supported bidegree. -/
noncomputable def stablePageIso (p : Fin 3) (q n : ℕ) :
    P.Einf p q ≅ (P.offsetPage (n + 1)).X (p, q) :=
  Nat.rec (motive := fun n ↦ P.Einf p q ≅ (P.offsetPage (n + 1)).X (p, q))
    (Iso.refl _) (fun n e ↦ e ≪≫ P.stablePageSuccIso n p q) n

end Raw

/-- A finite increasing filtration with three successive graded pieces. -/
structure FiniteFiltration (M : Type w) [AddCommGroup M] [Module R M] where
  step : Fin 4 →o Submodule R M
  step_zero : step 0 = ⊥
  step_three : step 3 = ⊤

namespace FiniteFiltration

variable {R} {M : Type w} [AddCommGroup M] [Module R M]

/-- The `p`th successive quotient of a three-step finite filtration. -/
abbrev GradedPiece (F : FiniteFiltration R M) (p : Fin 3) :=
  F.step p.succ ⧸ (F.step p.castSucc).submoduleOf (F.step p.succ)

end FiniteFiltration

/-- Genuine convergence data for a raw three-column spectral sequence.

For total degree `p+q`, the stable page is identified with the corresponding successive quotient
of an explicit exhaustive finite filtration of the abutment. -/
structure Convergence (P : Raw.{u, v} R) where
  H : ℕ → Type w
  [addCommGroup : ∀ n, AddCommGroup (H n)]
  [module : ∀ n, Module R (H n)]
  filtration : ∀ n, FiniteFiltration R (H n)
  gradedIso : ∀ (p : Fin 3) (q : ℕ),
    P.Einf p q ≃ₗ[R] (filtration (p + q)).GradedPiece p

attribute [instance] Convergence.addCommGroup Convergence.module

namespace Convergence

variable {R} {P : Raw.{u, v} R} (A : Convergence.{u, v, w} R P)

/-- If an abutment group vanishes, every stable-page graded piece in that total degree vanishes. -/
theorem Einf_subsingleton (p : Fin 3) (q : ℕ)
    (hH : Subsingleton (A.H (p.1 + q))) : Subsingleton (P.Einf p q) := by
  let _ : Subsingleton (A.H (p.1 + q)) := hH
  have hgraded : Subsingleton ((A.filtration (p.1 + q)).GradedPiece p) := inferInstance
  exact (A.gradedIso p q).toEquiv.subsingleton_congr.mpr hgraded

/-- Vanishing of `H^(q+1)` forces vanishing of the middle-column `E₂^(1,q)` object. -/
theorem middle_E₂_subsingleton (q : ℕ) (hH : Subsingleton (A.H (q + 1))) :
    Subsingleton (P.E₂ 1 q) := by
  have hstable : Subsingleton (P.Einf 1 q) :=
    A.Einf_subsingleton (1 : Fin 3) q (by simpa [Nat.add_comm] using hH)
  exact (P.middlePermanenceIso q).toLinearEquiv.toEquiv.subsingleton_congr.mpr hstable

end Convergence

end ThreeColumnSpectralSequence
