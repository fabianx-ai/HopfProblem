/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Lib.Algebra.Homology.ThreeColumnPage
public import Lib.Algebra.Homology.ThreeColumnSpectralSequence

/-!
# Adapter from an actual three-column spectral sequence to page bookkeeping

This file constructs the existing `ThreeColumnPage.Data` only after the two middle-column
vanishings have been derived from genuine convergence and abutment vanishing. The page entries and
the three lower differentials are the actual `E₂` objects and `d₂` morphisms of the supplied
spectral sequence.
-/

@[expose] public section

namespace ThreeColumnSpectralSequence

universe u v w

variable (R : Type u) [CommRing R]

/-- Rank-one coordinates on the six outer `E₂` objects used by the lower differentials. -/
structure OuterNormalization (P : Raw.{u, v} R) where
  source : ∀ i : Fin 3, P.E₂ 0 i.succ ≃ₗ[R] R
  target : ∀ i : Fin 3, P.E₂ 2 i.castSucc ≃ₗ[R] R

namespace Convergence

variable {R} {P : Raw.{u, v} R} (A : Convergence.{u, v, w} R P)

/-- Package the actual `E₂` page as `ThreeColumnPage.Data` after abutment vanishing has proved
the two middle-column entries trivial. -/
def toThreeColumnPageData (N : OuterNormalization R P)
    (hH₂ : Subsingleton (A.H 2)) (hH₃ : Subsingleton (A.H 3)) :
    ThreeColumnPage.Data R where
  E a b := P.E₂ a b
  addCommGroup _ _ := inferInstance
  module _ _ := inferInstance
  differential i := (P.d₂ 0 i).hom
  source i := N.source i
  target i := N.target i
  middle j := by
    fin_cases j
    · exact A.middle_E₂_subsingleton 1 hH₂
    · exact A.middle_E₂_subsingleton 2 hH₃

/-- The page entries of the packaged data are the `E₂` objects of the spectral sequence. -/
@[simp]
theorem toThreeColumnPageData_E (N : OuterNormalization R P)
    (hH₂ : Subsingleton (A.H 2)) (hH₃ : Subsingleton (A.H 3)) (a : Fin 3) (b : Fin 4) :
    (A.toThreeColumnPageData N hH₂ hH₃).E a b = P.E₂ a b :=
  rfl

/-- The differentials of the packaged data are the `d₂` morphisms of the spectral sequence. -/
@[simp]
theorem toThreeColumnPageData_differential (N : OuterNormalization R P)
    (hH₂ : Subsingleton (A.H 2)) (hH₃ : Subsingleton (A.H 3)) (i : Fin 3) :
    (A.toThreeColumnPageData N hH₂ hH₃).differential i = (P.d₂ 0 i).hom :=
  rfl

/-- The source coordinates of the packaged data are the chosen ones. -/
@[simp]
theorem toThreeColumnPageData_source (N : OuterNormalization R P)
    (hH₂ : Subsingleton (A.H 2)) (hH₃ : Subsingleton (A.H 3)) (i : Fin 3) :
    (A.toThreeColumnPageData N hH₂ hH₃).source i = N.source i :=
  rfl

/-- The target coordinates of the packaged data are the chosen ones. -/
@[simp]
theorem toThreeColumnPageData_target (N : OuterNormalization R P)
    (hH₂ : Subsingleton (A.H 2)) (hH₃ : Subsingleton (A.H 3)) (i : Fin 3) :
    (A.toThreeColumnPageData N hH₂ hH₃).target i = N.target i :=
  rfl

end Convergence

end ThreeColumnSpectralSequence
