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

end ThreeColumnSpectralSequence
