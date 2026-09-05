/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.SpectralObject.Postnikov

/-!
# The page-two differential of a Postnikov spectral object

This file expands the page-two differential of a coyoneda Postnikov spectral object as the
connecting map of the adjacent two-slice truncation triangle.  The endpoint isomorphisms use
normalized integer cutoffs.  This avoids a dependent transport between the propositionally equal
expressions `↑(q + 1)` and `↑q + 1` in the natural-indexed spectral-sequence API.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Triangulated.TStructure

universe uC vC

variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-- The source page isomorphism for the page-two differential
`(p,q+1) ⟶ (p+2,q)`, with all cutoffs normalized as integer expressions in `q`. -/
def coyonedaPostnikovD₂SourcePageIso
    (t : TStructure C) (A K : C) [t.IsLE A 0] [t.IsGE K 0] (p q : ℕ) :
    ((t.coyonedaPostnikovSpectralSequence A K).page 2).X (p, q + 1) ≅
      AddCommGrpCat.of
        (A ⟶ ((t.eTruncGE.obj ((q : ℤ) + 1 : ℤ)).obj
          ((t.eTruncLT.obj ((q : ℤ) + 2 : ℤ)).obj K))⟦((p : ℤ) + q + 1 : ℤ)⟧) :=
  (t.coyonedaPostnikovSpectralObject A K).spectralSequenceFirstPageXIso
    Abelian.SpectralObject.coreE₂CohomologicalNat (p, q + 1)
    ((q : ℤ) + 1 : ℤ) ((q : ℤ) + 2 : ℤ)
    (by simp) (by exact congrArg (fun z : ℤ => (z : EInt)) (by omega))
    ((p : ℤ) + q + 1 : ℤ)
    (by simp only [Abelian.SpectralObject.coreE₂CohomologicalNat_deg]; omega)

/-- The target page isomorphism for the page-two differential
`(p,q+1) ⟶ (p+2,q)`, with all cutoffs normalized as integer expressions in `q`. -/
def coyonedaPostnikovD₂TargetPageIso
    (t : TStructure C) (A K : C) [t.IsLE A 0] [t.IsGE K 0] (p q : ℕ) :
    ((t.coyonedaPostnikovSpectralSequence A K).page 2).X (p + 2, q) ≅
      AddCommGrpCat.of
        (A ⟶ ((t.eTruncGE.obj (q : ℤ)).obj
          ((t.eTruncLT.obj ((q : ℤ) + 1 : ℤ)).obj K))⟦((p : ℤ) + q + 2 : ℤ)⟧) :=
  (t.coyonedaPostnikovSpectralObject A K).spectralSequenceFirstPageXIso
    Abelian.SpectralObject.coreE₂CohomologicalNat (p + 2, q)
    (q : ℤ) ((q : ℤ) + 1 : ℤ)
    (by simp) (by simp)
    ((p : ℤ) + q + 2 : ℤ)
    (by simp only [Abelian.SpectralObject.coreE₂CohomologicalNat_deg]; omega)

/-- The spectral-object connecting map used by `d₂` is definitionally the homological
connecting map of the adjacent two-slice truncation triangle. -/
lemma coyonedaPostnikovD₂δ_eq (t : TStructure C) (A K : C) (p q : ℕ) :
    (t.coyonedaPostnikovSpectralObject A K).δ
        (homOfLE (show ((q : ℤ) : EInt) ≤ (((q : ℤ) + 1 : ℤ) : EInt) by simp))
        (homOfLE (show (((q : ℤ) + 1 : ℤ) : EInt) ≤
          (((q : ℤ) + 2 : ℤ) : EInt) by simp))
        ((p : ℤ) + q + 1 : ℤ) ((p : ℤ) + q + 2 : ℤ) (by omega) =
      (preadditiveCoyoneda.obj (op A)).homologySequenceδ
        ((t.triangleω₁δ (q : ℤ) ((q : ℤ) + 1 : ℤ) ((q : ℤ) + 2 : ℤ)
          (by simp) (by simp)).obj K)
        ((p : ℤ) + q + 1 : ℤ) ((p : ℤ) + q + 2 : ℤ) (by omega) := by
  rfl

/-- Under normalized endpoint isomorphisms, the page-two differential is exactly the
homological connecting map of the adjacent two-slice Postnikov triangle. -/
lemma coyonedaPostnikovE₂_d₂_eq
    (t : TStructure C) (A K : C) [t.IsLE A 0] [t.IsGE K 0] (p q : ℕ) :
    ((t.coyonedaPostnikovSpectralSequence A K).page 2).d (p, q + 1) (p + 2, q) =
      (coyonedaPostnikovD₂SourcePageIso t A K p q).hom ≫
        (preadditiveCoyoneda.obj (op A)).homologySequenceδ
          ((t.triangleω₁δ (q : ℤ) ((q : ℤ) + 1 : ℤ) ((q : ℤ) + 2 : ℤ)
            (by simp) (by simp)).obj K)
          ((p : ℤ) + q + 1 : ℤ) ((p : ℤ) + q + 2 : ℤ) (by omega) ≫
        (coyonedaPostnikovD₂TargetPageIso t A K p q).inv := by
  rw [← coyonedaPostnikovD₂δ_eq t A K p q]
  exact
    (t.coyonedaPostnikovSpectralObject A K).spectralSequence_first_page_d_eq
      Abelian.SpectralObject.coreE₂CohomologicalNat
      (p, q + 1) (p + 2, q)
      (by simp [ComplexShape.spectralSequenceNat_rel_iff])
      (q : ℤ) ((q : ℤ) + 1 : ℤ) ((q : ℤ) + 2 : ℤ)
      (by simp) (by simp)
      (by exact congrArg (fun z : ℤ => (z : EInt)) (by omega))
      ((p : ℤ) + q + 1 : ℤ) ((p : ℤ) + q + 2 : ℤ)
      (by simp only [Abelian.SpectralObject.coreE₂CohomologicalNat_deg]; omega) (by omega)

end CategoryTheory.Triangulated.TStructure
