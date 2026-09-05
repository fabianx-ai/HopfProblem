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

/-- Changing the integer representative of the total degree in a coyoneda Postnikov first-page
coordinate only inserts the corresponding equality transport on the represented morphism. -/
lemma coyonedaPostnikovFirstPageXIso_hom_apply_eq_of_deg
    (t : TStructure C) (A K : C) [t.IsLE A 0] [t.IsGE K 0]
    (pq : ℕ × ℕ) (i₁ i₂ : EInt)
    (hi₁ : i₁ = Abelian.SpectralObject.coreE₂CohomologicalNat.i₁ pq)
    (hi₂ : i₂ = Abelian.SpectralObject.coreE₂CohomologicalNat.i₂ pq)
    (n n' : ℤ)
    (hn : n = Abelian.SpectralObject.coreE₂CohomologicalNat.deg pq)
    (hn' : n' = Abelian.SpectralObject.coreE₂CohomologicalNat.deg pq)
    (y : ((t.coyonedaPostnikovSpectralSequence A K).page 2).X pq) :
    ((t.coyonedaPostnikovSpectralObject A K).spectralSequenceFirstPageXIso
        Abelian.SpectralObject.coreE₂CohomologicalNat pq i₁ i₂ hi₁ hi₂ n hn).hom.hom y ≫
      eqToHom (by subst n; subst n'; rfl) =
    ((t.coyonedaPostnikovSpectralObject A K).spectralSequenceFirstPageXIso
        Abelian.SpectralObject.coreE₂CohomologicalNat pq i₁ i₂ hi₁ hi₂ n' hn').hom.hom y := by
  subst n
  subst n'
  simp only [eqToHom_refl]
  erw [Category.comp_id]

/-- Changing all index representatives in a coyoneda Postnikov first-page coordinate only
inserts the equality transport between the represented morphism objects. -/
@[reassoc]
lemma coyonedaPostnikovFirstPageXIso_hom_apply_eq_of_indices
    (t : TStructure C) (A K : C) [t.IsLE A 0] [t.IsGE K 0]
    (pq : ℕ × ℕ) (i₁ i₂ i₁' i₂' : EInt)
    (hi₁ : i₁ = Abelian.SpectralObject.coreE₂CohomologicalNat.i₁ pq)
    (hi₂ : i₂ = Abelian.SpectralObject.coreE₂CohomologicalNat.i₂ pq)
    (hi₁' : i₁' = Abelian.SpectralObject.coreE₂CohomologicalNat.i₁ pq)
    (hi₂' : i₂' = Abelian.SpectralObject.coreE₂CohomologicalNat.i₂ pq)
    (n n' : ℤ)
    (hn : n = Abelian.SpectralObject.coreE₂CohomologicalNat.deg pq)
    (hn' : n' = Abelian.SpectralObject.coreE₂CohomologicalNat.deg pq)
    (y : ((t.coyonedaPostnikovSpectralSequence A K).page 2).X pq) :
    ((t.coyonedaPostnikovSpectralObject A K).spectralSequenceFirstPageXIso
        Abelian.SpectralObject.coreE₂CohomologicalNat pq i₁ i₂ hi₁ hi₂ n hn).hom.hom y ≫
      eqToHom (by subst i₁; subst i₁'; subst i₂; subst i₂'; subst n; subst n'; rfl) =
    ((t.coyonedaPostnikovSpectralObject A K).spectralSequenceFirstPageXIso
        Abelian.SpectralObject.coreE₂CohomologicalNat pq i₁' i₂' hi₁' hi₂' n' hn').hom.hom y := by
  subst i₁
  subst i₂
  subst i₁'
  subst i₂'
  subst n
  subst n'
  simp only [eqToHom_refl]
  erw [Category.comp_id]

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

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- At target bidegree `(2,q)`, the ordinary Postnikov page coordinate and the normalized
page-two-differential target coordinate agree after transport to the common shift `q + 2`. -/
lemma coyonedaPostnikovE₂PageIso_two_eq_d₂Target_apply
    (t : TStructure C) (A K : C) [t.IsLE A 0] [t.IsGE K 0] (q : ℕ)
    (y : ((t.coyonedaPostnikovSpectralSequence A K).page 2).X (2, q)) :
    (t.coyonedaPostnikovE₂PageIso A K 2 q).hom.hom y ≫
        eqToHom (show
          ((t.truncGE (q : ℤ)).obj
            ((t.truncLT ((q : ℤ) + 1)).obj K))⟦(2 : ℤ) + q⟧ =
          ((t.truncGE (q : ℤ)).obj
            ((t.truncLT ((q : ℤ) + 1)).obj K))⟦(q : ℤ) + 2⟧ by
            rw [show (2 : ℤ) + q = q + 2 by omega]) =
      (coyonedaPostnikovD₂TargetPageIso t A K 0 q).hom.hom y ≫
        eqToHom (show
          ((t.truncGE (q : ℤ)).obj
            ((t.truncLT ((q : ℤ) + 1)).obj K))⟦(0 : ℤ) + q + 2⟧ =
          ((t.truncGE (q : ℤ)).obj
            ((t.truncLT ((q : ℤ) + 1)).obj K))⟦(q : ℤ) + 2⟧ by
            rw [zero_add]) := by
  have h := coyonedaPostnikovFirstPageXIso_hom_apply_eq_of_deg
    t A K (2, q) (q : ℤ) (((q : ℤ) + 1 : ℤ) : EInt)
      (by simp)
      (by exact congrArg (fun z : ℤ => (z : EInt)) (by omega))
      ((2 : ℤ) + q) ((0 : ℤ) + q + 2)
      (by simp only [Abelian.SpectralObject.coreE₂CohomologicalNat_deg]; omega)
      (by simp only [Abelian.SpectralObject.coreE₂CohomologicalNat_deg]; omega) y
  dsimp [coyonedaPostnikovE₂PageIso,
    coyonedaPostnikovD₂TargetPageIso]
  convert h using 1 <;> simp
  all_goals rfl

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
