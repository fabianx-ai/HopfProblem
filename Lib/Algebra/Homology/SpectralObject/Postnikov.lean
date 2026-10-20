/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Lib.Algebra.Homology.SpectralObject.MapHomologicalFunctor
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.SpectralObject.FirstPage
public import Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject
public import Mathlib.CategoryTheory.Triangulated.Yoneda

/-!
# Postnikov spectral objects

This file combines the truncation spectral object of a `t`-structure with a homological functor.
For a representable functor `Hom(A, -)`, an object `A` in nonpositive degrees and an object `K`
in nonnegative degrees, it also proves the first-quadrant hypotheses and exposes the resulting
`E₂` spectral sequence.

The construction supplies pages and page-to-page homology isomorphisms.  It does not claim an
associated-graded identification with the total object: Mathlib's current `SpectralSequence` API
does not yet package that convergence datum.

## References

* [A. A. Beilinson, J. Bernstein, P. Deligne, *Faisceaux pervers*][bbd82], §1.3.
* [S. I. Gelfand, Yu. I. Manin, *Methods of homological algebra*][gelfandManin03], Chapter IV,
  §4 (the hypercohomology spectral sequence of the t-structure filtration).

-/

@[expose] public section

noncomputable section

namespace CategoryTheory

open Limits Opposite

namespace Triangulated.TStructure

universe uC vC uA vA

variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {A : Type uA} [Category.{vA} A] [Abelian A]

/-- Apply a homological functor to the Postnikov spectral object of `K`. -/
noncomputable def postnikovSpectralObject (t : TStructure C) (K : C) (F : C ⥤ A)
    [F.IsHomological] [F.ShiftSequence ℤ] :
    Abelian.SpectralObject A EInt :=
  (t.spectralObject K).mapHomologicalFunctor F

/-- The total interval of the Postnikov spectral object is the original object, so after applying
`F` its degree-`n` value is `(F.shift n).obj K`. -/
noncomputable def postnikovTotalIso (t : TStructure C) (K : C) (F : C ⥤ A)
    [F.IsHomological] [F.ShiftSequence ℤ] (n : ℤ) :
    (((t.postnikovSpectralObject K F).H n).obj
      (ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤)))) ≅
      (F.shift n).obj K :=
  Iso.refl _

/-- The Postnikov spectral object seen by the representable homological functor `Hom(A, -)`. -/
noncomputable def coyonedaPostnikovSpectralObject (t : TStructure C) (A K : C) :
    Abelian.SpectralObject AddCommGrpCat.{vC} EInt :=
  t.postnikovSpectralObject K (preadditiveCoyoneda.obj (op A))

/-- A bounded-below Postnikov tower, tested against an object in nonpositive degrees, satisfies
Mathlib's first-quadrant hypotheses. -/
instance coyonedaPostnikovSpectralObject_isFirstQuadrant
    (t : TStructure C) (A K : C) [t.IsLE A 0] [t.IsGE K 0] :
    (t.coyonedaPostnikovSpectralObject A K).IsFirstQuadrant where
  isZero₁ i j hij hj n := by
    change IsZero (((preadditiveCoyoneda.obj (op A)).shift n).obj
      ((t.eTruncGE.obj i).obj ((t.eTruncLT.obj j).obj K)))
    exact Functor.map_isZero _
      (Functor.map_isZero _ (t.isZero_eTruncLT_obj_obj K 0 j hj))
  isZero₂ i j hij n hi := by
    let Z := (t.eTruncGE.obj i).obj ((t.eTruncLT.obj j).obj K)
    have hni : (n + 1 : ℤ) ≤ i := by
      induction i using WithBotTop.rec <;> simp_all
      omega
    let hZ : t.IsGE Z (n + 1) :=
      t.isGE_eTruncGE_obj_obj (n + 1) i hni _
    change IsZero (AddCommGrpCat.of (A ⟶ Z⟦n⟧))
    rw [AddCommGrpCat.isZero_iff_subsingleton]
    constructor
    intro f g
    rw [t.zero_of_isLE_of_isGE f 0 1 (by omega) inferInstance
      (t.isGE_shift Z (n + 1) n 1 (by omega))]
    rw [t.zero_of_isLE_of_isGE g 0 1 (by omega) inferInstance
      (t.isGE_shift Z (n + 1) n 1 (by omega))]

/-- The first-quadrant `E₂` spectral sequence associated to the Postnikov tower of `K` and the
representable homological functor `Hom(A, -)`. -/
noncomputable abbrev coyonedaPostnikovSpectralSequence
    (t : TStructure C) (A K : C) [t.IsLE A 0] [t.IsGE K 0] :
    E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{vC} :=
  (t.coyonedaPostnikovSpectralObject A K).E₂SpectralSequenceNat

/-- The initial page at `(p,q)` is the shifted representable group of the Postnikov slice
`τ_[q,q+1) K`.  Identifying this slice with the degree-`q` cohomology object is a separate,
application-independent comparison. -/
noncomputable def coyonedaPostnikovE₂PageIso
    (t : TStructure C) (A K : C) [t.IsLE A 0] [t.IsGE K 0] (p q : ℕ) :
    ((t.coyonedaPostnikovSpectralSequence A K).page 2).X (p, q) ≅
      AddCommGrpCat.of
        (A ⟶ ((t.eTruncGE.obj (q : ℤ)).obj
          ((t.eTruncLT.obj (q + 1 : ℤ)).obj K))⟦(p + q : ℤ)⟧) :=
  (t.coyonedaPostnikovSpectralObject A K).spectralSequenceFirstPageXIso
    Abelian.SpectralObject.coreE₂CohomologicalNat (p, q)
    (q : ℤ) (q + 1 : ℤ) rfl rfl (p + q : ℤ) (by simp)

end Triangulated.TStructure

end CategoryTheory
