/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Algebra.Homology.ShortComplex.AbCycleClass
public import Lib.Algebra.Homology.CohomologyLongExact

/-!
# Cocycle classes in the cohomology of a cochain complex of abelian groups

The elementwise description of `L.homology q` for a cochain complex `L` of abelian groups indexed
by `ℕ`: cocycles `Cocycle L q` (the kernel of `L.d q (q + 1)`), their classes
`cocycleClass L q : Cocycle L q →+ L.homology q`, surjectivity, the vanishing criterion (a
coboundary in positive degree, zero in degree `0`), descent of additive maps out of cocycles that
kill coboundaries (`cohomologyDescSucc`, `cohomologyDescZero`), and naturality under maps of
complexes.  This is the cochain counterpart of `SingularMayerVietoris.ModuleHomology` (cycle
classes of chain complexes of `ℤ`-modules), built on `ShortComplex.shortCycleClass`.

The short complex `L.sc q` has middle term `L.X q` but outer terms indexed by the opaque
`(ComplexShape.up ℕ).prev q` and `.next q`; the definitions below are stated with the literal
degrees `q - 1`, `q`, `q + 1` and the transport is confined to this file.

## Main definitions and results

* `CochainCocycle.Cocycle`, `CochainCocycle.mkCocycle`, `CochainCocycle.cocycleClass`.
* `CochainCocycle.cocycleClass_surjective`, `cocycleClass_eq_zero_iff_succ`,
  `cocycleClass_eq_zero_iff_zero`, `cocycleClass_eq_iff_succ`.
* `CochainCocycle.cohomologyDescSucc`, `cohomologyDescZero` and their `_cocycleClass` lemmas.
* `CochainCocycle.mapCocycle`, `cohomologyHom_cocycleClass`.

## Tags

cochain complex, cocycle, cohomology class
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace CochainCocycle

variable (L : CochainComplex AddCommGrpCat.{0} ℕ) (q : ℕ)

/-- The degree-`q` cocycles of `L`: the kernel of `L.d q (q + 1)`. -/
abbrev Cocycle := AddMonoidHom.ker (L.d q (q + 1)).hom

/-- A cocycle satisfies `L.d q (q + 1) z = 0`. -/
theorem cocycle_condition (z : Cocycle L q) : L.d q (q + 1) z.1 = 0 := z.2

/-- A cochain with vanishing coboundary as a cocycle. -/
def mkCocycle (z : L.X q) (hz : L.d q (q + 1) z = 0) : Cocycle L q := ⟨z, hz⟩

@[simp] theorem mkCocycle_val (z : L.X q) (hz : L.d q (q + 1) z = 0) : (mkCocycle L q z hz).1 = z := rfl

/-- A cocycle is a cycle of the short complex `L.sc q`. -/
theorem sc_g_apply_eq_zero (z : Cocycle L q) : (L.sc q).g z.1 = 0 := by
  change (L.d q ((ComplexShape.up ℕ).next q)) z.1 = 0
  rw [CochainComplex.next]
  exact z.2

/-- A cycle of the short complex `L.sc q`, as a cocycle. -/
def toCocycle (z : AddMonoidHom.ker (L.sc q).g.hom) : Cocycle L q :=
  ⟨z.1, by
    have h : (L.d q ((ComplexShape.up ℕ).next q)) z.1 = 0 := z.2
    rw [CochainComplex.next] at h
    exact h⟩

@[simp] theorem toCocycle_val (z : AddMonoidHom.ker (L.sc q).g.hom) : (toCocycle L q z).1 = z.1 := rfl

/-- A cocycle as a cycle of the short complex `L.sc q`. -/
def ofCocycle : Cocycle L q →+ AddMonoidHom.ker (L.sc q).g.hom :=
  AddMonoidHom.mk' (fun z => ⟨z.1, sc_g_apply_eq_zero L q z⟩) (fun _ _ => rfl)

@[simp] theorem ofCocycle_val (z : Cocycle L q) : (ofCocycle L q z).1 = z.1 := rfl

/-- The cohomology class of a cocycle. -/
def cocycleClass : Cocycle L q →+ L.homology q :=
  ((L.sc q).homologyπ.hom.comp (L.sc q).abCyclesIso.inv.hom).comp (ofCocycle L q)

theorem cocycleClass_apply (z : Cocycle L q) :
    cocycleClass L q z = ShortComplex.shortCycleClass (L.sc q) (ofCocycle L q z).1 (ofCocycle L q z).2 := rfl

/-- Every cohomology class is the class of a cocycle. -/
theorem cocycleClass_surjective : Function.Surjective (cocycleClass L q) := by
  intro x
  obtain ⟨z, hz, rfl⟩ := ShortComplex.shortCycleClass_surjective (L.sc q) x
  exact ⟨toCocycle L q ⟨z, hz⟩, rfl⟩

/-- Two additive maps out of `L.homology q` agreeing on all cocycle classes are equal. -/
theorem cohomology_hom_ext {M : Type*} [AddCommGroup M] {f g : L.homology q →+ M}
    (h : ∀ z : Cocycle L q, f (cocycleClass L q z) = g (cocycleClass L q z)) : f = g := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨z, rfl⟩ := cocycleClass_surjective L q x
  exact h z

/-- In positive degree a cocycle class vanishes exactly when the cocycle is a coboundary. -/
theorem cocycleClass_eq_zero_iff_succ (z : Cocycle L (q + 1)) :
    cocycleClass L (q + 1) z = 0 ↔ ∃ b : L.X q, L.d q (q + 1) b = z.1 := by
  refine (ShortComplex.shortCycleClass_eq_zero_iff (L.sc (q + 1)) z.1 _).trans ?_
  change (∃ b : L.X ((ComplexShape.up ℕ).prev (q + 1)),
    L.d ((ComplexShape.up ℕ).prev (q + 1)) (q + 1) b = z.1) ↔ _
  rw [CochainComplex.prev_nat_succ]

/-- In degree `0` a cocycle class vanishes exactly when the cocycle is zero. -/
theorem cocycleClass_eq_zero_iff_zero (z : Cocycle L 0) : cocycleClass L 0 z = 0 ↔ z.1 = 0 := by
  refine (ShortComplex.shortCycleClass_eq_zero_iff (L.sc 0) z.1 _).trans ?_
  change (∃ b : L.X ((ComplexShape.up ℕ).prev 0), L.d ((ComplexShape.up ℕ).prev 0) 0 b = z.1) ↔ _
  rw [CochainComplex.prev_nat_zero]
  constructor
  · rintro ⟨b, hb⟩
    rw [← hb, L.shape 0 0 (by simp)]
    rfl
  · intro h
    exact ⟨0, by rw [map_zero, h]⟩

/-- Two cocycle classes agree exactly when the cocycles differ by a coboundary (positive
degree). -/
theorem cocycleClass_eq_iff_succ (z w : Cocycle L (q + 1)) :
    cocycleClass L (q + 1) z = cocycleClass L (q + 1) w ↔ ∃ b : L.X q, L.d q (q + 1) b = z.1 - w.1 := by
  rw [← sub_eq_zero, ← map_sub, cocycleClass_eq_zero_iff_succ]
  rfl

/-- Two cocycle classes in degree `0` agree exactly when the cocycles agree. -/
theorem cocycleClass_eq_iff_zero (z w : Cocycle L 0) :
    cocycleClass L 0 z = cocycleClass L 0 w ↔ z.1 = w.1 := by
  rw [← sub_eq_zero, ← map_sub, cocycleClass_eq_zero_iff_zero, AddSubgroup.coe_sub, sub_eq_zero]

/-! ### Descent to cohomology -/

/-- The incoming coboundary of the short complex at `q + 1`, in literal form. -/
theorem sc_f_succ_apply (b : (L.sc (q + 1)).X₁) :
    (L.sc (q + 1)).f b = L.d q (q + 1) ((L.XIsoOfEq (CochainComplex.prev_nat_succ q)).hom b) := by
  change (L.d ((ComplexShape.up ℕ).prev (q + 1)) (q + 1)) b = _
  rw [← L.XIsoOfEq_hom_comp_d (CochainComplex.prev_nat_succ q) (q + 1)]
  rfl

/-- The incoming coboundary of the short complex at `0` vanishes. -/
theorem sc_f_zero_apply (b : (L.sc 0).X₁) : (L.sc 0).f b = 0 := by
  change (L.d ((ComplexShape.up ℕ).prev 0) 0) b = 0
  rw [← L.XIsoOfEq_hom_comp_d CochainComplex.prev_nat_zero 0, L.shape 0 0 (by simp),
    Limits.comp_zero]
  rfl

/-- The lift of an additive map on cocycles vanishing on incoming coboundaries to cycles modulo
boundaries. -/
def descLift {M : Type*} [AddCommGroup M] (f : Cocycle L q →+ M)
    (hf : ∀ b : (L.sc q).X₁, f (toCocycle L q ((L.sc q).abToCycles b)) = 0) :
    (AddMonoidHom.ker (L.sc q).g.hom ⧸ AddMonoidHom.range (L.sc q).abToCycles) →+ M :=
  QuotientAddGroup.lift (AddMonoidHom.range (L.sc q).abToCycles)
    (f.comp (AddMonoidHom.mk' (toCocycle L q) (fun _ _ => rfl))) (by
      rintro _ ⟨b, rfl⟩
      exact hf b)

/-- Descent of an additive map on cocycles vanishing on incoming coboundaries to cohomology. -/
def cohomologyDesc {M : Type*} [AddCommGroup M] (f : Cocycle L q →+ M)
    (hf : ∀ b : (L.sc q).X₁, f (toCocycle L q ((L.sc q).abToCycles b)) = 0) : L.homology q →+ M :=
  (descLift L q f hf).comp (L.sc q).abHomologyIso.hom.hom

theorem cohomologyDesc_cocycleClass {M : Type*} [AddCommGroup M] (f : Cocycle L q →+ M)
    (hf : ∀ b : (L.sc q).X₁, f (toCocycle L q ((L.sc q).abToCycles b)) = 0) (z : Cocycle L q) :
    cohomologyDesc L q f hf (cocycleClass L q z) = f z := by
  change descLift L q f hf ((L.sc q).abHomologyIso.hom
    (ShortComplex.shortCycleClass (L.sc q) (ofCocycle L q z).1 (ofCocycle L q z).2)) = f z
  refine (congrArg (descLift L q f hf) (ShortComplex.shortCycleClass_quotient (L.sc q)
    (ofCocycle L q z).1 (ofCocycle L q z).2)).trans ?_
  rfl

/-- Descent in positive degree: an additive map on cocycles vanishing on all coboundaries
`L.d q (q + 1) b` descends to `L.homology (q + 1)`. -/
def cohomologyDescSucc {M : Type*} [AddCommGroup M] (f : Cocycle L (q + 1) →+ M)
    (hf : ∀ (b : L.X q) (hb : L.d (q + 1) (q + 1 + 1) (L.d q (q + 1) b) = 0),
      f (mkCocycle L (q + 1) (L.d q (q + 1) b) hb) = 0) : L.homology (q + 1) →+ M :=
  cohomologyDesc L (q + 1) f (fun b => by
    have h : toCocycle L (q + 1) ((L.sc (q + 1)).abToCycles b) =
        mkCocycle L (q + 1) (L.d q (q + 1) ((L.XIsoOfEq (CochainComplex.prev_nat_succ q)).hom b))
          (by rw [← ConcreteCategory.comp_apply, L.d_comp_d]; rfl) :=
      Subtype.ext (sc_f_succ_apply L q b)
    rw [h]
    exact hf _ _)

@[simp]
theorem cohomologyDescSucc_cocycleClass {M : Type*} [AddCommGroup M] (f : Cocycle L (q + 1) →+ M)
    (hf) (z : Cocycle L (q + 1)) :
    cohomologyDescSucc L q f hf (cocycleClass L (q + 1) z) = f z :=
  cohomologyDesc_cocycleClass L (q + 1) f _ z

/-- In degree `0` every additive map on cocycles descends. -/
def cohomologyDescZero {M : Type*} [AddCommGroup M] (f : Cocycle L 0 →+ M) : L.homology 0 →+ M :=
  cohomologyDesc L 0 f (fun b => by
    have h : toCocycle L 0 ((L.sc 0).abToCycles b) = 0 := Subtype.ext (sc_f_zero_apply L b)
    rw [h, map_zero])

@[simp]
theorem cohomologyDescZero_cocycleClass {M : Type*} [AddCommGroup M] (f : Cocycle L 0 →+ M)
    (z : Cocycle L 0) : cohomologyDescZero L f (cocycleClass L 0 z) = f z :=
  cohomologyDesc_cocycleClass L 0 f _ z

/-! ### Naturality -/

variable {L} {L' : CochainComplex AddCommGrpCat.{0} ℕ}

/-- The image of a cocycle under a map of cochain complexes. -/
def mapCocycle (φ : L ⟶ L') (z : Cocycle L q) : Cocycle L' q :=
  mkCocycle L' q (φ.f q z.1) (by
    rw [← ConcreteCategory.comp_apply, φ.comm q (q + 1), ConcreteCategory.comp_apply,
      cocycle_condition, map_zero])

@[simp] theorem mapCocycle_val (φ : L ⟶ L') (z : Cocycle L q) : (mapCocycle q φ z).1 = φ.f q z.1 := rfl

/-- The map on cohomology sends cocycle classes to the classes of the image cocycles. -/
theorem cohomologyHom_cocycleClass (φ : L ⟶ L') (z : Cocycle L q) :
    CohomologyLongExact.cohomologyHom φ q (cocycleClass L q z) = cocycleClass L' q (mapCocycle q φ z) := by
  rw [cocycleClass_apply, cocycleClass_apply]
  exact ShortComplex.shortHomologyMap_cycleClass
    ((HomologicalComplex.shortComplexFunctor _ _ q).map φ) _ _ _

end CochainCocycle
