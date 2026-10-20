/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.Cohomology.Cech.CochainSheafResolution
public import Lib.Topology.Sheaves.Cohomology.Cech.CohomologySystem
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Topology.Sheaves.Flasque

/-!
# Flasque acyclicity for normalized fixed-cover Čech cohomology

For an arbitrary set-indexed open cover and a flasque sheaf of abelian groups, every
positive-degree cocycle in the normalized ordered Čech complex has an actual primitive: a flasque
sheaf is Čech-acyclic for every cover.  The proof is the direct cochain-sheaf argument.

The sheaf of degree-`n` cochains is flasque because it is a product of flasque
intersection-section factors.  The exact augmented cochain-sheaf resolution then presents its
successive cycle sheaves in short exact sequences.  The flasque extension theorem makes those
cycle sheaves flasque inductively and makes the preceding map surjective on global sections.
Lifting a global cycle through that map produces the required normalized Čech primitive.

No local-finiteness, separation, or paracompactness hypothesis is used, and no cohomology
comparison theorem enters the proof.

## References

* R. Godement, *Topologie algébrique et théorie des faisceaux*, II.5.2.3
* R. Hartshorne, *Algebraic Geometry*, III, Proposition 2.5 and Lemma 4.2
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace TopologicalSpace.OpenCover.OrderedCech

variable {X : TopCat.{u}}
variable {ι : Type u} [LinearOrder ι]

/-! ## Flasqueness of the cochain sheaves -/

/-- Intersecting the argument of a flasque sheaf with a fixed open produces a flasque sheaf. -/
theorem intersectionSectionsSheaf_isFlasque
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) [F.IsFlasque]
    (V : Opens X) : (intersectionSectionsSheaf F V).IsFlasque where
  epi {W Z} i := by
    change Epi (F.presheaf.map _)
    infer_instance

/-- Every normalized Čech cochain sheaf of a flasque sheaf is flasque.

For each inclusion of opens, the restriction morphism is conjugate to the product of the
restriction morphisms of the intersection-section factors. -/
theorem cochainSheaf_isFlasque
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) [F.IsFlasque]
    (U : ι → Opens X) (n : ℕ) : (cochainSheaf F U n).IsFlasque := by
  constructor
  intro W Z i
  let eW := cochainSheafSectionsProductIso F U n W.unop
  let eZ := cochainSheafSectionsProductIso F U n Z.unop
  let p : ∀ σ : OrderedSimplex ι n,
      ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj W).obj
          ((TopCat.Sheaf.forget AddCommGrpCat X).obj
            (intersectionSectionsSheaf F (σ.intersection U))) ⟶
        ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj Z).obj
          ((TopCat.Sheaf.forget AddCommGrpCat X).obj
            (intersectionSectionsSheaf F (σ.intersection U))) :=
    fun σ => (intersectionSectionsSheaf F (σ.intersection U)).presheaf.map i
  have hp (σ : OrderedSimplex ι n) : Epi (p σ) := by
    dsimp only [p]
    exact (intersectionSectionsSheaf_isFlasque F (σ.intersection U)).epi i
  have hPi : Epi (Limits.Pi.map p) := by
    dsimp only [Limits.Pi.map]
    rw [Limits.limMap_eq]
    let A : OrderedSimplex ι n → AddCommGrpCat.{u} := fun σ =>
      ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj W).obj
        ((TopCat.Sheaf.forget AddCommGrpCat X).obj
          (intersectionSectionsSheaf F (σ.intersection U)))
    let B : OrderedSimplex ι n → AddCommGrpCat.{u} := fun σ =>
      ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj Z).obj
        ((TopCat.Sheaf.forget AddCommGrpCat X).obj
          (intersectionSectionsSheaf F (σ.intersection U)))
    let α : Discrete.functor A ⟶ Discrete.functor B :=
      Discrete.natTrans fun σ => p σ.as
    have hα : Epi α := (CategoryTheory.NatTrans.epi_iff_epi_app α).2
      (fun σ => hp σ.as)
    exact @Functor.map_epi _ _ _ _
      (lim (J := Discrete (OrderedSimplex ι n)) (C := AddCommGrpCat.{u}))
      _ _ _ α hα
  have hmap : (cochainSheaf F U n).presheaf.map i =
      eW.hom ≫ Limits.Pi.map p ≫ eZ.inv := by
    apply (cancel_mono eZ.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply Limits.Pi.hom_ext
    intro σ
    simp only [Category.assoc]
    rw [Limits.Pi.map_π]
    dsimp only [eW, eZ]
    rw [cochainSheafSectionsProductIso_hom_π,
      cochainSheafSectionsProductIso_hom_π_assoc]
    exact (Limits.Pi.π (fun τ : OrderedSimplex ι n =>
      intersectionSectionsSheaf F (τ.intersection U)) σ).hom.naturality i
  rw [hmap]
  infer_instance

/-! ## Cycle sheaves and global primitives -/

private noncomputable def cochainSheafGlobalSectionsIso
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U : ι → Opens X) (n : ℕ) :
    (cochainSheaf F U n).presheaf.obj (op (⊤ : Opens X)) ≅
      OrderedCech.object F.presheaf U n := by
  let h : restrictedFamily (⊤ : Opens X) U = U := by
    funext i
    simp [restrictedFamily]
  exact cochainSheafSectionsIso F U n (⊤ : Opens X) ≪≫
    eqToIso (congrArg
      (fun V : ι → Opens X => OrderedCech.object F.presheaf V n) h)

private theorem differential_eqToHom
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) {U V : ι → Opens X}
    (h : U = V) (n : ℕ) :
    differential F.presheaf U n ≫ eqToHom (congrArg
        (fun W : ι → Opens X => OrderedCech.object F.presheaf W (n + 1)) h) =
      eqToHom (congrArg
          (fun W : ι → Opens X => OrderedCech.object F.presheaf W n) h) ≫
        differential F.presheaf V n := by
  subst V
  simp

@[reassoc]
private theorem cochainSheafDifferential_app_comp_globalSectionsIso
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U : ι → Opens X) (n : ℕ) :
    (cochainSheafDifferential F U n).hom.app (op (⊤ : Opens X)) ≫
        (cochainSheafGlobalSectionsIso F U (n + 1)).hom =
      (cochainSheafGlobalSectionsIso F U n).hom ≫
        differential F.presheaf U n := by
  let h : restrictedFamily (⊤ : Opens X) U = U := by
    funext i
    simp [restrictedFamily]
  change (cochainSheafDifferential F U n).hom.app (op (⊤ : Opens X)) ≫
      (cochainSheafSectionsIso F U (n + 1) (⊤ : Opens X)).hom ≫
        eqToHom (congrArg (fun V : ι → Opens X =>
          OrderedCech.object F.presheaf V (n + 1)) h) =
    (cochainSheafSectionsIso F U n (⊤ : Opens X)).hom ≫
      eqToHom (congrArg (fun V : ι → Opens X =>
        OrderedCech.object F.presheaf V n) h) ≫ differential F.presheaf U n
  rw [← Category.assoc, cochainSheafDifferential_app_comp_sectionsIso]
  rw [Category.assoc, differential_eqToHom F h n]

/-- The cycle sheaves in the exact augmented normalized Čech cochain-sheaf resolution of a
flasque sheaf are flasque. -/
theorem augmentedCochainSheafCycle_isFlasque
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) [F.IsFlasque]
    (U : ι → Opens X) (hU : IsOpenCover U) (n : ℕ) :
    (augmentedCochainSheafComplex F U hU).Z n |>.IsFlasque := by
  induction n with
  | zero =>
      change F.IsFlasque
      infer_instance
  | succ n ih =>
      let R := augmentedCochainSheafComplex F U hU
      have hX : (R.complex.X n).IsFlasque := by
        change (cochainSheaf F U n).IsFlasque
        exact cochainSheaf_isFlasque F U n
      let _ : (R.Z n).IsFlasque := ih
      let _ : (R.complex.X n).IsFlasque := hX
      exact TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂
        (R.step_shortExact n)

private theorem globalCocycle_boundary
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) [F.IsFlasque]
    (U : ι → Opens X) (hU : IsOpenCover U) (n : ℕ)
    (c : (cochainSheaf F U (n + 1)).presheaf.obj (op (⊤ : Opens X)))
    (hc : (cochainSheafDifferential F U (n + 1)).hom.app
      (op (⊤ : Opens X)) c = 0) :
    ∃ b : (cochainSheaf F U n).presheaf.obj (op (⊤ : Opens X)),
      (cochainSheafDifferential F U n).hom.app (op (⊤ : Opens X)) b = c := by
  let R := augmentedCochainSheafComplex F U hU
  have hcR : (R.complex.d (n + 1) ((n + 1) + 1)).hom.app
      (op (⊤ : Opens X)) c = 0 := by
    have hdR : R.complex.d (n + 1) ((n + 1) + 1) =
        cochainSheafDifferential F U (n + 1) := by
      simpa only [R, augmentedCochainSheafComplex] using
        cochainSheafComplex_d F U (n + 1)
    rw [hdR]
    exact hc
  obtain ⟨z, hz⟩ := TopCat.Sheaf.sections_exact_of_left_exact
    (R.unfactoredStep_exact (n + 1)) (R.mono_i (n + 1)) c hcR
  have hZn : (R.Z n).IsFlasque :=
    augmentedCochainSheafCycle_isFlasque F U hU n
  let _ : (R.Z n).IsFlasque := hZn
  have hp : Epi ((R.p n).hom.app (op (⊤ : Opens X))) :=
    TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := ⊤) (R.step_shortExact n)
  obtain ⟨b, hb⟩ := (AddCommGrpCat.epi_iff_surjective _).mp hp z
  refine ⟨b, ?_⟩
  have hpi : R.p n ≫ R.i (n + 1) = cochainSheafDifferential F U n := by
    simpa only [R, augmentedCochainSheafComplex, cochainSheafComplex_d] using R.p_i n
  have hpiApp := congrArg (fun f => f.hom.app (op (⊤ : Opens X))) hpi
  have hbmap := ConcreteCategory.congr_hom hpiApp b
  change (R.i (n + 1)).hom.app (op (⊤ : Opens X))
      ((R.p n).hom.app (op (⊤ : Opens X)) b) =
    (cochainSheafDifferential F U n).hom.app (op (⊤ : Opens X)) b at hbmap
  rw [hb, hz] at hbmap
  exact hbmap.symm

/-- Every positive-degree normalized Čech cocycle with values in a flasque sheaf has an actual
primitive for the normalized alternating differential. -/
theorem cocycle_boundary_of_isFlasque
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) [F.IsFlasque]
    (U : ι → Opens X) (hU : IsOpenCover U) (n : ℕ)
    (c : OrderedCech.object (A := AddCommGrpCat.{u}) (X := X)
      F.presheaf U (n + 1))
    (hc : differential (A := AddCommGrpCat.{u}) (X := X)
      F.presheaf U (n + 1) c = 0) :
    ∃ b : OrderedCech.object (A := AddCommGrpCat.{u}) (X := X) F.presheaf U n,
      differential (A := AddCommGrpCat.{u}) (X := X) F.presheaf U n b = c := by
  let e (k : ℕ) := cochainSheafGlobalSectionsIso F U k
  let c' := (e (n + 1)).inv c
  have hc' : (cochainSheafDifferential F U (n + 1)).hom.app
      (op (⊤ : Opens X)) c' = 0 := by
    apply (AddCommGrpCat.mono_iff_injective (e (n + 2)).hom).mp inferInstance
    change (e (n + 2)).hom
        ((cochainSheafDifferential F U (n + 1)).hom.app
          (op (⊤ : Opens X)) c') = (e (n + 2)).hom 0
    rw [map_zero, ← ConcreteCategory.comp_apply,
      cochainSheafDifferential_app_comp_globalSectionsIso,
      ConcreteCategory.comp_apply]
    dsimp only [c', e]
    rw [Iso.inv_hom_id_apply, hc]
  obtain ⟨b', hb'⟩ := globalCocycle_boundary F U hU n c' hc'
  refine ⟨(e n).hom b', ?_⟩
  have hd := ConcreteCategory.congr_hom
    (cochainSheafDifferential_app_comp_globalSectionsIso F U n) b'
  change (e (n + 1)).hom
      ((cochainSheafDifferential F U n).hom.app (op (⊤ : Opens X)) b') =
    differential F.presheaf U n ((e n).hom b') at hd
  rw [hb'] at hd
  dsimp only [c', e] at hd
  rw [Iso.inv_hom_id_apply] at hd
  exact hd.symm

/-- The normalized ordered Čech complex of a flasque sheaf is exact in every positive degree. -/
theorem exactAt_succ_of_isFlasque
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) [F.IsFlasque]
    (U : ι → Opens X) (hU : IsOpenCover U) (n : ℕ) :
    (complex F.presheaf U).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' (complex F.presheaf U)
      n (n + 1) (n + 2) (CochainComplex.prev_nat_succ n)
      (CochainComplex.next ℕ (n + 1)),
    ShortComplex.ab_exact_iff]
  intro c hc
  dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor'] at hc ⊢
  rw [complex_d] at hc
  obtain ⟨b, hb⟩ := cocycle_boundary_of_isFlasque F U hU n c hc
  refine ⟨b, ?_⟩
  rw [complex_d]
  exact hb

/-- Positive-degree homology of the normalized ordered Čech complex of a flasque sheaf is zero. -/
theorem homology_isZero_of_isFlasque
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) [F.IsFlasque]
    (U : ι → Opens X) (hU : IsOpenCover U) {q : ℕ} (hq : 0 < q) :
    IsZero ((complex F.presheaf U).homology q) := by
  cases q with
  | zero => omega
  | succ n =>
      exact (exactAt_succ_of_isFlasque F U hU n).isZero_homology

end TopologicalSpace.OpenCover.OrderedCech

namespace TopologicalSpace.OpenCover.SetOpenCover

open OrderedCech

variable {X : TopCat.{u}}

/-- The normalized fixed-cover Čech cohomology object of a flasque abelian sheaf is zero in every
positive degree, for an arbitrary set-valued open cover. -/
theorem normalizedCechCohomology_isZero_of_isFlasque
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) [F.IsFlasque]
    (U : SetOpenCover X) {q : ℕ} (hq : 0 < q) :
    IsZero (normalizedCechCohomology (A := AddCommGrpCat.{u})
      (X := X) F.presheaf U q) :=
  homology_isZero_of_isFlasque F U.family U.isOpenCover hq

/-- For a flasque abelian sheaf, positive-degree normalized fixed-cover Čech cohomology is a
subsingleton group for every set-valued open cover. -/
theorem normalizedCechCohomology_subsingleton_of_isFlasque
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) [F.IsFlasque]
    (U : SetOpenCover X) {q : ℕ} (hq : 0 < q) :
    Subsingleton (normalizedCechCohomology (A := AddCommGrpCat.{u})
      (X := X) F.presheaf U q) :=
  AddCommGrpCat.subsingleton_of_isZero
    (normalizedCechCohomology_isZero_of_isFlasque F U hq)

end TopologicalSpace.OpenCover.SetOpenCover
