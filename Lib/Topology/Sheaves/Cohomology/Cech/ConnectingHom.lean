/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.Cohomology.Cech.LocalLifting
public import Lib.Topology.Sheaves.Cohomology.Cech.ColimitCoefficients
public import Mathlib.Algebra.Homology.ConcreteCategory

/-!
# Connecting homomorphisms in refinement-directed Čech cohomology

This file translates reviewed textbook section CD-05H.  Its first layer constructs the
sectionwise exact normalized Čech cochain sequence and the lift--differentiate--descend
presentation underlying equation (C21).
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace TopologicalSpace.OpenCover.SetOpenCover

variable {X : TopCat.{u}}

private theorem exists_section_preimage
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (U : TopologicalSpace.Opens X)
    (b : S.X₂.presheaf.obj (op U)) (hb : S.g.hom.app (op U) b = 0) :
    ∃ a : S.X₁.presheaf.obj (op U), S.f.hom.app (op U) a = b := by
  let F := TopCat.Sheaf.forget AddCommGrpCat.{u} X
  let E :=
    (CategoryTheory.evaluation (TopologicalSpace.Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)
  let _ : Mono S.f := hS.mono_f
  have hF : (S.map F).Exact :=
    hS.exact.map_of_mono_of_preservesKernel F hS.mono_f (by infer_instance)
  let _ : Mono ((S.map F).f) := Functor.map_mono F S.f
  let _ : E.PreservesZeroMorphisms := by
    dsimp only [E]
    infer_instance
  let _ : PreservesFiniteLimits E := by
    dsimp only [E]
    infer_instance
  have hE : PreservesLimit (parallelPair (S.map F).g 0) E := by infer_instance
  have hFE : ((S.map F).map E).Exact :=
    hF.map_of_mono_of_preservesKernel E (by infer_instance) hE
  exact ((((S.map F).map E).ab_exact_iff).1 hFE b hb)

private theorem section_f_injective
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (U : TopologicalSpace.Opens X) :
    Function.Injective (S.f.hom.app (op U)) := by
  let _ : Mono S.f.hom :=
    (CategoryTheory.Sheaf.Hom.mono_iff_presheaf_mono
      (Opens.grothendieckTopology X) AddCommGrpCat S.f).mp hS.mono_f
  exact (AddCommGrpCat.mono_iff_injective _).1 (by infer_instance)

/-- The coefficient maps on normalized Čech cochains form the sectionwise short complex
attached to a short complex of abelian sheaves. -/
@[implicit_reducible]
noncomputable def cochainShortComplex
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X))
    (U : SetOpenCover X) (q : ℕ) : ShortComplex AddCommGrpCat.{u} :=
  let f : S.X₁.presheaf ⟶ S.X₂.presheaf := S.f.hom
  let g : S.X₂.presheaf ⟶ S.X₃.presheaf := S.g.hom
  ShortComplex.mk
    (OrderedCech.coefficientMapDegree
      (P := S.X₁.presheaf) (Q := S.X₂.presheaf) f U.family q)
    (OrderedCech.coefficientMapDegree
      (P := S.X₂.presheaf) (Q := S.X₃.presheaf) g U.family q) (by
      apply Limits.Pi.hom_ext
      intro σ
      dsimp only [OrderedCech.coefficientMapDegree]
      simp only [zero_comp, Category.assoc, Limits.Pi.map_π]
      have hsheaf : S.f ≫ S.g = 0 := S.zero
      have hz : f ≫ g = 0 := congrArg
        (fun k : S.X₁ ⟶ S.X₃ => k.hom) hsheaf
      rw [← Category.assoc, Limits.Pi.map_π, Category.assoc]
      rw [← NatTrans.comp_app, hz]
      simp)

/-- Exactness at the middle sheaf is inherited by every normalized fixed-cover Čech
cochain group. -/
theorem cochainShortComplex_exact
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (U : SetOpenCover X) (q : ℕ) :
    (cochainShortComplex S U q).Exact := by
  apply (ShortComplex.ab_exact_iff (cochainShortComplex S U q)).2
  intro b hb
  have hcomponent : ∀ σ : OrderedSimplex U.Index q,
      S.g.hom.app (op (σ.intersection U.family))
          (OrderedCech.π S.X₂.presheaf U.family q σ b) = 0 := by
    intro σ
    calc
      S.g.hom.app (op (σ.intersection U.family))
          (OrderedCech.π S.X₂.presheaf U.family q σ b) =
          OrderedCech.π S.X₃.presheaf U.family q σ
            (OrderedCech.coefficientMapDegree S.g.hom U.family q b) := by
        exact (ConcreteCategory.congr_hom
          (OrderedCech.coefficientMapDegree_π S.g.hom U.family q σ) b).symm
      _ = 0 := by
        rw [show OrderedCech.coefficientMapDegree S.g.hom U.family q b = 0 from hb]
        exact map_zero _
  choose a ha using fun σ : OrderedSimplex U.Index q =>
    exists_section_preimage hS (σ.intersection U.family)
      (OrderedCech.π S.X₂.presheaf U.family q σ b) (hcomponent σ)
  let lift : OrderedCech.object (A := AddCommGrpCat.{u}) (X := X)
      S.X₁.presheaf U.family q :=
    (Limits.Concrete.productEquiv
      (fun σ : OrderedSimplex U.Index q =>
        S.X₁.presheaf.obj (op (σ.intersection U.family)))).symm a
  refine ⟨lift, ?_⟩
  change OrderedCech.coefficientMapDegree S.f.hom U.family q lift = b
  apply (Limits.Concrete.productEquiv
    (fun σ : OrderedSimplex U.Index q =>
      S.X₂.presheaf.obj (op (σ.intersection U.family)))).injective
  funext σ
  conv_lhs =>
    rw [Limits.Concrete.productEquiv_apply_apply]
  conv_rhs =>
    rw [Limits.Concrete.productEquiv_apply_apply]
  calc
    OrderedCech.π S.X₂.presheaf U.family q σ
        (OrderedCech.coefficientMapDegree S.f.hom U.family q lift) =
      S.f.hom.app (op (σ.intersection U.family))
        (OrderedCech.π S.X₁.presheaf U.family q σ lift) := by
          exact ConcreteCategory.congr_hom
            (OrderedCech.coefficientMapDegree_π S.f.hom U.family q σ) lift
    _ = OrderedCech.π S.X₂.presheaf U.family q σ b := by
      rw [show OrderedCech.π S.X₁.presheaf U.family q σ lift = a σ by
        simpa only [OrderedCech.π, lift] using
          (Limits.Concrete.productEquiv_symm_apply_π
            (fun τ : OrderedSimplex U.Index q =>
              S.X₁.presheaf.obj (op (τ.intersection U.family))) a σ)]
      exact ha σ

/-- The normalized Čech cochain map induced by the left map of a short exact sequence of
abelian sheaves is injective. -/
theorem cochain_f_injective
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (U : SetOpenCover X) (q : ℕ) :
    Function.Injective
      (OrderedCech.coefficientMapDegree S.f.hom U.family q) := by
  intro a b hab
  apply (Limits.Concrete.productEquiv
    (fun σ : OrderedSimplex U.Index q =>
      S.X₁.presheaf.obj (op (σ.intersection U.family)))).injective
  funext σ
  simp only [Limits.Concrete.productEquiv_apply_apply]
  apply section_f_injective hS (σ.intersection U.family)
  calc
    S.f.hom.app (op (σ.intersection U.family))
        (OrderedCech.π S.X₁.presheaf U.family q σ a) =
      OrderedCech.π S.X₂.presheaf U.family q σ
        (OrderedCech.coefficientMapDegree S.f.hom U.family q a) := by
          exact (ConcreteCategory.congr_hom
            (OrderedCech.coefficientMapDegree_π S.f.hom U.family q σ) a).symm
    _ = OrderedCech.π S.X₂.presheaf U.family q σ
        (OrderedCech.coefficientMapDegree S.f.hom U.family q b) := by rw [hab]
    _ = S.f.hom.app (op (σ.intersection U.family))
        (OrderedCech.π S.X₁.presheaf U.family q σ b) := by
          exact ConcreteCategory.congr_hom
            (OrderedCech.coefficientMapDegree_π S.f.hom U.family q σ) b

/-! ## Concrete cocycles and their fixed-cover classes -/

/-- A concrete normalized Čech cocycle on one set-valued cover. -/
abbrev CechCocycle (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    (U : SetOpenCover X) (q : ℕ) :=
  AddMonoidHom.ker (OrderedCech.differential F U.family q).hom

/-- The concrete kernel of the displayed Čech differential is the kernel used internally by
the homology short complex. -/
noncomputable def cocycleKernelEquiv
    (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    (U : SetOpenCover X) (q : ℕ) :
    CechCocycle F U q ≃+
      AddMonoidHom.ker
        ((((normalizedCechComplex (A := AddCommGrpCat.{u}) F U).sc q).g).hom) where
  toFun c := ⟨c.1, by
    change (OrderedCech.complex F U.family).d q ((ComplexShape.up ℕ).next q) c.1 = 0
    rw [CochainComplex.next, OrderedCech.complex_d]
    exact c.2⟩
  invFun c := ⟨c.1, by
    have hc := c.2
    change (OrderedCech.complex F U.family).d q ((ComplexShape.up ℕ).next q) c.1 = 0 at hc
    rw [CochainComplex.next, OrderedCech.complex_d] at hc
    exact hc⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The fixed-cover cohomology class represented by a concrete normalized Čech cocycle. -/
def cocycleClass (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    (U : SetOpenCover X) (q : ℕ) :
    CechCocycle F U q →+
      ToType (normalizedCechCohomology (A := AddCommGrpCat.{u}) F U q) :=
  ((((normalizedCechComplex (A := AddCommGrpCat.{u}) F U).sc q).abCyclesIso.inv ≫
    ((normalizedCechComplex (A := AddCommGrpCat.{u}) F U).sc q).homologyπ).hom).comp
      (cocycleKernelEquiv F U q).toAddMonoidHom

/-! ## Lift--differentiate--descend presentations -/

/-- A lift--differentiate--descend presentation of the connecting class of one fixed-cover
cocycle. The two equations are exactly (C20) and (C21). -/
structure BoundaryPresentation
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X))
    (U : SetOpenCover X) (q : ℕ) (c : CechCocycle S.X₃.presheaf U q) where
  /-- A cover on which the cocycle lifts. -/
  cover : SetOpenCover X
  /-- The chosen refinement function to the original cover. -/
  refinement : Refinement cover.family U.family
  /-- The refined cochain lift with values in the middle sheaf. -/
  lift : OrderedCech.object (A := AddCommGrpCat.{u}) S.X₂.presheaf cover.family q
  /-- The unique left-sheaf cochain whose image is the differential of the lift. -/
  descended : OrderedCech.object (A := AddCommGrpCat.{u})
    S.X₁.presheaf cover.family (q + 1)
  /-- Equation (C20). -/
  lift_eq : OrderedCech.coefficientMapDegree S.g.hom cover.family q lift =
    OrderedCech.refinementMapDegree S.X₃.presheaf refinement q c.1
  /-- Equation (C21), with no additional sign. -/
  descended_eq : OrderedCech.coefficientMapDegree S.f.hom cover.family (q + 1) descended =
    OrderedCech.differential S.X₂.presheaf cover.family q lift

namespace BoundaryPresentation

variable {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
variable {U : SetOpenCover X} {q : ℕ} {c : CechCocycle S.X₃.presheaf U q}

/-- The cochain descended in (C21) is a cocycle: applying the injective left coefficient map
reduces its differential to `d²` of the middle-sheaf lift. -/
theorem descended_isCocycle (hS : S.ShortExact) (P : BoundaryPresentation S U q c) :
    OrderedCech.differential S.X₁.presheaf P.cover.family (q + 1) P.descended = 0 := by
  apply cochain_f_injective hS P.cover (q + 2)
  rw [map_zero]
  calc
    OrderedCech.coefficientMapDegree S.f.hom P.cover.family (q + 2)
        (OrderedCech.differential S.X₁.presheaf P.cover.family (q + 1) P.descended) =
      OrderedCech.differential S.X₂.presheaf P.cover.family (q + 1)
        (OrderedCech.coefficientMapDegree S.f.hom P.cover.family (q + 1) P.descended) := by
          exact (ConcreteCategory.congr_hom
            (OrderedCech.coefficientMapDegree_comp_differential
              S.f.hom P.cover.family (q + 1)) P.descended).symm
    _ = OrderedCech.differential S.X₂.presheaf P.cover.family (q + 1)
        (OrderedCech.differential S.X₂.presheaf P.cover.family q P.lift) := by
          rw [P.descended_eq]
    _ = 0 := by
      calc
        OrderedCech.differential S.X₂.presheaf P.cover.family (q + 1)
            (OrderedCech.differential S.X₂.presheaf P.cover.family q P.lift) =
          (OrderedCech.differential S.X₂.presheaf P.cover.family q ≫
            OrderedCech.differential S.X₂.presheaf P.cover.family (q + 1)) P.lift := by
              rw [ConcreteCategory.comp_apply]
        _ = 0 := by
          rw [OrderedCech.differential_comp_differential]
          rfl

/-- The descended cochain, viewed as the resulting concrete cocycle. -/
def descendedCocycle (hS : S.ShortExact) (P : BoundaryPresentation S U q c) :
    CechCocycle S.X₁.presheaf P.cover (q + 1) :=
  ⟨P.descended, P.descended_isCocycle hS⟩

/-- The direct-limit class furnished by a lift--differentiate--descend presentation. -/
def cechClass (hS : S.ShortExact) (P : BoundaryPresentation S U q c) :
    ToType (cechCohomology S.X₁.presheaf (q + 1)) :=
  toCechCohomology S.X₁.presheaf (q + 1) P.cover
    (cocycleClass S.X₁.presheaf P.cover (q + 1) (P.descendedCocycle hS))

end BoundaryPresentation

/-- Every fixed-cover cocycle has a lift--differentiate--descend presentation after a
refinement. -/
theorem exists_boundaryPresentation
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) (U : SetOpenCover X) (q : ℕ)
    (c : CechCocycle S.X₃.presheaf U q) :
    Nonempty (BoundaryPresentation S U q c) := by
  let _ : Epi S.g := hS.epi_g
  obtain ⟨V, r, b, hb⟩ :=
    exists_refinement_cochain_lift S.g U q c.1
  have hkernel :
      OrderedCech.coefficientMapDegree S.g.hom V.family (q + 1)
          (OrderedCech.differential S.X₂.presheaf V.family q b) = 0 := by
    calc
      OrderedCech.coefficientMapDegree S.g.hom V.family (q + 1)
          (OrderedCech.differential S.X₂.presheaf V.family q b) =
        OrderedCech.differential S.X₃.presheaf V.family q
          (OrderedCech.coefficientMapDegree S.g.hom V.family q b) := by
            exact (ConcreteCategory.congr_hom
              (OrderedCech.coefficientMapDegree_comp_differential
                S.g.hom V.family q) b).symm
      _ = OrderedCech.differential S.X₃.presheaf V.family q
          (OrderedCech.refinementMapDegree S.X₃.presheaf r q c.1) := by rw [hb]
      _ = OrderedCech.refinementMapDegree S.X₃.presheaf r (q + 1)
          (OrderedCech.differential S.X₃.presheaf U.family q c.1) := by
            exact ConcreteCategory.congr_hom
              (OrderedCech.refinementMapDegree_comp_differential
                S.X₃.presheaf r q) c.1
      _ = 0 := by rw [c.2]; exact map_zero _
  obtain ⟨a, ha⟩ :=
    ((cochainShortComplex S V (q + 1)).ab_exact_iff.1
      (cochainShortComplex_exact hS V (q + 1))
      (OrderedCech.differential S.X₂.presheaf V.family q b) hkernel)
  exact ⟨{
    cover := V
    refinement := r
    lift := b
    descended := a
    lift_eq := hb
    descended_eq := ha }⟩

/-- A fixed classical choice of lift--differentiate--descend presentation. All later formulas
are proved independent of this choice. -/
noncomputable def chosenBoundaryPresentation
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) (U : SetOpenCover X) (q : ℕ)
    (c : CechCocycle S.X₃.presheaf U q) : BoundaryPresentation S U q c :=
  Classical.choice (exists_boundaryPresentation hS U q c)

end TopologicalSpace.OpenCover.SetOpenCover
