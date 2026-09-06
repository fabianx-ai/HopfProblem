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

This file translates reviewed textbook section CD-05H. It constructs the sectionwise exact
normalized Čech cochain sequence and the lift--differentiate--descend presentation underlying
equation (C21), proves all lift, cover, refinement-function, cocycle, and direct-limit
representative choices immaterial via (C22)--(C23), and descends the resulting additive formula
to the Čech connecting homomorphism.
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

/-- A concrete cocycle represents zero exactly when it is the differential of a cochain in
the preceding object of the normalized Čech complex. -/
theorem cocycleClass_eq_zero_iff
    (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    (U : SetOpenCover X) (q : ℕ) (c : CechCocycle F U q) :
    cocycleClass F U q c = 0 ↔
      ∃ b : ((normalizedCechComplex F U).sc q).X₁,
        ((normalizedCechComplex F U).sc q).f b = c.1 := by
  let K := normalizedCechComplex (A := AddCommGrpCat.{u}) F U
  let T := K.sc q
  let c' : AddMonoidHom.ker T.g.hom := cocycleKernelEquiv F U q c
  have hclass : T.abHomologyIso.hom (cocycleClass F U q c) =
      QuotientAddGroup.mk' T.abToCycles.range c' := by
    have h : T.abCyclesIso.inv ≫ T.homologyπ ≫ T.abHomologyIso.hom =
        AddCommGrpCat.ofHom (QuotientAddGroup.mk' T.abToCycles.range) := by
      change T.abLeftHomologyData.cyclesIso.inv ≫ T.homologyπ ≫
        T.abLeftHomologyData.homologyIso.hom = T.abLeftHomologyData.π
      rw [T.abLeftHomologyData.homologyπ_comp_homologyIso_hom,
        ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    exact ConcreteCategory.congr_hom h c'
  constructor
  · intro hc
    have hq : QuotientAddGroup.mk' T.abToCycles.range c' = 0 :=
      hclass.symm.trans
        ((congrArg T.abHomologyIso.hom hc).trans T.abHomologyIso.hom.hom.map_zero)
    have hb : c' ∈ T.abToCycles.range :=
      (QuotientAddGroup.eq_zero_iff _).1 hq
    obtain ⟨b, hb⟩ := hb
    exact ⟨b, congrArg Subtype.val hb⟩
  · rintro ⟨b, hb⟩
    have hq : QuotientAddGroup.mk' T.abToCycles.range c' = 0 :=
      (QuotientAddGroup.eq_zero_iff _).2 ⟨b, Subtype.ext hb⟩
    apply (AddCommGrpCat.mono_iff_injective T.abHomologyIso.hom).1 inferInstance
    exact (hclass.trans hq).trans T.abHomologyIso.hom.hom.map_zero.symm

/-- Two positive-degree cocycles which differ by the differential of a cochain represent the
same fixed-cover cohomology class. -/
theorem cocycleClass_eq_of_sub_eq_differential
    (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    (U : SetOpenCover X) (q : ℕ) (c c' : CechCocycle F U (q + 1))
    (b : OrderedCech.object (A := AddCommGrpCat.{u}) (X := X) F U.family q)
    (h : c.1 - c'.1 = OrderedCech.differential F U.family q b) :
    cocycleClass F U (q + 1) c = cocycleClass F U (q + 1) c' := by
  rw [← sub_eq_zero, ← map_sub]
  apply (cocycleClass_eq_zero_iff F U (q + 1) (c - c')).2
  let K := normalizedCechComplex (A := AddCommGrpCat.{u}) F U
  change ∃ b' : K.X ((ComplexShape.up ℕ).prev (q + 1)),
    K.d ((ComplexShape.up ℕ).prev (q + 1)) (q + 1) b' = c.1 - c'.1
  rw [CochainComplex.prev_nat_succ]
  refine ⟨b, ?_⟩
  simpa only [K, normalizedCechComplex, OrderedCech.complex_d] using h.symm

/-- Pullback of concrete cocycles along a chosen refinement. -/
def refineCocycle (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    {U V : SetOpenCover X} (r : Refinement V.family U.family) (q : ℕ) :
    CechCocycle F U q →+ CechCocycle F V q where
  toFun c := ⟨OrderedCech.refinementMapDegree F r q c.1, by
    have hcomm := OrderedCech.refinementMapDegree_comp_differential F r q
    calc
      OrderedCech.differential F V.family q
          (OrderedCech.refinementMapDegree F r q c.1) =
        OrderedCech.refinementMapDegree F r (q + 1)
          (OrderedCech.differential F U.family q c.1) := by
            exact ConcreteCategory.congr_hom hcomm c.1
      _ = 0 := by rw [c.2]; exact map_zero _⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero _
  map_add' c c' := by
    apply Subtype.ext
    exact map_add _ _ _

/-- Refinement sends the class of a concrete cocycle to the class of its literal pullback. -/
theorem homologyMap_cocycleClass
    (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    {U V : SetOpenCover X} (r : Refinement V.family U.family) (q : ℕ)
    (c : CechCocycle F U q) :
    HomologicalComplex.homologyMap (OrderedCech.refinementMap F r) q
        (cocycleClass F U q c) =
      cocycleClass F V q (refineCocycle F r q c) := by
  let K := normalizedCechComplex (A := AddCommGrpCat.{u}) F U
  let L := normalizedCechComplex (A := AddCommGrpCat.{u}) F V
  let φ : K ⟶ L := OrderedCech.refinementMap F r
  let ψ := (HomologicalComplex.shortComplexFunctor AddCommGrpCat.{u}
    (ComplexShape.up ℕ) q).map φ
  let z := cocycleKernelEquiv F U q c
  let w := cocycleKernelEquiv F V q (refineCocycle F r q c)
  have hcycles : ShortComplex.cyclesMap ψ ((K.sc q).abCyclesIso.inv z) =
      (L.sc q).abCyclesIso.inv w := by
    apply (AddCommGrpCat.mono_iff_injective (L.sc q).iCycles).1 inferInstance
    rw [← ConcreteCategory.comp_apply, ShortComplex.cyclesMap_i,
      ConcreteCategory.comp_apply, (K.sc q).abCyclesIso_inv_apply_iCycles,
      (L.sc q).abCyclesIso_inv_apply_iCycles]
    rfl
  change ShortComplex.homologyMap ψ
      ((K.sc q).homologyπ ((K.sc q).abCyclesIso.inv z)) =
    (L.sc q).homologyπ ((L.sc q).abCyclesIso.inv w)
  rw [← ConcreteCategory.comp_apply, ShortComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply, hcycles]

/-- The thin-cover transition map has the same concrete-cocycle formula for any chosen
refinement function witnessing it. -/
theorem normalizedCechCohomologyMap_cocycleClass
    (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    {U V : SetOpenCover X} (h : U ≤ V)
    (r : Refinement V.family U.family) (q : ℕ) (c : CechCocycle F U q) :
    normalizedCechCohomologyMap F h q (cocycleClass F U q c) =
      cocycleClass F V q (refineCocycle F r q c) := by
  rw [normalizedCechCohomologyMap_eq F h r q]
  exact homologyMap_cocycleClass F r q c

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

private structure BoundaryData
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X))
    (U V : SetOpenCover X) (q : ℕ) (c : CechCocycle S.X₃.presheaf U q) where
  refinement : Refinement V.family U.family
  lift : OrderedCech.object (A := AddCommGrpCat.{u}) S.X₂.presheaf V.family q
  descended : OrderedCech.object (A := AddCommGrpCat.{u}) S.X₁.presheaf V.family (q + 1)
  lift_eq : OrderedCech.coefficientMapDegree S.g.hom V.family q lift =
    OrderedCech.refinementMapDegree S.X₃.presheaf refinement q c.1
  descended_eq : OrderedCech.coefficientMapDegree S.f.hom V.family (q + 1) descended =
    OrderedCech.differential S.X₂.presheaf V.family q lift

private def BoundaryData.toPresentation
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    {U V : SetOpenCover X} {q : ℕ} {c : CechCocycle S.X₃.presheaf U q}
    (D : BoundaryData S U V q c) : BoundaryPresentation S U q c where
  cover := V
  refinement := D.refinement
  lift := D.lift
  descended := D.descended
  lift_eq := D.lift_eq
  descended_eq := D.descended_eq

private def BoundaryPresentation.toData
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    {U : SetOpenCover X} {q : ℕ} {c : CechCocycle S.X₃.presheaf U q}
    (P : BoundaryPresentation S U q c) : BoundaryData S U P.cover q c where
  refinement := P.refinement
  lift := P.lift
  descended := P.descended
  lift_eq := P.lift_eq
  descended_eq := P.descended_eq

namespace BoundaryPresentation

variable {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
variable {U : SetOpenCover X} {q : ℕ} {c : CechCocycle S.X₃.presheaf U q}

private theorem coefficient_refinement_apply
    {P Q : TopCat.Presheaf AddCommGrpCat.{u} X}
    {V W : SetOpenCover X} (f : P ⟶ Q)
    (r : Refinement W.family V.family) (n : ℕ)
    (x : OrderedCech.object (A := AddCommGrpCat.{u}) P V.family n) :
    OrderedCech.coefficientMapDegree f W.family n
        (OrderedCech.refinementMapDegree P r n x) =
      OrderedCech.refinementMapDegree Q r n
        (OrderedCech.coefficientMapDegree f V.family n x) := by
  have h := congrArg (fun k => k.f n)
    (OrderedCech.coefficientMap_comp_refinementMap f r)
  exact (ConcreteCategory.congr_hom h x).symm

private theorem refinement_comp_apply
    (P : TopCat.Presheaf AddCommGrpCat.{u} X)
    {V W Z : SetOpenCover X}
    (r : Refinement W.family V.family) (s : Refinement Z.family W.family)
    (n : ℕ) (x : OrderedCech.object (A := AddCommGrpCat.{u}) P V.family n) :
    OrderedCech.refinementMapDegree P (r.comp s) n x =
      OrderedCech.refinementMapDegree P s n
        (OrderedCech.refinementMapDegree P r n x) := by
  have h := congrArg (fun k => k.f n) (OrderedCech.refinementMap_comp P r s)
  exact ConcreteCategory.congr_hom h x

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

/-- Pulling every cochain in a boundary presentation to a further refinement gives another
presentation of the same original cocycle. -/
def refine (P : BoundaryPresentation S U q c)
    (W : SetOpenCover X) (s : Refinement W.family P.cover.family) :
    BoundaryPresentation S U q c where
  cover := W
  refinement := P.refinement.comp s
  lift := OrderedCech.refinementMapDegree S.X₂.presheaf s q P.lift
  descended := OrderedCech.refinementMapDegree S.X₁.presheaf s (q + 1) P.descended
  lift_eq := by
    calc
      OrderedCech.coefficientMapDegree S.g.hom W.family q
          (OrderedCech.refinementMapDegree S.X₂.presheaf s q P.lift) =
        OrderedCech.refinementMapDegree S.X₃.presheaf s q
          (OrderedCech.coefficientMapDegree S.g.hom P.cover.family q P.lift) :=
            coefficient_refinement_apply S.g.hom s q P.lift
      _ = OrderedCech.refinementMapDegree S.X₃.presheaf s q
          (OrderedCech.refinementMapDegree S.X₃.presheaf P.refinement q c.1) := by
            rw [P.lift_eq]
      _ = OrderedCech.refinementMapDegree S.X₃.presheaf (P.refinement.comp s) q c.1 :=
            (refinement_comp_apply S.X₃.presheaf P.refinement s q c.1).symm
  descended_eq := by
    calc
      OrderedCech.coefficientMapDegree S.f.hom W.family (q + 1)
          (OrderedCech.refinementMapDegree S.X₁.presheaf s (q + 1) P.descended) =
        OrderedCech.refinementMapDegree S.X₂.presheaf s (q + 1)
          (OrderedCech.coefficientMapDegree S.f.hom P.cover.family (q + 1) P.descended) :=
            coefficient_refinement_apply S.f.hom s (q + 1) P.descended
      _ = OrderedCech.refinementMapDegree S.X₂.presheaf s (q + 1)
          (OrderedCech.differential S.X₂.presheaf P.cover.family q P.lift) := by
            rw [P.descended_eq]
      _ = OrderedCech.differential S.X₂.presheaf W.family q
          (OrderedCech.refinementMapDegree S.X₂.presheaf s q P.lift) := by
            exact (ConcreteCategory.congr_hom
              (OrderedCech.refinementMapDegree_comp_differential
                S.X₂.presheaf s q) P.lift).symm

@[simp]
theorem refine_descendedCocycle (hS : S.ShortExact)
    (P : BoundaryPresentation S U q c)
    (W : SetOpenCover X) (s : Refinement W.family P.cover.family) :
    (P.refine W s).descendedCocycle hS =
      refineCocycle S.X₁.presheaf s (q + 1) (P.descendedCocycle hS) := by
  apply Subtype.ext
  rfl

/-- Further refinement does not change the direct-limit class of a boundary presentation. -/
theorem cechClass_refine (hS : S.ShortExact)
    (P : BoundaryPresentation S U q c)
    (W : SetOpenCover X) (s : Refinement W.family P.cover.family) :
    (P.refine W s).cechClass hS = P.cechClass hS := by
  let h : P.cover ≤ W := ⟨s⟩
  calc
    (P.refine W s).cechClass hS =
        toCechCohomology S.X₁.presheaf (q + 1) W
          (normalizedCechCohomologyMap S.X₁.presheaf h (q + 1)
            (cocycleClass S.X₁.presheaf P.cover (q + 1)
              (P.descendedCocycle hS))) := by
      rw [normalizedCechCohomologyMap_cocycleClass
        S.X₁.presheaf h s (q + 1) (P.descendedCocycle hS)]
      rfl
    _ = P.cechClass hS := by
      simpa only [ConcreteCategory.comp_apply, cechClass] using ConcreteCategory.congr_hom
        (normalizedCechCohomologyMap_comp_toCechCohomology
          S.X₁.presheaf (q + 1) h)
        (cocycleClass S.X₁.presheaf P.cover (q + 1)
          (P.descendedCocycle hS))

private theorem exists_descended_sub_eq_differential
    (hS : S.ShortExact) {V : SetOpenCover X}
    (D₁ D₂ : BoundaryData S U V q c)
    (z : OrderedCech.object (A := AddCommGrpCat.{u}) S.X₂.presheaf V.family q)
    (hkernel : OrderedCech.coefficientMapDegree S.g.hom V.family q
      (D₂.lift - D₁.lift - z) = 0)
    (hz : OrderedCech.differential S.X₂.presheaf V.family q z = 0) :
    ∃ e : OrderedCech.object (A := AddCommGrpCat.{u}) S.X₁.presheaf V.family q,
      D₂.descended - D₁.descended =
        OrderedCech.differential S.X₁.presheaf V.family q e := by
  obtain ⟨e, he⟩ :=
    ((cochainShortComplex S V q).ab_exact_iff.1
      (cochainShortComplex_exact hS V q) (D₂.lift - D₁.lift - z) hkernel)
  change OrderedCech.coefficientMapDegree S.f.hom V.family q e =
    D₂.lift - D₁.lift - z at he
  refine ⟨e, ?_⟩
  apply cochain_f_injective hS V (q + 1)
  calc
    OrderedCech.coefficientMapDegree S.f.hom V.family (q + 1)
        (D₂.descended - D₁.descended) =
      OrderedCech.coefficientMapDegree S.f.hom V.family (q + 1) D₂.descended -
        OrderedCech.coefficientMapDegree S.f.hom V.family (q + 1) D₁.descended :=
          map_sub _ _ _
    _ = OrderedCech.differential S.X₂.presheaf V.family q D₂.lift -
        OrderedCech.differential S.X₂.presheaf V.family q D₁.lift := by
          rw [D₂.descended_eq, D₁.descended_eq]
    _ = OrderedCech.differential S.X₂.presheaf V.family q
        (D₂.lift - D₁.lift - z) := by
          simp only [map_sub, hz, sub_zero]
    _ = OrderedCech.differential S.X₂.presheaf V.family q
        (OrderedCech.coefficientMapDegree S.f.hom V.family q e) := by rw [he]
    _ = OrderedCech.coefficientMapDegree S.f.hom V.family (q + 1)
        (OrderedCech.differential S.X₁.presheaf V.family q e) := by
          exact ConcreteCategory.congr_hom
            (OrderedCech.coefficientMapDegree_comp_differential
              S.f.hom V.family q) e

private theorem boundaryData_cechClass_eq_zero_degree
    (hS : S.ShortExact) {V : SetOpenCover X}
    (c : CechCocycle S.X₃.presheaf U 0)
    (D₁ D₂ : BoundaryData S U V 0 c) :
    D₁.toPresentation.cechClass hS = D₂.toPresentation.cechClass hS := by
  have hprism := ConcreteCategory.congr_hom
    (OrderedCech.differential_comp_refinementPrismDegree_zero
      S.X₃.presheaf D₁.refinement D₂.refinement) c.1
  have hprism' :
      OrderedCech.refinementPrismDegree S.X₃.presheaf
          D₁.refinement D₂.refinement 0
          (OrderedCech.differential S.X₃.presheaf U.family 0 c.1) =
        OrderedCech.refinementMapDegree S.X₃.presheaf D₂.refinement 0 c.1 -
          OrderedCech.refinementMapDegree S.X₃.presheaf D₁.refinement 0 c.1 := by
    simpa only [ConcreteCategory.comp_apply, AddCommGrpCat.hom_sub,
      AddMonoidHom.sub_apply] using hprism
  have hrefine :
      OrderedCech.refinementMapDegree S.X₃.presheaf D₂.refinement 0 c.1 =
        OrderedCech.refinementMapDegree S.X₃.presheaf D₁.refinement 0 c.1 := by
    rw [c.2, map_zero] at hprism'
    exact sub_eq_zero.1 hprism'.symm
  have hkernel : OrderedCech.coefficientMapDegree S.g.hom V.family 0
      (D₂.lift - D₁.lift - 0) = 0 := by
    simp only [sub_zero, map_sub, D₂.lift_eq, D₁.lift_eq, hrefine, sub_self]
  obtain ⟨e, he⟩ := exists_descended_sub_eq_differential hS D₁ D₂ 0 hkernel (map_zero _)
  have hclass := cocycleClass_eq_of_sub_eq_differential
    S.X₁.presheaf V 0
    (D₂.toPresentation.descendedCocycle hS)
    (D₁.toPresentation.descendedCocycle hS) e he
  exact congrArg (toCechCohomology S.X₁.presheaf 1 V) hclass.symm

private theorem boundaryData_cechClass_eq_succ
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) {V : SetOpenCover X} (n : ℕ)
    (c : CechCocycle S.X₃.presheaf U (n + 1))
    (D₁ D₂ : BoundaryData S U V (n + 1) c) :
    D₁.toPresentation.cechClass hS = D₂.toPresentation.cechClass hS := by
  let k : OrderedCech.object (A := AddCommGrpCat.{u}) S.X₃.presheaf V.family n :=
    OrderedCech.refinementPrismDegree S.X₃.presheaf
      D₁.refinement D₂.refinement n c.1
  have hprism0 := ConcreteCategory.congr_hom
    (OrderedCech.differential_comp_refinementPrismDegree_succ
      S.X₃.presheaf D₁.refinement D₂.refinement n) c.1
  have hprism :
      OrderedCech.refinementPrismDegree S.X₃.presheaf
          D₁.refinement D₂.refinement (n + 1)
          (OrderedCech.differential S.X₃.presheaf U.family (n + 1) c.1) +
        OrderedCech.differential S.X₃.presheaf V.family n k =
      OrderedCech.refinementMapDegree S.X₃.presheaf D₂.refinement (n + 1) c.1 -
        OrderedCech.refinementMapDegree S.X₃.presheaf D₁.refinement (n + 1) c.1 := by
    simpa only [ConcreteCategory.comp_apply, AddCommGrpCat.hom_add,
      AddCommGrpCat.hom_sub, AddMonoidHom.add_apply, AddMonoidHom.sub_apply, k] using hprism0
  rw [c.2, map_zero, zero_add] at hprism
  let _ : Epi S.g := hS.epi_g
  obtain ⟨W, s, t, ht⟩ :=
    exists_refinement_cochain_lift S.g V n k
  let P₁ := D₁.toPresentation
  let P₂ := D₂.toPresentation
  let Q₁ := P₁.refine W s
  let Q₂ := P₂.refine W s
  let E₁ : BoundaryData S U W (n + 1) c := Q₁.toData
  let E₂ : BoundaryData S U W (n + 1) c := Q₂.toData
  have hE₁lift :
      OrderedCech.coefficientMapDegree S.g.hom W.family (n + 1) E₁.lift =
        OrderedCech.refinementMapDegree S.X₃.presheaf s (n + 1)
          (OrderedCech.refinementMapDegree S.X₃.presheaf D₁.refinement (n + 1) c.1) := by
    change OrderedCech.coefficientMapDegree S.g.hom W.family (n + 1)
        (OrderedCech.refinementMapDegree S.X₂.presheaf s (n + 1) D₁.lift) = _
    calc
      _ = OrderedCech.refinementMapDegree S.X₃.presheaf s (n + 1)
          (OrderedCech.coefficientMapDegree S.g.hom V.family (n + 1) D₁.lift) :=
            coefficient_refinement_apply S.g.hom s (n + 1) D₁.lift
      _ = _ := by rw [D₁.lift_eq]
  have hE₂lift :
      OrderedCech.coefficientMapDegree S.g.hom W.family (n + 1) E₂.lift =
        OrderedCech.refinementMapDegree S.X₃.presheaf s (n + 1)
          (OrderedCech.refinementMapDegree S.X₃.presheaf D₂.refinement (n + 1) c.1) := by
    change OrderedCech.coefficientMapDegree S.g.hom W.family (n + 1)
        (OrderedCech.refinementMapDegree S.X₂.presheaf s (n + 1) D₂.lift) = _
    calc
      _ = OrderedCech.refinementMapDegree S.X₃.presheaf s (n + 1)
          (OrderedCech.coefficientMapDegree S.g.hom V.family (n + 1) D₂.lift) :=
            coefficient_refinement_apply S.g.hom s (n + 1) D₂.lift
      _ = _ := by rw [D₂.lift_eq]
  have hdt :
      OrderedCech.coefficientMapDegree S.g.hom W.family (n + 1)
          (OrderedCech.differential S.X₂.presheaf W.family n t) =
        OrderedCech.differential S.X₃.presheaf W.family n
          (OrderedCech.refinementMapDegree S.X₃.presheaf s n k) := by
    calc
      _ = OrderedCech.differential S.X₃.presheaf W.family n
          (OrderedCech.coefficientMapDegree S.g.hom W.family n t) := by
            exact (ConcreteCategory.congr_hom
              (OrderedCech.coefficientMapDegree_comp_differential
                S.g.hom W.family n) t).symm
      _ = _ := by rw [ht]
  have hpull :
      OrderedCech.refinementMapDegree S.X₃.presheaf s (n + 1)
          (OrderedCech.refinementMapDegree S.X₃.presheaf D₂.refinement (n + 1) c.1) -
        OrderedCech.refinementMapDegree S.X₃.presheaf s (n + 1)
          (OrderedCech.refinementMapDegree S.X₃.presheaf D₁.refinement (n + 1) c.1) =
      OrderedCech.differential S.X₃.presheaf W.family n
        (OrderedCech.refinementMapDegree S.X₃.presheaf s n k) := by
    calc
      _ = OrderedCech.refinementMapDegree S.X₃.presheaf s (n + 1)
          (OrderedCech.refinementMapDegree S.X₃.presheaf D₂.refinement (n + 1) c.1 -
            OrderedCech.refinementMapDegree S.X₃.presheaf D₁.refinement (n + 1) c.1) := by
              rw [map_sub]
      _ = OrderedCech.refinementMapDegree S.X₃.presheaf s (n + 1)
          (OrderedCech.differential S.X₃.presheaf V.family n k) := by rw [← hprism]
      _ = _ := by
        exact (ConcreteCategory.congr_hom
          (OrderedCech.refinementMapDegree_comp_differential
            S.X₃.presheaf s n) k).symm
  have hkernel : OrderedCech.coefficientMapDegree S.g.hom W.family (n + 1)
      (E₂.lift - E₁.lift -
        OrderedCech.differential S.X₂.presheaf W.family n t) = 0 := by
    rw [map_sub, map_sub, hE₂lift, hE₁lift, hdt, hpull, sub_self]
  have hz : OrderedCech.differential S.X₂.presheaf W.family (n + 1)
      (OrderedCech.differential S.X₂.presheaf W.family n t) = 0 := by
    calc
      _ = (OrderedCech.differential S.X₂.presheaf W.family n ≫
          OrderedCech.differential S.X₂.presheaf W.family (n + 1)) t := by
            rw [ConcreteCategory.comp_apply]
      _ = 0 := by
        rw [OrderedCech.differential_comp_differential]
        rfl
  obtain ⟨e, he⟩ := exists_descended_sub_eq_differential hS E₁ E₂
    (OrderedCech.differential S.X₂.presheaf W.family n t) hkernel hz
  have hfixed := cocycleClass_eq_of_sub_eq_differential
    S.X₁.presheaf W (n + 1)
    (E₂.toPresentation.descendedCocycle hS)
    (E₁.toPresentation.descendedCocycle hS) e he
  have hsame : E₁.toPresentation.cechClass hS = E₂.toPresentation.cechClass hS :=
    congrArg (toCechCohomology S.X₁.presheaf (n + 2) W) hfixed.symm
  calc
    D₁.toPresentation.cechClass hS = Q₁.cechClass hS :=
      (BoundaryPresentation.cechClass_refine hS P₁ W s).symm
    _ = E₁.toPresentation.cechClass hS := by rfl
    _ = E₂.toPresentation.cechClass hS := hsame
    _ = Q₂.cechClass hS := by rfl
    _ = D₂.toPresentation.cechClass hS :=
      BoundaryPresentation.cechClass_refine hS P₂ W s

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

namespace BoundaryPresentation

variable {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
variable {U : SetOpenCover X} {q : ℕ} {c : CechCocycle S.X₃.presheaf U q}

/-- Any two lift--differentiate--descend presentations of the same fixed-cover cocycle give
the same direct-limit class. This includes independence of the lift, refined cover, and chosen
refinement function; the proof uses the prism identity in positive degree and the separate
degree-zero equality. -/
theorem cechClass_eq [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) (P Q : BoundaryPresentation S U q c) :
    P.cechClass hS = Q.cechClass hS := by
  let W := commonRefinement P.cover Q.cover
  let r : Refinement W.family P.cover.family := commonRefinementLeft P.cover Q.cover
  let s : Refinement W.family Q.cover.family := commonRefinementRight P.cover Q.cover
  let P' := P.refine W r
  let Q' := Q.refine W s
  have hsame : P'.cechClass hS = Q'.cechClass hS := by
    cases q with
    | zero =>
        exact boundaryData_cechClass_eq_zero_degree hS c P'.toData Q'.toData
    | succ n =>
        exact boundaryData_cechClass_eq_succ hS n c P'.toData Q'.toData
  calc
    P.cechClass hS = P'.cechClass hS := (P.cechClass_refine hS W r).symm
    _ = Q'.cechClass hS := hsame
    _ = Q.cechClass hS := Q.cechClass_refine hS W s

end BoundaryPresentation

/-- The connecting class of a concrete fixed-cover cocycle, defined by one chosen
lift--differentiate--descend presentation. -/
noncomputable def boundaryClass
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) (U : SetOpenCover X) (q : ℕ)
    (c : CechCocycle S.X₃.presheaf U q) :
    ToType (cechCohomology S.X₁.presheaf (q + 1)) :=
  (chosenBoundaryPresentation hS U q c).cechClass hS

/-- Fixed-cover representative formula: every valid lift--differentiate--descend presentation
computes the chosen connecting class. -/
theorem boundaryClass_eq_cechClass
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) (U : SetOpenCover X) (q : ℕ)
    (c : CechCocycle S.X₃.presheaf U q)
    (P : BoundaryPresentation S U q c) :
    boundaryClass hS U q c = P.cechClass hS :=
  BoundaryPresentation.cechClass_eq hS (chosenBoundaryPresentation hS U q c) P

/-- The connecting class of the zero cocycle is zero. -/
@[simp]
theorem boundaryClass_zero
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) (U : SetOpenCover X) (q : ℕ) :
    boundaryClass hS U q 0 = 0 := by
  let P : BoundaryPresentation S U q 0 :=
    { cover := U
      refinement := Refinement.refl U.family
      lift := 0
      descended := 0
      lift_eq := by simp
      descended_eq := by simp }
  rw [boundaryClass_eq_cechClass hS U q 0 P]
  change toCechCohomology S.X₁.presheaf (q + 1) U
    (cocycleClass S.X₁.presheaf U (q + 1) (P.descendedCocycle hS)) = 0
  have hz : P.descendedCocycle hS = 0 := by
    apply Subtype.ext
    rfl
  rw [hz, map_zero, map_zero]

private theorem lift_differential_in_kernel
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    {U V : SetOpenCover X} {q : ℕ}
    (c : CechCocycle S.X₃.presheaf U q)
    (r : Refinement V.family U.family)
    (b : OrderedCech.object (A := AddCommGrpCat.{u}) S.X₂.presheaf V.family q)
    (hb : OrderedCech.coefficientMapDegree S.g.hom V.family q b =
      OrderedCech.refinementMapDegree S.X₃.presheaf r q c.1) :
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

private noncomputable def boundaryDataOfLift
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) {U V : SetOpenCover X} {q : ℕ}
    (c : CechCocycle S.X₃.presheaf U q)
    (r : Refinement V.family U.family)
    (b : OrderedCech.object (A := AddCommGrpCat.{u}) S.X₂.presheaf V.family q)
    (hb : OrderedCech.coefficientMapDegree S.g.hom V.family q b =
      OrderedCech.refinementMapDegree S.X₃.presheaf r q c.1) :
    BoundaryData S U V q c := by
  let hkernel := lift_differential_in_kernel c r b hb
  let hexists :=
    ((cochainShortComplex S V (q + 1)).ab_exact_iff.1
      (cochainShortComplex_exact hS V (q + 1))
      (OrderedCech.differential S.X₂.presheaf V.family q b) hkernel)
  exact
    { refinement := r
      lift := b
      descended := Classical.choose hexists
      lift_eq := hb
      descended_eq := Classical.choose_spec hexists }

/-- The connecting class is additive on concrete cocycles. The proof first refines twice so
that both cocycles have lifts for one common refinement function, then adds equations (C20)
and (C21) on that cover. -/
theorem boundaryClass_add
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) (U : SetOpenCover X) (q : ℕ)
    (c₁ c₂ : CechCocycle S.X₃.presheaf U q) :
    boundaryClass hS U q (c₁ + c₂) =
      boundaryClass hS U q c₁ + boundaryClass hS U q c₂ := by
  let _ : Epi S.g := hS.epi_g
  obtain ⟨V, r, b₁V, hb₁V⟩ :=
    exists_refinement_cochain_lift S.g U q c₁.1
  let c₂V : CechCocycle S.X₃.presheaf V q :=
    refineCocycle S.X₃.presheaf r q c₂
  obtain ⟨W, s, b₂, hb₂raw⟩ :=
    exists_refinement_cochain_lift S.g V q c₂V.1
  let r' : Refinement W.family U.family := r.comp s
  let b₁ : OrderedCech.object (A := AddCommGrpCat.{u})
      S.X₂.presheaf W.family q :=
    OrderedCech.refinementMapDegree S.X₂.presheaf s q b₁V
  have hb₁ : OrderedCech.coefficientMapDegree S.g.hom W.family q b₁ =
      OrderedCech.refinementMapDegree S.X₃.presheaf r' q c₁.1 := by
    calc
      _ = OrderedCech.refinementMapDegree S.X₃.presheaf s q
          (OrderedCech.coefficientMapDegree S.g.hom V.family q b₁V) :=
            BoundaryPresentation.coefficient_refinement_apply S.g.hom s q b₁V
      _ = OrderedCech.refinementMapDegree S.X₃.presheaf s q
          (OrderedCech.refinementMapDegree S.X₃.presheaf r q c₁.1) := by rw [hb₁V]
      _ = _ := (BoundaryPresentation.refinement_comp_apply
        S.X₃.presheaf r s q c₁.1).symm
  have hb₂ : OrderedCech.coefficientMapDegree S.g.hom W.family q b₂ =
      OrderedCech.refinementMapDegree S.X₃.presheaf r' q c₂.1 := by
    calc
      _ = OrderedCech.refinementMapDegree S.X₃.presheaf s q c₂V.1 := hb₂raw
      _ = OrderedCech.refinementMapDegree S.X₃.presheaf s q
          (OrderedCech.refinementMapDegree S.X₃.presheaf r q c₂.1) := by rfl
      _ = _ := (BoundaryPresentation.refinement_comp_apply
        S.X₃.presheaf r s q c₂.1).symm
  let D₁ : BoundaryData S U W q c₁ := boundaryDataOfLift hS c₁ r' b₁ hb₁
  let D₂ : BoundaryData S U W q c₂ := boundaryDataOfLift hS c₂ r' b₂ hb₂
  let Dsum : BoundaryData S U W q (c₁ + c₂) :=
    { refinement := r'
      lift := b₁ + b₂
      descended := D₁.descended + D₂.descended
      lift_eq := by
        calc
          OrderedCech.coefficientMapDegree S.g.hom W.family q (b₁ + b₂) =
            OrderedCech.coefficientMapDegree S.g.hom W.family q b₁ +
              OrderedCech.coefficientMapDegree S.g.hom W.family q b₂ := map_add _ _ _
          _ = OrderedCech.refinementMapDegree S.X₃.presheaf r' q c₁.1 +
              OrderedCech.refinementMapDegree S.X₃.presheaf r' q c₂.1 := by
                rw [hb₁, hb₂]
          _ = OrderedCech.refinementMapDegree S.X₃.presheaf r' q (c₁.1 + c₂.1) :=
                (map_add _ _ _).symm
          _ = OrderedCech.refinementMapDegree S.X₃.presheaf r' q (c₁ + c₂).1 := rfl
      descended_eq := by
        calc
          OrderedCech.coefficientMapDegree S.f.hom W.family (q + 1)
              (D₁.descended + D₂.descended) =
            OrderedCech.coefficientMapDegree S.f.hom W.family (q + 1) D₁.descended +
              OrderedCech.coefficientMapDegree S.f.hom W.family (q + 1) D₂.descended :=
                map_add _ _ _
          _ = OrderedCech.differential S.X₂.presheaf W.family q D₁.lift +
              OrderedCech.differential S.X₂.presheaf W.family q D₂.lift := by
                rw [D₁.descended_eq, D₂.descended_eq]
          _ = OrderedCech.differential S.X₂.presheaf W.family q (b₁ + b₂) := by
                change _ = OrderedCech.differential S.X₂.presheaf W.family q
                  (D₁.lift + D₂.lift)
                exact (map_add _ _ _).symm }
  rw [boundaryClass_eq_cechClass hS U q (c₁ + c₂) Dsum.toPresentation,
    boundaryClass_eq_cechClass hS U q c₁ D₁.toPresentation,
    boundaryClass_eq_cechClass hS U q c₂ D₂.toPresentation]
  let zsum : CechCocycle S.X₁.presheaf W (q + 1) :=
    Dsum.toPresentation.descendedCocycle hS
  let z₁ : CechCocycle S.X₁.presheaf W (q + 1) :=
    D₁.toPresentation.descendedCocycle hS
  let z₂ : CechCocycle S.X₁.presheaf W (q + 1) :=
    D₂.toPresentation.descendedCocycle hS
  have hdesc : zsum = z₁ + z₂ := by
    apply Subtype.ext
    rfl
  change toCechCohomology S.X₁.presheaf (q + 1) W
      (cocycleClass S.X₁.presheaf W (q + 1) zsum) =
    toCechCohomology S.X₁.presheaf (q + 1) W
        (cocycleClass S.X₁.presheaf W (q + 1) z₁) +
      toCechCohomology S.X₁.presheaf (q + 1) W
        (cocycleClass S.X₁.presheaf W (q + 1) z₂)
  rw [hdesc, map_add, map_add]

/-- The additive map on concrete cocycles defined by lift--differentiate--descend. -/
noncomputable def boundaryCocycleMap
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) (U : SetOpenCover X) (q : ℕ) :
    CechCocycle S.X₃.presheaf U q →+
      ToType (cechCohomology S.X₁.presheaf (q + 1)) where
  toFun := boundaryClass hS U q
  map_zero' := boundaryClass_zero hS U q
  map_add' := boundaryClass_add hS U q

@[simp]
theorem boundaryCocycleMap_apply
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) (U : SetOpenCover X) (q : ℕ)
    (c : CechCocycle S.X₃.presheaf U q) :
    boundaryCocycleMap hS U q c = boundaryClass hS U q c := rfl

namespace BoundaryPresentation

variable {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}

/-- A presentation of the pullback of a cocycle along `r` is also a presentation of the
original cocycle, after composing its refinement function with `r`. -/
def ofRefinedCocycle {U V : SetOpenCover X}
    (r : Refinement V.family U.family) (q : ℕ)
    (c : CechCocycle S.X₃.presheaf U q)
    (P : BoundaryPresentation S V q (refineCocycle S.X₃.presheaf r q c)) :
    BoundaryPresentation S U q c where
  cover := P.cover
  refinement := r.comp P.refinement
  lift := P.lift
  descended := P.descended
  lift_eq := by
    calc
      OrderedCech.coefficientMapDegree S.g.hom P.cover.family q P.lift =
        OrderedCech.refinementMapDegree S.X₃.presheaf P.refinement q
          (refineCocycle S.X₃.presheaf r q c).1 := P.lift_eq
      _ = OrderedCech.refinementMapDegree S.X₃.presheaf P.refinement q
          (OrderedCech.refinementMapDegree S.X₃.presheaf r q c.1) := rfl
      _ = OrderedCech.refinementMapDegree S.X₃.presheaf
          (r.comp P.refinement) q c.1 :=
            (refinement_comp_apply S.X₃.presheaf r P.refinement q c.1).symm
  descended_eq := P.descended_eq

@[simp]
theorem ofRefinedCocycle_cechClass {U V : SetOpenCover X}
    (hS : S.ShortExact) (r : Refinement V.family U.family) (q : ℕ)
    (c : CechCocycle S.X₃.presheaf U q)
    (P : BoundaryPresentation S V q (refineCocycle S.X₃.presheaf r q c)) :
    (P.ofRefinedCocycle r q c).cechClass hS = P.cechClass hS := rfl

end BoundaryPresentation

/-- Pulling a concrete cocycle to a refinement does not change its connecting class. -/
theorem boundaryClass_refine
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) {U V : SetOpenCover X}
    (r : Refinement V.family U.family) (q : ℕ)
    (c : CechCocycle S.X₃.presheaf U q) :
    boundaryClass hS V q (refineCocycle S.X₃.presheaf r q c) =
      boundaryClass hS U q c := by
  let P := chosenBoundaryPresentation hS V q (refineCocycle S.X₃.presheaf r q c)
  calc
    boundaryClass hS V q (refineCocycle S.X₃.presheaf r q c) = P.cechClass hS :=
      boundaryClass_eq_cechClass hS V q _ P
    _ = (P.ofRefinedCocycle r q c).cechClass hS :=
      (P.ofRefinedCocycle_cechClass hS r q c).symm
    _ = boundaryClass hS U q c :=
      (boundaryClass_eq_cechClass hS U q c (P.ofRefinedCocycle r q c)).symm

/-- A positive-degree cocycle which is literally a Čech coboundary has zero connecting class.
The primitive is refined and lifted; its differential is then a lift whose descended cochain is
zero by `d² = 0`. -/
theorem boundaryClass_eq_zero_of_eq_differential
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) (U : SetOpenCover X) (q : ℕ)
    (c : CechCocycle S.X₃.presheaf U (q + 1))
    (z : OrderedCech.object (A := AddCommGrpCat.{u})
      S.X₃.presheaf U.family q)
    (hc : c.1 = OrderedCech.differential S.X₃.presheaf U.family q z) :
    boundaryClass hS U (q + 1) c = 0 := by
  let _ : Epi S.g := hS.epi_g
  obtain ⟨V, r, t, ht⟩ :=
    exists_refinement_cochain_lift S.g U q z
  let b : OrderedCech.object (A := AddCommGrpCat.{u})
      S.X₂.presheaf V.family (q + 1) :=
    OrderedCech.differential S.X₂.presheaf V.family q t
  have hb : OrderedCech.coefficientMapDegree S.g.hom V.family (q + 1) b =
      OrderedCech.refinementMapDegree S.X₃.presheaf r (q + 1) c.1 := by
    calc
      _ = OrderedCech.differential S.X₃.presheaf V.family q
          (OrderedCech.coefficientMapDegree S.g.hom V.family q t) := by
            exact (ConcreteCategory.congr_hom
              (OrderedCech.coefficientMapDegree_comp_differential
                S.g.hom V.family q) t).symm
      _ = OrderedCech.differential S.X₃.presheaf V.family q
          (OrderedCech.refinementMapDegree S.X₃.presheaf r q z) := by rw [ht]
      _ = OrderedCech.refinementMapDegree S.X₃.presheaf r (q + 1)
          (OrderedCech.differential S.X₃.presheaf U.family q z) := by
            exact ConcreteCategory.congr_hom
              (OrderedCech.refinementMapDegree_comp_differential
                S.X₃.presheaf r q) z
      _ = _ := by rw [← hc]
  let P : BoundaryPresentation S U (q + 1) c :=
    { cover := V
      refinement := r
      lift := b
      descended := 0
      lift_eq := hb
      descended_eq := by
        rw [map_zero]
        change 0 = OrderedCech.differential S.X₂.presheaf V.family (q + 1)
          (OrderedCech.differential S.X₂.presheaf V.family q t)
        symm
        calc
          _ = (OrderedCech.differential S.X₂.presheaf V.family q ≫
              OrderedCech.differential S.X₂.presheaf V.family (q + 1)) t := by
                rw [ConcreteCategory.comp_apply]
          _ = 0 := by
            rw [OrderedCech.differential_comp_differential]
            rfl }
  rw [boundaryClass_eq_cechClass hS U (q + 1) c P]
  change toCechCohomology S.X₁.presheaf (q + 2) V
    (cocycleClass S.X₁.presheaf V (q + 2) (P.descendedCocycle hS)) = 0
  have hz : P.descendedCocycle hS = 0 := by
    apply Subtype.ext
    rfl
  rw [hz, map_zero, map_zero]

/-- Positive-degree cocycles differing by a Čech coboundary have the same connecting class. -/
theorem boundaryClass_eq_of_sub_eq_differential
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) (U : SetOpenCover X) (q : ℕ)
    (c c' : CechCocycle S.X₃.presheaf U (q + 1))
    (z : OrderedCech.object (A := AddCommGrpCat.{u})
      S.X₃.presheaf U.family q)
    (h : c.1 - c'.1 = OrderedCech.differential S.X₃.presheaf U.family q z) :
    boundaryClass hS U (q + 1) c = boundaryClass hS U (q + 1) c' := by
  apply sub_eq_zero.1
  change boundaryCocycleMap hS U (q + 1) c -
    boundaryCocycleMap hS U (q + 1) c' = 0
  rw [← map_sub]
  exact boundaryClass_eq_zero_of_eq_differential hS U q (c - c') z h

/-- The connecting class depends only on the fixed-cover cohomology class of its cocycle.
In degree zero, the incoming differential is zero, so equal classes force equal cocycles;
positive degrees use a lifted boundary primitive. -/
theorem boundaryClass_eq_of_cocycleClass_eq
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) (U : SetOpenCover X) (q : ℕ)
    (c c' : CechCocycle S.X₃.presheaf U q)
    (h : cocycleClass S.X₃.presheaf U q c =
      cocycleClass S.X₃.presheaf U q c') :
    boundaryClass hS U q c = boundaryClass hS U q c' := by
  have hzero : cocycleClass S.X₃.presheaf U q (c - c') = 0 := by
    rw [map_sub, h, sub_self]
  obtain ⟨b, hb⟩ :=
    (cocycleClass_eq_zero_iff S.X₃.presheaf U q (c - c')).1 hzero
  cases q with
  | zero =>
      have hnot : ¬(ComplexShape.up ℕ).Rel ((ComplexShape.up ℕ).prev 0) 0 := by
        simp only [CochainComplex.prev_nat_zero, ComplexShape.up_Rel]
        omega
      have hfzero : ((normalizedCechComplex S.X₃.presheaf U).sc 0).f b = 0 := by
        change (normalizedCechComplex S.X₃.presheaf U).d
          ((ComplexShape.up ℕ).prev 0) 0 b = 0
        rw [(normalizedCechComplex S.X₃.presheaf U).shape _ _ hnot]
        rfl
      have hval : (c - c').1 = 0 := hb.symm.trans hfzero
      have hcc : c = c' := sub_eq_zero.1 (Subtype.ext hval)
      rw [hcc]
  | succ n =>
      let K := normalizedCechComplex (A := AddCommGrpCat.{u}) S.X₃.presheaf U
      let z : OrderedCech.object (A := AddCommGrpCat.{u})
          S.X₃.presheaf U.family n :=
        (K.XIsoOfEq (CochainComplex.prev_nat_succ n)).hom b
      apply boundaryClass_eq_of_sub_eq_differential hS U n c c' z
      calc
        (c - c').1 = K.d ((ComplexShape.up ℕ).prev (n + 1)) (n + 1) b := hb.symm
        _ = K.d n (n + 1) z := by
          exact (ConcreteCategory.congr_hom
            (K.XIsoOfEq_hom_comp_d (CochainComplex.prev_nat_succ n) (n + 1)) b).symm
        _ = OrderedCech.differential S.X₃.presheaf U.family n z := by
          simp only [K, normalizedCechComplex, OrderedCech.complex_d]

/-- The abstract cycle object used by the homology API is additively equivalent to concrete
normalized Čech cocycles. -/
noncomputable def cyclesCocycleEquiv
    (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    (U : SetOpenCover X) (q : ℕ) :
    ToType ((normalizedCechComplex F U).sc q).cycles ≃+ CechCocycle F U q :=
  ((normalizedCechComplex F U).sc q).abCyclesIso.addCommGroupIsoToAddEquiv.trans
    (cocycleKernelEquiv F U q).symm

/-- Under the concrete cycle equivalence, the abstract homology projection is exactly
`cocycleClass`. -/
@[simp]
theorem cocycleClass_cyclesCocycleEquiv
    (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    (U : SetOpenCover X) (q : ℕ)
    (z : ToType ((normalizedCechComplex F U).sc q).cycles) :
    cocycleClass F U q (cyclesCocycleEquiv F U q z) =
      ((normalizedCechComplex F U).sc q).homologyπ z := by
  change (((normalizedCechComplex F U).sc q).abCyclesIso.inv ≫
      ((normalizedCechComplex F U).sc q).homologyπ)
        (((normalizedCechComplex F U).sc q).abCyclesIso.hom z) =
    ((normalizedCechComplex F U).sc q).homologyπ z
  rw [← ConcreteCategory.comp_apply, Iso.hom_inv_id_assoc]

/-- The additive lift--differentiate--descend map on the abstract cycle object of one fixed
cover. -/
noncomputable def boundaryCyclesMap
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) (U : SetOpenCover X) (q : ℕ) :
    ((normalizedCechComplex S.X₃.presheaf U).sc q).cycles ⟶
      cechCohomology S.X₁.presheaf (q + 1) :=
  AddCommGrpCat.ofHom
    ((boundaryCocycleMap hS U q).comp (cyclesCocycleEquiv S.X₃.presheaf U q).toAddMonoidHom)

@[simp]
theorem boundaryCyclesMap_apply
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) (U : SetOpenCover X) (q : ℕ)
    (z : ToType ((normalizedCechComplex S.X₃.presheaf U).sc q).cycles) :
    boundaryCyclesMap hS U q z =
      boundaryClass hS U q (cyclesCocycleEquiv S.X₃.presheaf U q z) := rfl

theorem toCycles_comp_boundaryCyclesMap
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) (U : SetOpenCover X) (q : ℕ) :
    ((normalizedCechComplex S.X₃.presheaf U).sc q).toCycles ≫
      boundaryCyclesMap hS U q = 0 := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro b
  change boundaryClass hS U q
    (cyclesCocycleEquiv S.X₃.presheaf U q
      (((normalizedCechComplex S.X₃.presheaf U).sc q).toCycles b)) = 0
  let c := cyclesCocycleEquiv S.X₃.presheaf U q
    (((normalizedCechComplex S.X₃.presheaf U).sc q).toCycles b)
  calc
    boundaryClass hS U q c = boundaryClass hS U q 0 :=
      boundaryClass_eq_of_cocycleClass_eq hS U q c 0 (by
        dsimp only [c]
        rw [cocycleClass_cyclesCocycleEquiv, map_zero,
          ← ConcreteCategory.comp_apply,
          ((normalizedCechComplex S.X₃.presheaf U).sc q).toCycles_comp_homologyπ]
        rfl)
    _ = 0 := boundaryClass_zero hS U q

/-- The homomorphism from fixed-cover Čech cohomology to the target direct limit obtained by
descending the additive cocycle formula through fixed-cover coboundaries. -/
noncomputable def fixedCoverBoundaryHom
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) (U : SetOpenCover X) (q : ℕ) :
    normalizedCechCohomology S.X₃.presheaf U q ⟶
      cechCohomology S.X₁.presheaf (q + 1) :=
  ((normalizedCechComplex S.X₃.presheaf U).sc q).descHomology
    (boundaryCyclesMap hS U q) (toCycles_comp_boundaryCyclesMap hS U q)

/-- Fixed-cover representative formula for the descended homomorphism. -/
theorem fixedCoverBoundaryHom_cocycleClass
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) (U : SetOpenCover X) (q : ℕ)
    (c : CechCocycle S.X₃.presheaf U q) :
    fixedCoverBoundaryHom hS U q (cocycleClass S.X₃.presheaf U q c) =
      boundaryClass hS U q c := by
  change (((normalizedCechComplex S.X₃.presheaf U).sc q).descHomology
      (boundaryCyclesMap hS U q) (toCycles_comp_boundaryCyclesMap hS U q))
        (((normalizedCechComplex S.X₃.presheaf U).sc q).homologyπ
          (((normalizedCechComplex S.X₃.presheaf U).sc q).abCyclesIso.inv
            (cocycleKernelEquiv S.X₃.presheaf U q c))) = _
  rw [← ConcreteCategory.comp_apply,
    ((normalizedCechComplex S.X₃.presheaf U).sc q).π_descHomology]
  rw [boundaryCyclesMap_apply]
  congr 1
  apply (cocycleKernelEquiv S.X₃.presheaf U q).injective
  change (cocycleKernelEquiv S.X₃.presheaf U q)
      ((cocycleKernelEquiv S.X₃.presheaf U q).symm
        (((normalizedCechComplex S.X₃.presheaf U).sc q).abCyclesIso.hom
          (((normalizedCechComplex S.X₃.presheaf U).sc q).abCyclesIso.inv
            (cocycleKernelEquiv S.X₃.presheaf U q c)))) =
    cocycleKernelEquiv S.X₃.presheaf U q c
  rw [(cocycleKernelEquiv S.X₃.presheaf U q).apply_symm_apply]
  change ((normalizedCechComplex S.X₃.presheaf U).sc q).abCyclesIso.hom
      (((normalizedCechComplex S.X₃.presheaf U).sc q).abCyclesIso.inv
        (cocycleKernelEquiv S.X₃.presheaf U q c)) =
    cocycleKernelEquiv S.X₃.presheaf U q c
  rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id]
  rfl

/-- Every fixed-cover cohomology class has a concrete normalized cocycle representative. -/
theorem cocycleClass_surjective
    (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    (U : SetOpenCover X) (q : ℕ) :
    Function.Surjective (cocycleClass F U q) := by
  let p : ((normalizedCechComplex F U).sc q).cycles ⟶
      normalizedCechCohomology F U q :=
    ((normalizedCechComplex F U).sc q).homologyπ
  let _ : Epi p :=
    Limits.epi_of_isColimit_cofork
      ((normalizedCechComplex F U).sc q).homologyIsCokernel
  intro x
  obtain ⟨z, hz⟩ := (AddCommGrpCat.epi_iff_surjective p).1 inferInstance x
  refine ⟨cyclesCocycleEquiv F U q z, ?_⟩
  rw [cocycleClass_cyclesCocycleEquiv]
  exact hz

/-- The fixed-cover boundary homomorphisms are compatible with the refinement-directed
transition maps. -/
theorem normalizedCechCohomologyMap_comp_fixedCoverBoundaryHom
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) {U V : SetOpenCover X} (h : U ≤ V) (q : ℕ) :
    normalizedCechCohomologyMap S.X₃.presheaf h q ≫ fixedCoverBoundaryHom hS V q =
      fixedCoverBoundaryHom hS U q := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  obtain ⟨c, rfl⟩ := cocycleClass_surjective S.X₃.presheaf U q x
  rw [ConcreteCategory.comp_apply,
    normalizedCechCohomologyMap_cocycleClass S.X₃.presheaf h (refinementOfLE h) q c,
    fixedCoverBoundaryHom_cocycleClass, fixedCoverBoundaryHom_cocycleClass,
    boundaryClass_refine]

/-- The additive Čech connecting homomorphism associated to a short exact sequence of
abelian sheaves. Its construction is lift--differentiate--descend, with no additional sign. -/
noncomputable def connectingHom
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) (q : ℕ) :
    cechCohomology S.X₃.presheaf q ⟶ cechCohomology S.X₁.presheaf (q + 1) :=
  cechCohomologyDesc S.X₃.presheaf q (cechCohomology S.X₁.presheaf (q + 1))
    (fun U => fixedCoverBoundaryHom hS U q)
    (fun {_ _} h => normalizedCechCohomologyMap_comp_fixedCoverBoundaryHom hS h q)

/-- On every fixed cover, the connecting homomorphism is the descended fixed-cover boundary
homomorphism. -/
theorem toCechCohomology_comp_connectingHom
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) (U : SetOpenCover X) (q : ℕ) :
    toCechCohomology S.X₃.presheaf q U ≫ connectingHom hS q =
      fixedCoverBoundaryHom hS U q := by
  apply toCechCohomology_comp_cechCohomologyDesc

/-- Fixed-cover cocycle formula for the connecting homomorphism. -/
theorem connectingHom_cocycleClass
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) (U : SetOpenCover X) (q : ℕ)
    (c : CechCocycle S.X₃.presheaf U q) :
    connectingHom hS q
        (toCechCohomology S.X₃.presheaf q U
          (cocycleClass S.X₃.presheaf U q c)) =
      boundaryClass hS U q c := by
  rw [← ConcreteCategory.comp_apply, toCechCohomology_comp_connectingHom,
    fixedCoverBoundaryHom_cocycleClass]

/-- Fully expanded representative formula: any lift--differentiate--descend presentation
computes the image of its fixed-cover cocycle under the connecting homomorphism. -/
theorem connectingHom_cocycleClass_eq_cechClass
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) (U : SetOpenCover X) (q : ℕ)
    (c : CechCocycle S.X₃.presheaf U q)
    (P : BoundaryPresentation S U q c) :
    connectingHom hS q
        (toCechCohomology S.X₃.presheaf q U
          (cocycleClass S.X₃.presheaf U q c)) =
      P.cechClass hS := by
  rw [connectingHom_cocycleClass, boundaryClass_eq_cechClass hS U q c P]

/-- The lift--differentiate--descend value is independent of the chosen fixed-cover cocycle
representative of a direct-limit class, even when the representatives live on different covers. -/
theorem boundaryClass_eq_of_directLimit_rep_eq
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) {U V : SetOpenCover X} (q : ℕ)
    (c : CechCocycle S.X₃.presheaf U q)
    (c' : CechCocycle S.X₃.presheaf V q)
    (h : toCechCohomology S.X₃.presheaf q U
        (cocycleClass S.X₃.presheaf U q c) =
      toCechCohomology S.X₃.presheaf q V
        (cocycleClass S.X₃.presheaf V q c')) :
    boundaryClass hS U q c = boundaryClass hS V q c' := by
  calc
    boundaryClass hS U q c = connectingHom hS q
        (toCechCohomology S.X₃.presheaf q U
          (cocycleClass S.X₃.presheaf U q c)) :=
      (connectingHom_cocycleClass hS U q c).symm
    _ = connectingHom hS q
        (toCechCohomology S.X₃.presheaf q V
          (cocycleClass S.X₃.presheaf V q c')) := congrArg (connectingHom hS q) h
    _ = boundaryClass hS V q c' := connectingHom_cocycleClass hS V q c'

/-- Every direct-limit Čech class is represented by a concrete cocycle on one fixed cover. -/
theorem cechCohomology_exists_cocycle_rep
    (F : TopCat.Presheaf AddCommGrpCat.{u} X) (q : ℕ)
    (x : ToType (cechCohomology F q)) :
    ∃ (U : SetOpenCover X) (c : CechCocycle F U q),
      toCechCohomology F q U (cocycleClass F U q c) = x := by
  obtain ⟨U, y, hy⟩ := cechCohomology_exists_rep F q x
  obtain ⟨c, rfl⟩ := cocycleClass_surjective F U q y
  exact ⟨U, c, hy⟩

/-- Every direct-limit class admits the reviewed lift--differentiate--descend formula on a
fixed cover and a further lifting refinement. -/
theorem connectingHom_exists_boundaryPresentation
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) (q : ℕ)
    (x : ToType (cechCohomology S.X₃.presheaf q)) :
    ∃ (U : SetOpenCover X) (c : CechCocycle S.X₃.presheaf U q)
      (P : BoundaryPresentation S U q c),
      toCechCohomology S.X₃.presheaf q U
          (cocycleClass S.X₃.presheaf U q c) = x ∧
        connectingHom hS q x = P.cechClass hS := by
  obtain ⟨U, c, hc⟩ := cechCohomology_exists_cocycle_rep S.X₃.presheaf q x
  let P := chosenBoundaryPresentation hS U q c
  refine ⟨U, c, P, hc, ?_⟩
  rw [← hc]
  exact connectingHom_cocycleClass_eq_cechClass hS U q c P

@[simp]
theorem connectingHom_zero
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) (q : ℕ) :
    connectingHom hS q 0 = 0 := map_zero _

theorem connectingHom_add
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    [ParacompactSpace X] [T2Space X]
    (hS : S.ShortExact) (q : ℕ)
    (x y : ToType (cechCohomology S.X₃.presheaf q)) :
    connectingHom hS q (x + y) = connectingHom hS q x + connectingHom hS q y :=
  map_add _ _ _

/-- The cochain descended through the monomorphism in (C21) is uniquely determined by its
coefficient image. -/
theorem BoundaryPresentation.descended_unique
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    {U : SetOpenCover X} {q : ℕ} {c : CechCocycle S.X₃.presheaf U q}
    (hS : S.ShortExact) (P : BoundaryPresentation S U q c)
    (a : OrderedCech.object (A := AddCommGrpCat.{u})
      S.X₁.presheaf P.cover.family (q + 1))
    (ha : OrderedCech.coefficientMapDegree S.f.hom P.cover.family (q + 1) a =
      OrderedCech.differential S.X₂.presheaf P.cover.family q P.lift) :
    a = P.descended :=
  cochain_f_injective hS P.cover (q + 1) (ha.trans P.descended_eq.symm)

end TopologicalSpace.OpenCover.SetOpenCover
