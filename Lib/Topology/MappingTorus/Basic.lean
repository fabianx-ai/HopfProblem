/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Algebra.Homology.MayerVietorisShortExact
import Lib.AlgebraicTopology.SingularHomology.Chains
import Lib.AlgebraicTopology.SingularHomology.ModuleHomology
import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Lib.Topology.Homotopy.Suspension
import Lib.AlgebraicTopology.SingularHomology.Sphere
import Lib.AlgebraicTopology.SingularHomology.Suspension
import Lib.AlgebraicTopology.SingularHomology.Sum
import Lib.AlgebraicTopology.SingularHomology.CircleProduct
import Lib.AlgebraicTopology.SingularHomology.SphereHomology
/-!
# The mapping torus of a homeomorphism

  The mapping torus of a homeomorphism `f : X ~= X`: the quotient of `I x X` by
  `(1, x) ~ (0, f x)`, its base and fiber projections, the two-open cover by the
  cylinder halves, and the H_1 presentation (Hatcher, Algebraic Topology,
  Example 2.48).
-/



set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

abbrev MappingTorus.Circle :=
  AddCircle (1 : ℝ)

def MappingTorus.deck {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) (n : ℤ) (p : ℝ × X) : ℝ × X :=
  (p.1 + (n : ℝ), (f ^ (-n)) p.2)

@[simp]
theorem MappingTorus.deck_zero {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) (p : ℝ × X) :
    deck f 0 p = p := by simp [deck]

theorem MappingTorus.deck_add {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) (m n : ℤ)
    (p : ℝ × X) : deck f (m + n) p = deck f m (deck f n p) := by
  apply Prod.ext
  · simp only [deck, Int.cast_add]
    abel
  · simp only [deck, neg_add, zpow_add, Homeomorph.mul_apply]

theorem MappingTorus.deck_continuous {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) (n : ℤ) :
    Continuous (deck f n) :=
  (continuous_fst.add continuous_const).prodMk ((f ^ (-n)).continuous.comp continuous_snd)

def MappingTorus.deckHomeomorph {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) (n : ℤ) :
    (ℝ × X) ≃ₜ (ℝ × X) where
  toFun := deck f n
  invFun := deck f (-n)
  left_inv p := by rw [← deck_add, neg_add_cancel, deck_zero]
  right_inv p := by rw [← deck_add, add_neg_cancel, deck_zero]
  continuous_toFun := deck_continuous f n
  continuous_invFun := deck_continuous f (-n)

def MappingTorus.orbitSetoid {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) : Setoid (ℝ × X)
    where
  r p q := ∃ n : ℤ, deck f n p = q
  iseqv :=
    { refl := fun p ↦ ⟨0, deck_zero f p⟩
      symm := by
        rintro p q ⟨n, rfl⟩
        exact ⟨-n, by rw [← deck_add, neg_add_cancel, deck_zero]⟩
      trans := by
        rintro p q r ⟨m, rfl⟩ ⟨n, rfl⟩
        exact ⟨n + m, deck_add f n m p⟩ }

def MappingTorus.Torus {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) :=
  Quotient (orbitSetoid f)

instance MappingTorus.instLocal1 {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) :
    TopologicalSpace (Torus f) :=
  inferInstanceAs (TopologicalSpace (Quotient (orbitSetoid f)))

def MappingTorus.mk {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) (p : ℝ × X) : Torus f :=
  Quotient.mk (orbitSetoid f) p

theorem MappingTorus.mk_continuous {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) :
    Continuous (MappingTorus.mk f) :=
  continuous_quotient_mk'

theorem MappingTorus.mk_surjective {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) :
    Function.Surjective (MappingTorus.mk f) :=
  Quotient.mk_surjective

theorem MappingTorus.mk_eq_mk_iff {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) (p q : ℝ × X) :
    MappingTorus.mk f p = MappingTorus.mk f q ↔
      ∃ n : ℤ, q.1 = p.1 + (n : ℝ) ∧ q.2 = (f ^ (-n)) p.2 := by
  change (Quotient.mk (orbitSetoid f) p = Quotient.mk (orbitSetoid f) q) ↔ _
  rw [Quotient.eq]
  change (∃ n : ℤ, deck f n p = q) ↔ _
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (congrArg Prod.fst hn).symm, (congrArg Prod.snd hn).symm⟩
  · rintro ⟨n, ht, hx⟩
    exact ⟨n, Prod.ext ht.symm hx.symm⟩

@[simp]
theorem MappingTorus.mk_deck {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) (n : ℤ) (p : ℝ × X) :
    MappingTorus.mk f (deck f n p) = MappingTorus.mk f p :=
  (Quotient.sound (s := orbitSetoid f) ⟨n, rfl⟩).symm

@[simp]
theorem MappingTorus.mk_sub_one {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) (t : ℝ) (x : X) :
    MappingTorus.mk f (t - 1, f x) = MappingTorus.mk f (t, x) := by
  simpa [deck, sub_eq_add_neg] using mk_deck f (-1) (t, x)

theorem MappingTorus.mk_add_one {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) (t : ℝ) (x : X) :
    MappingTorus.mk f (t + 1, x) = MappingTorus.mk f (t, f x) := by
  simpa using (mk_sub_one f (t + 1) x).symm

theorem MappingTorus.mk_preimage_image {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X)
    (s : Set (ℝ × X)) : MappingTorus.mk f ⁻¹' (MappingTorus.mk f '' s) = ⋃ n : ℤ, deck f n '' s :=
  by
  ext p
  constructor
  · rintro ⟨q, hq, he⟩
    obtain ⟨n, hn⟩ := Quotient.exact he
    exact Set.mem_iUnion.mpr ⟨n, q, hq, hn⟩
  · intro hp
    obtain ⟨n, q, hq, rfl⟩ := Set.mem_iUnion.mp hp
    exact ⟨q, hq, (mk_deck f n q).symm⟩

theorem MappingTorus.mk_open {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) :
    IsOpenMap (MappingTorus.mk f) := by
  intro s hs
  apply (isQuotientMap_quotient_mk' (s := orbitSetoid f)).isOpen_preimage.mp
  change IsOpen (MappingTorus.mk f ⁻¹' (MappingTorus.mk f '' s))
  rw [mk_preimage_image]
  exact isOpen_iUnion fun n ↦ (deckHomeomorph f n).isOpenMap s hs

@[simp]
theorem MappingTorus.circle_intCast (n : ℤ) : ((n : ℝ) : MappingTorus.Circle) = 0 := by
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  exact ⟨n, by simp⟩

theorem MappingTorus.circle_coe_eq_iff (t s : ℝ) :
    (t : MappingTorus.Circle) = (s : MappingTorus.Circle) ↔ ∃ n : ℤ, s = t + (n : ℝ) := by
  constructor
  · intro h
    have hs : ((s - t : ℝ) : MappingTorus.Circle) = 0 := by rw [AddCircle.coe_sub, h, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hs
    refine ⟨n, ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hn
    linarith
  · rintro ⟨n, rfl⟩
    simp

def MappingTorus.base {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) :
    C(Torus f, MappingTorus.Circle)
    where
  toFun :=
    Quotient.lift (fun p : ℝ × X ↦ (p.1 : MappingTorus.Circle))
      (by
        rintro p q ⟨n, rfl⟩
        simp [deck])
  continuous_toFun := (AddCircle.continuous_mk' (1 : ℝ)).comp continuous_fst |>.quotient_lift _

@[simp]
theorem MappingTorus.base_mk {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) (p : ℝ × X) :
    base f (MappingTorus.mk f p) = (p.1 : MappingTorus.Circle) :=
  rfl

theorem MappingTorus.base_mk_ne_of_mem_Ioo {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) (a : ℝ)
    (t : Set.Ioo a (a + 1)) (x : X) :
    base f (MappingTorus.mk f ((t : ℝ), x)) ≠ (a : MappingTorus.Circle) :=
  (AddCircle.openPartialHomeomorphCoe (1 : ℝ) a).map_source t.property

def MappingTorus.intervalParam {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) (a : ℝ)
    (p : Set.Ioo a (a + 1) × X) : { q : Torus f // base f q ≠ (a : MappingTorus.Circle) } :=
  ⟨MappingTorus.mk f ((p.1 : ℝ), p.2), base_mk_ne_of_mem_Ioo f a p.1 p.2⟩

theorem MappingTorus.intervalParam_continuous {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X)
    (a : ℝ) : Continuous (intervalParam f a) :=
  ((mk_continuous f).comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).subtype_mk
    _

theorem MappingTorus.intervalParam_open {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) (a : ℝ) :
    IsOpenMap (intervalParam f a) :=
  ((mk_open f).comp (isOpen_Ioo.isOpenMap_subtype_val.prodMap IsOpenMap.id)).subtype_mk _

theorem MappingTorus.intervalParam_injective {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X)
    (a : ℝ) : Function.Injective (intervalParam f a) := by
  intro p q hpq
  have he : MappingTorus.mk f ((p.1 : ℝ), p.2) = MappingTorus.mk f ((q.1 : ℝ), q.2) :=
    congrArg Subtype.val hpq
  have hc : ((p.1 : ℝ) : MappingTorus.Circle) = ((q.1 : ℝ) : MappingTorus.Circle) :=
    congrArg (base f) he
  have ht : (p.1 : ℝ) = (q.1 : ℝ) :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico (Set.Ioo_subset_Ico_self p.1.property)
          (Set.Ioo_subset_Ico_self q.1.property)).mp
      hc
  obtain ⟨n, hn, hx⟩ := (mk_eq_mk_iff f _ _).mp he
  have hnR : (n : ℝ) = 0 := by
    dsimp at hn
    linarith
  have hn0 : n = 0 := Int.cast_eq_zero.mp hnR
  apply Prod.ext (Subtype.ext ht)
  simpa [hn0] using hx.symm

theorem MappingTorus.intervalParam_surjective {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X)
    (a : ℝ) : Function.Surjective (intervalParam f a) := by
  intro q
  obtain ⟨⟨s, x⟩, hp⟩ := mk_surjective f q.val
  let e := AddCircle.openPartialHomeomorphCoe (1 : ℝ) a
  let t : Set.Ioo a (a + 1) := ⟨e.symm (base f q.val), e.map_target q.property⟩
  have ht : ((t : ℝ) : MappingTorus.Circle) = base f q.val := e.right_inv q.property
  have hst : (s : MappingTorus.Circle) = ((t : ℝ) : MappingTorus.Circle) :=
    (congrArg (base f) hp).trans ht.symm
  obtain ⟨n, hn⟩ := (circle_coe_eq_iff s (t : ℝ)).mp hst
  refine ⟨(t, (f ^ (-n)) x), Subtype.ext ?_⟩
  change MappingTorus.mk f ((t : ℝ), (f ^ (-n)) x) = q.val
  rw [hn]
  exact (mk_deck f n (s, x)).trans hp

def MappingTorus.intervalHomeomorph {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) (a : ℝ) :
    { q : Torus f // base f q ≠ (a : MappingTorus.Circle) } ≃ₜ (Set.Ioo a (a + 1) × X) :=
  ((Equiv.ofBijective (intervalParam f a)
          ⟨intervalParam_injective f a,
            intervalParam_surjective f a⟩).toHomeomorphOfContinuousOpen
      (intervalParam_continuous f a) (intervalParam_open f a)).symm

@[simp]
theorem MappingTorus.intervalHomeomorph_symm_coe {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X)
    (a : ℝ) (p : Set.Ioo a (a + 1) × X) :
    ((intervalHomeomorph f a).symm p : Torus f) = MappingTorus.mk f ((p.1 : ℝ), p.2) :=
  rfl

theorem MappingTorus.HomologyCover.negativeHalf_coe :
    ((-(1 / 2 : ℝ)) : (SingularHomology.CircleTopology.Circle)) =
      SingularHomology.CircleTopology.halfPoint := by
  have h := AddCircle.coe_add_period (p := (1 : ℝ)) (-(1 / 2 : ℝ))
  norm_num [SingularHomology.CircleTopology.halfPoint] at h ⊢
  exact h.symm

theorem MappingTorus.HomologyCover.negativeHalf_coe_ne_zero :
    ((-(1 / 2 : ℝ)) : (SingularHomology.CircleTopology.Circle)) ≠ 0 := by
  rw [negativeHalf_coe]
  exact SingularHomology.CircleTopology.halfPoint_ne_zero

theorem MappingTorus.HomologyCover.unitInterval_coe_eq_negativeHalf_iff (t : Set.Ioo (0 : ℝ) 1) :
    ((t : ℝ) : (SingularHomology.CircleTopology.Circle)) =
        ((-(1 / 2 : ℝ)) : (SingularHomology.CircleTopology.Circle)) ↔
      (t : ℝ) = 1 / 2 := by
  rw [negativeHalf_coe]
  exact
    AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := 0)
      ⟨le_of_lt t.property.1, by simpa only [zero_add] using t.property.2⟩ (by norm_num)

theorem MappingTorus.HomologyCover.unitInterval_coe_ne_negativeHalf_iff (t : Set.Ioo (0 : ℝ) 1) :
    ((t : ℝ) : (SingularHomology.CircleTopology.Circle)) ≠
        ((-(1 / 2 : ℝ)) : (SingularHomology.CircleTopology.Circle)) ↔
      (t : ℝ) ≠ 1 / 2 :=
  not_congr (unitInterval_coe_eq_negativeHalf_iff t)

def MappingTorus.HomologyCover.firstPredicateHomeomorph (A X : Type*) [TopologicalSpace A]
    [TopologicalSpace X] (p : A → Prop) : { z : A × X // p z.1 } ≃ₜ ({ a : A // p a } × X)
    where
  toFun z := (⟨z.val.1, z.property⟩, z.val.2)
  invFun z := ⟨(z.1.val, z.2), z.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.fst.subtype_mk _).prodMk continuous_subtype_val.snd
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).subtype_mk _

def MappingTorus.HomologyCover.intervalIntersectionHomeomorph (X : Type*) [TopologicalSpace X] :
    { p : Set.Ioo (0 : ℝ) 1 × X // (p.1 : ℝ) ≠ 1 / 2 } ≃ₜ
      ((Set.Ioo (0 : ℝ) (1 / 2) × X) ⊕ (Set.Ioo (1 / 2 : ℝ) 1 × X)) :=
  ((firstPredicateHomeomorph (Set.Ioo (0 : ℝ) 1) X (fun t => (t : ℝ) ≠ 1 / 2)).trans
        (SingularHomology.CircleTopology.puncturedIntervalHomeomorph.prodCongr
          (Homeomorph.refl X))).trans
    Homeomorph.sumProdDistrib

def MappingTorus.HomologyCover.U {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    Set (MappingTorus.Torus f) :=
  {q | MappingTorus.base f q ≠ ((0 : ℝ) : MappingTorus.Circle)}

def MappingTorus.HomologyCover.V {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    Set (MappingTorus.Torus f) :=
  {q | MappingTorus.base f q ≠ ((-(1 / 2 : ℝ)) : MappingTorus.Circle)}

theorem MappingTorus.HomologyCover.U_open {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    IsOpen (U f) :=
  isOpen_compl_singleton.preimage (MappingTorus.base f).continuous

theorem MappingTorus.HomologyCover.V_open {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    IsOpen (V f) :=
  isOpen_compl_singleton.preimage (MappingTorus.base f).continuous

theorem MappingTorus.HomologyCover.cover {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    U f ∪ V f = Set.univ := by
  ext q
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  by_cases hq : MappingTorus.base f q = 0
  · right
    change MappingTorus.base f q ≠ ((-(1 / 2 : ℝ)) : MappingTorus.Circle)
    rw [hq]
    exact Ne.symm negativeHalf_coe_ne_zero
  · exact Or.inl hq

def MappingTorus.HomologyCover.chartU {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    U f ≃ₜ Set.Ioo (0 : ℝ) 1 × X :=
  (MappingTorus.intervalHomeomorph f 0).trans
    ((Homeomorph.setCongr (by simp : Ioo (0 : ℝ) (0 + 1) = Ioo 0 1)).prodCongr
      (Homeomorph.refl X))

def MappingTorus.HomologyCover.chartV {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    V f ≃ₜ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) × X :=
  (MappingTorus.intervalHomeomorph f (-(1 / 2 : ℝ))).trans
    ((Homeomorph.setCongr
          (by norm_num : Ioo (-(1 / 2 : ℝ)) (-(1 / 2) + 1) = Ioo (-(1 / 2)) (1 / 2))).prodCongr
      (Homeomorph.refl X))

@[simp]
theorem MappingTorus.HomologyCover.chartU_symm_coe {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (p : Set.Ioo (0 : ℝ) 1 × X) :
    ((chartU f).symm p : MappingTorus.Torus f) = MappingTorus.mk f ((p.1 : ℝ), p.2) :=
  MappingTorus.intervalHomeomorph_symm_coe f 0 _

@[simp]
theorem MappingTorus.HomologyCover.chartV_symm_coe {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (p : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) × X) :
    ((chartV f).symm p : MappingTorus.Torus f) = MappingTorus.mk f ((p.1 : ℝ), p.2) :=
  MappingTorus.intervalHomeomorph_symm_coe f (-(1 / 2 : ℝ)) _

theorem MappingTorus.HomologyCover.chartU_mk {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (q : U f) (p : Set.Ioo (0 : ℝ) 1 × X)
    (hq : (q : MappingTorus.Torus f) = MappingTorus.mk f ((p.1 : ℝ), p.2)) : chartU f q = p := by
  apply (chartU f).symm.injective
  rw [Homeomorph.symm_apply_apply]
  exact Subtype.ext (hq.trans (chartU_symm_coe f p).symm)

theorem MappingTorus.HomologyCover.chartV_mk {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (q : V f) (p : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) × X)
    (hq : (q : MappingTorus.Torus f) = MappingTorus.mk f ((p.1 : ℝ), p.2)) : chartV f q = p := by
  apply (chartV f).symm.injective
  rw [Homeomorph.symm_apply_apply]
  exact Subtype.ext (hq.trans (chartV_symm_coe f p).symm)

theorem MappingTorus.HomologyCover.chartU_representation {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (q : U f) :
    MappingTorus.mk f (((chartU f q).1 : ℝ), (chartU f q).2) = (q : MappingTorus.Torus f) := by
  rw [← chartU_symm_coe, Homeomorph.symm_apply_apply]

theorem MappingTorus.HomologyCover.chartV_representation {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (q : V f) :
    MappingTorus.mk f (((chartV f q).1 : ℝ), (chartV f q).2) = (q : MappingTorus.Torus f) := by
  rw [← chartV_symm_coe, Homeomorph.symm_apply_apply]

theorem MappingTorus.HomologyCover.chartU_base {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (q : U f) : (((chartU f q).1 : ℝ) : MappingTorus.Circle) = MappingTorus.base f q := by
  have h := congrArg (MappingTorus.base f) (chartU_representation f q)
  simpa only [MappingTorus.base_mk] using h

theorem MappingTorus.HomologyCover.chartU_mem_V_iff {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (q : U f) : (q : MappingTorus.Torus f) ∈ V f ↔ ((chartU f q).1 : ℝ) ≠ 1 / 2 := by
  change MappingTorus.base f q ≠ ((-(1 / 2 : ℝ)) : MappingTorus.Circle) ↔ _
  rw [← chartU_base]
  exact unitInterval_coe_ne_negativeHalf_iff _

def MappingTorus.HomologyCover.intersectionChart {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    ↥(U f ∩ V f) ≃ₜ { p : Set.Ioo (0 : ℝ) 1 × X // (p.1 : ℝ) ≠ 1 / 2 } :=
  (SingularHomology.CircleTopology.intersectionSubtypeHomeomorph (U f) (V f)).trans
    ((chartU f).subtype (chartU_mem_V_iff f))

def MappingTorus.HomologyCover.intersectionHomeomorph {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) :
    ↥(U f ∩ V f) ≃ₜ ((Set.Ioo (0 : ℝ) (1 / 2) × X) ⊕ (Set.Ioo (1 / 2 : ℝ) 1 × X)) :=
  (intersectionChart f).trans (intervalIntersectionHomeomorph X)

@[simp]
theorem MappingTorus.HomologyCover.intersectionHomeomorph_symm_inl_coe {X : Type}
    [TopologicalSpace X] (f : X ≃ₜ X) (p : Set.Ioo (0 : ℝ) (1 / 2) × X) :
    ((intersectionHomeomorph f).symm (Sum.inl p) : MappingTorus.Torus f) =
      MappingTorus.mk f ((p.1 : ℝ), p.2) :=
  chartU_symm_coe f _

@[simp]
theorem MappingTorus.HomologyCover.intersectionHomeomorph_symm_inr_coe {X : Type}
    [TopologicalSpace X] (f : X ≃ₜ X) (p : Set.Ioo (1 / 2 : ℝ) 1 × X) :
    ((intersectionHomeomorph f).symm (Sum.inr p) : MappingTorus.Torus f) =
      MappingTorus.mk f ((p.1 : ℝ), p.2) :=
  chartU_symm_coe f _

def MappingTorus.HomologyCover.inclusionU {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    C(U f, MappingTorus.Torus f) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def MappingTorus.HomologyCover.inclusionV {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    C(V f, MappingTorus.Torus f) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def MappingTorus.HomologyCover.intersectionToU {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    C(↥(U f ∩ V f), U f) :=
  ContinuousMap.inclusion Set.inter_subset_left

def MappingTorus.HomologyCover.intersectionToV {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    C(↥(U f ∩ V f), V f) :=
  ContinuousMap.inclusion Set.inter_subset_right

theorem MappingTorus.HomologyCover.chartU_intersection_inl {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (p : Set.Ioo (0 : ℝ) (1 / 2) × X) :
    (chartU f (intersectionToU f ((intersectionHomeomorph f).symm (Sum.inl p)))).2 = p.2 := by
  exact
    congrArg Prod.snd
      (chartU_mk f (intersectionToU f ((intersectionHomeomorph f).symm (Sum.inl p)))
        ((SingularHomology.CircleTopology.puncturedIntervalInl p.1).val, p.2)
        (intersectionHomeomorph_symm_inl_coe f p))

theorem MappingTorus.HomologyCover.chartU_intersection_inr {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (p : Set.Ioo (1 / 2 : ℝ) 1 × X) :
    (chartU f (intersectionToU f ((intersectionHomeomorph f).symm (Sum.inr p)))).2 = p.2 := by
  exact
    congrArg Prod.snd
      (chartU_mk f (intersectionToU f ((intersectionHomeomorph f).symm (Sum.inr p)))
        ((SingularHomology.CircleTopology.puncturedIntervalInr p.1).val, p.2)
        (intersectionHomeomorph_symm_inr_coe f p))

theorem MappingTorus.HomologyCover.chartV_intersection_inl {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (p : Set.Ioo (0 : ℝ) (1 / 2) × X) :
    (chartV f (intersectionToV f ((intersectionHomeomorph f).symm (Sum.inl p)))).2 = p.2 := by
  let t : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) :=
    ⟨p.1, by constructor <;> linarith [p.1.property.1, p.1.property.2]⟩
  rw [chartV_mk f _ (t, p.2) (intersectionHomeomorph_symm_inl_coe f p)]

theorem MappingTorus.HomologyCover.chartV_intersection_inr {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (p : Set.Ioo (1 / 2 : ℝ) 1 × X) :
    (chartV f (intersectionToV f ((intersectionHomeomorph f).symm (Sum.inr p)))).2 = f p.2 := by
  let t : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) :=
    ⟨(p.1 : ℝ) - 1, by constructor <;> linarith [p.1.property.1, p.1.property.2]⟩
  apply congrArg Prod.snd (chartV_mk f _ (t, f p.2) ?_)
  exact (intersectionHomeomorph_symm_inr_coe f p).trans (MappingTorus.mk_sub_one f _ _).symm

def MappingTorus.HomologyCover.fibreInclusion {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    C(X, MappingTorus.Torus f) :=
  ⟨fun x => MappingTorus.mk f (0, x),
    (MappingTorus.mk_continuous f).comp (continuous_const.prodMk continuous_id)⟩

def MappingTorus.HomologyCover.liftContraction {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    {S : Type} [TopologicalSpace S] (q : C(S, MappingTorus.Torus f)) (l : C(S, ℝ × X))
    (hl : ∀ s, MappingTorus.mk f (l s) = q s) :
    q.Homotopy ((fibreInclusion f).comp (ContinuousMap.snd.comp l))
    where
  toFun p := MappingTorus.mk f ((1 - (p.1 : ℝ)) * (l p.2).1, (l p.2).2)
  continuous_toFun :=
    (MappingTorus.mk_continuous f).comp
      (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
            (l.continuous.fst.comp continuous_snd)).prodMk
        (l.continuous.snd.comp continuous_snd))
  map_zero_left s := by simpa using hl s
  map_one_left s := by simp [fibreInclusion]

def MappingTorus.HomologyCover.liftU {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    C(U f, ℝ × X) :=
  ⟨fun q => (((chartU f q).1 : ℝ), (chartU f q).2),
    (continuous_subtype_val.comp (chartU f).continuous.fst).prodMk (chartU f).continuous.snd⟩

def MappingTorus.HomologyCover.liftV {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    C(V f, ℝ × X) :=
  ⟨fun q => (((chartV f q).1 : ℝ), (chartV f q).2),
    (continuous_subtype_val.comp (chartV f).continuous.fst).prodMk (chartV f).continuous.snd⟩

def MappingTorus.HomologyCover.homotopyEquivU {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    U f ≃ₕ X := by
  letI : ContractibleSpace (Set.Ioo (0 : ℝ) 1) :=
    SingularHomology.CircleTopology.intervalContractible 0 1 zero_lt_one
  exact
    (chartU f).toHomotopyEquiv.trans
      (SingularHomology.CircleTopology.contractibleProdHomotopyEquiv (Set.Ioo (0 : ℝ) 1)
        X)

def MappingTorus.HomologyCover.homotopyEquivV {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    V f ≃ₕ X := by
  letI : ContractibleSpace (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
    SingularHomology.CircleTopology.intervalContractible _ _ (by norm_num)
  exact
    (chartV f).toHomotopyEquiv.trans
      (SingularHomology.CircleTopology.contractibleProdHomotopyEquiv
        (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) X)

def MappingTorus.HomologyCover.inclusionUHomotopy {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    (inclusionU f).Homotopy ((fibreInclusion f).comp (homotopyEquivU f).toFun) :=
  liftContraction f (inclusionU f) (liftU f) (chartU_representation f)

def MappingTorus.HomologyCover.inclusionVHomotopy {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    (inclusionV f).Homotopy ((fibreInclusion f).comp (homotopyEquivV f).toFun) :=
  liftContraction f (inclusionV f) (liftV f) (chartV_representation f)

def MappingTorus.HomologyCover.intersectionHomotopyEquiv {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) : ↥(U f ∩ V f) ≃ₕ X ⊕ X :=
  (intersectionHomeomorph f).toHomotopyEquiv.trans
    (SingularHomology.CircleTopology.sumHomotopyEquiv
      (SingularHomology.CircleTopology.contractibleProdHomotopyEquiv
        (Set.Ioo (0 : ℝ) (1 / 2)) X)
      (SingularHomology.CircleTopology.contractibleProdHomotopyEquiv
        (Set.Ioo (1 / 2 : ℝ) 1) X))

@[simp]
theorem MappingTorus.HomologyCover.intersectionHomotopyEquiv_inl {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (p : Set.Ioo (0 : ℝ) (1 / 2) × X) :
    intersectionHomotopyEquiv f ((intersectionHomeomorph f).symm (Sum.inl p)) = Sum.inl p.2 := by
  change
    Sum.map (fun p : Set.Ioo (0 : ℝ) (1 / 2) × X => p.2)
        (fun p : Set.Ioo (1 / 2 : ℝ) 1 × X => p.2)
        (intersectionHomeomorph f ((intersectionHomeomorph f).symm (Sum.inl p))) =
      _
  rw [Homeomorph.apply_symm_apply]
  rfl

@[simp]
theorem MappingTorus.HomologyCover.intersectionHomotopyEquiv_inr {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (p : Set.Ioo (1 / 2 : ℝ) 1 × X) :
    intersectionHomotopyEquiv f ((intersectionHomeomorph f).symm (Sum.inr p)) = Sum.inr p.2 := by
  change
    Sum.map (fun p : Set.Ioo (0 : ℝ) (1 / 2) × X => p.2)
        (fun p : Set.Ioo (1 / 2 : ℝ) 1 × X => p.2)
        (intersectionHomeomorph f ((intersectionHomeomorph f).symm (Sum.inr p))) =
      _
  rw [Homeomorph.apply_symm_apply]
  rfl

theorem MappingTorus.HomologyCover.intersectionToU_fold {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) :
    (homotopyEquivU f).toFun.comp (intersectionToU f) =
      (SingularHomology.sumElimMap (ContinuousMap.id X) (ContinuousMap.id X)).comp
        (intersectionHomotopyEquiv f).toFun := by
  apply ContinuousMap.ext
  intro q
  obtain ⟨p, rfl⟩ := (intersectionHomeomorph f).symm.surjective q
  cases p with
  | inl
    p =>
    change
      (chartU f (intersectionToU f _)).2 =
        SingularHomology.sumElimMap (ContinuousMap.id X) (ContinuousMap.id X)
          (intersectionHomotopyEquiv f _)
    rw [intersectionHomotopyEquiv_inl, chartU_intersection_inl]
    rfl
  | inr
    p =>
    change
      (chartU f (intersectionToU f _)).2 =
        SingularHomology.sumElimMap (ContinuousMap.id X) (ContinuousMap.id X)
          (intersectionHomotopyEquiv f _)
    rw [intersectionHomotopyEquiv_inr, chartU_intersection_inr]
    rfl

theorem MappingTorus.HomologyCover.intersectionToV_twistedFold {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) :
    (homotopyEquivV f).toFun.comp (intersectionToV f) =
      (SingularHomology.sumElimMap (ContinuousMap.id X) (f : C(X, X))).comp
        (intersectionHomotopyEquiv f).toFun := by
  apply ContinuousMap.ext
  intro q
  obtain ⟨p, rfl⟩ := (intersectionHomeomorph f).symm.surjective q
  cases p with
  | inl
    p =>
    change
      (chartV f (intersectionToV f _)).2 =
        SingularHomology.sumElimMap (ContinuousMap.id X) (f : C(X, X))
          (intersectionHomotopyEquiv f _)
    rw [intersectionHomotopyEquiv_inl, chartV_intersection_inl]
    rfl
  | inr
    p =>
    change
      (chartV f (intersectionToV f _)).2 =
        SingularHomology.sumElimMap (ContinuousMap.id X) (f : C(X, X))
          (intersectionHomotopyEquiv f _)
    rw [intersectionHomotopyEquiv_inr, chartV_intersection_inr]
    rfl
end Mathoverflow1973
