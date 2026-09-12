/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib

/-!
# The unreduced suspension of a topological space

The unreduced suspension `Suspension.topSus X` of a nonempty topological space `X` is the quotient
of `[0,1] × X` that collapses `0 × X` to the south pole and `1 × X` to the north pole:

* `Suspension.topSus (X : Type*) [TopologicalSpace X] : Type*` — the suspension
  topological space (a `TopologicalSpace` instance via the quotient topology), with
  `suspensionUnitSphereHomeomorph`-style presentations and the north/south pole API.

This file is pure topology: it is consumed by the suspension isomorphism in singular homology
(`Lib/AlgebraicTopology/SingularHomology/Suspension.lean`).

## Outline of the construction

1. *The quotient.*  `suspensionSetoid` on `unitInterval × X` collapses the two ends;
   `Suspension.topSus X := Quotient (suspensionSetoid X)` with the quotient topology
   (`instSuspensionTopologicalSpace`-style local instance).
2. *Poles and levels.*  The south and north pole points, and the level decomposition of the
   suspension into the cylinder `0 < t < 1` (`middleBand`-style lemmas).
3. *Topological properties.*  Continuity of the quotient map and of the pole inclusions;
   compactness of the suspension of a compact space (`Suspension.suspension_compactSpace`).

## Main definitions and results

* `Suspension.topSus` : the unreduced suspension, a topological space.
* `Suspension.topSus.suspension_compactSpace` : compactness.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §0 (unreduced suspension)

## Tags

suspension, quotient topology
-/


set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

@[expose] public noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

def Suspension.suspensionSetoid (X : Type*) : Setoid (unitInterval × X)
    where
  r p q := p.1 = q.1 ∧ (p.1 = 0 ∨ p.1 = 1 ∨ p.2 = q.2)
  iseqv :=
    { refl := fun _ => ⟨rfl, Or.inr (Or.inr rfl)⟩
      symm := by
        rintro p q ⟨ht, h | h | h⟩
        · exact ⟨ht.symm, Or.inl (ht.symm.trans h)⟩
        · exact ⟨ht.symm, Or.inr (Or.inl (ht.symm.trans h))⟩
        · exact ⟨ht.symm, Or.inr (Or.inr h.symm)⟩
      trans := by
        rintro p q r ⟨hpq, hp | hp | hp⟩ ⟨hqr, hq⟩
        · exact ⟨hpq.trans hqr, Or.inl hp⟩
        · exact ⟨hpq.trans hqr, Or.inr (Or.inl hp)⟩
        · rcases hq with hq | hq | hq
          · exact ⟨hpq.trans hqr, Or.inl (hpq.trans hq)⟩
          · exact ⟨hpq.trans hqr, Or.inr (Or.inl (hpq.trans hq))⟩
          · exact ⟨hpq.trans hqr, Or.inr (Or.inr (hp.trans hq))⟩ }

def Suspension.topSus (X : Type*) :=
  Quotient (suspensionSetoid X)

instance Suspension.instLocal1 {X : Type*} [TopologicalSpace X] :
    TopologicalSpace (Suspension.topSus X) :=
  inferInstanceAs (TopologicalSpace (Quotient (suspensionSetoid X)))

def Suspension.topSus.mk {X : Type*} (t : unitInterval) (x : X) :
    Suspension.topSus X :=
  Quotient.mk (Suspension.suspensionSetoid X) (t, x)

theorem Suspension.topSus.mk_eq_mk_iff {X : Type*} (t s : unitInterval) (x y : X) :
    Suspension.topSus.mk t x = Suspension.topSus.mk s y ↔
      t = s ∧ (t = 0 ∨ t = 1 ∨ x = y) :=
  Quotient.eq

theorem Suspension.topSus.mk_surjective {X : Type*} :
    Function.Surjective (fun p : unitInterval × X => Suspension.topSus.mk p.1 p.2) :=
  Quotient.mk_surjective

theorem Suspension.topSus.isQuotientMap_mk {X : Type*} [TopologicalSpace X] :
    Topology.IsQuotientMap
      (fun p : unitInterval × X => Suspension.topSus.mk p.1 p.2) :=
  isQuotientMap_quotient_mk'

@[continuity, fun_prop]
theorem Suspension.topSus.continuous_mk {X : Type*} [TopologicalSpace X] :
    Continuous (fun p : unitInterval × X => Suspension.topSus.mk p.1 p.2) :=
  isQuotientMap_mk.continuous

def Suspension.topSus.height {X : Type*} :
    Suspension.topSus X → unitInterval :=
  Quotient.lift Prod.fst (fun _ _ h => h.1)

@[continuity, fun_prop]
theorem Suspension.topSus.continuous_height {X : Type*} [TopologicalSpace X] :
    Continuous (height : Suspension.topSus X → _) :=
  isQuotientMap_mk.continuous_iff.mpr continuous_fst

@[continuity, fun_prop]
theorem Suspension.topSus.continuous_realHeight {X : Type*} [TopologicalSpace X] :
    Continuous (fun p : Suspension.topSus X => (height p : ℝ)) :=
  continuous_subtype_val.comp continuous_height

theorem Suspension.topSus.mk_zero_eq {X : Type*} (x y : X) :
    Suspension.topSus.mk 0 x = Suspension.topSus.mk 0 y :=
  Quotient.sound ⟨rfl, Or.inl rfl⟩

theorem Suspension.topSus.mk_one_eq {X : Type*} (x y : X) :
    Suspension.topSus.mk 1 x = Suspension.topSus.mk 1 y :=
  Quotient.sound ⟨rfl, Or.inr (Or.inl rfl)⟩

def Suspension.topSus.northOpen {X : Type*} :
    Set (Suspension.topSus X) :=
  {p | (height p : ℝ) < 3 / 4}

def Suspension.topSus.southOpen {X : Type*} :
    Set (Suspension.topSus X) :=
  {p | 1 / 4 < (height p : ℝ)}

@[simp]
theorem Suspension.topSus.mem_northOpen {X : Type*}
    (p : Suspension.topSus X) : p ∈ northOpen ↔ (height p : ℝ) < 3 / 4 :=
  Iff.rfl

@[simp]
theorem Suspension.topSus.mem_southOpen {X : Type*}
    (p : Suspension.topSus X) : p ∈ southOpen ↔ 1 / 4 < (height p : ℝ) :=
  Iff.rfl

theorem Suspension.topSus.northOpen_isOpen {X : Type*} [TopologicalSpace X] :
    IsOpen (northOpen : Set (Suspension.topSus X)) :=
  isOpen_lt continuous_realHeight continuous_const

theorem Suspension.topSus.southOpen_isOpen {X : Type*} [TopologicalSpace X] :
    IsOpen (southOpen : Set (Suspension.topSus X)) :=
  isOpen_lt continuous_const continuous_realHeight

theorem Suspension.topSus.open_cover {X : Type*} :
    (northOpen ∪ southOpen : Set (Suspension.topSus X)) = Set.univ := by
  ext p
  simp only [Set.mem_union, mem_northOpen, mem_southOpen, Set.mem_univ, iff_true]
  by_cases h : (height p : ℝ) < 3 / 4
  · exact Or.inl h
  · exact Or.inr (by linarith)

def Suspension.topSus.north {X : Type*} [Nonempty X] :
    Suspension.topSus X :=
  Suspension.topSus.mk 0 (Classical.choice ‹Nonempty X›)

def Suspension.topSus.south {X : Type*} [Nonempty X] :
    Suspension.topSus X :=
  Suspension.topSus.mk 1 (Classical.choice ‹Nonempty X›)

@[simp]
theorem Suspension.topSus.mk_zero {X : Type*} [Nonempty X] (x : X) :
    Suspension.topSus.mk 0 x = north :=
  mk_zero_eq _ _

@[simp]
theorem Suspension.topSus.mk_one {X : Type*} [Nonempty X] (x : X) :
    Suspension.topSus.mk 1 x = south :=
  mk_one_eq _ _

theorem Suspension.topSus.north_mem_northOpen {X : Type*} [Nonempty X] :
    (north : Suspension.topSus X) ∈ northOpen := by
  change (0 : ℝ) < 3 / 4
  norm_num

theorem Suspension.topSus.south_mem_southOpen {X : Type*} [Nonempty X] :
    (south : Suspension.topSus X) ∈ southOpen := by
  change (1 / 4 : ℝ) < 1
  norm_num

instance Suspension.topSus.instLocal1 {X : Type*} [Nonempty X] :
    Nonempty (Suspension.topSus X) :=
  ⟨north⟩

abbrev Suspension.topSus.middleBand (X : Type*) :=
  (northOpen ∩ southOpen : Set (Suspension.topSus X))

abbrev Suspension.topSus.middleCylinder (X : Type*) :=
  (fun p : unitInterval × X => Suspension.topSus.mk p.1 p.2) ⁻¹' middleBand X

theorem Suspension.topSus.middleBand_isOpen {X : Type*} [TopologicalSpace X] :
    IsOpen (middleBand X) :=
  northOpen_isOpen.inter southOpen_isOpen

theorem Suspension.topSus.middleCylinder_height_mo1973_4378 {X : Type*}
    (p : middleCylinder X) : (1 / 4 : ℝ) < (p.1.1 : ℝ) ∧ (p.1.1 : ℝ) < 3 / 4 :=
  ⟨p.2.2, p.2.1⟩

theorem Suspension.topSus.middleBand_restrict_injective {X : Type*} :
    Function.Injective
      ((middleBand X).restrictPreimage
        (fun p : unitInterval × X => Suspension.topSus.mk p.1 p.2)) := by
  intro p q h
  have hmk :
    Suspension.topSus.mk p.1.1 p.1.2 =
      Suspension.topSus.mk q.1.1 q.1.2 :=
    congrArg Subtype.val h
  obtain ⟨ht, hx⟩ := (mk_eq_mk_iff _ _ _ _).mp hmk
  have hp := middleCylinder_height_mo1973_4378 p
  have hx' : p.1.2 = q.1.2 := by
    rcases hx with h0 | h1 | hx
    · have hz : (p.1.1 : ℝ) = 0 := congrArg Subtype.val h0
      linarith [hp.1]
    · have hz : (p.1.1 : ℝ) = 1 := congrArg Subtype.val h1
      linarith [hp.2]
    · exact hx
  exact Subtype.ext (Prod.ext ht hx')

def Suspension.topSus.middleBandQuotientHomeomorph {X : Type*} [TopologicalSpace X] :
    middleCylinder X ≃ₜ middleBand X :=
  ((isHomeomorph_iff_isQuotientMap_injective).mpr
        ⟨isQuotientMap_mk.restrictPreimage_isOpen middleBand_isOpen,
          middleBand_restrict_injective⟩).homeomorph
    _

def Suspension.topSus.middleCylinderHomeomorph {X : Type*} [TopologicalSpace X] :
    middleCylinder X ≃ₜ (Set.Ioo (1 / 4 : ℝ) (3 / 4) × X)
    where
  toFun p := (⟨p.1.1, middleCylinder_height_mo1973_4378 p⟩, p.1.2)
  invFun p := ⟨(⟨p.1, by constructor <;> linarith [p.1.2.1, p.1.2.2]⟩, p.2), p.1.2.2, p.1.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)
    · exact continuous_snd.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact continuous_subtype_val.comp continuous_fst
    · exact continuous_snd

def Suspension.topSus.middleBandHomeomorph {X : Type*} [TopologicalSpace X] :
    middleBand X ≃ₜ (Set.Ioo (1 / 4 : ℝ) (3 / 4) × X) :=
  middleBandQuotientHomeomorph.symm.trans middleCylinderHomeomorph

instance Suspension.topSus.middleInterval_contractibleSpace :
    ContractibleSpace (Set.Ioo (1 / 4 : ℝ) (3 / 4)) :=
  (convex_Ioo (1 / 4 : ℝ) (3 / 4)).contractibleSpace ⟨1 / 2, by norm_num⟩

def Suspension.topSus.middleBandHomotopyEquiv {X : Type*} [TopologicalSpace X] :
    middleBand X ≃ₕ X :=
  middleBandHomeomorph.toHomotopyEquiv.trans
    (((Classical.choice (ContractibleSpace.hequiv_unit (Set.Ioo (1 / 4 : ℝ) (3 / 4)))).prodCongr
          (ContinuousMap.HomotopyEquiv.refl X)).trans
      (Homeomorph.uniqueProd Unit X).toHomotopyEquiv)

theorem Suspension.topSus.joined_north {X : Type*} [TopologicalSpace X] [Nonempty X]
    (p : Suspension.topSus X) :
    Joined (north : Suspension.topSus X) p := by
  obtain ⟨⟨t, x⟩, rfl⟩ := mk_surjective p
  refine
    ⟨{  toFun := fun s : unitInterval => Suspension.topSus.mk (s * t) x
        continuous_toFun := by
          apply continuous_mk.comp (f := fun s : unitInterval => (s * t, x))
          apply Continuous.prodMk
          · apply Continuous.subtype_mk
            exact continuous_subtype_val.mul continuous_const
          · exact continuous_const
        source' := by simp
        target' := by simp }⟩

instance Suspension.topSus.suspension_pathConnectedSpace {X : Type*}
    [TopologicalSpace X] [Nonempty X] : PathConnectedSpace (Suspension.topSus X)
    where
  nonempty := inferInstance
  joined p q := (joined_north p).symm.trans (joined_north q)

def Suspension.topSus.liftFromSurjection_mo1973_4391 {A B S Z : Type*}
    (q : A → B) (hq : Function.Surjective q) (F : S × A → Z) (p : S × B) : Z :=
  F (p.1, Function.surjInv hq p.2)

theorem Suspension.topSus.liftFromSurjection_comp_mo1973_4392
    {A B S Z : Type*} (q : A → B) (hq : Function.Surjective q) (F : S × A → Z)
    (hF : ∀ s a b, q a = q b → F (s, a) = F (s, b)) (s : S) (a : A) :
    liftFromSurjection_mo1973_4391 q hq F (s, q a) = F (s, a) :=
  hF s _ _ (Function.surjInv_eq hq (q a))

theorem Suspension.topSus.liftFromSurjection_continuous_mo1973_4393
    {A B S Z : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace S]
    [TopologicalSpace Z] [LocallyCompactSpace S] (q : A → B) (hq : Topology.IsQuotientMap q)
    (F : S × A → Z) (hF : ∀ s a b, q a = q b → F (s, a) = F (s, b)) (hcont : Continuous F) :
    Continuous (liftFromSurjection_mo1973_4391 q hq.surjective F) := by
  apply hq.continuous_lift_prod_right
  convert hcont using 1
  funext p
  exact liftFromSurjection_comp_mo1973_4392 q hq.surjective F hF p.1 p.2

abbrev Suspension.topSus.NorthCylinder_mo1973_4394 (X : Type*)
    [TopologicalSpace X] :=
  (fun p : unitInterval × X => Suspension.topSus.mk p.1 p.2) ⁻¹' northOpen

def Suspension.topSus.northProjection_mo1973_4395 {X : Type*}
    [TopologicalSpace X] :
    NorthCylinder_mo1973_4394 X → (northOpen : Set (Suspension.topSus X)) :=
  northOpen.restrictPreimage
    (fun p : unitInterval × X => Suspension.topSus.mk p.1 p.2)

theorem Suspension.topSus.northProjection_isQuotientMap_mo1973_4396
    {X : Type*} [TopologicalSpace X] :
    Topology.IsQuotientMap (northProjection_mo1973_4395 (X := X)) :=
  isQuotientMap_mk.restrictPreimage_isOpen northOpen_isOpen

def Suspension.topSus.northCylinderContraction_mo1973_4397 {X : Type*}
    [TopologicalSpace X] (p : unitInterval × NorthCylinder_mo1973_4394 X) :
    (northOpen : Set (Suspension.topSus X)) :=
  ⟨Suspension.topSus.mk (unitInterval.symm p.1 * p.2.1.1) p.2.1.2,
    by
    change ((unitInterval.symm p.1 * p.2.1.1 : unitInterval) : ℝ) < 3 / 4
    exact lt_of_le_of_lt unitInterval.mul_le_right p.2.2⟩

theorem Suspension.topSus.northCylinderContraction_respects_mo1973_4398
    {X : Type*} [TopologicalSpace X] (s : unitInterval) (a b : NorthCylinder_mo1973_4394 X)
    (h : northProjection_mo1973_4395 a = northProjection_mo1973_4395 b) :
    northCylinderContraction_mo1973_4397 (s, a) = northCylinderContraction_mo1973_4397 (s, b) := by
  apply Subtype.ext
  have hab :
    Suspension.topSus.mk a.1.1 a.1.2 =
      Suspension.topSus.mk b.1.1 b.1.2 :=
    congrArg Subtype.val h
  rcases (mk_eq_mk_iff _ _ _ _).mp hab with ⟨ht, hzero | hone | hx⟩
  · apply (mk_eq_mk_iff _ _ _ _).mpr
    exact
      ⟨congrArg (fun t => unitInterval.symm s * t) ht,
        Or.inl (by rw [hzero, MulZeroClass.mul_zero])⟩
  · have ha : (a.1.1 : ℝ) < 3 / 4 := a.2
    rw [hone] at ha
    norm_num at ha
  · change
      Suspension.topSus.mk (unitInterval.symm s * a.1.1) a.1.2 =
        Suspension.topSus.mk (unitInterval.symm s * b.1.1) b.1.2
    rw [ht, hx]

theorem Suspension.topSus.northCylinderContraction_continuous_mo1973_4399
    {X : Type*} [TopologicalSpace X] :
    Continuous (northCylinderContraction_mo1973_4397 (X := X)) := by
  apply Continuous.subtype_mk
  apply
    continuous_mk.comp (f := fun p : unitInterval × NorthCylinder_mo1973_4394 X =>
      (unitInterval.symm p.1 * p.2.1.1, p.2.1.2))
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    exact
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (continuous_subtype_val.comp
          (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)))
  · exact continuous_snd.comp (continuous_subtype_val.comp continuous_snd)

def Suspension.topSus.northContract_mo1973_4400 {X : Type*}
    [TopologicalSpace X] :
    unitInterval × (northOpen : Set (Suspension.topSus X)) →
      (northOpen : Set (Suspension.topSus X)) :=
  liftFromSurjection_mo1973_4391 northProjection_mo1973_4395
    northProjection_isQuotientMap_mo1973_4396.surjective northCylinderContraction_mo1973_4397

theorem Suspension.topSus.northContract_projection_mo1973_4401 {X : Type*}
    [TopologicalSpace X] (s : unitInterval) (a : NorthCylinder_mo1973_4394 X) :
    northContract_mo1973_4400 (s, northProjection_mo1973_4395 a) =
      northCylinderContraction_mo1973_4397 (s, a) :=
  liftFromSurjection_comp_mo1973_4392 _ _ _ northCylinderContraction_respects_mo1973_4398 s a

theorem Suspension.topSus.northContract_continuous_mo1973_4402 {X : Type*}
    [TopologicalSpace X] : Continuous (northContract_mo1973_4400 (X := X)) :=
  liftFromSurjection_continuous_mo1973_4393 _ northProjection_isQuotientMap_mo1973_4396 _
    northCylinderContraction_respects_mo1973_4398 northCylinderContraction_continuous_mo1973_4399

def Suspension.topSus.northContraction {X : Type*} [TopologicalSpace X]
    [Nonempty X] :
    ContinuousMap.Homotopy (ContinuousMap.id (northOpen : Set (Suspension.topSus X)))
      (ContinuousMap.const _ ⟨north, north_mem_northOpen⟩)
    where
  toFun := northContract_mo1973_4400
  continuous_toFun := northContract_continuous_mo1973_4402
  map_zero_left
    q := by
    obtain ⟨a, rfl⟩ := northProjection_isQuotientMap_mo1973_4396.surjective q
    rw [northContract_projection_mo1973_4401]
    apply Subtype.ext
    change
      Suspension.topSus.mk (unitInterval.symm 0 * a.1.1) a.1.2 =
        Suspension.topSus.mk a.1.1 a.1.2
    simp
  map_one_left
    q := by
    obtain ⟨a, rfl⟩ := northProjection_isQuotientMap_mo1973_4396.surjective q
    rw [northContract_projection_mo1973_4401]
    apply Subtype.ext
    change Suspension.topSus.mk (unitInterval.symm 1 * a.1.1) a.1.2 = north
    simp

instance Suspension.topSus.northOpen_contractibleSpace {X : Type*}
    [TopologicalSpace X] [Nonempty X] :
    ContractibleSpace (northOpen : Set (Suspension.topSus X)) :=
  (contractible_iff_id_nullhomotopic _).mpr ⟨⟨north, north_mem_northOpen⟩, ⟨northContraction⟩⟩

abbrev Suspension.topSus.SouthCylinder_mo1973_4406 (X : Type*)
    [TopologicalSpace X] :=
  (fun p : unitInterval × X => Suspension.topSus.mk p.1 p.2) ⁻¹' southOpen

def Suspension.topSus.southProjection_mo1973_4407 {X : Type*}
    [TopologicalSpace X] :
    SouthCylinder_mo1973_4406 X → (southOpen : Set (Suspension.topSus X)) :=
  southOpen.restrictPreimage
    (fun p : unitInterval × X => Suspension.topSus.mk p.1 p.2)

theorem Suspension.topSus.southProjection_isQuotientMap_mo1973_4408
    {X : Type*} [TopologicalSpace X] :
    Topology.IsQuotientMap (southProjection_mo1973_4407 (X := X)) :=
  isQuotientMap_mk.restrictPreimage_isOpen southOpen_isOpen

def Suspension.topSus.southCylinderContraction_mo1973_4409 {X : Type*}
    [TopologicalSpace X] (p : unitInterval × SouthCylinder_mo1973_4406 X) :
    (southOpen : Set (Suspension.topSus X)) :=
  ⟨Suspension.topSus.mk
      (unitInterval.symm (unitInterval.symm p.1 * unitInterval.symm p.2.1.1)) p.2.1.2,
    by
    change
      1 / 4 <
        ((unitInterval.symm (unitInterval.symm p.1 * unitInterval.symm p.2.1.1) : unitInterval) :
          ℝ)
    have hle : unitInterval.symm p.1 * unitInterval.symm p.2.1.1 ≤ unitInterval.symm p.2.1.1 :=
      unitInterval.mul_le_right
    have hbound :
      p.2.1.1 ≤ unitInterval.symm (unitInterval.symm p.1 * unitInterval.symm p.2.1.1) :=
      unitInterval.le_symm_comm.mpr hle
    exact lt_of_lt_of_le p.2.2 hbound⟩

theorem Suspension.topSus.southCylinderContraction_respects_mo1973_4410
    {X : Type*} [TopologicalSpace X] (s : unitInterval) (a b : SouthCylinder_mo1973_4406 X)
    (h : southProjection_mo1973_4407 a = southProjection_mo1973_4407 b) :
    southCylinderContraction_mo1973_4409 (s, a) = southCylinderContraction_mo1973_4409 (s, b) := by
  apply Subtype.ext
  have hab :
    Suspension.topSus.mk a.1.1 a.1.2 =
      Suspension.topSus.mk b.1.1 b.1.2 :=
    congrArg Subtype.val h
  rcases (mk_eq_mk_iff _ _ _ _).mp hab with ⟨ht, hzero | hone | hx⟩
  · have ha : 1 / 4 < (a.1.1 : ℝ) := a.2
    rw [hzero] at ha
    norm_num at ha
  · apply (mk_eq_mk_iff _ _ _ _).mpr
    refine
      ⟨congrArg (fun t => unitInterval.symm (unitInterval.symm s * unitInterval.symm t)) ht,
        Or.inr (Or.inl ?_)⟩
    simp [hone]
  · change
      Suspension.topSus.mk
          (unitInterval.symm (unitInterval.symm s * unitInterval.symm a.1.1)) a.1.2 =
        Suspension.topSus.mk
          (unitInterval.symm (unitInterval.symm s * unitInterval.symm b.1.1)) b.1.2
    rw [ht, hx]

theorem Suspension.topSus.southCylinderContraction_continuous_mo1973_4411
    {X : Type*} [TopologicalSpace X] :
    Continuous (southCylinderContraction_mo1973_4409 (X := X)) := by
  apply Continuous.subtype_mk
  apply
    continuous_mk.comp (f := fun p : unitInterval × SouthCylinder_mo1973_4406 X =>
      (unitInterval.symm (unitInterval.symm p.1 * unitInterval.symm p.2.1.1), p.2.1.2))
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    exact
      continuous_const.sub
        ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
          (continuous_const.sub
            (continuous_subtype_val.comp
              (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)))))
  · exact continuous_snd.comp (continuous_subtype_val.comp continuous_snd)

def Suspension.topSus.southContract_mo1973_4412 {X : Type*}
    [TopologicalSpace X] :
    unitInterval × (southOpen : Set (Suspension.topSus X)) →
      (southOpen : Set (Suspension.topSus X)) :=
  liftFromSurjection_mo1973_4391 southProjection_mo1973_4407
    southProjection_isQuotientMap_mo1973_4408.surjective southCylinderContraction_mo1973_4409

theorem Suspension.topSus.southContract_projection_mo1973_4413 {X : Type*}
    [TopologicalSpace X] (s : unitInterval) (a : SouthCylinder_mo1973_4406 X) :
    southContract_mo1973_4412 (s, southProjection_mo1973_4407 a) =
      southCylinderContraction_mo1973_4409 (s, a) :=
  liftFromSurjection_comp_mo1973_4392 _ _ _ southCylinderContraction_respects_mo1973_4410 s a

theorem Suspension.topSus.southContract_continuous_mo1973_4414 {X : Type*}
    [TopologicalSpace X] : Continuous (southContract_mo1973_4412 (X := X)) :=
  liftFromSurjection_continuous_mo1973_4393 _ southProjection_isQuotientMap_mo1973_4408 _
    southCylinderContraction_respects_mo1973_4410 southCylinderContraction_continuous_mo1973_4411

def Suspension.topSus.southContraction {X : Type*} [TopologicalSpace X]
    [Nonempty X] :
    ContinuousMap.Homotopy (ContinuousMap.id (southOpen : Set (Suspension.topSus X)))
      (ContinuousMap.const _ ⟨south, south_mem_southOpen⟩)
    where
  toFun := southContract_mo1973_4412
  continuous_toFun := southContract_continuous_mo1973_4414
  map_zero_left
    q := by
    obtain ⟨a, rfl⟩ := southProjection_isQuotientMap_mo1973_4408.surjective q
    rw [southContract_projection_mo1973_4413]
    apply Subtype.ext
    change
      Suspension.topSus.mk
          (unitInterval.symm (unitInterval.symm 0 * unitInterval.symm a.1.1)) a.1.2 =
        Suspension.topSus.mk a.1.1 a.1.2
    simp
  map_one_left
    q := by
    obtain ⟨a, rfl⟩ := southProjection_isQuotientMap_mo1973_4408.surjective q
    rw [southContract_projection_mo1973_4413]
    apply Subtype.ext
    change
      Suspension.topSus.mk
          (unitInterval.symm (unitInterval.symm 1 * unitInterval.symm a.1.1)) a.1.2 =
        south
    simp

instance Suspension.topSus.southOpen_contractibleSpace {X : Type*}
    [TopologicalSpace X] [Nonempty X] :
    ContractibleSpace (southOpen : Set (Suspension.topSus X)) :=
  (contractible_iff_id_nullhomotopic _).mpr ⟨⟨south, south_mem_southOpen⟩, ⟨southContraction⟩⟩

@[simp]
theorem Suspension.topSus.middleBandHomotopyEquiv_apply {X : Type*}
    [TopologicalSpace X] (p : middleBand X) :
    middleBandHomotopyEquiv p = (middleBandHomeomorph p).2 :=
  rfl

instance Suspension.topSus.suspension_compactSpace {X : Type*} [TopologicalSpace X]
    [CompactSpace X] : CompactSpace (Suspension.topSus X) :=
  mk_surjective.compactSpace continuous_mk
end Mathoverflow1973
