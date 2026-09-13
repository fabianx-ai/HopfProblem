/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib

/-!
# The unreduced suspension of a topological space

The unreduced suspension `Suspension X` of a nonempty topological space `X` is the quotient
of `[0,1] × X` that collapses `0 × X` to the north pole and `1 × X` to the south pole:

* `Suspension (X : Type*) : Type*` — the suspension
  topological space (a `TopologicalSpace` instance via the quotient topology), with
  `suspensionUnitSphereHomeomorph`-style presentations and the north/south pole API.

This file is pure topology: it is consumed by the suspension isomorphism in singular homology
(`Lib/AlgebraicTopology/SingularHomology/Suspension.lean`).

## Outline of the construction

1. *The quotient.*  `suspensionSetoid` on `unitInterval × X` collapses the two ends;
   `Suspension X := Quotient (suspensionSetoid X)` with the quotient topology
   (`Suspension.instTopologicalSpace`).
2. *Poles and levels.*  The south and north pole points, and the level decomposition of the
   interior cylinder `0 < t < 1` and the overlap band `1 / 4 < t < 3 / 4`
   used by `middleBand`.
3. *Topological properties.*  Continuity of the quotient map and of the pole inclusions;
   compactness of the suspension of a compact space (`Suspension.suspension_compactSpace`).

## Main definitions and results

* `Suspension` : the unreduced suspension, a topological space.
* `Suspension.suspension_compactSpace` : compactness.

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

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-! ### The suspension type -/

/-- The setoid identifying each endpoint fiber of the interval cylinder to a point. -/
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

/-- The interval cylinder modulo collapse of each endpoint fiber to a point. -/
def Suspension (X : Type*) :=
  Quotient (Suspension.suspensionSetoid X)

/-- The suspension carries the quotient topology of the interval cylinder. -/
instance Suspension.instTopologicalSpace {X : Type*} [TopologicalSpace X] :
    TopologicalSpace (Suspension X) :=
  inferInstanceAs (TopologicalSpace (Quotient (suspensionSetoid X)))

/-- The class of an interval coordinate and a point in the suspension quotient. -/
def Suspension.mk {X : Type*} (t : unitInterval) (x : X) :
    Suspension X :=
  Quotient.mk (Suspension.suspensionSetoid X) (t, x)

/-- Two suspension classes are equal exactly when their interval coordinates agree and either that coordinate is an endpoint or their base points agree. -/
theorem Suspension.mk_eq_mk_iff {X : Type*} (t s : unitInterval) (x y : X) :
    Suspension.mk t x = Suspension.mk s y ↔
      t = s ∧ (t = 0 ∨ t = 1 ∨ x = y) :=
  Quotient.eq

/-- Every suspension point is the class of an interval coordinate and a base point. -/
theorem Suspension.mk_surjective {X : Type*} :
    Function.Surjective (fun p : unitInterval × X => Suspension.mk p.1 p.2) :=
  Quotient.mk_surjective

/-- The map `(t, x) ↦ mk t x` is a quotient map. -/
theorem Suspension.isQuotientMap_mk {X : Type*} [TopologicalSpace X] :
    Topology.IsQuotientMap
      (fun p : unitInterval × X => Suspension.mk p.1 p.2) :=
  isQuotientMap_quotient_mk'

/-- The map `(t, x) ↦ mk t x` is continuous. -/
@[continuity, fun_prop]
theorem Suspension.continuous_mk {X : Type*} [TopologicalSpace X] :
    Continuous (fun p : unitInterval × X => Suspension.mk p.1 p.2) :=
  isQuotientMap_mk.continuous

/-- The interval coordinate of a suspension point. -/
def Suspension.height {X : Type*} :
    Suspension X → unitInterval :=
  Quotient.lift Prod.fst (fun _ _ h => h.1)

/-- The height function is continuous. -/
@[continuity, fun_prop]
theorem Suspension.continuous_height {X : Type*} [TopologicalSpace X] :
    Continuous (height : Suspension X → _) :=
  isQuotientMap_mk.continuous_iff.mpr continuous_fst

/-- The real-valued height is continuous. -/
@[continuity, fun_prop]
theorem Suspension.continuous_realHeight {X : Type*} [TopologicalSpace X] :
    Continuous (fun p : Suspension X => (height p : ℝ)) :=
  continuous_subtype_val.comp continuous_height

/-- All points at height `0` collapse to the north pole. -/
theorem Suspension.mk_zero_eq {X : Type*} (x y : X) :
    Suspension.mk 0 x = Suspension.mk 0 y :=
  Quotient.sound ⟨rfl, Or.inl rfl⟩

/-- All points at height `1` collapse to the south pole. -/
theorem Suspension.mk_one_eq {X : Type*} (x y : X) :
    Suspension.mk 1 x = Suspension.mk 1 y :=
  Quotient.sound ⟨rfl, Or.inr (Or.inl rfl)⟩

/-! ### The two-open cover -/

/-- The open northern hemisphere `t < 3/4` of the suspension. -/
def Suspension.northOpen {X : Type*} :
    Set (Suspension X) :=
  {p | (height p : ℝ) < 3 / 4}

/-- The open southern hemisphere `1/4 < t` of the suspension. -/
def Suspension.southOpen {X : Type*} :
    Set (Suspension X) :=
  {p | 1 / 4 < (height p : ℝ)}

/-- A point lies in the northern hemisphere below height `3/4`. -/
@[simp]
theorem Suspension.mem_northOpen {X : Type*}
    (p : Suspension X) : p ∈ northOpen ↔ (height p : ℝ) < 3 / 4 :=
  Iff.rfl

/-- A point lies in the southern hemisphere above height `1/4`. -/
@[simp]
theorem Suspension.mem_southOpen {X : Type*}
    (p : Suspension X) : p ∈ southOpen ↔ 1 / 4 < (height p : ℝ) :=
  Iff.rfl

/-- The northern hemisphere is open. -/
theorem Suspension.northOpen_isOpen {X : Type*} [TopologicalSpace X] :
    IsOpen (northOpen : Set (Suspension X)) :=
  isOpen_lt continuous_realHeight continuous_const

/-- The southern hemisphere is open. -/
theorem Suspension.southOpen_isOpen {X : Type*} [TopologicalSpace X] :
    IsOpen (southOpen : Set (Suspension X)) :=
  isOpen_lt continuous_const continuous_realHeight

/-- The two hemispheres cover the suspension. -/
theorem Suspension.open_cover {X : Type*} :
    (northOpen ∪ southOpen : Set (Suspension X)) = Set.univ := by
  ext p
  simp only [Set.mem_union, mem_northOpen, mem_southOpen, Set.mem_univ, iff_true]
  by_cases h : (height p : ℝ) < 3 / 4
  · exact Or.inl h
  · exact Or.inr (by linarith)

/-- The north pole of the suspension. -/
def Suspension.north {X : Type*} [Nonempty X] :
    Suspension X :=
  Suspension.mk 0 (Classical.choice ‹Nonempty X›)

/-- The south pole of the suspension. -/
def Suspension.south {X : Type*} [Nonempty X] :
    Suspension X :=
  Suspension.mk 1 (Classical.choice ‹Nonempty X›)

/-- Height `0` is the north pole. -/
@[simp]
theorem Suspension.mk_zero {X : Type*} [Nonempty X] (x : X) :
    Suspension.mk 0 x = north :=
  mk_zero_eq _ _

/-- Height `1` is the south pole. -/
@[simp]
theorem Suspension.mk_one {X : Type*} [Nonempty X] (x : X) :
    Suspension.mk 1 x = south :=
  mk_one_eq _ _

/-- The north pole lies in the northern hemisphere. -/
theorem Suspension.north_mem_northOpen {X : Type*} [Nonempty X] :
    (north : Suspension X) ∈ northOpen := by
  change (0 : ℝ) < 3 / 4
  norm_num

/-- The south pole lies in the southern hemisphere. -/
theorem Suspension.south_mem_southOpen {X : Type*} [Nonempty X] :
    (south : Suspension X) ∈ southOpen := by
  change (1 / 4 : ℝ) < 1
  norm_num

/-- A point of the base gives a point of its suspension. -/
instance Suspension.instNonempty {X : Type*} [Nonempty X] :
    Nonempty (Suspension X) :=
  ⟨north⟩

/-! ### The middle band -/

/-- The overlap band `1/4 < t < 3/4` of the suspension. -/
abbrev Suspension.middleBand (X : Type*) :=
  (northOpen ∩ southOpen : Set (Suspension X))

/-- The corresponding band of the interval cylinder. -/
abbrev Suspension.middleCylinder (X : Type*) :=
  (fun p : unitInterval × X => Suspension.mk p.1 p.2) ⁻¹' middleBand X

/-- The middle band is open. -/
theorem Suspension.middleBand_isOpen {X : Type*} [TopologicalSpace X] :
    IsOpen (middleBand X) :=
  northOpen_isOpen.inter southOpen_isOpen

/-- Points of the middle cylinder have height between `1/4` and `3/4`. -/
theorem Suspension.middleCylinder_height {X : Type*}
    (p : middleCylinder X) : (1 / 4 : ℝ) < (p.1.1 : ℝ) ∧ (p.1.1 : ℝ) < 3 / 4 :=
  ⟨p.2.2, p.2.1⟩

/-- The quotient map is injective on the middle cylinder. -/
theorem Suspension.middleBand_restrict_injective {X : Type*} :
    Function.Injective
      ((middleBand X).restrictPreimage
        (fun p : unitInterval × X => Suspension.mk p.1 p.2)) := by
  intro p q h
  have hmk :
    Suspension.mk p.1.1 p.1.2 =
      Suspension.mk q.1.1 q.1.2 :=
    congrArg Subtype.val h
  obtain ⟨ht, hx⟩ := (mk_eq_mk_iff _ _ _ _).mp hmk
  have hp := middleCylinder_height p
  have hx' : p.1.2 = q.1.2 := by
    rcases hx with h0 | h1 | hx
    · have hz : (p.1.1 : ℝ) = 0 := congrArg Subtype.val h0
      linarith [hp.1]
    · have hz : (p.1.1 : ℝ) = 1 := congrArg Subtype.val h1
      linarith [hp.2]
    · exact hx
  exact Subtype.ext (Prod.ext ht hx')

/-- The middle band is homeomorphic to the middle cylinder. -/
def Suspension.middleBandQuotientHomeomorph {X : Type*} [TopologicalSpace X] :
    middleCylinder X ≃ₜ middleBand X :=
  ((isHomeomorph_iff_isQuotientMap_injective).mpr
        ⟨isQuotientMap_mk.restrictPreimage_isOpen middleBand_isOpen,
          middleBand_restrict_injective⟩).homeomorph
    _

/-- The middle cylinder is the product `Ioo (1/4) (3/4) × X`. -/
def Suspension.middleCylinderHomeomorph {X : Type*} [TopologicalSpace X] :
    middleCylinder X ≃ₜ (Set.Ioo (1 / 4 : ℝ) (3 / 4) × X)
    where
  toFun p := (⟨p.1.1, middleCylinder_height p⟩, p.1.2)
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

/-- The middle band is homeomorphic to `Ioo (1/4) (3/4) × X`. -/
def Suspension.middleBandHomeomorph {X : Type*} [TopologicalSpace X] :
    middleBand X ≃ₜ (Set.Ioo (1 / 4 : ℝ) (3 / 4) × X) :=
  middleBandQuotientHomeomorph.symm.trans middleCylinderHomeomorph

/-- The open interval `(1/4, 3/4)` is contractible. -/
instance Suspension.middleInterval_contractibleSpace :
    ContractibleSpace (Set.Ioo (1 / 4 : ℝ) (3 / 4)) :=
  (convex_Ioo (1 / 4 : ℝ) (3 / 4)).contractibleSpace ⟨1 / 2, by norm_num⟩

/-- The middle band is homotopy equivalent to the base. -/
def Suspension.middleBandHomotopyEquiv {X : Type*} [TopologicalSpace X] :
    middleBand X ≃ₕ X :=
  middleBandHomeomorph.toHomotopyEquiv.trans
    (((Classical.choice (ContractibleSpace.hequiv_unit (Set.Ioo (1 / 4 : ℝ) (3 / 4)))).prodCongr
          (ContinuousMap.HomotopyEquiv.refl X)).trans
      (Homeomorph.uniqueProd Unit X).toHomotopyEquiv)

/-- Every suspension point is joined to the north pole. -/
theorem Suspension.joined_north {X : Type*} [TopologicalSpace X] [Nonempty X]
    (p : Suspension X) :
    Joined (north : Suspension X) p := by
  obtain ⟨⟨t, x⟩, rfl⟩ := mk_surjective p
  refine
    ⟨{  toFun := fun s : unitInterval => Suspension.mk (s * t) x
        continuous_toFun := by
          apply continuous_mk.comp (f := fun s : unitInterval => (s * t, x))
          apply Continuous.prodMk
          · apply Continuous.subtype_mk
            exact continuous_subtype_val.mul continuous_const
          · exact continuous_const
        source' := by simp
        target' := by simp }⟩

/-- The suspension of a nonempty space is path connected. -/
instance Suspension.suspension_pathConnectedSpace {X : Type*}
    [TopologicalSpace X] [Nonempty X] : PathConnectedSpace (Suspension X)
    where
  nonempty := inferInstance
  joined p q := (joined_north p).symm.trans (joined_north q)

/-! ### Lifting through a surjection -/

/-- A function defined through a surjection, using a chosen preimage. -/
def Suspension.liftFromSurjection {A B S Z : Type*}
    (q : A → B) (hq : Function.Surjective q) (F : S × A → Z) (p : S × B) : Z :=
  F (p.1, Function.surjInv hq p.2)

/-- The lifted function computes on genuine preimages. -/
theorem Suspension.liftFromSurjection_comp
    {A B S Z : Type*} (q : A → B) (hq : Function.Surjective q) (F : S × A → Z)
    (hF : ∀ s a b, q a = q b → F (s, a) = F (s, b)) (s : S) (a : A) :
    liftFromSurjection q hq F (s, q a) = F (s, a) :=
  hF s _ _ (Function.surjInv_eq hq (q a))

/-- The lift through a quotient map is continuous when compatible and the parameter space is locally compact. -/
theorem Suspension.liftFromSurjection_continuous
    {A B S Z : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace S]
    [TopologicalSpace Z] [LocallyCompactSpace S] (q : A → B) (hq : Topology.IsQuotientMap q)
    (F : S × A → Z) (hF : ∀ s a b, q a = q b → F (s, a) = F (s, b)) (hcont : Continuous F) :
    Continuous (liftFromSurjection q hq.surjective F) := by
  apply hq.continuous_lift_prod_right
  convert hcont using 1
  funext p
  exact liftFromSurjection_comp q hq.surjective F hF p.1 p.2

/-! ### Contractibility of the hemispheres -/

/-- The part of the cylinder below height `3/4`. -/
abbrev Suspension.NorthCylinder (X : Type*)
    [TopologicalSpace X] :=
  (fun p : unitInterval × X => Suspension.mk p.1 p.2) ⁻¹' northOpen

/-- The quotient map from the northern cylinder to the northern hemisphere. -/
def Suspension.northProjection {X : Type*}
    [TopologicalSpace X] :
    NorthCylinder X → (northOpen : Set (Suspension X)) :=
  northOpen.restrictPreimage
    (fun p : unitInterval × X => Suspension.mk p.1 p.2)

/-- The northern projection is a quotient map. -/
theorem Suspension.northProjection_isQuotientMap
    {X : Type*} [TopologicalSpace X] :
    Topology.IsQuotientMap (northProjection (X := X)) :=
  isQuotientMap_mk.restrictPreimage_isOpen northOpen_isOpen

/-- The straight-line contraction of the northern cylinder toward the pole. -/
def Suspension.northCylinderContraction {X : Type*}
    [TopologicalSpace X] (p : unitInterval × NorthCylinder X) :
    (northOpen : Set (Suspension X)) :=
  ⟨Suspension.mk (unitInterval.symm p.1 * p.2.1.1) p.2.1.2,
    by
    change ((unitInterval.symm p.1 * p.2.1.1 : unitInterval) : ℝ) < 3 / 4
    exact lt_of_le_of_lt unitInterval.mul_le_right p.2.2⟩

/-- The northern contraction respects the quotient relation. -/
theorem Suspension.northCylinderContraction_respects
    {X : Type*} [TopologicalSpace X] (s : unitInterval) (a b : NorthCylinder X)
    (h : northProjection a = northProjection b) :
    northCylinderContraction (s, a) = northCylinderContraction (s, b) := by
  apply Subtype.ext
  have hab :
    Suspension.mk a.1.1 a.1.2 =
      Suspension.mk b.1.1 b.1.2 :=
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
      Suspension.mk (unitInterval.symm s * a.1.1) a.1.2 =
        Suspension.mk (unitInterval.symm s * b.1.1) b.1.2
    rw [ht, hx]

/-- The northern contraction is continuous. -/
theorem Suspension.northCylinderContraction_continuous
    {X : Type*} [TopologicalSpace X] :
    Continuous (northCylinderContraction (X := X)) := by
  apply Continuous.subtype_mk
  apply
    continuous_mk.comp (f := fun p : unitInterval × NorthCylinder X =>
      (unitInterval.symm p.1 * p.2.1.1, p.2.1.2))
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    exact
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (continuous_subtype_val.comp
          (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)))
  · exact continuous_snd.comp (continuous_subtype_val.comp continuous_snd)

/-- The contraction of the northern hemisphere toward the north pole. -/
def Suspension.northContract {X : Type*}
    [TopologicalSpace X] :
    unitInterval × (northOpen : Set (Suspension X)) →
      (northOpen : Set (Suspension X)) :=
  liftFromSurjection northProjection
    northProjection_isQuotientMap.surjective northCylinderContraction

/-- The northern contraction computes through the cylinder contraction. -/
theorem Suspension.northContract_projection {X : Type*}
    [TopologicalSpace X] (s : unitInterval) (a : NorthCylinder X) :
    northContract (s, northProjection a) =
      northCylinderContraction (s, a) :=
  liftFromSurjection_comp _ _ _ northCylinderContraction_respects s a

/-- The northern contraction is continuous. -/
theorem Suspension.northContract_continuous {X : Type*}
    [TopologicalSpace X] : Continuous (northContract (X := X)) :=
  liftFromSurjection_continuous _ northProjection_isQuotientMap _
    northCylinderContraction_respects northCylinderContraction_continuous

/-- The homotopy contracting the northern hemisphere to the north pole. -/
def Suspension.northContraction {X : Type*} [TopologicalSpace X]
    [Nonempty X] :
    ContinuousMap.Homotopy (ContinuousMap.id (northOpen : Set (Suspension X)))
      (ContinuousMap.const _ ⟨north, north_mem_northOpen⟩)
    where
  toFun := northContract
  continuous_toFun := northContract_continuous
  map_zero_left
    q := by
    obtain ⟨a, rfl⟩ := northProjection_isQuotientMap.surjective q
    rw [northContract_projection]
    apply Subtype.ext
    change
      Suspension.mk (unitInterval.symm 0 * a.1.1) a.1.2 =
        Suspension.mk a.1.1 a.1.2
    simp
  map_one_left
    q := by
    obtain ⟨a, rfl⟩ := northProjection_isQuotientMap.surjective q
    rw [northContract_projection]
    apply Subtype.ext
    change Suspension.mk (unitInterval.symm 1 * a.1.1) a.1.2 = north
    simp

/-- The northern hemisphere is contractible. -/
instance Suspension.northOpen_contractibleSpace {X : Type*}
    [TopologicalSpace X] [Nonempty X] :
    ContractibleSpace (northOpen : Set (Suspension X)) :=
  (contractible_iff_id_nullhomotopic _).mpr ⟨⟨north, north_mem_northOpen⟩, ⟨northContraction⟩⟩

/-- The part of the cylinder above height `1/4`. -/
abbrev Suspension.SouthCylinder (X : Type*)
    [TopologicalSpace X] :=
  (fun p : unitInterval × X => Suspension.mk p.1 p.2) ⁻¹' southOpen

/-- The quotient map from the southern cylinder to the southern hemisphere. -/
def Suspension.southProjection {X : Type*}
    [TopologicalSpace X] :
    SouthCylinder X → (southOpen : Set (Suspension X)) :=
  southOpen.restrictPreimage
    (fun p : unitInterval × X => Suspension.mk p.1 p.2)

/-- The southern projection is a quotient map. -/
theorem Suspension.southProjection_isQuotientMap
    {X : Type*} [TopologicalSpace X] :
    Topology.IsQuotientMap (southProjection (X := X)) :=
  isQuotientMap_mk.restrictPreimage_isOpen southOpen_isOpen

/-- The straight-line contraction of the southern cylinder toward the pole. -/
def Suspension.southCylinderContraction {X : Type*}
    [TopologicalSpace X] (p : unitInterval × SouthCylinder X) :
    (southOpen : Set (Suspension X)) :=
  ⟨Suspension.mk
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

/-- The southern contraction respects the quotient relation. -/
theorem Suspension.southCylinderContraction_respects
    {X : Type*} [TopologicalSpace X] (s : unitInterval) (a b : SouthCylinder X)
    (h : southProjection a = southProjection b) :
    southCylinderContraction (s, a) = southCylinderContraction (s, b) := by
  apply Subtype.ext
  have hab :
    Suspension.mk a.1.1 a.1.2 =
      Suspension.mk b.1.1 b.1.2 :=
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
      Suspension.mk
          (unitInterval.symm (unitInterval.symm s * unitInterval.symm a.1.1)) a.1.2 =
        Suspension.mk
          (unitInterval.symm (unitInterval.symm s * unitInterval.symm b.1.1)) b.1.2
    rw [ht, hx]

/-- The southern contraction is continuous. -/
theorem Suspension.southCylinderContraction_continuous
    {X : Type*} [TopologicalSpace X] :
    Continuous (southCylinderContraction (X := X)) := by
  apply Continuous.subtype_mk
  apply
    continuous_mk.comp (f := fun p : unitInterval × SouthCylinder X =>
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

/-- The contraction of the southern hemisphere toward the south pole. -/
def Suspension.southContract {X : Type*}
    [TopologicalSpace X] :
    unitInterval × (southOpen : Set (Suspension X)) →
      (southOpen : Set (Suspension X)) :=
  liftFromSurjection southProjection
    southProjection_isQuotientMap.surjective southCylinderContraction

/-- The southern contraction computes through the cylinder contraction. -/
theorem Suspension.southContract_projection {X : Type*}
    [TopologicalSpace X] (s : unitInterval) (a : SouthCylinder X) :
    southContract (s, southProjection a) =
      southCylinderContraction (s, a) :=
  liftFromSurjection_comp _ _ _ southCylinderContraction_respects s a

/-- The southern contraction is continuous. -/
theorem Suspension.southContract_continuous {X : Type*}
    [TopologicalSpace X] : Continuous (southContract (X := X)) :=
  liftFromSurjection_continuous _ southProjection_isQuotientMap _
    southCylinderContraction_respects southCylinderContraction_continuous

/-- The homotopy contracting the southern hemisphere to the south pole. -/
def Suspension.southContraction {X : Type*} [TopologicalSpace X]
    [Nonempty X] :
    ContinuousMap.Homotopy (ContinuousMap.id (southOpen : Set (Suspension X)))
      (ContinuousMap.const _ ⟨south, south_mem_southOpen⟩)
    where
  toFun := southContract
  continuous_toFun := southContract_continuous
  map_zero_left
    q := by
    obtain ⟨a, rfl⟩ := southProjection_isQuotientMap.surjective q
    rw [southContract_projection]
    apply Subtype.ext
    change
      Suspension.mk
          (unitInterval.symm (unitInterval.symm 0 * unitInterval.symm a.1.1)) a.1.2 =
        Suspension.mk a.1.1 a.1.2
    simp
  map_one_left
    q := by
    obtain ⟨a, rfl⟩ := southProjection_isQuotientMap.surjective q
    rw [southContract_projection]
    apply Subtype.ext
    change
      Suspension.mk
          (unitInterval.symm (unitInterval.symm 1 * unitInterval.symm a.1.1)) a.1.2 =
        south
    simp

/-- The southern hemisphere is contractible. -/
instance Suspension.southOpen_contractibleSpace {X : Type*}
    [TopologicalSpace X] [Nonempty X] :
    ContractibleSpace (southOpen : Set (Suspension X)) :=
  (contractible_iff_id_nullhomotopic _).mpr ⟨⟨south, south_mem_southOpen⟩, ⟨southContraction⟩⟩

/-- The middle-band homotopy equivalence extracts the base point. -/
@[simp]
theorem Suspension.middleBandHomotopyEquiv_apply {X : Type*}
    [TopologicalSpace X] (p : middleBand X) :
    middleBandHomotopyEquiv p = (middleBandHomeomorph p).2 :=
  rfl

/-- The suspension of a compact space is compact. -/
instance Suspension.suspension_compactSpace {X : Type*} [TopologicalSpace X]
    [CompactSpace X] : CompactSpace (Suspension X) :=
  mk_surjective.compactSpace continuous_mk
