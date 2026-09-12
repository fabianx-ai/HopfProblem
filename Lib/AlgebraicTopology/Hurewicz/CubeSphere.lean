/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.Degree
import Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition
import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Lib.Topology.OnePointCollapse

set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

noncomputable section

namespace Mathoverflow1973

def OnePointCollapse.collapseLift {K X : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [TopologicalSpace X] (F : Set K) (hF : IsClosed F) (hne : F.Nonempty) (f : C(K, X)) (x : X)
    (hf : ∀ a ∈ F, f a = x) : C(OnePoint ↥Fᶜ, X) :=
  Topology.IsQuotientMap.lift (f := collapseMap F hF) (isQuotientMap_collapse F hF hne) f
    (by
      intro a b h
      rcases (collapse_eq_iff F a b).mp h with rfl | ⟨ha, hb⟩
      · rfl
      · exact (hf a ha).trans (hf b hb).symm)

@[simp]
theorem OnePointCollapse.collapseLift_comp {K X : Type*} [TopologicalSpace K] [CompactSpace K]
    [T2Space K] [TopologicalSpace X] (F : Set K) (hF : IsClosed F) (hne : F.Nonempty)
    (f : C(K, X)) (x : X) (hf : ∀ a ∈ F, f a = x) :
    (collapseLift F hF hne f x hf).comp (collapseMap F hF) = f :=
  Topology.IsQuotientMap.lift_comp (f := collapseMap F hF) (isQuotientMap_collapse F hF hne) f _

@[simp]
theorem OnePointCollapse.collapseLift_apply {K X : Type*} [TopologicalSpace K] [CompactSpace K]
    [T2Space K] [TopologicalSpace X] (F : Set K) (hF : IsClosed F) (hne : F.Nonempty)
    (f : C(K, X)) (x : X) (hf : ∀ a ∈ F, f a = x) (a : K) :
    collapseLift F hF hne f x hf (collapse F a) = f a :=
  ContinuousMap.congr_fun (collapseLift_comp F hF hne f x hf) a

abbrev SixSphereCube.OpenUnitInterval :=
  Set.Ioo (0 : ℝ) 1

def SixSphereCube.openUnitIntervalAffineOrderIso : OpenUnitInterval ≃o Set.Ioo (-1 : ℝ) 1
    where
  toFun t := ⟨2 * (t : ℝ) - 1, by constructor <;> linarith [t.property.1, t.property.2]⟩
  invFun t := ⟨((t : ℝ) + 1) / 2, by constructor <;> linarith [t.property.1, t.property.2]⟩
  left_inv
    t := by
    apply Subtype.ext
    change (2 * (t : ℝ) - 1 + 1) / 2 = (t : ℝ)
    ring
  right_inv
    t := by
    apply Subtype.ext
    change 2 * (((t : ℝ) + 1) / 2) - 1 = (t : ℝ)
    ring
  map_rel_iff' := by
    intro t s
    change 2 * (t : ℝ) - 1 ≤ 2 * (s : ℝ) - 1 ↔ (t : ℝ) ≤ (s : ℝ)
    constructor <;> intro h <;> linarith

def SixSphereCube.openUnitIntervalHomeomorph : OpenUnitInterval ≃ₜ ℝ :=
  openUnitIntervalAffineOrderIso.toHomeomorph.trans (orderIsoIooNegOneOne ℝ).toHomeomorph.symm

abbrev SixSphereCube.CubeInteriorN (n : ℕ) :=
  { u : Fin n → (unitInterval) // u ∉ Cube.boundary (Fin n) }

theorem SixSphereCube.not_mem_cubeBoundary_iff {n : ℕ} (u : Fin n → (unitInterval)) :
    u ∉ Cube.boundary (Fin n) ↔ ∀ i, 0 < (u i : ℝ) ∧ (u i : ℝ) < 1 := by
  simp only [Cube.boundary, Set.mem_ofPred_eq, not_exists, not_or, unitInterval.coe_pos,
    unitInterval.coe_lt_one, unitInterval.pos_iff_ne_zero, unitInterval.lt_one_iff_ne_one]

theorem SixSphereCube.cubeBoundary_eq_iUnion (n : ℕ) :
    Cube.boundary (Fin n) =
      ⋃ i : Fin n,
        {u : Fin n → (unitInterval) | u i = 0} ∪ {u : Fin n → (unitInterval) | u i = 1} := by
  ext u
  simp only [Cube.boundary, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_union]

theorem SixSphereCube.isClosed_cubeBoundaryN (n : ℕ) : IsClosed (Cube.boundary (Fin n)) := by
  rw [cubeBoundary_eq_iUnion]
  exact
    isClosed_iUnion_of_finite fun i =>
      (isClosed_eq (continuous_apply i) continuous_const).union
        (isClosed_eq (continuous_apply i) continuous_const)

def SixSphereCube.cubeInteriorCoordinates (n : ℕ) : CubeInteriorN n ≃ₜ (Fin n → OpenUnitInterval)
    where
  toFun u i := ⟨(u.val i : ℝ), (not_mem_cubeBoundary_iff u.val).mp u.property i⟩
  invFun
    v :=
    ⟨fun i => ⟨(v i : ℝ), ⟨(v i).property.1.le, (v i).property.2.le⟩⟩,
      (not_mem_cubeBoundary_iff _).mpr fun i => (v i).property⟩
  left_inv
    u := by
    apply Subtype.ext
    funext i
    exact Subtype.ext rfl
  right_inv
    v := by
    funext i
    exact Subtype.ext rfl
  continuous_toFun := by
    refine continuous_pi fun i => ?_
    have hi : Continuous (fun u : CubeInteriorN n => u.val i) :=
      (continuous_apply i).comp continuous_subtype_val
    exact (continuous_subtype_val.comp hi).subtype_mk _
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_pi fun i => ?_
    have hi : Continuous (fun v : Fin n → OpenUnitInterval => v i) := continuous_apply i
    exact (continuous_subtype_val.comp hi).subtype_mk _

def SixSphereCube.cubeInteriorEuclideanHomeomorph (n : ℕ) :
    CubeInteriorN n ≃ₜ EuclideanSpace ℝ (Fin n) :=
  (cubeInteriorCoordinates n).trans
    ((Homeomorph.piCongrRight fun _ : Fin n => openUnitIntervalHomeomorph).trans
      (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).symm)

abbrev Degree.SphereCube.Sphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

def Degree.SphereCube.compactification (n : ℕ) :
    OnePoint (SixSphereCube.CubeInteriorN n) ≃ₜ Sphere n :=
  (SixSphereCube.cubeInteriorEuclideanHomeomorph n).onePointCongr.trans
    (onePointEquivSphereOfFinrankEq (V := EuclideanSpace ℝ (Fin n)) (ι := Fin (n + 1)) (by simp))

def Degree.SphereCube.point (n : ℕ) : Sphere n :=
  compactification n (OnePoint.infty)

def Degree.SphereCube.quotient (n : ℕ) : C(Fin n → (unitInterval), Sphere n) :=
  (compactification n : C(OnePoint (SixSphereCube.CubeInteriorN n), Sphere n)).comp
    (OnePointCollapse.collapseMap (Cube.boundary (Fin n)) (SixSphereCube.isClosed_cubeBoundaryN n))

theorem Degree.SphereCube.quotient_boundary (n : ℕ) (z : Fin n → (unitInterval))
    (hz : z ∈ Cube.boundary (Fin n)) : quotient n z = point n := by
  change
    compactification n (OnePointCollapse.collapse (Cube.boundary (Fin n)) z) =
      compactification n (OnePoint.infty)
  rw [OnePointCollapse.collapse_of_mem _ hz]

theorem Degree.SphereCube.zero_boundary {n : ℕ} (hn : 0 < n) :
    (0 : Fin n → (unitInterval)) ∈ Cube.boundary (Fin n) :=
  ⟨⟨0, hn⟩, Or.inl rfl⟩

theorem Degree.SphereCube.quotient_surjective {n : ℕ} (hn : 0 < n) :
    Function.Surjective (quotient n) :=
  (compactification n).surjective.comp
    (OnePointCollapse.collapse_surjective (Cube.boundary (Fin n)) ⟨0, zero_boundary hn⟩)

theorem Degree.SphereCube.quotient_eq_iff (n : ℕ) (z w : Fin n → (unitInterval)) :
    quotient n z = quotient n w ↔ z = w ∨ z ∈ Cube.boundary (Fin n) ∧ w ∈ Cube.boundary (Fin n) :=
  by
  change
    compactification n (OnePointCollapse.collapse (Cube.boundary (Fin n)) z) =
        compactification n (OnePointCollapse.collapse (Cube.boundary (Fin n)) w) ↔
      _
  rw [(compactification n).injective.eq_iff, OnePointCollapse.collapse_eq_iff]

def Degree.SphereCube.cylinder (n : ℕ) :
    C((unitInterval) × (Fin n → (unitInterval)), (unitInterval) × Sphere n) :=
  (ContinuousMap.id (unitInterval)).prodMap (quotient n)

theorem Degree.SphereCube.cylinder_surjective {n : ℕ} (hn : 0 < n) :
    Function.Surjective (cylinder n) := by
  rintro ⟨t, z⟩
  obtain ⟨w, rfl⟩ := quotient_surjective hn z
  exact ⟨(t, w), rfl⟩

theorem Degree.SphereCube.cylinder_isQuotientMap {n : ℕ} (hn : 0 < n) :
    Topology.IsQuotientMap (cylinder n) :=
  .of_surjective_continuous (cylinder_surjective hn) (cylinder n).continuous

def Degree.SphereCube.basedCube {n : ℕ} {X : Type*} [TopologicalSpace X] (u : C(Sphere n, X)) :
    GenLoop (Fin n) X (u (point n)) :=
  ⟨u.comp (quotient n), fun z hz => congrArg u (quotient_boundary n z hz)⟩

theorem Degree.SphereCube.homotopicRel_const_of_subsingleton {n : ℕ} {X : Type*}
    [TopologicalSpace X] (hn : 0 < n) (u : C(Sphere n, X)) [Subsingleton (π_ n X (u (point n)))] :
    u.HomotopicRel (ContinuousMap.const (Sphere n) (u (point n))) {point n} := by
  let H := HigherHurewicz.nativeCubeNullHomotopy (basedCube u)
  have hfib : ∀ a b, cylinder n a = cylinder n b → H a = H b := by
    rintro ⟨t, z⟩ ⟨s, w⟩ h
    have ht : t = s := congrArg Prod.fst h
    subst s
    have hzw : quotient n z = quotient n w := congrArg Prod.snd h
    rcases (quotient_eq_iff n z w).mp hzw with rfl | ⟨hz, hw⟩
    · rfl
    · exact
        ((H.eq_fst t hz).trans ((basedCube u).property z hz)).trans
          ((H.eq_fst t hw).trans ((basedCube u).property w hw)).symm
  let G := (cylinder_isQuotientMap hn).lift H.toHomotopy.toContinuousMap hfib
  have hG (t : (unitInterval)) (z : Fin n → (unitInterval)) : G (t, quotient n z) = H (t, z) :=
    ContinuousMap.congr_fun
      ((cylinder_isQuotientMap hn).lift_comp H.toHomotopy.toContinuousMap hfib) (t, z)
  refine
    ⟨{  toContinuousMap := G
        map_zero_left := ?_
        map_one_left := ?_
        prop' := ?_ }⟩
  · intro z
    obtain ⟨w, rfl⟩ := quotient_surjective hn z
    exact (hG 0 w).trans (H.apply_zero w)
  · intro z
    obtain ⟨w, rfl⟩ := quotient_surjective hn z
    exact (hG 1 w).trans (H.apply_one w)
  · intro t z hz
    have hz' : z = point n := hz
    subst z
    change G (t, point n) = u (point n)
    rw [← quotient_boundary n 0 (zero_boundary hn), hG]
    exact H.eq_fst t (zero_boundary hn)

/-- The quotient map from the cube to the sphere, as a based loop. -/
def Degree.SphereCube.quotientLoop (n : ℕ) : GenLoop (Fin n) (Sphere n) (point n) :=
  ⟨quotient n, quotient_boundary n⟩

@[simp]
theorem Degree.SphereCube.quotientLoop_val (n : ℕ) : (quotientLoop n).val = quotient n :=
  rfl

/-- The factor map of a based loop through the sphere quotient: the loop pushed to the sphere
is the identity on the cube class. -/
def Degree.SphereCube.factorMap {n : ℕ} (hn : 0 < n) {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin n) X x) : C(Sphere n, X) :=
  (OnePointCollapse.collapseLift (Cube.boundary (Fin n)) (SixSphereCube.isClosed_cubeBoundaryN n)
        ⟨0, zero_boundary hn⟩ p.val x (fun u hu => p.property u hu)).comp
    ((compactification n).symm : C(Sphere n, OnePoint (SixSphereCube.CubeInteriorN n)))

/-- The factor map on the quotient image of a cube point is the loop's value. -/
@[simp]
theorem Degree.SphereCube.factorMap_quotient {n : ℕ} (hn : 0 < n) {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin n) X x) (u : Fin n → (unitInterval)) :
    factorMap hn p (quotient n u) = p u := by
  change
    OnePointCollapse.collapseLift (Cube.boundary (Fin n)) (SixSphereCube.isClosed_cubeBoundaryN n)
        ⟨0, zero_boundary hn⟩ p.val x (fun v hv => p.property v hv)
        ((compactification n).symm (compactification n (OnePointCollapse.collapse (Cube.boundary (Fin n)) u))) =
      p u
  rw [(compactification n).symm_apply_apply]
  exact OnePointCollapse.collapseLift_apply (Cube.boundary (Fin n))
    (SixSphereCube.isClosed_cubeBoundaryN n) ⟨0, zero_boundary hn⟩ p.val x
    (fun v hv => p.property v hv) u

/-- The factor map composed with the quotient is the loop. -/
@[simp]
theorem Degree.SphereCube.factorMap_comp_quotient {n : ℕ} (hn : 0 < n) {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x) :
    (factorMap hn p).comp (quotient n) = p.val := by
  ext u
  exact factorMap_quotient hn p u

/-- The factor map is the unique continuous map factoring the loop through the quotient. -/
theorem Degree.SphereCube.factorMap_unique {n : ℕ} (hn : 0 < n) {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin n) X x) (f : C(Sphere n, X))
    (hf : f.comp (quotient n) = p.val) : f = factorMap hn p := by
  ext z
  obtain ⟨u, rfl⟩ := quotient_surjective hn z
  exact (ContinuousMap.congr_fun hf u).trans (factorMap_quotient hn p u).symm

/-- The factor map on the cube chain: pushing the sphere's cube chain along the factor map
recovers the loop's cube chain. -/
theorem Degree.SphereCube.factor_cubeChain {n : ℕ} (hn : 0 < n) {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin n) X x) :
    SingularChains.inducedChain (factorMap hn p) n
        (HigherHurewicz.cubeChain (quotientLoop n)) =
      HigherHurewicz.cubeChain p := by
  simp only [HigherHurewicz.cubeChain]
  rw [quotientLoop_val, ← LinearMap.comp_apply, ← SingularChains.inducedChain_comp,
    factorMap_comp_quotient]

/-- The factor map on the cube cycle: the sphere's cube cycle maps to the loop's cube cycle. -/
theorem Degree.SphereCube.factor_cubeCycle {n : ℕ} (hn : 0 < n) {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin n) X x)
    (hσ : HigherHurewicz.cubeChain (quotientLoop n) ∈
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex (Sphere n)) n)
    (hp : HigherHurewicz.cubeChain p ∈
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    SingularMayerVietoris.ModuleHomology.mapCycles
        (SingularChains.singularChainMap (factorMap hn p)) n
        ⟨HigherHurewicz.cubeChain (quotientLoop n), hσ⟩ =
      ⟨HigherHurewicz.cubeChain p, hp⟩ := by
  apply Subtype.ext
  rw [SingularMayerVietoris.ModuleHomology.mapCycles_val]
  exact factor_cubeChain hn p

/-- The factor map on the cube homology class: the sphere's cube class maps to the loop's
cube class. -/
theorem Degree.SphereCube.factor_cubeHomologyClass {n : ℕ} (hn : 0 < n) {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x)
    (hσ : HigherHurewicz.cubeChain (quotientLoop n) ∈
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex (Sphere n)) n)
    (hp : HigherHurewicz.cubeChain p ∈
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    SingularMayerVietoris.singularHomologyMap (factorMap hn p) n
        (SingularMayerVietoris.ModuleHomology.cycleClass
          (SingularChains.singularComplex (Sphere n)) n
          ⟨HigherHurewicz.cubeChain (quotientLoop n), hσ⟩) =
      SingularMayerVietoris.ModuleHomology.cycleClass
        (SingularChains.singularComplex X) n ⟨HigherHurewicz.cubeChain p, hp⟩ := by
  rw [SingularMayerVietoris.singularHomologyMap]
  rw [SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass]
  exact congrArg _ (factor_cubeCycle hn p hσ hp)

/-- The factor map on the cube homology class, using the general cube cycle. -/
theorem Degree.SphereCube.factor_cubeHomologyClass_cycle {m : ℕ} {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin (m + 2)) X x) :
    SingularMayerVietoris.singularHomologyMap (factorMap (Nat.succ_pos (m + 1)) p) (m + 2)
        (HigherHurewicz.cubeHomologyClass (quotientLoop (m + 2))) =
      HigherHurewicz.cubeHomologyClass p := by
  unfold HigherHurewicz.cubeHomologyClass
  rw [SingularMayerVietoris.singularHomologyMap,
    SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass]
  apply congrArg
  apply Subtype.ext
  rw [SingularMayerVietoris.ModuleHomology.mapCycles_val, HigherHurewicz.cubeCycle_val,
    HigherHurewicz.cubeCycle_val]
  exact factor_cubeChain (Nat.succ_pos (m + 1)) p

/-- A homotopy of based cubes relative to the boundary descends to a homotopy of
factor maps on the sphere. -/
def Degree.SphereCube.factorMap_homotopy {n : ℕ} (hn : 0 < n) {X : Type*}
    [TopologicalSpace X] {x : X} {p q : GenLoop (Fin n) X x}
    (H : p.val.HomotopyRel q.val (Cube.boundary (Fin n))) :
    (factorMap hn p).Homotopy (factorMap hn q) := by
  have hfib : ∀ a b, cylinder n a = cylinder n b → H a = H b := by
    rintro ⟨t, z⟩ ⟨s, w⟩ h
    have ht : t = s := congrArg Prod.fst h
    subst s
    have hzw : quotient n z = quotient n w := congrArg Prod.snd h
    rcases (quotient_eq_iff n z w).mp hzw with rfl | ⟨hz, hw⟩
    · rfl
    · exact
        ((H.eq_fst t hz).trans (p.property z hz)).trans
          ((H.eq_fst t hw).trans (p.property w hw)).symm
  let G := (cylinder_isQuotientMap hn).lift H.toHomotopy.toContinuousMap hfib
  have hG (t : (unitInterval)) (z : Fin n → (unitInterval)) :
      G (t, quotient n z) = H (t, z) :=
    ContinuousMap.congr_fun
      ((cylinder_isQuotientMap hn).lift_comp H.toHomotopy.toContinuousMap hfib) (t, z)
  refine
    { toContinuousMap := G
      map_zero_left := ?_
      map_one_left := ?_ }
  · intro z
    obtain ⟨w, rfl⟩ := quotient_surjective hn z
    exact (hG 0 w).trans ((H.apply_zero w).trans (factorMap_quotient hn p w).symm)
  · intro z
    obtain ⟨w, rfl⟩ := quotient_surjective hn z
    exact (hG 1 w).trans ((H.apply_one w).trans (factorMap_quotient hn q w).symm)

/-- Homotopic based cubes have the same cube homology class. -/
theorem HigherHurewicz.cubeHomologyClass_homotopic {m : ℕ} {X : Type} [TopologicalSpace X]
    {x : X} {p q : GenLoop (Fin (m + 2)) X x} (h : GenLoop.Homotopic p q) :
    HigherHurewicz.cubeHomologyClass p = HigherHurewicz.cubeHomologyClass q := by
  obtain ⟨H⟩ := h
  have Hf : (Degree.SphereCube.factorMap (Nat.succ_pos (m + 1)) p).Homotopic
      (Degree.SphereCube.factorMap (Nat.succ_pos (m + 1)) q) :=
    ⟨Degree.SphereCube.factorMap_homotopy (Nat.succ_pos (m + 1)) H⟩
  rw [← Degree.SphereCube.factor_cubeHomologyClass_cycle p,
    ← Degree.SphereCube.factor_cubeHomologyClass_cycle q]
  exact congrArg (fun F => F (HigherHurewicz.cubeHomologyClass
      (Degree.SphereCube.quotientLoop (m + 2))))
    (SingularHomology.homotopic_homologyMap Hf (m + 2))

/-- In degree `2` the cube homology class is the square homology class. -/
theorem HigherHurewicz.cubeHomologyClass_eq_squareHomologyClass {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    HigherHurewicz.cubeHomologyClass (m := 0) p = SecondHurewicz.squareHomologyClass p := by
  unfold HigherHurewicz.cubeHomologyClass SecondHurewicz.squareHomologyClass
  apply congrArg
  apply Subtype.ext
  change HigherHurewicz.cubeChain p = SecondHurewicz.squareChain p
  exact HigherHurewicz.cubeChain_eq_squareChain p

/-- Concatenation along the first coordinate adds cube classes in degree `2`. -/
theorem HigherHurewicz.cubeHomologyClass_transAt_two {X : Type} [TopologicalSpace X]
    {x : X} (p q : GenLoop (Fin 2) X x) :
    HigherHurewicz.cubeHomologyClass (m := 0) (GenLoop.transAt (0 : Fin 2) p q) =
      HigherHurewicz.cubeHomologyClass (m := 0) p +
        HigherHurewicz.cubeHomologyClass (m := 0) q := by
  simpa only [HigherHurewicz.cubeHomologyClass_eq_squareHomologyClass] using
    SecondHurewicz.squareHomologyClass_transAt p q


/-- Concatenation along any coordinate adds cube classes in degree `2`. -/
theorem HigherHurewicz.cubeHomologyClass_transAt_two_coord {X : Type} [TopologicalSpace X]
    {x : X} (i : Fin 2) (p q : GenLoop (Fin 2) X x) :
    HigherHurewicz.cubeHomologyClass (m := 0) (GenLoop.transAt i p q) =
      HigherHurewicz.cubeHomologyClass (m := 0) p +
        HigherHurewicz.cubeHomologyClass (m := 0) q := by
  have h : GenLoop.Homotopic (GenLoop.transAt i p q)
      (GenLoop.transAt (0 : Fin 2) p q) :=
    Quotient.eq.mp (HomotopyGroup.transAt_indep (0 : Fin 2) p q)
  rw [HigherHurewicz.cubeHomologyClass_homotopic h]
  exact HigherHurewicz.cubeHomologyClass_transAt_two p q

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
/-- The extra term of the `transAt 0` cube-chain difference is a boundary at every
degree. -/
theorem HigherHurewicz.cubeChain_transAt_zero_extra_boundary {n : ℕ} {X : Type}
    [TopologicalSpace X] {x : X} (p q : GenLoop (Fin (n + 2)) X x) :
    ∃ W : SingularChains.Chains X (n + 3),
      ((SingularChains.singularComplex X).d (n + 3) (n + 2)).hom W =
        SingularChains.inducedChain
          ((GenLoop.transAt (0 : Fin (n + 2)) p q).val.comp
            (HigherHurewicz.cubeCoordinates (n + 1))) (n + 2)
          (PeriodTorusHigherHomology.crossProductTriangle (unitInterval)
            (Fin (n + 1) → (unitInterval)) n
            (SingularChains.concatChain HigherHurewicz.intervalPathLeft
              HigherHurewicz.intervalPathRight)
            (((SingularChains.singularComplex (Fin (n + 1) → (unitInterval))).d (n + 1) n).hom
              (HigherHurewicz.fundamentalCubeChain (n + 1)))) := by
  obtain ⟨k, hk⟩ := HigherHurewicz.cubeChain_transAt_zero_extra_eq_smul p q
  by_cases hEven : Even (n + 2)
  · have hdiff := HigherHurewicz.cubeChain_transAt_zero_diff_boundary p q
    have hp := HigherHurewicz.cubeChain_boundary p
    have hq := HigherHurewicz.cubeChain_boundary q
    have ht := HigherHurewicz.cubeChain_boundary (GenLoop.transAt (0 : Fin (n + 2)) p q)
    have hdd :
        ((SingularChains.singularComplex X).d (n + 2) (n + 1)).hom
            (((SingularChains.singularComplex X).d (n + 3) (n + 2)).hom
              (SingularChains.inducedChain
                ((GenLoop.transAt (0 : Fin (n + 2)) p q).val.comp
                  (HigherHurewicz.cubeCoordinates (n + 1))) (n + 3)
                (PeriodTorusHigherHomology.crossProductTriangle (unitInterval)
                  (Fin (n + 1) → (unitInterval)) (n + 1)
                  (SingularChains.concatChain HigherHurewicz.intervalPathLeft
                    HigherHurewicz.intervalPathRight)
                  (HigherHurewicz.fundamentalCubeChain (n + 1))))) = 0 :=
      congrArg (fun f : SingularChains.Chains X (n + 3) ⟶ SingularChains.Chains X (n + 1) =>
          f.hom _) ((SingularChains.singularComplex X).d_comp_d (n + 3) (n + 2) (n + 1))
    have hextra0 :
        ((SingularChains.singularComplex X).d (n + 2) (n + 1)).hom
            (SingularChains.inducedChain
              ((GenLoop.transAt (0 : Fin (n + 2)) p q).val.comp
                (HigherHurewicz.cubeCoordinates (n + 1))) (n + 2)
              (PeriodTorusHigherHomology.crossProductTriangle (unitInterval)
                (Fin (n + 1) → (unitInterval)) n
                (SingularChains.concatChain HigherHurewicz.intervalPathLeft
                  HigherHurewicz.intervalPathRight)
                (((SingularChains.singularComplex (Fin (n + 1) → (unitInterval))).d (n + 1) n).hom
                  (HigherHurewicz.fundamentalCubeChain (n + 1))))) = 0 := by
      have h := congrArg ((SingularChains.singularComplex X).d (n + 2) (n + 1)).hom hdiff
      simp only [map_sub, map_add, hp, hq, ht, hdd, add_zero, sub_zero, zero_sub] at h
      exact neg_eq_zero.mp h.symm
    have hk0 : k = 0 := by
      have hbound := congrArg ((SingularChains.singularComplex X).d (n + 2) (n + 1)).hom hk
      rw [hextra0, map_zsmul, HigherHurewicz.boundary_const_simplex, Fin.sum_neg_one_pow] at hbound
      have hodd : ¬Even (n + 3) := Nat.not_even_iff_odd.mpr hEven.add_one
      simp only [if_neg hodd, one_smul] at hbound
      have haug :=
        congrArg (SecondHurewicz.SimplyConnected.chainAugmentation X (n + 1)) hbound
      simpa [map_zero, map_zsmul, SecondHurewicz.SimplyConnected.chainAugmentation_simplex]
        using haug.symm
    refine ⟨0, ?_⟩
    rw [hk, hk0, zero_smul, map_zero]
  · refine ⟨k • SingularChains.simplexChain X (n + 3)
        (ContinuousMap.const (SingularChains.Simplex (n + 3)) x), ?_⟩
    rw [hk, map_zsmul, HigherHurewicz.boundary_const_simplex, Fin.sum_neg_one_pow]
    have hodd : ¬Even (n + 4) := by
      simpa [show n + 4 = n + 2 + 2 from rfl, Nat.even_add] using hEven
    simp [if_neg hodd]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
/-- Concatenation along coordinate `0` adds cube homology classes at every degree `n ≥ 2`. -/
theorem HigherHurewicz.cubeHomologyClass_transAt_zero {m : ℕ} {X : Type}
    [TopologicalSpace X] {x : X} (p q : GenLoop (Fin (m + 2)) X x) :
    HigherHurewicz.cubeHomologyClass (GenLoop.transAt (0 : Fin (m + 2)) p q) =
      HigherHurewicz.cubeHomologyClass p + HigherHurewicz.cubeHomologyClass q := by
  obtain ⟨Wextra, hWextra⟩ := HigherHurewicz.cubeChain_transAt_zero_extra_boundary p q
  have hdiff := HigherHurewicz.cubeChain_transAt_zero_diff_boundary p q
  unfold HigherHurewicz.cubeHomologyClass
  rw [← map_add]
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff
        (SingularChains.singularComplex X) (m + 2)
        (HigherHurewicz.cubeCycle (GenLoop.transAt (0 : Fin (m + 2)) p q))
        (HigherHurewicz.cubeCycle p + HigherHurewicz.cubeCycle q)).mpr
  refine ⟨Wextra -
      SingularChains.inducedChain
        ((GenLoop.transAt (0 : Fin (m + 2)) p q).val.comp
          (HigherHurewicz.cubeCoordinates (m + 1))) (m + 3)
        (PeriodTorusHigherHomology.crossProductTriangle (unitInterval)
          (Fin (m + 1) → (unitInterval)) (m + 1)
          (SingularChains.concatChain HigherHurewicz.intervalPathLeft
            HigherHurewicz.intervalPathRight)
          (HigherHurewicz.fundamentalCubeChain (m + 1))), ?_⟩
  simp only [Submodule.coe_add, Submodule.coe_sub, HigherHurewicz.cubeCycle_val, map_sub, hWextra]
  rw [show HigherHurewicz.cubeChain (GenLoop.transAt (0 : Fin (m + 2)) p q) -
        (HigherHurewicz.cubeChain p + HigherHurewicz.cubeChain q) =
      - (HigherHurewicz.cubeChain p + HigherHurewicz.cubeChain q -
          HigherHurewicz.cubeChain (GenLoop.transAt (0 : Fin (m + 2)) p q)) by abel,
    hdiff]
  abel

/-- Concatenation along any coordinate adds cube homology classes at every degree `n ≥ 2`. -/
theorem HigherHurewicz.cubeHomologyClass_transAt {m : ℕ} {X : Type} [TopologicalSpace X]
    {x : X} (i : Fin (m + 2)) (p q : GenLoop (Fin (m + 2)) X x) :
    HigherHurewicz.cubeHomologyClass (GenLoop.transAt i p q) =
      HigherHurewicz.cubeHomologyClass p + HigherHurewicz.cubeHomologyClass q := by
  have h : GenLoop.Homotopic (GenLoop.transAt i p q)
      (GenLoop.transAt (0 : Fin (m + 2)) p q) :=
    Quotient.eq.mp (HomotopyGroup.transAt_indep (0 : Fin (m + 2)) p q)
  rw [HigherHurewicz.cubeHomologyClass_homotopic h]
  exact HigherHurewicz.cubeHomologyClass_transAt_zero p q


/-- The Hurewicz function at degree `n ≥ 2`: the cube homology class of a representative. -/
def HigherHurewicz.hurewiczFunction {m : ℕ} {X : Type} [TopologicalSpace X] (x : X) :
    π_ (m + 2) X x → SingularMayerVietoris.SingularHomology X (m + 2) :=
  Quotient.lift HigherHurewicz.cubeHomologyClass fun _ _ h =>
    HigherHurewicz.cubeHomologyClass_homotopic h

/-- The Hurewicz function as a group homomorphism `π_n →+ (H_n, +)` written multiplicatively. -/
def HigherHurewicz.hurewiczPi {m : ℕ} {X : Type} [TopologicalSpace X] (x : X) :
    π_ (m + 2) X x →* Multiplicative (SingularMayerVietoris.SingularHomology X (m + 2))
    where
  toFun a := Multiplicative.ofAdd (HigherHurewicz.hurewiczFunction x a)
  map_one' := congrArg Multiplicative.ofAdd (HigherHurewicz.cubeHomologyClass_const (x := x))
  map_mul' a b := by
    refine Quotient.inductionOn₂ a b fun p q => ?_
    refine
      (congrArg (fun c : π_ (m + 2) X x =>
            Multiplicative.ofAdd (HigherHurewicz.hurewiczFunction x c))
          (HomotopyGroup.mul_spec (i := (0 : Fin (m + 2))) (p := p) (q := q))).trans
        ?_
    change
      Multiplicative.ofAdd
          (HigherHurewicz.cubeHomologyClass (GenLoop.transAt (0 : Fin (m + 2)) q p)) =
        Multiplicative.ofAdd
          (HigherHurewicz.cubeHomologyClass p + HigherHurewicz.cubeHomologyClass q)
    apply congrArg Multiplicative.ofAdd
    rw [HigherHurewicz.cubeHomologyClass_transAt_zero q p]
    exact add_comm _ _

/-- The Hurewicz map in degree `n ≥ 2`, as a `ℤ`-linear map on the additive homotopy group. -/
def HigherHurewicz.hurewiczMap {m : ℕ} {X : Type} [TopologicalSpace X] (x : X) :
    Additive (π_ (m + 2) X x) →ₗ[ℤ] SingularMayerVietoris.SingularHomology X (m + 2)
    where
  toFun := (HigherHurewicz.hurewiczPi (m := m) x).toAdditiveLeft
  map_add' := (HigherHurewicz.hurewiczPi (m := m) x).toAdditiveLeft.map_add
  map_smul' n a := by
    simpa using
      map_intCast_smul (HigherHurewicz.hurewiczPi (m := m) x).toAdditiveLeft ℤ ℤ n a

end Mathoverflow1973
