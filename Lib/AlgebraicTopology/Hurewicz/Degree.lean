/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.CubeGluing

/-!
# Straightening cycles and descending to singular homology

`Hurewicz.straightenedCycle n H H' h c` replaces a singular `(n + 1)`-cycle `c` by its
time-`1` endpoint under a face-compatible pair of simplex homotopies;
`Hurewicz.straightenedCycle_class` shows the two cycles represent the same homology
class (the prism operator bounds their difference).
`Hurewicz.singularHomologyDesc n F hF` descends a `ℤ`-linear map on `n`-chains that
vanishes on boundaries to a map `SingularHomology X n →ₗ[ℤ] M`.

## Outline of the construction

1. Vanishing `π_ n X x` gives boundary-relative nullhomotopies of based cube and
   simplex maps (`nativeCubeNullHomotopy`, `simplexNullHomotopy`).
2. `simplexStraighteningHomotopy` contracts an already boundary-based `n`-simplex to
   `x` and is stationary on all other simplices, compatibly with the stationary
   lower-dimensional family.
3. The time-`1` endpoint of a face-compatible homotopy preserves the homology class
   via the prism operator (`straightenedCycle_class`).
4. `singularHomologyDesc` descends chain maps killing boundaries to homology.
5. Parity of the boundary signs of the constant simplex
   (`constantSimplexCycle`, `correctedSimplexCycle`) corrects the straightened cycle
   assignment (`normalizedCycleAssignment_class`).

## Main definitions and results

* `Hurewicz.straightenedCycle`, `Hurewicz.straightenedCycle_class`: straightening a
  cycle preserves its class.
* `Hurewicz.singularHomologyDesc`: descent of boundary-killing chain maps.
* `Hurewicz.normalizedCycleAssignment`, `Hurewicz.normalizedCycleAssignment_class`:
  the normalized assignment and its class preservation.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], Theorems 2.10 and 4.32; the
  argument is recorded in `Lib/docs/C.md`, §§8 and 12–13.

## Tags

Hurewicz theorem, straightening, cycles, singular homology
-/


open Set Function Filter Manifold Topology

noncomputable section

/-! ### Nullhomotopies from vanishing homotopy groups -/

/-- A based cube map into a space with `Subsingleton (π_ n X x)` is homotopic relative
to the cube boundary to the constant map at `x`. -/
def Hurewicz.nativeCubeNullHomotopy {n : ℕ} {X : Type*} [TopologicalSpace X] {x : X}
    [hπ : Subsingleton (π_ n X x)] (p : GenLoop (Fin n) X x) :
    p.val.HomotopyRel (ContinuousMap.const (Fin n → (unitInterval)) x) (Cube.boundary (Fin n)) :=
  Classical.choice
    (show GenLoop.Homotopic p GenLoop.const from
      Quotient.exact (@Subsingleton.elim (π_ n X x) hπ ⟦p⟧ ⟦GenLoop.const⟧))

/-- The nullhomotopy precomposed with a map `r : C(A, Fin n → unitInterval)` sending
`S ⊆ A` into the cube boundary, as a homotopy rel `S`. -/
def Hurewicz.nativeCubeNullHomotopy_comp {n : ℕ} {X : Type*} [TopologicalSpace X] {x : X}
    {A : Type*} [TopologicalSpace A] [Subsingleton (π_ n X x)] (p : GenLoop (Fin n) X x)
    (r : C(A, Fin n → (unitInterval))) (S : Set A) (hr : Set.MapsTo r S (Cube.boundary (Fin n))) :
    (p.val.comp r).HomotopyRel (ContinuousMap.const A x) S
    where
  toFun z := nativeCubeNullHomotopy p (z.1, r z.2)
  continuous_toFun :=
    (nativeCubeNullHomotopy p).continuous.comp
      (continuous_fst.prodMk (r.continuous.comp continuous_snd))
  map_zero_left a := (nativeCubeNullHomotopy p).apply_zero (r a)
  map_one_left a := (nativeCubeNullHomotopy p).apply_one (r a)
  prop' t _ ha := (nativeCubeNullHomotopy p).eq_fst t (hr ha)

/-! ### Straightening simplices relative to the boundary -/

/-- The based cube map obtained from a based simplex `τ` by precomposing with the
inverse `simplexCubeHomeomorph n ⁻¹` of the simplex–cube homeomorphism. -/
def Hurewicz.basedSimplexNativeLoop {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedSimplex n x) : GenLoop (Fin n) X x :=
  ⟨τ.val.comp ⟨(simplexCubeHomeomorph n).symm, (simplexCubeHomeomorph n).symm.continuous⟩,
    fun u hu => τ.property _ ((simplexCubeHomeomorph_symm_boundary_iff n u).mpr hu)⟩

/-- Composing `basedSimplexNativeLoop τ` back with `simplexCubeHomeomorph n` recovers
`τ`. -/
theorem Hurewicz.basedSimplexNativeLoop_comp_homeomorph {n : ℕ} {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedSimplex n x) :
    (basedSimplexNativeLoop τ).val.comp
        ⟨simplexCubeHomeomorph n, (simplexCubeHomeomorph n).continuous⟩ =
      τ.val := by
  apply ContinuousMap.ext
  intro s
  change τ.val ((simplexCubeHomeomorph n).symm (simplexCubeHomeomorph n s)) = τ.val s
  rw [Homeomorph.symm_apply_apply]

/-- The unnormalized nullhomotopy of a based simplex `τ`, obtained by transporting the
native cube nullhomotopy of `basedSimplexNativeLoop τ` back along the
simplex–cube homeomorphism. -/
def Hurewicz.simplexNullHomotopyUnnormalized {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    [Subsingleton (π_ n X x)] (τ : BasedSimplex n x) :
    τ.val.HomotopyRel (ContinuousMap.const (SingularChains.Simplex n) x)
      (Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary n) :=
  ContinuousMap.HomotopyRel.cast
    (nativeCubeNullHomotopy_comp (basedSimplexNativeLoop τ)
      ⟨simplexCubeHomeomorph n, (simplexCubeHomeomorph n).continuous⟩
      (Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary n)
      (fun s hs => (simplexCubeHomeomorph_boundary_iff n s).mpr hs))
    (basedSimplexNativeLoop_comp_homeomorph τ) rfl

/-- A based `n`-simplex in a space with `Subsingleton (π_ n X x)` is homotopic relative
to the simplex boundary to the constant map at `x`. -/
def Hurewicz.simplexNullHomotopy {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    [Subsingleton (π_ n X x)] (τ : BasedSimplex n x) :
    τ.val.HomotopyRel (ContinuousMap.const (SingularChains.Simplex n) x)
      (Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary n) := by
  classical
    exact
    if h : τ = constantBasedSimplex n x then
      ContinuousMap.HomotopyRel.cast
        (ContinuousMap.HomotopyRel.refl (ContinuousMap.const (SingularChains.Simplex n) x)
          (Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary n))
        (congrArg (fun υ : BasedSimplex n x => υ.val) h).symm rfl
    else simplexNullHomotopyUnnormalized τ

/-- The simplex nullhomotopy starts at `τ`. -/
@[simp]
theorem Hurewicz.simplexNullHomotopy_zero {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    [Subsingleton (π_ n X x)] (τ : BasedSimplex n x) (s : SingularChains.Simplex n) :
    simplexNullHomotopy τ (0, s) = τ.val s :=
  (simplexNullHomotopy τ).apply_zero s

/-- The simplex nullhomotopy ends at the constant map at `x`. -/
@[simp]
theorem Hurewicz.simplexNullHomotopy_one {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    [Subsingleton (π_ n X x)] (τ : BasedSimplex n x) (s : SingularChains.Simplex n) :
    simplexNullHomotopy τ (1, s) = x :=
  (simplexNullHomotopy τ).apply_one s

/-- The nullhomotopy of the constant based simplex is itself stationary. -/
@[simp]
theorem Hurewicz.simplexNullHomotopy_constant {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) [Subsingleton (π_ n X x)] :
    simplexNullHomotopy (constantBasedSimplex n x) =
      ContinuousMap.HomotopyRel.refl (ContinuousMap.const (SingularChains.Simplex n) x)
        (Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary n) := by
  classical
  unfold simplexNullHomotopy
  rw [dif_pos rfl]
  rfl

/-- The underlying continuous map of the constant simplex's nullhomotopy is constant in
the time parameter. -/
@[simp]
theorem Hurewicz.simplexNullHomotopy_constant_toContinuousMap {X : Type}
    [TopologicalSpace X] (n : ℕ) (x : X) [Subsingleton (π_ n X x)] :
    (simplexNullHomotopy (constantBasedSimplex n x)).toContinuousMap =
      ContinuousMap.const ((unitInterval) × SingularChains.Simplex n) x := by
  rw [simplexNullHomotopy_constant]
  rfl

/-- The straightening homotopy of a singular `n`-simplex in a space with
`Subsingleton (π_ n X x)`: if `smp` is already boundary-based it is the
nullhomotopy `simplexNullHomotopy` contracting `smp` to `x`, and otherwise it is
stationary. -/
def Hurewicz.simplexStraighteningHomotopy {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    [Subsingleton (π_ n X x)] (smp : SingularChains.SingularSimplex X n) :
    C((unitInterval) × SingularChains.Simplex n, X) := by
  classical
    exact
    if h : ∀ s ∈ Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary n, smp s = x then
      (simplexNullHomotopy (⟨smp, h⟩ : BasedSimplex n x)).toContinuousMap
    else Hurewicz.DegreeTwo.SimplyConnected.stationarySimplexHomotopy n smp

/-- The straightening homotopy starts at the simplex itself. -/
@[simp]
theorem Hurewicz.simplexStraighteningHomotopy_zero {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) [Subsingleton (π_ n X x)] (smp : SingularChains.SingularSimplex X n)
    (s : SingularChains.Simplex n) : simplexStraighteningHomotopy n x smp (0, s) = smp s := by
  classical
  unfold simplexStraighteningHomotopy
  split
  · rename_i h
    exact simplexNullHomotopy_zero (⟨smp, h⟩ : BasedSimplex n x) s
  · rfl

/-- For an already boundary-based simplex `smp`, the straightening homotopy ends at
the constant map `x`. -/
theorem Hurewicz.simplexStraighteningHomotopy_one {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) [Subsingleton (π_ n X x)] (smp : SingularChains.SingularSimplex X n)
    (h : ∀ s ∈ Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary n, smp s = x)
    (s : SingularChains.Simplex n) : simplexStraighteningHomotopy n x smp (1, s) = x := by
  classical
  rw [simplexStraighteningHomotopy, dif_pos h]
  exact simplexNullHomotopy_one (⟨smp, h⟩ : BasedSimplex n x) s

/-- On the simplex boundary the straightening homotopy is fixed at `smp s` for all
times. -/
theorem Hurewicz.simplexStraighteningHomotopy_boundary {X : Type} [TopologicalSpace X]
    (n : ℕ) (x : X) [Subsingleton (π_ n X x)] (smp : SingularChains.SingularSimplex X n)
    (r : (unitInterval)) (s : SingularChains.Simplex n)
    (hs : s ∈ Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary n) :
    simplexStraighteningHomotopy n x smp (r, s) = smp s := by
  classical
  unfold simplexStraighteningHomotopy
  split
  · rename_i h
    exact (simplexNullHomotopy (⟨smp, h⟩ : BasedSimplex n x)).eq_fst r hs
  · rfl

/-- The straightening homotopy of the constant simplex is stationary. -/
@[simp]
theorem Hurewicz.simplexStraighteningHomotopy_const {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) [Subsingleton (π_ n X x)] :
    simplexStraighteningHomotopy n x (ContinuousMap.const (SingularChains.Simplex n) x) =
      ContinuousMap.const ((unitInterval) × SingularChains.Simplex n) x := by
  classical
  have h :
    ∀ s ∈ Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary n,
      (ContinuousMap.const (SingularChains.Simplex n) x) s = x :=
    fun _ _ => rfl
  rw [simplexStraighteningHomotopy, dif_pos h]
  exact simplexNullHomotopy_constant_toContinuousMap n x

/-- The degree-`(n+1)` straightening homotopy restricted to each face equals the
stationary homotopy of the face: `simplexStraighteningHomotopy` is face-compatible
with `stationarySimplexHomotopy`. -/
theorem Hurewicz.simplexStraighteningHomotopy_face {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) [Subsingleton (π_ (n + 1) X x)] :
    Hurewicz.DegreeTwo.SimplyConnected.FaceCompatibleHomotopies n
      (Hurewicz.DegreeTwo.SimplyConnected.stationarySimplexHomotopy n)
      (simplexStraighteningHomotopy (n + 1) x) := by
  intro smp i
  ext u
  change
    simplexStraighteningHomotopy (n + 1) x smp (u.1, SingularChains.simplexFace n i u.2) =
      smp (SingularChains.simplexFace n i u.2)
  exact
    simplexStraighteningHomotopy_boundary (n + 1) x smp u.1 _
      ⟨i, SingularChains.simplexFace_apply_self n i u.2⟩

/-- If the time-`1` endpoint of every lower-family homotopy is the constant simplex
at `x`, then every face of the time-`1` endpoint of `H' smp` is also constant. -/
theorem Hurewicz.simplexEndpoint_face_constant {X : Type} [TopologicalSpace X] {n : ℕ}
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (hface : Hurewicz.DegreeTwo.SimplyConnected.FaceCompatibleHomotopies n H H') (x : X)
    (hone :
      ∀ smp,
        Hurewicz.DegreeTwo.SimplyConnected.timeSlice (H smp) 1 =
          ContinuousMap.const (SingularChains.Simplex n) x)
    (smp : SingularChains.SingularSimplex X (n + 1)) (i : Fin (n + 2)) :
    (Hurewicz.DegreeTwo.SimplyConnected.timeSlice (H' smp) 1).comp (SingularChains.simplexFace n i) =
      ContinuousMap.const (SingularChains.Simplex n) x :=
  (Hurewicz.DegreeTwo.SimplyConnected.timeSlice_face hface smp i 1).trans (hone _)

/-- If the time-`1` endpoint of every lower-family homotopy is the constant simplex
at `x`, then the time-`1` endpoint of `H' smp` takes the value `x` on the whole
simplex boundary. -/
theorem Hurewicz.simplexEndpoint_boundary {X : Type} [TopologicalSpace X] {n : ℕ}
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (hface : Hurewicz.DegreeTwo.SimplyConnected.FaceCompatibleHomotopies n H H') (x : X)
    (hone :
      ∀ smp,
        Hurewicz.DegreeTwo.SimplyConnected.timeSlice (H smp) 1 =
          ContinuousMap.const (SingularChains.Simplex n) x)
    (smp : SingularChains.SingularSimplex X (n + 1)) (s : SingularChains.Simplex (n + 1))
    (hs : s ∈ Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary (n + 1)) :
    Hurewicz.DegreeTwo.SimplyConnected.timeSlice (H' smp) 1 s = x := by
  obtain ⟨i, t, ht⟩ :=
    Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary_exists_face n
      (⟨s, hs⟩ : Hurewicz.DegreeTwo.SimplyConnected.SimplexBoundary (n + 1))
  have he : SingularChains.simplexFace n i t = s := congrArg Subtype.val ht
  rw [← he]
  exact
    congrArg (fun f : C(SingularChains.Simplex n, X) => f t)
      (simplexEndpoint_face_constant H H' hface x hone smp i)

/-! ### Straightened cycles and prism class preservation -/

/-- The straightened form of an `(n + 1)`-cycle `c`: the chain obtained by evaluating a
face-compatible simplex homotopy family `H'` at time `1`, which is again a cycle. -/
def Hurewicz.straightenedCycle {X : Type} [TopologicalSpace X] (n : ℕ)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (h : Hurewicz.DegreeTwo.SimplyConnected.FaceCompatibleHomotopies n H H')
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) (n + 1)) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) (n + 1) :=
  SingularMayerVietoris.ModuleHomology.mkCycle (SingularChains.singularComplex X) (n + 1)
    (Hurewicz.DegreeTwo.SimplyConnected.simplexEndpointOperator (n + 1) H' 1 c.1)
    (by
      have hc : ((SingularChains.singularComplex X).d (n + 1) n).hom c.1 = 0 := by
        exact
          SingularMayerVietoris.ModuleHomology.cycle_condition (SingularChains.singularComplex X)
            (n + 1) c
      rw [Nat.add_sub_cancel,
        Hurewicz.DegreeTwo.SimplyConnected.simplexEndpointOperator_boundary n H H' h, hc, map_zero])

/-- The underlying chain of `straightenedCycle` is the time-`1` endpoint of `H'`
applied to `c`. -/
@[simp]
theorem Hurewicz.straightenedCycle_val {X : Type} [TopologicalSpace X] (n : ℕ)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (h : Hurewicz.DegreeTwo.SimplyConnected.FaceCompatibleHomotopies n H H')
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) (n + 1)) :
    (straightenedCycle n H H' h c).1 =
      Hurewicz.DegreeTwo.SimplyConnected.simplexEndpointOperator (n + 1) H' 1 c.1 :=
  rfl

/-- The prism operator of `H'` bounds the difference between `c` and its straightened
cycle: `c - straightenedCycle c` is a boundary. -/
theorem Hurewicz.straightenedCycle_boundary {X : Type} [TopologicalSpace X] (n : ℕ)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (h : Hurewicz.DegreeTwo.SimplyConnected.FaceCompatibleHomotopies n H H')
    (h₀ : ∀ smp, Hurewicz.DegreeTwo.SimplyConnected.timeSlice (H' smp) 0 = smp)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) (n + 1)) :
    ((SingularChains.singularComplex X).d (n + 2) (n + 1)).hom
        (Hurewicz.DegreeTwo.SimplyConnected.simplexPrismOperator (n + 1) H' c.1) =
      (straightenedCycle n H H' h c).1 - c.1 := by
  have hc : ((SingularChains.singularComplex X).d (n + 1) n).hom c.1 = 0 := by
    exact
      SingularMayerVietoris.ModuleHomology.cycle_condition (SingularChains.singularComplex X)
        (n + 1) c
  rw [Hurewicz.DegreeTwo.SimplyConnected.simplexPrismOperator_boundary n H H' h,
    Hurewicz.DegreeTwo.SimplyConnected.simplexEndpointOperator_zero (n + 1) H' h₀, hc, map_zero,
    sub_zero]
  rfl

/-- Straightening preserves the homology class: `straightenedCycle c` and `c` represent
the same class. -/
theorem Hurewicz.straightenedCycle_class {X : Type} [TopologicalSpace X] (n : ℕ)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (h : Hurewicz.DegreeTwo.SimplyConnected.FaceCompatibleHomotopies n H H')
    (h₀ : ∀ smp, Hurewicz.DegreeTwo.SimplyConnected.timeSlice (H' smp) 0 = smp)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) (n + 1)) :
    SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) (n + 1)
        (straightenedCycle n H H' h c) =
      SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) (n + 1)
        c := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (SingularChains.singularComplex X)
        (n + 1) _ _).mpr
  exact
    ⟨Hurewicz.DegreeTwo.SimplyConnected.simplexPrismOperator (n + 1) H' c.1,
      straightenedCycle_boundary n H H' h h₀ c⟩

/-! ### Descending to singular homology -/

/-- A `ℤ`-linear map on singular `n`-chains that vanishes on all boundaries descends to
a linear map on `SingularHomology X n`. -/
def Hurewicz.singularHomologyDesc {X : Type} [TopologicalSpace X] {M : Type*}
    [AddCommGroup M] [Module ℤ M] (n : ℕ) (F : SingularChains.Chains X n →ₗ[ℤ] M)
    (hF :
      ∀ b : SingularChains.Chains X (n + 1),
        F (((SingularChains.singularComplex X).d (n + 1) n).hom b) = 0) :
    SingularMayerVietoris.SingularHomology X n →ₗ[ℤ] M :=
  SingularHomology.homologyDesc (SingularChains.singularComplex X) n
    (F.comp
      (SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n).subtype)
    (fun b => hF b)

/-- `singularHomologyDesc` sends the class of a cycle `c` to `F` applied to `c`'s
underlying chain. -/
@[simp]
theorem Hurewicz.singularHomologyDesc_cycleClass {X : Type} [TopologicalSpace X] {M : Type*}
    [AddCommGroup M] [Module ℤ M] (n : ℕ) (F : SingularChains.Chains X n →ₗ[ℤ] M)
    (hF :
      ∀ b : SingularChains.Chains X (n + 1),
        F (((SingularChains.singularComplex X).d (n + 1) n).hom b) = 0)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    singularHomologyDesc n F hF
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) n c) =
      F c.1 :=
  SingularHomology.homologyDesc_cycleClass (SingularChains.singularComplex X) n _ _ c

/-- If `g : M →ₗ[ℤ] SingularHomology X n` sends `F c` to the class of `c` for every
cycle `c`, then `g ∘ singularHomologyDesc n F hF` is the identity on homology. -/
theorem Hurewicz.comp_singularHomologyDesc_eq_id {X : Type} [TopologicalSpace X] {M : Type*}
    [AddCommGroup M] [Module ℤ M] (n : ℕ) (F : SingularChains.Chains X n →ₗ[ℤ] M)
    (hF :
      ∀ b : SingularChains.Chains X (n + 1),
        F (((SingularChains.singularComplex X).d (n + 1) n).hom b) = 0)
    (g : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology X n)
    (hg :
      ∀ c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n,
        g (F c.1) =
          SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) n c) :
    g.comp (singularHomologyDesc n F hF) = LinearMap.id := by
  apply SingularHomology.homologyLinearMap_ext (SingularChains.singularComplex X) n
  intro c
  simpa only [LinearMap.comp_apply, singularHomologyDesc_cycleClass, LinearMap.id_apply] using
    hg c

/-! ### Parity of the constant simplex -/

/-- When `n + 1` is even, the alternating boundary sign sum `∑ (-1)^i` over
`Fin (n + 2)` equals `1`. -/
theorem Hurewicz.boundarySignSum_even (n : ℕ) (hn : Even (n + 1)) :
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val) = 1 := by
  rw [Fin.sum_neg_one_pow]
  have h : ¬Even (n + 2) := Nat.not_even_iff_odd.mpr hn.add_one
  exact if_neg h

/-- When `n + 1` is odd, the alternating boundary sign sum over `Fin (n + 2)` equals
`0`. -/
theorem Hurewicz.boundarySignSum_odd (n : ℕ) (hn : Odd (n + 1)) :
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val) = 0 := by
  rw [Fin.sum_neg_one_pow]
  have h : Even (n + 2) := hn.add_one
  exact if_pos h

/-- The boundary of the constant `(n + 1)`-simplex chain is the alternating sign sum
times the constant `n`-simplex chain. -/
theorem Hurewicz.boundary_constantSimplexChain {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) :
    ((SingularChains.singularComplex X).d (n + 1) n).hom (constantSimplexChain (n + 1) x) =
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val) • constantSimplexChain n x := by
  rw [constantSimplexChain, SingularChains.boundary_simplex]
  change (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • constantSimplexChain n x) = _
  exact
    (map_sum (zmultiplesHom (SingularChains.Chains X n) (constantSimplexChain n x))
        (fun i : Fin (n + 2) => (-1 : ℤ) ^ i.val) Finset.univ).symm

/-- For `n + 1` even, the boundary of the constant `(n + 1)`-simplex chain is the
constant `n`-simplex chain. -/
theorem Hurewicz.boundary_constantSimplexChain_even {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) (hn : Even (n + 1)) :
    ((SingularChains.singularComplex X).d (n + 1) n).hom (constantSimplexChain (n + 1) x) =
      constantSimplexChain n x := by
  rw [boundary_constantSimplexChain, boundarySignSum_even n hn, one_smul]

/-- For `n + 1` odd, the boundary of the constant `(n + 1)`-simplex chain vanishes. -/
theorem Hurewicz.boundary_constantSimplexChain_odd {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) (hn : Odd (n + 1)) :
    ((SingularChains.singularComplex X).d (n + 1) n).hom (constantSimplexChain (n + 1) x) = 0 := by
  rw [boundary_constantSimplexChain, boundarySignSum_odd n hn, zero_smul]

/-- For odd `n`, the constant `n`-simplex chain is a cycle. -/
theorem Hurewicz.constantSimplexChain_cycle_condition {X : Type} [TopologicalSpace X]
    (n : ℕ) (x : X) (hn : Odd n) :
    ((SingularChains.singularComplex X).d n (n - 1)).hom (constantSimplexChain n x) = 0 := by
  cases n with
  | zero => simp at hn
  | succ n => exact boundary_constantSimplexChain_odd n x hn

/-- The constant `n`-simplex chain viewed as a cycle, for odd `n`. -/
def Hurewicz.constantSimplexCycle {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    (hn : Odd n) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n :=
  SingularMayerVietoris.ModuleHomology.mkCycle (SingularChains.singularComplex X) n
    (constantSimplexChain n x) (constantSimplexChain_cycle_condition n x hn)

/-- The underlying chain of `constantSimplexCycle` is the constant simplex chain. -/
@[simp]
theorem Hurewicz.constantSimplexCycle_val {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    (hn : Odd n) : (constantSimplexCycle n x hn).1 = constantSimplexChain n x :=
  rfl

/-- For odd `n`, the homology class of `constantSimplexCycle` is `0`. -/
@[simp]
theorem Hurewicz.constantSimplexCycle_class {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    (hn : Odd n) :
    SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) n
        (constantSimplexCycle n x hn) =
      0 := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_zero_iff (SingularChains.singularComplex X)
        n _).mpr
  exact ⟨constantSimplexChain (n + 1) x, boundary_constantSimplexChain_even n x hn.add_one⟩

/-! ### Corrected simplices and chain augmentation -/

/-- For a simplex whose faces are all constant at `x`, the corrected chain (the simplex
minus the constant simplex) is a cycle. -/
theorem Hurewicz.correctedSimplexChain_boundary {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) (smp : SingularChains.SingularSimplex X (n + 1))
    (hfaces :
      ∀ i : Fin (n + 2),
        smp.comp (SingularChains.simplexFace n i) =
          ContinuousMap.const (SingularChains.Simplex n) x) :
    ((SingularChains.singularComplex X).d (n + 1) n).hom (correctedSimplexChain (n + 1) x smp) =
      0 := by
  rw [correctedSimplexChain, map_sub, constantSimplexChain, SingularChains.boundary_simplex,
    SingularChains.boundary_simplex]
  simp only [hfaces, ContinuousMap.const_comp, sub_self]

/-- The cycle formed by a boundary-constant simplex minus the constant simplex chain. -/
def Hurewicz.correctedSimplexCycle {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    (smp : SingularChains.SingularSimplex X (n + 1))
    (hfaces :
      ∀ i : Fin (n + 2),
        smp.comp (SingularChains.simplexFace n i) =
          ContinuousMap.const (SingularChains.Simplex n) x) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) (n + 1) :=
  SingularMayerVietoris.ModuleHomology.mkCycle (SingularChains.singularComplex X) (n + 1)
    (correctedSimplexChain (n + 1) x smp) (correctedSimplexChain_boundary n x smp hfaces)

/-- The underlying chain of `correctedSimplexCycle` is `smp`'s chain minus the constant
simplex chain. -/
@[simp]
theorem Hurewicz.correctedSimplexCycle_val {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    (smp : SingularChains.SingularSimplex X (n + 1))
    (hfaces :
      ∀ i : Fin (n + 2),
        smp.comp (SingularChains.simplexFace n i) =
          ContinuousMap.const (SingularChains.Simplex n) x) :
    (correctedSimplexCycle n x smp hfaces).1 =
      SingularChains.simplexChain X (n + 1) smp - constantSimplexChain (n + 1) x :=
  rfl

/-- `chainAugmentation` of the boundary of an `(n+1)`-chain equals the alternating
sign sum `∑ i, (-1)^i` times `chainAugmentation c`. -/
theorem Hurewicz.chainAugmentation_boundary (X : Type) [TopologicalSpace X] (n : ℕ)
    (c : SingularChains.Chains X (n + 1)) :
    Hurewicz.DegreeTwo.SimplyConnected.chainAugmentation X n
        (((SingularChains.singularComplex X).d (n + 1) n).hom c) =
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val) •
        Hurewicz.DegreeTwo.SimplyConnected.chainAugmentation X (n + 1) c := by
  have h :
    (Hurewicz.DegreeTwo.SimplyConnected.chainAugmentation X n).comp
        ((SingularChains.singularComplex X).d (n + 1) n).hom =
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val) •
        Hurewicz.DegreeTwo.SimplyConnected.chainAugmentation X (n + 1) := by
    apply SingularChains.chainMap_ext X (n + 1)
    intro smp
    simp only [LinearMap.comp_apply, SingularChains.boundary_simplex, map_sum, map_zsmul,
      Hurewicz.DegreeTwo.SimplyConnected.chainAugmentation_simplex, LinearMap.smul_apply,
      zsmul_eq_mul, mul_one, Int.cast_id]
  exact LinearMap.congr_fun h c

/-- For `n + 1` even, `chainAugmentation` of the boundary of `c` equals
`chainAugmentation c` (the sign sum is `1`). -/
theorem Hurewicz.chainAugmentation_boundary_even (X : Type) [TopologicalSpace X] (n : ℕ)
    (hn : Even (n + 1)) (c : SingularChains.Chains X (n + 1)) :
    Hurewicz.DegreeTwo.SimplyConnected.chainAugmentation X n
        (((SingularChains.singularComplex X).d (n + 1) n).hom c) =
      Hurewicz.DegreeTwo.SimplyConnected.chainAugmentation X (n + 1) c := by
  rw [chainAugmentation_boundary, boundarySignSum_even n hn, one_smul]

/-- For even positive `n`, `chainAugmentation` of an `n`-cycle vanishes. -/
theorem Hurewicz.chainAugmentation_evenCycle (X : Type) [TopologicalSpace X] (n : ℕ)
    (hn : Even n) (hpos : 0 < n)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    Hurewicz.DegreeTwo.SimplyConnected.chainAugmentation X n c.1 = 0 := by
  cases n with
  | zero => exact False.elim (Nat.lt_irrefl 0 hpos)
  | succ n =>
    rw [← chainAugmentation_boundary_even X n hn]
    have hc : ((SingularChains.singularComplex X).d (n + 1) n).hom c.1 = 0 :=
      SingularMayerVietoris.ModuleHomology.cycle_condition (SingularChains.singularComplex X)
        (n + 1) c
    rw [hc, map_zero]

/-- On an even-degree cycle, `chainLift` of `smp ↦ f smp - m` equals `chainLift` of
`f` (the constant correction vanishes). -/
theorem Hurewicz.chainLift_sub_constant_evenCycle (X : Type) [TopologicalSpace X] {M : Type}
    [AddCommGroup M] [Module ℤ M] (n : ℕ) (hn : Even n) (hpos : 0 < n)
    (f : SingularChains.SingularSimplex X n → M) (m : M)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    SingularChains.chainLift X n (fun smp => f smp - m) c.1 = SingularChains.chainLift X n f c.1 := by
  rw [Hurewicz.DegreeTwo.SimplyConnected.chainLift_sub_constant,
    chainAugmentation_evenCycle X n hn hpos, zero_smul, sub_zero]

/-! ### Coherent cube endpoints -/

/-- If the tail sums of a simplex point at two indices `i < j` coincide, the
`j`-th barycentric coordinate vanishes. -/
theorem Hurewicz.simplex_coordinate_zero_of_tail_eq {n : ℕ} (s : SingularChains.Simplex n)
    {i j : Fin n} (hij : i < j)
    (h :
      (∑ k : Fin (n + 1), if i.val < k.val then s k else 0) =
        ∑ k : Fin (n + 1), if j.val < k.val then s k else 0) :
    s i.succ = 0 := by
  classical
  let A := Finset.univ.filter (fun k : Fin (n + 1) => i.val < k.val)
  let B := Finset.univ.filter (fun k : Fin (n + 1) => j.val < k.val)
  have hAB : (∑ k ∈ A, s k) = ∑ k ∈ B, s k := by simpa only [A, B, Finset.sum_filter] using h
  have hiB : i.succ ∉ B := by
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_succ, not_lt]
    exact hij
  have hsub : Insert.insert i.succ B ⊆ A := by
    intro k hk
    rcases Finset.mem_insert.mp hk with hk | hk
    · subst k
      simp [A]
    · have hjk : j.val < k.val := (Finset.mem_filter.mp hk).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_trans hij hjk⟩
  have hle : s i.succ + ∑ k ∈ B, s k ≤ ∑ k ∈ A, s k := by
    calc
      s i.succ + ∑ k ∈ B, s k = ∑ k ∈ Insert.insert i.succ B, s k := (Finset.sum_insert hiB).symm
      _ ≤ ∑ k ∈ A, s k :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => stdSimplex.zero_le s k)
  exact le_antisymm (by linarith) (stdSimplex.zero_le s i.succ)

/-- If two ordered coordinates `e i < e j` of `cubeSimplex e s` coincide, then `s` lies
on the simplex boundary. -/
theorem Hurewicz.cubeSimplex_ordered_coordinate_equality_boundary {n : ℕ}
    (e : Equiv.Perm (Fin n)) (s : SingularChains.Simplex n) {i j : Fin n} (hij : i ≠ j)
    (h : CubeTriangulation.cubeSimplex e s (e i) = CubeTriangulation.cubeSimplex e s (e j)) :
    s ∈ Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary n := by
  have hreal := congrArg (fun t : (unitInterval) => (t : ℝ)) h
  rw [CubeTriangulation.cubeSimplex_coordinate, CubeTriangulation.cubeSimplex_coordinate] at hreal
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact ⟨i.succ, simplex_coordinate_zero_of_tail_eq s hlt hreal⟩
  · exact ⟨j.succ, simplex_coordinate_zero_of_tail_eq s hgt hreal.symm⟩

/-- If two distinct coordinates of `cubeSimplex e s` coincide, then `s` lies on the
simplex boundary. -/
theorem Hurewicz.cubeSimplex_coordinate_equality_boundary {n : ℕ} (e : Equiv.Perm (Fin n))
    (s : SingularChains.Simplex n) {i j : Fin n} (hij : i ≠ j)
    (h : CubeTriangulation.cubeSimplex e s i = CubeTriangulation.cubeSimplex e s j) :
    s ∈ Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary n := by
  apply cubeSimplex_ordered_coordinate_equality_boundary e s (e.symm.injective.ne hij)
  simpa only [Equiv.apply_symm_apply] using h

/-- The coherent cube endpoint is based at `x` on the boundary of each Kuhn cell:
every boundary point of `cubeSimplex e` maps to `x`. -/
theorem Hurewicz.coherentCubeEndpoint_cell_boundary {n : ℕ} {X : Type} [TopologicalSpace X]
    {x : X}
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (hface : Hurewicz.DegreeTwo.SimplyConnected.FaceCompatibleHomotopies n H H')
    (hconst :
      H (ContinuousMap.const (SingularChains.Simplex n) x) =
        ContinuousMap.const ((unitInterval) × SingularChains.Simplex n) x)
    (hone :
      ∀ smp,
        Hurewicz.DegreeTwo.SimplyConnected.timeSlice (H smp) 1 =
          ContinuousMap.const (SingularChains.Simplex n) x)
    (p : GenLoop (Fin (n + 1)) X x) (e : Equiv.Perm (Fin (n + 1)))
    (s : SingularChains.Simplex (n + 1))
    (hs : s ∈ Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary (n + 1)) :
    CubeGluing.coherentCubeEndpoint H H' hface hconst p (CubeTriangulation.cubeSimplex e s) = x :=
  by
  have he :=
    congrArg (fun f : C(SingularChains.Simplex (n + 1), X) => f s)
      (CubeGluing.coherentCubeEndpoint_cell H H' hface hconst p e)
  exact he.trans (simplexEndpoint_boundary H H' hface x hone _ s hs)

/-- The coherent cube endpoint is internally based for the native subdivision. -/
theorem Hurewicz.coherentCubeEndpoint_internalBased {n : ℕ} {X : Type} [TopologicalSpace X]
    {x : X}
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (hface : Hurewicz.DegreeTwo.SimplyConnected.FaceCompatibleHomotopies n H H')
    (hconst :
      H (ContinuousMap.const (SingularChains.Simplex n) x) =
        ContinuousMap.const ((unitInterval) × SingularChains.Simplex n) x)
    (hone :
      ∀ smp,
        Hurewicz.DegreeTwo.SimplyConnected.timeSlice (H smp) 1 =
          ContinuousMap.const (SingularChains.Simplex n) x)
    (p : GenLoop (Fin (n + 1)) X x) (u : Fin (n + 1) → (unitInterval)) (i j : Fin (n + 1))
    (hij : i ≠ j) (hu : u i = u j) : CubeGluing.coherentCubeEndpoint H H' hface hconst p u = x := by
  obtain ⟨e, s, rfl⟩ := CubeTriangulation.exists_cubeSimplex u
  exact
    coherentCubeEndpoint_cell_boundary H H' hface hconst hone p e s
      (cubeSimplex_coordinate_equality_boundary e s hij hu)

/-! ### Normalized cycle assignments -/

/-- The linear map on `(n + 1)`-chains assigning to each simplex the corrected cycle of
its normalized based simplex `f smp`. -/
def Hurewicz.normalizedCycleAssignment {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    (f : SingularChains.SingularSimplex X (n + 1) → SimplexGeometry.BasedSimplex (n + 1) x) :
    SingularChains.Chains X (n + 1) →ₗ[ℤ]
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) (n + 1) :=
  SingularChains.chainLift X (n + 1) fun smp =>
    correctedSimplexCycle n x (f smp).val (SimplexGeometry.basedSimplex_face (f smp))

/-- On a generator simplex, `normalizedCycleAssignment` returns the corrected cycle of
`f smp`. -/
@[simp]
theorem Hurewicz.normalizedCycleAssignment_simplex {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) (f : SingularChains.SingularSimplex X (n + 1) → SimplexGeometry.BasedSimplex (n + 1) x)
    (smp : SingularChains.SingularSimplex X (n + 1)) :
    normalizedCycleAssignment n x f (SingularChains.simplexChain X (n + 1) smp) =
      correctedSimplexCycle n x (f smp).val (SimplexGeometry.basedSimplex_face (f smp)) :=
  SingularChains.chainLift_simplex X (n + 1) _ smp

/-- The underlying chain of `normalizedCycleAssignment c` is the lift of
`smp ↦ simplexChain (f smp) - constantSimplexChain x` applied to `c`. -/
theorem Hurewicz.normalizedCycleAssignment_val {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) (f : SingularChains.SingularSimplex X (n + 1) → SimplexGeometry.BasedSimplex (n + 1) x)
    (c : SingularChains.Chains X (n + 1)) :
    (normalizedCycleAssignment n x f c).val =
      SingularChains.chainLift X (n + 1)
        (fun smp =>
          SingularChains.simplexChain X (n + 1) (f smp).val - constantSimplexChain (n + 1) x)
        c := by
  have h :
    (SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X)
            (n + 1)).subtype.comp
        (normalizedCycleAssignment n x f) =
      SingularChains.chainLift X (n + 1)
        (fun smp =>
          SingularChains.simplexChain X (n + 1) (f smp).val - constantSimplexChain (n + 1) x) := by
    apply SingularChains.chainMap_ext X (n + 1)
    intro smp
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, normalizedCycleAssignment_simplex,
      correctedSimplexCycle_val, SingularChains.chainLift_simplex]
  exact LinearMap.congr_fun h c

/-- When `f` is the time-`1` endpoint of `H'`, the underlying chain of
`normalizedCycleAssignment c` equals the endpoint chain minus the chain augmentation
times the constant simplex chain. -/
theorem Hurewicz.normalizedCycleAssignment_val_endpoint {X : Type} [TopologicalSpace X]
    (n : ℕ) (x : X)
    (f : SingularChains.SingularSimplex X (n + 1) → SimplexGeometry.BasedSimplex (n + 1) x)
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (hf : ∀ smp, (f smp).val = Hurewicz.DegreeTwo.SimplyConnected.timeSlice (H' smp) 1)
    (c : SingularChains.Chains X (n + 1)) :
    (normalizedCycleAssignment n x f c).val =
      Hurewicz.DegreeTwo.SimplyConnected.simplexEndpointOperator (n + 1) H' 1 c -
        Hurewicz.DegreeTwo.SimplyConnected.chainAugmentation X (n + 1) c •
          constantSimplexChain (n + 1) x := by
  rw [normalizedCycleAssignment_val, Hurewicz.DegreeTwo.SimplyConnected.chainLift_sub_constant]
  have hmap :
    SingularChains.chainLift X (n + 1)
        (fun smp => SingularChains.simplexChain X (n + 1) (f smp).val) =
      Hurewicz.DegreeTwo.SimplyConnected.simplexEndpointOperator (n + 1) H' 1 := by
    apply SingularChains.chainMap_ext X (n + 1)
    intro smp
    rw [SingularChains.chainLift_simplex,
      Hurewicz.DegreeTwo.SimplyConnected.simplexEndpointOperator_simplex, hf]
  rw [hmap]

/-- For `n + 1` even, the normalized cycle assignment of a cycle equals its
straightened cycle. -/
theorem Hurewicz.normalizedCycleAssignment_evenCycle {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) (f : SingularChains.SingularSimplex X (n + 1) → SimplexGeometry.BasedSimplex (n + 1) x)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (hface : Hurewicz.DegreeTwo.SimplyConnected.FaceCompatibleHomotopies n H H')
    (hf : ∀ smp, (f smp).val = Hurewicz.DegreeTwo.SimplyConnected.timeSlice (H' smp) 1)
    (heven : Even (n + 1))
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) (n + 1)) :
    normalizedCycleAssignment n x f c.val = straightenedCycle n H H' hface c := by
  apply Subtype.ext
  rw [normalizedCycleAssignment_val_endpoint n x f H' hf,
    chainAugmentation_evenCycle X (n + 1) heven (Nat.zero_lt_succ n), zero_smul, sub_zero,
    straightenedCycle_val]

/-- For `n + 1` odd, the normalized cycle assignment of a cycle equals its straightened
cycle minus the augmentation times the constant simplex cycle. -/
theorem Hurewicz.normalizedCycleAssignment_oddCycle {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) (f : SingularChains.SingularSimplex X (n + 1) → SimplexGeometry.BasedSimplex (n + 1) x)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (hface : Hurewicz.DegreeTwo.SimplyConnected.FaceCompatibleHomotopies n H H')
    (hf : ∀ smp, (f smp).val = Hurewicz.DegreeTwo.SimplyConnected.timeSlice (H' smp) 1)
    (hodd : Odd (n + 1))
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) (n + 1)) :
    normalizedCycleAssignment n x f c.val =
      straightenedCycle n H H' hface c -
        Hurewicz.DegreeTwo.SimplyConnected.chainAugmentation X (n + 1) c.val •
          constantSimplexCycle (n + 1) x hodd := by
  apply Subtype.ext
  change
    (normalizedCycleAssignment n x f c.val).val =
      (straightenedCycle n H H' hface c).val -
        Hurewicz.DegreeTwo.SimplyConnected.chainAugmentation X (n + 1) c.val •
          (constantSimplexCycle (n + 1) x hodd).val
  rw [normalizedCycleAssignment_val_endpoint n x f H' hf, straightenedCycle_val,
    constantSimplexCycle_val]

/-- The normalized cycle assignment preserves homology classes: applied to a cycle `c`
it represents the same class as `c`. -/
theorem Hurewicz.normalizedCycleAssignment_class {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) (f : SingularChains.SingularSimplex X (n + 1) → SimplexGeometry.BasedSimplex (n + 1) x)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (hface : Hurewicz.DegreeTwo.SimplyConnected.FaceCompatibleHomotopies n H H')
    (h₀ : ∀ smp, Hurewicz.DegreeTwo.SimplyConnected.timeSlice (H' smp) 0 = smp)
    (hf : ∀ smp, (f smp).val = Hurewicz.DegreeTwo.SimplyConnected.timeSlice (H' smp) 1)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) (n + 1)) :
    SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) (n + 1)
        (normalizedCycleAssignment n x f c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) (n + 1)
        c := by
  by_cases heven : Even (n + 1)
  · rw [normalizedCycleAssignment_evenCycle n x f H H' hface hf heven]
    exact straightenedCycle_class n H H' hface h₀ c
  · have hodd : Odd (n + 1) := Nat.not_even_iff_odd.mp heven
    rw [normalizedCycleAssignment_oddCycle n x f H H' hface hf hodd, map_sub, map_zsmul,
      constantSimplexCycle_class, zsmul_zero, sub_zero]
    exact straightenedCycle_class n H H' hface h₀ c

