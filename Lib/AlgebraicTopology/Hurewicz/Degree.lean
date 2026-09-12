/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.CubeGluing

set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

noncomputable section

namespace Mathoverflow1973

def Hurewicz.nativeCubeNullHomotopy {n : ℕ} {X : Type*} [TopologicalSpace X] {x : X}
    [hπ : Subsingleton (π_ n X x)] (p : GenLoop (Fin n) X x) :
    p.val.HomotopyRel (ContinuousMap.const (Fin n → (unitInterval)) x) (Cube.boundary (Fin n)) :=
  Classical.choice
    (show GenLoop.Homotopic p GenLoop.const from
      Quotient.exact (@Subsingleton.elim (π_ n X x) hπ ⟦p⟧ ⟦GenLoop.const⟧))

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

def Hurewicz.basedSimplexNativeLoop {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedSimplex n x) : GenLoop (Fin n) X x :=
  ⟨τ.val.comp ⟨(simplexCubeHomeomorph n).symm, (simplexCubeHomeomorph n).symm.continuous⟩,
    fun u hu => τ.property _ ((simplexCubeHomeomorph_symm_boundary_iff n u).mpr hu)⟩

theorem Hurewicz.basedSimplexNativeLoop_comp_homeomorph {n : ℕ} {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedSimplex n x) :
    (basedSimplexNativeLoop τ).val.comp
        ⟨simplexCubeHomeomorph n, (simplexCubeHomeomorph n).continuous⟩ =
      τ.val := by
  apply ContinuousMap.ext
  intro s
  change τ.val ((simplexCubeHomeomorph n).symm (simplexCubeHomeomorph n s)) = τ.val s
  rw [Homeomorph.symm_apply_apply]

def Hurewicz.simplexNullHomotopyUnnormalized {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    [Subsingleton (π_ n X x)] (τ : BasedSimplex n x) :
    τ.val.HomotopyRel (ContinuousMap.const (SingularChains.Simplex n) x)
      (SecondHurewicz.SimplyConnected.simplexBoundary n) :=
  ContinuousMap.HomotopyRel.cast
    (nativeCubeNullHomotopy_comp (basedSimplexNativeLoop τ)
      ⟨simplexCubeHomeomorph n, (simplexCubeHomeomorph n).continuous⟩
      (SecondHurewicz.SimplyConnected.simplexBoundary n)
      (fun s hs => (simplexCubeHomeomorph_boundary_iff n s).mpr hs))
    (basedSimplexNativeLoop_comp_homeomorph τ) rfl

def Hurewicz.simplexNullHomotopy {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    [Subsingleton (π_ n X x)] (τ : BasedSimplex n x) :
    τ.val.HomotopyRel (ContinuousMap.const (SingularChains.Simplex n) x)
      (SecondHurewicz.SimplyConnected.simplexBoundary n) := by
  classical
    exact
    if h : τ = constantBasedSimplex n x then
      ContinuousMap.HomotopyRel.cast
        (ContinuousMap.HomotopyRel.refl (ContinuousMap.const (SingularChains.Simplex n) x)
          (SecondHurewicz.SimplyConnected.simplexBoundary n))
        (congrArg (fun υ : BasedSimplex n x => υ.val) h).symm rfl
    else simplexNullHomotopyUnnormalized τ

@[simp]
theorem Hurewicz.simplexNullHomotopy_zero {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    [Subsingleton (π_ n X x)] (τ : BasedSimplex n x) (s : SingularChains.Simplex n) :
    simplexNullHomotopy τ (0, s) = τ.val s :=
  (simplexNullHomotopy τ).apply_zero s

@[simp]
theorem Hurewicz.simplexNullHomotopy_one {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    [Subsingleton (π_ n X x)] (τ : BasedSimplex n x) (s : SingularChains.Simplex n) :
    simplexNullHomotopy τ (1, s) = x :=
  (simplexNullHomotopy τ).apply_one s

@[simp]
theorem Hurewicz.simplexNullHomotopy_constant {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) [Subsingleton (π_ n X x)] :
    simplexNullHomotopy (constantBasedSimplex n x) =
      ContinuousMap.HomotopyRel.refl (ContinuousMap.const (SingularChains.Simplex n) x)
        (SecondHurewicz.SimplyConnected.simplexBoundary n) := by
  classical
  unfold simplexNullHomotopy
  rw [dif_pos rfl]
  rfl

@[simp]
theorem Hurewicz.simplexNullHomotopy_constant_toContinuousMap {X : Type}
    [TopologicalSpace X] (n : ℕ) (x : X) [Subsingleton (π_ n X x)] :
    (simplexNullHomotopy (constantBasedSimplex n x)).toContinuousMap =
      ContinuousMap.const ((unitInterval) × SingularChains.Simplex n) x := by
  rw [simplexNullHomotopy_constant]
  rfl

def Hurewicz.simplexStraighteningHomotopy {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    [Subsingleton (π_ n X x)] (smp : SingularChains.SingularSimplex X n) :
    C((unitInterval) × SingularChains.Simplex n, X) := by
  classical
    exact
    if h : ∀ s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n, smp s = x then
      (simplexNullHomotopy (⟨smp, h⟩ : BasedSimplex n x)).toContinuousMap
    else SecondHurewicz.SimplyConnected.stationarySimplexHomotopy n smp

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

theorem Hurewicz.simplexStraighteningHomotopy_one {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) [Subsingleton (π_ n X x)] (smp : SingularChains.SingularSimplex X n)
    (h : ∀ s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n, smp s = x)
    (s : SingularChains.Simplex n) : simplexStraighteningHomotopy n x smp (1, s) = x := by
  classical
  rw [simplexStraighteningHomotopy, dif_pos h]
  exact simplexNullHomotopy_one (⟨smp, h⟩ : BasedSimplex n x) s

theorem Hurewicz.simplexStraighteningHomotopy_boundary {X : Type} [TopologicalSpace X]
    (n : ℕ) (x : X) [Subsingleton (π_ n X x)] (smp : SingularChains.SingularSimplex X n)
    (r : (unitInterval)) (s : SingularChains.Simplex n)
    (hs : s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n) :
    simplexStraighteningHomotopy n x smp (r, s) = smp s := by
  classical
  unfold simplexStraighteningHomotopy
  split
  · rename_i h
    exact (simplexNullHomotopy (⟨smp, h⟩ : BasedSimplex n x)).eq_fst r hs
  · rfl

@[simp]
theorem Hurewicz.simplexStraighteningHomotopy_const {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) [Subsingleton (π_ n X x)] :
    simplexStraighteningHomotopy n x (ContinuousMap.const (SingularChains.Simplex n) x) =
      ContinuousMap.const ((unitInterval) × SingularChains.Simplex n) x := by
  classical
  have h :
    ∀ s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n,
      (ContinuousMap.const (SingularChains.Simplex n) x) s = x :=
    fun _ _ => rfl
  rw [simplexStraighteningHomotopy, dif_pos h]
  exact simplexNullHomotopy_constant_toContinuousMap n x

theorem Hurewicz.simplexStraighteningHomotopy_face {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) [Subsingleton (π_ (n + 1) X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n
      (SecondHurewicz.SimplyConnected.stationarySimplexHomotopy n)
      (simplexStraighteningHomotopy (n + 1) x) := by
  intro smp i
  ext u
  change
    simplexStraighteningHomotopy (n + 1) x smp (u.1, SingularChains.simplexFace n i u.2) =
      smp (SingularChains.simplexFace n i u.2)
  exact
    simplexStraighteningHomotopy_boundary (n + 1) x smp u.1 _
      ⟨i, SingularChains.simplexFace_apply_self n i u.2⟩

theorem Hurewicz.simplexEndpoint_face_constant {X : Type} [TopologicalSpace X] {n : ℕ}
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H') (x : X)
    (hone :
      ∀ smp,
        SecondHurewicz.SimplyConnected.timeSlice (H smp) 1 =
          ContinuousMap.const (SingularChains.Simplex n) x)
    (smp : SingularChains.SingularSimplex X (n + 1)) (i : Fin (n + 2)) :
    (SecondHurewicz.SimplyConnected.timeSlice (H' smp) 1).comp (SingularChains.simplexFace n i) =
      ContinuousMap.const (SingularChains.Simplex n) x :=
  (SecondHurewicz.SimplyConnected.timeSlice_face hface smp i 1).trans (hone _)

theorem Hurewicz.simplexEndpoint_boundary {X : Type} [TopologicalSpace X] {n : ℕ}
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H') (x : X)
    (hone :
      ∀ smp,
        SecondHurewicz.SimplyConnected.timeSlice (H smp) 1 =
          ContinuousMap.const (SingularChains.Simplex n) x)
    (smp : SingularChains.SingularSimplex X (n + 1)) (s : SingularChains.Simplex (n + 1))
    (hs : s ∈ SecondHurewicz.SimplyConnected.simplexBoundary (n + 1)) :
    SecondHurewicz.SimplyConnected.timeSlice (H' smp) 1 s = x := by
  obtain ⟨i, t, ht⟩ :=
    SecondHurewicz.SimplyConnected.simplexBoundary_exists_face n
      (⟨s, hs⟩ : SecondHurewicz.SimplyConnected.SimplexBoundary (n + 1))
  have he : SingularChains.simplexFace n i t = s := congrArg Subtype.val ht
  rw [← he]
  exact
    congrArg (fun f : C(SingularChains.Simplex n, X) => f t)
      (simplexEndpoint_face_constant H H' hface x hone smp i)

def Hurewicz.straightenedCycle {X : Type} [TopologicalSpace X] (n : ℕ)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (h : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H')
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) (n + 1)) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) (n + 1) :=
  SingularMayerVietoris.ModuleHomology.mkCycle (SingularChains.singularComplex X) (n + 1)
    (SecondHurewicz.SimplyConnected.simplexEndpointOperator (n + 1) H' 1 c.1)
    (by
      have hc : ((SingularChains.singularComplex X).d (n + 1) n).hom c.1 = 0 := by
        exact
          SingularMayerVietoris.ModuleHomology.cycle_condition (SingularChains.singularComplex X)
            (n + 1) c
      rw [Nat.add_sub_cancel,
        SecondHurewicz.SimplyConnected.simplexEndpointOperator_boundary n H H' h, hc, map_zero])

@[simp]
theorem Hurewicz.straightenedCycle_val {X : Type} [TopologicalSpace X] (n : ℕ)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (h : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H')
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) (n + 1)) :
    (straightenedCycle n H H' h c).1 =
      SecondHurewicz.SimplyConnected.simplexEndpointOperator (n + 1) H' 1 c.1 :=
  rfl

theorem Hurewicz.straightenedCycle_boundary {X : Type} [TopologicalSpace X] (n : ℕ)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (h : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H')
    (h₀ : ∀ smp, SecondHurewicz.SimplyConnected.timeSlice (H' smp) 0 = smp)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) (n + 1)) :
    ((SingularChains.singularComplex X).d (n + 2) (n + 1)).hom
        (SecondHurewicz.SimplyConnected.simplexPrismOperator (n + 1) H' c.1) =
      (straightenedCycle n H H' h c).1 - c.1 := by
  have hc : ((SingularChains.singularComplex X).d (n + 1) n).hom c.1 = 0 := by
    exact
      SingularMayerVietoris.ModuleHomology.cycle_condition (SingularChains.singularComplex X)
        (n + 1) c
  rw [SecondHurewicz.SimplyConnected.simplexPrismOperator_boundary n H H' h,
    SecondHurewicz.SimplyConnected.simplexEndpointOperator_zero (n + 1) H' h₀, hc, map_zero,
    sub_zero]
  rfl

theorem Hurewicz.straightenedCycle_class {X : Type} [TopologicalSpace X] (n : ℕ)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (h : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H')
    (h₀ : ∀ smp, SecondHurewicz.SimplyConnected.timeSlice (H' smp) 0 = smp)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) (n + 1)) :
    SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) (n + 1)
        (straightenedCycle n H H' h c) =
      SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) (n + 1)
        c := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (SingularChains.singularComplex X)
        (n + 1) _ _).mpr
  exact
    ⟨SecondHurewicz.SimplyConnected.simplexPrismOperator (n + 1) H' c.1,
      straightenedCycle_boundary n H H' h h₀ c⟩

def Hurewicz.singularHomologyDesc {X : Type} [TopologicalSpace X] {M : Type*}
    [AddCommGroup M] [Module ℤ M] (n : ℕ) (F : SingularChains.Chains X n →ₗ[ℤ] M)
    (hF :
      ∀ b : SingularChains.Chains X (n + 1),
        F (((SingularChains.singularComplex X).d (n + 1) n).hom b) = 0) :
    SingularMayerVietoris.SingularHomology X n →ₗ[ℤ] M :=
  PeriodTorusHigherHomology.homologyDesc (SingularChains.singularComplex X) n
    (F.comp
      (SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n).subtype)
    (fun b => hF b)

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
  PeriodTorusHigherHomology.homologyDesc_cycleClass (SingularChains.singularComplex X) n _ _ c

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
  apply PeriodTorusHigherHomology.homologyLinearMap_ext (SingularChains.singularComplex X) n
  intro c
  simpa only [LinearMap.comp_apply, singularHomologyDesc_cycleClass, LinearMap.id_apply] using
    hg c

theorem Hurewicz.boundarySignSum_even (n : ℕ) (hn : Even (n + 1)) :
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val) = 1 := by
  rw [Fin.sum_neg_one_pow]
  have h : ¬Even (n + 2) := Nat.not_even_iff_odd.mpr hn.add_one
  exact if_neg h

theorem Hurewicz.boundarySignSum_odd (n : ℕ) (hn : Odd (n + 1)) :
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val) = 0 := by
  rw [Fin.sum_neg_one_pow]
  have h : Even (n + 2) := hn.add_one
  exact if_pos h

theorem Hurewicz.boundary_constantSimplexChain {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) :
    ((SingularChains.singularComplex X).d (n + 1) n).hom (constantSimplexChain (n + 1) x) =
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val) • constantSimplexChain n x := by
  rw [constantSimplexChain, SingularChains.boundary_simplex]
  change (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • constantSimplexChain n x) = _
  exact
    (map_sum (zmultiplesHom (SingularChains.Chains X n) (constantSimplexChain n x))
        (fun i : Fin (n + 2) => (-1 : ℤ) ^ i.val) Finset.univ).symm

theorem Hurewicz.boundary_constantSimplexChain_even {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) (hn : Even (n + 1)) :
    ((SingularChains.singularComplex X).d (n + 1) n).hom (constantSimplexChain (n + 1) x) =
      constantSimplexChain n x := by
  rw [boundary_constantSimplexChain, boundarySignSum_even n hn, one_smul]

theorem Hurewicz.boundary_constantSimplexChain_odd {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) (hn : Odd (n + 1)) :
    ((SingularChains.singularComplex X).d (n + 1) n).hom (constantSimplexChain (n + 1) x) = 0 := by
  rw [boundary_constantSimplexChain, boundarySignSum_odd n hn, zero_smul]

theorem Hurewicz.constantSimplexChain_cycle_condition {X : Type} [TopologicalSpace X]
    (n : ℕ) (x : X) (hn : Odd n) :
    ((SingularChains.singularComplex X).d n (n - 1)).hom (constantSimplexChain n x) = 0 := by
  cases n with
  | zero => simp at hn
  | succ n => exact boundary_constantSimplexChain_odd n x hn

def Hurewicz.constantSimplexCycle {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    (hn : Odd n) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n :=
  SingularMayerVietoris.ModuleHomology.mkCycle (SingularChains.singularComplex X) n
    (constantSimplexChain n x) (constantSimplexChain_cycle_condition n x hn)

@[simp]
theorem Hurewicz.constantSimplexCycle_val {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    (hn : Odd n) : (constantSimplexCycle n x hn).1 = constantSimplexChain n x :=
  rfl

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

def Hurewicz.correctedSimplexCycle {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    (smp : SingularChains.SingularSimplex X (n + 1))
    (hfaces :
      ∀ i : Fin (n + 2),
        smp.comp (SingularChains.simplexFace n i) =
          ContinuousMap.const (SingularChains.Simplex n) x) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) (n + 1) :=
  SingularMayerVietoris.ModuleHomology.mkCycle (SingularChains.singularComplex X) (n + 1)
    (correctedSimplexChain (n + 1) x smp) (correctedSimplexChain_boundary n x smp hfaces)

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

theorem Hurewicz.chainAugmentation_boundary (X : Type) [TopologicalSpace X] (n : ℕ)
    (c : SingularChains.Chains X (n + 1)) :
    SecondHurewicz.SimplyConnected.chainAugmentation X n
        (((SingularChains.singularComplex X).d (n + 1) n).hom c) =
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val) •
        SecondHurewicz.SimplyConnected.chainAugmentation X (n + 1) c := by
  have h :
    (SecondHurewicz.SimplyConnected.chainAugmentation X n).comp
        ((SingularChains.singularComplex X).d (n + 1) n).hom =
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val) •
        SecondHurewicz.SimplyConnected.chainAugmentation X (n + 1) := by
    apply SingularChains.chainMap_ext X (n + 1)
    intro smp
    simp only [LinearMap.comp_apply, SingularChains.boundary_simplex, map_sum, map_zsmul,
      SecondHurewicz.SimplyConnected.chainAugmentation_simplex, LinearMap.smul_apply,
      zsmul_eq_mul, mul_one, Int.cast_id]
  exact LinearMap.congr_fun h c

theorem Hurewicz.chainAugmentation_boundary_even (X : Type) [TopologicalSpace X] (n : ℕ)
    (hn : Even (n + 1)) (c : SingularChains.Chains X (n + 1)) :
    SecondHurewicz.SimplyConnected.chainAugmentation X n
        (((SingularChains.singularComplex X).d (n + 1) n).hom c) =
      SecondHurewicz.SimplyConnected.chainAugmentation X (n + 1) c := by
  rw [chainAugmentation_boundary, boundarySignSum_even n hn, one_smul]

theorem Hurewicz.chainAugmentation_evenCycle (X : Type) [TopologicalSpace X] (n : ℕ)
    (hn : Even n) (hpos : 0 < n)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    SecondHurewicz.SimplyConnected.chainAugmentation X n c.1 = 0 := by
  cases n with
  | zero => exact False.elim (Nat.lt_irrefl 0 hpos)
  | succ n =>
    rw [← chainAugmentation_boundary_even X n hn]
    have hc : ((SingularChains.singularComplex X).d (n + 1) n).hom c.1 = 0 :=
      SingularMayerVietoris.ModuleHomology.cycle_condition (SingularChains.singularComplex X)
        (n + 1) c
    rw [hc, map_zero]

theorem Hurewicz.chainLift_sub_constant_evenCycle (X : Type) [TopologicalSpace X] {M : Type}
    [AddCommGroup M] [Module ℤ M] (n : ℕ) (hn : Even n) (hpos : 0 < n)
    (f : SingularChains.SingularSimplex X n → M) (m : M)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) n) :
    SingularChains.chainLift X n (fun smp => f smp - m) c.1 = SingularChains.chainLift X n f c.1 := by
  rw [SecondHurewicz.SimplyConnected.chainLift_sub_constant,
    chainAugmentation_evenCycle X n hn hpos, zero_smul, sub_zero]

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

theorem Hurewicz.cubeSimplex_ordered_coordinate_equality_boundary {n : ℕ}
    (e : Equiv.Perm (Fin n)) (s : SingularChains.Simplex n) {i j : Fin n} (hij : i ≠ j)
    (h : CubeTriangulation.cubeSimplex e s (e i) = CubeTriangulation.cubeSimplex e s (e j)) :
    s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n := by
  have hreal := congrArg (fun t : (unitInterval) => (t : ℝ)) h
  rw [CubeTriangulation.cubeSimplex_coordinate, CubeTriangulation.cubeSimplex_coordinate] at hreal
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact ⟨i.succ, simplex_coordinate_zero_of_tail_eq s hlt hreal⟩
  · exact ⟨j.succ, simplex_coordinate_zero_of_tail_eq s hgt hreal.symm⟩

theorem Hurewicz.cubeSimplex_coordinate_equality_boundary {n : ℕ} (e : Equiv.Perm (Fin n))
    (s : SingularChains.Simplex n) {i j : Fin n} (hij : i ≠ j)
    (h : CubeTriangulation.cubeSimplex e s i = CubeTriangulation.cubeSimplex e s j) :
    s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n := by
  apply cubeSimplex_ordered_coordinate_equality_boundary e s (e.symm.injective.ne hij)
  simpa only [Equiv.apply_symm_apply] using h

theorem Hurewicz.coherentCubeEndpoint_cell_boundary {n : ℕ} {X : Type} [TopologicalSpace X]
    {x : X}
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H')
    (hconst :
      H (ContinuousMap.const (SingularChains.Simplex n) x) =
        ContinuousMap.const ((unitInterval) × SingularChains.Simplex n) x)
    (hone :
      ∀ smp,
        SecondHurewicz.SimplyConnected.timeSlice (H smp) 1 =
          ContinuousMap.const (SingularChains.Simplex n) x)
    (p : GenLoop (Fin (n + 1)) X x) (e : Equiv.Perm (Fin (n + 1)))
    (s : SingularChains.Simplex (n + 1))
    (hs : s ∈ SecondHurewicz.SimplyConnected.simplexBoundary (n + 1)) :
    CubeGluing.coherentCubeEndpoint H H' hface hconst p (CubeTriangulation.cubeSimplex e s) = x :=
  by
  have he :=
    congrArg (fun f : C(SingularChains.Simplex (n + 1), X) => f s)
      (CubeGluing.coherentCubeEndpoint_cell H H' hface hconst p e)
  exact he.trans (simplexEndpoint_boundary H H' hface x hone _ s hs)

theorem Hurewicz.coherentCubeEndpoint_internalBased {n : ℕ} {X : Type} [TopologicalSpace X]
    {x : X}
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H')
    (hconst :
      H (ContinuousMap.const (SingularChains.Simplex n) x) =
        ContinuousMap.const ((unitInterval) × SingularChains.Simplex n) x)
    (hone :
      ∀ smp,
        SecondHurewicz.SimplyConnected.timeSlice (H smp) 1 =
          ContinuousMap.const (SingularChains.Simplex n) x)
    (p : GenLoop (Fin (n + 1)) X x) (u : Fin (n + 1) → (unitInterval)) (i j : Fin (n + 1))
    (hij : i ≠ j) (hu : u i = u j) : CubeGluing.coherentCubeEndpoint H H' hface hconst p u = x := by
  obtain ⟨e, s, rfl⟩ := CubeTriangulation.exists_cubeSimplex u
  exact
    coherentCubeEndpoint_cell_boundary H H' hface hconst hone p e s
      (cubeSimplex_coordinate_equality_boundary e s hij hu)

def Hurewicz.normalizedCycleAssignment {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    (f : SingularChains.SingularSimplex X (n + 1) → SimplexGeometry.BasedSimplex (n + 1) x) :
    SingularChains.Chains X (n + 1) →ₗ[ℤ]
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) (n + 1) :=
  SingularChains.chainLift X (n + 1) fun smp =>
    correctedSimplexCycle n x (f smp).val (SimplexGeometry.basedSimplex_face (f smp))

@[simp]
theorem Hurewicz.normalizedCycleAssignment_simplex {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) (f : SingularChains.SingularSimplex X (n + 1) → SimplexGeometry.BasedSimplex (n + 1) x)
    (smp : SingularChains.SingularSimplex X (n + 1)) :
    normalizedCycleAssignment n x f (SingularChains.simplexChain X (n + 1) smp) =
      correctedSimplexCycle n x (f smp).val (SimplexGeometry.basedSimplex_face (f smp)) :=
  SingularChains.chainLift_simplex X (n + 1) _ smp

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

theorem Hurewicz.normalizedCycleAssignment_val_endpoint {X : Type} [TopologicalSpace X]
    (n : ℕ) (x : X)
    (f : SingularChains.SingularSimplex X (n + 1) → SimplexGeometry.BasedSimplex (n + 1) x)
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (hf : ∀ smp, (f smp).val = SecondHurewicz.SimplyConnected.timeSlice (H' smp) 1)
    (c : SingularChains.Chains X (n + 1)) :
    (normalizedCycleAssignment n x f c).val =
      SecondHurewicz.SimplyConnected.simplexEndpointOperator (n + 1) H' 1 c -
        SecondHurewicz.SimplyConnected.chainAugmentation X (n + 1) c •
          constantSimplexChain (n + 1) x := by
  rw [normalizedCycleAssignment_val, SecondHurewicz.SimplyConnected.chainLift_sub_constant]
  have hmap :
    SingularChains.chainLift X (n + 1)
        (fun smp => SingularChains.simplexChain X (n + 1) (f smp).val) =
      SecondHurewicz.SimplyConnected.simplexEndpointOperator (n + 1) H' 1 := by
    apply SingularChains.chainMap_ext X (n + 1)
    intro smp
    rw [SingularChains.chainLift_simplex,
      SecondHurewicz.SimplyConnected.simplexEndpointOperator_simplex, hf]
  rw [hmap]

theorem Hurewicz.normalizedCycleAssignment_evenCycle {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) (f : SingularChains.SingularSimplex X (n + 1) → SimplexGeometry.BasedSimplex (n + 1) x)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H')
    (hf : ∀ smp, (f smp).val = SecondHurewicz.SimplyConnected.timeSlice (H' smp) 1)
    (heven : Even (n + 1))
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) (n + 1)) :
    normalizedCycleAssignment n x f c.val = straightenedCycle n H H' hface c := by
  apply Subtype.ext
  rw [normalizedCycleAssignment_val_endpoint n x f H' hf,
    chainAugmentation_evenCycle X (n + 1) heven (Nat.zero_lt_succ n), zero_smul, sub_zero,
    straightenedCycle_val]

theorem Hurewicz.normalizedCycleAssignment_oddCycle {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) (f : SingularChains.SingularSimplex X (n + 1) → SimplexGeometry.BasedSimplex (n + 1) x)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H')
    (hf : ∀ smp, (f smp).val = SecondHurewicz.SimplyConnected.timeSlice (H' smp) 1)
    (hodd : Odd (n + 1))
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) (n + 1)) :
    normalizedCycleAssignment n x f c.val =
      straightenedCycle n H H' hface c -
        SecondHurewicz.SimplyConnected.chainAugmentation X (n + 1) c.val •
          constantSimplexCycle (n + 1) x hodd := by
  apply Subtype.ext
  change
    (normalizedCycleAssignment n x f c.val).val =
      (straightenedCycle n H H' hface c).val -
        SecondHurewicz.SimplyConnected.chainAugmentation X (n + 1) c.val •
          (constantSimplexCycle (n + 1) x hodd).val
  rw [normalizedCycleAssignment_val_endpoint n x f H' hf, straightenedCycle_val,
    constantSimplexCycle_val]

theorem Hurewicz.normalizedCycleAssignment_class {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) (f : SingularChains.SingularSimplex X (n + 1) → SimplexGeometry.BasedSimplex (n + 1) x)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H')
    (h₀ : ∀ smp, SecondHurewicz.SimplyConnected.timeSlice (H' smp) 0 = smp)
    (hf : ∀ smp, (f smp).val = SecondHurewicz.SimplyConnected.timeSlice (H' smp) 1)
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

end Mathoverflow1973
