/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.Existence
public import Lib.Geometry.Manifold.RegularLevel
public import Lib.Geometry.Manifold.WhitneyEmbedding
public import Lib.Geometry.Manifold.Collar
public import Lib.Geometry.Manifold.Morse.SurgeryWindows
public import Lib.Geometry.Manifold.Morse.CubicFlow
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Lib.Geometry.Manifold.Transversality.Diffeomorph
public import Lib.Geometry.Manifold.Transversality.SupportedIsotopy
public import Lib.Geometry.Manifold.Transversality.GermRealization
public import Lib.Geometry.Manifold.Transversality.DiskShrinking
/-!
# The disc theorem

Two smooth embeddings of the closed unit disc into a compact manifold of dimension at least two,
of the same positive codimension and with the same centre, are carried onto one another by a
diffeomorphism isotopic to the identity. The proof aligns the two charts along the disc factor
(`SupportedGerms.exists_native_disk_germ_alignment`) and shrinks the disc into the region where they
agree (`DiskShrinking.exists_chart_disk_shrinking`).

## Main results

* `DiskShrinking.exists_embedded_disk_isotopy_of_same_center`

## References

* [M. Hirsch, *Differential Topology*][hirsch76], Thm 8.3.1; R. Palais, *Extending
  diffeomorphisms*, Proc. AMS 11 (1960).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff Matrix NNReal

@[expose] public noncomputable section


/-- An open set containing the closed unit ball contains a closed ball of radius strictly bigger
than one.
-/
theorem DiskShrinking.exists_larger_closedBall_subset {D : Type*} [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] {U : Set D} (hU : IsOpen U)
    (hunit : Metric.closedBall (0 : D) 1 ⊆ U) :
    ∃ R : ℝ, 1 < R ∧ Metric.closedBall (0 : D) R ⊆ U := by
  let T : Set ℝ := {r | ∀ x ∈ Metric.closedBall (0 : D) 1, r • x ∈ U}
  have hT : IsOpen T :=
    MorsePerturbation.isOpen_forall_mem_compact (ProperSpace.isCompact_closedBall (0 : D) 1)
      (hU.preimage (continuous_fst.smul continuous_snd))
  have h1 : (1 : ℝ) ∈ T := by
    intro x hx
    simpa only [one_smul] using hunit hx
  obtain ⟨δ, hδ, hδT⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds h1)
  let R : ℝ := 1 + δ / 2
  have hR : 1 < R := by dsimp [R]; linarith
  have hRpos : 0 < R := zero_lt_one.trans hR
  have hRT : R ∈ T :=
    hδT
      (by
        rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by dsimp [R]; linarith)]
        dsimp [R]
        linarith)
  refine ⟨R, hR, ?_⟩
  intro x hx
  have hnorm : ‖R⁻¹ • x‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRpos)]
    exact
      (inv_mul_le_iff₀ hRpos).mpr (by simpa only [mul_one] using mem_closedBall_zero_iff.mp hx)
  have hh := hRT (R⁻¹ • x) (mem_closedBall_zero_iff.mpr hnorm)
  simpa only [smul_inv_smul₀ hRpos.ne'] using hh

/-- An open set of `D × Z` containing the unit disc of the first factor contains the image of a ball
of radius `R > 1` under a linear isomorphism restricting to the inclusion of that disc.
-/
theorem DiskShrinking.exists_disk_ellipsoid_in_open {D Z : Type*} [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    [FiniteDimensional ℝ Z] {U : Set (D × Z)} (hU : IsOpen U)
    (hzero : Metric.closedBall (0 : D) 1 ×ˢ {(0 : Z)} ⊆ U) :
    ∃ R : ℝ,
      1 < R ∧
        ∃ L : WithLp 2 (D × Z) ≃L[ℝ] D × Z,
          (∀ x : D, L (WithLp.toLp 2 (x, (0 : Z))) = (x, 0)) ∧
            Set.MapsTo L (Metric.closedBall 0 R) U := by
  obtain ⟨A, B, hA, hB, hKA, h0B, hAB⟩ :=
    generalized_tube_lemma (ProperSpace.isCompact_closedBall (0 : D) 1)
      (isCompact_singleton (x := (0 : Z))) hU hzero
  obtain ⟨R, hR, hRA⟩ := exists_larger_closedBall_subset hA hKA
  obtain ⟨ε, hε, hεB⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.mp (hB.mem_nhds (h0B (Set.mem_singleton (0 : Z))))
  have hRpos : 0 < R := zero_lt_one.trans hR
  let δ : ℝ := ε / R
  have hδ : 0 < δ := div_pos hε hRpos
  let T : Z ≃L[ℝ] Z := (LinearEquiv.smulOfNeZero ℝ Z δ hδ.ne').toContinuousLinearEquiv
  let L : WithLp 2 (D × Z) ≃L[ℝ] D × Z :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ D Z).trans
      ((ContinuousLinearEquiv.refl ℝ D).prodCongr T)
  have hL (p : WithLp 2 (D × Z)) : L p = (p.fst, δ • p.snd) := rfl
  refine ⟨R, hR, L, ?_, ?_⟩
  · intro x
    rw [hL]
    change (x, δ • (0 : Z)) = (x, 0)
    rw [smul_zero]
  · intro p hp
    rw [hL]
    apply hAB
    refine
      ⟨hRA
          (mem_closedBall_zero_iff.mpr
            ((WithLp.norm_fst_le D p).trans (mem_closedBall_zero_iff.mp hp))),
        hεB ?_⟩
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
    calc
      δ * ‖p.snd‖ ≤ δ * R :=
        mul_le_mul_of_nonneg_left ((WithLp.norm_snd_le D p).trans (mem_closedBall_zero_iff.mp hp))
          hδ.le
      _ = ε := div_mul_cancel₀ ε hRpos.ne'


/-- In a chart whose source contains the unit disc of the first factor there is a diffeomorphism of
the manifold, isotopic to the identity through diffeomorphisms supported in some compact subset
`K ⊆ Φ.target` of the chart and fixing its centre `Φ (0, 0)`, which contracts that disc by the
factor `a`.
-/
theorem DiskShrinking.exists_chart_disk_shrinking {D Z E H M : Type*}
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z]
    [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] (Φ : PartialDiffeomorph 𝓘(ℝ, D × Z) I (D × Z) M ∞)
    (hzero : Metric.closedBall (0 : D) 1 ×ˢ {(0 : Z)} ⊆ Φ.source) {a : ℝ} (ha : 0 < a)
    (ha₁ : a ≤ 1) :
    ∃ K : Set M,
      IsCompact K ∧
        K ⊆ Φ.target ∧
          ∃ P : Diffeomorph I I M M ∞,
            Nonempty (SupportedDiffeomorph.SupportedRelativeIsotopy P K {Φ (0, 0)}) ∧
              ∀ x : D, ‖x‖ ≤ 1 → P (Φ (x, 0)) = Φ (a • x, 0) := by
  obtain ⟨R, hR, L, hLzero, hLsource⟩ := exists_disk_ellipsoid_in_open Φ.open_source hzero
  let Ψ := L.toDiffeomorph.toPartialDiffeomorph'.trans Φ
  have hsource : Metric.closedBall (0 : WithLp 2 (D × Z)) R ⊆ Ψ.source := by
    intro z hz
    exact ⟨Set.mem_univ z, hLsource hz⟩
  have htarget : Ψ.target ⊆ Φ.target := fun _ hy => hy.1
  have hΨ (x : D) : Ψ (WithLp.toLp 2 (x, (0 : Z))) = Φ (x, 0) := by
    change Φ (L (WithLp.toLp 2 (x, (0 : Z)))) = _
    rw [hLzero]
  have hΨ0 : Ψ (0 : WithLp 2 (D × Z)) = Φ (0, 0) := hΨ 0
  have h0source : (0 : WithLp 2 (D × Z)) ∈ Ψ.source :=
    hsource (Metric.mem_closedBall_self (zero_le_one.trans hR.le))
  have hfix : ∀ t (z : WithLp 2 (D × Z)), z ∉ Metric.closedBall 0 R → family R a (t, z) = z := by
    intro t z hz
    exact family_outer hR a t (le_of_not_ge (fun hn => hz (mem_closedBall_zero_iff.mpr hn)))
  obtain ⟨B, K, hK, hKt, hB, hB0, hBt, hBfix, -, hchart⟩ :=
    SupportedDiffeomorph.exists_supported_isotopy_extension Ψ (contMDiff_family R a)
      (family_zero R a) (family_slices hR ha ha₁) (ProperSpace.isCompact_closedBall 0 R) hsource
      hfix
  obtain ⟨P, hP⟩ := hBt 1
  refine
    ⟨K, hK, hKt.trans htarget, P,
      ⟨{  family := B
          smooth := hB
          zero := hB0
          one := fun y => (hP y).symm
          slices := hBt
          fixedOutside := hBfix
          fixedOn := ?_ }⟩, ?_⟩
  · intro t y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    rw [← hΨ0, hchart t 0 h0source, family_origin]
  · intro x hx
    have hn : ‖WithLp.toLp 2 (x, (0 : Z))‖ ≤ 1 := by simpa only [WithLp.norm_toLp_fst] using hx
    have hs : WithLp.toLp 2 (x, (0 : Z)) ∈ Ψ.source :=
      hsource (mem_closedBall_zero_iff.mpr (hn.trans hR.le))
    have hsmul : a • WithLp.toLp 2 (x, (0 : Z)) = WithLp.toLp 2 (a • x, (0 : Z)) := by
      change WithLp.toLp 2 (a • x, a • (0 : Z)) = _
      rw [smul_zero]
    rw [← hΨ x, hP, hchart 1 _ hs, family_one_inner hR a hn, hsmul, hΨ]


/-- Two charts with the same centre carry the unit disc of the first factor to discs that agree
after a diffeomorphism isotopic to the identity.
-/
theorem SupportedGerms.exists_disk_chart_isotopy {A B E H M ι κ : Type*}
    [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [InnerProductSpace ℝ B] [FiniteDimensional ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [Finite ι] [Finite κ] [Nontrivial κ] (b : Module.Basis ι ℝ B) (i : ι)
    (basis : Module.Basis κ ℝ (A × B)) (Φ Ψ : PartialDiffeomorph 𝓘(ℝ, A × B) J (A × B) M ∞)
    (hΦ : Metric.closedBall (0 : A) 1 ×ˢ {(0 : B)} ⊆ Φ.source)
    (hΨ : Metric.closedBall (0 : A) 1 ×ˢ {(0 : B)} ⊆ Ψ.source) (hcenter : Φ 0 = Ψ 0) :
    ∃ D : Diffeomorph J J M M ∞,
      SupportedDiffeomorph.IsotopicToIdentity D ∧
        ∀ x ∈ Metric.closedBall (0 : A) 1, D (Φ (x, 0)) = Ψ (x, 0) := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  have hz : (0 : A × B) ∈ Metric.closedBall (0 : A) 1 ×ˢ {(0 : B)} :=
    ⟨Metric.mem_closedBall_self zero_le_one, rfl⟩
  obtain ⟨D, K, -, -, ⟨HD⟩, hgerm⟩ :=
    exists_native_disk_germ_alignment b i basis Φ Ψ (hΦ hz) (hΨ hz) hcenter
  obtain ⟨ε, hε, hεeq⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hgerm
  let a : ℝ := Min.min 1 ε
  have ha : 0 < a := lt_min zero_lt_one hε
  have ha1 : a ≤ 1 := min_le_left _ _
  obtain ⟨KΦ, -, -, P, ⟨HP⟩, hP⟩ := DiskShrinking.exists_chart_disk_shrinking Φ hΦ ha ha1
  obtain ⟨KΨ, -, -, Q, ⟨HQ⟩, hQ⟩ := DiskShrinking.exists_chart_disk_shrinking Ψ hΨ ha ha1
  refine
    ⟨(P.trans D).trans Q.symm,
      (HP.isotopicToIdentity.trans HD.isotopicToIdentity).trans HQ.isotopicToIdentity.symm, ?_⟩
  intro x hx
  have hn : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
  have hsmall : a • x ∈ Metric.closedBall (0 : A) ε := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    exact (mul_le_of_le_one_right ha.le hn).trans (min_le_right _ _)
  have heq : D (Φ (a • x, 0)) = Ψ (a • x, 0) := hεeq hsmall
  change Q.symm (D (P (Φ (x, 0)))) = Ψ (x, 0)
  rw [hP x hn, heq, ← hQ x hn, Q.symm_apply_apply]

/-- The disc theorem: two smooth embeddings of the closed unit disc into a compact manifold of
dimension at least two, of the same positive codimension and with the same centre, are carried
onto one another by a diffeomorphism isotopic to the identity (Hirsch, Differential Topology,
Thm 8.3.1; Palais).
-/
theorem DiskShrinking.exists_embedded_disk_isotopy_of_same_center {D E M : Type*}
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f g : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) (hg : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ g)
    (hfi : Set.InjOn f (Metric.closedBall (0 : D) 1))
    (hgi : Set.InjOn g (Metric.closedBall (0 : D) 1))
    (hfd : ∀ x ∈ Metric.closedBall (0 : D) 1, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (hgd : ∀ x ∈ Metric.closedBall (0 : D) 1, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) g x))
    (n : ℕ) (hn : 0 < n) (hdim : Module.finrank ℝ D + n = Module.finrank ℝ E)
    (hE : 2 ≤ Module.finrank ℝ E) (hcenter : f 0 = g 0) :
    ∃ P : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      SupportedDiffeomorph.IsotopicToIdentity P ∧
        ∀ x ∈ Metric.closedBall (0 : D) 1, P (f x) = g x := by
  classical
  let B := EuclideanSpace ℝ (Fin n)
  obtain ⟨ε, hε, Φ, hΦprod, hΦzero, -⟩ :=
    exists_tubularNeighborhood_in_open_of_embedded_closedBall hf hfi hfd n hdim isOpen_univ
      (Set.mapsTo_univ _ _)
  obtain ⟨δ, hδ, Ψ, hΨprod, hΨzero, -⟩ :=
    exists_tubularNeighborhood_in_open_of_embedded_closedBall hg hgi hgd n hdim isOpen_univ
      (Set.mapsTo_univ _ _)
  have hΦ : Metric.closedBall (0 : D) 1 ×ˢ {(0 : B)} ⊆ Φ.source := by
    rintro ⟨x, z⟩ ⟨hx, hz⟩
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact hΦprod ⟨hx, Metric.mem_closedBall_self hε.le⟩
  have hΨ : Metric.closedBall (0 : D) 1 ×ˢ {(0 : B)} ⊆ Ψ.source := by
    rintro ⟨x, z⟩ ⟨hx, hz⟩
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact hΨprod ⟨hx, Metric.mem_closedBall_self hδ.le⟩
  have hcenter' : Φ 0 = Ψ 0 := by
    change Φ (0, 0) = Ψ (0, 0)
    rw [hΦzero 0 (Metric.mem_closedBall_self zero_le_one),
      hΨzero 0 (Metric.mem_closedBall_self zero_le_one), hcenter]
  have hB : 0 < Module.finrank ℝ B := by simpa only [B, finrank_euclideanSpace_fin] using hn
  have hDB : 2 ≤ Module.finrank ℝ (D × B) := by
    simpa only [Module.finrank_prod, B, finrank_euclideanSpace_fin, hdim] using hE
  let _ : Nontrivial (Fin (Module.finrank ℝ (D × B))) := Fin.nontrivial_iff_two_le.mpr hDB
  obtain ⟨P, hP, hformula⟩ :=
    SupportedGerms.exists_disk_chart_isotopy (Module.finBasis ℝ B) ⟨0, hB⟩
      (Module.finBasis ℝ (D × B)) Φ Ψ hΦ hΨ hcenter'
  refine ⟨P, hP, ?_⟩
  intro x hx
  rw [← hΦzero x hx, hformula x hx, hΨzero x hx]
