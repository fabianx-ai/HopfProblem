/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Topology.Homotopy.LoopSubdivision

/-!
# Spheres of dimension at least two are simply connected

  Spheres of dimension at least two are simply connected: the instances and
  path-connectedness lemmas reducing `pi_1(S^n)` to the stereographic charts
  (Hatcher, Algebraic Topology, Proposition 1.14).
-/



open Set Function Filter Manifold Topology

open scoped EuclideanSpace

universe u v

@[expose] public noncomputable section

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f


/-! ### Point-set properties of Euclidean spheres -/

/-- The `n`-dimensional unit sphere in `ℝⁿ⁺¹` is nonempty. -/
instance EuclideanSphere.instLocal1 {n : ℕ} :
    Nonempty ((fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n) :=
  Set.Nonempty.to_subtype (NormedSpace.sphere_nonempty.mpr (by norm_num))

/-- The `n + 1`-dimensional unit sphere is infinite. -/
instance EuclideanSphere.instLocal2 {n : ℕ} :
    Infinite ((fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (n + 1)) := by
  rw [← Set.infinite_univ_iff]
  have v : (fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (n + 1) :=
    Nonempty.some inferInstance
  apply Set.Infinite.of_image (stereographic' (n + 1) v)
  rw [Set.image_univ]
  apply
    Set.Infinite.mono (PartialEquiv.target_subset_range (stereographic' (n + 1) v).toPartialEquiv)
  rw [stereographic'_target]
  exact Set.infinite_univ

/-- The `n + 1`-dimensional unit sphere is path connected. -/
instance EuclideanSphere.instLocal3 (n : ℕ) :
    PathConnectedSpace
      ((fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (n + 1)) := by
  rw [← isPathConnected_iff_pathConnectedSpace]
  apply isPathConnected_sphere
  · rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact Nat.one_lt_ofNat
  · exact zero_le_one' ℝ

/-- A Euclidean sphere minus one point is contractible via stereographic projection. -/
instance EuclideanSphere.instContractibleSpace1 {n : ℕ}
    (v : (fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n) :
    ContractibleSpace
      ({ v }ᶜ : Set ((fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n)) := by
  let proj := stereographic' n v
  have : ContractibleSpace proj.target := by
    rw [stereographic'_target]
    exact Homeomorph.contractibleSpace (Homeomorph.Set.univ (EuclideanSpace ℝ (Fin n)))
  convert Homeomorph.contractibleSpace proj.toHomeomorphSourceTarget <;>
    exact (stereographic'_source v).symm

/-- A Euclidean sphere of dimension at least one minus one point is path connected. -/
theorem EuclideanSphere.isPathConnected_compl_singleton {n : ℕ}
    (v : (fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (n + 1)) :
    IsPathConnected ({ v }ᶜ) := by
  rw [isPathConnected_iff_pathConnectedSpace]
  infer_instance

/-- The inverse stereographic chart sends the origin to the antipode `-v`. -/
lemma EuclideanSphere.stereographic'_symm_zero {n : ℕ}
    (v : (fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n) :
    (stereographic' n v).toPartialEquiv.symm 0 = -v := by
  ext
  simp [stereographic', stereographic, stereoInvFun]

/-- A Euclidean sphere of dimension at least two minus a pair of antipodal points is path connected. -/
theorem EuclideanSphere.isPathConnected_compl_singleton_inter_neg {n : ℕ}
    (v : (fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (n + 2)) :
    IsPathConnected ({ v }ᶜ ∩ {-v}ᶜ) := by
  let proj := stereographic' (n + 2) v
  have : proj.toPartialEquiv.symm '' (proj.target \ {0}) = { v }ᶜ ∩ {-v}ᶜ := by
    rw [PartialEquiv.symm_image_target_minus_singleton_eq, stereographic'_source,
      stereographic'_symm_zero, Set.sdiff_eq]
    rw [stereographic'_target]
    exact Set.mem_univ 0
  rw [← this]
  apply IsPathConnected.image'
  · rw [stereographic'_target, ← Set.compl_eq_univ_sdiff]
    exact
      isPathConnected_compl_singleton_of_one_lt_rank
        (by rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]; exact Nat.one_lt_ofNat) 0
  · exact ContinuousOn.mono proj.continuousOn_invFun Set.sdiff_subset

private abbrev EuclideanSphere.c {n : ℕ}
    (v : (fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n) :
    Fin 2 → Set ((fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n) :=
  Fin.cases { v }ᶜ (fun _ ↦ {-v}ᶜ)

private lemma EuclideanSphere.hc₁ {n : ℕ}
    (v : (fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n) :
    ∀ i, IsOpen (c v i) := by apply Fin.cases <;> simp

private lemma EuclideanSphere.hc₂ {n : ℕ}
    (v : (fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n) :
    Set.univ ⊆ ⋃ i, c v i := by
  intro s _
  rcases eq_or_ne s v with rfl | h
  · rw [Set.mem_iUnion]
    use 1
    change
      s ∈ ({-s}ᶜ : Set ((fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n))
    rw [Set.mem_compl_iff, Set.mem_singleton_iff, ← Ne, ← Subtype.coe_ne_coe, coe_neg_sphere]
    intro hv
    apply (ne_zero_of_mem_unit_sphere s)
    ext k
    rw [PiLp.zero_apply, ← CharZero.eq_neg_self_iff, ← PiLp.neg_apply, ← hv]
  · rw [Set.mem_iUnion]
    use 0
    exact h

private lemma EuclideanSphere.hc₃ {n : ℕ}
    (v : (fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (n + 2)) :
    ∀ i j, IsPathConnected (c v i ∩ c v j) := by
  apply Fin.cases
  · apply Fin.cases
    · simp only [Fin.cases_zero, Set.inter_self]
      exact isPathConnected_compl_singleton v
    · intro _
      simp only [Fin.cases_zero, Fin.cases_succ]
      exact isPathConnected_compl_singleton_inter_neg v
  · intro _
    apply Fin.cases
    · simp only [Fin.cases_succ, Fin.cases_zero, Set.inter_comm]
      exact isPathConnected_compl_singleton_inter_neg v
    · intro _
      simp only [Fin.cases_succ, Set.inter_self]
      exact isPathConnected_compl_singleton (-v)

private lemma EuclideanSphere.hx {n : ℕ}
    (x : (fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (n + 1)) :
    ∃ v, ∀ i : Fin 2, x ∈ c v i := by
  have ⟨v, hv⟩ := Infinite.exists_notMem_finset {x, -x}
  use v
  apply Fin.cases
  · simp only [Fin.cases_zero, Set.mem_compl_singleton_iff]
    intro h
    apply hv
    rw [Finset.mem_insert]
    exact Or.inl h.symm
  · simp only [Fin.cases_succ, Set.mem_compl_singleton_iff]
    intro _ h
    apply hv
    rw [Finset.mem_insert, Finset.mem_singleton, h]
    exact Or.inr (neg_neg v).symm

/-! ### Loops on higher spheres -/

/-- A non-surjective loop on a sphere is homotopic to the constant loop. -/
theorem EuclideanSphere.homotopic_refl_of_not_surjective {n : ℕ}
    {v : (fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n} (γ : Path v v)
    (h : ¬(Function.Surjective γ)) : γ.Homotopic (Path.refl v) := by
  unfold Function.Surjective at h
  push Not at h
  obtain ⟨w, hw⟩ := h
  let w_compl : Set ((fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n) :=
    { w }ᶜ
  let v' : w_compl :=
    ⟨v, by
      rw [Set.mem_compl_singleton_iff]
      convert hw 0
      exact γ.source.symm⟩
  let f : (unitInterval) → γ ⁻¹' { w }ᶜ := fun x ↦ ⟨x, hw x⟩
  let γ' : Path v' v' :=
    { toFun := γ.restrictPreimage { w }ᶜ ∘ f
      source' := by
        rw [Function.comp_apply, ContinuousMap.restrictPreimage_apply]; ext
        simp [f, v']
      target' := by
        rw [Function.comp_apply, ContinuousMap.restrictPreimage_apply]; ext
        simp [f, v'] }
  have h : SimplyConnectedSpace w_compl := inferInstance
  let incl :
    C(w_compl, (fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  exact Path.Homotopic.map ((simply_connected_iff_loops_nullhomotopic.mp h).right v' γ') incl

/-- Spheres of dimension at least two are simply connected. -/
protected theorem EuclideanSphere.simplyConnectedSpace (n : ℕ) :
    SimplyConnectedSpace
      ((fun (n : ℕ) => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (n + 2)) := by
  rw [simply_connected_iff_loops_nullhomotopic]
  constructor
  · infer_instance
  · intro x p
    let ⟨v, hv⟩ := hx x
    have ⟨m, D, hDh, hDr⟩ :=
      Path.Homotopic.exists_loops_homotopic_concat_of_open_cover (hc₁ v)
        (hc₂ v) (hc₃ v) hv p
    apply Path.Homotopic.trans hDh.symm
    rw [← Path.concat_refl]
    apply Path.Homotopic.concat_hcomp
    intro k
    have ⟨i, hi⟩ := hDr k
    fin_cases i
    · simp only [Fin.zero_eta, Fin.cases_zero] at hi
      apply homotopic_refl_of_not_surjective
      exact fun h ↦ hi (h v) rfl
    · have : (1 : Fin 2) = Fin.succ 0 := rfl
      simp only [Fin.mk_one, this, Fin.cases_succ] at hi
      apply homotopic_refl_of_not_surjective
      exact fun a ↦ hi (a (-v)) rfl

