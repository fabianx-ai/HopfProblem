/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.RegularLevel
public import Lib.Geometry.Manifold.WhitneyEmbedding
public import Lib.Geometry.Manifold.Morse.SurgeryWindows
public import Lib.Geometry.Manifold.Morse.Cubic.Model
public import Lib.Geometry.Manifold.Morse.Cubic.DescentField
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Aligning the cubic model with a Morse chart

A bijection `ρ : Option (Fin m) ≃ Fin n` gives the linear equivalence
`MorseCancellation.splitEquiv ρ : ℝ × (Fin m → ℝ) ≃L[ℝ] (Fin n → ℝ)` placing the axis coordinate
at `ρ none`.  Composed with the splitting of a signed Morse chart `c` into negative and positive
coordinates it gives `selectedMorseFieldEquiv c ρ`, which conjugates the linear endpoint field of
the cubic model to the model descent field of the chart (`selectedMorseFieldEquiv_descent`).
Changing it by block isometries (`exists_positive_ray_alignment`, `morse_block_change_descent`,
`transverseFieldChange`, `splitTransverseChange`) one can moreover send the model axis onto a
prescribed ray of the unstable or of the stable plane (`exists_selected_outgoing_axis`,
`exists_selected_incoming_axis`).  The resulting charts in which a given field is the cubic descent
field near a critical point are `exists_cubic_field_endpoint_with_alignment`,
`exists_original_field_endpoint_with_alignment` and `exists_controlled_morse_field_endpoint`.
Cf. Milnor, *Lectures on the h-cobordism theorem*, §5.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-- The linear splitting into the axis and transverse directions. -/
def MorseCancellation.splitLinear {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n) : Model m ≃ₗ[ℝ] (Fin n → ℝ)
    where
  toFun p j := (ρ.symm j).elim p.1 p.2
  invFun f := (f (ρ Option.none), fun i => f (ρ (Option.some i)))
  left_inv
    p := by
    apply Prod.ext
    · simp
    · funext i
      simp
  right_inv
    f := by
    funext j
    have hj := ρ.apply_symm_apply j
    cases h : ρ.symm j with
    | none => simpa only [h, Option.elim_none] using congrArg f hj
    | some i => simpa only [h, Option.elim_some] using congrArg f hj
  map_add' p
    q := by
    funext j
    cases h : ρ.symm j <;> simp [h]
  map_smul' t
    p := by
    funext j
    cases h : ρ.symm j <;> simp [h]

/-- The split equivalence of the model space. -/
def MorseCancellation.splitEquiv {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n) : Model m ≃L[ℝ] (Fin n → ℝ) :=
  (splitLinear ρ).toContinuousLinearEquiv

/-- The split equivalence on the axis component. -/
theorem MorseCancellation.splitEquiv_apply_none {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n) (p : Model m) :
    splitEquiv ρ p (ρ Option.none) = p.1 := by
  change (ρ.symm (ρ Option.none)).elim p.1 p.2 = p.1
  simp

/-- The split equivalence on the transverse component. -/
theorem MorseCancellation.splitEquiv_apply_some {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n) (p : Model m)
    (i : Fin m) : splitEquiv ρ p (ρ (Option.some i)) = p.2 i := by
  change (ρ.symm (ρ (Option.some i))).elim p.1 p.2 = p.2 i
  simp

/-- The signed sum in split coordinates. -/
theorem MorseCancellation.split_signed_sum {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n) (w : Fin n → ℝ)
    (p : Model m) :
    (∑ j, w j * splitEquiv ρ p j ^ 2) =
      w (ρ Option.none) * p.1 ^ 2 + ∑ i, w (ρ (Option.some i)) * p.2 i ^ 2 := by
  rw [← ρ.sum_comp]
  simp only [Fintype.sum_option, splitEquiv_apply_none, splitEquiv_apply_some]

/-- The endpoint field in split coordinates. -/
theorem MorseCancellation.splitEquiv_endpoint_field {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n)
    (w : Fin n → ℝ) (p : Model m) :
    splitEquiv ρ
        (endpointLinearField (fun i => w (ρ (Option.some i))) (1 / 2) (w (ρ Option.none)) p) =
      fun j => -w j * splitEquiv ρ p j := by
  funext j
  obtain ⟨k, rfl⟩ := ρ.surjective j
  cases k with
  | none =>
    rw [splitEquiv_apply_none, splitEquiv_apply_none]
    change (-2 * w (ρ Option.none) * (1 / 2)) * p.1 = -w (ρ Option.none) * p.1
    ring
  | some i =>
    rw [splitEquiv_apply_some, splitEquiv_apply_some]
    rfl

attribute [local instance 100] Classical.propDecidable in
/-- The signed descent in split coordinates. -/
theorem MorseCancellation.splitCoordinates_signed_descent {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, w i = -1 ∨ w i = 1) (z : ι → ℝ) :
    MorseHandle.splitCoordinates w (fun i => -w i * z i) =
      MorseHandle.descent (MorseHandle.splitCoordinates w z) := by
  apply Prod.ext
  · ext i
    change -w i.1 * z i.1 = z i.1
    rw [i.2]
    ring
  · ext i
    change -w i.1 * z i.1 = -z i.1
    rw [(hw i.1).resolve_left i.2]
    ring

attribute [local instance 100] Classical.propDecidable in
/-- The linear equivalence aligning the selected Morse field. -/
def MorseCancellation.selectedMorseFieldEquiv {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ}
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) :
    Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates) :=
  (splitEquiv ρ).trans (MorseHandle.splitCoordinates c.weights)

attribute [local instance 100] Classical.propDecidable in
/-- The selected Morse field equivalence preserves descent. -/
theorem MorseCancellation.selectedMorseFieldEquiv_descent {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ}
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (p : Model m) :
    selectedMorseFieldEquiv c ρ
        (endpointLinearField (fun i => c.weights (ρ (Option.some i))) (1 / 2)
          (c.weights (ρ Option.none)) p) =
      MorseHandle.descent (selectedMorseFieldEquiv c ρ p) := by
  change
    MorseHandle.splitCoordinates c.weights (splitEquiv ρ _) =
      MorseHandle.descent (MorseHandle.splitCoordinates c.weights (splitEquiv ρ p))
  rw [splitEquiv_endpoint_field]
  exact splitCoordinates_signed_descent c.weights c.signs (splitEquiv ρ p)

/-- The transverse change of field. -/
def MorseCancellation.transverseFieldChange {m : ℕ} (T : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ)) :
    Model m ≃L[ℝ] Model m :=
  (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr T

/-- The transverse change preserves cubic descent. -/
theorem MorseCancellation.transverseFieldChange_cubicDescent {m : ℕ} (σ : Fin m → ℝ)
    (T : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ))
    (hcomm : ∀ z, T (fun i => σ i * z i) = fun i => σ i * T z i) (t : ℝ) (p : Model m) :
    transverseFieldChange T (cubicDescent σ t p) = cubicDescent σ t (transverseFieldChange T p) :=
  by
  apply Prod.ext
  · rfl
  · change T (fun i => -σ i * p.2 i) = fun i => -σ i * T p.2 i
    have hleft : (fun i => -σ i * p.2 i) = -(fun i => σ i * p.2 i) := by
      funext i
      simp only [Pi.neg_apply, neg_mul]
    rw [hleft, map_neg, hcomm]
    funext i
    simp only [Pi.neg_apply, neg_mul]

/-- The transverse change in split coordinates. -/
def MorseCancellation.splitTransverseChange {m : ℕ} {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] (e : (Fin m → ℝ) ≃L[ℝ] (A × B))
    (P : A ≃L[ℝ] A) (S : B ≃L[ℝ] B) : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ) :=
  (e.trans (P.prodCongr S)).trans e.symm

/-- The split transverse change commutes with the splitting. -/
theorem MorseCancellation.splitTransverseChange_commutes {m : ℕ} {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] (σ : Fin m → ℝ)
    (e : (Fin m → ℝ) ≃L[ℝ] (A × B)) (α β : ℝ)
    (he : ∀ z, e (fun i => σ i * z i) = (α • (e z).1, β • (e z).2)) (P : A ≃L[ℝ] A)
    (S : B ≃L[ℝ] B) (z : Fin m → ℝ) :
    splitTransverseChange e P S (fun i => σ i * z i) = fun i =>
      σ i * splitTransverseChange e P S z i := by
  apply e.injective
  simp only [splitTransverseChange, ContinuousLinearEquiv.trans_apply, e.apply_symm_apply, he,
    ContinuousLinearEquiv.prodCongr_apply, map_smul]

/-- The Morse block change preserves descent. -/
theorem MorseCancellation.morse_block_change_descent {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] (A : N ≃L[ℝ] N) (B : P ≃L[ℝ] P)
    (z : N × P) :
    (A.prodCongr B) (MorseHandle.descent z) =
      MorseHandle.descent ((A.prodCongr B) z) := by
  apply Prod.ext
  · rfl
  · change B (-z.2) = -B z.2
    exact B.map_neg _

/-- A positive ray alignment of the field exists. -/
theorem MorseCancellation.exists_positive_ray_alignment {D : Type*} [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] {u v : D} (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ (r : ℝ) (A : D ≃ₗᵢ[ℝ] D), 0 < r ∧ A (r • u) = v ∧ ∀ s : ℝ, A ((s * r) • u) = s • v := by
  let r := ‖v‖ / ‖u‖
  have hr : 0 < r := div_pos (norm_pos_iff.mpr hv) (norm_pos_iff.mpr hu)
  have hnorm : ‖r • u‖ = ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact div_mul_cancel₀ ‖v‖ (norm_ne_zero_iff.mpr hu)
  let A : D ≃ₗᵢ[ℝ] D := (ℝ ∙ (r • u - v))ᗮ.reflection
  have hA : A (r • u) = v := Submodule.reflection_sub hnorm
  refine ⟨r, A, hr, hA, ?_⟩
  intro s
  rw [← smul_smul, A.map_smul, hA]

attribute [local instance 100] Classical.propDecidable in
/-- The selected field's axis component is nonzero. -/
theorem MorseCancellation.selectedMorseFieldEquiv_axis_ne_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ}
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) :
    selectedMorseFieldEquiv c ρ (1, (0 : Fin m → ℝ)) ≠ 0 := by
  intro h
  have hh :=
    (selectedMorseFieldEquiv c ρ).injective
      (h.trans (map_zero (selectedMorseFieldEquiv c ρ)).symm)
  have h1 := congrArg Prod.fst hh
  norm_num at h1

attribute [local instance 100] Classical.propDecidable in
/-- The selected field's negative axis. -/
theorem MorseCancellation.selectedMorseFieldEquiv_negative_axis {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ}
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (he : c.weights (ρ Option.none) = -1) :
    (selectedMorseFieldEquiv c ρ (1, (0 : Fin m → ℝ))).2 = 0 ∧
      (selectedMorseFieldEquiv c ρ (1, (0 : Fin m → ℝ))).1 ≠ 0 := by
  let z := selectedMorseFieldEquiv c ρ (1, (0 : Fin m → ℝ))
  have hw :
    endpointLinearField (fun i => c.weights (ρ (Option.some i))) (1 / 2)
        (c.weights (ρ Option.none)) (1, (0 : Fin m → ℝ)) =
      (1, 0) := by ext i <;> simp [endpointLinearField, he]
  have hh := selectedMorseFieldEquiv_descent c ρ (1, (0 : Fin m → ℝ))
  rw [hw] at hh
  have h2 : z.2 = -z.2 := congrArg Prod.snd hh
  have hs : (2 : ℝ) • z.2 = 0 := by
    rw [two_smul]
    exact (congrArg (fun v => v + z.2) h2).trans (neg_add_cancel z.2)
  have hz : z.2 = 0 := (smul_eq_zero.mp hs).resolve_left (by norm_num)
  refine ⟨hz, ?_⟩
  intro h1
  exact selectedMorseFieldEquiv_axis_ne_zero c ρ (Prod.ext h1 hz)

attribute [local instance 100] Classical.propDecidable in
/-- The selected field's positive axis. -/
theorem MorseCancellation.selectedMorseFieldEquiv_positive_axis {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ}
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (he : c.weights (ρ Option.none) = 1) :
    (selectedMorseFieldEquiv c ρ (1, (0 : Fin m → ℝ))).1 = 0 ∧
      (selectedMorseFieldEquiv c ρ (1, (0 : Fin m → ℝ))).2 ≠ 0 := by
  let z := selectedMorseFieldEquiv c ρ (1, (0 : Fin m → ℝ))
  have hw :
    endpointLinearField (fun i => c.weights (ρ (Option.some i))) (1 / 2)
        (c.weights (ρ Option.none)) (1, (0 : Fin m → ℝ)) =
      -(1, 0) := by ext i <;> simp [endpointLinearField, he]
  have hh := selectedMorseFieldEquiv_descent c ρ (1, (0 : Fin m → ℝ))
  rw [hw, map_neg] at hh
  have h1 : z.1 = -z.1 := (congrArg Prod.fst hh).symm
  have hs : (2 : ℝ) • z.1 = 0 := by
    rw [two_smul]
    exact (congrArg (fun v => v + z.1) h1).trans (neg_add_cancel z.1)
  have hz : z.1 = 0 := (smul_eq_zero.mp hs).resolve_left (by norm_num)
  refine ⟨hz, ?_⟩
  intro h2
  exact selectedMorseFieldEquiv_axis_ne_zero c ρ (Prod.ext hz h2)

attribute [local instance 100] Classical.propDecidable in
/-- A selected outgoing axis exists. -/
theorem MorseCancellation.exists_selected_outgoing_axis {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ}
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (he : c.weights (ρ Option.none) = -1)
    {v : c.NegativeCoordinates} (hv : v ≠ 0) :
    ∃ (r : ℝ) (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates)),
      0 < r ∧
        L (r, 0) = (v, 0) ∧
          ∀ p,
            L
                (endpointLinearField (fun i => c.weights (ρ (Option.some i))) (1 / 2)
                  (c.weights (ρ Option.none)) p) =
              MorseHandle.descent (L p) := by
  let L₀ := selectedMorseFieldEquiv c ρ
  obtain ⟨hz, hn⟩ := selectedMorseFieldEquiv_negative_axis c ρ he
  obtain ⟨r, A, hr, hA, _⟩ := exists_positive_ray_alignment hn hv
  let B :=
    A.toContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ c.PositiveCoordinates)
  let L := L₀.trans B
  refine ⟨r, L, hr, ?_, ?_⟩
  · have hp : (r, (0 : Fin m → ℝ)) = r • (1, 0) := by simp
    rw [hp, L.map_smul]
    apply Prod.ext
    · change r • A ((L₀ (1, 0)).1) = v
      rw [← A.map_smul]
      exact hA
    · change r • (L₀ (1, 0)).2 = 0
      rw [hz, smul_zero]
  · intro p
    change B (L₀ _) = MorseHandle.descent (B (L₀ p))
    rw [selectedMorseFieldEquiv_descent]
    exact morse_block_change_descent _ _ _

attribute [local instance 100] Classical.propDecidable in
/-- A selected incoming axis exists. -/
theorem MorseCancellation.exists_selected_incoming_axis {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ}
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (he : c.weights (ρ Option.none) = 1)
    {v : c.PositiveCoordinates} (hv : v ≠ 0) :
    ∃ (r : ℝ) (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates)),
      0 < r ∧
        L (-r, 0) = (0, v) ∧
          ∀ p,
            L
                (endpointLinearField (fun i => c.weights (ρ (Option.some i))) (1 / 2)
                  (c.weights (ρ Option.none)) p) =
              MorseHandle.descent (L p) := by
  let L₀ := selectedMorseFieldEquiv c ρ
  obtain ⟨hz, hn⟩ := selectedMorseFieldEquiv_positive_axis c ρ he
  obtain ⟨r, A, hr, hA, _⟩ := exists_positive_ray_alignment hn (neg_ne_zero.mpr hv)
  let B :=
    (ContinuousLinearEquiv.refl ℝ c.NegativeCoordinates).prodCongr A.toContinuousLinearEquiv
  let L := L₀.trans B
  refine ⟨r, L, hr, ?_, ?_⟩
  · have hp : (-r, (0 : Fin m → ℝ)) = (-r) • (1, 0) := by simp
    rw [hp, L.map_smul]
    apply Prod.ext
    · change (-r) • (L₀ (1, 0)).1 = 0
      rw [hz, smul_zero]
    · change (-r) • A ((L₀ (1, 0)).2) = v
      rw [neg_smul, ← A.map_smul, hA, neg_neg]
  · intro p
    change B (L₀ _) = MorseHandle.descent (B (L₀ p))
    rw [selectedMorseFieldEquiv_descent]
    exact morse_block_change_descent _ _ _

attribute [local instance 100] Classical.propDecidable in
/-- A cubic field endpoint with ray alignment exists. -/
theorem MorseCancellation.exists_cubic_field_endpoint_with_alignment {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ} (σ : Fin m → ℝ)
    {e : ℝ} (he : e ^ 2 = 1) (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates))
    (hL : ∀ p, L (endpointLinearField σ (1 / 2) e p) = MorseHandle.descent (L p)) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (e / 2, (0 : Fin m → ℝ)) ∈ Φ.source ∧
        Φ (e / 2, 0) = x ∧
          Φ.target ⊆ c.splitChart.source ∧
            (∀ y ∈ Φ.target, c.descentField y = nativeCubicDescent σ Φ (-(1 / 2 : ℝ) ^ 2) y) ∧
              (Φ : Model m → M) = c.splitChart.symm ∘ L ∘ endpointFieldProduct (1 / 2) e := by
  let P := L.toDiffeomorph.toPartialDiffeomorph
  let Q := P.trans c.splitChart.symm
  have h0 : (0 : Model m) ∈ Q.source := by
    change (0 : Model m) ∈ Set.univ ∧ L 0 ∈ c.splitChart.target
    rw [map_zero, ← c.splitChart_center]
    exact ⟨Set.mem_univ _, c.splitChart.map_source' c.splitChart_mem_source⟩
  have hQzero : Q 0 = x := by
    change c.splitChart.symm (L 0) = x
    rw [map_zero, ← c.splitChart_center]
    exact c.splitChart.left_inv' c.splitChart_mem_source
  have hmodel :
    ∀ y ∈ Q.target,
      c.descentField y =
        FlowConstruction.partialChartField Q.symm (endpointLinearField σ (1 / 2) e) y := by
    intro y hy
    have hpush (p : Model m) (_ : p ∈ P.source) :
      fderiv ℝ P p (endpointLinearField σ (1 / 2) e p) = MorseHandle.descent (P p) := by
      change fderiv ℝ L p (endpointLinearField σ (1 / 2) e p) = MorseHandle.descent (L p)
      rw [L.fderiv]
      exact hL p
    exact
      (partialChartField_of_model_conjugacy P c.splitChart.symm (endpointLinearField σ (1 / 2) e)
          MorseHandle.descent hpush hy).symm
  obtain ⟨Φ, hp, hc, hsub, hf, hmap⟩ :=
    exists_native_cubic_field_endpoint σ (by norm_num : 0 < (1 / 2 : ℝ)) he Q h0 c.descentField
      hmodel
  refine ⟨Φ, ?_, ?_, fun y hy => (hsub hy).1, hf, hmap⟩
  · simpa only [mul_one_div] using hp
  · simpa only [mul_one_div, hQzero] using hc

attribute [local instance 100] Classical.propDecidable in
/-- An original field endpoint with ray alignment exists. -/
theorem MorseCancellation.exists_original_field_endpoint_with_alignment {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ} (σ : Fin m → ℝ)
    {e : ℝ} (he : e ^ 2 = 1) (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates))
    (hL : ∀ p, L (endpointLinearField σ (1 / 2) e p) = MorseHandle.descent (L p))
    (V : (y : M) → TangentSpace 𝓘(ℝ, E) y) (heq : ∀ᶠ y in 𝓝 x, V y = c.descentField y) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (e / 2, (0 : Fin m → ℝ)) ∈ Φ.source ∧
        Φ (e / 2, 0) = x ∧
          Φ.target ⊆ c.splitChart.source ∧
            (∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(1 / 2 : ℝ) ^ 2) y) ∧
              (Φ : Model m → M) = c.splitChart.symm ∘ L ∘ endpointFieldProduct (1 / 2) e := by
  obtain ⟨Φ, hp, hc, hsub, hf, hmap⟩ := exists_cubic_field_endpoint_with_alignment c σ he L hL
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp heq
  let Ψ := PartialChart.restrictTarget Φ hU
  have hpΨ : (e / 2, (0 : Fin m → ℝ)) ∈ Ψ.source := by
    change (e / 2, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (e / 2, 0) ∈ U
    exact ⟨hp, hc.symm ▸ hxU⟩
  refine ⟨Ψ, hpΨ, hc, fun y hy => hsub hy.1, ?_, hmap⟩
  intro y hy
  exact (hUsub hy.2).trans (hf y hy.1)

/-- The endpoint field coordinate on the open axis. -/
theorem MorseCancellation.endpointFieldCoordinate_mem_open_axis {a : ℝ} {e : ℝ} (he : e ^ 2 = 1) {s : ℝ}
    (hs : s ∈ endpointFieldDomain a e) (hdir : 0 < -e * endpointFieldCoordinate a e s) :
    s ∈ Set.Ioo (-a) a := by
  rcases sq_eq_one_iff.mp he with h | h
  · subst e
    have hd : 0 < a + s := by simpa [endpointFieldDomain] using hs
    have hy : (s - a) / (a + s) < 0 := by simpa [endpointFieldCoordinate] using hdir
    have hn : s - a < 0 := by simpa using (div_lt_iff₀ hd).mp hy
    exact ⟨by linarith, by linarith⟩
  · subst e
    have hd : 0 < a - s := by simpa [endpointFieldDomain] using hs
    have hy : 0 < (s + a) / (a - s) := by
      simpa [endpointFieldCoordinate, sub_eq_add_neg] using hdir
    have hn : 0 < s + a := by simpa using (lt_div_iff₀ hd).mp hy
    exact ⟨by linarith, by linarith⟩

attribute [local instance 100] Classical.propDecidable in
/-- A controlled Morse field endpoint exists. -/
theorem MorseCancellation.exists_controlled_morse_field_endpoint {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ} (σ : Fin m → ℝ) {e : ℝ}
    (he : e ^ 2 = 1) (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates))
    (hL : ∀ p, L (endpointLinearField σ (1 / 2) e p) = MorseHandle.descent (L p))
    (V : (y : M) → TangentSpace 𝓘(ℝ, E) y) (heq : ∀ᶠ y in 𝓝 x, V y = c.descentField y) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (e / 2, (0 : Fin m → ℝ)) ∈ Φ.source ∧
        Φ (e / 2, 0) = x ∧
          Φ.target ⊆ c.splitChart.source ∧
            (∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(1 / 2 : ℝ) ^ 2) y) ∧
              ∀ p ∈ Φ.source,
                p.1 ∈ endpointFieldDomain (1 / 2) e ∧
                  c.splitChart (Φ p) = L (endpointFieldProduct (1 / 2) e p) := by
  obtain ⟨Φ, hp, hc, hsub, hf, hmap⟩ :=
    exists_original_field_endpoint_with_alignment c σ he L hL V heq
  let q : Model m := (e / 2, 0)
  have hq : q.1 ∈ endpointFieldDomain (1 / 2) e := by
    simpa only [q, mul_one_div] using endpointField_mem_domain (by norm_num : 0 < (1 / 2 : ℝ)) he
  have hd : ContinuousAt (endpointFieldCoordinate (1 / 2) e) q.1 :=
    ((contDiffOn_endpointFieldCoordinate (1 / 2) e).contDiffAt
        ((endpointFieldDomain_open (1 / 2) e).mem_nhds hq)).continuousAt
  have hprod : ContinuousAt (endpointFieldProduct (m := m) (1 / 2) e) q :=
    (hd.comp continuousAt_fst).prodMk continuousAt_snd
  have hzero : L (endpointFieldProduct (1 / 2) e q) = 0 := by
    have hq' : q = (e * (1 / 2), (0 : Fin m → ℝ)) := by
      apply Prod.ext
      · dsimp [q]
        ring
      · rfl
    rw [hq']
    simp [endpointFieldProduct, endpointFieldCoordinate_center]
  have hct : ContinuousAt (fun p : Model m => L (endpointFieldProduct (1 / 2) e p)) q :=
    L.continuous.continuousAt.comp hprod
  have htarget0 : (0 : c.NegativeCoordinates × c.PositiveCoordinates) ∈ c.splitChart.target := by
    rw [← c.splitChart_center]
    exact c.splitChart.map_source' c.splitChart_mem_source
  have htarget : ∀ᶠ p in 𝓝 q, L (endpointFieldProduct (1 / 2) e p) ∈ c.splitChart.target := by
    have hn : ∀ᶠ z in 𝓝 (L (endpointFieldProduct (1 / 2) e q)), z ∈ c.splitChart.target :=
      c.splitChart.open_target.mem_nhds (hzero.symm ▸ htarget0)
    exact hct.eventually hn
  have hdomain : ∀ᶠ p in 𝓝 q, p.1 ∈ endpointFieldDomain (1 / 2) e :=
    continuousAt_fst.eventually ((endpointFieldDomain_open (1 / 2) e).mem_nhds hq)
  obtain ⟨U, hUsub, hU, hqU⟩ := mem_nhds_iff.mp (hdomain.and htarget)
  let Ψ := PartialChart.restrictSource Φ hU
  have hpΨ : q ∈ Ψ.source := ⟨hp, hqU⟩
  refine ⟨Ψ, hpΨ, hc, fun y hy => hsub hy.1, ?_, ?_⟩
  · intro y hy
    exact hf y hy.1
  · intro p hp
    obtain ⟨hpd, hpt⟩ := hUsub hp.2
    refine ⟨hpd, ?_⟩
    change c.splitChart (Φ p) = L (endpointFieldProduct (1 / 2) e p)
    rw [hmap]
    exact c.splitChart.right_inv' hpt
