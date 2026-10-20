/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Immersion.Relative.AffinePerturbation
import Lib.Geometry.Manifold.Immersion.Relative.Arc
import Lib.Geometry.Manifold.Whitney.FrameField.BlockDeterminant
import Lib.Geometry.Manifold.Whitney.FrameField.Complement

/-!
# Nowhere-zero fields and one-column frames with prescribed germs

* In a space of dimension at least two, two nonzero smooth germs at the endpoints `0` and `1` are
  the germs of one smooth nowhere-zero curve
  (`DiskFraming.exists_nonzero_smooth_curve_with_endpoint_germs`), via the punctured model
  `DiskFraming.puncturedModel B = B \ {0}`, which is path-connected.
* A field smooth on an open set is the germ along a closed subset of a globally smooth field
  (`FrameField.exists_global_field_with_closed_germ`); a smooth field on the plane with values in a
  space of dimension at least three can be perturbed relative to a closed set on which it is
  nowhere zero to a field nowhere zero on a compact set (`FrameField.exists_nonzero_field_rel_closed`,
  `FrameField.exists_nonzero_extension_of_local_field`): general position for a section of a bundle
  of rank exceeding the dimension of the base.
* The one-column versions (`FrameField.exists_one_column_extension_of_local_field`), and in a
  three-dimensional target the completion of such a field to a full frame by an orthogonal
  two-column field (`FrameField.exists_completed_one_column_frame`).

Cf. Hirsch, *Differential Topology*, Ch. 2 (approximation and general position), and Milnor,
*Lectures on the h-cobordism theorem*, §6 (framing the Whitney disc).

## Tags

general position, nowhere-zero section, frame field
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

/-- The punctured model of a normed space: the open set of nonzero vectors. -/
def DiskFraming.puncturedModel (B : Type*) [NormedAddCommGroup B] :
    TopologicalSpace.Opens B :=
  ⟨{0}ᶜ, isClosed_singleton.isOpen_compl⟩

/-- A smooth curve defined near `t₀` and nonzero there is the germ at `t₀` of a globally defined
smooth curve avoiding the origin. -/
theorem DiskFraming.exists_smooth_punctured_curve_with_germ {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] {a : ℝ → B} {U : Set ℝ} {t₀ : ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hU : IsOpen U) (ht₀ : t₀ ∈ U) (ha0 : a t₀ ≠ 0) :
    ∃ f : C(ℝ, puncturedModel B),
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, B) ∞ f ∧ (fun t => (f t : B)) =ᶠ[𝓝 t₀] a := by
  classical
  let A : ℝ → puncturedModel B := fun t => if h : a t = 0 then ⟨a t₀, ha0⟩ else ⟨a t, h⟩
  let V := U ∩ a ⁻¹' ({0}ᶜ : Set B)
  have hV : IsOpen V := ha.continuousOn.isOpen_inter_preimage hU isClosed_singleton.isOpen_compl
  have htV : t₀ ∈ V := ⟨ht₀, ha0⟩
  have hval {t : ℝ} (ht : t ∈ V) : (Subtype.val ∘ A) =ᶠ[𝓝 t] a := by
    filter_upwards [hV.mem_nhds ht] with s hs
    have hs0 : a s ≠ 0 := hs.2
    simp only [Function.comp_apply, A, dif_neg hs0]
  have hA : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, B) ∞ A V := by
    intro t ht
    have haAt : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, B) ∞ a t :=
      (ha.contDiffAt (hU.mem_nhds ht.1)).contMDiffAt
    have hvalAt := haAt.congr_of_eventuallyEq (hval ht)
    exact ((ContMDiffAt.subtypeVal_comp_iff (puncturedModel B) A t).mp hvalAt).contMDiffWithinAt
  obtain ⟨f, hf, hfgerm⟩ := exists_smooth_curve_with_germ_at hA hV htV
  refine ⟨f, hf, ?_⟩
  filter_upwards [hfgerm, hval htV] with t ht htval
  exact (congrArg Subtype.val ht).trans htval

/-- In a real vector space of dimension at least two, two prescribed nonzero smooth germs at the
endpoints `0` and `1` are realised by a single smooth nowhere-zero curve. -/
theorem DiskFraming.exists_nonzero_smooth_curve_with_endpoint_germs {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] {a b : ℝ → B} {U V : Set ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b V) (hU : IsOpen U) (hV : IsOpen V)
    (h0U : (0 : ℝ) ∈ U) (h1V : (1 : ℝ) ∈ V) (ha0 : a 0 ≠ 0) (hb1 : b 1 ≠ 0)
    (hdim : 2 ≤ Module.finrank ℝ B) :
    ∃ v : ℝ → B, ContDiff ℝ ∞ v ∧ (∀ t, v t ≠ 0) ∧ (v =ᶠ[𝓝 (0 : ℝ)] a) ∧ (v =ᶠ[𝓝 (1 : ℝ)] b) := by
  obtain ⟨a', ha', heqa⟩ := exists_smooth_punctured_curve_with_germ ha hU h0U ha0
  obtain ⟨b', hb', heqb⟩ := exists_smooth_punctured_curve_with_germ hb hV h1V hb1
  have hrank : 1 < Module.rank ℝ B := by
    rw [← Module.finrank_eq_rank]
    exact_mod_cast (show 1 < Module.finrank ℝ B by omega)
  let : PathConnectedSpace (puncturedModel B) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_compl_singleton_of_one_lt_rank hrank (0 : B))
  let γ := PathConnectedSpace.somePath (a' 0) (b' 1)
  obtain ⟨f, hf, hfa, hfb⟩ := exists_smooth_curve_with_endpoint_germs a' b' ha' hb' γ
  let v : ℝ → B := fun t => (f t : B)
  have hv : ContDiff ℝ ∞ v :=
    ((contMDiff_subtype_val (I := 𝓘(ℝ, B)) (U := puncturedModel B)).comp hf).contDiff
  refine ⟨v, hv, fun t => (f t).property, ?_, ?_⟩
  · filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / 8 by norm_num), heqa] with t ht hta
    change t < 1 / 8 at ht
    exact (congrArg Subtype.val (hfa ht.le)).trans hta
  · filter_upwards [Ioi_mem_nhds (show (7 / 8 : ℝ) < 1 by norm_num), heqb] with t ht htb
    change 7 / 8 < t at ht
    exact (congrArg Subtype.val (hfb ht.le)).trans htb


/-- A map defined and smooth on an open set is the germ along any closed subset of that open set of
a globally smooth map. -/
theorem FrameField.exists_global_field_with_closed_germ {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {L : PlaneImmersion.Plane → F} {U C : Set PlaneImmersion.Plane}
    (hU : IsOpen U) (hL : ContDiffOn ℝ ∞ L U) (hC : IsClosed C) (hCU : C ⊆ U) :
    ∃ L₀ : PlaneImmersion.Plane → F, ContDiff ℝ ∞ L₀ ∧ L₀ =ᶠ[𝓝ˢ C] L := by
  have hdisj : Disjoint Uᶜ C := Set.disjoint_left.mpr (fun _ hxU hxC => hxU (hCU hxC))
  obtain ⟨β, hβ0, hβ1, _⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, PlaneImmersion.Plane)
      hU.isClosed_compl hC hdisj (n := ⊤)
  let L₀ : PlaneImmersion.Plane → F := fun x => β x • L x
  have hβ : ContDiff ℝ ∞ (β : PlaneImmersion.Plane → ℝ) := β.contMDiff.contDiff
  have hL₀ : ContDiff ℝ ∞ L₀ := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact hβ.contDiffAt.smul (hL.contDiffAt (hU.mem_nhds hx))
    · apply
        (contDiffAt_const :
            ContDiffAt ℝ ∞ (fun _ : PlaneImmersion.Plane => (0 : F))
              x).congr_of_eventuallyEq
      have hβx : ∀ᶠ y in 𝓝 x, β y = 0 := hβ0.filter_mono (nhds_le_nhdsSet hx)
      filter_upwards [hβx] with y hy
      change β y • L y = 0
      rw [hy, zero_smul]
  refine ⟨L₀, hL₀, ?_⟩
  filter_upwards [hβ1] with x hx
  change β x • L x = L x
  rw [hx, one_smul]

/-- A smooth field with values in a space of dimension larger than that of the source can be
perturbed relative to a closed set, on which it is nowhere zero, to a field that is nowhere zero
on a prescribed compact set (general position for a section of a bundle of rank exceeding the
base dimension). -/
theorem FrameField.exists_nonzero_field_rel_closed {P F : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [FiniteDimensional ℝ P] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {v : P → F} (hv : ContDiff ℝ ∞ v)
    (hdim : Module.finrank ℝ P < Module.finrank ℝ F) {K C : Set P} (hK : IsCompact K)
    (hC : IsClosed C) (hne : ∀ x ∈ K ∩ C, v x ≠ 0) :
    ∃ v' : P → F, ContDiff ℝ ∞ v' ∧ v' =ᶠ[𝓝ˢ C] v ∧ ∀ x ∈ K, v' x ≠ 0 := by
  let B : Set P := K ∩ v ⁻¹' {0}
  have hB : IsCompact B := hK.inter_right (isClosed_singleton.preimage hv.continuous)
  have hdisj : Disjoint C B := Set.disjoint_left.mpr (fun x hxC hxB => hne x ⟨hxB.1, hxC⟩ hxB.2)
  obtain ⟨β, hβ0, hβ1, -⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, P) hC hB.isClosed hdisj (n := ⊤)
  have hfixed : ∀ x ∈ K, β x = 0 → v x ≠ 0 := by
    intro x hx hβx hvx
    have heq : β x = 1 := hβ1.self_of_nhdsSet x ⟨hx, hvx⟩
    exact zero_ne_one (hβx.symm.trans heq)
  let Z := EuclideanSpace ℝ (Fin 0)
  let g : Z → F := fun _ => 0
  have hg : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, F) ∞ g := contMDiff_const
  have hdim' : Module.finrank ℝ P + Module.finrank ℝ Z < Module.finrank ℝ F := by
    simpa only [Z, finrank_euclideanSpace_fin, add_zero] using hdim
  obtain ⟨a, -, ha⟩ :=
    exists_small_localized_image_avoidance hv.contMDiff hg β.contMDiff hdim'
      (show (0 : ℝ) < 1 by norm_num)
  refine ⟨fun x => v x + β x • a, hv.add (β.contMDiff.contDiff.smul contDiff_const), ?_, ?_⟩
  · filter_upwards [hβ0] with x hx
    rw [hx, zero_smul, add_zero]
  · intro x hx
    by_cases hβx : β x = 0
    · simpa only [hβx, zero_smul, add_zero] using hfixed x hx hβx
    · exact ha x hβx (0 : Z)

/-- A locally defined nowhere-zero field on the plane, given near a closed set, extends to a
globally smooth field, unchanged near the closed set, that is nowhere zero on a prescribed
compact set, provided the target has dimension at least three. -/
theorem FrameField.exists_nonzero_extension_of_local_field {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {v : PlaneImmersion.Plane → F} {U C K : Set PlaneImmersion.Plane} (hU : IsOpen U)
    (hv : ContDiffOn ℝ ∞ v U) (hC : IsClosed C) (hCU : C ⊆ U) (hK : IsCompact K)
    (hne : ∀ x ∈ K ∩ C, v x ≠ 0) (hdim : 3 ≤ Module.finrank ℝ F) :
    ∃ v' : PlaneImmersion.Plane → F, ContDiff ℝ ∞ v' ∧ v' =ᶠ[𝓝ˢ C] v ∧ ∀ x ∈ K, v' x ≠ 0 := by
  obtain ⟨v₀, hv₀, heq⟩ := exists_global_field_with_closed_germ hU hv hC hCU
  have hne₀ : ∀ x ∈ K ∩ C, v₀ x ≠ 0 := by
    intro x hx
    rw [heq.self_of_nhdsSet hx.2]
    exact hne x hx
  have hdim' : Module.finrank ℝ PlaneImmersion.Plane < Module.finrank ℝ F := by
    change Module.finrank ℝ (ℝ × ℝ) < Module.finrank ℝ F
    simp only [Module.finrank_prod, Module.finrank_self]
    omega
  obtain ⟨v', hv', hgerm, hne'⟩ := exists_nonzero_field_rel_closed hv₀ hdim' hK hC hne₀
  exact ⟨v', hv', hgerm.trans heq, hne'⟩


/-- Version of the nowhere-zero extension for one-column frames: a locally defined family of
injective maps out of a line extends to a global smooth family, unchanged near the closed set,
injective on a prescribed compact set. -/
theorem FrameField.exists_one_column_extension_of_local_field {A F : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] (hA : Module.finrank ℝ A = 1)
    {L : PlaneImmersion.Plane → (A →L[ℝ] F)} {U C K : Set PlaneImmersion.Plane}
    (hU : IsOpen U) (hL : ContDiffOn ℝ ∞ L U) (hC : IsClosed C) (hCU : C ⊆ U) (hK : IsCompact K)
    (hi : ∀ x ∈ K ∩ C, Function.Injective (L x)) (hdim : 3 ≤ Module.finrank ℝ F) :
    ∃ L' : PlaneImmersion.Plane → (A →L[ℝ] F),
      ContDiff ℝ ∞ L' ∧ L' =ᶠ[𝓝ˢ C] L ∧ ∀ x ∈ K, Function.Injective (L' x) := by
  have hne : ∀ x ∈ K ∩ C, L x ≠ 0 := fun x hx =>
    (injective_iff_ne_zero_of_finrank_one hA (L x)).mp (hi x hx)
  have hdim' : 3 ≤ Module.finrank ℝ (A →L[ℝ] F) := by rwa [finrank_one_column hA]
  obtain ⟨L', hL', heq, hne'⟩ := exists_nonzero_extension_of_local_field hU hL hC hCU hK hne hdim'
  exact
    ⟨L', hL', heq, fun x hx => (injective_iff_ne_zero_of_finrank_one hA (L' x)).mpr (hne' x hx)⟩

/-- In a three-dimensional target, a one-column frame given near a closed set extends to a global
smooth frame, unchanged near that closed set, which on a neighbourhood of a compact star-shaped
set is completed by a smooth two-column field spanning its orthogonal complement. -/
theorem FrameField.exists_completed_one_column_frame {A F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (hA : Module.finrank ℝ A = 1)
    {L : PlaneImmersion.Plane → (A →L[ℝ] F)} {U C K : Set PlaneImmersion.Plane}
    (hU : IsOpen U) (hL : ContDiffOn ℝ ∞ L U) (hC : IsClosed C) (hCU : C ⊆ U) (hK : IsCompact K)
    (hstar : StarConvex ℝ (0 : PlaneImmersion.Plane) K)
    (h0 : (0 : PlaneImmersion.Plane) ∈ K) (hi : ∀ x ∈ K ∩ C, Function.Injective (L x))
    (hdim : Module.finrank ℝ F = 3) :
    ∃ L' : PlaneImmersion.Plane → (A →L[ℝ] F),
      ContDiff ℝ ∞ L' ∧
        L' =ᶠ[𝓝ˢ C] L ∧
          ∃ V : Set PlaneImmersion.Plane,
            IsOpen V ∧
              K ⊆ V ∧
                ∃ B : PlaneImmersion.Plane → (EuclideanSpace ℝ (Fin 2) →L[ℝ] F),
                  ContDiffOn ℝ ∞ B V ∧
                    (∀ x ∈ K, (B x).range = (L' x).rangeᗮ) ∧
                      ∀ x ∈ V, Function.Bijective ((L' x).coprod (B x)) := by
  obtain ⟨L', hL', heq, hi'⟩ :=
    exists_one_column_extension_of_local_field hA hU hL hC hCU hK hi hdim.ge
  have hcodim : Module.finrank ℝ A + 2 = Module.finrank ℝ F := by rw [hA, hdim]
  obtain ⟨V, hV, hKV, B, hB, hr, hb⟩ :=
    exists_smooth_complement_near_starConvex hL' hK hstar h0 hi' 2 hcodim
  exact ⟨L', hL', heq, V, hV, hKV, B, hB, hr, hb⟩

end
