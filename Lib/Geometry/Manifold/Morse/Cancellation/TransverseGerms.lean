/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Rearrangement
import Lib.Geometry.Manifold.Morse.Connection

/-!
# Transversality of sheet factorisations

Two maps `F : X → M`, `G : Y → M` are transverse at `x`, `y` with `F x = G y`
when the images of their differentials span the tangent space
(`NativeTransversality.At`, from `Morse.Connection`). This file transports
transversality through factorisations:

* if `F = f ∘ u` and `G = g ∘ v` near `x`, `y` with `u x = 0`, `v y = 0`, then
  `F ⋔ G` implies `f ⋔ g` at `0` (`native_transversality_of_sheet_factorizations`);
* a map into a chart `P` whose image lies in the plane `L (A)` factors through
  `P ∘ L` (`exists_native_plane_factorization`,
  `exists_native_plane_sheet_factorization`), and the plane may be described by
  a basin condition (`exists_native_basin_sheet_factorization`);
* for sheets `ℝ × A → Z × ℝ` whose first component is time independent, i.e.
  `(F u).1 = f u.2` near `0`, transversality of the sheets in `Z × ℝ` gives
  transversality of the labels `f`, `g` in `Z`
  (`transverse_labels_of_time_independent_flow_sheets`,
  `transverse_labels_of_native_flow_sheets`).

These are the linear-algebra facts behind the reduction of transversality of
stable and unstable manifolds to transversality of their intersections with a
regular level, cf. Milnor, *Lectures on the h-cobordism theorem*, §4 and §5.

## Tags

transversality, differential-topology
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

/-! ### Time-independent labels -/

/-- The first derivative of a time-independent label. -/
theorem TransverseGerms.derivative_first_of_time_independent_label {A Z : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {F : ℝ × A → Z × ℝ} {f : A → Z} (hF : DifferentiableAt ℝ F 0) (hf : DifferentiableAt ℝ f 0)
    (hlabel : (fun u : ℝ × A => (F u).1) =ᶠ[𝓝 0] (fun u : ℝ × A => f u.2)) :
    ∀ u : ℝ × A, (fderiv ℝ F 0 u).1 = fderiv ℝ f 0 u.2 := by
  have hsnd : HasFDerivAt (fun u : ℝ × A => u.2) (ContinuousLinearMap.snd ℝ ℝ A) 0 :=
    (ContinuousLinearMap.snd ℝ ℝ A).hasFDerivAt
  have hd :
    HasFDerivAt (fun u : ℝ × A => f u.2) ((fderiv ℝ f 0).comp (ContinuousLinearMap.snd ℝ ℝ A))
      0 :=
    hf.hasFDerivAt.comp (f := fun u : ℝ × A => u.2) 0 hsnd
  have heq : fderiv ℝ (fun u : ℝ × A => (F u).1) 0 = fderiv ℝ (fun u : ℝ × A => f u.2) 0 :=
    hlabel.fderiv_eq
  rw [hF.hasFDerivAt.fst.fderiv, hd.fderiv] at heq
  intro u
  exact congrArg (fun L : (ℝ × A) →L[ℝ] Z => L u) heq

/-- Transverse labels of time-independent flow sheets. -/
theorem TransverseGerms.transverse_labels_of_time_independent_flow_sheets {A B Z : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {F : ℝ × A → Z × ℝ} {G : ℝ × B → Z × ℝ} {f : A → Z}
    {g : B → Z} (hF : DifferentiableAt ℝ F 0) (hG : DifferentiableAt ℝ G 0)
    (hf : DifferentiableAt ℝ f 0) (hg : DifferentiableAt ℝ g 0)
    (hlabelF : (fun u : ℝ × A => (F u).1) =ᶠ[𝓝 0] (fun u : ℝ × A => f u.2))
    (hlabelG : (fun u : ℝ × B => (G u).1) =ᶠ[𝓝 0] (fun u : ℝ × B => g u.2))
    (htrans : Function.Surjective ((fderiv ℝ F 0).coprod (fderiv ℝ G 0))) :
    Function.Surjective ((fderiv ℝ f 0).coprod (fderiv ℝ g 0)) := by
  have hfirstF := derivative_first_of_time_independent_label hF hf hlabelF
  have hfirstG := derivative_first_of_time_independent_label hG hg hlabelG
  intro z
  obtain ⟨⟨u, v⟩, huv⟩ := htrans (z, 0)
  refine ⟨(u.2, v.2), ?_⟩
  change fderiv ℝ f 0 u.2 + fderiv ℝ g 0 v.2 = z
  rw [← hfirstF u, ← hfirstG v]
  exact congrArg Prod.fst huv

/-- Transverse labels of native flow sheets. -/
theorem TransverseGerms.transverse_labels_of_native_flow_sheets {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (C : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞) (hC0 : (0 : Z × ℝ) ∈ C.source)
    (F : ℝ × A → M) (G : ℝ × B → M) (hF : MDifferentiableAt 𝓘(ℝ, ℝ × A) 𝓘(ℝ, E) F 0)
    (hG : MDifferentiableAt 𝓘(ℝ, ℝ × B) 𝓘(ℝ, E) G 0) (hF0 : F 0 = C 0) (hG0 : G 0 = C 0)
    {f : A → Z} {g : B → Z} (hf : DifferentiableAt ℝ f 0) (hg : DifferentiableAt ℝ g 0)
    (hlabelF : (fun u : ℝ × A => (C.symm (F u)).1) =ᶠ[𝓝 0] (fun u : ℝ × A => f u.2))
    (hlabelG : (fun u : ℝ × B => (C.symm (G u)).1) =ᶠ[𝓝 0] (fun u : ℝ × B => g u.2))
    (htrans : NativeTransversality.At 𝓘(ℝ, ℝ × A) 𝓘(ℝ, ℝ × B) 𝓘(ℝ, E) F G 0 0) :
    NativeTransversality.At 𝓘(ℝ, A) 𝓘(ℝ, B) 𝓘(ℝ, Z) f g 0 0 := by
  have hFt : F 0 ∈ C.target := hF0.symm ▸ C.map_source' hC0
  have hGt : G 0 ∈ C.target := hG0.symm ▸ C.map_source' hC0
  have hFb : MDifferentiableAt 𝓘(ℝ, ℝ × A) 𝓘(ℝ, Z × ℝ) (C.symm ∘ F) 0 :=
    (C.symm.mdifferentiableAt (by simp) hFt).comp (f := F) 0 hF
  have hGb : MDifferentiableAt 𝓘(ℝ, ℝ × B) 𝓘(ℝ, Z × ℝ) (C.symm ∘ G) 0 :=
    (C.symm.mdifferentiableAt (by simp) hGt).comp (f := G) 0 hG
  have hcross : G 0 = F 0 := hG0.trans hF0.symm
  have ht :=
    ChartMapPerturbation.transverse_in_chart C.symm hF hG hcross hFt (htrans hcross)
  rw [mfderiv_eq_fderiv, mfderiv_eq_fderiv] at ht
  have hl :=
    transverse_labels_of_time_independent_flow_sheets hFb.differentiableAt hGb.differentiableAt hf
      hg hlabelF hlabelG ht
  intro _
  rw [mfderiv_eq_fderiv, mfderiv_eq_fderiv]
  exact hl

/-! ### Sheet factorizations -/

/-- Native transversality from sheet factorizations. -/
theorem TransverseGerms.native_transversality_of_sheet_factorizations
    {A B U V E HU HV HE X Y M : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace HU] [TopologicalSpace HV] [TopologicalSpace HE]
    {I : ModelWithCorners ℝ U HU} {I' : ModelWithCorners ℝ V HV} {J : ModelWithCorners ℝ E HE}
    [TopologicalSpace X] [ChartedSpace HU X] [TopologicalSpace Y] [ChartedSpace HV Y]
    [TopologicalSpace M] [ChartedSpace HE M] {F : X → M} {G : Y → M} {f : A → M} {g : B → M}
    {u : X → A} {v : Y → B} {x : X} {y : Y} (hf : MDifferentiableAt 𝓘(ℝ, A) J f 0)
    (hg : MDifferentiableAt 𝓘(ℝ, B) J g 0) (hu : MDifferentiableAt I 𝓘(ℝ, A) u x)
    (hv : MDifferentiableAt I' 𝓘(ℝ, B) v y) (hu0 : u x = 0) (hv0 : v y = 0)
    (hF : F =ᶠ[𝓝 x] (f ∘ u)) (hG : G =ᶠ[𝓝 y] (g ∘ v)) (hcross : G y = F x)
    (htrans : NativeTransversality.At I I' J F G x y) :
    NativeTransversality.At 𝓘(ℝ, A) 𝓘(ℝ, B) J f g 0 0 := by
  have hfx : MDifferentiableAt 𝓘(ℝ, A) J f (u x) := hu0 ▸ hf
  have hgy : MDifferentiableAt 𝓘(ℝ, B) J g (v y) := hv0 ▸ hg
  have hFd :
    (mfderiv I J F x : U →L[ℝ] E) =
      (mfderiv 𝓘(ℝ, A) J f 0 : A →L[ℝ] E).comp (mfderiv I 𝓘(ℝ, A) u x) := by
    have heq : (mfderiv I J F x : U →L[ℝ] E) = mfderiv I J (f ∘ u) x := hF.mfderiv_eq
    rw [heq, mfderiv_comp x hfx hu, hu0]
  have hGd :
    (mfderiv I' J G y : V →L[ℝ] E) =
      (mfderiv 𝓘(ℝ, B) J g 0 : B →L[ℝ] E).comp (mfderiv I' 𝓘(ℝ, B) v y) := by
    have heq : (mfderiv I' J G y : V →L[ℝ] E) = mfderiv I' J (g ∘ v) y := hG.mfderiv_eq
    rw [heq, mfderiv_comp y hgy hv, hv0]
  intro _ z
  obtain ⟨⟨a, b⟩, hab⟩ := htrans hcross z
  refine ⟨(mfderiv I 𝓘(ℝ, A) u x a, mfderiv I' 𝓘(ℝ, B) v y b), ?_⟩
  rw [hFd, hGd] at hab
  exact hab

/-- A native plane factorization exists. -/
theorem TransverseGerms.exists_native_plane_factorization {A Z U E HU HE X M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace HU] [TopologicalSpace HE] {I : ModelWithCorners ℝ U HU}
    {J : ModelWithCorners ℝ E HE} [TopologicalSpace X] [ChartedSpace HU X] [TopologicalSpace M]
    [ChartedSpace HE M] (P : PartialDiffeomorph 𝓘(ℝ, Z) J Z M ∞) (hP0 : (0 : Z) ∈ P.source)
    (L : A →L[ℝ] Z) (R : Z →L[ℝ] A) (hRL : ∀ a, R (L a) = a) {F : X → M} {x : X}
    (hF : MDifferentiableAt I J F x) (hx : F x = P 0)
    (hplane : ∀ᶠ y in 𝓝 x, ∃ a, P.symm (F y) = L a) :
    ∃ u : X → A, MDifferentiableAt I 𝓘(ℝ, A) u x ∧ u x = 0 ∧ F =ᶠ[𝓝 x] (fun y => P (L (u y))) := by
  let u : X → A := fun y => R (P.symm (F y))
  have hxt : F x ∈ P.target := hx.symm ▸ P.map_source' hP0
  have hi := (P.symm.mdifferentiableAt (by simp) hxt).comp x hF
  have hu : MDifferentiableAt I 𝓘(ℝ, A) u x := R.differentiableAt.mdifferentiableAt.comp x hi
  have hu0 : u x = 0 := by
    change R (P.symm (F x)) = 0
    have hi0 : P.symm (P 0) = 0 := P.left_inv' hP0
    rw [hx, hi0, map_zero]
  refine ⟨u, hu, hu0, ?_⟩
  filter_upwards [hF.continuousAt (P.open_target.mem_nhds hxt), hplane] with y hy hplaneY
  obtain ⟨a, ha⟩ := hplaneY
  change F y = P (L (R (P.symm (F y))))
  rw [ha, hRL]
  exact (P.right_inv' hy).symm.trans (congrArg P ha)

/-- A native plane sheet factorization exists. -/
theorem TransverseGerms.exists_native_plane_sheet_factorization {A Z U E HU HE X M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace HU] [TopologicalSpace HE] {I : ModelWithCorners ℝ U HU}
    {J : ModelWithCorners ℝ E HE} [TopologicalSpace X] [ChartedSpace HU X] [TopologicalSpace M]
    [ChartedSpace HE M] (P : PartialDiffeomorph 𝓘(ℝ, Z) J Z M ∞) (hP0 : (0 : Z) ∈ P.source)
    (L : A →L[ℝ] Z) (R : Z →L[ℝ] A) (hRL : ∀ a, R (L a) = a) {F : X → M} {x : X}
    (hF : MDifferentiableAt I J F x) (hx : F x = P 0)
    (hplane : ∀ᶠ y in 𝓝 x, ∃ a, P.symm (F y) = L a) {f : A → M}
    (hmodel : f =ᶠ[𝓝 0] (fun a => P (L a))) :
    ∃ u : X → A, MDifferentiableAt I 𝓘(ℝ, A) u x ∧ u x = 0 ∧ F =ᶠ[𝓝 x] (f ∘ u) := by
  obtain ⟨u, hu, hu0, hfactor⟩ := exists_native_plane_factorization P hP0 L R hRL hF hx hplane
  have hut : Filter.Tendsto u (𝓝 x) (𝓝 (0 : A)) := hu0 ▸ hu.continuousAt
  have hcomp := hmodel.comp_tendsto hut
  exact ⟨u, hu, hu0, hfactor.trans hcomp.symm⟩

/-- A native basin sheet factorization exists. -/
theorem TransverseGerms.exists_native_basin_sheet_factorization {A Z U E HU HE X M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace HU] [TopologicalSpace HE] {I : ModelWithCorners ℝ U HU}
    {J : ModelWithCorners ℝ E HE} [TopologicalSpace X] [ChartedSpace HU X] [TopologicalSpace M]
    [ChartedSpace HE M] (P : PartialDiffeomorph 𝓘(ℝ, Z) J Z M ∞) (hP0 : (0 : Z) ∈ P.source)
    (L : A →L[ℝ] Z) (R : Z →L[ℝ] A) (hRL : ∀ a, R (L a) = a) {F : X → M} {x : X}
    (hF : MDifferentiableAt I J F x) (hx : F x = P 0) (Basin : M → Prop)
    (hbasin : ∀ z ∈ P.source, Basin (P z) → ∃ a, z = L a) (hFbasin : ∀ᶠ y in 𝓝 x, Basin (F y))
    {f : A → M} (hmodel : f =ᶠ[𝓝 0] (fun a => P (L a))) :
    ∃ u : X → A, MDifferentiableAt I 𝓘(ℝ, A) u x ∧ u x = 0 ∧ F =ᶠ[𝓝 x] (f ∘ u) := by
  have hxt : F x ∈ P.target := hx.symm ▸ P.map_source' hP0
  have hplane : ∀ᶠ y in 𝓝 x, ∃ a, P.symm (F y) = L a := by
    filter_upwards [hF.continuousAt (P.open_target.mem_nhds hxt), hFbasin] with y hy hby
    have hb : Basin (P (P.symm (F y))) := (P.right_inv' hy).symm ▸ hby
    exact hbasin (P.symm (F y)) (P.map_target' hy) hb
  exact exists_native_plane_sheet_factorization P hP0 L R hRL hF hx hplane hmodel

end
