/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib

/-!
# Extending a homotopy off a closed set

If `U` is open, `K ⊆ U` is closed, and `H` is a homotopy of `f|U` that is stationary off `K`,
then `H` extends by the constant homotopy to a homotopy of `f` on the whole space
(`OpenHomotopyExtension.exists_extended_homotopy`). The extension is the pasting of a function on
`U` with `f` (`OpenHomotopyExtension.extendFunction`), continuous by the local pasting lemma
over the open cover `{U, Kᶜ}`.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ENNReal

@[expose] public noncomputable section

attribute [local instance 100] Classical.propDecidable in
/-- The function equal to `g` on the open set `U` and to `f` off `U`. -/
def OpenHomotopyExtension.extendFunction {X Y : Type*} [TopologicalSpace X]
    (U : TopologicalSpace.Opens X) (f : X → Y) (g : U → Y) : X → Y := fun x =>
  if hx : x ∈ U then g ⟨x, hx⟩ else f x

attribute [local instance 100] Classical.propDecidable in
/-- `extendFunction U f g` agrees with `g` on `U`. -/
theorem OpenHomotopyExtension.extendFunction_of_mem {X Y : Type*} [TopologicalSpace X]
    (U : TopologicalSpace.Opens X) (f : X → Y) (g : U → Y) (x : U) :
    extendFunction U f g x = g x := by simp only [extendFunction, dif_pos x.property]

attribute [local instance 100] Classical.propDecidable in
/-- `extendFunction U f g` agrees with `f` off `U`. -/
theorem OpenHomotopyExtension.extendFunction_of_not_mem {X Y : Type*} [TopologicalSpace X]
    (U : TopologicalSpace.Opens X) (f : X → Y) (g : U → Y) {x : X} (hx : x ∉ U) :
    extendFunction U f g x = f x := by simp only [extendFunction, dif_neg hx]

attribute [local instance 100] Classical.propDecidable in
/-- If `f` and `g` are continuous and `g = f` on `U` off a closed set `K ⊆ U`, then `extendFunction
  U f g` is continuous. -/
theorem OpenHomotopyExtension.continuous_extendFunction {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (U : TopologicalSpace.Opens X) (f : X → Y) (g : U → Y)
    (hf : Continuous f) (hg : Continuous g) {K : Set X} (hK : IsClosed K) (hKU : K ⊆ U)
    (hfixed : ∀ x : U, (x : X) ∉ K → g x = f x) : Continuous (extendFunction U f g) := by
  have hU : ContinuousOn (extendFunction U f g) U := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (U : Set X).domRestrict (extendFunction U f g) = g :=
      funext (extendFunction_of_mem U f g)
    rw [heq]
    exact hg
  have haway : ContinuousOn (extendFunction U f g) Kᶜ := by
    apply hf.continuousOn.congr
    intro x hx
    by_cases hxU : x ∈ U
    · rw [extendFunction, dif_pos hxU]
      exact hfixed ⟨x, hxU⟩ hx
    · exact extendFunction_of_not_mem U f g hxU
  have hcover : (U : Set X) ∪ Kᶜ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ K
    · exact Or.inl (hKU hx)
    · exact Or.inr hx
  apply continuousOn_univ.mp
  rw [← hcover]
  exact hU.union_of_isOpen haway U.isOpen hK.isOpen_compl

/-- A homotopy on `U` fixed off a closed set extends to the whole space. -/
theorem OpenHomotopyExtension.exists_extended_homotopy {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (U : TopologicalSpace.Opens X) (f : C(X, Y)) (H : C(unitInterval × U, Y))
    {K : Set X} (hK : IsClosed K) (hKU : K ⊆ U) (hzero : ∀ x : U, H (0, x) = f x)
    (hfixed : ∀ t (x : U), (x : X) ∉ K → H (t, x) = f x) :
    ∃ g : C(X, Y),
      ∃ G : f.Homotopy g, (∀ t (x : U), G (t, x) = H (t, x)) ∧ (∀ t x, x ∉ K → G (t, x) = f x) := by
  let V : TopologicalSpace.Opens (unitInterval × X) :=
    ⟨Prod.snd ⁻¹' U, U.isOpen.preimage continuous_snd⟩
  let L : V → Y := fun z => H (z.val.1, ⟨z.val.2, z.property⟩)
  have hL : Continuous L :=
    H.continuous.comp
      ((continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _))
  let T : C(unitInterval × X, Y) :=
    ⟨extendFunction V (fun z => f z.2) L,
      continuous_extendFunction V _ L (f.continuous.comp continuous_snd) hL
        (hK.preimage continuous_snd) (fun _ hz => hKU hz)
        (fun z hz => hfixed z.val.1 ⟨z.val.2, z.property⟩ hz)⟩
  have hlocal (t) (x : U) : T (t, x) = H (t, x) :=
    extendFunction_of_mem V (fun z : unitInterval × X => f z.2) L ⟨(t, x), x.property⟩
  have houtside (t) (x : X) (hx : x ∉ K) : T (t, x) = f x := by
    by_cases hxU : x ∈ U
    · exact (hlocal t ⟨x, hxU⟩).trans (hfixed t ⟨x, hxU⟩ hx)
    · exact extendFunction_of_not_mem V (fun z : unitInterval × X => f z.2) L (x := (t, x)) hxU
  let g : C(X, Y) := T.comp ⟨fun x => (1, x), continuous_const.prodMk continuous_id⟩
  refine
    ⟨g, { toContinuousMap := T, map_zero_left := ?_, map_one_left := fun _ => rfl }, hlocal,
      houtside⟩
  intro x
  by_cases hx : x ∈ U
  · exact (hlocal 0 ⟨x, hx⟩).trans (hzero ⟨x, hx⟩)
  · exact houtside 0 x (fun h => hx (hKU h))

