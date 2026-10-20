/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Whitney.FrameField.FrameExtension

/-!
# Planar frames and the two components of `GL₂(ℝ)`

Explicit linear algebra on the plane `PlaneImmersion.Plane = ℝ × ℝ`: the area form
`PlanarFrame.area u v = u₁ v₂ - u₂ v₁`, the quarter turn, the coefficients of a vector in the
orthogonal basis `(u, quarterTurn u)`, and the determinant of an endomorphism as the area of its
columns (`PlanarFrame.determinant_eq_det`).

The set of endomorphisms whose determinant has a fixed sign is path-connected
(`PlanarFrame.nonempty_path_determinantComponent`), i.e. `GL₂(ℝ)` has two path components
distinguished by the sign of the determinant; consequently two smooth germs of endomorphisms at
`0` and `1` with determinants of the same sign are joined by a smooth path of invertible
endomorphisms (`PlanarFrame.exists_smooth_join_of_same_determinant_sign`).

Mathlib has `Matrix.det_fin_two` and `LinearMap.det` but not the path components of `GL₂(ℝ)`.

## Tags

general linear group, path component, determinant sign
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

/-- The area form of two vectors of the plane: the determinant `u₁ v₂ - u₂ v₁`. -/
def PlanarFrame.area (u v : PlaneImmersion.Plane) : ℝ :=
  u.1 * v.2 - u.2 * v.1

/-- The squared Euclidean length of a plane vector. -/
def PlanarFrame.squareLength (u : PlaneImmersion.Plane) : ℝ :=
  u.1 ^ 2 + u.2 ^ 2

/-- The quarter turn of the plane, `(u₁, u₂) ↦ (-u₂, u₁)`. -/
def PlanarFrame.quarterTurn (u : PlaneImmersion.Plane) : PlaneImmersion.Plane :=
  (-u.2, u.1)

/-- The coefficient of `v` along `u` in the orthogonal basis `(u, quarterTurn u)`. -/
def PlanarFrame.parallelCoeff (u v : PlaneImmersion.Plane) : ℝ :=
  (u.1 * v.1 + u.2 * v.2) / squareLength u

/-- The coefficient of `v` along `quarterTurn u` in the orthogonal basis `(u, quarterTurn u)`. -/
def PlanarFrame.transverseCoeff (u v : PlaneImmersion.Plane) : ℝ :=
  area u v / squareLength u

/-- The determinant of an endomorphism of the plane, as the area of its two columns. -/
def PlanarFrame.determinant
    (L : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) : ℝ :=
  area (L (1, 0)) (L (0, 1))

/-- A nonzero plane vector has positive squared length. -/
theorem PlanarFrame.squareLength_pos {u : PlaneImmersion.Plane} (hu : u ≠ 0) :
    0 < squareLength u := by
  have hsq₁ := sq_nonneg u.1
  have hsq₂ := sq_nonneg u.2
  by_contra h
  have hz : u.1 ^ 2 + u.2 ^ 2 ≤ 0 := le_of_not_gt h
  have hu₁ : u.1 = 0 := by nlinarith
  have hu₂ : u.2 = 0 := by nlinarith
  exact hu (Prod.ext hu₁ hu₂)

/-- For `u ≠ 0`, the basis `(u, quarterTurn u)` decomposes every plane vector: `v = parallelCoeff u
v • u + transverseCoeff u v • quarterTurn u`. -/
theorem PlanarFrame.decompose_second_column {u : PlaneImmersion.Plane} (hu : u ≠ 0)
    (v : PlaneImmersion.Plane) :
    parallelCoeff u v • u + transverseCoeff u v • quarterTurn u = v := by
  have hnorm := (squareLength_pos hu).ne'
  ext <;> dsimp [parallelCoeff, transverseCoeff, area, quarterTurn]
  · field_simp
    simp only [squareLength]
    ring
  · field_simp
    simp only [squareLength]
    ring

/-- The area of `u` with a vector written in the basis `(u, quarterTurn u)` reads off the transverse
coefficient: `area u (a • u + b • quarterTurn u) = b * squareLength u`. -/
theorem PlanarFrame.area_transverse (u : PlaneImmersion.Plane) (a b : ℝ) :
    area u (a • u + b • quarterTurn u) = b * squareLength u := by
  dsimp [area, quarterTurn, squareLength]
  ring

/-- The plane endomorphism with columns `(u, v)` sends the first basis vector to `u`. -/
theorem PlanarFrame.linearMap_first (u v : PlaneImmersion.Plane) :
    PlaneImmersion.linearMap (u, v) (1, 0) = u := by
  simp [PlaneImmersion.linearMap_apply]

/-- The plane endomorphism with columns `(u, v)` sends the second basis vector to `v`. -/
theorem PlanarFrame.linearMap_second (u v : PlaneImmersion.Plane) :
    PlaneImmersion.linearMap (u, v) (0, 1) = v := by
  simp [PlaneImmersion.linearMap_apply]

/-- An endomorphism of the plane is the endomorphism whose columns are its values on the two basis
vectors. -/
theorem PlanarFrame.linearMap_columns
    (L : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) :
    PlaneImmersion.linearMap (L (1, 0), L (0, 1)) = L := by
  apply ContinuousLinearMap.ext
  intro p
  have hp : p = p.1 • ((1 : ℝ), 0) + p.2 • (0, 1) := by ext <;> simp
  rw [PlaneImmersion.linearMap_apply, ← map_smul, ← map_smul, ← map_add, ← hp]

/-- The determinant of the plane endomorphism with columns `(u, v)` is the area of `u` and `v`. -/
theorem PlanarFrame.determinant_linearMap (u v : PlaneImmersion.Plane) :
    determinant (PlaneImmersion.linearMap (u, v)) = area u v := by
  rw [determinant, linearMap_first, linearMap_second]

/-- The planar determinant agrees with the determinant of the underlying linear map. -/
theorem PlanarFrame.determinant_eq_det
    (L : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) :
    determinant L = L.toLinearMap.det := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Module.Basis.coe_finTwoProd_repr, determinant, area, mul_comm]

/-- An endomorphism of the plane with nonzero determinant is bijective. -/
theorem PlanarFrame.bijective_of_determinant_ne_zero
    (L : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (hL : determinant L ≠ 0) :
    Function.Bijective L := by
  have hdet : L.toLinearMap.det ≠ 0 := by rwa [determinant_eq_det] at hL
  have hker : L.toLinearMap.ker = ⊥ := by
    by_contra h
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h)
  have hi : Function.Injective L := LinearMap.ker_eq_bot.mp hker
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi⟩

/-- The determinant is continuous on endomorphisms of the plane. -/
theorem PlanarFrame.continuous_determinant : Continuous determinant := by
  have h₁ :
    Continuous
      (fun L : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane => L (1, 0)) :=
    continuous_id.clm_apply continuous_const
  have h₂ :
    Continuous
      (fun L : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane => L (0, 1)) :=
    continuous_id.clm_apply continuous_const
  exact (h₁.fst.mul h₂.snd).sub (h₁.snd.mul h₂.fst)

/-- The quarter turn is continuous. -/
theorem PlanarFrame.continuous_quarterTurn : Continuous quarterTurn :=
  continuous_snd.neg.prodMk continuous_fst

/-- Assembling an endomorphism of the plane from its two columns is continuous. -/
theorem PlanarFrame.continuous_linearMap :
    Continuous
      (PlaneImmersion.linearMap :
        (PlaneImmersion.Plane × PlaneImmersion.Plane) →
          (PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane)) := by
  exact
    ((ContinuousLinearMap.smulRightL ℝ PlaneImmersion.Plane PlaneImmersion.Plane
              (ContinuousLinearMap.fst ℝ ℝ ℝ)).continuous.comp
          continuous_fst).add
      ((ContinuousLinearMap.smulRightL ℝ PlaneImmersion.Plane PlaneImmersion.Plane
            (ContinuousLinearMap.snd ℝ ℝ ℝ)).continuous.comp
        continuous_snd)


/-- The open set of plane endomorphisms whose determinant has the sign `σ`. -/
def PlanarFrame.determinantComponent (σ : ℝ) :
    TopologicalSpace.Opens (PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) :=
  ⟨{L | 0 < σ * determinant L},
    isOpen_lt continuous_const (continuous_const.mul continuous_determinant)⟩

/-- An endomorphism with a definite determinant sign has nonzero first column. -/
theorem PlanarFrame.first_column_ne_zero {σ : ℝ} (L : determinantComponent σ) :
    (L : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (1, 0) ≠ 0 := by
  intro hz
  have h := L.property
  change
    0 <
      σ *
        area ((L : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (1, 0))
          ((L : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (0, 1)) at h
  rw [hz] at h
  simp [area] at h

/-- For an endomorphism with determinant of sign `σ`, the transverse coefficient of the second
column relative to the first has that same sign. -/
theorem PlanarFrame.signed_transverseCoeff_pos {σ : ℝ} (L : determinantComponent σ) :
    0 <
      σ *
        transverseCoeff ((L : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (1, 0))
          ((L : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (0, 1)) := by
  rw [transverseCoeff, ← mul_div_assoc]
  exact div_pos L.property (squareLength_pos (first_column_ne_zero L))

/-- The set of plane endomorphisms of a fixed determinant sign is path-connected: `GL₂(ℝ)` has two
path components, distinguished by the sign of the determinant. -/
theorem PlanarFrame.nonempty_path_determinantComponent {σ : ℝ}
    (a b : determinantComponent σ) : Nonempty (Path a b) := by
  have hrank : 1 < Module.rank ℝ PlaneImmersion.Plane := by
    rw [← Module.finrank_eq_rank]
    norm_num [PlaneImmersion.Plane, Module.finrank_prod, Module.finrank_self]
  let : PathConnectedSpace (DiskFraming.puncturedModel PlaneImmersion.Plane) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_compl_singleton_of_one_lt_rank hrank (0 : PlaneImmersion.Plane))
  let a₁ : DiskFraming.puncturedModel PlaneImmersion.Plane :=
    ⟨(a : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (1, 0),
      first_column_ne_zero a⟩
  let b₁ : DiskFraming.puncturedModel PlaneImmersion.Plane :=
    ⟨(b : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (1, 0),
      first_column_ne_zero b⟩
  let γ := PathConnectedSpace.somePath a₁ b₁
  let v : unitInterval → PlaneImmersion.Plane := fun t => (γ t : PlaneImmersion.Plane)
  have hv : Continuous v := continuous_subtype_val.comp γ.continuous
  have hvne (t : unitInterval) : v t ≠ 0 := (γ t).property
  let α₀ :=
    parallelCoeff ((a : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (1, 0))
      ((a : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (0, 1))
  let α₁ :=
    parallelCoeff ((b : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (1, 0))
      ((b : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (0, 1))
  let β₀ :=
    transverseCoeff ((a : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (1, 0))
      ((a : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (0, 1))
  let β₁ :=
    transverseCoeff ((b : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (1, 0))
      ((b : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (0, 1))
  let α (t : unitInterval) : ℝ := (1 - (t : ℝ)) * α₀ + (t : ℝ) * α₁
  let β (t : unitInterval) : ℝ := (1 - (t : ℝ)) * β₀ + (t : ℝ) * β₁
  have hα : Continuous α :=
    ((continuous_const.sub continuous_subtype_val).mul continuous_const).add
      (continuous_subtype_val.mul continuous_const)
  have hβ : Continuous β :=
    ((continuous_const.sub continuous_subtype_val).mul continuous_const).add
      (continuous_subtype_val.mul continuous_const)
  have hβpos (t : unitInterval) : 0 < σ * β t := by
    have hpos : 0 < (1 - (t : ℝ)) * (σ * β₀) + (t : ℝ) * (σ * β₁) :=
      (convex_Ioi (0 : ℝ)) (signed_transverseCoeff_pos a) (signed_transverseCoeff_pos b)
        (sub_nonneg.mpr t.property.2) t.property.1 (by ring)
    have heq : σ * β t = (1 - (t : ℝ)) * (σ * β₀) + (t : ℝ) * (σ * β₁) := by
      dsimp only [β]
      ring
    rwa [heq]
  let F (t : unitInterval) : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane :=
    PlaneImmersion.linearMap (v t, α t • v t + β t • quarterTurn (v t))
  have hF : Continuous F :=
    continuous_linearMap.comp
      (hv.prodMk ((hα.smul hv).add (hβ.smul (continuous_quarterTurn.comp hv))))
  have hcomponent (t : unitInterval) : F t ∈ determinantComponent σ := by
    change
      0 <
        σ *
          determinant (PlaneImmersion.linearMap (v t, α t • v t + β t • quarterTurn (v t)))
    rw [determinant_linearMap, area_transverse, ← mul_assoc]
    exact mul_pos (hβpos t) (squareLength_pos (hvne t))
  have hv0 : v 0 = (a : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (1, 0) :=
    congrArg Subtype.val γ.source
  have hv1 : v 1 = (b : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) (1, 0) :=
    congrArg Subtype.val γ.target
  have hF0 : F 0 = (a : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) := by
    change PlaneImmersion.linearMap (v 0, α 0 • v 0 + β 0 • quarterTurn (v 0)) = _
    have hα0 : α 0 = α₀ := by simp [α]
    have hβ0 : β 0 = β₀ := by simp [β]
    rw [hv0, hα0, hβ0, decompose_second_column (first_column_ne_zero a)]
    exact linearMap_columns a
  have hF1 : F 1 = (b : PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane) := by
    change PlaneImmersion.linearMap (v 1, α 1 • v 1 + β 1 • quarterTurn (v 1)) = _
    have hα1 : α 1 = α₁ := by simp [α]
    have hβ1 : β 1 = β₁ := by simp [β]
    rw [hv1, hα1, hβ1, decompose_second_column (first_column_ne_zero b)]
    exact linearMap_columns b
  exact
    ⟨{  toFun := fun t => ⟨F t, hcomponent t⟩
        continuous_toFun := hF.subtype_mk hcomponent
        source' := Subtype.ext hF0
        target' := Subtype.ext hF1 }⟩

/-- Two smooth germs of plane endomorphisms at the endpoints `0` and `1`, whose determinants have
the same sign, are joined by a smooth path of invertible endomorphisms of that determinant sign. -/
theorem PlanarFrame.exists_smooth_join_of_same_determinant_sign
    {a b : ℝ → (PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane)} {U V : Set ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b V) (hU : IsOpen U) (hV : IsOpen V)
    (h0U : (0 : ℝ) ∈ U) (h1V : (1 : ℝ) ∈ V)
    (hsign : 0 < (a 0).toLinearMap.det * (b 1).toLinearMap.det) :
    ∃ L : ℝ → (PlaneImmersion.Plane →L[ℝ] PlaneImmersion.Plane),
      ContDiff ℝ ∞ L ∧
        (∀ t, Function.Bijective (L t)) ∧
          (∀ t, 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det) ∧
            (L =ᶠ[𝓝 (0 : ℝ)] a) ∧ (L =ᶠ[𝓝 (1 : ℝ)] b) := by
  let σ := (a 0).toLinearMap.det
  have ha0ne : (a 0).toLinearMap.det ≠ 0 := by
    intro hz
    rw [hz, MulZeroClass.zero_mul] at hsign
    exact lt_irrefl _ hsign
  have ha0 : a 0 ∈ determinantComponent σ := by
    change 0 < (a 0).toLinearMap.det * determinant (a 0)
    rw [determinant_eq_det]
    exact mul_self_pos.mpr ha0ne
  have hb1 : b 1 ∈ determinantComponent σ := by
    change 0 < (a 0).toLinearMap.det * determinant (b 1)
    rw [determinant_eq_det]
    exact hsign
  obtain ⟨γ⟩ :=
    nonempty_path_determinantComponent (⟨a 0, ha0⟩ : determinantComponent σ)
      (⟨b 1, hb1⟩ : determinantComponent σ)
  obtain ⟨L, hL, hmem, hleft, hright⟩ :=
    exists_smooth_open_curve_with_endpoint_germs (determinantComponent σ) ha hb hU hV h0U
      h1V ha0 hb1 γ
  have hpositive (t : ℝ) : 0 < (a 0).toLinearMap.det * (L t).toLinearMap.det := by
    have h := hmem t
    change 0 < (a 0).toLinearMap.det * determinant (L t) at h
    rwa [determinant_eq_det] at h
  refine ⟨L, hL, ?_, hpositive, hleft, hright⟩
  intro t
  apply bijective_of_determinant_ne_zero (L t)
  intro hz
  rw [determinant_eq_det] at hz
  have h := hpositive t
  rw [hz, MulZeroClass.mul_zero] at h
  exact lt_irrefl _ h

end
