/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.GroupTheory.SplitExtension


set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

def twistRelators (a b d : ℤ) : Fin 5 → FreeGroup (Fin 3) :=
  let c := FreeGroup.of (0 : Fin 3)
  let x := FreeGroup.of (1 : Fin 3)
  let y := FreeGroup.of (2 : Fin 3)
  ![c * x * (x * c)⁻¹, c * y * (y * c)⁻¹, x * y * (c ^ a)⁻¹, x ^ 3 * (c ^ b)⁻¹, y ^ 4 * (c ^ d)⁻¹]

abbrev TwistGroup (a b d : ℤ) :=
  PresentedGroup (Set.range (twistRelators a b d))

def TwistGroup.c (a b d : ℤ) : TwistGroup a b d :=
  PresentedGroup.of 0

def TwistGroup.x (a b d : ℤ) : TwistGroup a b d :=
  PresentedGroup.of 1

def TwistGroup.y (a b d : ℤ) : TwistGroup a b d :=
  PresentedGroup.of 2

theorem TwistGroup.c_commute_x (a b d : ℤ) : Commute (c a b d) (x a b d) := by
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (Set.mem_range.mpr ⟨0, rfl⟩)

theorem TwistGroup.x_mul_y (a b d : ℤ) : x a b d * y a b d = c a b d ^ a := by
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (Set.mem_range.mpr ⟨2, rfl⟩)

theorem TwistGroup.x_cube (a b d : ℤ) : x a b d ^ 3 = c a b d ^ b := by
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (Set.mem_range.mpr ⟨3, rfl⟩)

theorem TwistGroup.y_fourth (a b d : ℤ) : y a b d ^ 4 = c a b d ^ d := by
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (Set.mem_range.mpr ⟨4, rfl⟩)

theorem TwistGroup.x_commute_y (a b d : ℤ) : Commute (x a b d) (y a b d) := by
  change x a b d * y a b d = y a b d * x a b d
  apply mul_left_cancel (a := x a b d)
  calc
    x a b d * (x a b d * y a b d) = x a b d * c a b d ^ a := by rw [x_mul_y]
    _ = c a b d ^ a * x a b d := ((c_commute_x a b d).symm.zpow_right a).eq
    _ = x a b d * (y a b d * x a b d) := by rw [← x_mul_y, mul_assoc]

theorem TwistGroup.x_fourth (a b d : ℤ) : x a b d ^ 4 = c a b d ^ (4 * a - d) := by
  calc
    x a b d ^ 4 = (x a b d * y a b d) ^ 4 * (y a b d ^ 4)⁻¹ := by
      rw [(x_commute_y a b d).mul_pow]; group
    _ = (c a b d ^ a) ^ 4 * (c a b d ^ d)⁻¹ := by rw [x_mul_y, y_fourth]
    _ = c a b d ^ (4 * a - d) := by
      rw [← zpow_natCast _ 4, ← zpow_mul, ← zpow_sub]
      congr 1
      ring

theorem TwistGroup.x_eq_c_power (a b d : ℤ) : x a b d = c a b d ^ (4 * a - b - d) := by
  calc
    x a b d = x a b d ^ 4 * (x a b d ^ 3)⁻¹ := by group
    _ = c a b d ^ (4 * a - d) * (c a b d ^ b)⁻¹ := by rw [x_fourth, x_cube]
    _ = c a b d ^ (4 * a - b - d) := by
      rw [← zpow_sub]
      congr 1
      ring

theorem TwistGroup.y_eq_c_power (a b d : ℤ) : y a b d = c a b d ^ (-3 * a + b + d) := by
  calc
    y a b d = (x a b d)⁻¹ * (x a b d * y a b d) := by group
    _ = (c a b d ^ (4 * a - b - d))⁻¹ * c a b d ^ a := by rw [x_mul_y, x_eq_c_power]
    _ = c a b d ^ (-3 * a + b + d) := by
      rw [← zpow_neg, ← zpow_add]
      congr 1
      ring

theorem TwistGroup.generated_by_c (a b d : ℤ) (z : TwistGroup a b d) :
    z ∈ Subgroup.zpowers (c a b d) := by
  apply PresentedGroup.generated_by
  intro j
  fin_cases j
  · exact Subgroup.mem_zpowers _
  · change x a b d ∈ _
    rw [x_eq_c_power]
    exact Subgroup.zpow_mem_zpowers _ _
  · change y a b d ∈ _
    rw [y_eq_c_power]
    exact Subgroup.zpow_mem_zpowers _ _

def TwistGroup.realizationImages {G : Type*} (c₀ x₀ y₀ : G) : Fin 3 → G :=
  ![c₀, x₀, y₀]

theorem TwistGroup.realizationImages_relators {G : Type*} [Group G] (a b d : ℤ) (c₀ x₀ y₀ : G)
    (hcx : Commute c₀ x₀) (hcy : Commute c₀ y₀) (hxy : x₀ * y₀ = c₀ ^ a) (hx : x₀ ^ 3 = c₀ ^ b)
    (hy : y₀ ^ 4 = c₀ ^ d) :
    ∀ r ∈ Set.range (twistRelators a b d), FreeGroup.lift (realizationImages c₀ x₀ y₀) r = 1 := by
  rintro r ⟨i, rfl⟩
  fin_cases i <;> simp [twistRelators, realizationImages, hcx.eq, hcy.eq, hxy, hx, hy]

def TwistGroup.realizationHom {G : Type*} [Group G] (a b d : ℤ) (c₀ x₀ y₀ : G)
    (hcx : Commute c₀ x₀) (hcy : Commute c₀ y₀) (hxy : x₀ * y₀ = c₀ ^ a) (hx : x₀ ^ 3 = c₀ ^ b)
    (hy : y₀ ^ 4 = c₀ ^ d) : TwistGroup a b d →* G :=
  PresentedGroup.toGroup (realizationImages_relators a b d c₀ x₀ y₀ hcx hcy hxy hx hy)

@[simp]
theorem TwistGroup.realizationHom_c {G : Type*} [Group G] (a b d : ℤ) (c₀ x₀ y₀ : G)
    (hcx : Commute c₀ x₀) (hcy : Commute c₀ y₀) (hxy : x₀ * y₀ = c₀ ^ a) (hx : x₀ ^ 3 = c₀ ^ b)
    (hy : y₀ ^ 4 = c₀ ^ d) : realizationHom a b d c₀ x₀ y₀ hcx hcy hxy hx hy (c a b d) = c₀ :=
  PresentedGroup.toGroup.of (realizationImages_relators a b d c₀ x₀ y₀ hcx hcy hxy hx hy)

@[simp]
theorem TwistGroup.realizationHom_x {G : Type*} [Group G] (a b d : ℤ) (c₀ x₀ y₀ : G)
    (hcx : Commute c₀ x₀) (hcy : Commute c₀ y₀) (hxy : x₀ * y₀ = c₀ ^ a) (hx : x₀ ^ 3 = c₀ ^ b)
    (hy : y₀ ^ 4 = c₀ ^ d) : realizationHom a b d c₀ x₀ y₀ hcx hcy hxy hx hy (x a b d) = x₀ :=
  PresentedGroup.toGroup.of (realizationImages_relators a b d c₀ x₀ y₀ hcx hcy hxy hx hy)

@[simp]
theorem TwistGroup.realizationHom_y {G : Type*} [Group G] (a b d : ℤ) (c₀ x₀ y₀ : G)
    (hcx : Commute c₀ x₀) (hcy : Commute c₀ y₀) (hxy : x₀ * y₀ = c₀ ^ a) (hx : x₀ ^ 3 = c₀ ^ b)
    (hy : y₀ ^ 4 = c₀ ^ d) : realizationHom a b d c₀ x₀ y₀ hcx hcy hxy hx hy (y a b d) = y₀ :=
  PresentedGroup.toGroup.of (realizationImages_relators a b d c₀ x₀ y₀ hcx hcy hxy hx hy)
end Mathoverflow1973
