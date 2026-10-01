module

public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.Reflection

/-!
# Unit-normal reflection for a real bilinear form

Textbook source: reviewed G06 R01/R02. The four-term bilinear expansion,
normal-coordinate negation and fixed-kernel argument require only the stated
symmetry and unit normalization. Involution and inverse reuse Module.reflection.
No topology, positivity or finite-dimensional hypothesis is needed.
-/

@[expose] public section
noncomputable section
namespace LinearMap.BilinForm
universe u

/-- The unit-normal reflection of R01, bundled by the existing linear reflection. -/
def unitNormalReflection {V : Type u} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (n : V) (hn : B n n = 1) : V ≃ₗ[ℝ] V :=
  Module.reflection (x := n) (f := (2 : ℝ) • B n)
    (by change (2 : ℝ) * B n n = 2; simp only [hn, mul_one])

/-- R01: evaluation with the normal in the first slot. -/
theorem unitNormalReflection_apply_left {V : Type u} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (n : V) (hn : B n n = 1) (v : V) :
    unitNormalReflection B n hn v = v - (2 * B n v) • n := by
  exact Module.reflection_apply v _

/-- R01: symmetry gives the reviewed second-slot formula. -/
theorem unitNormalReflection_apply {V : Type u} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hB : ∀ x y : V, B x y = B y x)
    (n : V) (hn : B n n = 1) (v : V) :
    unitNormalReflection B n hn v = v - (2 * B v n) • n := by
  rw [unitNormalReflection_apply_left, hB n v]

/-- R01: expand all four bilinear terms and cancel using the unit square. -/
theorem unitNormalReflection_preserves {V : Type u} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hB : ∀ x y : V, B x y = B y x)
    (n : V) (hn : B n n = 1) (v w : V) :
    B (unitNormalReflection B n hn v) (unitNormalReflection B n hn w) = B v w := by
  rw [unitNormalReflection_apply B hB, unitNormalReflection_apply B hB]
  simp only [sub_left, sub_right, smul_left, smul_right, hn, hB n w]
  ring

/-- R02: the normal coordinate is negated by direct bilinear expansion. -/
theorem unitNormalReflection_normal {V : Type u} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hB : ∀ x y : V, B x y = B y x)
    (n : V) (hn : B n n = 1) (v : V) :
    B (unitNormalReflection B n hn v) n = -B v n := by
  rw [unitNormalReflection_apply B hB]
  simp only [sub_left, smul_left, hn]
  ring

/-- R02: the existing normalized reflection is an involution. -/
theorem unitNormalReflection_involutive {V : Type u} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (n : V) (hn : B n n = 1) :
    Function.Involutive (unitNormalReflection B n hn) :=
  Module.involutive_reflection
    (by change (2 : ℝ) * B n n = 2; simp only [hn, mul_one])

/-- R02: the inverse is the same existing reflection. -/
theorem unitNormalReflection_symm {V : Type u} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (n : V) (hn : B n n = 1) :
    (unitNormalReflection B n hn).symm = unitNormalReflection B n hn :=
  Module.reflection_symm
    (by change (2 : ℝ) * B n n = 2; simp only [hn, mul_one])

/-- R02: the fixed set is exactly the perpendicular kernel; the unit normal is nonzero. -/
theorem unitNormalReflection_fixed_iff {V : Type u} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hB : ∀ x y : V, B x y = B y x)
    (n : V) (hn : B n n = 1) (v : V) :
    unitNormalReflection B n hn v = v ↔ B v n = 0 := by
  have hn0 : n ≠ 0 := by
    intro h
    have hzero : B n n = 0 := by rw [h, zero_left]
    exact one_ne_zero (hn.symm.trans hzero)
  rw [unitNormalReflection_apply B hB]
  constructor
  · intro h
    have hz : (2 * B v n) • n = 0 := (sub_eq_self.mp h)
    have hs : 2 * B v n = 0 := (smul_eq_zero.mp hz).resolve_right hn0
    exact (mul_eq_zero.mp hs).resolve_left (by norm_num)
  · intro h
    simp only [h, mul_zero, zero_smul, sub_zero]

/-- R02: the normal is sent to its negative by the existing reflection supplier. -/
theorem unitNormalReflection_self {V : Type u} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (n : V) (hn : B n n = 1) :
    unitNormalReflection B n hn n = -n :=
  Module.reflection_apply_self
    (by change (2 : ℝ) * B n n = 2; simp only [hn, mul_one])

end LinearMap.BilinForm
