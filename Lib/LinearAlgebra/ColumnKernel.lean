module
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Submodule.Ker

/-!
# Kernels of linear maps with an invertible column

A linear map `F (a, b) = f a + e b` out of a product whose second column `e` is an isomorphism
is surjective, and its kernel is the graph of `-e⁻¹ ∘ f`: the first projection is an isomorphism
`ker F ≃ₗ A`, with inverse `a ↦ (a, -e⁻¹ (f a))`.

This is the splitting of a short exact sequence along a retraction, specialised to a map given by
two columns; the nearest Mathlib statements are `LinearMap.coprod` and `LinearMap.ker`.
-/

@[expose] public noncomputable section
universe u v w
namespace LinearMap

/-- The first projection identifies the kernel of `F (a, b) = f a + e b` with the first factor
`A`, when the second column `e` is an isomorphism. -/
def kerEquivOfColumnIso
    {A : Type u} {B : Type v} {D : Type w}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup D]
    [Module ℤ A] [Module ℤ B] [Module ℤ D] [Module ℤ (A × B)]
    (F : (A × B) →ₗ[ℤ] D) (f : A →ₗ[ℤ] D) (e : B ≃ₗ[ℤ] D)
    (hF : ∀ a b, F (a, b) = f a + e b)
    [Module ℤ (LinearMap.ker F)] : LinearMap.ker F ≃ₗ[ℤ] A :=
  let E : LinearMap.ker F ≃+ A :=
    { toFun x := x.val.1
      invFun
        a :=
        ⟨(a, -e.symm (f a)), by
          change F (a, -e.symm (f a)) = 0
          rw [hF, map_neg, LinearEquiv.apply_symm_apply, add_neg_cancel]⟩
      left_inv
        x := by
        apply Subtype.ext
        change (x.val.1, -e.symm (f x.val.1)) = x.val
        refine Prod.ext (by rfl) ?_
        apply e.injective
        change e (-e.symm (f x.val.1)) = e x.val.2
        rw [map_neg, LinearEquiv.apply_symm_apply]
        have hx : f x.val.1 + e x.val.2 = 0 := (hF x.val.1 x.val.2).symm.trans x.property
        calc
          -f x.val.1 = -f x.val.1 + 0 := (add_zero _).symm
          _ = -f x.val.1 + (f x.val.1 + e x.val.2) := (congrArg (fun d => -f x.val.1 + d) hx.symm)
          _ = e x.val.2 := by rw [← add_assoc, neg_add_cancel, zero_add]
      right_inv _ := rfl
      map_add' _ _ := rfl
    }
  E.toIntLinearEquiv

/-- The kernel equivalence is the first-coordinate projection. -/
@[simp] theorem kerEquivOfColumnIso_apply
    {A : Type u} {B : Type v} {D : Type w}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup D]
    [Module ℤ A] [Module ℤ B] [Module ℤ D] [Module ℤ (A × B)]
    (F : (A × B) →ₗ[ℤ] D) (f : A →ₗ[ℤ] D) (e : B ≃ₗ[ℤ] D)
    (hF : ∀ a b, F (a, b) = f a + e b)
    [Module ℤ (LinearMap.ker F)] (x : LinearMap.ker F) :
    kerEquivOfColumnIso F f e hF x = x.val.1 := rfl

/-- The inverse of the kernel equivalence sends `a` to `(a, -e⁻¹ (f a))`, the unique point of the
kernel above `a`. -/
@[simp] theorem kerEquivOfColumnIso_symm_apply_val
    {A : Type u} {B : Type v} {D : Type w}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup D]
    [Module ℤ A] [Module ℤ B] [Module ℤ D] [Module ℤ (A × B)]
    (F : (A × B) →ₗ[ℤ] D) (f : A →ₗ[ℤ] D) (e : B ≃ₗ[ℤ] D)
    (hF : ∀ a b, F (a, b) = f a + e b)
    [Module ℤ (LinearMap.ker F)] (a : A) :
    ((kerEquivOfColumnIso F f e hF).symm a).val =
      (a, -e.symm (f a)) := rfl

/-- A map `F (a, b) = f a + e b` with an invertible second column is surjective: `d` is the image
of `(0, e⁻¹ d)`. -/
theorem surjective_of_columnIso {A B D : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup D] [Module ℤ A] [Module ℤ B] [Module ℤ D] [Module ℤ (A × B)]
    (F : (A × B) →ₗ[ℤ] D) (f : A →ₗ[ℤ] D) (e : B ≃ₗ[ℤ] D) (hF : ∀ a b, F (a, b) = f a + e b) :
    Function.Surjective F := by
  intro d
  refine ⟨(0, e.symm d), ?_⟩
  rw [hF, map_zero, LinearEquiv.apply_symm_apply, zero_add]

end LinearMap
