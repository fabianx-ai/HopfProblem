module
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Submodule.Ker

/-! The kernel of `F (a, b) = f a + e b`, with invertible second column,
is canonically the first factor. Textbook source: `CENTER_COLUMN_KERNEL_TEXTBOOK.md`,
CK1–CK7; the inverse recovers the unique second coordinate. -/

@[expose] public noncomputable section
universe u v w
namespace LinearMap

/-- First projection identifies the kernel of an integer-linear map with its first
factor when its second column is invertible (textbook CK1–CK6). -/
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

/-- The kernel equivalence is the actual first-coordinate projection (textbook CK7). -/
@[simp] theorem kerEquivOfColumnIso_apply
    {A : Type u} {B : Type v} {D : Type w}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup D]
    [Module ℤ A] [Module ℤ B] [Module ℤ D] [Module ℤ (A × B)]
    (F : (A × B) →ₗ[ℤ] D) (f : A →ₗ[ℤ] D) (e : B ≃ₗ[ℤ] D)
    (hF : ∀ a b, F (a, b) = f a + e b)
    [Module ℤ (LinearMap.ker F)] (x : LinearMap.ker F) :
    kerEquivOfColumnIso F f e hF x = x.val.1 := rfl

/-- The inverse has the uniquely forced negative second coordinate (textbook CK7). -/
@[simp] theorem kerEquivOfColumnIso_symm_apply_val
    {A : Type u} {B : Type v} {D : Type w}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup D]
    [Module ℤ A] [Module ℤ B] [Module ℤ D] [Module ℤ (A × B)]
    (F : (A × B) →ₗ[ℤ] D) (f : A →ₗ[ℤ] D) (e : B ≃ₗ[ℤ] D)
    (hF : ∀ a b, F (a, b) = f a + e b)
    [Module ℤ (LinearMap.ker F)] (a : A) :
    ((kerEquivOfColumnIso F f e hF).symm a).val =
      (a, -e.symm (f a)) := rfl

end LinearMap
