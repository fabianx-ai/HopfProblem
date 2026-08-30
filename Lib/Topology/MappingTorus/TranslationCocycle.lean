/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Lib.Topology.MappingTorus.Basic

/-!
# Translation cocycles on additive mapping tori

An equivariant path in an additive fibre produces an integer family of mapping-torus shears.
The monodromy is expressed by Mathlib's native `ContinuousAddEquiv` structure. The construction
descends through the quotient, supplies its inverse, and exposes a generic lift detector for
proving parameter faithfulness.
-/

@[expose] public section

open Set Function

noncomputable section

namespace Mathoverflow1973.MappingTorus

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X]

/-- A continuous fibre-translation path equivariant for an additive mapping-torus monodromy. -/
structure TranslationCocycle (monodromy : X ≃ₜ+ X) where
  shift : ℝ → X
  continuous_shift : Continuous shift
  shift_add_int : ∀ (t : ℝ) (n : ℤ),
    shift (t + (n : ℝ)) = (monodromy.toHomeomorph ^ (-n)) (shift t)

namespace TranslationCocycle

variable {monodromy : X ≃ₜ+ X}

/-- The cylinder lift of the shear with integer parameter `ell`. -/
def cylinder (C : TranslationCocycle monodromy) (ell : ℤ) (p : ℝ × X) : ℝ × X :=
  (p.1, p.2 + ell • C.shift p.1)

section TopologicalGroup

variable [IsTopologicalAddGroup X]

theorem cylinder_continuous (C : TranslationCocycle monodromy) (ell : ℤ) :
    Continuous (C.cylinder ell) := by
  exact continuous_fst.prodMk
    (continuous_snd.add ((C.continuous_shift.comp continuous_fst).zsmul ell))

end TopologicalGroup

/-- Equivariance is exact already on cylinder lifts. -/
theorem cylinder_deck (C : TranslationCocycle monodromy) (ell n : ℤ) (p : ℝ × X) :
    C.cylinder ell (Mathoverflow1973.MappingTorus.deck monodromy.toHomeomorph n p) =
      Mathoverflow1973.MappingTorus.deck monodromy.toHomeomorph n (C.cylinder ell p) := by
  have hmapAdd : ∀ (k : ℤ) (x y : X),
      (monodromy.toHomeomorph ^ k) (x + y) =
        (monodromy.toHomeomorph ^ k) x + (monodromy.toHomeomorph ^ k) y := by
    intro k
    exact zpow_induction_left (g := monodromy.toHomeomorph)
      (P := fun e ↦ ∀ x y : X, e (x + y) = e x + e y)
      (by intro x y; simp)
      (by
        intro e he x y
        simp only [Homeomorph.mul_apply]
        rw [he]
        change monodromy.toAddEquiv (e x + e y) =
          monodromy.toAddEquiv (e x) + monodromy.toAddEquiv (e y)
        exact monodromy.map_add (e x) (e y))
      (by
        intro e he x y
        simp only [Homeomorph.mul_apply]
        change monodromy.symm (e (x + y)) =
          monodromy.symm (e x) + monodromy.symm (e y)
        rw [he]
        change monodromy.symm.toAddEquiv (e x + e y) =
          monodromy.symm.toAddEquiv (e x) + monodromy.symm.toAddEquiv (e y)
        exact monodromy.symm.map_add (e x) (e y))
      k
  let powerAddHom (k : ℤ) : X →+ X :=
    { toFun := fun x ↦ (monodromy.toHomeomorph ^ k) x
      map_zero' := by
        have h := hmapAdd k 0 0
        have h' : (monodromy.toHomeomorph ^ k) 0 +
            (monodromy.toHomeomorph ^ k) 0 =
              (monodromy.toHomeomorph ^ k) 0 + 0 := by
          simpa only [zero_add, add_zero] using h.symm
        exact add_left_cancel h'
      map_add' := hmapAdd k }
  apply Prod.ext
  · rfl
  · simp only [cylinder, Mathoverflow1973.MappingTorus.deck]
    rw [C.shift_add_int p.1 n, hmapAdd (-n)]
    exact congrArg ((monodromy.toHomeomorph ^ (-n)) p.2 + ·)
      ((powerAddHom (-n)).map_zsmul ell (C.shift p.1)).symm

section TopologicalGroup

variable [IsTopologicalAddGroup X]

/-- The descended mapping-torus self-map. -/
def map (C : TranslationCocycle monodromy) (ell : ℤ) :
    C(Mathoverflow1973.MappingTorus.Torus monodromy.toHomeomorph,
      Mathoverflow1973.MappingTorus.Torus monodromy.toHomeomorph) where
  toFun := Quotient.lift
    (fun p : ℝ × X ↦
      Mathoverflow1973.MappingTorus.mk monodromy.toHomeomorph (C.cylinder ell p))
    (by
      rintro p q ⟨n, rfl⟩
      rw [C.cylinder_deck]
      exact (Mathoverflow1973.MappingTorus.mk_deck monodromy.toHomeomorph n
        (C.cylinder ell p)).symm)
  continuous_toFun :=
    (Mathoverflow1973.MappingTorus.mk_continuous monodromy.toHomeomorph |>.comp
      (C.cylinder_continuous ell)).quotient_lift _

@[simp]
theorem map_mk (C : TranslationCocycle monodromy) (ell : ℤ) (p : ℝ × X) :
    C.map ell (Mathoverflow1973.MappingTorus.mk monodromy.toHomeomorph p) =
      Mathoverflow1973.MappingTorus.mk monodromy.toHomeomorph (C.cylinder ell p) :=
  rfl

/-- Translation parameters add under composition. -/
theorem map_add_apply (C : TranslationCocycle monodromy) (m n : ℤ)
    (z : Mathoverflow1973.MappingTorus.Torus monodromy.toHomeomorph) :
    C.map (m + n) z = C.map m (C.map n z) := by
  induction z using Quotient.inductionOn with
  | _ p =>
      change Mathoverflow1973.MappingTorus.mk monodromy.toHomeomorph
          (C.cylinder (m + n) p) =
        C.map m (Mathoverflow1973.MappingTorus.mk monodromy.toHomeomorph (C.cylinder n p))
      rw [C.map_mk]
      apply congrArg (Mathoverflow1973.MappingTorus.mk monodromy.toHomeomorph)
      apply Prod.ext
      · rfl
      simp only [cylinder]
      rw [add_zsmul]
      abel

/-- The zero translation is the identity. -/
theorem map_zero_apply (C : TranslationCocycle monodromy)
    (z : Mathoverflow1973.MappingTorus.Torus monodromy.toHomeomorph) : C.map 0 z = z := by
  induction z using Quotient.inductionOn with
  | _ p =>
      change Mathoverflow1973.MappingTorus.mk monodromy.toHomeomorph (C.cylinder 0 p) =
        Mathoverflow1973.MappingTorus.mk monodromy.toHomeomorph p
      congr 2
      simp [cylinder]

/-- The descended translation is a homeomorphism, with inverse parameter `-ell`. -/
def shear (C : TranslationCocycle monodromy) (ell : ℤ) :
    Mathoverflow1973.MappingTorus.Torus monodromy.toHomeomorph ≃ₜ
      Mathoverflow1973.MappingTorus.Torus monodromy.toHomeomorph where
  toFun := C.map ell
  invFun := C.map (-ell)
  left_inv z := by
    rw [← C.map_add_apply (-ell) ell]
    simp only [neg_add_cancel]
    exact C.map_zero_apply z
  right_inv z := by
    rw [← C.map_add_apply ell (-ell)]
    simp only [add_neg_cancel]
    exact C.map_zero_apply z
  continuous_toFun := (C.map ell).continuous
  continuous_invFun := (C.map (-ell)).continuous

@[simp]
theorem base_shear (C : TranslationCocycle monodromy) (ell : ℤ)
    (z : Mathoverflow1973.MappingTorus.Torus monodromy.toHomeomorph) :
    Mathoverflow1973.MappingTorus.base monodromy.toHomeomorph (C.shear ell z) =
      Mathoverflow1973.MappingTorus.base monodromy.toHomeomorph z := by
  induction z using Quotient.inductionOn with
  | _ p => rfl

theorem shear_add_apply (C : TranslationCocycle monodromy) (m n : ℤ) (z) :
    C.shear (m + n) z = C.shear m (C.shear n z) :=
  C.map_add_apply m n z

/-- Equality of two shears forces equality of the corresponding translation at every lifted time.
This is the generic lift detector used for parameter injectivity. -/
theorem zsmul_shift_eq_zero_of_shear_eq (C : TranslationCocycle monodromy)
    {m n : ℤ} (h : C.shear m = C.shear n) (t : ℝ) :
    (m - n) • C.shift t = 0 := by
  let z : Mathoverflow1973.MappingTorus.Torus monodromy.toHomeomorph :=
    Mathoverflow1973.MappingTorus.mk monodromy.toHomeomorph (t, 0)
  have hz := congrArg
    (fun e : Mathoverflow1973.MappingTorus.Torus monodromy.toHomeomorph ≃ₜ
        Mathoverflow1973.MappingTorus.Torus monodromy.toHomeomorph ↦ e z) h
  change C.map m z = C.map n z at hz
  dsimp only [z] at hz
  rw [C.map_mk, C.map_mk] at hz
  change Mathoverflow1973.MappingTorus.mk monodromy.toHomeomorph (t, 0 + m • C.shift t) =
    Mathoverflow1973.MappingTorus.mk monodromy.toHomeomorph (t, 0 + n • C.shift t) at hz
  simp only [zero_add] at hz
  obtain ⟨q, htime, hfibre⟩ :=
    (Mathoverflow1973.MappingTorus.mk_eq_mk_iff monodromy.toHomeomorph _ _).mp hz
  have hqR : (q : ℝ) = 0 := by linarith
  have hq : q = 0 := by exact_mod_cast hqR
  subst q
  simp only [neg_zero, zpow_zero, Homeomorph.one_apply] at hfibre
  rw [sub_zsmul, hfibre.symm]
  simp

@[simp]
theorem shear_zero (C : TranslationCocycle monodromy) :
    C.shear 0 = Homeomorph.refl _ := by
  apply Homeomorph.ext
  exact C.map_zero_apply

end TopologicalGroup

end TranslationCocycle

end Mathoverflow1973.MappingTorus
