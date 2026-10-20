/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
-- Reference copy of Mathlib PR fabianx-ai/mathlib4#4 (branch first-hurewicz-structure-v2, commit d9dafd54). Kept verbatim except for import paths.
module

public import Lib.AlgebraicTopology.Hurewicz.Degree1

/-!
# Characters of the fundamental group through singular first homology

By the degree-one Hurewicz theorem, a homomorphism from the fundamental group of a
path-connected space to an abelian group is the same thing as a `ℤ`-linear character of
singular first homology. This file records that dictionary and its basic calculus:

* `h1CharacterOfPi1` : the `H₁` character induced by a character of `π₁` with abelian target;
* `h1CharacterOfPi1_loop` : its value on the class of a loop;
* `pi1_ker_le_of_h1_ker_le` : kernel inclusions descend from `H₁` to `π₁`;
* `monoidHom_eq_of_h1Character_eq` : two characters of `π₁` agree once their `H₁` characters
  agree;
* `rebaseCharacter` and `h1CharacterOfPi1_rebaseCharacter` : moving the basepoint along a path
  does not change the induced `H₁` character;
* `h1CharacterOfPi1_comp_map` : compatibility with continuous maps.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], Theorem 2A.1, combined with the universal
  property of abelianization (`Abelianization.lift`): a homomorphism from `π₁(X, b)` to an
  abelian group factors uniquely through `π₁(X, b)ᵃᵇ ≅ H₁(X)`.
-/

@[expose] public noncomputable section

open Function Topology
open scoped ContinuousMap

namespace AlgebraicTopology.Hurewicz

/-- Rebase a character along a path, using mathlib's fundamental-group path equivalence. -/
def rebaseCharacter {X G : Type*} [TopologicalSpace X] [Group G] {x y : X} (p : Path x y)
    (φ : FundamentalGroup X y →* G) : FundamentalGroup X x →* G :=
  φ.comp (FundamentalGroup.fundamentalGroupMulEquivOfPath p).toMonoidHom

variable {X Y A : Type} [TopologicalSpace X] [TopologicalSpace Y] [AddCommGroup A]

/-- The singular-`H₁` character induced by an abelian fundamental-group character. -/
def h1CharacterOfPi1 [PathConnectedSpace X] (b : X)
    (φ : FundamentalGroup X b →* Multiplicative A) : SingularH1 X →ₗ[ℤ] A :=
  (Abelianization.lift φ).toAdditiveLeft.toIntLinearMap.comp (hurewiczEquiv b).symm.toLinearMap

/-- The defining property of the induced `H₁` character: on the homology class of a loop it
returns the value of the original `π₁` character on that loop's class. -/
@[simp]
theorem h1CharacterOfPi1_loop [PathConnectedSpace X] (b : X)
    (φ : FundamentalGroup X b →* Multiplicative A) (p : Path b b) :
    h1CharacterOfPi1 b φ (loopHomologyClass p) = (φ ⟦p⟧).toAdd := by
  change (Abelianization.lift φ).toAdditiveLeft ((hurewiczEquiv b).symm (loopHomologyClass p)) = _
  rw [← hurewiczEquiv_loopClass, LinearEquiv.symm_apply_apply]
  rfl

/-- A degree-one homology kernel inclusion descends to the corresponding fundamental-group
kernel inclusion for an abelian character. -/
theorem pi1_ker_le_of_h1_ker_le [PathConnectedSpace X] (f : C(X, Y)) (b : X)
    (φ : FundamentalGroup X b →* Multiplicative A)
    (hker : (SingularH1.map f).ker ≤ (h1CharacterOfPi1 b φ).ker) :
    (FundamentalGroup.map f b).ker ≤ φ.ker := by
  intro a ha
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective a
  rw [MonoidHom.mem_ker] at ha ⊢
  have ha' : Path.Homotopic.Quotient.mk (p.map f.continuous) = (1 : FundamentalGroup Y (f b)) :=
    (Path.Homotopic.Quotient.mk_map p f).trans ha
  have hz : SingularH1.map f (loopHomologyClass p) = 0 := by
    rw [SingularH1.map_loopHomologyClass]
    exact loopHomologyClass_eq_zero_of_mk_eq_one _ ha'
  have hc := hker hz
  rw [LinearMap.mem_ker, h1CharacterOfPi1_loop] at hc
  exact hc

/-- Loop evaluation at an arbitrary point, transported to the character's basepoint. -/
theorem h1CharacterOfPi1_loop_at [PathConnectedSpace X] (b : X)
    (φ : FundamentalGroup X b →* Multiplicative A) {x : X} (γ : Path x b) (p : Path x x) :
    h1CharacterOfPi1 b φ (loopHomologyClass p) =
      ((φ.comp (FundamentalGroup.fundamentalGroupMulEquivOfPath γ).toMonoidHom) ⟦p⟧).toAdd := by
  rw [← loopHomologyClass_conjugate γ p, h1CharacterOfPi1_loop]
  rfl

/-- Abelian fundamental-group characters agree once their induced singular-`H₁` characters
agree. -/
theorem monoidHom_eq_of_h1Character_eq [PathConnectedSpace X] (x : X)
    (f g : FundamentalGroup X x →* Multiplicative A)
    (h : h1CharacterOfPi1 x f = h1CharacterOfPi1 x g) : f = g := by
  ext a
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective a
  change (f ⟦p⟧).toAdd = (g ⟦p⟧).toAdd
  rw [← h1CharacterOfPi1_loop x f p, ← h1CharacterOfPi1_loop x g p, h]

/-- Rebasing a character does not change its induced singular-`H₁` character. -/
theorem h1CharacterOfPi1_rebaseCharacter [PathConnectedSpace X] {x y : X} (p : Path x y)
    (φ : FundamentalGroup X y →* Multiplicative A) :
    h1CharacterOfPi1 x (rebaseCharacter p φ) = h1CharacterOfPi1 y φ := by
  ext a
  obtain ⟨q, rfl⟩ := loopHomologyClass_surjective x a
  rw [h1CharacterOfPi1_loop]
  exact (h1CharacterOfPi1_loop_at y φ p q).symm

/-- Compatibility of an induced `H₁` character with a continuous map. -/
theorem h1CharacterOfPi1_comp_map [PathConnectedSpace X] [PathConnectedSpace Y] (f : C(X, Y))
    (x : X) (φ : FundamentalGroup Y (f x) →* Multiplicative A) :
    h1CharacterOfPi1 x (φ.comp (FundamentalGroup.map f x)) =
      (h1CharacterOfPi1 (f x) φ).comp (SingularH1.map f) := by
  ext a
  obtain ⟨p, rfl⟩ := loopHomologyClass_surjective x a
  rw [h1CharacterOfPi1_loop, LinearMap.comp_apply, SingularH1.map_loopHomologyClass,
    h1CharacterOfPi1_loop]
  rfl

end AlgebraicTopology.Hurewicz
