/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib.Topology.Homotopy.Lifting

/-!
# Connectedness of principal quotient covers from monodromy

For a principal quotient cover over a path-connected base, surjectivity of the fundamental-group
monodromy onto the deck group implies that the total space is path-connected.  This is the
converse of `IsQuotientCoveringMap.fundamentalGroupToMulOpposite_surjective` under the natural
base connectedness hypothesis.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §1.3 (a covering space of a path-connected,
  locally path-connected base is path-connected exactly when the monodromy action on a fibre is
  transitive).
-/

@[expose] public section

open Function MulOpposite Topology

namespace IsQuotientCoveringMap

universe uG uE uX

variable {G : Type uG} {E : Type uE} {X : Type uX}
  [Group G] [TopologicalSpace E] [TopologicalSpace X] [MulAction G E]

/-- A principal quotient cover of a path-connected base has path-connected total space when its
fundamental-group monodromy reaches every deck transformation. -/
theorem pathConnectedSpace_of_fundamentalGroupToMulOpposite_surjective
    {p : E → X} (hp : IsQuotientCoveringMap p G) [PathConnectedSpace X]
    {x : X} (e : p ⁻¹' {x})
    (hsurj : Surjective (hp.fundamentalGroupToMulOpposite e)) :
    PathConnectedSpace E := by
  have joined_e (z : E) : Joined (e : E) z := by
    let δpath : Path x (p z) := PathConnectedSpace.somePath x (p z)
    let δ : Path.Homotopic.Quotient x (p z) := .mk δpath
    let z₀ : p ⁻¹' {p z} := hp.isCoveringMap.monodromy δ e
    obtain ⟨g, hg⟩ := hp.exists_toPermFiber_eq z₀ ⟨z, rfl⟩
    obtain ⟨loop, hloop⟩ := hsurj (op g)
    have hloope : hp.isCoveringMap.monodromy loop e =
        ⟨g • (e : E), (hp.map_smul (e := (e : E)) g).trans e.property⟩ := by
      apply Subtype.ext
      rw [← hp.unop_fundamentalGroupToMulOpposite_smul (e := e) (γ := loop), hloop]
      rfl
    have hend : hp.isCoveringMap.monodromy (loop.trans δ) e = ⟨z, rfl⟩ := by
      rw [hp.isCoveringMap.monodromy_trans_apply, hloope]
      change hp.isCoveringMap.monodromy δ (hp.toPermFiber x g e) = ⟨z, rfl⟩
      rw [hp.monodromy_toPermFiber]
      exact hg
    let Γq := hp.isCoveringMap.liftPathQuotient (loop.trans δ) e
    let Γq' : Path.Homotopic.Quotient (e : E) z :=
      Γq.cast rfl (congrArg Subtype.val hend).symm
    obtain ⟨Γ, -⟩ := Path.Homotopic.Quotient.mk_surjective Γq'
    exact ⟨Γ⟩
  exact
    { nonempty := ⟨e⟩
      joined := fun a b ↦ (joined_e a).symm.trans (joined_e b) }

end IsQuotientCoveringMap
