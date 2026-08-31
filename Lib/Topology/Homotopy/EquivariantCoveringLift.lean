/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Lib.Topology.Homotopy.QuotientCoveringSpace

/-!
# Equivariance of maps between principal covering spaces

A continuous map between principal covering spaces which covers a map of the bases is determined
by its value at one point.  Consequently, if the map intertwines one deck transformation at that
point, it intertwines that deck transformation everywhere.  An intertwining relation for all deck
transformations at one point therefore makes the map equivariant globally.

Existence and uniqueness of a based lift from a simply connected, locally path-connected source
are already supplied by `IsCoveringMap.existsUnique_continuousMap_lifts` in Mathlib.  The results
below are the complementary deck-equivariance step.
-/

@[expose] public section

noncomputable section

open Function

namespace IsQuotientCoveringMap

universe uG uH uE uE' uX uY

variable {G : Type uG} {H : Type uH} {E : Type uE} {E' : Type uE'}
  {X : Type uX} {Y : Type uY}
  [Group G] [Group H]
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace X] [TopologicalSpace Y]
  [MulAction G E] [MulAction H E']
  {p : E → X} {q : E' → Y}

/-- If a map between principal covering spaces intertwines a deck transformation at one point,
then it intertwines that deck transformation everywhere.

The source and target covers may have different bases.  The map `r` relates them through
`q (F e) = r (p e)`; no continuity hypothesis on `r` is needed for this uniqueness argument. -/
theorem lift_eq_smul_of_eq_at
    (hp : IsQuotientCoveringMap p G) (hq : IsQuotientCoveringMap q H)
    [PreconnectedSpace E]
    (r : X → Y) (F : C(E, E')) (hF : ∀ e, q (F e) = r (p e))
    (rho : G →* H) (g : G) (e₀ e : E)
    (h₀ : F (g • e₀) = rho g • F e₀) :
    F (g • e) = rho g • F e := by
  have hleft : Continuous (fun x : E ↦ F (g • x)) :=
    F.continuous.comp (hp.continuous_const_smul g)
  have hright : Continuous (fun x : E ↦ rho g • F x) :=
    (hq.continuous_const_smul (rho g)).comp F.continuous
  have hproj : q ∘ (fun x : E ↦ F (g • x)) = q ∘ (fun x : E ↦ rho g • F x) := by
    funext x
    rw [Function.comp_apply, Function.comp_apply, hF, hq.map_smul, hF, hp.map_smul]
  exact congrFun (hq.isCoveringMap.eq_of_comp_eq hleft hright hproj e₀ h₀) e

/-- A based map between principal covering spaces is globally equivariant if it intertwines every
deck transformation at the chosen basepoint. -/
theorem lift_equivariant_of_eq_at
    (hp : IsQuotientCoveringMap p G) (hq : IsQuotientCoveringMap q H)
    [PreconnectedSpace E]
    (r : X → Y) (F : C(E, E')) (hF : ∀ e, q (F e) = r (p e))
    (rho : G →* H) (e₀ : E)
    (h₀ : ∀ g, F (g • e₀) = rho g • F e₀)
    (g : G) (e : E) :
    F (g • e) = rho g • F e :=
  hp.lift_eq_smul_of_eq_at hq r F hF rho g e₀ e (h₀ g)

end IsQuotientCoveringMap
