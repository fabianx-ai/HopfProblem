/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.H1Vanishing.Flasque
public import Lib.Topology.Sheaves.OpenRestriction.Cohomology

/-!
# Flasque additive sheaves are acyclic

This is the standard dimension-shifting proof that a flasque sheaf of abelian groups has zero
sheaf cohomology in every strictly positive degree.

The categorical seam needed by the argument is proved explicitly: an injective additive sheaf is
flasque.  Sections on an open are represented by the free sheaf on that open, inclusion of opens
induces a monomorphism of representing sheaves, and injectivity extends the representing map.
Consequently, the cokernel of a flasque sheaf inside an injective sheaf is again flasque.  The
native Ext long exact sequence then reduces degree `n + 2` to degree `n + 1`, with the existing
degree-one theorem as the base case.

Reference: Hartshorne, *Algebraic Geometry*, III Lemma 2.4 (injective implies flasque) and
III Prop. 2.5 (flasque implies acyclic); see also Godement, *Topologie algébrique et théorie des
faisceaux*, II.4.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits
open CategoryTheory.Abelian

universe u

namespace TopCat.Sheaf.OpenRestriction

variable {X : TopCat.{u}}

/-- The free sheaf represented by an open, functorially in the open. -/
abbrev freeOpenFunctor (X : TopCat.{u}) :
    Opens X ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat

/-- Inclusion of opens induces a monomorphism between their free representing sheaves. -/
theorem freeOpenFunctor_map_mono {U V : Opens X} (i : U ⟶ V) :
    Mono ((freeOpenFunctor X).map i) := by
  have : Mono (yoneda.map i) := by infer_instance
  have : Mono (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map
      (yoneda.map i)) := by infer_instance
  have : (presheafToSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat).PreservesMonomorphisms := by infer_instance
  change Mono ((presheafToSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat).map
        (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map
          (yoneda.map i)))
  infer_instance

end TopCat.Sheaf.OpenRestriction

namespace TopCat.Sheaf.IsFlasque

variable {X : TopCat.{u}}

open TopCat.Sheaf.OpenRestriction

/-- Every injective additive sheaf is flasque. -/
theorem of_injective (I : TopCat.Sheaf AddCommGrpCat.{u} X) [Injective I] :
    TopCat.Sheaf.IsFlasque I := by
  constructor
  intro U V i
  rw [AddCommGrpCat.epi_iff_surjective]
  intro s
  let j : V.unop ⟶ U.unop := i.unop
  let m : freeOpen V.unop ⟶ freeOpen U.unop :=
    (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
      presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map j
  have hm : Mono m := by
    dsimp only [m]
    change Mono ((freeOpenFunctor X).map j)
    exact freeOpenFunctor_map_mono j
  let _ : Mono m := hm
  let h : freeOpen V.unop ⟶ I := (freeHomEquiv V.unop I).symm s
  let e : freeOpen U.unop ⟶ I := Injective.factorThru h m
  refine ⟨freeHomEquiv U.unop I e, ?_⟩
  have he : m ≫ e = h := Injective.comp_factorThru h m
  have hn := freeHomEquiv_naturality_open j I e
  have hn' :
      freeHomEquiv V.unop I (m ≫ e) =
        I.obj.map i (freeHomEquiv U.unop I e) := by
    simpa only [m, j, Quiver.Hom.op_unop] using hn
  change I.obj.map i (freeHomEquiv U.unop I e) = s
  rw [← hn', he]
  exact (freeHomEquiv V.unop I).apply_symm_apply s

end TopCat.Sheaf.IsFlasque

namespace TopCat.SheafCohomology

variable {X : TopCat.{u}}

private abbrev constantIntegerSheaf : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))

/-- A flasque additive sheaf has zero native Ext-defined cohomology in degree `n + 1`. -/
theorem subsingleton_h_succ_of_isFlasque
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) [TopCat.Sheaf.IsFlasque F]
    (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{u} F (n + 1)) := by
  induction n generalizing F with
  | zero =>
      simpa using TopCat.SheafH1.subsingleton_h1_of_isFlasque F
  | succ n ih =>
      let p : InjectivePresentation F := Classical.arbitrary _
      have hS := p.shortExact_shortComplex
      have hI : TopCat.Sheaf.IsFlasque p.J :=
        TopCat.Sheaf.IsFlasque.of_injective p.J
      let _ : TopCat.Sheaf.IsFlasque p.J := hI
      have hQ : TopCat.Sheaf.IsFlasque (cokernel p.f) :=
        TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hS
      let _ : TopCat.Sheaf.IsFlasque (cokernel p.f) := hQ
      have hsub : Subsingleton
          (Ext.{u} constantIntegerSheaf (cokernel p.f) (n + 1)) := by
        exact ih (cokernel p.f)
      refine subsingleton_of_forall_eq 0 ?_
      intro e
      obtain ⟨e₀, he₀⟩ := Ext.covariant_sequence_exact₁
        constantIntegerSheaf hS e (Ext.eq_zero_of_injective _)
        (n₀ := n + 1) (by omega)
      rw [← he₀, @Subsingleton.elim _ hsub e₀ 0]
      exact Ext.zero_comp constantIntegerSheaf (n + 1) hS.extClass (n + 2) (by omega)

/-- A flasque additive sheaf has zero native Ext-defined cohomology in every positive degree. -/
theorem subsingleton_h_of_isFlasque
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) [TopCat.Sheaf.IsFlasque F]
    (n : ℕ) (hn : 0 < n) :
    Subsingleton (CategoryTheory.Sheaf.H.{u} F n) := by
  cases n with
  | zero => simp at hn
  | succ n =>
      simpa [Nat.succ_eq_add_one] using subsingleton_h_succ_of_isFlasque F n

end TopCat.SheafCohomology
