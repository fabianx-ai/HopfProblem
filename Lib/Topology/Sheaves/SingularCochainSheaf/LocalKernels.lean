/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.SingularCochainSheaf.Sheaf
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Topology.Sheaves.Abelian

/-!
# Local kernel lifts and exactness after sheafification

Exactness of a short complex of sheaves is a stalkwise condition (Iversen, *Cohomology of Sheaves*
II.1; Hartshorne, *Algebraic Geometry* II Ex. 1.2).  Consequently a short complex of presheaves
whose section kernels are locally in the image of the previous map has exact sheafification.

## Main results

* `TopCat.SingularCochainSheaf.sheafify_exact_of_local_kernels`
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace TopCat.SingularCochainSheaf

universe u

variable {X : TopCat.{u}}

private theorem presheaf_stalk_exact_of_local_kernels
    (S : ShortComplex (TopCat.Presheaf AddCommGrpCat.{u} X))
    (h : ∀ (U : Opens X) (x : X) (_hx : x ∈ U) (s : S.X₂.obj (op U)),
      S.g.app (op U) s = 0 →
      ∃ (V : Opens X) (hVU : V ≤ U) (_hxV : x ∈ V) (t : S.X₁.obj (op V)),
        S.f.app (op V) t = S.X₂.map (homOfLE hVU).op s)
    (x : X) : (S.map (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)).Exact := by
  apply (ShortComplex.ab_exact_iff _).mpr
  intro a ha
  obtain ⟨U, hxU, s, rfl⟩ := S.X₂.exists_germ_eq a
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.g
    (S.X₂.germ U x hxU s) = 0 at ha
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at ha
  have hz : S.X₃.germ U x hxU (S.g.app (op U) s) = S.X₃.germ U x hxU 0 :=
    ha.trans (S.X₃.germ U x hxU).hom.map_zero.symm
  obtain ⟨V, hxV, iVU, jVU, he⟩ := S.X₃.germ_eq x hxU hxU _ _ hz
  have hv : S.g.app (op V) (S.X₂.map iVU.op s) = 0 :=
    ((ConcreteCategory.congr_hom (S.g.naturality iVU.op) s).trans he).trans
      (S.X₃.map jVU.op).hom.map_zero
  obtain ⟨W, hWV, hxW, t, ht⟩ := h V x hxV (S.X₂.map iVU.op s) hv
  refine ⟨S.X₁.germ W x hxW t, ?_⟩
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.f
    (S.X₁.germ W x hxW t) = S.X₂.germ U x hxU s
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, ht,
    S.X₂.germ_res_apply, S.X₂.germ_res_apply]

private def sheafificationStalkIso
    (S : ShortComplex (TopCat.Presheaf AddCommGrpCat.{u} X)) (x : X) :
    S.map (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) ≅
      (S.map (sheafification X)).map
        (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) := by
  let K := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  let e (P : TopCat.Presheaf AddCommGrpCat.{u} X) :
      K.obj P ≅ K.obj ((sheafification X).obj P).obj :=
    @asIso AddCommGrpCat.{u} _ _ _
      (K.map (toSheafify (Opens.grothendieckTopology X) P))
      (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat P)
  refine ShortComplex.isoMk (e S.X₁) (e S.X₂) (e S.X₃) ?_ ?_
  · change K.map (toSheafify (Opens.grothendieckTopology X) S.X₁) ≫
        K.map ((sheafification X).map S.f).hom =
      K.map S.f ≫ K.map (toSheafify (Opens.grothendieckTopology X) S.X₂)
    rw [← K.map_comp, ← K.map_comp]
    exact congrArg K.map
      (toSheafify_naturality (Opens.grothendieckTopology X) S.f).symm
  · change K.map (toSheafify (Opens.grothendieckTopology X) S.X₂) ≫
        K.map ((sheafification X).map S.g).hom =
      K.map S.g ≫ K.map (toSheafify (Opens.grothendieckTopology X) S.X₃)
    rw [← K.map_comp, ← K.map_comp]
    exact congrArg K.map
      (toSheafify_naturality (Opens.grothendieckTopology X) S.g).symm

/-- A short complex of presheaves in which every section killed by the second map is locally in
the image of the first has exact sheafification. -/
theorem sheafify_exact_of_local_kernels
    (S : ShortComplex (TopCat.Presheaf AddCommGrpCat.{u} X))
    (h : ∀ (U : Opens X) (x : X) (_hx : x ∈ U) (s : S.X₂.obj (op U)),
      S.g.app (op U) s = 0 →
      ∃ (V : Opens X) (hVU : V ≤ U) (_hxV : x ∈ V) (t : S.X₁.obj (op V)),
        S.f.app (op V) t = S.X₂.map (homOfLE hVU).op s) :
    (S.map (sheafification X)).Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).mpr
  intro x
  exact ShortComplex.exact_of_iso (sheafificationStalkIso S x)
    (presheaf_stalk_exact_of_local_kernels S h x)

end TopCat.SingularCochainSheaf
