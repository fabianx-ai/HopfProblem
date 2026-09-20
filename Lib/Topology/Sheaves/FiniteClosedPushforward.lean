/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Stalks of finite closed-map pushforwards

For a closed continuous map from a Hausdorff space, the stalk of the pushforward of an additive
sheaf is canonically the product of the stalks over the finite fibre.  The forward map is built
from Mathlib's actual `stalkPushforward` components.  The proof glues simultaneous stalk
representatives on disjoint neighborhoods and uses closedness to shrink around the whole fibre.

No proper-base-change or derived-pushforward theorem is asserted here.

References: Kashiwara–Schapira, *Sheaves on Manifolds*, Prop. 2.5.2 (the stalk of a proper direct
image), and Iversen, *Cohomology of Sheaves*, II.
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace TopCat.FiniteClosedPushforward

variable {X Y : TopCat.{u}}

/-- Every point of the fibre lies in the inverse image of a neighborhood of its image point. -/
theorem fiber_mem_preimage (f : X ⟶ Y) (y : Y) (x : f ⁻¹' {y})
    (U : Opens Y) (hy : y ∈ U) : x.val ∈ (Opens.map f).obj U := by
  change f x.val ∈ U
  exact (show f x.val = y from x.property).symm ▸ hy

/-- A closed map provides a saturated neighborhood inside any open set containing its whole
fibre. -/
theorem exists_open_preimage_subset (f : X ⟶ Y) (hf : IsClosedMap f)
    (y : Y) (U : Opens X) (hU : f ⁻¹' {y} ⊆ U) :
    ∃ V : Opens Y, y ∈ V ∧ (Opens.map f).obj V ≤ U := by
  let V : Opens Y :=
    ⟨(f '' (U : Set X)ᶜ)ᶜ, (hf _ U.isOpen.isClosed_compl).isOpen_compl⟩
  refine ⟨V, ?_, ?_⟩
  · rintro ⟨x, hx, hxy⟩
    exact hx (hU hxy)
  · intro x hx
    by_contra hxU
    exact hx ⟨x, hxU, rfl⟩

/-- The canonical pushforward-stalk component at an actual point of the fibre. -/
def pushforwardStalkComponent (f : X ⟶ Y)
    (F : TopCat.Presheaf AddCommGrpCat.{u} X) (y : Y)
    (x : f ⁻¹' {y}) : (f _* F).stalk y ⟶ F.stalk x.val := by
  have hx : f x.val = y := x.property
  exact eqToHom (congrArg (fun z => (f _* F).stalk z) hx.symm) ≫
    F.stalkPushforward AddCommGrpCat.{u} f x.val

/-- On a section over an inverse image, the canonical component is its usual germ at the selected
point of the fibre. -/
@[simp] theorem pushforwardStalkComponent_germ (f : X ⟶ Y)
    (F : TopCat.Presheaf AddCommGrpCat.{u} X) (y : Y)
    (x : f ⁻¹' {y}) (U : Opens Y) (hy : y ∈ U)
    (s : F.obj (op ((Opens.map f).obj U))) :
    pushforwardStalkComponent f F y x ((f _* F).germ U y hy s) =
      F.germ ((Opens.map f).obj U) x.val (fiber_mem_preimage f y x U hy) s := by
  rcases x with ⟨x, hx⟩
  have hxy : f x = y := hx
  subst y
  simp only [pushforwardStalkComponent, eqToHom_refl, Category.id_comp]
  exact TopCat.Presheaf.stalkPushforward_germ_apply AddCommGrpCat.{u} f F U x hy s

/-- The canonical additive map from a pushforward stalk to the product of the stalks at all fibre
points. -/
def pushforwardStalkHom (f : X ⟶ Y)
    (F : TopCat.Presheaf AddCommGrpCat.{u} X) (y : Y) :
    (f _* F).stalk y →+ ∀ x : f ⁻¹' {y}, F.stalk x.val :=
  AddMonoidHom.pi fun x => (pushforwardStalkComponent f F y x).hom

/-- The `x`-component of the canonical map to the fibre stalks is
`pushforwardStalkComponent`. -/
@[simp] theorem pushforwardStalkHom_apply (f : X ⟶ Y)
    (F : TopCat.Presheaf AddCommGrpCat.{u} X) (y : Y)
    (s : (f _* F).stalk y) (x : f ⁻¹' {y}) :
    pushforwardStalkHom f F y s x = pushforwardStalkComponent f F y x s := rfl

/-- The product map on an inverse-image section is computed by the actual germ maps. -/
@[simp] theorem pushforwardStalkHom_germ (f : X ⟶ Y)
    (F : TopCat.Presheaf AddCommGrpCat.{u} X) (y : Y)
    (U : Opens Y) (hy : y ∈ U)
    (s : F.obj (op ((Opens.map f).obj U))) (x : f ⁻¹' {y}) :
    pushforwardStalkHom f F y ((f _* F).germ U y hy s) x =
      F.germ ((Opens.map f).obj U) x.val (fiber_mem_preimage f y x U hy) s :=
  pushforwardStalkComponent_germ f F y x U hy s

/-- Any family of stalk elements at finitely many distinct points of a Hausdorff space has one
section representative on a neighborhood of those points. -/
theorem exists_section_germ_eq_of_finite [T2Space X]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) {s : Set X} (hs : s.Finite)
    (t : ∀ x : s, F.presheaf.stalk x.val) :
    ∃ (U : Opens X) (hU : s ⊆ U) (u : F.presheaf.obj (op U)),
      ∀ x : s, F.presheaf.germ U x.val (hU x.property) u = t x := by
  classical
  obtain ⟨V, hV, hdisj⟩ := hs.t2_separation
  let W : s → Opens X := fun x => ⟨V x.val, (hV x.val).2⟩
  choose U hUW hU u hu using fun x : s =>
    F.presheaf.exists_le_germ_eq (t x) (V := W x) (hV x.val).1
  have hcompatible : TopCat.Presheaf.IsCompatible F.presheaf U u := by
    intro x y
    by_cases hxy : x = y
    · subst y
      rfl
    · apply TopCat.Presheaf.section_ext F (U x ⊓ U y) _ _
      intro z hz
      exfalso
      have hne : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
      exact Set.disjoint_left.mp (hdisj x.property y.property hne)
        (hUW x hz.1) (hUW y hz.2)
  obtain ⟨v, hv, _⟩ := F.existsUnique_gluing U u hcompatible
  have hsubset : s ⊆ (iSup U : Opens X) := by
    intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hU ⟨x, hx⟩⟩
  refine ⟨iSup U, hsubset, v, ?_⟩
  intro x
  calc
    F.presheaf.germ (iSup U) x.val (hsubset x.property) v =
        F.presheaf.germ (U x) x.val (hU x)
          (F.presheaf.map (Opens.leSupr U x).op v) :=
      (F.presheaf.germ_res_apply (Opens.leSupr U x) x.val (hU x) v).symm
    _ = F.presheaf.germ (U x) x.val (hU x) (u x) := by rw [hv x]
    _ = t x := hu x

/-- Pushforward germs are equal whenever the corresponding section germs coincide at every point
of the fibre of a closed map. -/
theorem pushforward_germ_eq_of_fiber_germ_eq (f : X ⟶ Y) (hf : IsClosedMap f)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (y : Y)
    (U V : Opens Y) (hyU : y ∈ U) (hyV : y ∈ V)
    (s : F.presheaf.obj (op ((Opens.map f).obj U)))
    (t : F.presheaf.obj (op ((Opens.map f).obj V)))
    (h : ∀ x : f ⁻¹' {y},
      F.presheaf.germ ((Opens.map f).obj U) x.val
          (fiber_mem_preimage f y x U hyU) s =
        F.presheaf.germ ((Opens.map f).obj V) x.val
          (fiber_mem_preimage f y x V hyV) t) :
    (f _* F.presheaf).germ U y hyU s = (f _* F.presheaf).germ V y hyV t := by
  classical
  choose W hW iWU iWV heq using fun x : f ⁻¹' {y} =>
    F.presheaf.germ_eq x.val (fiber_mem_preimage f y x U hyU)
      (fiber_mem_preimage f y x V hyV) s t (h x)
  have hcover : f ⁻¹' {y} ⊆ (iSup W : Opens X) := by
    intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hW ⟨x, hx⟩⟩
  obtain ⟨T, hyT, hT⟩ := exists_open_preimage_subset f hf y (iSup W) hcover
  let Z : Opens Y := (T ⊓ U) ⊓ V
  have hyZ : y ∈ Z := ⟨⟨hyT, hyU⟩, hyV⟩
  let iZU : Z ⟶ U := homOfLE (inf_le_left.trans inf_le_right)
  let iZV : Z ⟶ V := homOfLE inf_le_right
  apply (f _* F.presheaf).germ_ext Z hyZ iZU iZV
  change F.presheaf.map ((Opens.map f).map iZU).op s =
    F.presheaf.map ((Opens.map f).map iZV).op t
  apply TopCat.Presheaf.section_ext F ((Opens.map f).obj Z) _ _
  intro z hz
  have hzT : z ∈ (Opens.map f).obj T := hz.1.1
  obtain ⟨x, hx⟩ := Opens.mem_iSup.mp (hT hzT)
  rw [F.presheaf.germ_res_apply, F.presheaf.germ_res_apply]
  have hlocal := congrArg (F.presheaf.germ (W x) z hx) (heq x)
  simpa only [F.presheaf.germ_res_apply] using hlocal

/-- For a closed map, the canonical map into all stalks of the fibre is injective. -/
theorem pushforwardStalkHom_injective (f : X ⟶ Y) (hf : IsClosedMap f)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (y : Y) :
    Function.Injective (pushforwardStalkHom f F.presheaf y) := by
  intro s t hst
  obtain ⟨U, hyU, u, rfl⟩ := (f _* F.presheaf).exists_germ_eq s
  obtain ⟨V, hyV, v, rfl⟩ := (f _* F.presheaf).exists_germ_eq t
  apply pushforward_germ_eq_of_fiber_germ_eq f hf F y U V hyU hyV u v
  intro x
  simpa only [pushforwardStalkHom_germ] using congrFun hst x

/-- Actual representatives on disjoint source neighborhoods give a pushforward-germ representative
for every tuple of fibre germs. -/
theorem pushforwardStalkHom_surjective [T2Space X]
    (f : X ⟶ Y) (hf : IsClosedMap f)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (y : Y)
    (hfinite : (f ⁻¹' {y}).Finite) :
    Function.Surjective (pushforwardStalkHom f F.presheaf y) := by
  intro t
  obtain ⟨U, hU, s, hs⟩ := exists_section_germ_eq_of_finite F hfinite t
  obtain ⟨V, hyV, hV⟩ := exists_open_preimage_subset f hf y U hU
  refine ⟨(f _* F.presheaf).germ V y hyV
    (F.presheaf.map (homOfLE hV).op s), ?_⟩
  funext x
  rw [pushforwardStalkHom_germ, F.presheaf.germ_res_apply]
  exact hs x

/-- The canonical map to fibre stalks is bijective for a closed map with finite fibre and
Hausdorff source. -/
theorem pushforwardStalkHom_bijective [T2Space X]
    (f : X ⟶ Y) (hf : IsClosedMap f)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (y : Y)
    (hfinite : (f ⁻¹' {y}).Finite) :
    Function.Bijective (pushforwardStalkHom f F.presheaf y) :=
  ⟨pushforwardStalkHom_injective f hf F y,
    pushforwardStalkHom_surjective f hf F y hfinite⟩

/-- The pushforward stalk is canonically the product of the stalks at the points of a finite
fibre. -/
def pushforwardStalkEquiv [T2Space X]
    (f : X ⟶ Y) (hf : IsClosedMap f)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (y : Y)
    (hfinite : (f ⁻¹' {y}).Finite) :
    (f _* F.presheaf).stalk y ≃+ ∀ x : f ⁻¹' {y}, F.presheaf.stalk x.val :=
  AddEquiv.ofBijective (pushforwardStalkHom f F.presheaf y)
    (pushforwardStalkHom_bijective f hf F y hfinite)

/-- The `x`-component of the finite-fibre equivalence is `pushforwardStalkComponent`. -/
@[simp] theorem pushforwardStalkEquiv_apply [T2Space X]
    (f : X ⟶ Y) (hf : IsClosedMap f)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (y : Y)
    (hfinite : (f ⁻¹' {y}).Finite) (s : (f _* F.presheaf).stalk y)
    (x : f ⁻¹' {y}) :
    pushforwardStalkEquiv f hf F y hfinite s x =
      pushforwardStalkComponent f F.presheaf y x s := rfl

/-- The canonical equivalence sends an inverse-image section germ to its germs at all fibre
points. -/
@[simp] theorem pushforwardStalkEquiv_germ [T2Space X]
    (f : X ⟶ Y) (hf : IsClosedMap f)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (y : Y)
    (hfinite : (f ⁻¹' {y}).Finite) (U : Opens Y) (hy : y ∈ U)
    (s : F.presheaf.obj (op ((Opens.map f).obj U))) (x : f ⁻¹' {y}) :
    pushforwardStalkEquiv f hf F y hfinite ((f _* F.presheaf).germ U y hy s) x =
      F.presheaf.germ ((Opens.map f).obj U) x.val (fiber_mem_preimage f y x U hy) s :=
  pushforwardStalkHom_germ f F.presheaf y U hy s x

/-- The canonical map to the fibre stalks is natural in the presheaf. -/
theorem pushforwardStalkHom_naturality (f : X ⟶ Y)
    {F G : TopCat.Presheaf AddCommGrpCat.{u} X} (α : F ⟶ G)
    (y : Y) (s : (f _* F).stalk y) (x : f ⁻¹' {y}) :
    pushforwardStalkHom f G y
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
          ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map α) s) x =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x.val).map α
        (pushforwardStalkHom f F y s x) := by
  obtain ⟨U, hyU, u, rfl⟩ := (f _* F).exists_germ_eq s
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    pushforwardStalkHom_germ, pushforwardStalkHom_germ,
    TopCat.Presheaf.stalkFunctor_map_germ_apply]
  rfl

/-- The finite-fibre equivalence intertwines the pushforward of a sheaf morphism with its stalk
maps at the actual fibre points. -/
theorem pushforwardStalkEquiv_naturality [T2Space X]
    (f : X ⟶ Y) (hf : IsClosedMap f)
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (α : F ⟶ G)
    (y : Y) (hfinite : (f ⁻¹' {y}).Finite)
    (s : (f _* F.presheaf).stalk y) (x : f ⁻¹' {y}) :
    pushforwardStalkEquiv f hf G y hfinite
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
          ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map α.hom) s) x =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x.val).map α.hom
        (pushforwardStalkEquiv f hf F y hfinite s x) :=
  pushforwardStalkHom_naturality f α.hom y s x

end TopCat.FiniteClosedPushforward
