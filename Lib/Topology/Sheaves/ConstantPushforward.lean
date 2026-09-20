/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.Sheafify

/-!
# Constant sheaves and connected-preimage pushforwards

This file identifies the canonical map from a constant sheaf to the pushforward of a constant
sheaf when inverse images of members of a connected open basis are connected.  The proof uses
Mathlib's actual sheafification of the constant presheaf.  It does not identify higher direct
images or make any cohomological claim.

Along the way the sections of a constant sheaf over an open set are identified with the locally
constant functions on it, so that a connected open set sees exactly one coefficient value.

References: Iversen, *Cohomology of Sheaves*, II (constant sheaves and their sections); Bredon,
*Sheaf Theory*, I.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

universe u

namespace TopCat.ConstantSheaf

/-- The constant presheaf with coefficient group `A`. -/
def presheaf (X : TopCat.{u}) (A : AddCommGrpCat.{u}) :
    TopCat.Presheaf AddCommGrpCat.{u} X :=
  (Functor.const (Opens X)ᵒᵖ).obj A

/-- Mathlib's sheafification of the constant presheaf with coefficient group `A`.  Reducible, so
that the constant sheaf is recognised wherever Mathlib spells it out (`CategoryTheory.Sheaf.H`). -/
@[reducible] def sheaf (X : TopCat.{u}) (A : AddCommGrpCat.{u}) :
    TopCat.Sheaf AddCommGrpCat.{u} X :=
  (CategoryTheory.constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A

/-- The sheafification unit, sending a value to its constant section. -/
def unit (X : TopCat.{u}) (A : AddCommGrpCat.{u}) :
    presheaf X A ⟶ (sheaf X A).obj :=
  CategoryTheory.toSheafify (Opens.grothendieckTopology X) (presheaf X A)

/-- The stalk of the constant presheaf is canonically its coefficient group. -/
def presheafStalkIso (X : TopCat.{u}) (A : AddCommGrpCat.{u}) (x : X) :
    (presheaf X A).stalk x ≅ A := by
  letI : IsConnected (OpenNhds x)ᵒᵖ := IsFiltered.isConnected _
  exact IsColimit.coconePointUniqueUpToIso
    (colimit.isColimit ((OpenNhds.inclusion x).op ⋙ presheaf X A))
    (isColimitConstCocone (OpenNhds x)ᵒᵖ A)

/-- The germ map of the constant presheaf followed by the stalk identification is the
identity. -/
@[reassoc (attr := simp)]
theorem presheaf_germ_stalkIso_hom (X : TopCat.{u}) (A : AddCommGrpCat.{u})
    (x : X) (U : Opens X) (hx : x ∈ U) :
    (presheaf X A).germ U x hx ≫ (presheafStalkIso X A x).hom = 𝟙 A := by
  let : IsConnected (OpenNhds x)ᵒᵖ := IsFiltered.isConnected _
  exact colimit.comp_coconePointUniqueUpToIso_hom
    (F := (OpenNhds.inclusion x).op ⋙ presheaf X A)
    (isColimitConstCocone (OpenNhds x)ᵒᵖ A) (op (⟨U, hx⟩ : OpenNhds x))

/-- Sheafification does not change stalks: the unit is a stalkwise isomorphism. -/
instance unit_stalk_isIso (X : TopCat.{u}) (A : AddCommGrpCat.{u}) (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (unit X A)) :=
  TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} (presheaf X A)

/-- The canonical identification of a native constant-sheaf stalk with its coefficient group. -/
def stalkIso (X : TopCat.{u}) (A : AddCommGrpCat.{u}) (x : X) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (sheaf X A).obj x ≅ A :=
  (asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (unit X A))).symm ≪≫
    presheafStalkIso X A x

/-- The stalk identification of the constant sheaf is compatible with that of the constant
presheaf along the sheafification unit. -/
@[reassoc (attr := simp)]
theorem unit_stalk_stalkIso_hom (X : TopCat.{u}) (A : AddCommGrpCat.{u}) (x : X) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (unit X A) ≫
      (stalkIso X A x).hom = (presheafStalkIso X A x).hom := by
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (unit X A) ≫
    inv ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (unit X A)) ≫
      (presheafStalkIso X A x).hom = _
  exact IsIso.hom_inv_id_assoc _ _

/-- The constant section of value `a` has germ `a` under the stalk identification. -/
@[reassoc (attr := simp)]
theorem unit_germ_stalkIso_hom (X : TopCat.{u}) (A : AddCommGrpCat.{u})
    (x : X) (U : Opens X) (hx : x ∈ U) :
    (unit X A).app (op U) ≫ TopCat.Presheaf.germ (sheaf X A).obj U x hx ≫
      (stalkIso X A x).hom = 𝟙 A := by
  exact (TopCat.Presheaf.stalkFunctor_map_germ_assoc U x hx (unit X A)
    (stalkIso X A x).hom).symm.trans
      ((congrArg (fun g ↦ (presheaf X A).germ U x hx ≫ g)
        (unit_stalk_stalkIso_hom X A x)).trans
          (presheaf_germ_stalkIso_hom X A x U hx))

/-- The additive equivalence underlying `stalkIso`. -/
def stalkEquiv (X : TopCat.{u}) (A : AddCommGrpCat.{u}) (x : X) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (sheaf X A).obj x ≃+ A :=
  (stalkIso X A x).addCommGroupIsoToAddEquiv

/-- The germ at `x` of the constant section of value `a` is `a`. -/
@[simp]
theorem stalkEquiv_germ_unit (X : TopCat.{u}) (A : AddCommGrpCat.{u})
    (x : X) (U : Opens X) (hx : x ∈ U) (a : A) :
    stalkEquiv X A x
      (TopCat.Presheaf.germ (sheaf X A).obj U x hx ((unit X A).app (op U) a)) = a :=
  ConcreteCategory.congr_hom (unit_germ_stalkIso_hom X A x U hx) a

variable {X : TopCat.{u}} {A : AddCommGrpCat.{u}}

private theorem exists_constant_restriction (U : Opens X)
    (s : (sheaf X A).obj.obj (op U)) (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U) (a : A), x ∈ V ∧
      (unit X A).app (op V) a = (sheaf X A).obj.map (homOfLE hVU).op s := by
  have hloc : TopCat.Presheaf.IsLocallySurjective (unit X A) := by
    change CategoryTheory.Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (presheaf X A))
    infer_instance
  obtain ⟨V, hVU, ⟨a, ha⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff (unit X A)).mp hloc U s x hx
  exact ⟨V, hVU, a, hxV, ha⟩

/-- Evaluate a section of the native constant sheaf at a point of its domain. -/
def sectionValue (U : Opens X) (s : (sheaf X A).obj.obj (op U)) (x : U) : A :=
  stalkEquiv X A x.1 (TopCat.Presheaf.germ (sheaf X A).obj U x.1 x.2 s)

/-- The constant section of value `a` takes the value `a` at every point. -/
@[simp]
theorem sectionValue_unit (U : Opens X) (a : A) (x : U) :
    sectionValue U ((unit X A).app (op U) a) x = a :=
  stalkEquiv_germ_unit X A x.1 U x.2 a

/-- Pointwise evaluation of a section commutes with restriction to a smaller open. -/
@[simp]
theorem sectionValue_restrict {U V : Opens X} (i : V ⟶ U)
    (s : (sheaf X A).obj.obj (op U)) (x : V) :
    sectionValue V ((sheaf X A).obj.map i.op s) x =
      sectionValue U s ⟨x.1, i.le x.2⟩ := by
  unfold sectionValue
  rw [TopCat.Presheaf.germ_res_apply]

private theorem section_ext (U : Opens X) (s t : (sheaf X A).obj.obj (op U))
    (h : ∀ x : U, sectionValue U s x = sectionValue U t x) : s = t := by
  apply TopCat.Presheaf.section_ext (sheaf X A) U s t
  intro x hx
  apply (stalkEquiv X A x).injective
  exact h ⟨x, hx⟩

/-- Pointwise values of a native constant-sheaf section are locally constant. -/
theorem sectionValue_isLocallyConstant (U : Opens X)
    (s : (sheaf X A).obj.obj (op U)) : IsLocallyConstant (sectionValue U s) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  obtain ⟨V, hVU, a, hxV, ha⟩ := exists_constant_restriction U s x.1 x.2
  have hval (y : U) (hy : y.1 ∈ V) : sectionValue U s y = a := by
    calc
      sectionValue U s y =
          sectionValue V ((sheaf X A).obj.map (homOfLE hVU).op s) ⟨y.1, hy⟩ :=
        (sectionValue_restrict (homOfLE hVU) s ⟨y.1, hy⟩).symm
      _ = sectionValue V ((unit X A).app (op V) a) ⟨y.1, hy⟩ :=
        congrArg (fun t ↦ sectionValue V t ⟨y.1, hy⟩) ha.symm
      _ = a := sectionValue_unit V a ⟨y.1, hy⟩
  refine ⟨Subtype.val ⁻¹' (V : Set X), V.isOpen.preimage continuous_subtype_val,
    hxV, ?_⟩
  intro y hy
  exact (hval y hy).trans (hval x hxV).symm

/-- On a preconnected open set, every section of the native constant sheaf is represented by a
single coefficient value.  This includes the empty open set. -/
theorem unit_app_surjective (X : TopCat.{u}) (A : AddCommGrpCat.{u})
    (U : Opens X) (hU : IsPreconnected (U : Set X)) :
    Function.Surjective ((unit X A).app (op U)) := by
  let : PreconnectedSpace U := Subtype.preconnectedSpace hU
  intro s
  obtain ⟨a, ha⟩ := (sectionValue_isLocallyConstant U s).exists_eq_const
  refine ⟨a, ?_⟩
  apply section_ext
  intro x
  exact (sectionValue_unit U a x).trans (congrFun ha x).symm

/-- A nonempty open set distinguishes coefficient values viewed as constant sections. -/
theorem unit_app_injective (X : TopCat.{u}) (A : AddCommGrpCat.{u})
    (U : Opens X) (hU : (U : Set X).Nonempty) :
    Function.Injective ((unit X A).app (op U)) := by
  obtain ⟨x, hx⟩ := hU
  intro a b hab
  have h := congrArg (fun s ↦ sectionValue U s ⟨x, hx⟩) hab
  exact (sectionValue_unit U a ⟨x, hx⟩).symm.trans
    (h.trans (sectionValue_unit U b ⟨x, hx⟩))

/-- On a connected open set, the sheafification unit identifies sections with the coefficient
group. -/
theorem unit_app_bijective (X : TopCat.{u}) (A : AddCommGrpCat.{u})
    (U : Opens X) (hU : IsConnected (U : Set X)) :
    Function.Bijective ((unit X A).app (op U)) :=
  ⟨unit_app_injective X A U hU.nonempty,
    unit_app_surjective X A U hU.isPreconnected⟩

variable {X Y : TopCat.{u}} (A : AddCommGrpCat.{u}) (f : X ⟶ Y)

/-- The canonical map from the constant presheaf on the target to its ordinary pushforward keeps
the coefficient value on every open set. -/
def rawPushforwardHom :
    presheaf Y A ⟶
      (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).obj (presheaf X A) where
  app _ := 𝟙 A
  naturality _ _ _ := rfl

/-- The canonical sheaf map from the constant sheaf on the target to the pushforward of the
constant sheaf on the source. -/
def pushforwardHom :
    sheaf Y A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj (sheaf X A) where
  hom := CategoryTheory.sheafifyLift (Opens.grothendieckTopology Y)
    (rawPushforwardHom A f ≫
      (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map (unit X A))
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj (sheaf X A)).property

/-- The canonical map intertwines the constant-presheaf sheafification units. -/
theorem unit_pushforwardHom :
    unit Y A ≫ (pushforwardHom A f).hom =
      rawPushforwardHom A f ≫
        (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map (unit X A) :=
  CategoryTheory.toSheafify_sheafifyLift (Opens.grothendieckTopology Y)
    (rawPushforwardHom A f ≫
      (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map (unit X A))
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj (sheaf X A)).property

/-- The canonical map to the pushforward constant sheaf carries the constant section of value
`a` on `U` to the constant section of value `a` on `f ⁻¹' U`. -/
@[simp]
theorem pushforwardHom_app_unit (U : Opens Y) (a : A) :
    (pushforwardHom A f).hom.app (op U) ((unit Y A).app (op U) a) =
      (unit X A).app (op ((Opens.map f).obj U)) a :=
  by
    have h :=
      ConcreteCategory.congr_hom (NatTrans.congr_app (unit_pushforwardHom A f) (op U)) a
    rw [NatTrans.comp_app, NatTrans.comp_app] at h
    change
      (pushforwardHom A f).hom.app (op U) ((unit Y A).app (op U) a) =
        (unit X A).app (op ((Opens.map f).obj U)) a at h
    exact h

private theorem pushforwardHom_app_bijective (U : Opens Y)
    (hU : IsConnected (U : Set Y))
    (hpre : IsConnected (f ⁻¹' (U : Set Y))) :
    Function.Bijective ((pushforwardHom A f).hom.app (op U)) := by
  have hmap : ((Opens.map f).obj U : Set X) = f ⁻¹' (U : Set Y) := rfl
  have hsource := unit_app_bijective Y A U hU
  have htarget := unit_app_bijective X A ((Opens.map f).obj U) (by simpa [hmap] using hpre)
  constructor
  · intro s t hst
    obtain ⟨a, rfl⟩ := hsource.surjective s
    obtain ⟨b, rfl⟩ := hsource.surjective t
    exact congrArg ((unit Y A).app (op U))
      (htarget.injective
        ((pushforwardHom_app_unit A f U a).symm.trans
          (hst.trans (pushforwardHom_app_unit A f U b))))
  · intro t
    obtain ⟨a, rfl⟩ := htarget.surjective t
    exact ⟨(unit Y A).app (op U) a, pushforwardHom_app_unit A f U a⟩

/-- If a basis consists of connected opens with connected inverse images, the canonical map from
the constant sheaf to the pushforward constant sheaf is an isomorphism. -/
theorem pushforwardHom_isIso_of_isBasis {B : Set (Opens Y)}
    (hB : Opens.IsBasis B)
    (hconnected : ∀ U ∈ B, IsConnected (U : Set Y))
    (hpreimage : ∀ U ∈ B, IsConnected (f ⁻¹' (U : Set Y))) :
    IsIso (pushforwardHom A f) := by
  let ι := B
  let basis : ι → Opens Y := fun U ↦ U.1
  have hbasis : Opens.IsBasis (Set.range basis) := by
    simpa [basis] using hB
  apply TopCat.Sheaf.isIso_iff_isIso_basis hbasis
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  exact pushforwardHom_app_bijective A f (basis U)
    (hconnected U.1 U.2) (hpreimage U.1 U.2)

/-- On a locally connected target, connectedness of inverse images of connected opens makes the
canonical map from the constant sheaf to the pushforward constant sheaf an isomorphism. -/
theorem pushforwardHom_isIso [LocallyConnectedSpace Y]
    (hpreimage : ∀ U : Opens Y, IsConnected (U : Set Y) →
      IsConnected (f ⁻¹' (U : Set Y))) :
    IsIso (pushforwardHom A f) := by
  let B : Set (Opens Y) := {U | IsConnected (U : Set Y)}
  apply pushforwardHom_isIso_of_isBasis A f (B := B)
  · rw [Opens.isBasis_iff_nbhd]
    intro U y hy
    obtain ⟨V, ⟨hVopen, hyV, hVconnected⟩, hVU⟩ :=
      (LocallyConnectedSpace.open_connected_basis y).mem_iff.mp (U.2.mem_nhds hy)
    exact ⟨⟨V, hVopen⟩, hVconnected, hyV, hVU⟩
  · intro U hU
    exact hU
  · intro U hU
    exact hpreimage U hU

end TopCat.ConstantSheaf
