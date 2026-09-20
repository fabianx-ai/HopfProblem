/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
-- Reference copy of Mathlib PR fabianx-ai/mathlib4#4 (branch first-hurewicz-structure-v2, commit d9dafd54). Kept verbatim except for import paths.
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Explicit degree-one cycles and homology classes for complexes of modules

Mathlib's `K.homology 1` is defined abstractly, through the homology of the short complex
`K.sc 1`.  This file provides the concrete interface that chain-level arguments need, built
directly on `(K.sc 1).moduleCatLeftHomologyData`:

* degree-one cycles `Cycle1 K` as a submodule of the one-chains, with the surjective class map
  `cycleClass K : ModuleCat.of R (Cycle1 K) ⟶ K.homology 1`, a constructor `mkCycle1` from the
  boundary equation `d₁ z = 0`, and the characterization `cycleClass_eq_zero_iff` of classes
  that vanish;
* one-chains modulo boundaries as the abstract `Opchains K := (K.sc 1).opcycles`, with the
  class map `chainClass`, the boundary criterion `chainClass_eq_iff`, and the injection
  `homologyToChainClass` of homology into it — the workhorse for proving that two homology
  classes are equal;
* the universal property `homologyDesc`: a linear map on cycles that kills boundaries descends
  to homology; and
* functoriality: a chain map sends cycles to cycles (`mapCycles`, via
  `ShortComplex.cyclesMap'`) compatibly with `HomologicalComplex.homologyMap`
  (`cycleClass_comp_homologyMap`).

The degree-one Hurewicz theorem instantiates this interface at `R = ℤ`.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], Section 2.1, the definition of homology as
  cycles modulo boundaries. This file only makes that definition explicit for the degree-one
  term of a chain complex of modules, on top of Mathlib's `moduleCatLeftHomologyData`; no
  theorem is proved here.
-/

@[expose] public noncomputable section

universe v u

namespace AlgebraicTopology.Hurewicz.ChainHomology

open CategoryTheory

variable {R : Type u} [Ring R] (K : ChainComplex (ModuleCat.{v} R) ℕ)

/-! ### Degree-one cycles and their homology classes

The `ComplexShape` bookkeeping (`prev 1 = 2`, `next 1 = 0`) is normalized here once, into the
boundary maps `K.d 2 1` and `K.d 1 0` that a chain-level argument actually manipulates. -/

/-- The degree-one cycles of a chain complex of modules, as a submodule of the one-chains. -/
abbrev Cycle1 : Submodule R (K.X 1) := LinearMap.ker (K.sc 1).g.hom

/-- The incoming map of the degree-one short complex has the same range as `K.d 2 1`. -/
lemma range_sc_one_f : LinearMap.range (K.sc 1).f.hom = LinearMap.range (K.d 2 1).hom := by
  change LinearMap.range (K.d ((ComplexShape.down ℕ).prev 1) 1).hom = _
  have hp : (ComplexShape.down ℕ).prev 1 = 2 := (ComplexShape.down ℕ).prev_eq' (by simp)
  rw [hp]

/-- The homology class of a degree-one cycle. -/
def cycleClass : ModuleCat.of R (Cycle1 K) ⟶ K.homology 1 :=
  (K.sc 1).moduleCatLeftHomologyData.π ≫ (K.sc 1).moduleCatHomologyIso.inv

/-- Every degree-one homology class is the class of a cycle. -/
lemma cycleClass_surjective : Function.Surjective (cycleClass K) :=
  ((ModuleCat.epi_iff_surjective (K.sc 1).moduleCatHomologyIso.inv).mp inferInstance).comp
    (Submodule.mkQ_surjective _)

/-- The class map from cycles to homology is an epimorphism: the categorical form of
`cycleClass_surjective`. -/
instance : Epi (cycleClass K) := (ModuleCat.epi_iff_surjective _).mpr (cycleClass_surjective K)

/-- To prove a statement about all degree-one homology classes, it suffices to prove it for
classes of cycles. -/
@[elab_as_elim]
lemma cycleClass_induction_on {motive : K.homology 1 → Prop} (x : K.homology 1)
    (h : ∀ c : Cycle1 K, motive (cycleClass K c)) : motive x := by
  obtain ⟨c, rfl⟩ := cycleClass_surjective K x
  exact h c

/-- Build a degree-one cycle from a one-chain killed by the boundary map `K.d 1 0`. -/
def mkCycle1 (z : K.X 1) (hz : (K.d 1 0).hom z = 0) : Cycle1 K :=
  ⟨z, by
    change (K.d 1 ((ComplexShape.down ℕ).next 1)).hom z = 0
    have hn : (ComplexShape.down ℕ).next 1 = 0 := (ComplexShape.down ℕ).next_eq' (by simp)
    rw [hn]
    exact hz⟩

/-- A degree-one cycle has trivial homology class exactly when it is the boundary of a
two-chain. -/
lemma cycleClass_eq_zero_iff (c : Cycle1 K) :
    cycleClass K c = 0 ↔ ∃ b : K.X 2, (K.d 2 1).hom b = c.1 := by
  have hinj : Function.Injective (K.sc 1).moduleCatHomologyIso.inv :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hiff : cycleClass K c = 0 ↔ c ∈ LinearMap.range (K.sc 1).moduleCatToCycles := by
    have hπ : cycleClass K c = 0 ↔ (K.sc 1).moduleCatLeftHomologyData.π c = 0 :=
      ⟨fun h => hinj (h.trans (map_zero _).symm),
        fun h => by
          change (K.sc 1).moduleCatHomologyIso.inv ((K.sc 1).moduleCatLeftHomologyData.π c) = 0
          rw [h, map_zero]⟩
    rw [hπ]
    exact Submodule.Quotient.mk_eq_zero _
  rw [hiff]
  constructor
  · rintro ⟨b, hb⟩
    have hmem : c.1 ∈ LinearMap.range (K.d 2 1).hom := by
      rw [← range_sc_one_f]
      exact ⟨b, congrArg Subtype.val hb⟩
    exact hmem
  · rintro ⟨b, hb⟩
    have hmem : c.1 ∈ LinearMap.range (K.sc 1).f.hom := by
      rw [range_sc_one_f]
      exact ⟨b, hb⟩
    obtain ⟨b', hb'⟩ := hmem
    exact ⟨b', Subtype.ext hb'⟩

/-- The boundary of a two-chain, as a degree-one cycle. -/
def boundaryCycle1 (b : K.X 2) : Cycle1 K :=
  mkCycle1 K ((K.d 2 1).hom b) congr($(K.d_comp_d 2 1 0) b)

/-! ### One-chains modulo boundaries

Homology injects into the opcycles of the degree-one short complex — one-chains modulo
boundaries.  The Hurewicz argument proves equalities in `H₁` by exhibiting an explicit
two-chain whose boundary is the difference of the representatives. -/

/-- The one-chains of a chain complex of modules, modulo boundaries of two-chains: the
opcycles of the degree-one short complex. -/
abbrev Opchains : ModuleCat R := (K.sc 1).opcycles

/-- The class of a one-chain modulo boundaries. -/
def chainClass : K.X 1 ⟶ Opchains K := (K.sc 1).pOpcycles

/-- Boundaries of two-chains vanish modulo boundaries. -/
@[simp]
lemma chainClass_boundary (b : K.X 2) : chainClass K ((K.d 2 1).hom b) = 0 :=
  ((K.sc 1).moduleCat_pOpcycles_eq_zero_iff _).mpr (by rw [range_sc_one_f]; exact ⟨b, rfl⟩)

/-- Two one-chains agree modulo boundaries exactly when their difference is the boundary of a
two-chain. -/
lemma chainClass_eq_iff (x y : K.X 1) :
    chainClass K x = chainClass K y ↔ ∃ b : K.X 2, (K.d 2 1).hom b = x - y := by
  refine ((K.sc 1).moduleCat_pOpcycles_eq_iff x y).trans ?_
  rw [range_sc_one_f]
  exact ⟨fun ⟨b, hb⟩ => ⟨b, hb⟩, fun ⟨b, hb⟩ => ⟨b, hb⟩⟩

/-- The canonical injection of degree-one homology into one-chains modulo boundaries. -/
def homologyToChainClass : K.homology 1 ⟶ Opchains K := (K.sc 1).homologyι

/-- Degree-one homology injects into one-chains modulo boundaries: to prove two homology
classes equal, it suffices to compare representatives modulo boundaries. -/
lemma homologyToChainClass_injective : Function.Injective (homologyToChainClass K) :=
  (ModuleCat.mono_iff_injective (K.sc 1).homologyι).mp inferInstance

/-- The `moduleCatHomologyIso` inverse intertwines the two presentations of a homology
class: `π ≫ iso.inv ≫ homologyι = i ≫ pOpcycles`. -/
private lemma pi_homologyIso_inv_homologyi (S : ShortComplex (ModuleCat.{v} R)) :
    S.moduleCatLeftHomologyData.π ≫ S.moduleCatHomologyIso.inv ≫ S.homologyι =
      S.moduleCatLeftHomologyData.i ≫ S.pOpcycles := by
  rw [← S.moduleCatCyclesIso_inv_π_assoc, S.homology_π_ι, S.moduleCatCyclesIso_inv_iCycles_assoc]

/-- Taking the homology class of a cycle and then its image in one-chains modulo boundaries
is the same as forgetting that the cycle is a cycle and taking its class modulo boundaries:
the square formed by `cycleClass`, `homologyToChainClass`, and `chainClass` commutes. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma cycleClass_comp_homologyToChainClass :
    cycleClass K ≫ homologyToChainClass K =
      (K.sc 1).moduleCatLeftHomologyData.i ≫ chainClass K :=
  (Category.assoc _ _ _).trans (pi_homologyIso_inv_homologyi (K.sc 1))

/-- `homologyToChainClass` sends the class of a cycle to the class of its underlying
one-chain.  (The simp normal form is the `elementwise` companion of
`cycleClass_comp_homologyToChainClass`.) -/
lemma homologyToChainClass_cycleClass (c : Cycle1 K) :
    homologyToChainClass K (cycleClass K c) = chainClass K c.1 :=
  congr($(cycleClass_comp_homologyToChainClass K) c)

/-! ### The universal property

A linear map defined on cycles that kills boundaries descends to degree-one homology. -/

/-- A linear map on degree-one cycles killing all boundaries vanishes on the range of the
canonical map from the previous chain object. -/
lemma range_toCycles_le_ker {M : Type v} [AddCommGroup M] [Module R M]
    (f : Cycle1 K →ₗ[R] M) (hf : ∀ b : K.X 2, f (boundaryCycle1 K b) = 0) :
    LinearMap.range (K.sc 1).moduleCatToCycles ≤ LinearMap.ker f := by
  rintro c ⟨b, hb⟩
  have hc : cycleClass K c = 0 :=
    (cycleClass_eq_zero_iff K c).mpr (by
      have : c.1 ∈ LinearMap.range (K.d 2 1).hom := by
        rw [← range_sc_one_f]
        exact ⟨b, congrArg Subtype.val hb⟩
      exact this)
  obtain ⟨b', hb'⟩ := (cycleClass_eq_zero_iff K c).mp hc
  have he : boundaryCycle1 K b' = c := Subtype.ext hb'
  exact he ▸ hf b'

/-- Composing the canonical map to cycles with a linear map that kills boundaries gives
zero — the hypothesis `descH` needs. -/
lemma f'_comp_ofHom_eq_zero {M : Type v} [AddCommGroup M] [Module R M]
    (f : Cycle1 K →ₗ[R] M) (hf : ∀ b : K.X 2, f (boundaryCycle1 K b) = 0) :
    (K.sc 1).moduleCatLeftHomologyData.f' ≫ ModuleCat.ofHom f = 0 := by
  ext x
  exact range_toCycles_le_ker K f hf ⟨x, rfl⟩

/-- Descend a linear map on degree-one cycles that kills boundaries to a map on homology. -/
def homologyDesc {M : Type v} [AddCommGroup M] [Module R M] (f : Cycle1 K →ₗ[R] M)
    (hf : ∀ b : K.X 2, f (boundaryCycle1 K b) = 0) : K.homology 1 →ₗ[R] M :=
  (((K.sc 1).moduleCatHomologyIso.hom ≫
    (K.sc 1).moduleCatLeftHomologyData.descH (ModuleCat.ofHom f)
      (f'_comp_ofHom_eq_zero K f hf) :
    K.homology 1 ⟶ ModuleCat.of R M)).hom

/-- The descended map agrees with the original map on classes of cycles. -/
@[simp]
lemma homologyDesc_cycleClass {M : Type v} [AddCommGroup M] [Module R M] (f : Cycle1 K →ₗ[R] M)
    (hf : ∀ b : K.X 2, f (boundaryCycle1 K b) = 0) (c : Cycle1 K) :
    homologyDesc K f hf (cycleClass K c) = f c := by
  change ((K.sc 1).moduleCatLeftHomologyData.descH (ModuleCat.ofHom f)
      (f'_comp_ofHom_eq_zero K f hf))
    ((K.sc 1).moduleCatHomologyIso.hom
      ((K.sc 1).moduleCatHomologyIso.inv ((K.sc 1).moduleCatLeftHomologyData.π c))) = f c
  rw [(K.sc 1).moduleCatHomologyIso.inv_hom_id_apply]
  exact congr($((K.sc 1).moduleCatLeftHomologyData.π_descH (ModuleCat.ofHom f)
    (f'_comp_ofHom_eq_zero K f hf)) c)

/-! ### Functoriality

A chain map sends degree-one cycles to degree-one cycles, compatibly with the induced map on
homology.  The map on cycles is `ShortComplex.cyclesMap'` at the concrete left homology
data. -/

variable {K} {L : ChainComplex (ModuleCat.{v} R) ℕ} (F : K ⟶ L)

/-- The morphism of degree-one short complexes induced by a chain map. -/
abbrev shortMap : K.sc 1 ⟶ L.sc 1 :=
  (HomologicalComplex.shortComplexFunctor (ModuleCat.{v} R) (ComplexShape.down ℕ) 1).map F

/-- The map on degree-one cycles induced by a chain map. -/
def mapCycles : ModuleCat.of R (Cycle1 K) ⟶ ModuleCat.of R (Cycle1 L) :=
  ShortComplex.cyclesMap' (shortMap F) (K.sc 1).moduleCatLeftHomologyData
    (L.sc 1).moduleCatLeftHomologyData

/-- The map on cycles induced by a chain map acts on underlying one-chains as the chain map
itself. -/
@[simp]
lemma mapCycles_val (c : Cycle1 K) : (mapCycles F c).1 = (F.f 1).hom c.1 :=
  congr($(ShortComplex.cyclesMap'_i (shortMap F) (K.sc 1).moduleCatLeftHomologyData
    (L.sc 1).moduleCatLeftHomologyData) c)

/-- Naturality of `π ≫ moduleCatHomologyIso.inv` across a short-complex map. -/
private lemma pi_homologyIso_inv_naturality {S₁ S₂ : ShortComplex (ModuleCat.{v} R)}
    (φ : S₁ ⟶ S₂) :
    (S₁.moduleCatLeftHomologyData.π ≫ S₁.moduleCatHomologyIso.inv) ≫
        ShortComplex.homologyMap φ =
      ShortComplex.cyclesMap' φ S₁.moduleCatLeftHomologyData S₂.moduleCatLeftHomologyData ≫
        S₂.moduleCatLeftHomologyData.π ≫ S₂.moduleCatHomologyIso.inv := by
  dsimp only [ShortComplex.moduleCatHomologyIso]
  simp only [Category.assoc]
  rw [← ShortComplex.leftHomologyπ_naturality'_assoc φ]
  congr 1
  rw [Iso.inv_comp_eq, ← Category.assoc,
    ShortComplex.LeftHomologyData.leftHomologyIso_hom_naturality φ, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- The induced map on homology sends the class of a cycle to the class of its image. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma cycleClass_comp_homologyMap :
    cycleClass K ≫ HomologicalComplex.homologyMap F 1 = mapCycles F ≫ cycleClass L :=
  pi_homologyIso_inv_naturality (shortMap F)

/-- Element form of `cycleClass_comp_homologyMap`. -/
lemma homologyMap_cycleClass (c : Cycle1 K) :
    (HomologicalComplex.homologyMap F 1).hom (cycleClass K c) = cycleClass L (mapCycles F c) :=
  congr($(cycleClass_comp_homologyMap F) c)

end AlgebraicTopology.Hurewicz.ChainHomology
