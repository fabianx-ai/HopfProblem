/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.Relative.Support
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.SmallSimplices

/-!
# Excision

For open sets `U, V ⊆ X` covering `X`, the inclusion of pairs `(V, V ∩ U) → (X, U)` induces
isomorphisms on relative homology (Hatcher, *Algebraic Topology*, Theorem 2.20, in the form of
its open-cover case: `Z = X ∖ V`, `A = U`, `cl Z ⊆ int A`):

* `RelativeSingularHomology.excisionEquiv U V hU hV hcover n :
    RelativeHomology V (trace U V) n ≃ₗ[ℤ] RelativeHomology X U n`,

realized by `relativeHomologyMap (subtypeInclusion V)`.

## Outline of the proof

Hatcher's proof, with the chain complexes of `Lib/Algebra/Homology/ChainSubmodule.lean`:

1. *Chains of `V` relative to `V ∩ U`, inside `X`.*  The chain isomorphism `supportedComplexIso V`
   identifies `C(V)` with the chains of `X` supported in `V`, and under it the chains of `V`
   supported in `V ∩ U` are the chains of `X` supported in `U` (`inducedChain_mem_supported_iff`),
   so `C(V, V ∩ U) ≅ supported V / (supported U ⊓ supported V)` (`toRelative`, an isomorphism of
   complexes by `toRelative_f_bijective`).
2. *The second isomorphism theorem.*  `supported V / (supported U ⊓ supported V) ≅
   (supported U ⊔ supported V) / supported U` (`ChainSubmodule.relativeSupIso`); the numerator is
   the complex of `(U, V)`-small chains `C^{U,V}(X)`.
3. *Small chains.*  `C^{U,V}(X) → C(X)` is a quasi-isomorphism (`smallInclusion_quasiIso`, Hatcher,
   Proposition 2.21), so by the five lemma `C^{U,V}(X)/C(U) → C(X)/C(U)` is one
   (`ChainSubmodule.relativeToQuotient_quasiIso`).
4. The composite of the three is the chain map of the inclusion of pairs
   (`excisionChainMap_eq`), hence a quasi-isomorphism (`excision_quasiIso`), hence bijective on
   homology (`excision_bijective`).

## Main definitions and results

* `RelativeSingularHomology.excision_quasiIso`, `RelativeSingularHomology.excision_bijective`,
  `RelativeSingularHomology.excisionEquiv` : **excision** for an open cover.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], Theorem 2.20 and Proposition 2.21

## Tags

excision, relative homology, small chains
-/

open Set Function CategoryTheory

@[expose] public noncomputable section

namespace RelativeSingularHomology

open SingularChains SingularMayerVietoris

variable {X : Type} [TopologicalSpace X]

/-! ### Chains of a subspace relative to a subset, inside the ambient space -/

/-- The trace `U ∩ V` of `U` on the subspace `V`, as a subset of `V`.  (A definition rather than
`Subtype.val ⁻¹' U`, so that the relative complexes of the pair `(V, U ∩ V)` are stated with one
fixed term.) -/
def trace (U V : Set X) : Set V := Subtype.val ⁻¹' U

omit [TopologicalSpace X] in
@[simp]
theorem mem_trace (U V : Set X) (v : V) : v ∈ trace U V ↔ (v : X) ∈ U := Iff.rfl

/-- The subspace inclusion `V → X` is a map of pairs `(V, U ∩ V) → (X, U)`. -/
theorem mapsTo_subtypeInclusion_trace (U V : Set X) : MapsTo (subtypeInclusion V) (trace U V) U :=
  fun _ hv => hv

/-- The chains of `X` supported in `U ∩ V` are the images of the chains of `V` supported in the
preimage of `U`. -/
theorem supportedChainSubmodule_inter_eq_map (U V : Set X) (n : ℕ) :
    supportedChainSubmodule (U ∩ V) n =
      (supportedChainSubmodule (trace U V) n).map (inducedChain (subtypeInclusion V) n) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨σ, hσ, rfl⟩
    have hV : Set.range σ ⊆ V := hσ.trans inter_subset_right
    refine ⟨simplexChain V n (restrictSimplex V n σ hV), ?_, ?_⟩
    · apply simplexChain_mem_supported
      rintro _ ⟨s, rfl⟩
      exact (hσ ⟨s, rfl⟩).1
    · rw [inducedChain_simplex, subtypeInclusion_comp_restrictSimplex]
  · rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro _ ⟨σ, hσ, rfl⟩
    change inducedChain (subtypeInclusion V) n (simplexChain V n σ) ∈ supportedChainSubmodule (U ∩ V) n
    rw [inducedChain_simplex]
    apply simplexChain_mem_supported
    rintro _ ⟨s, rfl⟩
    exact ⟨hσ ⟨s, rfl⟩, (σ s).2⟩

/-- A chain of `V` is supported in the preimage of `U` exactly when its image in `X` is supported
in `U`. -/
theorem inducedChain_mem_supported_iff (U V : Set X) (n : ℕ) (c : Chains V n) :
    inducedChain (subtypeInclusion V) n c ∈ supportedChainSubmodule U n ↔
      c ∈ supportedChainSubmodule (trace U V) n := by
  constructor
  · intro hc
    have hUV : inducedChain (subtypeInclusion V) n c ∈ supportedChainSubmodule (U ∩ V) n := by
      rw [← supportedChainSubmodule_inf]
      exact ⟨hc, subtypeInclusion_chain_mem V n c⟩
    rw [supportedChainSubmodule_inter_eq_map] at hUV
    obtain ⟨c', hc', hcc'⟩ := hUV
    rw [subtypeInclusion_chain_injective V n hcc'] at hc'
    exact hc'
  · intro hc
    exact inducedChain_mem_supported_of_mapsTo _ (mapsTo_subtypeInclusion_trace U V) n c hc

/-- The chain map `C(V, V ∩ U) ⟶ supported V / (supported U ⊓ supported V)`. -/
def toRelative (U V : Set X) :
    relativeComplex V (trace U V) ⟶
      ChainSubmodule.relativeComplex (supportedSubmodule V) (supportedSubmodule U) where
  f n := ModuleCat.ofHom (Submodule.mapQ _ _ ((toSupported V).f n).hom
    (fun c hc => (inducedChain_mem_supported_iff U V n c).mpr hc))
  comm' i j _ := ChainSubmodule.quotient_hom_ext fun c => by
    change (Submodule.Quotient.mk ((supportedSubmodule V).subDifferential i j (((toSupported V).f i).hom c)) :
        (supportedSubmodule V).carrier j ⧸
          ChainSubmodule.relativeSubmodule (supportedSubmodule V) (supportedSubmodule U) j) =
      Submodule.Quotient.mk (((toSupported V).f j).hom (((singularComplex V).d i j).hom c))
    congr 1
    apply Subtype.ext
    exact congrArg (fun g : Chains V i ⟶ Chains X j => g.hom c)
      ((singularChainMap (subtypeInclusion V)).comm i j)

@[simp]
theorem toRelative_f_relativeClass (U V : Set X) (n : ℕ) (c : Chains V n) :
    ((toRelative U V).f n).hom (relativeClass (trace U V) n c) =
      ((ChainSubmodule.relativeProjection (supportedSubmodule V) (supportedSubmodule U)).f n).hom
        (((toSupported V).f n).hom c) :=
  rfl

/-- `toRelative` is bijective in every degree. -/
theorem toRelative_f_bijective (U V : Set X) (n : ℕ) :
    Function.Bijective ((toRelative U V).f n).hom := by
  constructor
  · intro a b hab
    induction a using Submodule.Quotient.induction_on with
    | H a =>
    induction b using Submodule.Quotient.induction_on with
    | H b =>
    have hab' : (Submodule.Quotient.mk (((toSupported V).f n).hom a) :
        (supportedSubmodule V).carrier n ⧸ _) = Submodule.Quotient.mk (((toSupported V).f n).hom b) :=
      hab
    rw [Submodule.Quotient.eq] at hab' ⊢
    rw [← map_sub] at hab'
    exact (inducedChain_mem_supported_iff U V n (a - b)).mp hab'
  · intro c
    induction c using Submodule.Quotient.induction_on with
    | H c =>
    obtain ⟨a, ha⟩ := (toSupported_f_bijective V n).2 c
    refine ⟨relativeClass (trace U V) n a, ?_⟩
    rw [toRelative_f_relativeClass, ha]
    rfl

instance toRelative_f_isIso (U V : Set X) (n : ℕ) : IsIso ((toRelative U V).f n) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (toRelative_f_bijective U V n)

instance toRelative_isIso (U V : Set X) : IsIso (toRelative U V) :=
  HomologicalComplex.Hom.isIso_of_components _

/-! ### The small chains as a subcomplex -/

/-- The complex of `(U, V)`-small chains is the subcomplex of the chain submodule
`supported U ⊔ supported V`. -/
def smallComplexIso (U V : Set X) :
    smallComplex U V ≅ (supportedSubmodule U ⊔ supportedSubmodule V).subComplex :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (fun _ _ _ => rfl)

/-- The small-chain inclusion is the inclusion of the chain submodule `supported U ⊔ supported V`. -/
theorem smallInclusion_eq (U V : Set X) :
    smallInclusion U V = (smallComplexIso U V).hom ≫ ChainSubmodule.ι (supportedSubmodule U ⊔ supportedSubmodule V) :=
  HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

/-- The inclusion of the chain submodule `supported U ⊔ supported V` is a quasi-isomorphism for an
open cover (the small simplices theorem, Hatcher, Proposition 2.21). -/
theorem smallInclusion_quasiIso_sup (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) :
    QuasiIso (ChainSubmodule.ι (supportedSubmodule U ⊔ supportedSubmodule V)) := by
  have h := smallInclusion_quasiIso U V hU hV hcover
  rw [smallInclusion_eq] at h
  exact (quasiIso_iff_comp_left (smallComplexIso U V).hom _).mp h

/-! ### Excision -/

/-- The chain map of the inclusion of pairs `(V, V ∩ U) → (X, U)` factors through the relative
complexes inside `X`. -/
theorem excisionChainMap_eq (U V : Set X) :
    relativeChainMap (subtypeInclusion V) (mapsTo_subtypeInclusion_trace U V) =
      toRelative U V ≫ (ChainSubmodule.relativeSupIso (supportedSubmodule V) (supportedSubmodule U)).hom ≫
        ChainSubmodule.relativeToQuotient (supportedSubmodule U ⊔ supportedSubmodule V)
          (supportedSubmodule U) :=
  ChainSubmodule.quotientComplex_hom_ext fun _ _ => rfl

/-- **Excision**: for an open cover `U ∪ V = X`, the inclusion of pairs `(V, V ∩ U) → (X, U)` is a
quasi-isomorphism on relative chains. -/
theorem excision_quasiIso (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) :
    QuasiIso (relativeChainMap (subtypeInclusion V) (mapsTo_subtypeInclusion_trace U V)) := by
  rw [excisionChainMap_eq]
  have := smallInclusion_quasiIso_sup U V hU hV hcover
  have := ChainSubmodule.relativeToQuotient_quasiIso
    (ChainSubmodule.le_sup_left (supportedSubmodule U) (supportedSubmodule V))
  infer_instance

/-- **Excision**: `H_n(V, V ∩ U) → H_n(X, U)` is bijective for an open cover `U ∪ V = X`. -/
theorem excision_bijective (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) :
    Function.Bijective
      (relativeHomologyMap (subtypeInclusion V) (mapsTo_subtypeInclusion_trace U V) n) :=
  letI := excision_quasiIso U V hU hV hcover
  bijective_of_quasiIso _ n

/-- **Excision** (Hatcher, Theorem 2.20): for open `U, V` with `U ∪ V = X`, the inclusion of pairs
`(V, V ∩ U) → (X, U)` induces `H_n(V, V ∩ U) ≅ H_n(X, U)`. -/
def excisionEquiv (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (n : ℕ) : RelativeHomology V (trace U V) n ≃ₗ[ℤ] RelativeHomology X U n :=
  LinearEquiv.ofBijective (relativeHomologyMap (subtypeInclusion V) (mapsTo_subtypeInclusion_trace U V) n)
    (excision_bijective U V hU hV hcover n)

@[simp]
theorem excisionEquiv_apply (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (n : ℕ) (a : RelativeHomology V (trace U V) n) :
    excisionEquiv U V hU hV hcover n a =
      relativeHomologyMap (subtypeInclusion V) (mapsTo_subtypeInclusion_trace U V) n a :=
  rfl

end RelativeSingularHomology
