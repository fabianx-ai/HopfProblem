/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Algebra.Homology.ChainSubmodule
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.SingularHomology
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.SmallChains

/-!
# Relative singular homology

For a space `X` and a subset `A ⊆ X`, the relative singular chain complex is the quotient
`C_n(X, A) = C_n(X) / C_n(A)` of the singular chains of `X` by the chains supported in `A`
(Hatcher, *Algebraic Topology*, §2.1, "Relative homology groups"), and the relative homology
`H_n(X, A)` is its homology:

* `RelativeSingularHomology.relativeComplex X A : ChainComplex (ModuleCat ℤ) ℕ`;
* `RelativeSingularHomology.RelativeHomology X A n := (relativeComplex X A).homology n`.

The chains supported in `A` are `SingularMayerVietoris.supportedChainSubmodule A n`, a subcomplex
(`boundary_mem_supported`) isomorphic to the singular chain complex of the subspace `A`
(`supportedComplexIso`, from `subtypeInclusion_chain_injective` and `subtypeInclusion_chain_range`).
The short exact sequence `0 → C(A) → C(X) → C(X, A) → 0` is `pairSequence X A`, short exact by
`pairSequence_shortExact`, and the long exact sequence of the pair follows from
`Lib/AlgebraicTopology/SingularHomology/MayerVietoris/HomologyLongExact.lean`:
`pairConnecting X A n : H_{n+1}(X, A) → H_n(A)` with exactness at the three terms
(`pair_exact_at_subspace`, `pair_exact_at_space`, `pair_exact_at_pair`).  The two degenerate
pairs are identified: `relativeHomologyEquivOfEmpty : H_n(X, ∅) ≃ H_n(X)` and
`relativeHomology_subsingleton_of_univ : H_n(X, X) = 0`.

## Outline

1. *Supported chains form a subcomplex.*  `boundary_mem_supported`, `supportedSubmodule U :
   ChainSubmodule (singularComplex X)`, `supportedComplex U`, and the identification with the
   subspace complex `supportedComplexIso U`.
2. *The relative complex.*  `relativeComplex X A` is the quotient complex of `supportedSubmodule A`;
   `relativeProjection X A : C(X) ⟶ C(X, A)`; `subspaceInclusion X A : C(A) ⟶ C(X)`.
3. *The long exact sequence.*  `pairSequence`, `pairSequence_shortExact`, `pairConnecting`, the
   exactness statements, and the degree-zero surjectivity.
4. *Degenerate pairs.*  `supportedChainSubmodule_empty`, `supportedChainSubmodule_univ`,
   `relativeHomologyEquivOfEmpty`, `relativeHomology_subsingleton_of_univ`.
5. *Restriction.*  `restriction (h : A ⊆ A') n : H_n(X, A) → H_n(X, A')` from
   `supportedChainSubmodule_mono`.

## Main definitions and results

* `RelativeSingularHomology.relativeComplex`, `RelativeSingularHomology.RelativeHomology` : the
  relative chain complex and relative homology.
* `RelativeSingularHomology.pairSequence_shortExact`, `RelativeSingularHomology.pairConnecting`,
  `RelativeSingularHomology.pair_exact_at_*` : the long exact sequence of the pair.
* `RelativeSingularHomology.relativeHomologyEquivOfEmpty`,
  `RelativeSingularHomology.relativeHomology_subsingleton_of_univ`.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §2.1, Relative homology groups

## Tags

relative homology, pair, long exact sequence
-/

open Set Function CategoryTheory

@[expose] public noncomputable section

namespace RelativeSingularHomology

open SingularChains SingularMayerVietoris

variable {X : Type} [TopologicalSpace X]

/-! ### Supported chains form a subcomplex -/

/-- The boundary of a chain supported in `U` is supported in `U`. -/
theorem boundary_mem_supported (U : Set X) (n : ℕ) (c : Chains X (n + 1))
    (hc : c ∈ supportedChainSubmodule U (n + 1)) :
    ((singularComplex X).d (n + 1) n).hom c ∈ supportedChainSubmodule U n := by
  have hle : supportedChainSubmodule U (n + 1) ≤
      (supportedChainSubmodule U n).comap ((singularComplex X).d (n + 1) n).hom := by
    apply Submodule.span_le.mpr
    rintro _ ⟨σ, hσ, rfl⟩
    change (singularComplex X).d (n + 1) n (simplexChain X (n + 1) σ) ∈ supportedChainSubmodule U n
    rw [boundary_simplex]
    apply Submodule.sum_mem
    intro i _
    apply (supportedChainSubmodule U n).toAddSubgroup.zsmul_mem
    exact simplexChain_mem_supported U n _ (simplex_face_supported U n σ hσ i)
  exact hle hc

/-- Supported chains are monotone in the set. -/
theorem supportedChainSubmodule_mono {U V : Set X} (h : U ⊆ V) (n : ℕ) :
    supportedChainSubmodule U n ≤ supportedChainSubmodule V n :=
  Submodule.span_mono (Set.image_mono fun _ hσ => hσ.trans h)

/-- The chains supported in `U`, as a chain submodule of the singular chain complex. -/
def supportedSubmodule (U : Set X) : ChainSubmodule (singularComplex X) :=
  ChainSubmodule.mk' (fun n => supportedChainSubmodule U n) (fun n _ hc =>
    boundary_mem_supported U n _ hc)

@[simp]
theorem supportedSubmodule_carrier (U : Set X) (n : ℕ) :
    (supportedSubmodule U).carrier n = supportedChainSubmodule U n := rfl

theorem supportedSubmodule_mono {U V : Set X} (h : U ⊆ V) :
    supportedSubmodule U ≤ supportedSubmodule V :=
  fun n => supportedChainSubmodule_mono h n

/-- The subcomplex of chains supported in `U`. -/
abbrev supportedComplex (U : Set X) : ChainComplex (ModuleCat ℤ) ℕ :=
  (supportedSubmodule U).subComplex

/-- The subtype chain map, with codomain the supported chains. -/
def toSupported (U : Set X) : singularComplex U ⟶ supportedComplex U where
  f n := ModuleCat.ofHom ((inducedChain (subtypeInclusion U) n).codRestrict
    (supportedChainSubmodule U n) (subtypeInclusion_chain_mem U n))
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact congrArg (fun g : Chains U i ⟶ Chains X j => g.hom c)
      ((singularChainMap (subtypeInclusion U)).comm i j)

@[simp]
theorem toSupported_f_apply_coe (U : Set X) (n : ℕ) (c : Chains U n) :
    (((toSupported U).f n).hom c : Chains X n) = inducedChain (subtypeInclusion U) n c := rfl

@[simp]
theorem toSupported_ι (U : Set X) :
    toSupported U ≫ (supportedSubmodule U).ι = singularChainMap (subtypeInclusion U) :=
  HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

theorem toSupported_f_bijective (U : Set X) (n : ℕ) : Function.Bijective ((toSupported U).f n).hom := by
  constructor
  · intro a b hab
    exact subtypeInclusion_chain_injective U n (congrArg Subtype.val hab :)
  · intro c
    have hc : (c : Chains X n) ∈ LinearMap.range (inducedChain (subtypeInclusion U) n) := by
      rw [subtypeInclusion_chain_range]
      exact c.2
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp hc
    exact ⟨a, Subtype.ext ha⟩

/-- The singular chain complex of the subspace `U` is isomorphic to the complex of chains of `X`
supported in `U`. -/
def supportedComplexIso (U : Set X) : singularComplex U ≅ supportedComplex U :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (LinearEquiv.ofBijective _ (toSupported_f_bijective U n)).toModuleIso)
    (fun i j _ => (toSupported U).comm i j)

@[simp]
theorem supportedComplexIso_hom (U : Set X) : (supportedComplexIso U).hom = toSupported U := rfl

/-! ### The relative complex -/

/-- The relative singular chain complex `C(X, A) = C(X) / C(A)` (Hatcher, Algebraic Topology, §2.1). -/
abbrev relativeComplex (X : Type) [TopologicalSpace X] (A : Set X) : ChainComplex (ModuleCat ℤ) ℕ :=
  (supportedSubmodule A).quotientComplex

/-- The relative singular homology `H_n(X, A)` with integer coefficients (Hatcher, Algebraic Topology, §2.1). -/
abbrev RelativeHomology (X : Type) [TopologicalSpace X] (A : Set X) (n : ℕ) :=
  (relativeComplex X A).homology n

/-- The projection from chains of `X` to relative chains. -/
abbrev relativeProjection (X : Type) [TopologicalSpace X] (A : Set X) :
    singularComplex X ⟶ relativeComplex X A :=
  (supportedSubmodule A).π

/-- The chain map of the subspace inclusion `A → X`. -/
abbrev subspaceInclusion (X : Type) [TopologicalSpace X] (A : Set X) :
    singularComplex A ⟶ singularComplex X :=
  singularChainMap (subtypeInclusion A)

/-- The class of a chain in the relative chain group. -/
abbrev relativeClass (A : Set X) (n : ℕ) (c : Chains X n) : (relativeComplex X A).X n :=
  Submodule.Quotient.mk c

theorem relativeClass_eq_zero_iff (A : Set X) (n : ℕ) (c : Chains X n) :
    relativeClass A n c = 0 ↔ c ∈ supportedChainSubmodule A n :=
  Submodule.Quotient.mk_eq_zero _

theorem relativeProjection_f_apply (A : Set X) (n : ℕ) (c : Chains X n) :
    ((relativeProjection X A).f n).hom c = relativeClass A n c := rfl

theorem relativeComplex_d_relativeClass (A : Set X) (i j : ℕ) (c : Chains X i) :
    ((relativeComplex X A).d i j).hom (relativeClass A i c) =
      relativeClass A j (((singularComplex X).d i j).hom c) :=
  ChainSubmodule.quotientDifferential_mk _ i j c

/-- The homology map of the subspace inclusion. -/
abbrev subspaceHomologyMap (A : Set X) (n : ℕ) : SingularHomology A n →ₗ[ℤ] SingularHomology X n :=
  singularHomologyMap (subtypeInclusion A) n

/-- The homology map of the relative projection. -/
abbrev relativeProjectionHomologyMap (A : Set X) (n : ℕ) :
    SingularHomology X n →ₗ[ℤ] RelativeHomology X A n :=
  homologyLinearMap (relativeProjection X A) n

/-! ### The long exact sequence of the pair -/

/-- The short complex `C(A) → C(X) → C(X, A)`. -/
def pairSequence (X : Type) [TopologicalSpace X] (A : Set X) :
    ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (subspaceInclusion X A) (relativeProjection X A)
    (HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext (LinearMap.ext fun c =>
      (Submodule.Quotient.mk_eq_zero (supportedChainSubmodule A n)).mpr
        (subtypeInclusion_chain_mem A n c)))

/-- The sequence `0 → C(A) → C(X) → C(X, A) → 0` is short exact. -/
theorem pairSequence_shortExact (A : Set X) : (pairSequence X A).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  apply ModuleCat.shortComplex_shortExact
  · intro c
    constructor
    · intro hc
      have hc' : ∃ a, inducedChain (subtypeInclusion A) n a = (c : Chains X n) := by
        apply LinearMap.mem_range.mp
        rw [subtypeInclusion_chain_range]
        exact (Submodule.Quotient.mk_eq_zero (supportedChainSubmodule A n)).mp hc
      exact hc'
    · rintro ⟨a, rfl⟩
      exact (Submodule.Quotient.mk_eq_zero (supportedChainSubmodule A n)).mpr
        (subtypeInclusion_chain_mem A n a)
  · exact subtypeInclusion_chain_injective A n
  · exact Submodule.Quotient.mk_surjective (supportedChainSubmodule A n)

/-- The connecting homomorphism `H_{n+1}(X, A) → H_n(A)` of the pair. -/
abbrev pairConnecting (X : Type) [TopologicalSpace X] (A : Set X) (n : ℕ) :
    RelativeHomology X A (n + 1) →ₗ[ℤ] SingularHomology A n :=
  connectingMap (pairSequence_shortExact A) n

/-- Exactness at `H_n(A)`: the image of the connecting map is the kernel of `H_n(A) → H_n(X)`. -/
theorem pair_exact_at_subspace (A : Set X) (n : ℕ) :
    LinearMap.range (pairConnecting X A n) = LinearMap.ker (subspaceHomologyMap A n) :=
  exact_at_leftHomology (pairSequence_shortExact A) n

/-- Exactness at `H_n(X)`. -/
theorem pair_exact_at_space (A : Set X) (n : ℕ) :
    LinearMap.range (subspaceHomologyMap A n) = LinearMap.ker (relativeProjectionHomologyMap A n) :=
  exact_at_middleHomology (pairSequence_shortExact A) n

/-- Exactness at `H_{n+1}(X, A)`. -/
theorem pair_exact_at_pair (A : Set X) (n : ℕ) :
    LinearMap.range (relativeProjectionHomologyMap A (n + 1)) =
      LinearMap.ker (pairConnecting X A n) :=
  exact_at_rightHomology (pairSequence_shortExact A) n

/-- `H_0(X) → H_0(X, A)` is surjective. -/
theorem relativeProjectionHomologyMap_zero_surjective (A : Set X) :
    Function.Surjective (relativeProjectionHomologyMap A 0) :=
  homologyLinearMap_second_zero_surjective (pairSequence_shortExact A)

/-! ### Degenerate pairs -/

/-- No chain of positive length is supported in the empty set. -/
theorem supportedChainSubmodule_empty (n : ℕ) :
    supportedChainSubmodule (∅ : Set X) n = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨σ, hσ, rfl⟩
  obtain ⟨s⟩ : Nonempty (Simplex n) := inferInstance
  exact absurd (hσ ⟨s, rfl⟩) (Set.notMem_empty _)

/-- Every chain is supported in the whole space. -/
theorem supportedChainSubmodule_univ (n : ℕ) :
    supportedChainSubmodule (Set.univ : Set X) n = ⊤ := by
  rw [← simplexChain_span X n, supportedChainSubmodule]
  congr 1
  ext c
  simp

/-- The homology of isomorphic complexes is linearly equivalent. -/
def homologyEquivOfIso {K L : ChainComplex (ModuleCat ℤ) ℕ} (e : K ≅ L) (n : ℕ) :
    K.homology n ≃ₗ[ℤ] L.homology n :=
  (HomologicalComplex.homologyMapIso e n).toLinearEquiv

@[simp]
theorem homologyEquivOfIso_apply {K L : ChainComplex (ModuleCat ℤ) ℕ} (e : K ≅ L) (n : ℕ)
    (a : K.homology n) : homologyEquivOfIso e n a = homologyLinearMap e.hom n a := rfl

/-- The relative projection for `A = ∅` is an isomorphism of complexes. -/
def relativeComplexIsoOfEmpty (X : Type) [TopologicalSpace X] :
    singularComplex X ≅ relativeComplex X ∅ :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => ((Submodule.quotEquivOfEqBot _ (supportedChainSubmodule_empty n)).symm).toModuleIso)
    (fun i j _ => (relativeProjection X ∅).comm i j)

@[simp]
theorem relativeComplexIsoOfEmpty_hom (X : Type) [TopologicalSpace X] :
    (relativeComplexIsoOfEmpty X).hom = relativeProjection X ∅ := rfl

/-- `H_n(X, ∅) ≅ H_n(X)`, realized by the relative projection. -/
def relativeHomologyEquivOfEmpty (X : Type) [TopologicalSpace X] (n : ℕ) :
    SingularHomology X n ≃ₗ[ℤ] RelativeHomology X ∅ n :=
  homologyEquivOfIso (relativeComplexIsoOfEmpty X) n

@[simp]
theorem relativeHomologyEquivOfEmpty_apply (X : Type) [TopologicalSpace X] (n : ℕ)
    (a : SingularHomology X n) :
    relativeHomologyEquivOfEmpty X n a = relativeProjectionHomologyMap ∅ n a := rfl

/-- The relative complex `C(X, X)` is zero in every degree. -/
instance relativeComplex_univ_subsingleton (n : ℕ) :
    Subsingleton ((relativeComplex X Set.univ).X n) := by
  change Subsingleton (Chains X n ⧸ supportedChainSubmodule Set.univ n)
  rw [supportedChainSubmodule_univ]
  exact Submodule.Quotient.subsingleton_iff.mpr rfl

/-- `H_n(X, X) = 0`. -/
theorem relativeHomology_subsingleton_of_univ (n : ℕ) :
    Subsingleton (RelativeHomology X Set.univ n) := by
  have hz : Limits.IsZero ((relativeComplex X Set.univ).X n) :=
    ModuleCat.isZero_of_subsingleton _
  have : (relativeComplex X Set.univ).ExactAt n := HomologicalComplex.ExactAt.of_isZero hz
  exact ModuleCat.isZero_iff_subsingleton.mp this.isZero_homology

/-! ### Restriction along `A ⊆ A'` -/

/-- The chain map `C(X, A) ⟶ C(X, A')` for `A ⊆ A'`. -/
abbrev restrictionChainMap {A A' : Set X} (h : A ⊆ A') : relativeComplex X A ⟶ relativeComplex X A' :=
  ChainSubmodule.quotientMap (supportedSubmodule_mono h)

/-- The restriction `H_n(X, A) → H_n(X, A')` for `A ⊆ A'`, induced by the inclusion of pairs
`(X, A) ⊆ (X, A')`. -/
abbrev restriction {A A' : Set X} (h : A ⊆ A') (n : ℕ) :
    RelativeHomology X A n →ₗ[ℤ] RelativeHomology X A' n :=
  homologyLinearMap (restrictionChainMap h) n

theorem restrictionChainMap_relativeClass {A A' : Set X} (h : A ⊆ A') (n : ℕ) (c : Chains X n) :
    ((restrictionChainMap h).f n).hom (relativeClass A n c) = relativeClass A' n c :=
  ChainSubmodule.quotientMap_f_mk _ n c

theorem restriction_comp {A A' A'' : Set X} (h : A ⊆ A') (h' : A' ⊆ A'') (n : ℕ) :
    (restriction h' n).comp (restriction h n) = restriction (h.trans h') n := by
  rw [restriction, restriction, ← homologyLinearMap_comp, ChainSubmodule.quotientMap_comp]

theorem restriction_refl (A : Set X) (n : ℕ) : restriction (subset_refl A) n = LinearMap.id := by
  rw [restriction, restrictionChainMap, ChainSubmodule.quotientMap_id, homologyLinearMap,
    HomologicalComplex.homologyMap_id]
  rfl

/-- Restriction commutes with the relative projection. -/
theorem restriction_relativeProjectionHomologyMap {A A' : Set X} (h : A ⊆ A') (n : ℕ) :
    (restriction h n).comp (relativeProjectionHomologyMap A n) = relativeProjectionHomologyMap A' n := by
  rw [relativeProjectionHomologyMap, restriction, ← homologyLinearMap_comp,
    ChainSubmodule.π_quotientMap]

/-! ### Consequences of the long exact sequence -/

/-- If `H_{n+1}(X) = 0`, the connecting map `H_{n+1}(X, A) → H_n(A)` is injective. -/
theorem pairConnecting_injective (A : Set X) (n : ℕ)
    (hX : Subsingleton (SingularHomology X (n + 1))) : Function.Injective (pairConnecting X A n) := by
  rw [← LinearMap.ker_eq_bot, ← pair_exact_at_pair, LinearMap.range_eq_bot]
  ext a
  rw [Subsingleton.elim a 0, map_zero]
  rfl

/-- If `H_n(X) = 0`, the connecting map `H_{n+1}(X, A) → H_n(A)` is surjective. -/
theorem pairConnecting_surjective (A : Set X) (n : ℕ) (hX : Subsingleton (SingularHomology X n)) :
    Function.Surjective (pairConnecting X A n) := by
  rw [← LinearMap.range_eq_top, pair_exact_at_subspace, LinearMap.ker_eq_top]
  ext a
  exact Subsingleton.elim _ _

/-- If `H_{n+1}(X) = H_n(X) = 0`, the connecting map is an isomorphism `H_{n+1}(X, A) ≅ H_n(A)`. -/
def pairConnectingEquiv (A : Set X) (n : ℕ) (hX₁ : Subsingleton (SingularHomology X (n + 1)))
    (hX₀ : Subsingleton (SingularHomology X n)) :
    RelativeHomology X A (n + 1) ≃ₗ[ℤ] SingularHomology A n :=
  LinearEquiv.ofBijective _ ⟨pairConnecting_injective A n hX₁, pairConnecting_surjective A n hX₀⟩

@[simp]
theorem pairConnectingEquiv_apply (A : Set X) (n : ℕ) (hX₁) (hX₀) (a : RelativeHomology X A (n + 1)) :
    pairConnectingEquiv A n hX₁ hX₀ a = pairConnecting X A n a := rfl

/-- If `H_{n+1}(X) = 0` and `H_n(A) → H_n(X)` is injective, then `H_{n+1}(X, A) = 0`. -/
theorem relativeHomology_succ_subsingleton (A : Set X) (n : ℕ)
    (hX : Subsingleton (SingularHomology X (n + 1))) (hinj : Function.Injective (subspaceHomologyMap A n)) :
    Subsingleton (RelativeHomology X A (n + 1)) := by
  refine ⟨fun a b => pairConnecting_injective A n hX ?_⟩
  have hker : LinearMap.ker (subspaceHomologyMap A n) = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have hrange : LinearMap.range (pairConnecting X A n) = ⊥ := by rw [pair_exact_at_subspace, hker]
  have ha : pairConnecting X A n a ∈ LinearMap.range (pairConnecting X A n) := ⟨a, rfl⟩
  have hb : pairConnecting X A n b ∈ LinearMap.range (pairConnecting X A n) := ⟨b, rfl⟩
  rw [hrange, Submodule.mem_bot] at ha hb
  rw [ha, hb]

/-- If `H_0(A) → H_0(X)` is surjective, then `H_0(X, A) = 0`. -/
theorem relativeHomology_zero_subsingleton (A : Set X)
    (hsurj : Function.Surjective (subspaceHomologyMap A 0)) : Subsingleton (RelativeHomology X A 0) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨a', rfl⟩ := relativeProjectionHomologyMap_zero_surjective A a
  obtain ⟨b', rfl⟩ := relativeProjectionHomologyMap_zero_surjective A b
  have hker : LinearMap.ker (relativeProjectionHomologyMap A 0) = ⊤ := by
    rw [← pair_exact_at_space, LinearMap.range_eq_top]
    exact hsurj
  have ha : a' ∈ LinearMap.ker (relativeProjectionHomologyMap A 0) := by rw [hker]; trivial
  have hb : b' ∈ LinearMap.ker (relativeProjectionHomologyMap A 0) := by rw [hker]; trivial
  rw [LinearMap.mem_ker] at ha hb
  rw [ha, hb]

/-- Restriction along an equality of sets is bijective. -/
theorem restriction_bijective_of_eq {A A' : Set X} (h : A = A') (n : ℕ) :
    Function.Bijective (restriction (le_of_eq h) n) := by
  subst h
  rw [restriction_refl]
  exact Function.bijective_id

end RelativeSingularHomology
