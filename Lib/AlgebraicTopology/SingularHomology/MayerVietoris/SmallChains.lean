/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.Chains

/-!
# Small singular chains for a two-set cover

For a topological space `X` and sets `U V : Set X`, the singular chains supported on `U`
(`supportedChainSubmodule U n`: spanned by the simplices with image in `U`) and the
`(U, V)`-small chains — chains each of whose simplices lies in `U` or in `V`
(`smallChainSubmodule U V n`) — form a subcomplex `smallComplex U V` of the singular chain
complex, with inclusion `smallInclusion U V`.  This is the complex `C_n^𝒰(X)` of Hatcher,
*Algebraic Topology*, Proposition 2.21, for the cover `𝒰 = {U, V}`.

The singular chains of the subspace `U` map to `X` along `subtypeInclusion U`; the induced
chain map is injective with image the supported submodule (`subtypeInclusion_chain_injective`,
`subtypeInclusion_chain_range`, through the retraction `subtypeChainRetraction`), and the
supported submodules of `U` and `V` meet in that of `U ∩ V` (`supportedChainSubmodule_inf`).

## Main definitions

* `SingularMayerVietoris.smallComplex`, `SingularMayerVietoris.smallInclusion`;
* `SingularMayerVietoris.liftToSmall` — a chain map into the singular complex with small values
  factors through the small complex.
-/

open Set Function Filter Topology

open scoped CategoryTheory

@[expose] public noncomputable section

/-- The submodule of singular chains supported on a set `U`: chains whose simplices all have image inside `U` (the carrier set underlying the Mayer-Vietoris small-chain argument). -/
def SingularMayerVietoris.supportedChainSubmodule {X : Type} [TopologicalSpace X] (U : Set X)
    (n : ℕ) : Submodule ℤ (SingularChains.Chains X n) :=
  Submodule.span ℤ
    (SingularChains.simplexChain X n '' {σ : SingularChains.SingularSimplex X n | Set.range σ ⊆ U})

/-- The submodule of `(U, V)`-small chains: chains whose simplices each lie in `U` or in `V` (Hatcher, Algebraic Topology, proof of Theorem 2.20). -/
def SingularMayerVietoris.smallChainSubmodule {X : Type} [TopologicalSpace X] (U V : Set X)
    (n : ℕ) : Submodule ℤ (SingularChains.Chains X n) :=
  supportedChainSubmodule U n ⊔ supportedChainSubmodule V n

/-! ### Small and supported chains -/

/-- The small chains are spanned by the supported simplices. -/
theorem SingularMayerVietoris.smallChainSubmodule_eq_span {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) :
    smallChainSubmodule U V n =
      Submodule.span ℤ
        (SingularChains.simplexChain X n ''
          {σ : SingularChains.SingularSimplex X n | Set.range σ ⊆ U ∨ Set.range σ ⊆ V}) := by
  rw [smallChainSubmodule, supportedChainSubmodule, supportedChainSubmodule, ←
    Submodule.span_union, ← Set.image_union]
  rfl

/-- A simplex supported on `U` lies in the supported submodule. -/
theorem SingularMayerVietoris.simplexChain_mem_supported {X : Type} [TopologicalSpace X]
    (U : Set X) (n : ℕ) (σ : SingularChains.SingularSimplex X n) (hσ : Set.range σ ⊆ U) :
    SingularChains.simplexChain X n σ ∈ supportedChainSubmodule U n :=
  Submodule.subset_span ⟨σ, hσ, rfl⟩

/-- A simplex supported on `U` or `V` is small. -/
theorem SingularMayerVietoris.simplexChain_mem_small {X : Type} [TopologicalSpace X] (U V : Set X)
    (n : ℕ) (σ : SingularChains.SingularSimplex X n) (hσ : Set.range σ ⊆ U ∨ Set.range σ ⊆ V) :
    SingularChains.simplexChain X n σ ∈ smallChainSubmodule U V n := by
  rw [smallChainSubmodule_eq_span]
  exact Submodule.subset_span ⟨σ, hσ, rfl⟩

/-- Faces of a supported simplex are supported. -/
theorem SingularMayerVietoris.simplex_face_supported {X : Type} [TopologicalSpace X] (U : Set X)
    (n : ℕ) (σ : SingularChains.SingularSimplex X (n + 1)) (hσ : Set.range σ ⊆ U)
    (i : Fin (n + 2)) : Set.range (σ.comp (SingularChains.simplexFace n i)) ⊆ U := by
  rintro x ⟨s, rfl⟩
  exact hσ ⟨SingularChains.simplexFace n i s, rfl⟩

/-- The boundary of a small simplex is small. -/
theorem SingularMayerVietoris.boundary_mem_small_succ {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (c : SingularChains.Chains X (n + 1))
    (hc : c ∈ smallChainSubmodule U V (n + 1)) :
    ((SingularChains.singularComplex X).d (n + 1) n).hom c ∈ smallChainSubmodule U V n := by
  have hle :
    smallChainSubmodule U V (n + 1) ≤
      (smallChainSubmodule U V n).comap ((SingularChains.singularComplex X).d (n + 1) n).hom := by
    rw [smallChainSubmodule_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨σ, hσ, rfl⟩
    change
      (SingularChains.singularComplex X).d (n + 1) n (SingularChains.simplexChain X (n + 1) σ) ∈
        smallChainSubmodule U V n
    rw [SingularChains.boundary_simplex]
    apply Submodule.sum_mem
    intro i hi
    apply (smallChainSubmodule U V n).toAddSubgroup.zsmul_mem
    apply simplexChain_mem_small
    exact
      hσ.imp (fun h => simplex_face_supported U n σ h i)
        (fun h => simplex_face_supported V n σ h i)
  exact hle hc

/-- The boundary of a small chain is small. -/
theorem SingularMayerVietoris.boundary_mem_small {X : Type} [TopologicalSpace X] (U V : Set X)
    (i j : ℕ) (c : SingularChains.Chains X i) (hc : c ∈ smallChainSubmodule U V i) :
    ((SingularChains.singularComplex X).d i j).hom c ∈ smallChainSubmodule U V j := by
  by_cases hij : (ComplexShape.down ℕ).Rel i j
  · have he : j + 1 = i := hij
    subst i
    exact boundary_mem_small_succ U V j c hc
  · have he :=
      congrArg (fun f : SingularChains.Chains X i ⟶ SingularChains.Chains X j => f.hom c)
        ((SingularChains.singularComplex X).shape i j hij)
    rw [he]
    exact Submodule.zero_mem _

/-- The submodule of small chains. -/
instance SingularMayerVietoris.smallChainModule {X : Type} [TopologicalSpace X] (U V : Set X)
    (n : ℕ) : Module ℤ (smallChainSubmodule U V n) :=
  (smallChainSubmodule U V n).module

/-- The boundary restricted to small chains. -/
def SingularMayerVietoris.smallDifferential {X : Type} [TopologicalSpace X] (U V : Set X)
    (i j : ℕ) : smallChainSubmodule U V i →ₗ[ℤ] smallChainSubmodule U V j :=
  (((SingularChains.singularComplex X).d i j).hom.comp
        (smallChainSubmodule U V i).subtype).codRestrict
    _ (fun c => boundary_mem_small U V i j c.1 c.2)

/-- The chain complex of `(U, V)`-small chains: the subcomplex of the singular chain complex spanned by simplices lying in `U` or in `V`. -/
def SingularMayerVietoris.smallComplex {X : Type} [TopologicalSpace X] (U V : Set X) :
    ChainComplex (ModuleCat ℤ) ℕ
    where
  X n := ModuleCat.of ℤ (smallChainSubmodule U V n)
  d i j := ModuleCat.ofHom (smallDifferential U V i j)
  shape i j
    hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact
      congrArg (fun f : SingularChains.Chains X i ⟶ SingularChains.Chains X j => f.hom c.1)
        ((SingularChains.singularComplex X).shape i j hij)
  d_comp_d' i j k hij
    hjk := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact
      congrArg (fun f : SingularChains.Chains X i ⟶ SingularChains.Chains X k => f.hom c.1)
        ((SingularChains.singularComplex X).d_comp_d i j k)

/-- The inclusion of small chains into all chains. -/
def SingularMayerVietoris.smallInclusion {X : Type} [TopologicalSpace X] (U V : Set X) :
    smallComplex U V ⟶ SingularChains.singularComplex X
    where
  f n := ModuleCat.ofHom (smallChainSubmodule U V n).subtype
  comm' i j
    hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    rfl

/-- The small-chain inclusion is injective in each degree. -/
theorem SingularMayerVietoris.smallInclusion_f_injective {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) : Function.Injective ((smallInclusion U V).f n) :=
  Subtype.val_injective

/-- The small-chain inclusion is a mono. -/
instance SingularMayerVietoris.smallInclusion_mono {X : Type} [TopologicalSpace X] (U V : Set X) :
    CategoryTheory.Mono (smallInclusion U V) :=
  HomologicalComplex.mono_of_mono_f _
    (fun n => (ModuleCat.mono_iff_injective _).mpr (smallInclusion_f_injective U V n))

/-- The subdivision lift: every chain of the ambient complex is sent, after enough barycentric subdivision, to the small subcomplex (the division lemma of the Mayer-Vietoris proof, Hatcher, Algebraic Topology, Theorem 2.20). -/
def SingularMayerVietoris.liftToSmall {X : Type} [TopologicalSpace X] (U V : Set X)
    {K : ChainComplex (ModuleCat ℤ) ℕ} (f : K ⟶ SingularChains.singularComplex X)
    (hf : ∀ n (c : K.X n), (f.f n).hom c ∈ smallChainSubmodule U V n) : K ⟶ smallComplex U V
    where
  f n := ModuleCat.ofHom ((f.f n).hom.codRestrict _ (hf n))
  comm' i j
    hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact congrArg (fun g : K.X i ⟶ SingularChains.Chains X j => g.hom c) (f.comm i j)

/-- A chain lifted to small chains includes to itself. -/
@[simp]
theorem SingularMayerVietoris.liftToSmall_inclusion {X : Type} [TopologicalSpace X] (U V : Set X)
    {K : ChainComplex (ModuleCat ℤ) ℕ} (f : K ⟶ SingularChains.singularComplex X)
    (hf : ∀ n (c : K.X n), (f.f n).hom c ∈ smallChainSubmodule U V n) :
    liftToSmall U V f hf ≫ smallInclusion U V = f := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  rfl

/-- The chain map induced by a subtype inclusion. -/
def SingularMayerVietoris.subtypeInclusion {X : Type} [TopologicalSpace X] (U : Set X) :
    C(U, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- A simplex factored through a subtype containing its range. -/
def SingularMayerVietoris.restrictSimplex {X : Type} [TopologicalSpace X] (U : Set X) (n : ℕ)
    (σ : SingularChains.SingularSimplex X n) (hσ : Set.range σ ⊆ U) :
    SingularChains.SingularSimplex U n :=
  ⟨fun p => ⟨σ p, hσ ⟨p, rfl⟩⟩, σ.continuous.subtype_mk _⟩

/-- The restricted simplex includes to the original. -/
@[simp]
theorem SingularMayerVietoris.subtypeInclusion_comp_restrictSimplex {X : Type}
    [TopologicalSpace X] (U : Set X) (n : ℕ) (σ : SingularChains.SingularSimplex X n)
    (hσ : Set.range σ ⊆ U) : (subtypeInclusion U).comp (restrictSimplex U n σ hσ) = σ := by
  ext p
  rfl

/-- The range of the subtype chain map is the supported submodule. -/
theorem SingularMayerVietoris.range_subtypeInclusion_comp {X : Type} [TopologicalSpace X]
    (U : Set X) (n : ℕ) (σ : SingularChains.SingularSimplex U n) :
    Set.range ((subtypeInclusion U).comp σ) ⊆ U := by
  rintro x ⟨p, rfl⟩
  exact (σ p).2

/-- The restricted simplex maps back to the original. -/
@[simp]
theorem SingularMayerVietoris.restrictSimplex_inclusion {X : Type} [TopologicalSpace X]
    (U : Set X) (n : ℕ) (σ : SingularChains.SingularSimplex U n)
    (hσ : Set.range ((subtypeInclusion U).comp σ) ⊆ U) :
    restrictSimplex U n ((subtypeInclusion U).comp σ) hσ = σ := by
  ext p
  rfl

/-- A chosen simplex preimage under a surjective map. -/
def SingularMayerVietoris.simplexRetraction {X : Type} [TopologicalSpace X] (U : Set X) (n : ℕ)
    (σ : SingularChains.SingularSimplex X n) : SingularChains.Chains U n := by
  classical
    exact
    if hσ : Set.range σ ⊆ U then SingularChains.simplexChain U n (restrictSimplex U n σ hσ) else 0

/-- The chain retraction along a surjective map on simplices. -/
def SingularMayerVietoris.subtypeChainRetraction {X : Type} [TopologicalSpace X] (U : Set X)
    (n : ℕ) : SingularChains.Chains X n →ₗ[ℤ] SingularChains.Chains U n :=
  SingularChains.chainLift X n (simplexRetraction U n)

/-- The retraction of an included simplex is the restricted simplex. -/
theorem SingularMayerVietoris.subtypeChainRetraction_inclusion_simplex {X : Type}
    [TopologicalSpace X] (U : Set X) (n : ℕ) (σ : SingularChains.SingularSimplex U n) :
    subtypeChainRetraction U n
        (SingularChains.inducedChain (subtypeInclusion U) n (SingularChains.simplexChain U n σ)) =
      SingularChains.simplexChain U n σ := by
  rw [SingularChains.inducedChain_simplex]
  change SingularChains.chainLift X n (simplexRetraction U n) _ = _
  rw [SingularChains.chainLift_simplex]
  simp only [simplexRetraction, dif_pos (range_subtypeInclusion_comp U n σ),
    restrictSimplex_inclusion]

/-- The retraction left-inverts the subtype chain inclusion. -/
theorem SingularMayerVietoris.subtypeChainRetraction_comp {X : Type} [TopologicalSpace X]
    (U : Set X) (n : ℕ) :
    (subtypeChainRetraction U n).comp (SingularChains.inducedChain (subtypeInclusion U) n) =
      LinearMap.id := by
  apply SingularChains.chainMap_ext U n
  intro σ
  exact subtypeChainRetraction_inclusion_simplex U n σ

/-- The subtype chain map is injective. -/
theorem SingularMayerVietoris.subtypeInclusion_chain_injective {X : Type} [TopologicalSpace X]
    (U : Set X) (n : ℕ) :
    Function.Injective (SingularChains.inducedChain (subtypeInclusion U) n) :=
  (show
      Function.LeftInverse (subtypeChainRetraction U n)
        (SingularChains.inducedChain (subtypeInclusion U) n)
      from fun c => LinearMap.congr_fun (subtypeChainRetraction_comp U n) c).injective

/-- The generator image under the subtype chain map. -/
theorem SingularMayerVietoris.subtypeInclusion_generator_image {X : Type} [TopologicalSpace X]
    (U : Set X) (n : ℕ) :
    SingularChains.inducedChain (subtypeInclusion U) n ''
        Set.range (SingularChains.simplexChain U n) =
      SingularChains.simplexChain X n ''
        {σ : SingularChains.SingularSimplex X n | Set.range σ ⊆ U} := by
  ext c
  constructor
  · rintro ⟨_, ⟨σ, rfl⟩, rfl⟩
    exact
      ⟨(subtypeInclusion U).comp σ, range_subtypeInclusion_comp U n σ,
        (SingularChains.inducedChain_simplex (subtypeInclusion U) n σ).symm⟩
  · rintro ⟨σ, hσ, rfl⟩
    refine ⟨SingularChains.simplexChain U n (restrictSimplex U n σ hσ), ⟨_, rfl⟩, ?_⟩
    rw [SingularChains.inducedChain_simplex, subtypeInclusion_comp_restrictSimplex]

/-- The subtype chain map's range is the supported submodule. -/
theorem SingularMayerVietoris.subtypeInclusion_chain_range {X : Type} [TopologicalSpace X]
    (U : Set X) (n : ℕ) :
    LinearMap.range (SingularChains.inducedChain (subtypeInclusion U) n) =
      supportedChainSubmodule U n := by
  rw [LinearMap.range_eq_map, ← SingularChains.simplexChain_span U n, Submodule.map_span,
    subtypeInclusion_generator_image]
  rfl

/-- Supported submodules intersect to the intersection support. -/
theorem SingularMayerVietoris.supportedChainSubmodule_inf {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) :
    supportedChainSubmodule U n ⊓ supportedChainSubmodule V n =
      supportedChainSubmodule (U ∩ V) n := by
  have hsets :
    ({σ : SingularChains.SingularSimplex X n | Set.range σ ⊆ U} ∩
        {σ : SingularChains.SingularSimplex X n | Set.range σ ⊆ V}) =
      {σ : SingularChains.SingularSimplex X n | Set.range σ ⊆ U ∩ V} := by
    ext σ
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.subset_inter_iff]
  unfold supportedChainSubmodule
  rw [SingularChains.simplex_span_inter, hsets]

/-- A chain lies in the subtype range exactly when supported. -/
theorem SingularMayerVietoris.subtypeInclusion_chain_mem {X : Type} [TopologicalSpace X]
    (U : Set X) (n : ℕ) (c : SingularChains.Chains U n) :
    SingularChains.inducedChain (subtypeInclusion U) n c ∈ supportedChainSubmodule U n := by
  rw [← subtypeInclusion_chain_range U n]
  exact ⟨c, rfl⟩
