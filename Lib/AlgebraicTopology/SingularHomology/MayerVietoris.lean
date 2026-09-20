/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Algebra.Homology.MayerVietorisShortExact
public import Lib.AlgebraicTopology.SingularHomology.Chains
public import Lib.AlgebraicTopology.SingularHomology.ModuleHomology

/-!
# The Mayer–Vietoris theorem for singular homology

For two open sets `U`, `V` covering `X` (`U ∪ V = univ`), the singular chain complexes fit
into a short exact sequence of chain complexes `0 → C(U ∩ V) → C(U) ⊞ C(V) → C^{U,V}(X) → 0`,
and the induced long exact sequence in homology is the Mayer–Vietoris sequence (Hatcher
§2.2). The headline exactness statement:

* `SingularMayerVietoris.exact_at_ambient (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ)` — exactness at the ambient homology of the long exact
  sequence assembled from `chainSequence`.

The sequence is built so that every chain of `C^{U,V}(X)` is small after enough barycentric
subdivision, and small chains split into `U`- and `V`-parts (`smallInclusion_quasiIso` —
the small simplices theorem, Hatcher Prop 2.21): the inclusion of the small chain complex
into the ambient one is a quasi-isomorphism.

## Outline of the proof

1. *Supported and small chains.*  `supportedChainSubmodule`, `smallChainSubmodule`,
   `smallComplex`, `smallInclusion`; small chains split (`toSmallLeft`, `toSmallRight`,
   `toSmall_jointly_surjective`) and the split parts agree on the intersection
   (`intersectionToLeft`, `intersectionToRight`).
2. *The short exact sequence.*  `middleComplex`, `leftMap`, `rightMap`, `chainSequence`,
   `chainSequence_shortExact` (via `SmallChainBiprod.shortExactOfComplexes`);
   `homologyLinearMap`, `connectingMap`, and the three exactness points of the
   module-level sequence (`exact_at_leftHomology`, `exact_at_middleHomology`,
   `exact_at_rightHomology`).
3. *Affine simplices and formal chains.*  `affineSimplex`, `simplexBarycenter`,
   `formalSimplex`, `formalLift`, `formalCone`, `formalBoundary`, `formalSubdivision`;
   the boundary identities `formalBoundary_cone`, `formalBoundary_boundary`,
   `formalMap_boundary`.
4. *Barycentric subdivision.*  `subdivision`, `subdivision_simplex`, `subdivision_boundary`;
   the chain homotopy `subdivisionHomotopy` between subdivision and identity
   (`subdivisionHomotopy_boundary`), iterated (`formalSubdivisionIteratedHomotopy`).
5. *Small simplices.*  Supports (`formalChainsSupported`), the Lebesgue-number argument
   (`exists_lebesgue_number_two`, `meshFactor`, `formalSubdivision_mesh`),
   `eventually_subdivision_mem_small`, and `smallInclusion_quasiIso` — after enough
   subdivisions every cycle is small, so `smallInclusion` is a quasi-isomorphism
   (Hatcher Prop 2.21).
6. *The long exact sequence.*  Comparison of the small sequence with the ambient one
   (`smallHomologyComparison`, `small_exact_at_*`, `rightTransport_*`), the connecting
   homomorphism `connectingHomomorphism`, and the exactness theorems
   `exact_at_intersection`, `exact_at_pair`, `exact_at_ambient`.

## Main definitions and results

* `SingularMayerVietoris.chainSequence` / `chainSequence_shortExact` : the short exact
  sequence of chain complexes.
* `SingularMayerVietoris.subdivision`, `.subdivisionHomotopy` : barycentric subdivision and
  its chain homotopy.
* `SingularMayerVietoris.smallInclusion_quasiIso` : the small simplices theorem
  (Hatcher Prop 2.21).
* `SingularMayerVietoris.exact_at_intersection/_pair/_ambient` :
  the Mayer–Vietoris long exact sequence (Hatcher Thm 2.20's conclusion for two opens).

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §2.2, Prop 2.21 and Theorem 2.20

## Tags

Mayer–Vietoris, barycentric subdivision, small simplices, long exact sequence
-/



open Set Function Filter Manifold Topology

open scoped CategoryTheory

universe u v

@[expose] public noncomputable section

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

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

/-! ### The Mayer–Vietoris short complex -/

/-- The left map of the Mayer–Vietoris short complex into small chains. -/
def SingularMayerVietoris.toSmallLeft {X : Type} [TopologicalSpace X] (U V : Set X) :
    SingularChains.singularComplex U ⟶ smallComplex U V :=
  liftToSmall U V (SingularChains.singularChainMap (subtypeInclusion U))
    (fun n c =>
      (show supportedChainSubmodule U n ≤ smallChainSubmodule U V n from le_sup_left)
        (subtypeInclusion_chain_mem U n c))

/-- The right map from small chains to the ambient chains. -/
def SingularMayerVietoris.toSmallRight {X : Type} [TopologicalSpace X] (U V : Set X) :
    SingularChains.singularComplex V ⟶ smallComplex U V :=
  liftToSmall U V (SingularChains.singularChainMap (subtypeInclusion V))
    (fun n c =>
      (show supportedChainSubmodule V n ≤ smallChainSubmodule U V n from le_sup_right)
        (subtypeInclusion_chain_mem V n c))

/-- The left map computes through the intersection inclusions. -/
@[simp]
theorem SingularMayerVietoris.toSmallLeft_inclusion {X : Type} [TopologicalSpace X]
    (U V : Set X) :
    toSmallLeft U V ≫ smallInclusion U V = SingularChains.singularChainMap (subtypeInclusion U) :=
  liftToSmall_inclusion U V _ _

/-- The right map computes the signed sum of inclusions. -/
@[simp]
theorem SingularMayerVietoris.toSmallRight_inclusion {X : Type} [TopologicalSpace X]
    (U V : Set X) :
    toSmallRight U V ≫ smallInclusion U V = SingularChains.singularChainMap (subtypeInclusion V) :=
  liftToSmall_inclusion U V _ _

/-- The two cover inclusions are jointly surjective onto small chains. -/
theorem SingularMayerVietoris.toSmall_jointly_surjective {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (s : (smallComplex U V).X n) :
    ∃ x : SingularChains.Chains U n,
      ∃ y : SingularChains.Chains V n,
        ((toSmallLeft U V).f n).hom x + ((toSmallRight U V).f n).hom y = s := by
  obtain ⟨c, hc, d, hd, hcd⟩ := Submodule.mem_sup.mp s.2
  rw [← subtypeInclusion_chain_range U n] at hc
  rw [← subtypeInclusion_chain_range V n] at hd
  obtain ⟨x, hx⟩ := hc
  obtain ⟨y, hy⟩ := hd
  refine ⟨x, y, ?_⟩
  apply Subtype.ext
  change
    SingularChains.inducedChain (subtypeInclusion U) n x +
        SingularChains.inducedChain (subtypeInclusion V) n y =
      s.1
  rw [hx, hy]
  exact hcd

/-- The chain map of the intersection into the left cover. -/
def SingularMayerVietoris.intersectionToLeft {X : Type} [TopologicalSpace X] (U V : Set X) :
    SingularChains.singularComplex (U ∩ V : Set X) ⟶ SingularChains.singularComplex U :=
  SingularChains.singularChainMap (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U))

/-- The chain map of the intersection into the right cover. -/
def SingularMayerVietoris.intersectionToRight {X : Type} [TopologicalSpace X] (U V : Set X) :
    SingularChains.singularComplex (U ∩ V : Set X) ⟶ SingularChains.singularComplex V :=
  SingularChains.singularChainMap (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V))

/-- The left intersection map viewed in the ambient chains. -/
theorem SingularMayerVietoris.intersectionToLeft_ambient {X : Type} [TopologicalSpace X]
    (U V : Set X) :
    intersectionToLeft U V ≫ SingularChains.singularChainMap (subtypeInclusion U) =
      SingularChains.singularChainMap (subtypeInclusion (U ∩ V)) := by
  have h :=
    ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map_comp
      (TopCat.ofHom (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)))
      (TopCat.ofHom (subtypeInclusion U))
  exact h.symm

/-- The right intersection map viewed in the ambient chains. -/
theorem SingularMayerVietoris.intersectionToRight_ambient {X : Type} [TopologicalSpace X]
    (U V : Set X) :
    intersectionToRight U V ≫ SingularChains.singularChainMap (subtypeInclusion V) =
      SingularChains.singularChainMap (subtypeInclusion (U ∩ V)) := by
  have h :=
    ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map_comp
      (TopCat.ofHom (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V)))
      (TopCat.ofHom (subtypeInclusion V))
  exact h.symm

/-- The left intersection map computes through the subtype inclusion. -/
@[simp]
theorem SingularMayerVietoris.intersectionToLeft_ambient_apply {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (c : SingularChains.Chains (U ∩ V : Set X) n) :
    SingularChains.inducedChain (subtypeInclusion U) n (((intersectionToLeft U V).f n).hom c) =
      SingularChains.inducedChain (subtypeInclusion (U ∩ V)) n c :=
  congrArg (fun f => (f.f n).hom c) (intersectionToLeft_ambient U V)

/-- The right intersection map computes through the subtype inclusion. -/
@[simp]
theorem SingularMayerVietoris.intersectionToRight_ambient_apply {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (c : SingularChains.Chains (U ∩ V : Set X) n) :
    SingularChains.inducedChain (subtypeInclusion V) n (((intersectionToRight U V).f n).hom c) =
      SingularChains.inducedChain (subtypeInclusion (U ∩ V)) n c :=
  congrArg (fun f => (f.f n).hom c) (intersectionToRight_ambient U V)

/-- The left intersection chain map is injective. -/
theorem SingularMayerVietoris.intersectionToLeft_f_injective {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) : Function.Injective ((intersectionToLeft U V).f n).hom := by
  intro a b hab
  apply subtypeInclusion_chain_injective (U ∩ V) n
  calc
    _ =
        SingularChains.inducedChain (subtypeInclusion U) n
          (((intersectionToLeft U V).f n).hom a) :=
      (intersectionToLeft_ambient_apply U V n a).symm
    _ =
        SingularChains.inducedChain (subtypeInclusion U) n
          (((intersectionToLeft U V).f n).hom b) :=
      (congrArg (SingularChains.inducedChain (subtypeInclusion U) n) hab)
    _ = _ := intersectionToLeft_ambient_apply U V n b

/-- The two intersection inclusions commute with the cover inclusions. -/
theorem SingularMayerVietoris.intersection_toSmall_comm {X : Type} [TopologicalSpace X]
    (U V : Set X) :
    intersectionToLeft U V ≫ toSmallLeft U V = intersectionToRight U V ≫ toSmallRight U V := by
  apply (CategoryTheory.cancel_mono (smallInclusion U V)).mp
  simp only [CategoryTheory.Category.assoc, toSmallLeft_inclusion, toSmallRight_inclusion,
    intersectionToLeft_ambient, intersectionToRight_ambient]

/-- A small chain over the overlap lifts to the left. -/
theorem SingularMayerVietoris.toSmall_overlap_lift {X : Type} [TopologicalSpace X] (U V : Set X)
    (n : ℕ) (x : SingularChains.Chains U n) (y : SingularChains.Chains V n)
    (hxy : ((toSmallLeft U V).f n).hom x = ((toSmallRight U V).f n).hom y) :
    ∃ z : SingularChains.Chains (U ∩ V : Set X) n,
      ((intersectionToLeft U V).f n).hom z = x ∧ ((intersectionToRight U V).f n).hom z = y := by
  have hxy' :
    SingularChains.inducedChain (subtypeInclusion U) n x =
      SingularChains.inducedChain (subtypeInclusion V) n y :=
    congrArg (fun s : (smallComplex U V).X n => s.1) hxy
  have hy : SingularChains.inducedChain (subtypeInclusion U) n x ∈ supportedChainSubmodule V n := by
    rw [hxy']
    exact subtypeInclusion_chain_mem V n y
  have hi :
    SingularChains.inducedChain (subtypeInclusion U) n x ∈
      supportedChainSubmodule U n ⊓ supportedChainSubmodule V n :=
    ⟨subtypeInclusion_chain_mem U n x, hy⟩
  rw [supportedChainSubmodule_inf, ← subtypeInclusion_chain_range (U ∩ V) n] at hi
  obtain ⟨z, hz⟩ := hi
  refine ⟨z, ?_, ?_⟩
  · apply subtypeInclusion_chain_injective U n
    rw [intersectionToLeft_ambient_apply]
    exact hz
  · apply subtypeInclusion_chain_injective V n
    rw [intersectionToRight_ambient_apply]
    exact hz.trans hxy'

/-- The middle term of the Mayer–Vietoris short complex. -/
def SingularMayerVietoris.middleComplex {X : Type} [TopologicalSpace X] (U V : Set X) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  SingularChains.singularComplex U ⊞ SingularChains.singularComplex V

/-- The left short-complex map `c ↦ (i_* c, −j_* c)`. -/
def SingularMayerVietoris.leftMap {X : Type} [TopologicalSpace X] (U V : Set X) :
    SingularChains.singularComplex (U ∩ V : Set X) ⟶ middleComplex U V :=
  CategoryTheory.Limits.biprod.lift (intersectionToLeft U V) (-(intersectionToRight U V))

/-- The right short-complex map `(a, b) ↦ i_* a + j_* b`. -/
def SingularMayerVietoris.rightMap {X : Type} [TopologicalSpace X] (U V : Set X) :
    middleComplex U V ⟶ smallComplex U V :=
  CategoryTheory.Limits.biprod.desc (toSmallLeft U V) (toSmallRight U V)

/-- The first component of the left map. -/
@[simp]
theorem SingularMayerVietoris.leftMap_fst {X : Type} [TopologicalSpace X] (U V : Set X) :
    leftMap U V ≫
        (CategoryTheory.Limits.biprod.fst : middleComplex U V ⟶ SingularChains.singularComplex U) =
      intersectionToLeft U V :=
  CategoryTheory.Limits.biprod.lift_fst _ _

/-- The second component of the left map. -/
@[simp]
theorem SingularMayerVietoris.leftMap_snd {X : Type} [TopologicalSpace X] (U V : Set X) :
    leftMap U V ≫
        (CategoryTheory.Limits.biprod.snd : middleComplex U V ⟶ SingularChains.singularComplex V) =
      -(intersectionToRight U V) :=
  CategoryTheory.Limits.biprod.lift_snd _ _

/-- The right map on the left summand is the `U` inclusion. -/
@[simp]
theorem SingularMayerVietoris.inl_rightMap {X : Type} [TopologicalSpace X] (U V : Set X) :
    (CategoryTheory.Limits.biprod.inl : SingularChains.singularComplex U ⟶ middleComplex U V) ≫
        rightMap U V =
      toSmallLeft U V :=
  CategoryTheory.Limits.biprod.inl_desc _ _

/-- The right map on the right summand is the `V` inclusion. -/
@[simp]
theorem SingularMayerVietoris.inr_rightMap {X : Type} [TopologicalSpace X] (U V : Set X) :
    (CategoryTheory.Limits.biprod.inr : SingularChains.singularComplex V ⟶ middleComplex U V) ≫
        rightMap U V =
      toSmallRight U V :=
  CategoryTheory.Limits.biprod.inr_desc _ _

/-- The composite `leftMap ∘ rightMap` is zero. -/
theorem SingularMayerVietoris.leftMap_rightMap {X : Type} [TopologicalSpace X] (U V : Set X) :
    leftMap U V ≫ rightMap U V = 0 := by
  change
    CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.biprod.lift _ _)
        (CategoryTheory.Limits.biprod.desc _ _) =
      0
  rw [CategoryTheory.Limits.biprod.lift_desc, CategoryTheory.Preadditive.neg_comp,
    intersection_toSmall_comm, add_neg_cancel]

/-- The short exact sequence of chain complexes `0 -> C(U cap V) -> C(U) +" C(V) -> C^{U,V}(X) -> 0` underlying the Mayer-Vietoris long exact sequence. -/
def SingularMayerVietoris.chainSequence {X : Type} [TopologicalSpace X] (U V : Set X) :
    CategoryTheory.ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  CategoryTheory.ShortComplex.mk (leftMap U V) (rightMap U V) (leftMap_rightMap U V)

/-- The chain sequence of a two-open cover is short exact: injectivity on the intersection, kernel = image at the sum, and surjectivity onto the small chains (Hatcher, Algebraic Topology, Theorem 2.20). -/
theorem SingularMayerVietoris.chainSequence_shortExact {X : Type} [TopologicalSpace X]
    (U V : Set X) : (chainSequence U V).ShortExact :=
  SmallChainBiprod.shortExactOfComplexes (intersectionToLeft U V) (intersectionToRight U V)
    (toSmallLeft U V) (toSmallRight U V) (intersection_toSmall_comm U V)
    (intersectionToLeft_f_injective U V) (toSmall_jointly_surjective U V)
    (toSmall_overlap_lift U V)

/-! ### Homology of the short complex -/

/-- The homology map induced by a chain map. -/
abbrev SingularMayerVietoris.homologyLinearMap {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f : K ⟶ L) (n : ℕ) : K.homology n →ₗ[ℤ] L.homology n :=
  (HomologicalComplex.homologyMap f n).hom

/-- Homology maps compose. -/
theorem SingularMayerVietoris.homologyLinearMap_comp {K L M : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f : K ⟶ L) (g : L ⟶ M) (n : ℕ) :
    homologyLinearMap (f ≫ g) n = (homologyLinearMap g n).comp (homologyLinearMap f n) :=
  congrArg ModuleCat.Hom.hom (HomologicalComplex.homologyMap_comp f g n)

/-- The homology map of a negated chain map is negated. -/
@[simp]
theorem SingularMayerVietoris.homologyLinearMap_neg {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f : K ⟶ L) (n : ℕ) : homologyLinearMap (-f) n = -homologyLinearMap f n :=
  congrArg ModuleCat.Hom.hom (HomologicalComplex.homologyMap_neg f n)

/-- The connecting homomorphism of the short complex. -/
def SingularMayerVietoris.connectingMap
    {S : CategoryTheory.ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ)} (hS : S.ShortExact)
    (n : ℕ) : S.X₃.homology (n + 1) →ₗ[ℤ] S.X₁.homology n :=
  (hS.δ (n + 1) n (by simp)).hom

/-- Exactness at the left homology term. -/
theorem SingularMayerVietoris.exact_at_leftHomology
    {S : CategoryTheory.ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ)} (hS : S.ShortExact)
    (n : ℕ) : LinearMap.range (connectingMap hS n) = LinearMap.ker (homologyLinearMap S.f n) :=
  (hS.homology_exact₁ (n + 1) n (by simp)).moduleCat_range_eq_ker

/-- Exactness at the middle homology term. -/
theorem SingularMayerVietoris.exact_at_middleHomology
    {S : CategoryTheory.ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ)} (hS : S.ShortExact)
    (n : ℕ) :
    LinearMap.range (homologyLinearMap S.f n) = LinearMap.ker (homologyLinearMap S.g n) :=
  (hS.homology_exact₂ n).moduleCat_range_eq_ker

/-- Exactness at the right homology term. -/
theorem SingularMayerVietoris.exact_at_rightHomology
    {S : CategoryTheory.ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ)} (hS : S.ShortExact)
    (n : ℕ) :
    LinearMap.range (homologyLinearMap S.g (n + 1)) = LinearMap.ker (connectingMap hS n) :=
  (hS.homology_exact₃ (n + 1) n (by simp)).moduleCat_range_eq_ker

/-- The degree-zero right map is surjective. -/
theorem SingularMayerVietoris.homologyLinearMap_second_zero_surjective
    {S : CategoryTheory.ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ)} (hS : S.ShortExact) :
    Function.Surjective (homologyLinearMap S.g 0) := by
  have := hS.epi_g
  have := HomologicalComplex.epi_homologyMap_of_epi_of_not_rel S.g 0 (by intro j; simp)
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

/-- The connecting map is natural in the short exact sequence. -/
theorem SingularMayerVietoris.connectingMap_naturality
    {S T : CategoryTheory.ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ)} (hS : S.ShortExact)
    (φ : S ⟶ T) (hT : T.ShortExact) (n : ℕ) :
    (homologyLinearMap φ.τ₁ n).comp (connectingMap hS n) =
      (connectingMap hT n).comp (homologyLinearMap φ.τ₃ (n + 1)) :=
  congrArg ModuleCat.Hom.hom
    (HomologicalComplex.HomologySequence.δ_naturality φ hS hT (n + 1) n (by simp))

/-- The homology class of a cycle element. -/
def SingularMayerVietoris.homologyClassOfCycle (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) {i : ℕ}
    (z : K.X i) (j : ℕ) (hj : (ComplexShape.down ℕ).next i = j) (hz : (K.d i j).hom z = 0) :
    K.homology i :=
  (K.homologyπ i).hom (K.cyclesMk z j hj hz)

/-- The chosen lift of a connecting preimage is a cycle. -/
theorem SingularMayerVietoris.connectingMap_lift_is_cycle
    {S : CategoryTheory.ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ)} (hS : S.ShortExact)
    (n : ℕ) (z₂ : S.X₂.X (n + 1)) (z₁ : S.X₁.X n)
    (hz₁ : (S.f.f n).hom z₁ = (S.X₂.d (n + 1) n).hom z₂) (k : ℕ) : (S.X₁.d n k).hom z₁ = 0 :=
  hS.d_eq_zero_of_f_eq_d_apply (n + 1) n z₂ z₁ hz₁ k

/-- The connecting map computes on cycle classes. -/
theorem SingularMayerVietoris.connectingMap_homologyClassOfCycle
    {S : CategoryTheory.ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ)} (hS : S.ShortExact)
    (n : ℕ) (z₃ : S.X₃.X (n + 1)) (hz₃ : (S.X₃.d (n + 1) n).hom z₃ = 0) (z₂ : S.X₂.X (n + 1))
    (hz₂ : (S.g.f (n + 1)).hom z₂ = z₃) (z₁ : S.X₁.X n)
    (hz₁ : (S.f.f n).hom z₁ = (S.X₂.d (n + 1) n).hom z₂) :
    connectingMap hS n
        (homologyClassOfCycle S.X₃ z₃ n ((ComplexShape.down ℕ).next_eq' (by simp)) hz₃) =
      homologyClassOfCycle S.X₁ z₁ ((ComplexShape.down ℕ).next n) rfl
        (connectingMap_lift_is_cycle hS n z₂ z₁ hz₁ _) :=
  hS.δ_apply (n + 1) n (by simp) z₃ hz₃ z₂ hz₂ z₁ hz₁ _ rfl

/-- The left component of an `inl` homology class. -/
theorem SingularMayerVietoris.homology_fst_inl
    (K L : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) (a : K.homology n) :
    (HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.fst : K ⊞ L ⟶ K) n).hom
        ((HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L) n).hom
          a) =
      a := by
  have h :=
    HomologicalComplex.homologyMap_comp (CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L)
      CategoryTheory.Limits.biprod.fst n
  rw [CategoryTheory.Limits.biprod.inl_fst, HomologicalComplex.homologyMap_id] at h
  exact (congrArg (fun f => f.hom a) h).symm

/-- The right component of an `inl` homology class. -/
theorem SingularMayerVietoris.homology_snd_inl
    (K L : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) (a : K.homology n) :
    (HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.snd : K ⊞ L ⟶ L) n).hom
        ((HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L) n).hom
          a) =
      0 := by
  have h :=
    HomologicalComplex.homologyMap_comp (CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L)
      CategoryTheory.Limits.biprod.snd n
  rw [CategoryTheory.Limits.biprod.inl_snd, HomologicalComplex.homologyMap_zero] at h
  exact (congrArg (fun f => f.hom a) h).symm

/-- The left component of an `inr` homology class. -/
theorem SingularMayerVietoris.homology_fst_inr
    (K L : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) (b : L.homology n) :
    (HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.fst : K ⊞ L ⟶ K) n).hom
        ((HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L) n).hom
          b) =
      0 := by
  have h :=
    HomologicalComplex.homologyMap_comp (CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L)
      CategoryTheory.Limits.biprod.fst n
  rw [CategoryTheory.Limits.biprod.inr_fst, HomologicalComplex.homologyMap_zero] at h
  exact (congrArg (fun f => f.hom b) h).symm

/-- The right component of an `inr` homology class. -/
theorem SingularMayerVietoris.homology_snd_inr
    (K L : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) (b : L.homology n) :
    (HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.snd : K ⊞ L ⟶ L) n).hom
        ((HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L) n).hom
          b) =
      b := by
  have h :=
    HomologicalComplex.homologyMap_comp (CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L)
      CategoryTheory.Limits.biprod.snd n
  rw [CategoryTheory.Limits.biprod.inr_snd, HomologicalComplex.homologyMap_id] at h
  exact (congrArg (fun f => f.hom b) h).symm

/-- Every pair-homology class splits into `inl` and `inr` parts. -/
theorem SingularMayerVietoris.homology_biprod_total
    (K L : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) (a : (K ⊞ L).homology n) :
    (HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L) n).hom
          ((HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.fst : K ⊞ L ⟶ K) n).hom
            a) +
        (HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L) n).hom
          ((HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.snd : K ⊞ L ⟶ L) n).hom
            a) =
      a := by
  have h :
    HomologicalComplex.homologyMap
        (CategoryTheory.CategoryStruct.comp CategoryTheory.Limits.biprod.fst
              CategoryTheory.Limits.biprod.inl +
            CategoryTheory.CategoryStruct.comp CategoryTheory.Limits.biprod.snd
              CategoryTheory.Limits.biprod.inr :
          K ⊞ L ⟶ K ⊞ L)
        n =
      𝟙 ((K ⊞ L).homology n) := by
    rw [CategoryTheory.Limits.biprod.total, HomologicalComplex.homologyMap_id]
  rw [HomologicalComplex.homologyMap_add, HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp] at h
  exact congrArg (fun f => f.hom a) h

/-! ### Homology of a bipod sequence -/

/-- Homology of a bipod complex is the product of homologies. -/
def SingularMayerVietoris.homologyBiprodEquiv (K L : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) :
    (K ⊞ L).homology n ≃ₗ[ℤ] (K.homology n × L.homology n) :=
  ({    toFun
          a :=
          ((HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.fst : K ⊞ L ⟶ K) n).hom
              a,
            (HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.snd : K ⊞ L ⟶ L) n).hom
              a)
        invFun
          a :=
          (HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L) n).hom
              a.1 +
            (HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L) n).hom
              a.2
        left_inv := homology_biprod_total K L n
        right_inv
          a := by
          apply Prod.ext
          · change
              (HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.fst : K ⊞ L ⟶ K)
                      n).hom
                  ((HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L)
                          n).hom
                      a.1 +
                    (HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L)
                          n).hom
                      a.2) =
                a.1
            rw [map_add, homology_fst_inl, homology_fst_inr, add_zero]
          · change
              (HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.snd : K ⊞ L ⟶ L)
                      n).hom
                  ((HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L)
                          n).hom
                      a.1 +
                    (HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L)
                          n).hom
                      a.2) =
                a.2
            rw [map_add, homology_snd_inl, homology_snd_inr, zero_add]
        map_add' a
          b := by
          change (_, _) = (_, _)
          rw [map_add, map_add] } :
      (K ⊞ L).homology n ≃+ (K.homology n × L.homology n)).toIntLinearEquiv

/-- The inverse equivalence computes the pair class. -/
theorem SingularMayerVietoris.homologyBiprodEquiv_symm_apply
    (K L : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) (a : K.homology n × L.homology n) :
    (homologyBiprodEquiv K L n).symm a =
      (HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L) n).hom a.1 +
        (HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L) n).hom
          a.2 :=
  rfl

/-- The equivalence descends a pair of homology maps. -/
theorem SingularMayerVietoris.homologyBiprodEquiv_desc {K : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    {L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (n : ℕ) {A : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f : K ⟶ A) (g : L ⟶ A) (a : K.homology n × L.homology n) :
    (HomologicalComplex.homologyMap (CategoryTheory.Limits.biprod.desc f g) n).hom
        ((homologyBiprodEquiv K L n).symm a) =
      (HomologicalComplex.homologyMap f n).hom a.1 +
        (HomologicalComplex.homologyMap g n).hom a.2 := by
  rw [homologyBiprodEquiv_symm_apply, map_add]
  congr 1
  · have h :=
      HomologicalComplex.homologyMap_comp (CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L)
        (CategoryTheory.Limits.biprod.desc f g) n
    rw [CategoryTheory.Limits.biprod.inl_desc] at h
    exact (congrArg (fun k => k.hom a.1) h).symm
  · have h :=
      HomologicalComplex.homologyMap_comp (CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L)
        (CategoryTheory.Limits.biprod.desc f g) n
    rw [CategoryTheory.Limits.biprod.inr_desc] at h
    exact (congrArg (fun k => k.hom a.2) h).symm

/-- The first map of the bipod sequence. -/
def SingularMayerVietoris.biprodSequenceFirstMap {A K L : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f : A ⟶ K ⊞ L) (n : ℕ) : A.homology n →ₗ[ℤ] (K.homology n × L.homology n) :=
  (homologyBiprodEquiv K L n).toLinearMap.comp (homologyLinearMap f n)

/-- The second map of the bipod sequence. -/
def SingularMayerVietoris.biprodSequenceSecondMap {K L B : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (g : K ⊞ L ⟶ B) (n : ℕ) : (K.homology n × L.homology n) →ₗ[ℤ] B.homology n :=
  (homologyLinearMap g n).comp (homologyBiprodEquiv K L n).symm.toLinearMap

/-- The second map descends the two components. -/
theorem SingularMayerVietoris.biprodSequenceSecondMap_desc
    {K L B : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : K ⟶ B) (g : L ⟶ B) (n : ℕ)
    (a : K.homology n × L.homology n) :
    biprodSequenceSecondMap (CategoryTheory.Limits.biprod.desc f g) n a =
      homologyLinearMap f n a.1 + homologyLinearMap g n a.2 :=
  homologyBiprodEquiv_desc n f g a

/-- The bipod sequence is exact at the left term. -/
theorem SingularMayerVietoris.biprodSequence_exact_at_leftHomology
    {A K L B : ChainComplex (ModuleCat.{0} ℤ) ℕ} {f : A ⟶ K ⊞ L} {g : K ⊞ L ⟶ B} {hfg : f ≫ g = 0}
    (hS : (CategoryTheory.ShortComplex.mk f g hfg).ShortExact) (n : ℕ) :
    LinearMap.range (connectingMap hS n) = LinearMap.ker (biprodSequenceFirstMap f n) := by
  rw [exact_at_leftHomology hS n]
  ext a
  change homologyLinearMap f n a = 0 ↔ homologyBiprodEquiv K L n (homologyLinearMap f n a) = 0
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    exact (homologyBiprodEquiv K L n).injective (h.trans (map_zero _).symm)

/-- The bipod sequence is exact at the middle term. -/
theorem SingularMayerVietoris.biprodSequence_exact_at_middleHomology
    {A K L B : ChainComplex (ModuleCat.{0} ℤ) ℕ} {f : A ⟶ K ⊞ L} {g : K ⊞ L ⟶ B} {hfg : f ≫ g = 0}
    (hS : (CategoryTheory.ShortComplex.mk f g hfg).ShortExact) (n : ℕ) :
    LinearMap.range (biprodSequenceFirstMap f n) = LinearMap.ker (biprodSequenceSecondMap g n) := by
  ext a
  change
    (∃ b, homologyBiprodEquiv K L n (homologyLinearMap f n b) = a) ↔
      homologyLinearMap g n ((homologyBiprodEquiv K L n).symm a) = 0
  constructor
  · rintro ⟨b, rfl⟩
    rw [LinearEquiv.symm_apply_apply]
    have hb : homologyLinearMap f n b ∈ LinearMap.range (homologyLinearMap f n) := ⟨b, rfl⟩
    rw [exact_at_middleHomology hS n] at hb
    exact hb
  · intro ha
    have hb : (homologyBiprodEquiv K L n).symm a ∈ LinearMap.range (homologyLinearMap f n) := by
      rw [exact_at_middleHomology hS n]
      exact ha
    obtain ⟨b, hb⟩ := hb
    exact
      ⟨b,
        (congrArg (homologyBiprodEquiv K L n) hb).trans
          ((homologyBiprodEquiv K L n).apply_symm_apply a)⟩

/-- The bipod sequence is exact at the right term. -/
theorem SingularMayerVietoris.biprodSequence_exact_at_rightHomology
    {A K L B : ChainComplex (ModuleCat.{0} ℤ) ℕ} {f : A ⟶ K ⊞ L} {g : K ⊞ L ⟶ B} {hfg : f ≫ g = 0}
    (hS : (CategoryTheory.ShortComplex.mk f g hfg).ShortExact) (n : ℕ) :
    LinearMap.range (biprodSequenceSecondMap g (n + 1)) = LinearMap.ker (connectingMap hS n) := by
  rw [← exact_at_rightHomology hS n]
  ext b
  change
    (∃ a, homologyLinearMap g (n + 1) ((homologyBiprodEquiv K L (n + 1)).symm a) = b) ↔
      ∃ a, homologyLinearMap g (n + 1) a = b
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨(homologyBiprodEquiv K L (n + 1)).symm a, ha⟩
  · rintro ⟨a, ha⟩
    refine ⟨homologyBiprodEquiv K L (n + 1) a, ?_⟩
    rwa [LinearEquiv.symm_apply_apply]

/-- The degree-zero second map is surjective. -/
theorem SingularMayerVietoris.biprodSequence_second_zero_surjective
    {A K L B : ChainComplex (ModuleCat.{0} ℤ) ℕ} {f : A ⟶ K ⊞ L} {g : K ⊞ L ⟶ B} {hfg : f ≫ g = 0}
    (hS : (CategoryTheory.ShortComplex.mk f g hfg).ShortExact) :
    Function.Surjective (biprodSequenceSecondMap g 0) :=
  (homologyLinearMap_second_zero_surjective hS).comp (homologyBiprodEquiv K L 0).symm.surjective

/-! ### Small homology and the comparison -/

/-- The singular homology module of a space. -/
abbrev SingularMayerVietoris.SingularHomology (Y : Type) [TopologicalSpace Y] (n : ℕ) :=
  (SingularChains.singularComplex Y).homology n

/-- The homology map induced by a continuous map. -/
abbrev SingularMayerVietoris.singularHomologyMap {Y Z : Type} [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(Y, Z)) (n : ℕ) :
    SingularHomology Y n →ₗ[ℤ] SingularHomology Z n :=
  homologyLinearMap (SingularChains.singularChainMap f) n

/-- The induced map in degree `n + 1` formulation. -/
@[simp]
theorem SingularMayerVietoris.singularHomologyMap_one {Y Z : Type} [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(Y, Z)) :
    singularHomologyMap f 1 = SingularChains.inducedHomology f :=
  rfl

/-- The homology of the small-chains complex. -/
abbrev SingularMayerVietoris.SmallHomology {X : Type} [TopologicalSpace X] (U V : Set X)
    (n : ℕ) :=
  (smallComplex U V).homology n

/-- The left map on small homology. -/
def SingularMayerVietoris.smallLeftHomologyMap {X : Type} [TopologicalSpace X] (U V : Set X)
    (n : ℕ) :
    SingularHomology (U ∩ V : Set X) n →ₗ[ℤ] (SingularHomology U n × SingularHomology V n) :=
  biprodSequenceFirstMap (leftMap U V) n

/-- The right map on small homology. -/
def SingularMayerVietoris.smallRightHomologyMap {X : Type} [TopologicalSpace X] (U V : Set X)
    (n : ℕ) : (SingularHomology U n × SingularHomology V n) →ₗ[ℤ] SmallHomology U V n :=
  biprodSequenceSecondMap (rightMap U V) n

/-- The connecting map of the small homology sequence. -/
def SingularMayerVietoris.smallConnectingMap {X : Type} [TopologicalSpace X] (U V : Set X)
    (n : ℕ) : SmallHomology U V (n + 1) →ₗ[ℤ] SingularHomology (U ∩ V : Set X) n :=
  connectingMap (chainSequence_shortExact U V) n

/-- The comparison from small homology to singular homology. -/
def SingularMayerVietoris.smallHomologyComparison {X : Type} [TopologicalSpace X] (U V : Set X)
    (n : ℕ) : SmallHomology U V n →ₗ[ℤ] SingularHomology X n :=
  homologyLinearMap (smallInclusion U V) n

/-- The left small-homology map in components. -/
theorem SingularMayerVietoris.smallLeftHomologyMap_components {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (a : SingularHomology (U ∩ V : Set X) n) :
    smallLeftHomologyMap U V n a =
      (homologyLinearMap
          (leftMap U V ≫
            (CategoryTheory.Limits.biprod.fst :
              middleComplex U V ⟶ SingularChains.singularComplex U))
          n a,
        homologyLinearMap
          (leftMap U V ≫
            (CategoryTheory.Limits.biprod.snd :
              middleComplex U V ⟶ SingularChains.singularComplex V))
          n a) := by
  apply Prod.ext
  · exact
      (LinearMap.congr_fun
          (homologyLinearMap_comp (leftMap U V) CategoryTheory.Limits.biprod.fst n) a).symm
  · exact
      (LinearMap.congr_fun
          (homologyLinearMap_comp (leftMap U V) CategoryTheory.Limits.biprod.snd n) a).symm

/-- The right small-homology map in components. -/
theorem SingularMayerVietoris.smallRightHomologyMap_components {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (a : SingularHomology U n × SingularHomology V n) :
    smallRightHomologyMap U V n a =
      homologyLinearMap
          ((CategoryTheory.Limits.biprod.inl :
              SingularChains.singularComplex U ⟶ middleComplex U V) ≫
            rightMap U V)
          n a.1 +
        homologyLinearMap
          ((CategoryTheory.Limits.biprod.inr :
              SingularChains.singularComplex V ⟶ middleComplex U V) ≫
            rightMap U V)
          n a.2 := by
  rw [inl_rightMap, inr_rightMap]
  exact biprodSequenceSecondMap_desc (toSmallLeft U V) (toSmallRight U V) n a

/-- The left small-homology map on a class. -/
theorem SingularMayerVietoris.smallLeftHomologyMap_apply {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (a : SingularHomology (U ∩ V : Set X) n) :
    smallLeftHomologyMap U V n a =
      (singularHomologyMap (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n a,
        -singularHomologyMap (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V)) n
            a) := by
  rw [smallLeftHomologyMap_components, leftMap_fst, leftMap_snd, homologyLinearMap_neg]
  rfl

/-- The right small-homology map on a class. -/
theorem SingularMayerVietoris.smallRightHomologyMap_apply {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (a : SingularHomology U n × SingularHomology V n) :
    smallRightHomologyMap U V n a =
      homologyLinearMap (toSmallLeft U V) n a.1 + homologyLinearMap (toSmallRight U V) n a.2 := by
  rw [smallRightHomologyMap_components, inl_rightMap, inr_rightMap]

/-- The comparison intertwines the right maps. -/
theorem SingularMayerVietoris.smallHomologyComparison_right {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (a : SingularHomology U n × SingularHomology V n) :
    smallHomologyComparison U V n (smallRightHomologyMap U V n a) =
      singularHomologyMap (subtypeInclusion U) n a.1 +
        singularHomologyMap (subtypeInclusion V) n a.2 := by
  rw [smallRightHomologyMap_apply, map_add]
  apply congrArg₂ (· + ·)
  · change
      homologyLinearMap (smallInclusion U V) n (homologyLinearMap (toSmallLeft U V) n a.1) = _
    rw [← LinearMap.comp_apply, ← homologyLinearMap_comp, toSmallLeft_inclusion]
  · change
      homologyLinearMap (smallInclusion U V) n (homologyLinearMap (toSmallRight U V) n a.2) = _
    rw [← LinearMap.comp_apply, ← homologyLinearMap_comp, toSmallRight_inclusion]

/-- The small sequence is exact at the intersection homology. -/
theorem SingularMayerVietoris.small_exact_at_intersection {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) :
    LinearMap.range (smallConnectingMap U V n) = LinearMap.ker (smallLeftHomologyMap U V n) :=
  biprodSequence_exact_at_leftHomology (chainSequence_shortExact U V) n

/-- The small sequence is exact at the pair homology. -/
theorem SingularMayerVietoris.small_exact_at_pair {X : Type} [TopologicalSpace X] (U V : Set X)
    (n : ℕ) :
    LinearMap.range (smallLeftHomologyMap U V n) = LinearMap.ker (smallRightHomologyMap U V n) :=
  biprodSequence_exact_at_middleHomology (chainSequence_shortExact U V) n

/-- The small sequence is exact at the small homology. -/
theorem SingularMayerVietoris.small_exact_at_smallHomology {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) :
    LinearMap.range (smallRightHomologyMap U V (n + 1)) =
      LinearMap.ker (smallConnectingMap U V n) :=
  biprodSequence_exact_at_rightHomology (chainSequence_shortExact U V) n

/-- The degree-zero right small map is surjective. -/
theorem SingularMayerVietoris.smallRightHomologyMap_zero_surjective {X : Type}
    [TopologicalSpace X] (U V : Set X) : Function.Surjective (smallRightHomologyMap U V 0) :=
  biprodSequence_second_zero_surjective (chainSequence_shortExact U V)

/-- The left map after the connecting map is zero. -/
theorem SingularMayerVietoris.smallLeftHomologyMap_comp_right {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) : (smallRightHomologyMap U V n).comp (smallLeftHomologyMap U V n) = 0 :=
  by
  apply LinearMap.ext
  intro a
  have ha : smallLeftHomologyMap U V n a ∈ LinearMap.range (smallLeftHomologyMap U V n) :=
    ⟨a, rfl⟩
  rw [small_exact_at_pair] at ha
  exact ha

/-- Transported exactness: the range is the kernel. -/
theorem SingularMayerVietoris.rightTransport_range_eq_ker {A P B C : Type*} [AddCommGroup A]
    [Module ℤ A] [AddCommGroup P] [Module ℤ P] [AddCommGroup B] [Module ℤ B] [AddCommGroup C]
    [Module ℤ C] (e : B ≃ₗ[ℤ] C) (g : P →ₗ[ℤ] B) (δ : B →ₗ[ℤ] A)
    (h : LinearMap.range g = LinearMap.ker δ) :
    LinearMap.range (e.toLinearMap.comp g) = LinearMap.ker (δ.comp e.symm.toLinearMap) := by
  ext c
  change (∃ p, e (g p) = c) ↔ δ (e.symm c) = 0
  constructor
  · rintro ⟨p, rfl⟩
    rw [LinearEquiv.symm_apply_apply]
    have hp : g p ∈ LinearMap.range g := ⟨p, rfl⟩
    rw [h] at hp
    exact hp
  · intro hc
    have hp : e.symm c ∈ LinearMap.range g := by
      rw [h]
      exact hc
    obtain ⟨p, hp⟩ := hp
    exact ⟨p, (congrArg e hp).trans (e.apply_symm_apply c)⟩

/-- The transported connecting range. -/
theorem SingularMayerVietoris.rightTransport_connecting_range {A B C : Type*} [AddCommGroup A]
    [Module ℤ A] [AddCommGroup B] [Module ℤ B] [AddCommGroup C] [Module ℤ C] (e : B ≃ₗ[ℤ] C)
    (δ : B →ₗ[ℤ] A) : LinearMap.range (δ.comp e.symm.toLinearMap) = LinearMap.range δ :=
  e.symm.range_comp δ

/-- The transported second map's kernel. -/
theorem SingularMayerVietoris.rightTransport_second_ker {P B C : Type*} [AddCommGroup P]
    [Module ℤ P] [AddCommGroup B] [Module ℤ B] [AddCommGroup C] [Module ℤ C] (e : B ≃ₗ[ℤ] C)
    (g : P →ₗ[ℤ] B) : LinearMap.ker (e.toLinearMap.comp g) = LinearMap.ker g :=
  e.ker_comp g

/-- The transported second map is surjective. -/
theorem SingularMayerVietoris.rightTransport_second_surjective {P B C : Type*} [AddCommGroup P]
    [Module ℤ P] [AddCommGroup B] [Module ℤ B] [AddCommGroup C] [Module ℤ C] (e : B ≃ₗ[ℤ] C)
    (g : P →ₗ[ℤ] B) (hg : Function.Surjective g) : Function.Surjective (e.toLinearMap.comp g) :=
  e.surjective.comp hg

/-! ### Affine simplices and the barycenter -/

/-- The affine simplex on a list of vertices. -/
def SingularMayerVietoris.affineSimplex {n p : ℕ} (v : Fin (n + 1) → SingularChains.Simplex p) :
    C(SingularChains.Simplex n, SingularChains.Simplex p)
    where
  toFun
    t :=
    ⟨∑ i, t i • (v i : Fin (p + 1) → ℝ),
      (convex_stdSimplex ℝ (Fin (p + 1))).sum_mem (fun i _ => stdSimplex.zero_le t i)
        (stdSimplex.sum_eq_one t) (fun i _ => (v i).property)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact
      continuous_finsetSum _
        (fun i _ => ((continuous_apply i).comp continuous_subtype_val).smul continuous_const)

/-- The affine simplex evaluates the convex combination. -/
@[simp]
theorem SingularMayerVietoris.affineSimplex_coordinate {n p : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p) (t : SingularChains.Simplex n) (j : Fin (p + 1)) :
    affineSimplex v t j = ∑ i, t i * v i j := by
  change (∑ i, t i • (v i : Fin (p + 1) → ℝ)) j = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- The affine simplex at a vertex. -/
@[simp]
theorem SingularMayerVietoris.affineSimplex_vertex {n p : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p) (i : Fin (n + 1)) :
    affineSimplex v (stdSimplex.vertex (S := ℝ) i) = v i := by
  apply Subtype.ext
  change
    (∑ j : Fin (n + 1), ((Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ) j) • (v j : Fin (p + 1) → ℝ)) =
      (v i : Fin (p + 1) → ℝ)
  simp [Pi.single_apply]

/-- The standard basis vertices of the simplex. -/
def SingularMayerVietoris.stdVertices (n : ℕ) : Fin (n + 1) → SingularChains.Simplex n :=
  stdSimplex.vertex

/-- The affine simplex on the standard vertices is the identity. -/
@[simp]
theorem SingularMayerVietoris.affineSimplex_stdVertices (n : ℕ) :
    affineSimplex (stdVertices n) = ContinuousMap.id (SingularChains.Simplex n) := by
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  funext j
  change (∑ i, t i • Pi.single i (1 : ℝ)) j = t j
  simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]

/-- The face of an affine simplex is affine on the deleted vertices. -/
theorem SingularMayerVietoris.affineSimplex_face {n p : ℕ}
    (v : Fin (n + 2) → SingularChains.Simplex p) (i : Fin (n + 2)) :
    (affineSimplex v).comp (SingularChains.simplexFace n i) =
      affineSimplex (fun j => v (i.succAbove j)) := by
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  change
    (∑ j : Fin (n + 2), SingularChains.simplexFace n i t j • (v j : Fin (p + 1) → ℝ)) =
      ∑ j : Fin (n + 1), t j • (v (i.succAbove j) : Fin (p + 1) → ℝ)
  rw [Fin.sum_univ_succAbove _ i]
  simp only [SingularChains.simplexFace_apply_self, zero_smul,
    SingularChains.simplexFace_apply_succAbove, zero_add]

/-- Affine simplices compose by vertex lists. -/
theorem SingularMayerVietoris.affineSimplex_comp {m n p : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p) (w : Fin (m + 1) → SingularChains.Simplex n) :
    (affineSimplex v).comp (affineSimplex w) = affineSimplex (fun j => affineSimplex v (w j)) := by
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  funext k
  change
    affineSimplex v (affineSimplex w t) k = affineSimplex (fun j => affineSimplex v (w j)) t k
  simp only [affineSimplex_coordinate, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- The affine simplex lands in the convex hull of its vertices. -/
theorem SingularMayerVietoris.affineSimplex_mem_convexHull {n p : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p) (t : SingularChains.Simplex n) :
    (affineSimplex v t : Fin (p + 1) → ℝ) ∈
      convexHull ℝ (Set.range fun i => (v i : Fin (p + 1) → ℝ)) := by
  change (∑ i, t i • (v i : Fin (p + 1) → ℝ)) ∈ _
  apply (convex_convexHull ℝ _).sum_mem
  · intro i _
    exact stdSimplex.zero_le t i
  · exact stdSimplex.sum_eq_one t
  · intro i _
    exact subset_convexHull ℝ _ (Set.mem_range_self i)

/-- The barycenter of the standard simplex. -/
def SingularMayerVietoris.simplexBarycenter {n p : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p) : SingularChains.Simplex p :=
  affineSimplex v (stdSimplex.barycenter : SingularChains.Simplex n)

/-- The barycenter's coordinates are all `1/(n+1)`. -/
theorem SingularMayerVietoris.simplexBarycenter_coe {n p : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p) :
    (simplexBarycenter v : Fin (p + 1) → ℝ) =
      ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ i, (v i : Fin (p + 1) → ℝ) := by
  change (∑ i, (Fintype.card (Fin (n + 1)) : ℝ)⁻¹ • (v i : Fin (p + 1) → ℝ)) = _
  simp only [Fintype.card_fin, Finset.smul_sum]

/-- The affine simplex sends the barycenter to the vertex average. -/
theorem SingularMayerVietoris.affineSimplex_simplexBarycenter {m n p : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p) (w : Fin (m + 1) → SingularChains.Simplex n) :
    affineSimplex v (simplexBarycenter w) = simplexBarycenter (fun j => affineSimplex v (w j)) :=
  ContinuousMap.congr_fun (affineSimplex_comp v w)
    (stdSimplex.barycenter : SingularChains.Simplex m)

/-! ### Formal chains -/

/-- Formal chains: finsupp chains on affine simplices. -/
abbrev SingularMayerVietoris.FormalChains (V : Type*) (n : ℕ) :=
  (Fin n → V) →₀ ℤ

/-- A formal simplex as a formal chain. -/
def SingularMayerVietoris.formalSimplex {V : Type*} {n : ℕ} (v : Fin n → V) : FormalChains V n :=
  Finsupp.single v 1

/-- A function on formal simplices lifted to formal chains. -/
def SingularMayerVietoris.formalLift {V M : Type*} {n : ℕ} [AddCommGroup M] [Module ℤ M]
    (f : (Fin n → V) → M) : FormalChains V n →ₗ[ℤ] M :=
  Finsupp.linearCombination ℤ f

/-- The formal lift computes the given value on a simplex. -/
@[simp]
theorem SingularMayerVietoris.formalLift_simplex {V M : Type*} {n : ℕ} [AddCommGroup M]
    [modM : Module ℤ M] (f : (Fin n → V) → M) (v : Fin n → V) :
    formalLift f (formalSimplex v) = f v := by
  exact (Finsupp.linearCombination_single ℤ 1 v).trans (modM.one_smul (f v))

/-- Formal-chain maps agreeing on simplices are equal. -/
theorem SingularMayerVietoris.formalChains_ext {V M : Type*} {n : ℕ} [AddCommGroup M] [Module ℤ M]
    {f g : FormalChains V n →ₗ[ℤ] M} (h : ∀ v, f (formalSimplex v) = g (formalSimplex v)) :
    f = g := by
  apply Finsupp.lhom_ext
  intro v z
  have hs : Finsupp.single v z = z • formalSimplex v := by
    simp [formalSimplex, Finsupp.smul_single]
  rw [hs, f.map_smul, g.map_smul, h]

/-- A vertex map induces a map of formal chains. -/
def SingularMayerVietoris.formalMap {V W : Type*} (f : V → W) (n : ℕ) :
    FormalChains V n →ₗ[ℤ] FormalChains W n :=
  Finsupp.lmapDomain ℤ ℤ (fun v => f ∘ v)

/-- The formal map applies the vertex map to a simplex. -/
@[simp]
theorem SingularMayerVietoris.formalMap_simplex {V W : Type*} (f : V → W) {n : ℕ}
    (v : Fin n → V) : formalMap f n (formalSimplex v) = formalSimplex (f ∘ v) := by
  simp [formalMap, formalSimplex]

/-- The cone of a formal simplex on a vertex. -/
def SingularMayerVietoris.formalCone {V : Type*} (a : V) (n : ℕ) :
    FormalChains V n →ₗ[ℤ] FormalChains V (n + 1) :=
  Finsupp.lmapDomain ℤ ℤ (fun v => Fin.cons a v)

/-- The cone prepends the vertex. -/
@[simp]
theorem SingularMayerVietoris.formalCone_simplex {V : Type*} (a : V) {n : ℕ} (v : Fin n → V) :
    formalCone a n (formalSimplex v) = formalSimplex (Fin.cons a v) := by
  simp [formalCone, formalSimplex]

/-- The formal boundary on affine simplices. -/
def SingularMayerVietoris.formalBoundary {V : Type*} (n : ℕ) :
    FormalChains V (n + 1) →ₗ[ℤ] FormalChains V n :=
  formalLift fun v => ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • formalSimplex (v ∘ i.succAbove)

/-- The formal boundary is the alternating face sum. -/
@[simp]
theorem SingularMayerVietoris.formalBoundary_simplex {V : Type*} (n : ℕ) (v : Fin (n + 1) → V) :
    formalBoundary n (formalSimplex v) =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • formalSimplex (v ∘ i.succAbove) :=
  formalLift_simplex _ _

/-- The boundary of a cone at degree zero. -/
theorem SingularMayerVietoris.formalBoundary_cone_zero {V : Type*} (a : V)
    (c : FormalChains V 0) : formalBoundary 0 (formalCone a 0 c) = c := by
  have h : (formalBoundary 0).comp (formalCone a 0) = LinearMap.id := by
    apply formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, formalCone_simplex, formalBoundary_simplex,
      LinearMap.id_apply]
    change
      (∑ i : Fin 1, (-1 : ℤ) ^ i.val • formalSimplex (Fin.cons a v ∘ i.succAbove)) =
        formalSimplex v
    simp only [Fin.sum_univ_one, Fin.val_zero, pow_zero, one_smul]
    congr 1
  exact LinearMap.congr_fun h c

/-- The cone is a chain contraction of the boundary. -/
theorem SingularMayerVietoris.formalBoundary_cone {V : Type*} (a : V) (n : ℕ)
    (c : FormalChains V (n + 1)) :
    formalBoundary (n + 1) (formalCone a (n + 1) c) = c - formalCone a n (formalBoundary n c) := by
  have h :
    (formalBoundary (n + 1)).comp (formalCone a (n + 1)) =
      LinearMap.id - (formalCone a n).comp (formalBoundary n) := by
    apply formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, formalCone_simplex,
      formalBoundary_simplex]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul]
    have hz : Fin.cons a v ∘ (0 : Fin (n + 2)).succAbove = v := by
      funext i
      simp
    rw [hz, sub_eq_add_neg]
    congr 1
    rw [map_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Fin.val_succ, pow_succ, mul_neg_one, neg_smul, Fin.cons_comp_succ_succAbove,
      map_smul, formalCone_simplex]
    rfl
  exact LinearMap.congr_fun h c

/-- The formal boundary squares to zero. -/
theorem SingularMayerVietoris.formalBoundary_comp {V : Type*} (n : ℕ) :
    (formalBoundary (V := V) n).comp (formalBoundary (n + 1)) = 0 := by
  induction n with
  | zero =>
    apply formalChains_ext
    intro v
    change formalBoundary 0 (formalBoundary 1 (formalSimplex v)) = 0
    have hv : formalSimplex v = formalCone (v 0) 1 (formalSimplex (Fin.tail v)) := by
      rw [formalCone_simplex, Fin.cons_self_tail]
    rw [hv, formalBoundary_cone, map_sub, formalBoundary_cone_zero, sub_self]
  | succ n ih =>
    apply formalChains_ext
    intro v
    change formalBoundary (n + 1) (formalBoundary (n + 2) (formalSimplex v)) = 0
    have hv : formalSimplex v = formalCone (v 0) (n + 2) (formalSimplex (Fin.tail v)) := by
      rw [formalCone_simplex, Fin.cons_self_tail]
    have hb := LinearMap.congr_fun ih (formalSimplex (Fin.tail v))
    change formalBoundary n (formalBoundary (n + 1) (formalSimplex (Fin.tail v))) = 0 at hb
    rw [hv, formalBoundary_cone, map_sub, formalBoundary_cone, hb, map_zero, sub_zero, sub_self]

/-- The formal boundary is a chain-map identity. -/
@[simp]
theorem SingularMayerVietoris.formalBoundary_boundary {V : Type*} (n : ℕ)
    (c : FormalChains V (n + 2)) : formalBoundary n (formalBoundary (n + 1) c) = 0 :=
  LinearMap.congr_fun (formalBoundary_comp n) c

/-- The formal map commutes with the boundary. -/
theorem SingularMayerVietoris.formalMap_boundary {V W : Type*} (f : V → W) (n : ℕ)
    (c : FormalChains V (n + 1)) :
    formalMap f n (formalBoundary n c) = formalBoundary n (formalMap f (n + 1) c) := by
  have h :
    (formalMap f n).comp (formalBoundary n) = (formalBoundary n).comp (formalMap f (n + 1)) := by
    apply formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, formalBoundary_simplex, map_sum, map_smul, formalMap_simplex,
      Function.comp_assoc]
  exact LinearMap.congr_fun h c

/-- The formal map commutes with the cone. -/
theorem SingularMayerVietoris.formalMap_cone {V W : Type*} (f : V → W) (a : V) (n : ℕ)
    (c : FormalChains V n) :
    formalMap f (n + 1) (formalCone a n c) = formalCone (f a) n (formalMap f n c) := by
  have h :
    (formalMap f (n + 1)).comp (formalCone a n) = (formalCone (f a) n).comp (formalMap f n) := by
    apply formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, formalCone_simplex, formalMap_simplex]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  exact LinearMap.congr_fun h c

/-! ### Barycentric subdivision -/

/-- A center assignment for coning formal simplices. -/
abbrev SingularMayerVietoris.FormalCenter (V : Type*) :=
  ∀ n : ℕ, (Fin (n + 1) → V) → V

/-- The barycentric subdivision of a formal chain. -/
def SingularMayerVietoris.formalSubdivision {V : Type*} (center : FormalCenter V) :
    (n : ℕ) → FormalChains V n →ₗ[ℤ] FormalChains V n
  | 0 => LinearMap.id
  | n + 1 =>
    formalLift fun v =>
      formalCone (center n v) n (formalSubdivision center n (formalBoundary n (formalSimplex v)))

/-- Subdivision of a 0-simplex is the simplex. -/
@[simp]
theorem SingularMayerVietoris.formalSubdivision_zero {V : Type*} (center : FormalCenter V)
    (c : FormalChains V 0) : formalSubdivision center 0 c = c :=
  rfl

/-- Subdivision of a simplex is the cone of the boundary subdivision. -/
@[simp]
theorem SingularMayerVietoris.formalSubdivision_simplex_succ {V : Type*} (center : FormalCenter V)
    (n : ℕ) (v : Fin (n + 1) → V) :
    formalSubdivision center (n + 1) (formalSimplex v) =
      formalCone (center n v) n
        (formalSubdivision center n (formalBoundary n (formalSimplex v))) :=
  formalLift_simplex _ _

/-- Subdivision is a chain map. -/
theorem SingularMayerVietoris.formalBoundary_subdivision {V : Type*} (center : FormalCenter V) :
    ∀ (n : ℕ) (c : FormalChains V (n + 1)),
      formalBoundary n (formalSubdivision center (n + 1) c) =
        formalSubdivision center n (formalBoundary n c) := by
  intro n
  induction n with
  | zero =>
    intro c
    have h :
      (formalBoundary 0).comp (formalSubdivision center 1) =
        (formalSubdivision center 0).comp (formalBoundary 0) := by
      apply formalChains_ext
      intro v
      simp only [LinearMap.comp_apply, formalSubdivision_simplex_succ, formalBoundary_cone_zero]
    exact LinearMap.congr_fun h c
  | succ n ih =>
    intro c
    have h :
      (formalBoundary (n + 1)).comp (formalSubdivision center (n + 2)) =
        (formalSubdivision center (n + 1)).comp (formalBoundary (n + 1)) := by
      apply formalChains_ext
      intro v
      simp only [LinearMap.comp_apply, formalSubdivision_simplex_succ]
      rw [formalBoundary_cone, ih, formalBoundary_boundary, map_zero, map_zero, sub_zero]
    exact LinearMap.congr_fun h c

/-- The formal map commutes with subdivision. -/
theorem SingularMayerVietoris.formalMap_subdivision {V W : Type*} (center : FormalCenter V)
    (center' : FormalCenter W) (f : V → W) (hf : ∀ n v, f (center n v) = center' n (f ∘ v)) :
    ∀ (n : ℕ) (c : FormalChains V n),
      formalMap f n (formalSubdivision center n c) =
        formalSubdivision center' n (formalMap f n c) := by
  intro n
  induction n with
  | zero => intro c; rfl
  | succ n ih =>
    intro c
    have h :
      (formalMap f (n + 1)).comp (formalSubdivision center (n + 1)) =
        (formalSubdivision center' (n + 1)).comp (formalMap f (n + 1)) := by
      apply formalChains_ext
      intro v
      simp only [LinearMap.comp_apply, formalSubdivision_simplex_succ, formalMap_simplex]
      rw [formalMap_cone, ih, formalMap_boundary, formalMap_simplex, hf]
    exact LinearMap.congr_fun h c

/-! ### The affine chain map -/

/-- The barycenter of an affine simplex. -/
def SingularMayerVietoris.simplexCenter (p : ℕ) : FormalCenter (SingularChains.Simplex p) :=
  fun _ v => simplexBarycenter v

/-- The chain map realizing formal chains as singular chains. -/
def SingularMayerVietoris.affineChainMap (p n : ℕ) :
    FormalChains (SingularChains.Simplex p) (n + 1) →ₗ[ℤ]
      SingularChains.Chains (SingularChains.Simplex p) n :=
  formalLift fun v => SingularChains.simplexChain (SingularChains.Simplex p) n (affineSimplex v)

/-- The affine chain map sends a formal simplex to its affine simplex. -/
@[simp]
theorem SingularMayerVietoris.affineChainMap_simplex (p n : ℕ)
    (v : Fin (n + 1) → SingularChains.Simplex p) :
    affineChainMap p n (formalSimplex v) =
      SingularChains.simplexChain (SingularChains.Simplex p) n (affineSimplex v) :=
  formalLift_simplex _ _

/-- The affine chain map commutes with the boundary. -/
theorem SingularMayerVietoris.affineChainMap_boundary (p n : ℕ)
    (c : FormalChains (SingularChains.Simplex p) (n + 2)) :
    ((SingularChains.singularComplex (SingularChains.Simplex p)).d (n + 1) n).hom
        (affineChainMap p (n + 1) c) =
      affineChainMap p n (formalBoundary (n + 1) c) := by
  have h :
    (((SingularChains.singularComplex (SingularChains.Simplex p)).d (n + 1) n).hom).comp
        (affineChainMap p (n + 1)) =
      (affineChainMap p n).comp (formalBoundary (n + 1)) := by
    apply formalChains_ext
    intro v
    change
      ((SingularChains.singularComplex (SingularChains.Simplex p)).d (n + 1) n).hom
          (affineChainMap p (n + 1) (formalSimplex v)) =
        _
    rw [affineChainMap_simplex, SingularChains.boundary_simplex]
    change _ = affineChainMap p n (formalBoundary (n + 1) (formalSimplex v))
    rw [formalBoundary_simplex, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_zsmul, affineChainMap_simplex, affineSimplex_face]
    rfl
  exact LinearMap.congr_fun h c

/-- The induced chain of an affine chain map. -/
theorem SingularMayerVietoris.inducedChain_affineChainMap {m n p : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p)
    (c : FormalChains (SingularChains.Simplex n) (m + 1)) :
    SingularChains.inducedChain (affineSimplex v) m (affineChainMap n m c) =
      affineChainMap p m (formalMap (affineSimplex v) (m + 1) c) := by
  have h :
    (SingularChains.inducedChain (affineSimplex v) m).comp (affineChainMap n m) =
      (affineChainMap p m).comp (formalMap (affineSimplex v) (m + 1)) := by
    apply formalChains_ext
    intro w
    simp only [LinearMap.comp_apply, affineChainMap_simplex, SingularChains.inducedChain_simplex,
      formalMap_simplex, affineSimplex_comp]
    rfl
  exact LinearMap.congr_fun h c

/-- The affine chain of the standard simplex is the identity simplex. -/
@[simp]
theorem SingularMayerVietoris.affineChainMap_stdVertices (n : ℕ) :
    affineChainMap n n (formalSimplex (stdVertices n)) =
      SingularChains.simplexChain (SingularChains.Simplex n) n
        (ContinuousMap.id (SingularChains.Simplex n)) := by
  rw [affineChainMap_simplex, affineSimplex_stdVertices]

/-- The affine map preserves the barycenter. -/
theorem SingularMayerVietoris.affineSimplex_preserves_center {n p : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p) (m : ℕ)
    (w : Fin (m + 1) → SingularChains.Simplex n) :
    affineSimplex v (simplexCenter n m w) = simplexCenter p m (affineSimplex v ∘ w) :=
  affineSimplex_simplexBarycenter v w

/-- The formal chain homotopy between subdivision and identity. -/
def SingularMayerVietoris.formalSubdivisionHomotopy {V : Type*} (center : FormalCenter V) :
    (n : ℕ) → FormalChains V n →ₗ[ℤ] FormalChains V (n + 1)
  | 0 => 0
  | n + 1 =>
    formalLift fun v =>
      formalCone (v 0) (n + 1)
        (formalSimplex v - formalSubdivision center (n + 1) (formalSimplex v) -
          formalSubdivisionHomotopy center n (formalBoundary n (formalSimplex v)))

/-- The subdivision homotopy in degree zero. -/
@[simp]
theorem SingularMayerVietoris.formalSubdivisionHomotopy_zero {V : Type*} (center : FormalCenter V)
    (c : FormalChains V 0) : formalSubdivisionHomotopy center 0 c = 0 :=
  rfl

/-- The subdivision homotopy on a simplex. -/
@[simp]
theorem SingularMayerVietoris.formalSubdivisionHomotopy_simplex_succ {V : Type*}
    (center : FormalCenter V) (n : ℕ) (v : Fin (n + 1) → V) :
    formalSubdivisionHomotopy center (n + 1) (formalSimplex v) =
      formalCone (v 0) (n + 1)
        (formalSimplex v - formalSubdivision center (n + 1) (formalSimplex v) -
          formalSubdivisionHomotopy center n (formalBoundary n (formalSimplex v))) :=
  formalLift_simplex _ _

/-- The subdivision homotopy satisfies the chain-homotopy identity. -/
theorem SingularMayerVietoris.formalSubdivisionHomotopy_boundary {V : Type*}
    (center : FormalCenter V) :
    ∀ (n : ℕ) (c : FormalChains V (n + 1)),
      formalBoundary (n + 1) (formalSubdivisionHomotopy center (n + 1) c) +
          formalSubdivisionHomotopy center n (formalBoundary n c) =
        c - formalSubdivision center (n + 1) c := by
  intro n
  induction n with
  | zero =>
    intro c
    have h :
      (formalBoundary 1).comp (formalSubdivisionHomotopy center 1) +
          (formalSubdivisionHomotopy center 0).comp (formalBoundary 0) =
        LinearMap.id - formalSubdivision center 1 := by
      apply formalChains_ext
      intro v
      change
        formalBoundary 1 (formalSubdivisionHomotopy center 1 (formalSimplex v)) +
            formalSubdivisionHomotopy center 0 (formalBoundary 0 (formalSimplex v)) =
          formalSimplex v - formalSubdivision center 1 (formalSimplex v)
      have hc :
        formalBoundary 0
            (formalSimplex v - formalSubdivision center 1 (formalSimplex v) -
              formalSubdivisionHomotopy center 0 (formalBoundary 0 (formalSimplex v))) =
          0 := by
        simp only [map_sub, formalBoundary_subdivision, formalSubdivision_zero,
          formalSubdivisionHomotopy_zero, sub_self, sub_zero]
      rw [formalSubdivisionHomotopy_simplex_succ, formalBoundary_cone, hc, map_zero, sub_zero,
        sub_add_cancel]
    exact LinearMap.congr_fun h c
  | succ n ih =>
    intro c
    have h :
      (formalBoundary (n + 2)).comp (formalSubdivisionHomotopy center (n + 2)) +
          (formalSubdivisionHomotopy center (n + 1)).comp (formalBoundary (n + 1)) =
        LinearMap.id - formalSubdivision center (n + 2) := by
      apply formalChains_ext
      intro v
      change
        formalBoundary (n + 2) (formalSubdivisionHomotopy center (n + 2) (formalSimplex v)) +
            formalSubdivisionHomotopy center (n + 1) (formalBoundary (n + 1) (formalSimplex v)) =
          formalSimplex v - formalSubdivision center (n + 2) (formalSimplex v)
      have hp :
        formalBoundary (n + 1)
            (formalSubdivisionHomotopy center (n + 1)
              (formalBoundary (n + 1) (formalSimplex v))) =
          formalBoundary (n + 1) (formalSimplex v) -
            formalSubdivision center (n + 1) (formalBoundary (n + 1) (formalSimplex v)) := by
        simpa only [formalBoundary_boundary, map_zero, add_zero] using
          ih (formalBoundary (n + 1) (formalSimplex v))
      have hc :
        formalBoundary (n + 1)
            (formalSimplex v - formalSubdivision center (n + 2) (formalSimplex v) -
              formalSubdivisionHomotopy center (n + 1)
                (formalBoundary (n + 1) (formalSimplex v))) =
          0 := by rw [map_sub, map_sub, formalBoundary_subdivision, hp, sub_self]
      rw [formalSubdivisionHomotopy_simplex_succ, formalBoundary_cone, hc, map_zero, sub_zero,
        sub_add_cancel]
    exact LinearMap.congr_fun h c

/-- The formal map commutes with the subdivision homotopy. -/
theorem SingularMayerVietoris.formalMap_subdivisionHomotopy {V W : Type*}
    (center : FormalCenter V) (center' : FormalCenter W) (f : V → W)
    (hf : ∀ n v, f (center n v) = center' n (f ∘ v)) :
    ∀ (n : ℕ) (c : FormalChains V n),
      formalMap f (n + 1) (formalSubdivisionHomotopy center n c) =
        formalSubdivisionHomotopy center' n (formalMap f n c) := by
  intro n
  induction n with
  | zero => intro c; simp
  | succ n ih =>
    intro c
    have h :
      (formalMap f (n + 2)).comp (formalSubdivisionHomotopy center (n + 1)) =
        (formalSubdivisionHomotopy center' (n + 1)).comp (formalMap f (n + 1)) := by
      apply formalChains_ext
      intro v
      simp only [LinearMap.comp_apply, formalSubdivisionHomotopy_simplex_succ, formalMap_simplex]
      rw [formalMap_cone]
      congr 1
      rw [map_sub, map_sub, formalMap_simplex, formalMap_subdivision center center' f hf, ih,
        formalMap_boundary, formalMap_simplex]
    exact LinearMap.congr_fun h c

/-- Iterated subdivision remains a chain map. -/
theorem SingularMayerVietoris.formalBoundary_subdivision_iterate {V : Type*}
    (center : FormalCenter V) (k n : ℕ) (c : FormalChains V (n + 1)) :
    formalBoundary n ((formalSubdivision center (n + 1))^[k] c) =
      (formalSubdivision center n)^[k] (formalBoundary n c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', formalBoundary_subdivision,
      ih]

/-- The formal map commutes with iterated subdivision. -/
theorem SingularMayerVietoris.formalMap_subdivision_iterate {V W : Type*}
    (center : FormalCenter V) (center' : FormalCenter W) (f : V → W)
    (hf : ∀ n v, f (center n v) = center' n (f ∘ v)) (k n : ℕ) (c : FormalChains V n) :
    formalMap f n ((formalSubdivision center n)^[k] c) =
      (formalSubdivision center' n)^[k] (formalMap f n c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      formalMap_subdivision center center' f hf, ih]

/-- The homotopy between iterated subdivision and identity. -/
def SingularMayerVietoris.formalSubdivisionIteratedHomotopy {V : Type*} (center : FormalCenter V)
    (k n : ℕ) : FormalChains V n →ₗ[ℤ] FormalChains V (n + 1) :=
  ∑ j ∈ Finset.range k,
    (formalSubdivisionHomotopy center n).comp ((formalSubdivision center n) ^ j)

/-- The iterated homotopy computes on a chain. -/
theorem SingularMayerVietoris.formalSubdivisionIteratedHomotopy_apply {V : Type*}
    (center : FormalCenter V) (k n : ℕ) (c : FormalChains V n) :
    formalSubdivisionIteratedHomotopy center k n c =
      ∑ j ∈ Finset.range k,
        formalSubdivisionHomotopy center n ((formalSubdivision center n)^[j] c) := by
  simp only [formalSubdivisionIteratedHomotopy, LinearMap.sum_apply, LinearMap.comp_apply,
    Module.End.pow_apply]

/-- The iterated homotopy in degree zero. -/
@[simp]
theorem SingularMayerVietoris.formalSubdivisionIteratedHomotopy_zero {V : Type*}
    (center : FormalCenter V) (n : ℕ) (c : FormalChains V n) :
    formalSubdivisionIteratedHomotopy center 0 n c = 0 := by
  simp [formalSubdivisionIteratedHomotopy]

/-- The iterated homotopy recursion. -/
theorem SingularMayerVietoris.formalSubdivisionIteratedHomotopy_succ {V : Type*}
    (center : FormalCenter V) (k n : ℕ) (c : FormalChains V n) :
    formalSubdivisionIteratedHomotopy center (k + 1) n c =
      formalSubdivisionIteratedHomotopy center k n c +
        formalSubdivisionHomotopy center n ((formalSubdivision center n)^[k] c) := by
  simp only [formalSubdivisionIteratedHomotopy_apply, Finset.sum_range_succ]

/-- The iterated homotopy is zero in degree zero. -/
@[simp]
theorem SingularMayerVietoris.formalSubdivisionIteratedHomotopy_degree_zero {V : Type*}
    (center : FormalCenter V) (k : ℕ) (c : FormalChains V 0) :
    formalSubdivisionIteratedHomotopy center k 0 c = 0 := by
  simp [formalSubdivisionIteratedHomotopy_apply]

/-- The iterated homotopy satisfies the chain-homotopy identity. -/
theorem SingularMayerVietoris.formalSubdivisionIteratedHomotopy_boundary {V : Type*}
    (center : FormalCenter V) (k n : ℕ) (c : FormalChains V (n + 1)) :
    formalBoundary (n + 1) (formalSubdivisionIteratedHomotopy center k (n + 1) c) +
        formalSubdivisionIteratedHomotopy center k n (formalBoundary n c) =
      c - (formalSubdivision center (n + 1))^[k] c := by
  induction k with
  | zero => simp
  | succ k
    ih =>
    rw [formalSubdivisionIteratedHomotopy_succ, formalSubdivisionIteratedHomotopy_succ, map_add]
    have hh :=
      formalSubdivisionHomotopy_boundary center n ((formalSubdivision center (n + 1))^[k] c)
    rw [formalBoundary_subdivision_iterate] at hh
    calc
      _ =
          (formalBoundary (n + 1) (formalSubdivisionIteratedHomotopy center k (n + 1) c) +
              formalSubdivisionIteratedHomotopy center k n (formalBoundary n c)) +
            (formalBoundary (n + 1)
                (formalSubdivisionHomotopy center (n + 1)
                  ((formalSubdivision center (n + 1))^[k] c)) +
              formalSubdivisionHomotopy center n
                ((formalSubdivision center n)^[k] (formalBoundary n c))) := by abel
      _ =
          (c - (formalSubdivision center (n + 1))^[k] c) +
            ((formalSubdivision center (n + 1))^[k] c -
              formalSubdivision center (n + 1) ((formalSubdivision center (n + 1))^[k] c)) := by
        rw [ih, hh]
      _ = c - (formalSubdivision center (n + 1))^[k + 1] c := by
        rw [Function.iterate_succ_apply']
        abel

/-- The formal map commutes with the iterated homotopy. -/
theorem SingularMayerVietoris.formalMap_subdivisionIteratedHomotopy {V W : Type*}
    (center : FormalCenter V) (center' : FormalCenter W) (f : V → W)
    (hf : ∀ n v, f (center n v) = center' n (f ∘ v)) (k n : ℕ) (c : FormalChains V n) :
    formalMap f (n + 1) (formalSubdivisionIteratedHomotopy center k n c) =
      formalSubdivisionIteratedHomotopy center' k n (formalMap f n c) := by
  simp only [formalSubdivisionIteratedHomotopy_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [formalMap_subdivisionHomotopy center center' f hf,
    formalMap_subdivision_iterate center center' f hf]

/-- Barycentric subdivision as an iterated chain map: the `k`-fold subdivision of an `n`-chain (Hatcher, Algebraic Topology, barycentric subdivision operator `Sd_k`). -/
def SingularMayerVietoris.subdivision (X : Type) [TopologicalSpace X] (k n : ℕ) :
    SingularChains.Chains X n →ₗ[ℤ] SingularChains.Chains X n :=
  SingularChains.chainLift X n fun σ =>
    SingularChains.inducedChain σ n
      (affineChainMap n n
        ((formalSubdivision (simplexCenter n) (n + 1))^[k] (formalSimplex (stdVertices n))))

/-- The singular subdivision of a simplex. -/
@[simp]
theorem SingularMayerVietoris.subdivision_simplex (X : Type) [TopologicalSpace X] (k n : ℕ)
    (σ : SingularChains.SingularSimplex X n) :
    subdivision X k n (SingularChains.simplexChain X n σ) =
      SingularChains.inducedChain σ n
        (affineChainMap n n
          ((formalSubdivision (simplexCenter n) (n + 1))^[k] (formalSimplex (stdVertices n)))) :=
  SingularChains.chainLift_simplex X n _ σ

/-- The induced chain of a subdivision. -/
theorem SingularMayerVietoris.inducedChain_subdivision {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (k n : ℕ) (c : SingularChains.Chains X n) :
    SingularChains.inducedChain f n (subdivision X k n c) =
      subdivision Y k n (SingularChains.inducedChain f n c) := by
  have h :
    (SingularChains.inducedChain f n).comp (subdivision X k n) =
      (subdivision Y k n).comp (SingularChains.inducedChain f n) := by
    apply SingularChains.chainMap_ext X n
    intro σ
    simp only [LinearMap.comp_apply, subdivision_simplex, SingularChains.inducedChain_simplex]
    rw [SingularChains.inducedChain_comp]
    rfl
  exact LinearMap.congr_fun h c

/-- An affine simplex is the affine map of the standard vertices. -/
theorem SingularMayerVietoris.affineSimplex_comp_stdVertices {n p : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p) : affineSimplex v ∘ stdVertices n = v := by
  funext i
  exact affineSimplex_vertex v i

/-- Subdivision commutes with the affine chain map. -/
theorem SingularMayerVietoris.subdivision_affineChainMap (p k n : ℕ)
    (c : FormalChains (SingularChains.Simplex p) (n + 1)) :
    subdivision (SingularChains.Simplex p) k n (affineChainMap p n c) =
      affineChainMap p n ((formalSubdivision (simplexCenter p) (n + 1))^[k] c) := by
  have h :
    (subdivision (SingularChains.Simplex p) k n).comp (affineChainMap p n) =
      (affineChainMap p n).comp ((formalSubdivision (simplexCenter p) (n + 1)) ^ k) := by
    apply formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, affineChainMap_simplex, subdivision_simplex,
      Module.End.pow_apply]
    rw [inducedChain_affineChainMap,
      formalMap_subdivision_iterate (simplexCenter n) (simplexCenter p) (affineSimplex v)
        (affineSimplex_preserves_center v),
      formalMap_simplex, affineSimplex_comp_stdVertices]
  simpa only [LinearMap.comp_apply, Module.End.pow_apply] using LinearMap.congr_fun h c

/-- Subdivision commutes with the boundary operator: `bd (Sd_k c) = Sd_k (bd c)` (Hatcher, Algebraic Topology, the chain-map property of subdivision). -/
theorem SingularMayerVietoris.subdivision_boundary {X : Type} [TopologicalSpace X] (k n : ℕ)
    (c : SingularChains.Chains X (n + 1)) :
    ((SingularChains.singularComplex X).d (n + 1) n).hom (subdivision X k (n + 1) c) =
      subdivision X k n (((SingularChains.singularComplex X).d (n + 1) n).hom c) := by
  have h :
    (((SingularChains.singularComplex X).d (n + 1) n).hom).comp (subdivision X k (n + 1)) =
      (subdivision X k n).comp ((SingularChains.singularComplex X).d (n + 1) n).hom := by
    apply SingularChains.chainMap_ext X (n + 1)
    intro σ
    change
      ((SingularChains.singularComplex X).d (n + 1) n).hom
          (subdivision X k (n + 1) (SingularChains.simplexChain X (n + 1) σ)) =
        _
    rw [subdivision_simplex, ← SingularChains.inducedChain_boundary, affineChainMap_boundary,
      formalBoundary_subdivision_iterate, ← subdivision_affineChainMap, inducedChain_subdivision,
      ← affineChainMap_boundary, SingularChains.inducedChain_boundary, affineChainMap_stdVertices,
      SingularChains.inducedChain_simplex, ContinuousMap.comp_id]
    rfl
  exact LinearMap.congr_fun h c

/-- The chain homotopy between a chain and its subdivision: `Sd_k` is chain homotopic to the identity, the key to smallness after subdivision (Hatcher, Algebraic Topology, proof of Theorem 2.20). -/
def SingularMayerVietoris.subdivisionHomotopy (X : Type) [TopologicalSpace X] (k n : ℕ) :
    SingularChains.Chains X n →ₗ[ℤ] SingularChains.Chains X (n + 1) :=
  SingularChains.chainLift X n fun σ =>
    SingularChains.inducedChain σ (n + 1)
      (affineChainMap n (n + 1)
        (formalSubdivisionIteratedHomotopy (simplexCenter n) k (n + 1)
          (formalSimplex (stdVertices n))))

/-- The singular subdivision homotopy on a simplex. -/
@[simp]
theorem SingularMayerVietoris.subdivisionHomotopy_simplex (X : Type) [TopologicalSpace X]
    (k n : ℕ) (σ : SingularChains.SingularSimplex X n) :
    subdivisionHomotopy X k n (SingularChains.simplexChain X n σ) =
      SingularChains.inducedChain σ (n + 1)
        (affineChainMap n (n + 1)
          (formalSubdivisionIteratedHomotopy (simplexCenter n) k (n + 1)
            (formalSimplex (stdVertices n)))) :=
  SingularChains.chainLift_simplex X n _ σ

/-- The induced chain of the subdivision homotopy. -/
theorem SingularMayerVietoris.inducedChain_subdivisionHomotopy {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (k n : ℕ) (c : SingularChains.Chains X n) :
    SingularChains.inducedChain f (n + 1) (subdivisionHomotopy X k n c) =
      subdivisionHomotopy Y k n (SingularChains.inducedChain f n c) := by
  have h :
    (SingularChains.inducedChain f (n + 1)).comp (subdivisionHomotopy X k n) =
      (subdivisionHomotopy Y k n).comp (SingularChains.inducedChain f n) := by
    apply SingularChains.chainMap_ext X n
    intro σ
    simp only [LinearMap.comp_apply, subdivisionHomotopy_simplex,
      SingularChains.inducedChain_simplex]
    rw [SingularChains.inducedChain_comp]
    rfl
  exact LinearMap.congr_fun h c

/-- The subdivision homotopy commutes with the affine chain map. -/
theorem SingularMayerVietoris.subdivisionHomotopy_affineChainMap (p k n : ℕ)
    (c : FormalChains (SingularChains.Simplex p) (n + 1)) :
    subdivisionHomotopy (SingularChains.Simplex p) k n (affineChainMap p n c) =
      affineChainMap p (n + 1)
        (formalSubdivisionIteratedHomotopy (simplexCenter p) k (n + 1) c) := by
  have h :
    (subdivisionHomotopy (SingularChains.Simplex p) k n).comp (affineChainMap p n) =
      (affineChainMap p (n + 1)).comp
        (formalSubdivisionIteratedHomotopy (simplexCenter p) k (n + 1)) := by
    apply formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, affineChainMap_simplex, subdivisionHomotopy_simplex]
    rw [inducedChain_affineChainMap,
      formalMap_subdivisionIteratedHomotopy (simplexCenter n) (simplexCenter p) (affineSimplex v)
        (affineSimplex_preserves_center v),
      formalMap_simplex, affineSimplex_comp_stdVertices]
  exact LinearMap.congr_fun h c

/-- The degree-zero boundary of the conjugated homotopy. -/
theorem SingularMayerVietoris.subdivisionHomotopy_boundary_zero_affineChainMap (p k : ℕ)
    (c : FormalChains (SingularChains.Simplex p) 1) :
    ((SingularChains.singularComplex (SingularChains.Simplex p)).d 1 0).hom
        (subdivisionHomotopy (SingularChains.Simplex p) k 0 (affineChainMap p 0 c)) =
      affineChainMap p 0 c - subdivision (SingularChains.Simplex p) k 0 (affineChainMap p 0 c) := by
  rw [subdivisionHomotopy_affineChainMap, affineChainMap_boundary, subdivision_affineChainMap, ←
    map_sub]
  apply congrArg (affineChainMap p 0)
  simpa only [formalSubdivisionIteratedHomotopy_degree_zero, add_zero] using
    formalSubdivisionIteratedHomotopy_boundary (simplexCenter p) k 0 c

/-- The boundary of the conjugated subdivision homotopy. -/
theorem SingularMayerVietoris.subdivisionHomotopy_boundary_affineChainMap (p k n : ℕ)
    (c : FormalChains (SingularChains.Simplex p) (n + 2)) :
    ((SingularChains.singularComplex (SingularChains.Simplex p)).d (n + 2) (n + 1)).hom
          (subdivisionHomotopy (SingularChains.Simplex p) k (n + 1) (affineChainMap p (n + 1) c)) +
        subdivisionHomotopy (SingularChains.Simplex p) k n
          (((SingularChains.singularComplex (SingularChains.Simplex p)).d (n + 1) n).hom
            (affineChainMap p (n + 1) c)) =
      affineChainMap p (n + 1) c -
        subdivision (SingularChains.Simplex p) k (n + 1) (affineChainMap p (n + 1) c) := by
  rw [subdivisionHomotopy_affineChainMap, affineChainMap_boundary, affineChainMap_boundary,
    subdivisionHomotopy_affineChainMap, subdivision_affineChainMap, ← map_add, ← map_sub]
  exact
    congrArg (affineChainMap p (n + 1))
      (formalSubdivisionIteratedHomotopy_boundary (simplexCenter p) k (n + 1) c)

/-- The subdivision homotopy boundary in degree zero. -/
theorem SingularMayerVietoris.subdivisionHomotopy_boundary_zero {X : Type} [TopologicalSpace X]
    (k : ℕ) (c : SingularChains.Chains X 0) :
    ((SingularChains.singularComplex X).d 1 0).hom (subdivisionHomotopy X k 0 c) =
      c - subdivision X k 0 c := by
  have h :
    (((SingularChains.singularComplex X).d 1 0).hom).comp (subdivisionHomotopy X k 0) =
      LinearMap.id - subdivision X k 0 := by
    apply SingularChains.chainMap_ext X 0
    intro σ
    have hstd :=
      subdivisionHomotopy_boundary_zero_affineChainMap 0 k (formalSimplex (stdVertices 0))
    have hσ := congrArg (SingularChains.inducedChain σ 0) hstd
    simpa only [map_sub, SingularChains.inducedChain_boundary, inducedChain_subdivisionHomotopy,
      inducedChain_subdivision, affineChainMap_stdVertices, SingularChains.inducedChain_simplex,
      ContinuousMap.comp_id, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] using
      hσ
  exact LinearMap.congr_fun h c

/-- The subdivision homotopy satisfies `∂h + h∂ = sd − id`. -/
theorem SingularMayerVietoris.subdivisionHomotopy_boundary {X : Type} [TopologicalSpace X]
    (k n : ℕ) (c : SingularChains.Chains X (n + 1)) :
    ((SingularChains.singularComplex X).d (n + 2) (n + 1)).hom
          (subdivisionHomotopy X k (n + 1) c) +
        subdivisionHomotopy X k n (((SingularChains.singularComplex X).d (n + 1) n).hom c) =
      c - subdivision X k (n + 1) c := by
  have h :
    (((SingularChains.singularComplex X).d (n + 2) (n + 1)).hom).comp
          (subdivisionHomotopy X k (n + 1)) +
        (subdivisionHomotopy X k n).comp (((SingularChains.singularComplex X).d (n + 1) n).hom) =
      LinearMap.id - subdivision X k (n + 1) := by
    apply SingularChains.chainMap_ext X (n + 1)
    intro σ
    have hstd :=
      subdivisionHomotopy_boundary_affineChainMap (n + 1) k n
        (formalSimplex (stdVertices (n + 1)))
    have hσ := congrArg (SingularChains.inducedChain σ (n + 1)) hstd
    simpa only [map_add, map_sub, SingularChains.inducedChain_boundary,
      inducedChain_subdivisionHomotopy, inducedChain_subdivision, affineChainMap_stdVertices,
      SingularChains.inducedChain_simplex, ContinuousMap.comp_id, LinearMap.comp_apply,
      LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply] using hσ
  exact LinearMap.congr_fun h c

/-- On a cycle the homotopy boundary is `sd − id`. -/
theorem SingularMayerVietoris.subdivisionHomotopy_boundary_of_cycle {X : Type}
    [TopologicalSpace X] (k n : ℕ) (c : SingularChains.Chains X n)
    (hc : ((SingularChains.singularComplex X).d n (n - 1)).hom c = 0) :
    ((SingularChains.singularComplex X).d (n + 1) n).hom (subdivisionHomotopy X k n c) =
      c - subdivision X k n c := by
  cases n with
  | zero => exact subdivisionHomotopy_boundary_zero k c
  | succ
    n =>
    have hc' : ((SingularChains.singularComplex X).d (n + 1) n).hom c = 0 := by
      simpa only [Nat.succ_sub_one] using hc
    simpa only [hc', map_zero, add_zero] using subdivisionHomotopy_boundary k n c

/-! ### Supported formal chains -/

/-- The formal chains supported on a vertex set. -/
def SingularMayerVietoris.formalChainsSupported {V : Type*} (S : Set V) (n : ℕ) :
    Submodule ℤ (FormalChains V n) :=
  Finsupp.supported ℤ ℤ {v | ∀ i, v i ∈ S}

/-- A formal chain is supported exactly when its support is. -/
theorem SingularMayerVietoris.mem_formalChainsSupported_iff {V : Type*} {n : ℕ} {S : Set V}
    {c : FormalChains V n} : c ∈ formalChainsSupported S n ↔ ∀ v ∈ c.support, ∀ i, v i ∈ S :=
  Iff.rfl

/-- Supported formal chains are monotone in the vertex set. -/
theorem SingularMayerVietoris.formalChainsSupported_mono {V : Type*} {n : ℕ} {S T : Set V}
    (h : S ⊆ T) : formalChainsSupported S n ≤ formalChainsSupported T n := by
  intro c hc v hv i
  exact h (hc hv i)

/-- Every formal chain is supported on all vertices. -/
@[simp]
theorem SingularMayerVietoris.formalChainsSupported_univ {V : Type*} (n : ℕ) :
    formalChainsSupported (Set.univ : Set V) n = ⊤ := by
  apply top_unique
  intro c _ v hv i
  exact Set.mem_univ _

/-- A formal simplex is supported exactly when its vertices are. -/
@[simp]
theorem SingularMayerVietoris.formalSimplex_mem_supported_iff {V : Type*} {n : ℕ} {S : Set V}
    (v : Fin n → V) : formalSimplex v ∈ formalChainsSupported S n ↔ ∀ i, v i ∈ S := by
  classical simp [formalSimplex, formalChainsSupported, Finsupp.mem_supported]

/-- A formal simplex with vertices in the set is supported. -/
theorem SingularMayerVietoris.formalSimplex_mem_supported {V : Type*} {n : ℕ} {S : Set V}
    {v : Fin n → V} (hv : ∀ i, v i ∈ S) : formalSimplex v ∈ formalChainsSupported S n :=
  (formalSimplex_mem_supported_iff v).mpr hv

/-- A vertex set bounding the support gives supportedness. -/
theorem SingularMayerVietoris.formalChainsSupported_le {V : Type*} {n : ℕ} {S : Set V}
    {P : Submodule ℤ (FormalChains V n)} (h : ∀ v, (∀ i, v i ∈ S) → formalSimplex v ∈ P) :
    formalChainsSupported S n ≤ P := by
  rw [formalChainsSupported, Finsupp.supported_eq_span_single]
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hv, rfl⟩
  exact h v hv

/-- A formal linear map preserves supportedness. -/
theorem SingularMayerVietoris.formalLinearMap_mem_of_supported {V M : Type*} {n : ℕ}
    [AddCommGroup M] [Module ℤ M] {S : Set V} (f : FormalChains V n →ₗ[ℤ] M) (P : Submodule ℤ M)
    {c : FormalChains V n} (hc : c ∈ formalChainsSupported S n)
    (h : ∀ v, (∀ i, v i ∈ S) → f (formalSimplex v) ∈ P) : f c ∈ P := by
  exact (formalChainsSupported_le (P := P.comap f) h) hc

/-- The formal boundary preserves supportedness. -/
theorem SingularMayerVietoris.formalBoundary_mem_supported {V : Type*} {S : Set V} (n : ℕ)
    {c : FormalChains V (n + 1)} (hc : c ∈ formalChainsSupported S (n + 1)) :
    formalBoundary n c ∈ formalChainsSupported S n := by
  apply formalLinearMap_mem_of_supported (formalBoundary n) (formalChainsSupported S n) hc
  intro v hv
  rw [formalBoundary_simplex]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  exact formalSimplex_mem_supported fun j => hv (i.succAbove j)

/-- The formal cone preserves supportedness with its center. -/
theorem SingularMayerVietoris.formalCone_mem_supported {V : Type*} {n : ℕ} {S : Set V} {a : V}
    (ha : a ∈ S) {c : FormalChains V n} (hc : c ∈ formalChainsSupported S n) :
    formalCone a n c ∈ formalChainsSupported S (n + 1) := by
  apply formalLinearMap_mem_of_supported (formalCone a n) (formalChainsSupported S (n + 1)) hc
  intro v hv
  rw [formalCone_simplex]
  apply formalSimplex_mem_supported
  intro i
  exact Fin.cases ha hv i

/-- The formal map preserves supportedness. -/
theorem SingularMayerVietoris.formalMap_mem_supported {V W : Type*} {n : ℕ} {S : Set V}
    {T : Set W} (f : V → W) (hf : Set.MapsTo f S T) {c : FormalChains V n}
    (hc : c ∈ formalChainsSupported S n) : formalMap f n c ∈ formalChainsSupported T n := by
  apply formalLinearMap_mem_of_supported (formalMap f n) (formalChainsSupported T n) hc
  intro v hv
  rw [formalMap_simplex]
  exact formalSimplex_mem_supported fun i => hf (hv i)

/-- Subdivision preserves supportedness. -/
theorem SingularMayerVietoris.formalSubdivision_mem_supported {V : Type*}
    (center : FormalCenter V) {S : Set V} (hcenter : ∀ k v, (∀ i, v i ∈ S) → center k v ∈ S) :
    ∀ (n : ℕ) {c : FormalChains V n},
      c ∈ formalChainsSupported S n → formalSubdivision center n c ∈ formalChainsSupported S n := by
  intro n
  induction n with
  | zero =>
    intro c hc
    exact hc
  | succ n ih =>
    intro c hc
    apply
      formalLinearMap_mem_of_supported (formalSubdivision center (n + 1))
        (formalChainsSupported S (n + 1)) hc
    intro v hv
    rw [formalSubdivision_simplex_succ]
    exact
      formalCone_mem_supported (hcenter n v hv)
        (ih (formalBoundary_mem_supported n (formalSimplex_mem_supported hv)))

/-- A cone supported on the convex hull exists. -/
theorem SingularMayerVietoris.formalCone_support_exists {V : Type*} {n : ℕ} (a : V)
    {c : FormalChains V n} {w : Fin (n + 1) → V} (hw : w ∈ (formalCone a n c).support) :
    ∃ v ∈ c.support, w = Fin.cons a v := by
  classical
  change w ∈ (Finsupp.mapDomain (Fin.cons a) c).support at hw
  obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hw)
  exact ⟨v, hv, heq.symm⟩

/-- A lift supported on the convex hull exists. -/
theorem SingularMayerVietoris.formalLift_support_exists {V W : Type*} {n : ℕ} {m : ℕ}
    (f : (Fin n → V) → FormalChains W m) {c : FormalChains V n} {w : Fin m → W}
    (hw : w ∈ (formalLift f c).support) : ∃ v ∈ c.support, w ∈ (f v).support := by
  classical
  change w ∈ (c.sum fun v z => z • f v).support at hw
  obtain ⟨v, hv, hterm⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hw)
  exact ⟨v, hv, Finsupp.support_smul hterm⟩

/-- A supported formal map exists. -/
theorem SingularMayerVietoris.formalLinearMap_support_exists {V W : Type*} {n : ℕ} {m : ℕ}
    (f : FormalChains V n →ₗ[ℤ] FormalChains W m) {c : FormalChains V n} {w : Fin m → W}
    (hw : w ∈ (f c).support) : ∃ v ∈ c.support, w ∈ (f (formalSimplex v)).support := by
  have hf : f = formalLift (fun v => f (formalSimplex v)) := by
    apply formalChains_ext
    intro v
    simp only [formalLift_simplex]
  rw [hf] at hw
  exact formalLift_support_exists _ hw

/-- A supported formal boundary exists. -/
theorem SingularMayerVietoris.formalBoundary_support_exists {V : Type*} (n : ℕ)
    (v : Fin (n + 1) → V) {w : Fin n → V}
    (hw : w ∈ (formalBoundary n (formalSimplex v)).support) :
    ∃ i : Fin (n + 1), w = v ∘ i.succAbove := by
  classical
  rw [formalBoundary_simplex] at hw
  obtain ⟨i, hi, hterm⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hw)
  refine ⟨i, ?_⟩
  have hs : w ∈ (formalSimplex (v ∘ i.succAbove)).support := Finsupp.support_smul hterm
  simpa [formalSimplex] using hs

/-- A formal linear map is supported on the convex hull. -/
theorem SingularMayerVietoris.formalLinearMap_mem_of_support {V M : Type*} [AddCommGroup M]
    [Module ℤ M] {n : ℕ} (f : FormalChains V n →ₗ[ℤ] M) (P : Submodule ℤ M) (c : FormalChains V n)
    (hf : ∀ v ∈ c.support, f (formalSimplex v) ∈ P) : f c ∈ P := by
  have h : Finsupp.supported ℤ ℤ (c.support : Set (Fin n → V)) ≤ P.comap f := by
    rw [Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, rfl⟩
    exact hf v hv
  exact h (fun _ hv => hv)

/-- A singular linear map is supported on the convex hull. -/
theorem SingularMayerVietoris.singularLinearMap_mem_of_support {M : Type*} [AddCommGroup M]
    [Module ℤ M] {X : Type} [TopologicalSpace X] (n : ℕ) (f : SingularChains.Chains X n →ₗ[ℤ] M)
    (P : Submodule ℤ M) (c : SingularChains.Chains X n)
    (hf :
      ∀ σ ∈ (SingularChains.chainsEquivFinsupp X n c).support,
        f (SingularChains.simplexChain X n σ) ∈ P) :
    f c ∈ P := by
  let S : Set (SingularChains.SingularSimplex X n) :=
    (SingularChains.chainsEquivFinsupp X n c).support
  have hc : c ∈ Submodule.span ℤ (SingularChains.simplexChain X n '' S) :=
    (SingularChains.mem_simplex_span_iff X n S c).mpr (Set.Subset.refl _)
  have h : Submodule.span ℤ (SingularChains.simplexChain X n '' S) ≤ P.comap f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨σ, hσ, rfl⟩
    exact hf σ hσ
  exact h hc

/-- A singular linear map is small. -/
theorem SingularMayerVietoris.singularLinearMap_mem_of_small {M : Type*} [AddCommGroup M]
    [Module ℤ M] {X : Type} [TopologicalSpace X] (U V : Set X) (n : ℕ)
    (f : SingularChains.Chains X n →ₗ[ℤ] M) (P : Submodule ℤ M) (c : SingularChains.Chains X n)
    (hc : c ∈ smallChainSubmodule U V n)
    (hf :
      ∀ σ : SingularChains.SingularSimplex X n,
        (Set.range σ ⊆ U ∨ Set.range σ ⊆ V) → f (SingularChains.simplexChain X n σ) ∈ P) :
    f c ∈ P := by
  have h : smallChainSubmodule U V n ≤ P.comap f := by
    rw [smallChainSubmodule_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨σ, hσ, rfl⟩
    exact hf σ hσ
  exact h hc

/-- A realized chain is supported. -/
theorem SingularMayerVietoris.realizedChain_mem_supported {X : Type} [TopologicalSpace X]
    (U : Set X) (p n : ℕ) (σ : C(SingularChains.Simplex p, X)) (hσ : Set.range σ ⊆ U)
    (c : FormalChains (SingularChains.Simplex p) (n + 1)) :
    SingularChains.inducedChain σ n (affineChainMap p n c) ∈ supportedChainSubmodule U n := by
  apply
    formalLinearMap_mem_of_support ((SingularChains.inducedChain σ n).comp (affineChainMap p n))
      (supportedChainSubmodule U n) c
  intro v hv
  simp only [LinearMap.comp_apply, affineChainMap_simplex, SingularChains.inducedChain_simplex]
  apply simplexChain_mem_supported
  rintro x ⟨t, rfl⟩
  exact hσ ⟨affineSimplex v t, rfl⟩

/-- A realized chain is small. -/
theorem SingularMayerVietoris.realizedChain_mem_small {X : Type} [TopologicalSpace X]
    (U V : Set X) (p n : ℕ) (σ : C(SingularChains.Simplex p, X))
    (hσ : Set.range σ ⊆ U ∨ Set.range σ ⊆ V)
    (c : FormalChains (SingularChains.Simplex p) (n + 1)) :
    SingularChains.inducedChain σ n (affineChainMap p n c) ∈ smallChainSubmodule U V n := by
  rcases hσ with hσ | hσ
  · exact
      (le_sup_left : supportedChainSubmodule U n ≤ smallChainSubmodule U V n)
        (realizedChain_mem_supported U p n σ hσ c)
  · exact
      (le_sup_right : supportedChainSubmodule V n ≤ smallChainSubmodule U V n)
        (realizedChain_mem_supported V p n σ hσ c)

/-- A chain supported on small sets is small. -/
theorem SingularMayerVietoris.realizedChain_mem_small_of_support {X : Type} [TopologicalSpace X]
    (U V : Set X) (p n : ℕ) (σ : C(SingularChains.Simplex p, X))
    (c : FormalChains (SingularChains.Simplex p) (n + 1))
    (hc :
      ∀ v ∈ c.support,
        Set.range (σ.comp (affineSimplex v)) ⊆ U ∨ Set.range (σ.comp (affineSimplex v)) ⊆ V) :
    SingularChains.inducedChain σ n (affineChainMap p n c) ∈ smallChainSubmodule U V n := by
  apply
    formalLinearMap_mem_of_support ((SingularChains.inducedChain σ n).comp (affineChainMap p n))
      (smallChainSubmodule U V n) c
  intro v hv
  simp only [LinearMap.comp_apply, affineChainMap_simplex, SingularChains.inducedChain_simplex]
  exact simplexChain_mem_small U V n (σ.comp (affineSimplex v)) (hc v hv)

/-! ### Mesh estimates -/

/-- The barycenter of a vertex list. -/
def SingularMayerVietoris.vertexBarycenter {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {n : ℕ} (v : Fin (n + 1) → E) : E :=
  (1 / ((n : ℝ) + 1)) • ∑ i, v i

/-- The barycenter lies in the convex hull. -/
theorem SingularMayerVietoris.vertexBarycenter_mem_of_convex {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} (v : Fin (n + 1) → E) {s : Set E}
    (hs : Convex ℝ s) (hv : ∀ i, v i ∈ s) : vertexBarycenter v ∈ s := by
  simpa [vertexBarycenter, Finset.centerMass, Nat.cast_add, Nat.cast_one, one_div] using
    hs.centerMass_mem (t := Finset.univ) (w := fun _ : Fin (n + 1) => (1 : ℝ)) (z := v)
      (by intro i hi; exact zero_le_one)
      (by simpa using (Nat.cast_pos.mpr (Nat.succ_pos n) : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)))
      (by intro i hi; exact hv i)

/-- The barycenter minus a vertex. -/
theorem SingularMayerVietoris.vertexBarycenter_sub {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {n : ℕ} (v : Fin (n + 1) → E) (x : E) :
    vertexBarycenter v - x = (1 / ((n : ℝ) + 1)) • ∑ i, (v i - x) := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  simp only [vertexBarycenter, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_sub]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  simp [hn]

/-- The summed norms of vertex differences bound the diameter. -/
theorem SingularMayerVietoris.sum_norm_vertex_sub_le {E : Type*} [SeminormedAddCommGroup E]
    {n : ℕ} (v : Fin (n + 1) → E) {D : ℝ} (hpair : ∀ i j, Dist.dist (v i) (v j) ≤ D)
    (j : Fin (n + 1)) : (∑ i, ‖v i - v j‖) ≤ (n : ℝ) * D := by
  calc
    (∑ i, ‖v i - v j‖) = ∑ i ∈ Finset.univ.erase j, ‖v i - v j‖ := by
      simpa only [sub_self, norm_zero, add_zero] using
        (Finset.sum_erase_add Finset.univ (fun i => ‖v i - v j‖) (Finset.mem_univ j)).symm
    _ ≤ ∑ _i ∈ Finset.univ.erase j, D := by
      apply Finset.sum_le_sum
      intro i _hi
      simpa only [dist_eq_norm] using hpair i j
    _ = (n : ℝ) * D := by simp

/-- The barycenter-to-vertex distance bound. -/
theorem SingularMayerVietoris.dist_vertexBarycenter_vertex_le {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} (v : Fin (n + 1) → E) {D : ℝ}
    (hpair : ∀ i j, Dist.dist (v i) (v j) ≤ D) (j : Fin (n + 1)) :
    Dist.dist (vertexBarycenter v) (v j) ≤ (n : ℝ) / ((n : ℝ) + 1) * D := by
  have hc : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
  rw [dist_eq_norm, vertexBarycenter_sub, norm_smul, Real.norm_of_nonneg hc]
  calc
    _ ≤ (1 / ((n : ℝ) + 1)) * ∑ i, ‖v i - v j‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hc
    _ ≤ (1 / ((n : ℝ) + 1)) * ((n : ℝ) * D) :=
      (mul_le_mul_of_nonneg_left (sum_norm_vertex_sub_le v hpair j) hc)
    _ = (n : ℝ) / ((n : ℝ) + 1) * D := by ring

/-- The barycenter-to-hull distance bound. -/
theorem SingularMayerVietoris.dist_vertexBarycenter_convexHull_le {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} (v : Fin (n + 1) → E) {D : ℝ}
    (hpair : ∀ i j, Dist.dist (v i) (v j) ≤ D) {x : E} (hx : x ∈ convexHull ℝ (Set.range v)) :
    Dist.dist (vertexBarycenter v) x ≤ (n : ℝ) / ((n : ℝ) + 1) * D := by
  have hball :
    Set.range v ⊆ Metric.closedBall (vertexBarycenter v) ((n : ℝ) / ((n : ℝ) + 1) * D) := by
    rintro _ ⟨j, rfl⟩
    rw [Metric.mem_closedBall, dist_comm]
    exact dist_vertexBarycenter_vertex_le v hpair j
  have h := convexHull_min hball (convex_closedBall _ _) hx
  simpa only [Metric.mem_closedBall, dist_comm] using h

/-- The convex-hull diameter bound. -/
theorem SingularMayerVietoris.dist_convexHull_range_le {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {n : ℕ} (v : Fin (n + 1) → E) {D : ℝ}
    (hpair : ∀ i j, Dist.dist (v i) (v j) ≤ D) {x y : E} (hx : x ∈ convexHull ℝ (Set.range v))
    (hy : y ∈ convexHull ℝ (Set.range v)) : Dist.dist x y ≤ D := by
  obtain ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, h⟩ := convexHull_exists_dist_ge2 hx hy
  exact h.trans (hpair i j)

/-- A pairwise Lebesgue number for two open covers. -/
theorem SingularMayerVietoris.exists_lebesgue_number_two_pairwise {K X : Type*}
    [PseudoMetricSpace K] [CompactSpace K] [TopologicalSpace X] (σ : C(K, X)) {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hcover : Set.range σ ⊆ U ∪ V) :
    ∃ δ > 0, ∀ s : Set K, (∀ x ∈ s, ∀ y ∈ s, Dist.dist x y ≤ δ) → σ '' s ⊆ U ∨ σ '' s ⊆ V := by
  let W : Bool → Set K := fun b => if b then σ ⁻¹' U else σ ⁻¹' V
  have hW : ∀ b, IsOpen (W b) := by
    intro b
    cases b
    · exact hV.preimage σ.continuous
    · exact hU.preimage σ.continuous
  have hWcover : (Set.univ : Set K) ⊆ ⋃ b, W b := by
    intro x _
    rcases hcover ⟨x, rfl⟩ with hx | hx
    · exact Set.mem_iUnion.mpr ⟨Bool.true, hx⟩
    · exact Set.mem_iUnion.mpr ⟨Bool.false, hx⟩
  obtain ⟨ε, hε, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hW hWcover
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro s hdist
  by_cases hs : s.Nonempty
  · obtain ⟨x, hx⟩ := hs
    obtain ⟨b, hb⟩ := hball x (Set.mem_univ x)
    have hsub : s ⊆ Metric.ball x ε := by
      intro y hy
      exact (hdist y hy x hx).trans_lt (half_lt_self hε)
    cases b
    · right
      rintro _ ⟨y, hy, rfl⟩
      exact hb (hsub hy)
    · left
      rintro _ ⟨y, hy, rfl⟩
      exact hb (hsub hy)
  · left
    rw [Set.not_nonempty_iff_eq_empty.mp hs, Set.image_empty]
    exact Set.empty_subset _

/-- A Lebesgue number for a two-element open cover. -/
theorem SingularMayerVietoris.exists_lebesgue_number_two {K X : Type*} [PseudoMetricSpace K]
    [CompactSpace K] [TopologicalSpace X] (σ : C(K, X)) {U V : Set X} (hU : IsOpen U)
    (hV : IsOpen V) (hcover : Set.range σ ⊆ U ∪ V) :
    ∃ δ > 0, ∀ s : Set K, Metric.diam s ≤ δ → σ '' s ⊆ U ∨ σ '' s ⊆ V := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_lebesgue_number_two_pairwise σ hU hV hcover
  refine ⟨δ, hδ, fun s hs => hsmall s ?_⟩
  intro x hx y hy
  exact (Metric.dist_le_diam_of_mem Metric.isBounded_of_compactSpace hx hy).trans hs

/-- The subdivision mesh factor `n/(n+1)`. -/
def SingularMayerVietoris.meshFactor (n : ℕ) : ℝ :=
  (n : ℝ) / ((n : ℝ) + 1)

/-- The mesh factor is nonnegative. -/
theorem SingularMayerVietoris.meshFactor_nonneg (n : ℕ) : 0 ≤ meshFactor n := by
  exact div_nonneg (Nat.cast_nonneg n) (by positivity)

/-- The mesh factor is less than one. -/
theorem SingularMayerVietoris.meshFactor_lt_one (n : ℕ) : meshFactor n < 1 := by
  apply (div_lt_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
  linarith

/-- The mesh factor is monotone in the degree. -/
theorem SingularMayerVietoris.meshFactor_mono : Monotone meshFactor := by
  intro n m hnm
  dsimp [meshFactor]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hnm' : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  nlinarith

/-- Mesh factor powers tend to zero. -/
theorem SingularMayerVietoris.meshFactor_pow_tendsto (n : ℕ) :
    Filter.Tendsto (fun k : ℕ => meshFactor n ^ k) Filter.atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (meshFactor_nonneg n) (meshFactor_lt_one n)

/-- Scaled mesh powers tend to zero. -/
theorem SingularMayerVietoris.meshFactor_pow_mul_tendsto (n : ℕ) (D : ℝ) :
    Filter.Tendsto (fun k : ℕ => meshFactor n ^ k * D) Filter.atTop (𝓝 0) := by
  simpa only [MulZeroClass.zero_mul] using (meshFactor_pow_tendsto n).mul_const D

/-- Scaled mesh powers are eventually small. -/
theorem SingularMayerVietoris.eventually_meshFactor_pow_mul_lt (n : ℕ) (D : ℝ) {δ : ℝ}
    (hδ : 0 < δ) : ∃ N : ℕ, ∀ k ≥ N, meshFactor n ^ k * D < δ := by
  apply Filter.eventually_atTop.mp
  exact (meshFactor_pow_mul_tendsto n D).eventually (eventually_lt_nhds hδ)

/-- A Lebesgue number for the preimage cover of the simplex. -/
theorem SingularMayerVietoris.simplex_lebesgue_number_two {X : Type*} [TopologicalSpace X]
    {U V : Set X} {n : ℕ} (σ : C(SingularChains.Simplex n, X)) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : Set.range σ ⊆ U ∪ V) :
    ∃ δ > 0, ∀ s : Set (SingularChains.Simplex n), Metric.diam s ≤ δ → σ '' s ⊆ U ∨ σ '' s ⊆ V :=
  exists_lebesgue_number_two σ hU hV hcover

/-- Simplices below the Lebesgue number are small. -/
theorem SingularMayerVietoris.simplex_lebesgue_number_subsimplices {X : Type*}
    [TopologicalSpace X] {U V : Set X} {n : ℕ} (σ : C(SingularChains.Simplex n, X)) (hU : IsOpen U)
    (hV : IsOpen V) (hcover : Set.range σ ⊆ U ∪ V) :
    ∃ δ > 0,
      ∀ (m : ℕ) (f : C(SingularChains.Simplex m, SingularChains.Simplex n)),
        Metric.diam (Set.range f) ≤ δ → Set.range (σ.comp f) ⊆ U ∨ Set.range (σ.comp f) ⊆ V := by
  obtain ⟨δ, hδ, hsmall⟩ := simplex_lebesgue_number_two σ hU hV hcover
  refine ⟨δ, hδ, ?_⟩
  intro m f hf
  simpa only [ContinuousMap.coe_comp, Set.range_comp] using hsmall (Set.range f) hf

/-- Iterated subdivision eventually makes a simplex small. -/
theorem SingularMayerVietoris.simplex_eventually_small_of_diameter {X : Type*}
    [TopologicalSpace X] {U V : Set X} {n : ℕ} (σ : C(SingularChains.Simplex n, X)) (hU : IsOpen U)
    (hV : IsOpen V) (hcover : Set.range σ ⊆ U ∪ V) (D : ℝ) :
    ∃ N : ℕ,
      ∀ k ≥ N,
        ∀ (m : ℕ) (f : C(SingularChains.Simplex m, SingularChains.Simplex n)),
          Metric.diam (Set.range f) ≤ meshFactor n ^ k * D →
            Set.range (σ.comp f) ⊆ U ∨ Set.range (σ.comp f) ⊆ V := by
  obtain ⟨δ, hδ, hsmall⟩ := simplex_lebesgue_number_subsimplices σ hU hV hcover
  obtain ⟨N, hN⟩ := eventually_meshFactor_pow_mul_lt n D hδ
  refine ⟨N, ?_⟩
  intro k hk m f hf
  exact hsmall m f (hf.trans (hN k hk).le)

/-- A finite family of simplices is eventually simultaneously small. -/
theorem SingularMayerVietoris.finite_family_eventually_small_of_diameter {X : Type*}
    [TopologicalSpace X] {U V : Set X} {n : ℕ} (s : Finset C(SingularChains.Simplex n, X))
    (hU : IsOpen U) (hV : IsOpen V) (hcover : ∀ σ ∈ s, Set.range σ ⊆ U ∪ V) (D : ℝ) :
    ∃ N : ℕ,
      ∀ k ≥ N,
        ∀ σ ∈ s,
          ∀ (m : ℕ) (f : C(SingularChains.Simplex m, SingularChains.Simplex n)),
            Metric.diam (Set.range f) ≤ meshFactor n ^ k * D →
              Set.range (σ.comp f) ⊆ U ∨ Set.range (σ.comp f) ⊆ V := by
  classical
    induction s using Finset.induction_on with
  | empty => exact ⟨0, fun _ _ _ hσ => False.elim (Finset.notMem_empty _ hσ)⟩
  | @insert σ s hσ
    ih =>
    obtain ⟨Nσ, hNσ⟩ :=
      simplex_eventually_small_of_diameter σ hU hV (hcover σ (Finset.mem_insert_self σ s)) D
    obtain ⟨Ns, hNs⟩ := ih (fun τ hτ => hcover τ (Finset.mem_insert_of_mem hτ))
    refine ⟨Max.max Nσ Ns, ?_⟩
    intro k hk τ hτ m f hf
    rcases Finset.mem_insert.mp hτ with rfl | hτ
    · exact hNσ k ((le_max_left _ _).trans hk) m f hf
    · exact hNs k ((le_max_right _ _).trans hk) τ hτ m f hf

/-- The simplex barycenter is the vertex barycenter. -/
theorem SingularMayerVietoris.simplexBarycenter_eq_vertexBarycenter {n p : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p) :
    (simplexBarycenter v : Fin (p + 1) → ℝ) =
      vertexBarycenter (fun i => (v i : Fin (p + 1) → ℝ)) := by
  rw [simplexBarycenter_coe]
  simp only [vertexBarycenter, Nat.cast_add, Nat.cast_one, one_div]

/-- Points of an affine simplex are within the vertex diameter. -/
theorem SingularMayerVietoris.dist_affineSimplex_le {n p : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p) {D : ℝ} (hpair : ∀ i j, Dist.dist (v i) (v j) ≤ D)
    (t u : SingularChains.Simplex n) : Dist.dist (affineSimplex v t) (affineSimplex v u) ≤ D :=
  dist_convexHull_range_le (fun i => (v i : Fin (p + 1) → ℝ)) hpair
    (affineSimplex_mem_convexHull v t) (affineSimplex_mem_convexHull v u)

/-- The affine simplex's diameter is bounded by the vertex diameter. -/
theorem SingularMayerVietoris.affineSimplex_diam_le {n p : ℕ}
    (v : Fin (n + 1) → SingularChains.Simplex p) {D : ℝ}
    (hpair : ∀ i j, Dist.dist (v i) (v j) ≤ D) : Metric.diam (Set.range (affineSimplex v)) ≤ D := by
  apply Metric.diam_le_of_forall_dist_le_of_nonempty (Set.range_nonempty (affineSimplex v))
  rintro _ ⟨t, rfl⟩ _ ⟨u, rfl⟩
  exact dist_affineSimplex_le v hpair t u

/-- Vertex-bounded families become small under iteration. -/
theorem SingularMayerVietoris.finite_family_eventually_small_of_vertices {p : ℕ} {X : Type*}
    [TopologicalSpace X] {U V : Set X} (s : Finset C(SingularChains.Simplex p, X)) (hU : IsOpen U)
    (hV : IsOpen V) (hcover : ∀ σ ∈ s, Set.range σ ⊆ U ∪ V) (D : ℝ) :
    ∃ N : ℕ,
      ∀ k ≥ N,
        ∀ σ ∈ s,
          ∀ (m : ℕ) (v : Fin (m + 1) → SingularChains.Simplex p),
            (∀ i j, Dist.dist (v i) (v j) ≤ meshFactor p ^ k * D) →
              Set.range (σ.comp (affineSimplex v)) ⊆ U ∨
                Set.range (σ.comp (affineSimplex v)) ⊆ V := by
  obtain ⟨N, hN⟩ := finite_family_eventually_small_of_diameter s hU hV hcover D
  refine ⟨N, ?_⟩
  intro k hk σ hσ m v hv
  exact hN k hk σ hσ m (affineSimplex v) (affineSimplex_diam_le v hv)

/-- The formal center lies in the convex hull. -/
theorem SingularMayerVietoris.formalCenter_mem_of_convex {V E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] (center : FormalCenter V) (coords : V → E)
    (hcenter : ∀ n (v : Fin (n + 1) → V), coords (center n v) = vertexBarycenter (coords ∘ v))
    {S : Set E} (hS : Convex ℝ S) (n : ℕ) (v : Fin (n + 1) → V) (hv : ∀ i, coords (v i) ∈ S) :
    coords (center n v) ∈ S := by
  rw [hcenter]
  exact vertexBarycenter_mem_of_convex (coords ∘ v) hS hv

/-- Subdivision vertices stay in the convex hull. -/
theorem SingularMayerVietoris.formalSubdivision_simplex_vertices_mem_convexHull {V E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] (center : FormalCenter V) (coords : V → E)
    (hcenter : ∀ n (v : Fin (n + 1) → V), coords (center n v) = vertexBarycenter (coords ∘ v))
    {n : ℕ} (v : Fin n → V) {w : Fin n → V}
    (hw : w ∈ (formalSubdivision center n (formalSimplex v)).support) (i : Fin n) :
    coords (w i) ∈ convexHull ℝ (Set.range (coords ∘ v)) := by
  let S : Set V := coords ⁻¹' convexHull ℝ (Set.range (coords ∘ v))
  have hv : formalSimplex v ∈ formalChainsSupported S n := by
    apply formalSimplex_mem_supported
    intro j
    exact subset_convexHull ℝ _ (Set.mem_range_self j)
  have hS : ∀ k (u : Fin (k + 1) → V), (∀ j, u j ∈ S) → center k u ∈ S := by
    intro k u hu
    exact formalCenter_mem_of_convex center coords hcenter (convex_convexHull ℝ _) k u hu
  have hsub := formalSubdivision_mem_supported center hS n hv
  exact (mem_formalChainsSupported_iff.mp hsub) w hw i

/-- One subdivision scales the mesh by the factor. -/
theorem SingularMayerVietoris.formalSubdivision_simplex_mesh {V E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] (center : FormalCenter V) (coords : V → E)
    (hcenter : ∀ n (v : Fin (n + 1) → V), coords (center n v) = vertexBarycenter (coords ∘ v))
    (n : ℕ) :
    ∀ (v : Fin (n + 1) → V) {D : ℝ},
      (∀ i j, Dist.dist (coords (v i)) (coords (v j)) ≤ D) →
        ∀ {w : Fin (n + 1) → V},
          w ∈ (formalSubdivision center (n + 1) (formalSimplex v)).support →
            ∀ i j, Dist.dist (coords (w i)) (coords (w j)) ≤ meshFactor n * D := by
  induction n with
  | zero =>
    intro v D hpair w hw i j
    let : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
    have hij : i = j := Subsingleton.elim _ _
    subst j
    simp [meshFactor]
  | succ n ih =>
    intro v D hpair w hw
    have hD : 0 ≤ D := by simpa only [dist_self] using hpair 0 0
    have hHull := formalSubdivision_simplex_vertices_mem_convexHull center coords hcenter v hw
    rw [formalSubdivision_simplex_succ] at hw
    obtain ⟨u, hu, rfl⟩ := formalCone_support_exists (center (n + 1) v) hw
    obtain ⟨face, hface, hu⟩ :=
      formalLinearMap_support_exists (formalSubdivision center (n + 1)) hu
    obtain ⟨r, rfl⟩ := formalBoundary_support_exists (n + 1) v hface
    have huMesh := ih (v ∘ r.succAbove) (fun i j => hpair (r.succAbove i) (r.succAbove j)) hu
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simpa only [Fin.cons_zero, dist_self] using mul_nonneg (meshFactor_nonneg (n + 1)) hD
      · change Dist.dist (coords (center (n + 1) v)) (coords (u j)) ≤ meshFactor (n + 1) * D
        rw [hcenter]
        exact dist_vertexBarycenter_convexHull_le (coords ∘ v) hpair (hHull j.succ)
    · refine Fin.cases ?_ (fun j => ?_) j
      · change Dist.dist (coords (u i)) (coords (center (n + 1) v)) ≤ meshFactor (n + 1) * D
        rw [dist_comm, hcenter]
        exact dist_vertexBarycenter_convexHull_le (coords ∘ v) hpair (hHull i.succ)
      · change Dist.dist (coords (u i)) (coords (u j)) ≤ meshFactor (n + 1) * D
        exact (huMesh i j).trans (mul_le_mul_of_nonneg_right (meshFactor_mono (Nat.le_succ n)) hD)

/-- Subdivision scales a chain's mesh by the factor. -/
theorem SingularMayerVietoris.formalSubdivision_mesh {V E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] (center : FormalCenter V) (coords : V → E)
    (hcenter : ∀ n (v : Fin (n + 1) → V), coords (center n v) = vertexBarycenter (coords ∘ v))
    (n : ℕ) (c : FormalChains V (n + 1)) {D : ℝ}
    (hc : ∀ v ∈ c.support, ∀ i j, Dist.dist (coords (v i)) (coords (v j)) ≤ D) :
    ∀ w ∈ (formalSubdivision center (n + 1) c).support,
      ∀ i j, Dist.dist (coords (w i)) (coords (w j)) ≤ meshFactor n * D := by
  intro w hw
  obtain ⟨v, hv, hw⟩ := formalLinearMap_support_exists (formalSubdivision center (n + 1)) hw
  exact formalSubdivision_simplex_mesh center coords hcenter n v (hc v hv) hw

/-- Iterated subdivision scales the mesh by the power. -/
theorem SingularMayerVietoris.formalSubdivision_iterate_mesh {V E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] (center : FormalCenter V) (coords : V → E)
    (hcenter : ∀ n (v : Fin (n + 1) → V), coords (center n v) = vertexBarycenter (coords ∘ v))
    (n k : ℕ) (c : FormalChains V (n + 1)) {D : ℝ}
    (hc : ∀ v ∈ c.support, ∀ i j, Dist.dist (coords (v i)) (coords (v j)) ≤ D) :
    ∀ w ∈ ((formalSubdivision center (n + 1))^[k] c).support,
      ∀ i j, Dist.dist (coords (w i)) (coords (w j)) ≤ meshFactor n ^ k * D := by
  induction k with
  | zero => simpa only [Function.iterate_zero_apply, pow_zero, one_mul] using hc
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    intro w hw i j
    have h :=
      formalSubdivision_mesh center coords hcenter n ((formalSubdivision center (n + 1))^[k] c) ih
        w hw i j
    simpa only [pow_succ, mul_assoc, mul_left_comm] using h

/-- Points of the standard simplex are within distance one. -/
theorem SingularMayerVietoris.simplex_dist_le_one {p : ℕ} (x y : SingularChains.Simplex p) :
    Dist.dist x y ≤ 1 :=
  (Metric.dist_le_diam_of_mem (bounded_stdSimplex (Fin (p + 1))) x.property y.property).trans
    diam_stdSimplex_le

/-- Iterated subdivision makes the standard simplex's mesh small. -/
theorem SingularMayerVietoris.simplex_formalSubdivision_iterate_mesh {p n : ℕ} (k : ℕ)
    (c : FormalChains (SingularChains.Simplex p) (n + 1)) :
    ∀ w ∈ ((formalSubdivision (fun _ v => simplexBarycenter v) (n + 1))^[k] c).support,
      ∀ i j, Dist.dist (w i) (w j) ≤ meshFactor n ^ k := by
  have h :=
    formalSubdivision_iterate_mesh
      (fun n (v : Fin (n + 1) → SingularChains.Simplex p) => simplexBarycenter v)
      (fun x : SingularChains.Simplex p => (x : Fin (p + 1) → ℝ))
      (fun _ v => simplexBarycenter_eq_vertexBarycenter v) n k c (D := 1)
      (fun v _ i j => simplex_dist_le_one (v i) (v j))
  intro w hw i j
  change Dist.dist (w i : Fin (p + 1) → ℝ) (w j : Fin (p + 1) → ℝ) ≤ meshFactor n ^ k
  simpa only [mul_one] using h w hw i j

/-- A finite family is eventually small under iterated subdivision. -/
theorem SingularMayerVietoris.finite_family_formalSubdivision_eventually_small {p : ℕ} {X : Type*}
    [TopologicalSpace X] {U V : Set X} (s : Finset C(SingularChains.Simplex p, X)) (hU : IsOpen U)
    (hV : IsOpen V) (hcover : ∀ σ ∈ s, Set.range σ ⊆ U ∪ V) :
    ∃ N : ℕ,
      ∀ k ≥ N,
        ∀ σ ∈ s,
          ∀ c : FormalChains (SingularChains.Simplex p) (p + 1),
            ∀ w ∈ ((formalSubdivision (fun _ v => simplexBarycenter v) (p + 1))^[k] c).support,
              Set.range (σ.comp (affineSimplex w)) ⊆ U ∨
                Set.range (σ.comp (affineSimplex w)) ⊆ V := by
  obtain ⟨N, hN⟩ := finite_family_eventually_small_of_vertices s hU hV hcover 1
  refine ⟨N, ?_⟩
  intro k hk σ hσ c w hw
  apply hN k hk σ hσ p w
  simpa only [mul_one] using simplex_formalSubdivision_iterate_mesh k c w hw

/-! ### Subdivision lands in small chains -/

/-- The subdivision homotopy stays in small chains. -/
theorem SingularMayerVietoris.subdivisionHomotopy_mem_small {X : Type} [TopologicalSpace X]
    (U V : Set X) (k n : ℕ) (c : SingularChains.Chains X n) (hc : c ∈ smallChainSubmodule U V n) :
    subdivisionHomotopy X k n c ∈ smallChainSubmodule U V (n + 1) := by
  apply
    singularLinearMap_mem_of_small U V n (subdivisionHomotopy X k n)
      (smallChainSubmodule U V (n + 1)) c hc
  intro σ hσ
  rw [subdivisionHomotopy_simplex]
  exact realizedChain_mem_small U V n (n + 1) σ hσ _

/-- Some iterate of subdivision lands every chain in small chains. -/
theorem SingularMayerVietoris.eventually_subdivision_mem_small {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ)
    (c : SingularChains.Chains X n) :
    ∃ N : ℕ, ∀ k ≥ N, subdivision X k n c ∈ smallChainSubmodule U V n := by
  classical
  have hc : ∀ σ ∈ (SingularChains.chainsEquivFinsupp X n c).support, Set.range σ ⊆ U ∪ V := by
    intro σ hσ
    rw [hcover]
    exact Set.subset_univ _
  obtain ⟨N, hN⟩ :=
    finite_family_formalSubdivision_eventually_small
      (SingularChains.chainsEquivFinsupp X n c).support hU hV hc
  refine ⟨N, ?_⟩
  intro k hk
  apply singularLinearMap_mem_of_support n (subdivision X k n) (smallChainSubmodule U V n) c
  intro σ hσ
  rw [subdivision_simplex]
  apply realizedChain_mem_small_of_support U V n n σ
  intro v hv
  exact hN k hk σ hσ (formalSimplex (stdVertices n)) v hv

/-! ### The small-chains quasi-isomorphism -/

/-- A deformation retract makes the small inclusion a quasi-isomorphism. -/
theorem SingularMayerVietoris.smallInclusion_quasiIso_of_deformation {X : Type}
    [TopologicalSpace X] (U V : Set X)
    (s : ∀ _k n : ℕ, SingularChains.Chains X n →ₗ[ℤ] SingularChains.Chains X n)
    (h : ∀ _k n : ℕ, SingularChains.Chains X n →ₗ[ℤ] SingularChains.Chains X (n + 1))
    (hs :
      ∀ k n,
        ∀ c : SingularChains.Chains X (n + 1),
          ((SingularChains.singularComplex X).d (n + 1) n).hom (s k (n + 1) c) =
            s k n (((SingularChains.singularComplex X).d (n + 1) n).hom c))
    (hh :
      ∀ k n,
        ∀ c : SingularChains.Chains X n,
          ((SingularChains.singularComplex X).d n (n - 1)).hom c = 0 →
            ((SingularChains.singularComplex X).d (n + 1) n).hom (h k n c) = c - s k n c)
    (hsmall :
      ∀ k n,
        ∀ c : SingularChains.Chains X n,
          c ∈ smallChainSubmodule U V n → h k n c ∈ smallChainSubmodule U V (n + 1))
    (heventually :
      ∀ n, ∀ c : SingularChains.Chains X n, ∃ k, s k n c ∈ smallChainSubmodule U V n) :
    QuasiIso (smallInclusion U V) := by
  apply ModuleHomology.quasiIso_of_injective_chain_conditions (smallInclusion U V)
  · intro n
    exact smallInclusion_f_injective U V n
  · intro n c hc
    obtain ⟨k, hk⟩ := heventually n c
    exact ⟨⟨s k n c, hk⟩, h k n c, hh k n c hc⟩
  · intro n c hc b hb
    have hc' : ((SingularChains.singularComplex X).d n (n - 1)).hom c.1 = 0 :=
      congrArg (fun z : (smallComplex U V).X (n - 1) => z.1) hc
    change ((SingularChains.singularComplex X).d (n + 1) n).hom b = c.1 at hb
    obtain ⟨k, hk⟩ := heventually (n + 1) b
    refine
      ⟨⟨s k (n + 1) b + h k n c.1,
          (smallChainSubmodule U V (n + 1)).add_mem hk (hsmall k n c.1 c.2)⟩,
        ?_⟩
    apply Subtype.ext
    change ((SingularChains.singularComplex X).d (n + 1) n).hom (s k (n + 1) b + h k n c.1) = c.1
    rw [map_add, hs, hb, hh k n c.1 hc']
    rw [← add_sub_assoc, add_comm, add_sub_cancel_right]

/-- The small-chains inclusion is a quasi-isomorphism. -/
theorem SingularMayerVietoris.smallInclusion_quasiIso {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    QuasiIso (smallInclusion U V) := by
  apply smallInclusion_quasiIso_of_deformation U V (subdivision X) (subdivisionHomotopy X)
  · exact fun k n c => subdivision_boundary k n c
  · exact fun k n c hc => subdivisionHomotopy_boundary_of_cycle k n c hc
  · exact fun k n c hc => subdivisionHomotopy_mem_small U V k n c hc
  · intro n c
    obtain ⟨N, hN⟩ := eventually_subdivision_mem_small U V hU hV hcover n c
    exact ⟨N, hN N le_rfl⟩

/-- Small homology is isomorphic to singular homology. -/
def SingularMayerVietoris.smallHomologyIso {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (smallComplex U V).homology n ≅ (SingularChains.singularComplex X).homology n := by
  letI := smallInclusion_quasiIso U V hU hV hcover
  exact isoOfQuasiIsoAt (smallInclusion U V) n

/-- Small homology is linearly equivalent to singular homology. -/
def SingularMayerVietoris.smallHomologyEquiv {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (smallComplex U V).homology n ≃ₗ[ℤ] (SingularChains.singularComplex X).homology n :=
  (smallHomologyIso U V hU hV hcover n).toLinearEquiv

/-- The small-homology equivalence computes the comparison. -/
@[simp]
theorem SingularMayerVietoris.smallHomologyEquiv_toLinearMap {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (smallHomologyEquiv U V hU hV hcover n).toLinearMap =
      (HomologicalComplex.homologyMap (smallInclusion U V) n).hom :=
  rfl

/-! ### The Mayer–Vietoris sequence -/

/-- The left Mayer–Vietoris homology map. -/
abbrev SingularMayerVietoris.leftHomologyMap {X : Type} [TopologicalSpace X] (U V : Set X)
    (n : ℕ) :
    SingularHomology (U ∩ V : Set X) n →ₗ[ℤ] (SingularHomology U n × SingularHomology V n) :=
  smallLeftHomologyMap U V n

/-- The right Mayer–Vietoris homology map. -/
def SingularMayerVietoris.rightHomologyMap {X : Type} [TopologicalSpace X] (U V : Set X) (n : ℕ) :
    (SingularHomology U n × SingularHomology V n) →ₗ[ℤ] SingularHomology X n := by
  let f :=
    (singularHomologyMap (subtypeInclusion U) n).toAddMonoidHom.coprod
      (singularHomologyMap (subtypeInclusion V) n).toAddMonoidHom
  exact
    { toFun := f
      map_add' := f.map_add
      map_smul' r
        a := by
        convert! f.map_zsmul r a using 1
        exact int_smul_eq_zsmul .. }

/-- The left map computes the signed inclusion pair. -/
theorem SingularMayerVietoris.leftHomologyMap_apply {X : Type} [TopologicalSpace X] (U V : Set X)
    (n : ℕ) (a : SingularHomology (U ∩ V : Set X) n) :
    leftHomologyMap U V n a =
      (singularHomologyMap (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n a,
        -singularHomologyMap (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V)) n
            a) :=
  smallLeftHomologyMap_apply U V n a

/-- The right map computes the sum of inclusions. -/
@[simp]
theorem SingularMayerVietoris.rightHomologyMap_apply {X : Type} [TopologicalSpace X] (U V : Set X)
    (n : ℕ) (a : SingularHomology U n × SingularHomology V n) :
    rightHomologyMap U V n a =
      singularHomologyMap (subtypeInclusion U) n a.1 +
        singularHomologyMap (subtypeInclusion V) n a.2 :=
  rfl

/-- The right map transports through the small-homology comparison. -/
theorem SingularMayerVietoris.rightHomologyMap_eq_comparison {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) :
    rightHomologyMap U V n = (smallHomologyComparison U V n).comp (smallRightHomologyMap U V n) :=
  by
  apply LinearMap.ext
  intro a
  exact (smallHomologyComparison_right U V n a).symm

/-- The left map after the connecting map is zero. -/
theorem SingularMayerVietoris.leftHomologyMap_comp_right {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) : (rightHomologyMap U V n).comp (leftHomologyMap U V n) = 0 := by
  apply LinearMap.ext
  intro a
  have ha := LinearMap.congr_fun (smallLeftHomologyMap_comp_right U V n) a
  change smallRightHomologyMap U V n (smallLeftHomologyMap U V n a) = 0 at ha
  rw [rightHomologyMap_eq_comparison]
  change
    smallHomologyComparison U V n (smallRightHomologyMap U V n (smallLeftHomologyMap U V n a)) = 0
  rw [ha, map_zero]

/-- The equivalence computes the comparison map. -/
theorem SingularMayerVietoris.smallHomologyEquiv_eq_comparison {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (smallHomologyEquiv U V hU hV hcover n).toLinearMap = smallHomologyComparison U V n :=
  smallHomologyEquiv_toLinearMap U V hU hV hcover n

/-- The Mayer–Vietoris connecting homomorphism. -/
def SingularMayerVietoris.connectingHomomorphism {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    SingularHomology X (n + 1) →ₗ[ℤ] SingularHomology (U ∩ V : Set X) n :=
  (smallConnectingMap U V n).comp (smallHomologyEquiv U V hU hV hcover (n + 1)).symm.toLinearMap

/-- The connecting homomorphism transports through the comparison. -/
theorem SingularMayerVietoris.connectingHomomorphism_comparison {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ)
    (a : SmallHomology U V (n + 1)) :
    connectingHomomorphism U V hU hV hcover n (smallHomologyComparison U V (n + 1) a) =
      smallConnectingMap U V n a := by
  rw [← smallHomologyEquiv_eq_comparison U V hU hV hcover]
  exact
    congrArg (smallConnectingMap U V n)
      ((smallHomologyEquiv U V hU hV hcover (n + 1)).symm_apply_apply a)

/-- The right map equals the transported small right map. -/
theorem SingularMayerVietoris.rightHomologyMap_eq_transport {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    rightHomologyMap U V n =
      (smallHomologyEquiv U V hU hV hcover n).toLinearMap.comp (smallRightHomologyMap U V n) := by
  rw [smallHomologyEquiv_eq_comparison, rightHomologyMap_eq_comparison]

/-- Mayer–Vietoris exactness at the intersection term. -/
theorem SingularMayerVietoris.exact_at_intersection {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    LinearMap.range (connectingHomomorphism U V hU hV hcover n) =
      LinearMap.ker (leftHomologyMap U V n) := by
  rw [connectingHomomorphism, rightTransport_connecting_range]
  exact small_exact_at_intersection U V n

/-- Mayer–Vietoris exactness at the pair term. -/
theorem SingularMayerVietoris.exact_at_pair {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    LinearMap.range (leftHomologyMap U V n) = LinearMap.ker (rightHomologyMap U V n) := by
  rw [rightHomologyMap_eq_transport U V hU hV hcover, rightTransport_second_ker]
  exact small_exact_at_pair U V n

/-- The Mayer-Vietoris exactness statement: for open `U`, `V` covering `X`, the long exact sequence assembled from the short exact chain sequence is exact at the ambient homology - the connecting homomorphism `H_n(U cap V) -> H_{n-1}(U + V)` makes the braid exact (Hatcher, Algebraic Topology, Theorem 2.20). -/
theorem SingularMayerVietoris.exact_at_ambient {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    LinearMap.range (rightHomologyMap U V (n + 1)) =
      LinearMap.ker (connectingHomomorphism U V hU hV hcover n) := by
  rw [rightHomologyMap_eq_transport U V hU hV hcover]
  exact
    rightTransport_range_eq_ker (smallHomologyEquiv U V hU hV hcover (n + 1))
      (smallRightHomologyMap U V (n + 1)) (smallConnectingMap U V n)
      (small_exact_at_smallHomology U V n)

/-- The degree-zero right map is surjective. -/
theorem SingularMayerVietoris.rightHomologyMap_zero_surjective {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    Function.Surjective (rightHomologyMap U V 0) := by
  rw [rightHomologyMap_eq_transport U V hU hV hcover]
  exact
    rightTransport_second_surjective (smallHomologyEquiv U V hU hV hcover 0)
      (smallRightHomologyMap U V 0) (smallRightHomologyMap_zero_surjective U V)

/-- The connecting map after the left map is zero. -/
theorem SingularMayerVietoris.connectingHomomorphism_comp_left {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (leftHomologyMap U V n).comp (connectingHomomorphism U V hU hV hcover n) = 0 := by
  apply LinearMap.ext
  intro a
  have ha :
    connectingHomomorphism U V hU hV hcover n a ∈
      LinearMap.range (connectingHomomorphism U V hU hV hcover n) :=
    ⟨a, rfl⟩
  rw [exact_at_intersection] at ha
  exact ha
