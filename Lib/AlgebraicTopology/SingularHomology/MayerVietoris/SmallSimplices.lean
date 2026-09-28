/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.ModuleHomology
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.SmallChains
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.Subdivision
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.Mesh

/-!
# The small simplices theorem

For open sets `U`, `V` covering a space `X`, the inclusion of the complex of `(U, V)`-small
chains into the singular chain complex is a quasi-isomorphism (`smallInclusion_quasiIso`;
Hatcher, *Algebraic Topology*, Proposition 2.21 for the cover `{U, V}`), so small homology is
singular homology (`smallHomologyIso`, `smallHomologyEquiv`).

The proof: barycentric subdivision is a chain map chain homotopic to the identity, the
subdivision homotopy of a small chain is small (`subdivisionHomotopy_mem_small`), and every
chain becomes small after enough subdivisions (`eventually_subdivision_mem_small`, by the mesh
estimate and the Lebesgue number); the criterion `smallInclusion_quasiIso_of_deformation` turns
such data into the quasi-isomorphism.  The lemmas `singularLinearMap_mem_of_support`,
`singularLinearMap_mem_of_small` and `realizedChain_mem_small` reduce smallness of a realized
formal chain to smallness of its simplices.
-/

open Set Function Filter Topology

open scoped CategoryTheory

@[expose] public noncomputable section

/-! ### Realized chains and small chains -/

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
