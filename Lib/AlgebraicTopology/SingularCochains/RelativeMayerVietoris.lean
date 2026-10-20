/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularCochains.Relative
public import Lib.AlgebraicTopology.SingularHomology.Relative.MayerVietoris

/-!
# The relative Mayer–Vietoris sequence in cohomology

The dual of the short exact sequence of relative chain complexes
`0 → C(X)/C(A ∩ B) → C(X)/C(A) ⊕ C(X)/C(B) → C(X)/(C(A) + C(B)) → 0` of
`Relative/MayerVietoris.lean` is short exact (`dualRelativeChainSequence_shortExact`): its second
map has a degreewise section, built from the complement section of `C(X) → C(X)/(C(A) + C(B))`.
For open `A`, `B` the cochains of `C(X)/(C(A) + C(B))` compute `H^*(X, A ∪ B)`
(`dualMap_unionComparison_quasiIso`, the cochain form of the small simplices theorem for the cover
`{A, B}` of `A ∪ B`, through the five lemma `quasiIso_τ₁`).  Together these give the long exact
Mayer–Vietoris sequence of relative cohomology,

  `… → H^q(X, A ∪ B) → H^q(C(X)/C(A) ⊕ C(X)/C(B))^∨ → H^q(X, A ∩ B) → H^{q+1}(X, A ∪ B) → …`

(`cohomologyMV_exact_at_*`), stated with the cohomology of the dual of the biproduct in the middle
(its identification with `H^q(X, A) × H^q(X, B)` is left to the consumer).

## Main results

* `RelativeSingularCohomology.relativeChainSequenceSection`,
  `RelativeSingularCohomology.dualRelativeChainSequence_shortExact`.
* `RelativeSingularCohomology.dualMap_subMap_sup_union_quasiIso`,
  `RelativeSingularCohomology.dualMap_unionComparison_quasiIso`,
  `RelativeSingularCohomology.unionComparisonCohomologyEquiv`.
* `RelativeSingularCohomology.cohomologyMV_exact_at_union`, `cohomologyMV_exact_at_pair`,
  `cohomologyMV_exact_at_inter`.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §3.1 (the Mayer–Vietoris sequence in
  cohomology)

## Tags

relative cohomology, Mayer–Vietoris, small chains
-/

open Set Function CategoryTheory

@[expose] public noncomputable section

namespace RelativeSingularCohomology

open SingularChains SingularMayerVietoris RelativeSingularHomology
open AlgebraicTopology.SingularCochains AlgebraicTopology.SingularCochains.DualEvaluation

variable {X : Type} [TopologicalSpace X]

/-! ### The dual relative chain sequence -/

/-- A degreewise section of `C(X)/C(A) ⊕ C(X)/C(B) → C(X)/(C(A) + C(B))`: the complement section
into `C(X)`, projected to `C(X)/C(A)` and included as the first summand. -/
def relativeChainSequenceSection (A B : Set X) (n : ℕ) :
    (relativeChainSequence A B).X₃.X n →ₗ[ℤ] (relativeChainSequence A B).X₂.X n :=
  ((Limits.biprod.inl : relativeComplex X A ⟶ relativeComplex X A ⊞ relativeComplex X B).f n).hom ∘ₗ
    ((relativeProjection X A).f n).hom ∘ₗ complementSection (isSpannedBy_sup A B n)

/-- The section is right-inverse to the second map of the relative chain sequence. -/
theorem relativeChainSequence_g_section (A B : Set X) (n : ℕ)
    (x : (relativeChainSequence A B).X₃.X n) :
    ((relativeChainSequence A B).g.f n).hom (relativeChainSequenceSection A B n x) = x := by
  have h1 : ∀ c : Chains X n, ((Limits.biprod.desc (leftToSup A B) (rightToSup A B)).f n).hom
      (((Limits.biprod.inl : relativeComplex X A ⟶ relativeComplex X A ⊞ relativeComplex X B).f n).hom
        (((relativeProjection X A).f n).hom c)) =
      ((leftToSup A B).f n).hom (((relativeProjection X A).f n).hom c) := fun c =>
    congrArg (fun f : relativeComplex X A ⟶ _ => (f.f n).hom (((relativeProjection X A).f n).hom c))
      (Limits.biprod.inl_desc (leftToSup A B) (rightToSup A B))
  have h2 : ∀ c : Chains X n, ((leftToSup A B).f n).hom (((relativeProjection X A).f n).hom c) =
      ((supportedSubmodule A ⊔ supportedSubmodule B).π.f n).hom c := fun c =>
    congrArg (fun f : singularComplex X ⟶ _ => (f.f n).hom c)
      (ChainSubmodule.π_quotientMap (ChainSubmodule.le_sup_left (supportedSubmodule A) (supportedSubmodule B)))
  change ((Limits.biprod.desc (leftToSup A B) (rightToSup A B)).f n).hom
    (((Limits.biprod.inl : relativeComplex X A ⟶ relativeComplex X A ⊞ relativeComplex X B).f n).hom
      (((relativeProjection X A).f n).hom (complementSection (isSpannedBy_sup A B n) x))) = x
  rw [h1, h2]
  exact π_complementSection (isSpannedBy_sup A B n) x

/-- The dual of the relative chain sequence is short exact. -/
theorem dualRelativeChainSequence_shortExact (A B : Set X) :
    (dualShortComplex intCoeff (relativeChainSequence A B)).ShortExact :=
  dualShortComplex_shortExact_of_section intCoeff _ (relativeChainSequence_shortExact A B)
    (relativeChainSequenceSection A B) (relativeChainSequence_g_section A B)

/-! ### The cochains of `C(X)/(C(A) + C(B))` compute `H^*(X, A ∪ B)` -/

/-- For open `A`, `B`, the dual of `C(A) + C(B) → C(A ∪ B)` is a quasi-isomorphism. -/
theorem dualMap_subMap_sup_union_quasiIso (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) :
    QuasiIso (dualMap intCoeff (ChainSubmodule.subMap (sup_le_supportedSubmodule_union A B))) := by
  have h1 := dualMap_ι_sup_quasiIso (trace A (A ∪ B)) (trace B (A ∪ B)) (isOpen_trace hA _)
    (isOpen_trace hB _) (trace_union_trace A B)
  have h2 : QuasiIso (dualMap intCoeff (smallInclusion (trace A (A ∪ B)) (trace B (A ∪ B)))) := by
    rw [smallInclusion_eq, dualMap_comp]
    infer_instance
  have h3 : QuasiIso (dualMap intCoeff (smallInclusion (trace A (A ∪ B)) (trace B (A ∪ B)) ≫
      (supportedComplexIso (A ∪ B)).hom)) := by
    rw [dualMap_comp]
    infer_instance
  rw [smallInclusion_trace_eq, dualMap_comp] at h3
  exact (quasiIso_iff_comp_right _ _).mp h3

/-- For open `A`, `B`, the dual of `C(X)/(C(A) + C(B)) → C(X, A ∪ B)` is a quasi-isomorphism. -/
theorem dualMap_unionComparison_quasiIso (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) :
    QuasiIso (dualMap intCoeff (unionComparison A B)) := by
  let ψ := dualShortComplexMap intCoeff
    (ChainSubmodule.quotientSequenceMap (sup_le_supportedSubmodule_union A B))
  have hS₁ := dualQuotientSequence_shortExact (supportedSubmodule (A ∪ B)) _
    (isSpannedBy_supportedSubmodule (A ∪ B))
  have hS₂ := dualQuotientSequence_shortExact (supportedSubmodule A ⊔ supportedSubmodule B) _
    (isSpannedBy_sup A B)
  have h₂ : QuasiIso ψ.τ₂ := by
    change QuasiIso (dualMap intCoeff (𝟙 (singularComplex X)))
    rw [dualMap_id]
    infer_instance
  have h₃ : QuasiIso ψ.τ₃ := dualMap_subMap_sup_union_quasiIso A B hA hB
  exact HomologicalComplex.HomologySequence.quasiIso_τ₁ ψ hS₁ hS₂ h₂ h₃

/-- The cohomology of the dual of `C(X)/(C(A) + C(B))`. -/
abbrev SupQuotientCohomology (A B : Set X) (q : ℕ) :=
  (dualShortComplex intCoeff (relativeChainSequence A B)).X₁.homology q

/-- `H^q(X, A ∪ B) ≃ H^q((C(X)/(C(A) + C(B)))^∨)` for open `A`, `B`. -/
def unionComparisonCohomologyEquiv (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (q : ℕ) :
    RelativeCohomology X (A ∪ B) q ≃+ SupQuotientCohomology A B q :=
  letI := dualMap_unionComparison_quasiIso A B hA hB
  (isoOfQuasiIsoAt (dualMap intCoeff (unionComparison A B)) q).addCommGroupIsoToAddEquiv

theorem unionComparisonCohomologyEquiv_apply (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (q : ℕ)
    (x : RelativeCohomology X (A ∪ B) q) :
    unionComparisonCohomologyEquiv A B hA hB q x =
      CohomologyLongExact.cohomologyHom (dualMap intCoeff (unionComparison A B)) q x := rfl

/-! ### The Mayer–Vietoris sequence -/

/-- The cohomology of the dual of `C(X)/C(A) ⊕ C(X)/C(B)`. -/
abbrev PairCohomology (A B : Set X) (q : ℕ) :=
  (dualShortComplex intCoeff (relativeChainSequence A B)).X₂.homology q

/-- `H^q(X, A ∪ B) → H^q((C(X)/C(A) ⊕ C(X)/C(B))^∨)`. -/
def cohomologyMVLeft (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (q : ℕ) :
    RelativeCohomology X (A ∪ B) q →+ PairCohomology A B q :=
  (CohomologyLongExact.cohomologyHom (dualShortComplex intCoeff (relativeChainSequence A B)).f q).comp
    (unionComparisonCohomologyEquiv A B hA hB q).toAddMonoidHom

/-- `H^q((C(X)/C(A) ⊕ C(X)/C(B))^∨) → H^q(X, A ∩ B)`. -/
abbrev cohomologyMVRight (A B : Set X) (q : ℕ) :
    PairCohomology A B q →+ RelativeCohomology X (A ∩ B) q :=
  CohomologyLongExact.cohomologyHom (dualShortComplex intCoeff (relativeChainSequence A B)).g q

/-- The Mayer–Vietoris connecting homomorphism `H^q(X, A ∩ B) → H^{q+1}(X, A ∪ B)`. -/
def cohomologyMVConnecting (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (q : ℕ) :
    RelativeCohomology X (A ∩ B) q →+ RelativeCohomology X (A ∪ B) (q + 1) :=
  (unionComparisonCohomologyEquiv A B hA hB (q + 1)).symm.toAddMonoidHom.comp
    (CohomologyLongExact.connectingHom (dualRelativeChainSequence_shortExact A B) q)

/-- Exactness at `H^{q+1}(X, A ∪ B)`. -/
theorem cohomologyMV_exact_at_union (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (q : ℕ) :
    AddMonoidHom.range (cohomologyMVConnecting A B hA hB q) =
      AddMonoidHom.ker (cohomologyMVLeft A B hA hB (q + 1)) := by
  have hS := dualRelativeChainSequence_shortExact A B
  have h := CohomologyLongExact.exact_at_first hS q
  set e := unionComparisonCohomologyEquiv A B hA hB (q + 1)
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change CohomologyLongExact.cohomologyHom (dualShortComplex intCoeff (relativeChainSequence A B)).f
      (q + 1) (e (e.symm (CohomologyLongExact.connectingHom hS q y))) = 0
    rw [AddEquiv.apply_symm_apply]
    have hy : CohomologyLongExact.connectingHom hS q y ∈ AddMonoidHom.ker
        (CohomologyLongExact.cohomologyHom (dualShortComplex intCoeff (relativeChainSequence A B)).f
          (q + 1)) := by
      rw [← h]
      exact AddMonoidHom.mem_range.mpr ⟨y, rfl⟩
    exact hy
  · intro hx
    have hx' : e x ∈ AddMonoidHom.ker (CohomologyLongExact.cohomologyHom
        (dualShortComplex intCoeff (relativeChainSequence A B)).f (q + 1)) := hx
    rw [← h] at hx'
    obtain ⟨y, hy⟩ := hx'
    refine ⟨y, ?_⟩
    change e.symm (CohomologyLongExact.connectingHom hS q y) = x
    rw [hy, AddEquiv.symm_apply_apply]

/-- Exactness at `H^q((C(X)/C(A) ⊕ C(X)/C(B))^∨)`. -/
theorem cohomologyMV_exact_at_pair (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (q : ℕ) :
    AddMonoidHom.range (cohomologyMVLeft A B hA hB q) = AddMonoidHom.ker (cohomologyMVRight A B q) := by
  have hS := dualRelativeChainSequence_shortExact A B
  set e := unionComparisonCohomologyEquiv A B hA hB q
  change _ = AddMonoidHom.ker (CohomologyLongExact.cohomologyHom
    (dualShortComplex intCoeff (relativeChainSequence A B)).g q)
  rw [← CohomologyLongExact.exact_at_second hS q]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨e.symm y, by
      change CohomologyLongExact.cohomologyHom (dualShortComplex intCoeff (relativeChainSequence A B)).f
        q (e (e.symm y)) = _
      rw [AddEquiv.apply_symm_apply]⟩

/-- Exactness at `H^q(X, A ∩ B)`. -/
theorem cohomologyMV_exact_at_inter (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (q : ℕ) :
    AddMonoidHom.range (cohomologyMVRight A B q) =
      AddMonoidHom.ker (cohomologyMVConnecting A B hA hB q) := by
  have hS := dualRelativeChainSequence_shortExact A B
  set e := unionComparisonCohomologyEquiv A B hA hB (q + 1)
  change AddMonoidHom.range (CohomologyLongExact.cohomologyHom
    (dualShortComplex intCoeff (relativeChainSequence A B)).g q) = _
  rw [CohomologyLongExact.exact_at_third hS q]
  ext x
  change CohomologyLongExact.connectingHom hS q x = 0 ↔
    e.symm (CohomologyLongExact.connectingHom hS q x) = 0
  rw [map_eq_zero_iff _ e.symm.injective]

end RelativeSingularCohomology
