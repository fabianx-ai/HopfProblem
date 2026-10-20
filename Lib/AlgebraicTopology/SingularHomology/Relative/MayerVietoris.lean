/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.Relative.Excision
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.BiprodSequence
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris.SmallHomology

/-!
# The relative Mayer–Vietoris sequence

For open sets `A, B ⊆ X` the relative homology groups of the pairs `(X, A ∩ B)`, `(X, A)`,
`(X, B)` and `(X, A ∪ B)` fit into a long exact sequence

  `⋯ → H_n(X, A ∩ B) → H_n(X, A) ⊕ H_n(X, B) → H_n(X, A ∪ B) → H_{n-1}(X, A ∩ B) → ⋯`

(Hatcher, *Algebraic Topology*, §2.2, the relative form of the Mayer–Vietoris sequence used in
the proof of Lemma 3.27).  It comes from the short exact sequence of chain complexes

  `0 → C(X)/C(A ∩ B) → C(X)/C(A) ⊞ C(X)/C(B) → C(X)/(C(A) + C(B)) → 0`

(`relativeChainSequence`, `relativeChainSequence_shortExact`: `C(A) ∩ C(B) = C(A ∩ B)` by
`supportedChainSubmodule_inf`, and the other two conditions are immediate) together with the
identification of `C(X)/(C(A) + C(B))` with `C(X, A ∪ B)`: the inclusion `C(A) + C(B) → C(A ∪ B)`
is a quasi-isomorphism for open `A`, `B` (the small simplices theorem for the cover
`{A, B}` of `A ∪ B`, transported into `X` by `smallComplexTraceIso`), hence so is
`C(X)/(C(A) + C(B)) → C(X, A ∪ B)` (`unionComparison_quasiIso`, the five lemma).

## Main definitions and results

* `RelativeSingularHomology.relativeLeftMap A B n : H_n(X, A ∩ B) → H_n(X, A) × H_n(X, B)`,
  `a ↦ (a|_A, -a|_B)`;
* `RelativeSingularHomology.relativeRightMap A B n : H_n(X, A) × H_n(X, B) → H_n(X, A ∪ B)`,
  `(a, b) ↦ a|_{A ∪ B} + b|_{A ∪ B}`;
* `RelativeSingularHomology.relativeConnecting A B hA hB n : H_{n+1}(X, A ∪ B) → H_n(X, A ∩ B)`;
* `RelativeSingularHomology.relative_exact_at_inter`, `relative_exact_at_pair`,
  `relative_exact_at_union` : exactness; `relativeRightMap_zero_surjective`.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §2.2 (Mayer–Vietoris sequences, relative
  form) and the proof of Lemma 3.27

## Tags

Mayer–Vietoris, relative homology, open cover
-/

open Set Function CategoryTheory

@[expose] public noncomputable section

namespace RelativeSingularHomology

open SingularChains SingularMayerVietoris

variable {X : Type} [TopologicalSpace X]

/-! ### The small chains of the union, inside `X` -/

/-- `C(A) + C(B) ≤ C(A ∪ B)`. -/
theorem sup_le_supportedSubmodule_union (A B : Set X) :
    supportedSubmodule A ⊔ supportedSubmodule B ≤ supportedSubmodule (A ∪ B) :=
  ChainSubmodule.sup_le (supportedSubmodule_mono subset_union_left)
    (supportedSubmodule_mono subset_union_right)

/-- The `(A, B)`-small chains of the subspace `A ∪ B` map onto `C(A) + C(B)` inside `X`. -/
theorem smallChainSubmodule_trace_map (A B : Set X) (n : ℕ) :
    (smallChainSubmodule (trace A (A ∪ B)) (trace B (A ∪ B)) n).map
        (inducedChain (subtypeInclusion (A ∪ B)) n) =
      supportedChainSubmodule A n ⊔ supportedChainSubmodule B n := by
  rw [smallChainSubmodule, Submodule.map_sup, ← supportedChainSubmodule_inter_eq_map,
    ← supportedChainSubmodule_inter_eq_map, inter_eq_left.mpr subset_union_left,
    inter_eq_left.mpr subset_union_right]

/-- The degree-`n` component of `smallComplexTraceIso`. -/
def smallTraceMap (A B : Set X) (n : ℕ) :
    smallChainSubmodule (trace A (A ∪ B)) (trace B (A ∪ B)) n →ₗ[ℤ]
      (supportedSubmodule A ⊔ supportedSubmodule B).carrier n :=
  ((inducedChain (subtypeInclusion (A ∪ B)) n).comp
    (smallChainSubmodule (trace A (A ∪ B)) (trace B (A ∪ B)) n).subtype).codRestrict _ (fun c => by
      change inducedChain (subtypeInclusion (A ∪ B)) n c.1 ∈
        supportedChainSubmodule A n ⊔ supportedChainSubmodule B n
      rw [← smallChainSubmodule_trace_map]
      exact ⟨c.1, c.2, rfl⟩)

@[simp]
theorem smallTraceMap_apply_coe (A B : Set X) (n : ℕ)
    (c : smallChainSubmodule (trace A (A ∪ B)) (trace B (A ∪ B)) n) :
    (smallTraceMap A B n c : Chains X n) = inducedChain (subtypeInclusion (A ∪ B)) n c.1 := rfl

theorem smallTraceMap_bijective (A B : Set X) (n : ℕ) : Function.Bijective (smallTraceMap A B n) := by
  constructor
  · intro a b hab
    exact Subtype.ext (subtypeInclusion_chain_injective (A ∪ B) n (congrArg Subtype.val hab :))
  · intro c
    have hc : (c : Chains X n) ∈ (smallChainSubmodule (trace A (A ∪ B)) (trace B (A ∪ B)) n).map
        (inducedChain (subtypeInclusion (A ∪ B)) n) := by
      rw [smallChainSubmodule_trace_map]
      exact c.2
    obtain ⟨a, ha, hac⟩ := hc
    exact ⟨⟨a, ha⟩, Subtype.ext hac⟩

/-- The complex of `(A, B)`-small chains of the subspace `A ∪ B` is isomorphic to the subcomplex
`C(A) + C(B)` of `C(X)`. -/
def smallComplexTraceIso (A B : Set X) :
    smallComplex (trace A (A ∪ B)) (trace B (A ∪ B)) ≅
      (supportedSubmodule A ⊔ supportedSubmodule B).subComplex :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (LinearEquiv.ofBijective _ (smallTraceMap_bijective A B n)).toModuleIso)
    (fun i j _ => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      apply Subtype.ext
      exact congrArg (fun g : Chains (A ∪ B : Set X) i ⟶ Chains X j => g.hom c.1)
        ((singularChainMap (subtypeInclusion (A ∪ B))).comm i j))

/-- The small inclusion of the subspace `A ∪ B` corresponds to `C(A) + C(B) → C(A ∪ B)`. -/
theorem smallInclusion_trace_eq (A B : Set X) :
    smallInclusion (trace A (A ∪ B)) (trace B (A ∪ B)) ≫ (supportedComplexIso (A ∪ B)).hom =
      (smallComplexTraceIso A B).hom ≫ ChainSubmodule.subMap (sup_le_supportedSubmodule_union A B) :=
  HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

/-- The trace of an open set on a subspace is open. -/
theorem isOpen_trace {U : Set X} (hU : IsOpen U) (V : Set X) : IsOpen (trace U V) :=
  hU.preimage continuous_subtype_val

omit [TopologicalSpace X] in
/-- The traces of `A` and `B` cover the subspace `A ∪ B`. -/
theorem trace_union_trace (A B : Set X) : trace A (A ∪ B) ∪ trace B (A ∪ B) = Set.univ := by
  ext ⟨x, hx⟩
  simpa [trace] using hx

/-- For open `A`, `B`, the inclusion `C(A) + C(B) → C(A ∪ B)` is a quasi-isomorphism (the small
simplices theorem for the cover `{A, B}` of `A ∪ B`). -/
theorem subMap_sup_quasiIso (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) :
    QuasiIso (ChainSubmodule.subMap (sup_le_supportedSubmodule_union A B)) := by
  have h := smallInclusion_quasiIso (trace A (A ∪ B)) (trace B (A ∪ B)) (isOpen_trace hA _)
    (isOpen_trace hB _) (trace_union_trace A B)
  have h' : QuasiIso (smallInclusion (trace A (A ∪ B)) (trace B (A ∪ B)) ≫
      (supportedComplexIso (A ∪ B)).hom) := inferInstance
  rw [smallInclusion_trace_eq] at h'
  exact (quasiIso_iff_comp_left (smallComplexTraceIso A B).hom _).mp h'

/-- The comparison `C(X)/(C(A) + C(B)) ⟶ C(X, A ∪ B)`. -/
abbrev unionComparison (A B : Set X) :
    (supportedSubmodule A ⊔ supportedSubmodule B).quotientComplex ⟶ relativeComplex X (A ∪ B) :=
  ChainSubmodule.quotientMap (sup_le_supportedSubmodule_union A B)

/-- For open `A`, `B`, `C(X)/(C(A) + C(B)) → C(X, A ∪ B)` is a quasi-isomorphism. -/
theorem unionComparison_quasiIso (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) :
    QuasiIso (unionComparison A B) :=
  letI := subMap_sup_quasiIso A B hA hB
  ChainSubmodule.quotientMap_quasiIso _

/-! ### The short exact sequence of relative chain complexes -/

/-- `C(A ∩ B) ≤ C(A)`. -/
theorem supportedSubmodule_inter_le_left (A B : Set X) :
    supportedSubmodule (A ∩ B) ≤ supportedSubmodule A :=
  supportedSubmodule_mono inter_subset_left

/-- `C(A ∩ B) ≤ C(B)`. -/
theorem supportedSubmodule_inter_le_right (A B : Set X) :
    supportedSubmodule (A ∩ B) ≤ supportedSubmodule B :=
  supportedSubmodule_mono inter_subset_right

/-- `C(X)/C(A ∩ B) → C(X)/C(A)`. -/
abbrev interToLeft (A B : Set X) : relativeComplex X (A ∩ B) ⟶ relativeComplex X A :=
  ChainSubmodule.quotientMap (supportedSubmodule_inter_le_left A B)

/-- `C(X)/C(A ∩ B) → C(X)/C(B)`. -/
abbrev interToRight (A B : Set X) : relativeComplex X (A ∩ B) ⟶ relativeComplex X B :=
  ChainSubmodule.quotientMap (supportedSubmodule_inter_le_right A B)

/-- `C(X)/C(A) → C(X)/(C(A) + C(B))`. -/
abbrev leftToSup (A B : Set X) :
    relativeComplex X A ⟶ (supportedSubmodule A ⊔ supportedSubmodule B).quotientComplex :=
  ChainSubmodule.quotientMap (ChainSubmodule.le_sup_left _ _)

/-- `C(X)/C(B) → C(X)/(C(A) + C(B))`. -/
abbrev rightToSup (A B : Set X) :
    relativeComplex X B ⟶ (supportedSubmodule A ⊔ supportedSubmodule B).quotientComplex :=
  ChainSubmodule.quotientMap (ChainSubmodule.le_sup_right _ _)

theorem interToLeft_leftToSup (A B : Set X) :
    interToLeft A B ≫ leftToSup A B = interToRight A B ≫ rightToSup A B := by
  rw [ChainSubmodule.quotientMap_comp, ChainSubmodule.quotientMap_comp]

/-- The short complex `C(X)/C(A ∩ B) → C(X)/C(A) ⊞ C(X)/C(B) → C(X)/(C(A) + C(B))`. -/
def relativeChainSequence (A B : Set X) : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  SmallChainBiprod.shortComplexOfComplexes (interToLeft A B) (interToRight A B) (leftToSup A B)
    (rightToSup A B) (interToLeft_leftToSup A B)

/-- The relative chain sequence is short exact. -/
theorem relativeChainSequence_shortExact (A B : Set X) : (relativeChainSequence A B).ShortExact := by
  apply SmallChainBiprod.shortExactOfComplexes_of_jointly_injective
  · intro n z hz₁ hz₂
    induction z using Submodule.Quotient.induction_on with
    | H z =>
    change relativeClass A n z = 0 at hz₁
    change relativeClass B n z = 0 at hz₂
    rw [relativeClass_eq_zero_iff] at hz₁ hz₂
    apply (relativeClass_eq_zero_iff (A ∩ B) n z).mpr
    rw [← supportedChainSubmodule_inf]
    exact ⟨hz₁, hz₂⟩
  · intro n s
    induction s using Submodule.Quotient.induction_on with
    | H s =>
    exact ⟨relativeClass A n s, 0, by rw [map_zero, add_zero]; rfl⟩
  · intro n x y hxy
    induction x using Submodule.Quotient.induction_on with
    | H x =>
    induction y using Submodule.Quotient.induction_on with
    | H y =>
    have hxy' : (Submodule.Quotient.mk x : Chains X n ⧸ (supportedSubmodule A ⊔ supportedSubmodule B).carrier n) =
        Submodule.Quotient.mk y := hxy
    rw [Submodule.Quotient.eq] at hxy'
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hxy'
    refine ⟨relativeClass (A ∩ B) n (x - a), ?_, ?_⟩
    · change relativeClass A n (x - a) = relativeClass A n x
      rw [Submodule.Quotient.eq]
      simpa using (supportedChainSubmodule A n).neg_mem ha
    · change relativeClass B n (x - a) = relativeClass B n y
      rw [Submodule.Quotient.eq]
      have : x - a - y = b := by
        calc x - a - y = (x - y) - a := by abel
          _ = (a + b) - a := by rw [hab]
          _ = b := add_sub_cancel_left a b
      rw [this]
      exact hb

/-! ### The relative Mayer–Vietoris sequence -/

/-- The left map `H_n(X, A ∩ B) → H_n(X, A) × H_n(X, B)`, `a ↦ (a|_A, -a|_B)`. -/
def relativeLeftMap (A B : Set X) (n : ℕ) :
    RelativeHomology X (A ∩ B) n →ₗ[ℤ] RelativeHomology X A n × RelativeHomology X B n :=
  biprodSequenceFirstMap (relativeChainSequence A B).f n

theorem relativeLeftMap_apply (A B : Set X) (n : ℕ) (a : RelativeHomology X (A ∩ B) n) :
    relativeLeftMap A B n a =
      (restriction inter_subset_left n a, -restriction inter_subset_right n a) := by
  apply Prod.ext
  · change homologyLinearMap (Limits.biprod.fst : relativeComplex X A ⊞ relativeComplex X B ⟶ _) n
      (homologyLinearMap (Limits.biprod.lift (interToLeft A B) (-interToRight A B)) n a) = _
    rw [← LinearMap.comp_apply, ← homologyLinearMap_comp, Limits.biprod.lift_fst]
  · change homologyLinearMap (Limits.biprod.snd : relativeComplex X A ⊞ relativeComplex X B ⟶ _) n
      (homologyLinearMap (Limits.biprod.lift (interToLeft A B) (-interToRight A B)) n a) = _
    rw [← LinearMap.comp_apply, ← homologyLinearMap_comp, Limits.biprod.lift_snd,
      homologyLinearMap_neg]
    rfl

/-- The right map `H_n(X, A) × H_n(X, B) → H_n(X, A ∪ B)` through the quotient by `C(A) + C(B)`. -/
def relativeRightMapSup (A B : Set X) (n : ℕ) :
    RelativeHomology X A n × RelativeHomology X B n →ₗ[ℤ]
      ((supportedSubmodule A ⊔ supportedSubmodule B).quotientComplex).homology n :=
  biprodSequenceSecondMap (relativeChainSequence A B).g n

/-- The right map `H_n(X, A) × H_n(X, B) → H_n(X, A ∪ B)`, `(a, b) ↦ a|_{A ∪ B} + b|_{A ∪ B}`. -/
def relativeRightMap (A B : Set X) (n : ℕ) :
    RelativeHomology X A n × RelativeHomology X B n →ₗ[ℤ] RelativeHomology X (A ∪ B) n :=
  (homologyLinearMap (unionComparison A B) n).comp (relativeRightMapSup A B n)

theorem relativeRightMap_apply (A B : Set X) (n : ℕ)
    (a : RelativeHomology X A n × RelativeHomology X B n) :
    relativeRightMap A B n a =
      restriction subset_union_left n a.1 + restriction subset_union_right n a.2 := by
  change homologyLinearMap (unionComparison A B) n (biprodSequenceSecondMap
    (Limits.biprod.desc (leftToSup A B) (rightToSup A B)) n a) = _
  rw [biprodSequenceSecondMap_desc, map_add]
  change homologyLinearMap (unionComparison A B) n (homologyLinearMap (leftToSup A B) n a.1) +
    homologyLinearMap (unionComparison A B) n (homologyLinearMap (rightToSup A B) n a.2) = _
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← homologyLinearMap_comp,
    ← homologyLinearMap_comp, ChainSubmodule.quotientMap_comp, ChainSubmodule.quotientMap_comp]

/-- The relative Mayer–Vietoris connecting homomorphism `H_{n+1}(X, A ∪ B) → H_n(X, A ∩ B)`. -/
def relativeConnecting (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    RelativeHomology X (A ∪ B) (n + 1) →ₗ[ℤ] RelativeHomology X (A ∩ B) n :=
  (connectingMap (relativeChainSequence_shortExact A B) n).comp
    (letI := unionComparison_quasiIso A B hA hB
     (isoOfQuasiIsoAt (unionComparison A B) (n + 1)).toLinearEquiv.symm.toLinearMap)

/-- The comparison of the sup-quotient homology with `H_n(X, A ∪ B)` as a linear equivalence. -/
def unionComparisonEquiv (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    ((supportedSubmodule A ⊔ supportedSubmodule B).quotientComplex).homology n ≃ₗ[ℤ]
      RelativeHomology X (A ∪ B) n :=
  letI := unionComparison_quasiIso A B hA hB
  (isoOfQuasiIsoAt (unionComparison A B) n).toLinearEquiv

theorem unionComparisonEquiv_toLinearMap (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    (unionComparisonEquiv A B hA hB n).toLinearMap = homologyLinearMap (unionComparison A B) n := rfl

theorem relativeRightMap_eq (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    relativeRightMap A B n =
      (unionComparisonEquiv A B hA hB n).toLinearMap.comp (relativeRightMapSup A B n) := rfl

theorem relativeConnecting_eq (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    relativeConnecting A B hA hB n =
      (connectingMap (relativeChainSequence_shortExact A B) n).comp
        (unionComparisonEquiv A B hA hB (n + 1)).symm.toLinearMap := rfl

/-- Exactness at `H_n(X, A ∩ B)`. -/
theorem relative_exact_at_inter (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    LinearMap.range (relativeConnecting A B hA hB n) = LinearMap.ker (relativeLeftMap A B n) := by
  rw [relativeConnecting_eq]
  exact (rightTransport_connecting_range (unionComparisonEquiv A B hA hB (n + 1))
    (connectingMap (relativeChainSequence_shortExact A B) n)).trans
    (biprodSequence_exact_at_leftHomology (relativeChainSequence_shortExact A B) n)

/-- Exactness at `H_n(X, A) × H_n(X, B)`. -/
theorem relative_exact_at_pair (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    LinearMap.range (relativeLeftMap A B n) = LinearMap.ker (relativeRightMap A B n) := by
  rw [relativeRightMap_eq A B hA hB]
  exact (biprodSequence_exact_at_middleHomology (relativeChainSequence_shortExact A B) n).trans
    (rightTransport_second_ker (unionComparisonEquiv A B hA hB n) (relativeRightMapSup A B n)).symm

/-- Exactness at `H_{n+1}(X, A ∪ B)`. -/
theorem relative_exact_at_union (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    LinearMap.range (relativeRightMap A B (n + 1)) =
      LinearMap.ker (relativeConnecting A B hA hB n) := by
  rw [relativeRightMap_eq A B hA hB, relativeConnecting_eq]
  exact rightTransport_range_eq_ker (unionComparisonEquiv A B hA hB (n + 1))
    (relativeRightMapSup A B (n + 1)) (connectingMap (relativeChainSequence_shortExact A B) n)
    (biprodSequence_exact_at_rightHomology (relativeChainSequence_shortExact A B) n)

/-- The degree-zero right map is surjective. -/
theorem relativeRightMap_zero_surjective (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) :
    Function.Surjective (relativeRightMap A B 0) := by
  rw [relativeRightMap_eq A B hA hB]
  exact rightTransport_second_surjective (unionComparisonEquiv A B hA hB 0) (relativeRightMapSup A B 0)
    (biprodSequence_second_zero_surjective (relativeChainSequence_shortExact A B))

end RelativeSingularHomology
