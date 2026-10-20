/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.Relative.Functoriality
public import Lib.AlgebraicTopology.SingularHomology.ModuleHomology

/-!
# Supports of singular chains and relative cycles

The *support* of a singular chain `c` is the union of the images of the simplices occurring in `c`
with a nonzero coefficient (`chainSupport`).  It is compact (`isCompact_chainSupport`), and a chain
is supported in `U` in the sense of `SingularMayerVietoris.supportedChainSubmodule` exactly when its
support lies in `U` (`mem_supportedChainSubmodule_iff`).  Consequently a relative cycle of the pair
`(X, A)` — a chain `c` with `∂c` supported in `A` — is a relative cycle of every pair `(X, A')` with
`chainSupport (∂c) ⊆ A'`, and its classes in `H_n(X, A')` and `H_n(X, A)` correspond under
restriction when `A' ⊆ A` (`restriction_relativeHomologyClass`).  This is the compactness
mechanism of Hatcher's Lemma 3.27, step (3): a class in `H_n(M, M ∖ A)` is the image of a class in
`H_n(M, M ∖ K)` for a compact neighbourhood `K` of `A` missing the (compact) support of `∂c`.

## Main definitions and results

* `RelativeSingularHomology.chainSupport`, `isCompact_chainSupport`,
  `mem_supportedChainSubmodule_iff`.
* `RelativeSingularHomology.relativeHomologyClass A n c hc` : the class of a relative cycle.
* `RelativeSingularHomology.relativeHomologyClass_surjective`,
  `RelativeSingularHomology.restriction_relativeHomologyClass`,
  `RelativeSingularHomology.relativeHomologyMap_relativeHomologyClass`.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §2.1 (relative cycles), proof of Lemma 3.27 (3)

## Tags

singular chain, support, relative cycle
-/

open Set Function CategoryTheory

@[expose] public noncomputable section

namespace RelativeSingularHomology

open SingularChains SingularMayerVietoris

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-! ### The support of a chain -/

/-- The support of a singular chain: the union of the images of the simplices occurring in it. -/
def chainSupport {n : ℕ} (c : Chains X n) : Set X :=
  ⋃ σ ∈ (chainsRepr X n c).support, Set.range σ

theorem mem_chainSupport_iff {n : ℕ} (c : Chains X n) (x : X) :
    x ∈ chainSupport c ↔ ∃ σ ∈ (chainsRepr X n c).support, x ∈ Set.range σ := by
  simp [chainSupport]

/-- The support of a chain is compact. -/
theorem isCompact_chainSupport {n : ℕ} (c : Chains X n) : IsCompact (chainSupport c) :=
  (chainsRepr X n c).support.isCompact_biUnion fun σ _ => isCompact_range σ.continuous

/-- A chain is supported in `U` exactly when its support lies in `U`. -/
theorem mem_supportedChainSubmodule_iff (U : Set X) {n : ℕ} (c : Chains X n) :
    c ∈ supportedChainSubmodule U n ↔ chainSupport c ⊆ U := by
  rw [supportedChainSubmodule, mem_simplex_span_iff]
  constructor
  · intro h x hx
    obtain ⟨σ, hσ, hxσ⟩ := (mem_chainSupport_iff c x).mp hx
    exact h hσ hxσ
  · intro h σ hσ y hy
    exact h ((mem_chainSupport_iff c y).mpr ⟨σ, hσ, hy⟩)

/-- The support of a chain is contained in every set the chain is supported in. -/
theorem chainSupport_subset_of_mem {U : Set X} {n : ℕ} {c : Chains X n}
    (hc : c ∈ supportedChainSubmodule U n) : chainSupport c ⊆ U :=
  (mem_supportedChainSubmodule_iff U c).mp hc

/-- A chain is supported in its own support. -/
theorem mem_supportedChainSubmodule_chainSupport {n : ℕ} (c : Chains X n) :
    c ∈ supportedChainSubmodule (chainSupport c) n :=
  (mem_supportedChainSubmodule_iff _ c).mpr subset_rfl

/-- The support of the boundary of a chain lies in the support of the chain. -/
theorem chainSupport_boundary_subset {n : ℕ} (c : Chains X (n + 1)) :
    chainSupport (((singularComplex X).d (n + 1) n).hom c) ⊆ chainSupport c :=
  chainSupport_subset_of_mem (boundary_mem_supported _ n c (mem_supportedChainSubmodule_chainSupport c))

/-- The support of the image of a chain lies in the image of its support. -/
theorem chainSupport_inducedChain_subset (f : C(X, Y)) {n : ℕ} (c : Chains X n) :
    chainSupport (inducedChain f n c) ⊆ f '' chainSupport c :=
  chainSupport_subset_of_mem (inducedChain_mem_supported_of_mapsTo f (mapsTo_image f _) n c
    (mem_supportedChainSubmodule_chainSupport c))

/-! ### Relative cycles and their classes -/

/-- A chain whose boundary is supported in `A` is a relative cycle of `(X, A)`. -/
theorem relativeClass_boundary_eq_zero (A : Set X) (n : ℕ) (c : Chains X n)
    (hc : ((singularComplex X).d n (n - 1)).hom c ∈ supportedChainSubmodule A (n - 1)) :
    ((relativeComplex X A).d n (n - 1)).hom (relativeClass A n c) = 0 := by
  rw [relativeComplex_d_relativeClass]
  exact (relativeClass_eq_zero_iff A (n - 1) _).mpr hc

/-- The relative cycle determined by a chain with boundary supported in `A`. -/
def relativeCycle (A : Set X) (n : ℕ) (c : Chains X n)
    (hc : ((singularComplex X).d n (n - 1)).hom c ∈ supportedChainSubmodule A (n - 1)) :
    ModuleHomology.Cycle (relativeComplex X A) n :=
  ModuleHomology.mkCycle _ n (relativeClass A n c) (relativeClass_boundary_eq_zero A n c hc)

@[simp]
theorem relativeCycle_val (A : Set X) (n : ℕ) (c : Chains X n) (hc) :
    (relativeCycle A n c hc).1 = relativeClass A n c := rfl

/-- The homology class in `H_n(X, A)` of a chain whose boundary is supported in `A`. -/
def relativeHomologyClass (A : Set X) (n : ℕ) (c : Chains X n)
    (hc : ((singularComplex X).d n (n - 1)).hom c ∈ supportedChainSubmodule A (n - 1)) :
    RelativeHomology X A n :=
  ModuleHomology.cycleClass _ n (relativeCycle A n c hc)

/-- Every class of `H_n(X, A)` is the class of a relative cycle. -/
theorem relativeHomologyClass_surjective (A : Set X) (n : ℕ) (a : RelativeHomology X A n) :
    ∃ (c : Chains X n) (hc : ((singularComplex X).d n (n - 1)).hom c ∈
      supportedChainSubmodule A (n - 1)), relativeHomologyClass A n c hc = a := by
  obtain ⟨z, rfl⟩ := ModuleHomology.cycleClass_surjective (relativeComplex X A) n a
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective (supportedChainSubmodule A n) z.1
  have hz := ModuleHomology.cycle_condition (relativeComplex X A) n z
  rw [← hc] at hz
  change ((relativeComplex X A).d n (n - 1)).hom (relativeClass A n c) = 0 at hz
  rw [relativeComplex_d_relativeClass, relativeClass_eq_zero_iff] at hz
  refine ⟨c, hz, ?_⟩
  unfold relativeHomologyClass
  congr 1
  exact Subtype.ext hc

/-- Two relative cycles with the same class differ by a boundary and a chain in `A`. -/
theorem relativeHomologyClass_eq_zero_iff (A : Set X) (n : ℕ) (c : Chains X n) (hc) :
    relativeHomologyClass A n c hc = 0 ↔
      ∃ b : Chains X (n + 1), ((singularComplex X).d (n + 1) n).hom b - c ∈
        supportedChainSubmodule A n := by
  rw [relativeHomologyClass, ModuleHomology.cycleClass_eq_zero_iff]
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨b', rfl⟩ := Submodule.Quotient.mk_surjective (supportedChainSubmodule A (n + 1)) b
    refine ⟨b', ?_⟩
    rw [relativeCycle_val] at hb
    change relativeClass A n _ = relativeClass A n c at hb
    rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub] at hb
    exact (relativeClass_eq_zero_iff A n _).mp hb
  · rintro ⟨b, hb⟩
    refine ⟨relativeClass A (n + 1) b, ?_⟩
    rw [relativeCycle_val, relativeComplex_d_relativeClass, ← sub_eq_zero,
      ← Submodule.Quotient.mk_sub]
    exact (relativeClass_eq_zero_iff A n _).mpr hb

/-- The class of a relative cycle restricts along `A' ⊆ A` to the class of the same chain. -/
theorem restriction_relativeHomologyClass {A' A : Set X} (h : A' ⊆ A) (n : ℕ) (c : Chains X n)
    (hc' : ((singularComplex X).d n (n - 1)).hom c ∈ supportedChainSubmodule A' (n - 1)) :
    restriction h n (relativeHomologyClass A' n c hc') =
      relativeHomologyClass A n c (supportedChainSubmodule_mono h (n - 1) hc') := by
  unfold relativeHomologyClass
  change (HomologicalComplex.homologyMap (restrictionChainMap h) n).hom _ = _
  rw [ModuleHomology.homologyMap_cycleClass]
  congr 1
  apply Subtype.ext
  rw [ModuleHomology.mapCycles_val, relativeCycle_val, relativeCycle_val,
    restrictionChainMap_relativeClass]

/-- A map of pairs carries the class of a relative cycle to the class of the image chain. -/
theorem relativeHomologyMap_relativeHomologyClass (f : C(X, Y)) {A : Set X} {B : Set Y}
    (hf : MapsTo f A B) (n : ℕ) (c : Chains X n)
    (hc : ((singularComplex X).d n (n - 1)).hom c ∈ supportedChainSubmodule A (n - 1)) :
    relativeHomologyMap f hf n (relativeHomologyClass A n c hc) =
      relativeHomologyClass B n (inducedChain f n c) (by
        have hcomm : ((singularComplex Y).d n (n - 1)).hom (inducedChain f n c) =
            inducedChain f (n - 1) (((singularComplex X).d n (n - 1)).hom c) :=
          congrArg (fun g : Chains X n ⟶ Chains Y (n - 1) => g.hom c)
            ((singularChainMap f).comm n (n - 1))
        rw [hcomm]
        exact inducedChain_mem_supported_of_mapsTo f hf (n - 1) _ hc) := by
  unfold relativeHomologyClass
  change (HomologicalComplex.homologyMap (relativeChainMap f hf) n).hom _ = _
  rw [ModuleHomology.homologyMap_cycleClass]
  congr 1
  apply Subtype.ext
  rw [ModuleHomology.mapCycles_val, relativeCycle_val, relativeCycle_val,
    relativeChainMap_relativeClass]

/-- The relative projection on homology sends the class of a cycle to its relative class. -/
theorem relativeProjectionHomologyMap_cycleClass (A : Set X) (n : ℕ)
    (z : ModuleHomology.Cycle (singularComplex X) n) :
    relativeProjectionHomologyMap A n (ModuleHomology.cycleClass _ n z) =
      relativeHomologyClass A n z.1 (by
        rw [ModuleHomology.cycle_condition]
        exact Submodule.zero_mem _) := by
  unfold relativeHomologyClass
  change (HomologicalComplex.homologyMap (relativeProjection X A) n).hom _ = _
  rw [ModuleHomology.homologyMap_cycleClass]
  congr 1
  apply Subtype.ext
  rw [ModuleHomology.mapCycles_val, relativeCycle_val]
  rfl

end RelativeSingularHomology
