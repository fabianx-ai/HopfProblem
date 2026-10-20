/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.Relative.Chains

/-!
# Functoriality of relative singular homology

A map of pairs `f : (X, A) → (Y, B)` — a continuous map `f : C(X, Y)` with `f '' A ⊆ B` — induces a
chain map `C(X, A) ⟶ C(Y, B)` (`relativeChainMap`) and hence `relativeHomologyMap f hf n :
H_n(X, A) → H_n(Y, B)`, functorially (`relativeHomologyMap_id`, `relativeHomologyMap_comp`).  The
map of pairs is a morphism of the short exact pair sequences (`pairSequenceMap`), so the long exact
sequences of `(X, A)` and `(Y, B)` are connected by a commutative ladder, in particular the
connecting homomorphisms commute with the induced maps (`pairConnecting_naturality`).

The five lemma then gives the main tool of the file: a map of pairs inducing isomorphisms on the
homology of the spaces and on the homology of the subspaces induces isomorphisms on relative
homology (`relativeHomologyMap_bijective_of_bijective`, Hatcher, *Algebraic Topology*, the remark
after Theorem 2.13 and Proposition 2.19's use of the five lemma).  Homeomorphisms of pairs are the
first instance (`relativeHomologyEquivOfHomeomorph`).

## Main definitions and results

* `RelativeSingularHomology.pairRestrict` : the restriction `A → B` of a map of pairs.
* `RelativeSingularHomology.relativeChainMap`, `RelativeSingularHomology.relativeHomologyMap`,
  `relativeHomologyMap_id`, `relativeHomologyMap_comp`.
* `RelativeSingularHomology.pairSequenceMap`, `RelativeSingularHomology.pairConnecting_naturality`.
* `RelativeSingularHomology.relativeChainMap_quasiIso_of_quasiIso`,
  `RelativeSingularHomology.relativeHomologyMap_bijective_of_bijective` : the five lemma.
* `RelativeSingularHomology.relativeHomologyEquivOfHomeomorph`.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §2.1, relative homology groups; the five lemma
  (§2.1, after Theorem 2.13)

## Tags

relative homology, map of pairs, five lemma
-/

open Set Function CategoryTheory

@[expose] public noncomputable section

namespace RelativeSingularHomology

open SingularChains SingularMayerVietoris

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-! ### Maps of pairs on chains -/

/-- Pushforward along a map of pairs carries chains supported in `A` to chains supported in `B`. -/
theorem inducedChain_mem_supported_of_mapsTo (f : C(X, Y)) {A : Set X} {B : Set Y}
    (hf : MapsTo f A B) (n : ℕ) (c : Chains X n) (hc : c ∈ supportedChainSubmodule A n) :
    inducedChain f n c ∈ supportedChainSubmodule B n := by
  have hle : supportedChainSubmodule A n ≤ (supportedChainSubmodule B n).comap (inducedChain f n) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨σ, hσ, rfl⟩
    change inducedChain f n (simplexChain X n σ) ∈ supportedChainSubmodule B n
    rw [inducedChain_simplex]
    apply simplexChain_mem_supported
    rintro _ ⟨s, rfl⟩
    exact hf (hσ ⟨s, rfl⟩)
  exact hle hc

/-- The restriction of a map of pairs to the subspaces. -/
def pairRestrict (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : MapsTo f A B) : C(A, B) :=
  ⟨hf.restrict f A B, f.continuous.restrict hf⟩

@[simp]
theorem pairRestrict_apply_coe (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : MapsTo f A B) (a : A) :
    (pairRestrict f hf a : Y) = f a := rfl

/-- The subspace inclusion composed with a map of pairs is the restriction composed with the
inclusion. -/
theorem subtypeInclusion_comp_pairRestrict (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : MapsTo f A B) :
    (subtypeInclusion B).comp (pairRestrict f hf) = f.comp (subtypeInclusion A) := by
  ext a
  rfl

/-- The identity is a map of pairs `(X, A) → (X, A)`. -/
theorem mapsTo_contId (A : Set X) : MapsTo (ContinuousMap.id X) A A := fun _ hx => hx

/-- The chain map induced by the identity is the identity. -/
theorem singularChainMap_id : singularChainMap (ContinuousMap.id X) = 𝟙 (singularComplex X) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  exact inducedChain_id n

/-- The chain map induced by a composite is the composite of the chain maps. -/
theorem singularChainMap_comp (f : C(X, Y)) (g : C(Y, Z)) :
    singularChainMap (g.comp f) = singularChainMap f ≫ singularChainMap g := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  exact inducedChain_comp f g n

/-- The chain map `C(X, A) ⟶ C(Y, B)` of a map of pairs. -/
def relativeChainMap (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : MapsTo f A B) :
    relativeComplex X A ⟶ relativeComplex Y B :=
  ChainSubmodule.quotientMapOfChainMap (singularChainMap f)
    (fun n c hc => inducedChain_mem_supported_of_mapsTo f hf n c hc)

@[simp]
theorem relativeChainMap_relativeClass (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : MapsTo f A B)
    (n : ℕ) (c : Chains X n) :
    ((relativeChainMap f hf).f n).hom (relativeClass A n c) = relativeClass B n (inducedChain f n c) :=
  rfl

theorem relativeChainMap_id {A : Set X} (hf : MapsTo (ContinuousMap.id X) A A) :
    relativeChainMap (ContinuousMap.id X) hf = 𝟙 (relativeComplex X A) :=
  ChainSubmodule.quotientComplex_hom_ext fun n c => by
    change relativeClass A n (inducedChain (ContinuousMap.id X) n c) = relativeClass A n c
    rw [inducedChain_id]
    rfl

theorem relativeChainMap_comp (f : C(X, Y)) (g : C(Y, Z)) {A : Set X} {B : Set Y} {C : Set Z}
    (hf : MapsTo f A B) (hg : MapsTo g B C) (hgf : MapsTo (g.comp f) A C) :
    relativeChainMap f hf ≫ relativeChainMap g hg = relativeChainMap (g.comp f) hgf :=
  ChainSubmodule.quotientComplex_hom_ext fun n c => by
    change relativeClass C n (inducedChain g n (inducedChain f n c)) =
      relativeClass C n (inducedChain (g.comp f) n c)
    rw [inducedChain_comp]
    rfl

/-- The relative projection is natural. -/
theorem relativeProjection_relativeChainMap (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : MapsTo f A B) :
    relativeProjection X A ≫ relativeChainMap f hf = singularChainMap f ≫ relativeProjection Y B :=
  ChainSubmodule.π_quotientMapOfChainMap _ _

/-- The restriction along `A ⊆ A'` is the chain map of the identity as a map of pairs. -/
theorem restrictionChainMap_eq {A A' : Set X} (h : A ⊆ A') (h' : MapsTo (ContinuousMap.id X) A A') :
    restrictionChainMap h = relativeChainMap (ContinuousMap.id X) h' :=
  ChainSubmodule.quotientComplex_hom_ext fun n c => by
    change relativeClass A' n c = relativeClass A' n (inducedChain (ContinuousMap.id X) n c)
    rw [inducedChain_id]
    rfl

/-! ### Maps of pairs on homology -/

/-- The map `H_n(X, A) → H_n(Y, B)` induced by a map of pairs. -/
abbrev relativeHomologyMap (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : MapsTo f A B) (n : ℕ) :
    RelativeHomology X A n →ₗ[ℤ] RelativeHomology Y B n :=
  homologyLinearMap (relativeChainMap f hf) n

theorem relativeHomologyMap_id {A : Set X} (hf : MapsTo (ContinuousMap.id X) A A) (n : ℕ) :
    relativeHomologyMap (ContinuousMap.id X) hf n = LinearMap.id := by
  change homologyLinearMap (relativeChainMap (ContinuousMap.id X) hf) n = LinearMap.id
  rw [relativeChainMap_id, homologyLinearMap, HomologicalComplex.homologyMap_id]
  rfl

theorem relativeHomologyMap_comp (f : C(X, Y)) (g : C(Y, Z)) {A : Set X} {B : Set Y} {C : Set Z}
    (hf : MapsTo f A B) (hg : MapsTo g B C) (hgf : MapsTo (g.comp f) A C) (n : ℕ) :
    (relativeHomologyMap g hg n).comp (relativeHomologyMap f hf n) =
      relativeHomologyMap (g.comp f) hgf n := by
  change (homologyLinearMap (relativeChainMap g hg) n).comp (homologyLinearMap (relativeChainMap f hf) n) =
    homologyLinearMap (relativeChainMap (g.comp f) hgf) n
  rw [← homologyLinearMap_comp, relativeChainMap_comp f g hf hg hgf]

/-- Equal maps of pairs induce equal maps on relative homology. -/
theorem relativeHomologyMap_congr {f g : C(X, Y)} (hfg : f = g) {A : Set X} {B : Set Y}
    (hf : MapsTo f A B) (hg : MapsTo g A B) (n : ℕ) :
    relativeHomologyMap f hf n = relativeHomologyMap g hg n := by
  subst hfg
  rfl

theorem relativeHomologyMap_comp_apply (f : C(X, Y)) (g : C(Y, Z)) {A : Set X} {B : Set Y} {C : Set Z}
    (hf : MapsTo f A B) (hg : MapsTo g B C) (hgf : MapsTo (g.comp f) A C) (n : ℕ)
    (a : RelativeHomology X A n) :
    relativeHomologyMap g hg n (relativeHomologyMap f hf n a) =
      relativeHomologyMap (g.comp f) hgf n a :=
  LinearMap.congr_fun (relativeHomologyMap_comp f g hf hg hgf n) a

/-- The relative projection on homology is natural. -/
theorem relativeHomologyMap_relativeProjectionHomologyMap (f : C(X, Y)) {A : Set X} {B : Set Y}
    (hf : MapsTo f A B) (n : ℕ) :
    (relativeHomologyMap f hf n).comp (relativeProjectionHomologyMap A n) =
      (relativeProjectionHomologyMap B n).comp (singularHomologyMap f n) := by
  change (homologyLinearMap (relativeChainMap f hf) n).comp (homologyLinearMap (relativeProjection X A) n) =
    (homologyLinearMap (relativeProjection Y B) n).comp (homologyLinearMap (singularChainMap f) n)
  rw [← homologyLinearMap_comp, relativeProjection_relativeChainMap, homologyLinearMap_comp]

/-- Restriction on homology is the map of the identity as a map of pairs. -/
theorem restriction_eq {A A' : Set X} (h : A ⊆ A') (h' : MapsTo (ContinuousMap.id X) A A') (n : ℕ) :
    restriction h n = relativeHomologyMap (ContinuousMap.id X) h' n := by
  change homologyLinearMap (restrictionChainMap h) n = _
  rw [restrictionChainMap_eq h h']

/-! ### The ladder of long exact sequences -/

/-- A map of pairs as a morphism of the pair sequences. -/
def pairSequenceMap (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : MapsTo f A B) :
    pairSequence X A ⟶ pairSequence Y B where
  τ₁ := singularChainMap (pairRestrict f hf)
  τ₂ := singularChainMap f
  τ₃ := relativeChainMap f hf
  comm₁₂ := by
    change singularChainMap (pairRestrict f hf) ≫ singularChainMap (subtypeInclusion B) =
      singularChainMap (subtypeInclusion A) ≫ singularChainMap f
    rw [← singularChainMap_comp, ← singularChainMap_comp, subtypeInclusion_comp_pairRestrict]
  comm₂₃ := (relativeProjection_relativeChainMap f hf).symm

@[simp] theorem pairSequenceMap_τ₁ (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : MapsTo f A B) :
    (pairSequenceMap f hf).τ₁ = singularChainMap (pairRestrict f hf) := rfl
@[simp] theorem pairSequenceMap_τ₂ (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : MapsTo f A B) :
    (pairSequenceMap f hf).τ₂ = singularChainMap f := rfl
@[simp] theorem pairSequenceMap_τ₃ (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : MapsTo f A B) :
    (pairSequenceMap f hf).τ₃ = relativeChainMap f hf := rfl

/-- The connecting homomorphisms commute with the maps induced by a map of pairs. -/
theorem pairConnecting_naturality (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : MapsTo f A B) (n : ℕ) :
    (singularHomologyMap (pairRestrict f hf) n).comp (pairConnecting X A n) =
      (pairConnecting Y B n).comp (relativeHomologyMap f hf (n + 1)) :=
  connectingMap_naturality (pairSequence_shortExact A) (pairSequenceMap f hf)
    (pairSequence_shortExact B) n

/-! ### The five lemma -/

/-- A map of pairs that is a quasi-isomorphism on the spaces and on the subspaces is a
quasi-isomorphism on the relative complexes. -/
theorem relativeChainMap_quasiIso_of_quasiIso (f : C(X, Y)) {A : Set X} {B : Set Y}
    (hf : MapsTo f A B) (hX : QuasiIso (singularChainMap f))
    (hA : QuasiIso (singularChainMap (pairRestrict f hf))) : QuasiIso (relativeChainMap f hf) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃ (pairSequenceMap f hf) (pairSequence_shortExact A)
    (pairSequence_shortExact B) hA hX

/-- A chain map whose homology maps are all bijective is a quasi-isomorphism. -/
theorem quasiIso_of_bijective {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L)
    (h : ∀ n, Function.Bijective (homologyLinearMap φ n)) : QuasiIso φ := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact (ConcreteCategory.isIso_iff_bijective _).mpr (h n)

/-- The homology maps of a quasi-isomorphism are bijective. -/
theorem bijective_of_quasiIso {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) [QuasiIso φ]
    (n : ℕ) : Function.Bijective (homologyLinearMap φ n) :=
  (ConcreteCategory.isIso_iff_bijective _).mp
    ((quasiIsoAt_iff_isIso_homologyMap φ n).mp inferInstance)

/-- **The five lemma for pairs**: a map of pairs inducing isomorphisms on the homology of the
spaces and of the subspaces induces isomorphisms on relative homology. -/
theorem relativeHomologyMap_bijective_of_bijective (f : C(X, Y)) {A : Set X} {B : Set Y}
    (hf : MapsTo f A B) (hX : ∀ n, Function.Bijective (singularHomologyMap f n))
    (hA : ∀ n, Function.Bijective (singularHomologyMap (pairRestrict f hf) n)) (n : ℕ) :
    Function.Bijective (relativeHomologyMap f hf n) :=
  letI := relativeChainMap_quasiIso_of_quasiIso f hf (quasiIso_of_bijective _ hX)
    (quasiIso_of_bijective _ hA)
  bijective_of_quasiIso (relativeChainMap f hf) n

/-- The relative homology equivalence of a map of pairs satisfying the five-lemma hypotheses. -/
def relativeHomologyEquivOfBijective (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : MapsTo f A B)
    (hX : ∀ n, Function.Bijective (singularHomologyMap f n))
    (hA : ∀ n, Function.Bijective (singularHomologyMap (pairRestrict f hf) n)) (n : ℕ) :
    RelativeHomology X A n ≃ₗ[ℤ] RelativeHomology Y B n :=
  LinearEquiv.ofBijective _ (relativeHomologyMap_bijective_of_bijective f hf hX hA n)

@[simp]
theorem relativeHomologyEquivOfBijective_apply (f : C(X, Y)) {A : Set X} {B : Set Y}
    (hf : MapsTo f A B) (hX) (hA) (n : ℕ) (a : RelativeHomology X A n) :
    relativeHomologyEquivOfBijective f hf hX hA n a = relativeHomologyMap f hf n a := rfl

/-! ### Homeomorphisms of pairs -/

/-- A homeomorphism `e : X ≃ₜ Y` with `e '' A = B` induces isomorphisms on relative homology. -/
theorem relativeHomologyMap_bijective_of_homeomorph (e : X ≃ₜ Y) {A : Set X} {B : Set Y}
    (he : ∀ x, x ∈ A ↔ e x ∈ B) (n : ℕ) :
    Function.Bijective (relativeHomologyMap (e : C(X, Y)) (fun x hx => (he x).mp hx) n) := by
  have hf : MapsTo (e : C(X, Y)) A B := fun x hx => (he x).mp hx
  have hinv : MapsTo (e.symm : C(Y, X)) B A := fun y hy => by
    rw [he]
    simpa using hy
  have hcomp₁ : (e.symm : C(Y, X)).comp (e : C(X, Y)) = ContinuousMap.id X := by ext; simp
  have hcomp₂ : (e : C(X, Y)).comp (e.symm : C(Y, X)) = ContinuousMap.id Y := by ext; simp
  have h₁ : (relativeHomologyMap (e.symm : C(Y, X)) hinv n).comp (relativeHomologyMap (e : C(X, Y)) hf n) =
      LinearMap.id := by
    rw [relativeHomologyMap_comp _ _ hf hinv (hcomp₁ ▸ mapsTo_contId A),
      relativeHomologyMap_congr hcomp₁ _ (mapsTo_contId A), relativeHomologyMap_id]
  have h₂ : (relativeHomologyMap (e : C(X, Y)) hf n).comp (relativeHomologyMap (e.symm : C(Y, X)) hinv n) =
      LinearMap.id := by
    rw [relativeHomologyMap_comp _ _ hinv hf (hcomp₂ ▸ mapsTo_contId B),
      relativeHomologyMap_congr hcomp₂ _ (mapsTo_contId B), relativeHomologyMap_id]
  constructor
  · intro a b hab
    have := congrArg (relativeHomologyMap (e.symm : C(Y, X)) hinv n) hab
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, h₁] at this
  · intro b
    exact ⟨relativeHomologyMap (e.symm : C(Y, X)) hinv n b, LinearMap.congr_fun h₂ b⟩

/-- The relative homology equivalence of a homeomorphism of pairs. -/
def relativeHomologyEquivOfHomeomorph (e : X ≃ₜ Y) {A : Set X} {B : Set Y}
    (he : ∀ x, x ∈ A ↔ e x ∈ B) (n : ℕ) : RelativeHomology X A n ≃ₗ[ℤ] RelativeHomology Y B n :=
  LinearEquiv.ofBijective _ (relativeHomologyMap_bijective_of_homeomorph e he n)

@[simp]
theorem relativeHomologyEquivOfHomeomorph_apply (e : X ≃ₜ Y) {A : Set X} {B : Set Y}
    (he : ∀ x, x ∈ A ↔ e x ∈ B) (n : ℕ) (a : RelativeHomology X A n) :
    relativeHomologyEquivOfHomeomorph e he n a =
      relativeHomologyMap (e : C(X, Y)) (fun x hx => (he x).mp hx) n a := rfl

end RelativeSingularHomology
