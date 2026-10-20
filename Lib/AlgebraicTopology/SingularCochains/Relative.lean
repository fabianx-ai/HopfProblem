/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Algebra.Homology.DualShortExact
public import Lib.Algebra.Homology.CohomologyLongExact
public import Lib.Algebra.Homology.QuasiIsoTauOne
public import Lib.AlgebraicTopology.SingularHomology.Relative.Excision
public import Lib.AlgebraicTopology.SingularSmallChains.Barycentric
public import Lib.AlgebraicTopology.SingularSmallChains.CochainHomotopy

/-!
# Relative singular cohomology with integer coefficients

The relative cochains of a pair `(X, A)` are the integer-valued functionals on the relative
chains, `C^q(X, A; ℤ) = Hom(C_q(X)/C_q(A), ℤ)` (Hatcher, *Algebraic Topology*, §3.1), the dual
`dualComplex (AddCommGrpCat.of ℤ) (relativeComplex X A)` of `Lib`'s cochain framework:

* `RelativeSingularCohomology.RelativeCohomology X A q := (relativeCochains X A).homology q`,
  `SingularCohomology X q := (complex X (AddCommGrpCat.of ℤ)).homology q` (the latter is `Lib`'s
  integral singular cohomology).

The dual of the pair sequence `0 → C(A) → C(X) → C(X, A) → 0` is short exact
(`dualPairSequence_shortExact`, through the retraction `subtypeChainRetraction`), which gives the
long exact cohomology sequence of the pair (`pairCoconnecting`, `cohomology_exact_at_*`).
Excision holds in cohomology for an open cover `U ∪ V = X`
(`cohomology_excision_bijective`): the chain map of the inclusion of pairs factors as in
`Relative/Excision.lean`, and the dual of `C^{U,V}(X)/C(U) → C(X)/C(U)` is a quasi-isomorphism
because the restriction of cochains to `(U, V)`-small chains is one (the small simplices theorem
in its cochain form, `cochainRestriction_homologyMap_isIso`) and the five lemma for the first
term (`quasiIso_τ₁`) applies to the dual short exact sequences.

## Main definitions and results

* `RelativeSingularCohomology.relativeCochains`, `RelativeCohomology`, `SingularCohomology`.
* `RelativeSingularCohomology.dualPairSequence_shortExact`, `pairCoconnecting`,
  `cohomology_exact_at_relative`, `cohomology_exact_at_space`, `cohomology_exact_at_subspace`.
* `RelativeSingularCohomology.relativeCochainMap`, `cohomologyRestriction`.
* `RelativeSingularCohomology.cohomology_excision_bijective`.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §3.1 (relative cohomology, the long exact
  sequence of a pair, excision)

## Tags

relative cohomology, long exact sequence, excision, small chains
-/

open Set Function CategoryTheory

@[expose] public noncomputable section

namespace RelativeSingularCohomology

open SingularChains SingularMayerVietoris RelativeSingularHomology
open AlgebraicTopology.SingularCochains AlgebraicTopology.SingularCochains.DualEvaluation

/-- Integer coefficients, as an object of `AddCommGrpCat`. -/
abbrev intCoeff : AddCommGrpCat.{0} := AddCommGrpCat.of ℤ

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-! ### Relative cochains and cohomology -/

/-- The relative cochain complex `C^*(X, A; ℤ) = Hom(C_*(X, A), ℤ)`. -/
abbrev relativeCochains (X : Type) [TopologicalSpace X] (A : Set X) :
    CochainComplex AddCommGrpCat.{0} ℕ :=
  dualComplex intCoeff (relativeComplex X A)

/-- Relative singular cohomology `H^q(X, A; ℤ)`. -/
abbrev RelativeCohomology (X : Type) [TopologicalSpace X] (A : Set X) (q : ℕ) :=
  (relativeCochains X A).homology q

/-- Singular cohomology `H^q(X; ℤ)` (as in `Lib`'s cochain framework). -/
abbrev SingularCohomology (X : Type) [TopologicalSpace X] (q : ℕ) :=
  (complex X intCoeff).homology q

/-- The cochain map of a map of pairs `(X, A) → (Y, B)`: precomposition with the relative chain
map. -/
abbrev relativeCochainMap (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : MapsTo f A B) :
    relativeCochains Y B ⟶ relativeCochains X A :=
  dualMap intCoeff (relativeChainMap f hf)

/-- The map `H^q(Y, B) → H^q(X, A)` induced by a map of pairs. -/
abbrev relativeCohomologyMap (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : MapsTo f A B) (q : ℕ) :
    RelativeCohomology Y B q →+ RelativeCohomology X A q :=
  CohomologyLongExact.cohomologyHom (relativeCochainMap f hf) q

/-- The restriction of relative cochains along `A ⊆ A'`: `C^*(X, A') → C^*(X, A)`. -/
abbrev cochainRestrictionMap {A A' : Set X} (h : A ⊆ A') : relativeCochains X A' ⟶ relativeCochains X A :=
  dualMap intCoeff (restrictionChainMap h)

/-- The restriction `H^q(X, A') → H^q(X, A)` along `A ⊆ A'`. -/
abbrev cohomologyRestriction {A A' : Set X} (h : A ⊆ A') (q : ℕ) :
    RelativeCohomology X A' q →+ RelativeCohomology X A q :=
  CohomologyLongExact.cohomologyHom (cochainRestrictionMap h) q

/-! ### The long exact sequence of the pair -/

/-- The dual of the pair sequence: `C^*(X, A) → C^*(X) → C^*(A)`. -/
abbrev dualPairSequence (X : Type) [TopologicalSpace X] (A : Set X) :
    ShortComplex (CochainComplex AddCommGrpCat.{0} ℕ) :=
  dualShortComplex intCoeff (pairSequence X A)

/-- The dual pair sequence is short exact. -/
theorem dualPairSequence_shortExact (A : Set X) : (dualPairSequence X A).ShortExact :=
  dualShortComplex_shortExact intCoeff (pairSequence X A) (pairSequence_shortExact A)
    (fun n => subtypeChainRetraction A n)
    (fun n x => LinearMap.congr_fun (subtypeChainRetraction_comp A n) x)

/-- `H^q(X, A) → H^q(X)`. -/
abbrev cohomologyProjection (A : Set X) (q : ℕ) : RelativeCohomology X A q →+ SingularCohomology X q :=
  CohomologyLongExact.cohomologyHom (dualMap intCoeff (relativeProjection X A)) q

/-- `H^q(X) → H^q(A)`. -/
abbrev cohomologySubspace (A : Set X) (q : ℕ) : SingularCohomology X q →+ SingularCohomology A q :=
  CohomologyLongExact.cohomologyHom (dualMap intCoeff (subspaceInclusion X A)) q

/-- The connecting homomorphism `H^q(A) → H^{q+1}(X, A)`. -/
abbrev pairCoconnecting (A : Set X) (q : ℕ) : SingularCohomology A q →+ RelativeCohomology X A (q + 1) :=
  CohomologyLongExact.connectingHom (dualPairSequence_shortExact A) q

/-- Exactness at `H^{q+1}(X, A)`. -/
theorem cohomology_exact_at_relative (A : Set X) (q : ℕ) :
    AddMonoidHom.range (pairCoconnecting A q) = AddMonoidHom.ker (cohomologyProjection A (q + 1)) :=
  CohomologyLongExact.exact_at_first (dualPairSequence_shortExact A) q

/-- Exactness at `H^q(X)`. -/
theorem cohomology_exact_at_space (A : Set X) (q : ℕ) :
    AddMonoidHom.range (cohomologyProjection A q) = AddMonoidHom.ker (cohomologySubspace A q) :=
  CohomologyLongExact.exact_at_second (dualPairSequence_shortExact A) q

/-- Exactness at `H^q(A)`. -/
theorem cohomology_exact_at_subspace (A : Set X) (q : ℕ) :
    AddMonoidHom.range (cohomologySubspace A q) = AddMonoidHom.ker (pairCoconnecting A q) :=
  CohomologyLongExact.exact_at_third (dualPairSequence_shortExact A) q

/-- `H^0(X, A) → H^0(X)` is injective. -/
theorem cohomologyProjection_zero_injective (A : Set X) : Function.Injective (cohomologyProjection A 0) :=
  CohomologyLongExact.cohomologyHom_f_zero_injective (dualPairSequence_shortExact A)

/-! ### Retractions onto supported chains -/

open scoped Classical in
/-- The retraction of chains onto the chains supported in `U`: a simplex not in `U` is sent to `0`. -/
def supportedRetraction (U : Set X) (n : ℕ) : Chains X n →ₗ[ℤ] (supportedSubmodule U).carrier n :=
  chainLift X n fun σ =>
    if h : Set.range σ ⊆ U then ⟨simplexChain X n σ, simplexChain_mem_supported U n σ h⟩ else 0

/-- The retraction fixes supported chains. -/
theorem supportedRetraction_of_mem (U : Set X) (n : ℕ) (c : (supportedSubmodule U).carrier n) :
    supportedRetraction U n c = c := by
  apply Subtype.ext
  refine LinearMap.eqOn_span (R := ℤ)
    (f := ((supportedSubmodule U).carrier n).subtype ∘ₗ supportedRetraction U n) (g := LinearMap.id)
    ?_ c.2
  rintro _ ⟨σ, hσ, rfl⟩
  have hσ' : Set.range σ ⊆ U := hσ
  change (supportedRetraction U n (simplexChain X n σ) : Chains X n) = simplexChain X n σ
  rw [supportedRetraction, chainLift_simplex, dif_pos hσ']

/-- The dual of an isomorphism of chain complexes is an isomorphism. -/
instance dualMap_isIso {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : K ⟶ L) [IsIso f] :
    IsIso (dualMap intCoeff f) :=
  inferInstanceAs (IsIso ((dualComplexFunctor intCoeff).map f.op))

/-! ### Sections of quotient projections

For a chain submodule `S` of `C(X)` spanned in each degree by the simplices satisfying a predicate
`P`, the map killing those simplices descends to a section of `C(X) → C(X)/S`.  This gives the
degreewise splittings needed to dualize the quotient sequences. -/

open scoped Classical in
/-- The chain map sending simplices with `P` to `0` and all other simplices to themselves. -/
def killChains (P : SingularSimplex X n → Prop) : Chains X n →ₗ[ℤ] Chains X n :=
  chainLift X n fun σ => if P σ then 0 else simplexChain X n σ

/-- A chain submodule is *spanned by `P`* in degree `n` when it is the span of the simplices with
`P`. -/
def IsSpannedBy (S : ChainSubmodule (singularComplex X)) (n : ℕ) (P : SingularSimplex X n → Prop) :
    Prop :=
  S.carrier n = Submodule.span ℤ (simplexChain X n '' {σ | P σ})

theorem isSpannedBy_supportedSubmodule (U : Set X) (n : ℕ) :
    IsSpannedBy (supportedSubmodule U) n fun σ => Set.range σ ⊆ U := rfl

theorem isSpannedBy_sup (U V : Set X) (n : ℕ) :
    IsSpannedBy (supportedSubmodule U ⊔ supportedSubmodule V) n
      fun σ => Set.range σ ⊆ U ∨ Set.range σ ⊆ V :=
  smallChainSubmodule_eq_span U V n

/-- Killing the spanning simplices does not change the class modulo `S`. -/
theorem π_killChains {S : ChainSubmodule (singularComplex X)} {n : ℕ} {P : SingularSimplex X n → Prop}
    (hP : IsSpannedBy S n P) (c : Chains X n) :
    (S.π.f n).hom (killChains P c) = (S.π.f n).hom c := by
  classical
  have h : (S.π.f n).hom ∘ₗ killChains P = (S.π.f n).hom := by
    apply chainMap_ext X n
    intro σ
    change (S.π.f n).hom (killChains P (simplexChain X n σ)) = (S.π.f n).hom (simplexChain X n σ)
    rw [killChains, chainLift_simplex]
    by_cases hσ : P σ
    · rw [if_pos hσ, map_zero]
      symm
      rw [ChainSubmodule.π_f_apply]
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      rw [hP]
      exact Submodule.subset_span ⟨σ, hσ, rfl⟩
    · rw [if_neg hσ]
  exact LinearMap.congr_fun h c

/-- Killing the spanning simplices kills `S`. -/
theorem killChains_eq_zero_of_mem {S : ChainSubmodule (singularComplex X)} {n : ℕ}
    {P : SingularSimplex X n → Prop} (hP : IsSpannedBy S n P) (c : Chains X n) (hc : c ∈ S.carrier n) :
    killChains P c = 0 := by
  classical
  rw [hP] at hc
  refine LinearMap.eqOn_span (R := ℤ) (f := killChains P) (g := 0) ?_ hc
  rintro _ ⟨σ, hσ, rfl⟩
  have hσ' : P σ := hσ
  change killChains P (simplexChain X n σ) = 0
  rw [killChains, chainLift_simplex, if_pos hσ']

/-- The section `C(X)/S → C(X)` of the projection, for `S` spanned by `P`. -/
def complementSection {S : ChainSubmodule (singularComplex X)} {n : ℕ} {P : SingularSimplex X n → Prop}
    (hP : IsSpannedBy S n P) : S.quotientComplex.X n →ₗ[ℤ] Chains X n :=
  Submodule.liftQ (S.carrier n) (killChains P) fun c hc => by
    rw [LinearMap.mem_ker]
    exact killChains_eq_zero_of_mem hP c hc

theorem complementSection_mk {S : ChainSubmodule (singularComplex X)} {n : ℕ}
    {P : SingularSimplex X n → Prop} (hP : IsSpannedBy S n P) (c : Chains X n) :
    complementSection hP (Submodule.Quotient.mk c) = killChains P c := rfl

/-- The projection left-inverts the complement section. -/
theorem π_complementSection {S : ChainSubmodule (singularComplex X)} {n : ℕ}
    {P : SingularSimplex X n → Prop} (hP : IsSpannedBy S n P) (x : S.quotientComplex.X n) :
    (S.π.f n).hom (complementSection hP x) = x := by
  induction x using Submodule.Quotient.induction_on with
  | H c =>
  rw [complementSection_mk, π_killChains hP]
  rfl

/-- The dual of the quotient sequence `0 → S → C(X) → C(X)/S → 0` is short exact when `S` is
spanned by simplices in every degree. -/
theorem dualQuotientSequence_shortExact (S : ChainSubmodule (singularComplex X))
    (P : ∀ n, SingularSimplex X n → Prop) (hP : ∀ n, IsSpannedBy S n (P n)) :
    (dualShortComplex intCoeff S.quotientSequence).ShortExact :=
  dualShortComplex_shortExact_of_section intCoeff _ S.quotientSequence_shortExact
    (fun n => complementSection (hP n)) (fun n x => π_complementSection (hP n) x)

/-! ### The small-chain subcomplex of a two-set cover -/

/-- The two-set cover `![U, V]`. -/
abbrev twoCover (U V : Set X) : Fin 2 → Set X := ![U, V]

/-- A simplex is `![U, V]`-small iff it lies in `U` or in `V`. -/
theorem isSmallSimplex_twoCover_iff (U V : Set X) {n : ℕ} (σ : SingularSimplex X n) :
    TopCat.SingularSmallChains.IsSmallSimplex (twoCover U V) σ ↔ Set.range σ ⊆ U ∨ Set.range σ ⊆ V := by
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
  · rintro (h | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩

/-- The `![U, V]`-small submodule is `C(U) + C(V)`. -/
theorem smallChains_submodule_twoCover (U V : Set X) (n : ℕ) :
    TopCat.SingularSmallChains.submodule (twoCover U V) n =
      (supportedSubmodule U ⊔ supportedSubmodule V).carrier n := by
  change TopCat.SingularSmallChains.submodule (twoCover U V) n =
    supportedChainSubmodule U n ⊔ supportedChainSubmodule V n
  show _ = smallChainSubmodule U V n
  rw [smallChainSubmodule_eq_span]
  unfold TopCat.SingularSmallChains.submodule
  congr 1
  ext c
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨σ, (isSmallSimplex_twoCover_iff U V σ).mp hσ, rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨σ, (isSmallSimplex_twoCover_iff U V σ).mpr hσ, rfl⟩

/-- The `![U, V]`-small chains in degree `n` are the chains of `C(U) + C(V)`. -/
def smallChainsTwoCoverEquiv (U V : Set X) (n : ℕ) :
    TopCat.SingularSmallChains.submodule (twoCover U V) n ≃ₗ[ℤ]
      (supportedSubmodule U ⊔ supportedSubmodule V).carrier n :=
  LinearEquiv.ofEq _ _ (smallChains_submodule_twoCover U V n)

@[simp]
theorem smallChainsTwoCoverEquiv_apply_coe (U V : Set X) (n : ℕ)
    (c : TopCat.SingularSmallChains.submodule (twoCover U V) n) :
    (smallChainsTwoCoverEquiv U V n c).1 = c.1 := rfl

/-- The `![U, V]`-small chain complex is the subcomplex `C(U) + C(V)` of `C(X)`. -/
def smallComplexTwoCoverIso (U V : Set X) :
    TopCat.SingularSmallChains.complex (twoCover U V) ≅
      (supportedSubmodule U ⊔ supportedSubmodule V).subComplex :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (smallChainsTwoCoverEquiv U V n).toModuleIso)
    (fun i j _ => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      apply Subtype.ext
      rfl)

/-- The small inclusion of the two-set cover factors through the subcomplex. -/
theorem inclusion_twoCover_eq (U V : Set X) :
    TopCat.SingularSmallChains.inclusion (twoCover U V) =
      (smallComplexTwoCoverIso U V).hom ≫ ChainSubmodule.ι (supportedSubmodule U ⊔ supportedSubmodule V) :=
  HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

/-- For an open cover `U ∪ V = X`, restriction of integral cochains to `C(U) + C(V)` is a
quasi-isomorphism (the cochain form of the small simplices theorem). -/
theorem dualMap_ι_sup_quasiIso (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) :
    QuasiIso (dualMap intCoeff (ChainSubmodule.ι (supportedSubmodule U ⊔ supportedSubmodule V))) := by
  have hUo : ∀ i, IsOpen (twoCover U V i) := fun i => by fin_cases i <;> assumption
  have hUc : (⋃ i, twoCover U V i) = Set.univ := by
    rw [← hcover]
    ext x
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
    · rintro (h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
  have hres : ∀ n, IsIso (HomologicalComplex.homologyMap
      (TopCat.SingularSmallChains.cochainRestriction intCoeff (twoCover U V)) n) :=
    TopCat.SingularSmallChains.cochainRestriction_homologyMap_isIso intCoeff (twoCover U V)
      (TopCat.SingularSmallChains.Barycentric.smallChainHomotopyEquiv (twoCover U V) hUo hUc)
      (TopCat.SingularSmallChains.Barycentric.smallChainHomotopyEquiv_hom (twoCover U V) hUo hUc)
  have hq : QuasiIso (TopCat.SingularSmallChains.cochainRestriction intCoeff (twoCover U V)) := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact hres n
  have heq : TopCat.SingularSmallChains.cochainRestriction intCoeff (twoCover U V) =
      dualMap intCoeff (ChainSubmodule.ι (supportedSubmodule U ⊔ supportedSubmodule V)) ≫
        dualMap intCoeff (smallComplexTwoCoverIso U V).hom := by
    show dualMap intCoeff (TopCat.SingularSmallChains.inclusion (twoCover U V)) = _
    rw [inclusion_twoCover_eq]
    exact dualMap_comp intCoeff _ _
  rw [heq] at hq
  exact (quasiIso_iff_comp_right _ _).mp hq

/-! ### Excision in cohomology -/

/-- The dual of `C^{U,V}(X)/C(U) → C(X)/C(U)` is a quasi-isomorphism for an open cover
`U ∪ V = X`. -/
theorem dualMap_relativeToQuotient_quasiIso (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) :
    QuasiIso (dualMap intCoeff (ChainSubmodule.relativeToQuotient
      (supportedSubmodule U ⊔ supportedSubmodule V) (supportedSubmodule U))) := by
  set S := supportedSubmodule U
  set T := supportedSubmodule V
  have hle : S ≤ S ⊔ T := ChainSubmodule.le_sup_left S T
  -- the morphism of dual sequences
  let ψ := dualShortComplexMap intCoeff (ChainSubmodule.relativeSequenceToQuotientSequence hle)
  have hS₁ : (dualShortComplex intCoeff S.quotientSequence).ShortExact :=
    dualShortComplex_shortExact intCoeff _ S.quotientSequence_shortExact
      (fun n => supportedRetraction U n) (fun n x => supportedRetraction_of_mem U n x :)
  have hS₂ : (dualShortComplex intCoeff (ChainSubmodule.relativeSequence hle)).ShortExact :=
    dualShortComplex_shortExact intCoeff _ (ChainSubmodule.relativeSequence_shortExact hle)
      (fun n => (supportedRetraction U n).comp ((S ⊔ T).carrier n).subtype)
      (fun n x => supportedRetraction_of_mem U n x :)
  have h₂ : QuasiIso ψ.τ₂ := dualMap_ι_sup_quasiIso U V hU hV hcover
  have h₃ : QuasiIso ψ.τ₃ := by
    change QuasiIso (dualMap intCoeff (𝟙 S.subComplex))
    rw [dualMap_id]
    infer_instance
  exact HomologicalComplex.HomologySequence.quasiIso_τ₁ ψ hS₁ hS₂ h₂ h₃

/-- **Excision in cohomology** (Hatcher, §3.1): for open `U, V` with `U ∪ V = X`, the inclusion of
pairs `(V, V ∩ U) → (X, U)` induces isomorphisms `H^q(X, U) ≅ H^q(V, V ∩ U)`. -/
theorem cohomology_excision_bijective (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (q : ℕ) :
    Function.Bijective
      (relativeCohomologyMap (subtypeInclusion V) (mapsTo_subtypeInclusion_trace U V) q) := by
  have hq : QuasiIso (relativeCochainMap (subtypeInclusion V) (mapsTo_subtypeInclusion_trace U V)) := by
    change QuasiIso (dualMap intCoeff (relativeChainMap (subtypeInclusion V) (mapsTo_subtypeInclusion_trace U V)))
    rw [excisionChainMap_eq, dualMap_comp, dualMap_comp]
    have := dualMap_relativeToQuotient_quasiIso U V hU hV hcover
    have := (ChainSubmodule.relativeSupIso (supportedSubmodule V) (supportedSubmodule U)).isIso_hom
    infer_instance
  have := (quasiIsoAt_iff_isIso_homologyMap _ q).mp (hq.quasiIsoAt q)
  exact (ConcreteCategory.isIso_iff_bijective _).mp this

end RelativeSingularCohomology
