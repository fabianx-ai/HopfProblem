/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.AlgebraicTopology.SingularCochains
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.AlgebraicTopology.TopologicalSimplex

/-!
# Cover-small native singular chains

This file isolates the algebraic first layer of the small-chain theorem.  It uses Mathlib's
native integral singular-chain complex, its genuine coproduct simplex generators, and an
arbitrary family of subsets.  No cohomology comparison or Mayer--Vietoris exact sequence is
assumed.

The subcomplex `Cₙ^𝒰(X) ⊆ Cₙ(X)` of `𝒰`-small chains and its inclusion are the objects of
Hatcher, *Algebraic Topology*, Proposition 2.21 (Bredon IV.17; Spanier 4.4).
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Set
open scoped Simplicial

namespace TopCat.SingularSmallChains

/-- The native singular simplicial set. -/
abbrev singularSet (X : Type) [TopologicalSpace X] : SSet :=
  TopCat.toSSet.obj (TopCat.of X)

/-- Continuous singular `n`-simplices in Mathlib's standard-simplex model. -/
abbrev SingularSimplex (X : Type) [TopologicalSpace X] (n : ℕ) :=
  C(stdSimplex ℝ (Fin (n + 1)), X)

/-- A continuous simplex as an index of Mathlib's singular simplicial set. -/
def simplexIndex (X : Type) [TopologicalSpace X] (n : ℕ) (sigma : SingularSimplex X n) :
    (singularSet X).obj (Opposite.op (SimplexCategory.mk n)) :=
  ((TopCat.of X).toSSetObjEquiv (Opposite.op (SimplexCategory.mk n))).symm sigma

/-- The native singular-chain generator with coefficient one. -/
def simplexChain (X : Type) [TopologicalSpace X] (n : ℕ) (sigma : SingularSimplex X n) :
    (AlgebraicTopology.SingularCochains.chains X).X n :=
  ((singularSet X).ιChainComplex
    (R := ModuleCat.of ℤ ℤ) (simplexIndex X n sigma)) 1

/-- The coproduct map determined by values on native simplex generators. -/
def chainLift (X : Type) [TopologicalSpace X] (n : ℕ)
    {M : Type} [AddCommGroup M] [Module ℤ M]
    (f : SingularSimplex X n → M) :
    (AlgebraicTopology.SingularCochains.chains X).X n →ₗ[ℤ] M :=
  (Sigma.desc (fun s : (singularSet X).obj (Opposite.op (SimplexCategory.mk n)) =>
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ M
      (f ((TopCat.of X).toSSetObjEquiv (Opposite.op (SimplexCategory.mk n)) s)))) :
    (AlgebraicTopology.SingularCochains.chains X).X n ⟶ ModuleCat.of ℤ M).hom

/-- The map determined by values on simplex generators takes the prescribed value on each
generator. -/
@[simp]
theorem chainLift_simplex (X : Type) [TopologicalSpace X] (n : ℕ)
    {M : Type} [AddCommGroup M] [Module ℤ M]
    (f : SingularSimplex X n → M) (sigma : SingularSimplex X n) :
    chainLift X n f (simplexChain X n sigma) = f sigma := by
  have h := Sigma.ι_desc
    (fun s : (singularSet X).obj (Opposite.op (SimplexCategory.mk n)) =>
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ M
        (f ((TopCat.of X).toSSetObjEquiv (Opposite.op (SimplexCategory.mk n)) s))))
    (simplexIndex X n sigma)
  have he := congrArg
    (fun g : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ M => g.hom 1) h
  change chainLift X n f (simplexChain X n sigma) =
    (LinearMap.toSpanSingleton ℤ M
      (f ((TopCat.of X).toSSetObjEquiv (Opposite.op (SimplexCategory.mk n))
        (simplexIndex X n sigma)))) 1 at he
  simpa only [LinearMap.toSpanSingleton_apply_one, simplexIndex, Equiv.apply_symm_apply]
    using he

/-- A native linear map on chains is determined by its simplex values. -/
theorem chainMap_ext (X : Type) [TopologicalSpace X] (n : ℕ)
    {M : Type} [AddCommGroup M] [Module ℤ M]
    {f g : (AlgebraicTopology.SingularCochains.chains X).X n →ₗ[ℤ] M}
    (h : ∀ sigma : SingularSimplex X n,
      f (simplexChain X n sigma) = g (simplexChain X n sigma)) :
    f = g := by
  have hcat :
      (ModuleCat.ofHom f : (AlgebraicTopology.SingularCochains.chains X).X n ⟶
        ModuleCat.of ℤ M) = ModuleCat.ofHom g := by
    apply SSet.chainComplex_hom_ext
    intro s
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change f (((singularSet X).ιChainComplex
      (R := ModuleCat.of ℤ ℤ) s).hom 1) =
      g (((singularSet X).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) s).hom 1)
    have hs := h ((TopCat.of X).toSSetObjEquiv
      (Opposite.op (SimplexCategory.mk n)) s)
    simpa only [simplexChain, simplexIndex, Equiv.symm_apply_apply] using hs
  exact congrArg ModuleCat.Hom.hom hcat

/-- Coordinates of a native chain in the continuous-simplex coproduct. -/
def chainsRepr (X : Type) [TopologicalSpace X] (n : ℕ) :
    (AlgebraicTopology.SingularCochains.chains X).X n →ₗ[ℤ]
      (SingularSimplex X n →₀ ℤ) :=
  chainLift X n (fun sigma => Finsupp.single sigma 1)

/-- Assemble finitely supported simplex coefficients into a native chain. -/
def chainsFromFinsupp (X : Type) [TopologicalSpace X] (n : ℕ) :
    (SingularSimplex X n →₀ ℤ) →ₗ[ℤ]
      (AlgebraicTopology.SingularCochains.chains X).X n :=
  Finsupp.linearCombination ℤ (simplexChain X n)

/-- Assembling a single coefficient `a` at `σ` gives the chain `a • σ`. -/
@[simp]
theorem chainsFromFinsupp_single (X : Type) [TopologicalSpace X] (n : ℕ)
    (sigma : SingularSimplex X n) (a : ℤ) :
    chainsFromFinsupp X n (Finsupp.single sigma a) = a • simplexChain X n sigma :=
  (Finsupp.linearCombination_single ℤ (v := simplexChain X n) a sigma).trans
    (int_smul_eq_zsmul
      ((AlgebraicTopology.SingularCochains.chains X).X n).isModule a
        (simplexChain X n sigma))

/-- Reassembling a chain from its simplex coordinates recovers the chain. -/
theorem chainsFromFinsupp_comp_repr (X : Type) [TopologicalSpace X] (n : ℕ) :
    (chainsFromFinsupp X n).comp (chainsRepr X n) = LinearMap.id := by
  apply chainMap_ext X n
  intro sigma
  simp only [LinearMap.comp_apply, chainsRepr, chainLift_simplex,
    chainsFromFinsupp_single, one_smul, LinearMap.id_apply]

/-- The coordinates of the chain assembled from a finitely supported family are that
family. -/
theorem chainsRepr_comp_fromFinsupp (X : Type) [TopologicalSpace X] (n : ℕ) :
    (chainsRepr X n).comp (chainsFromFinsupp X n) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro sigma a
  simp only [LinearMap.comp_apply, chainsFromFinsupp_single, map_zsmul,
    chainsRepr, chainLift_simplex, Finsupp.smul_single, smul_eq_mul, mul_one,
    LinearMap.id_apply]

/-- Native integral singular chains are freely generated by continuous simplices. -/
def chainsEquivFinsupp (X : Type) [TopologicalSpace X] (n : ℕ) :
    (AlgebraicTopology.SingularCochains.chains X).X n ≃ₗ[ℤ]
      (SingularSimplex X n →₀ ℤ) where
  toLinearMap := chainsRepr X n
  invFun := chainsFromFinsupp X n
  left_inv c := LinearMap.congr_fun (chainsFromFinsupp_comp_repr X n) c
  right_inv c := LinearMap.congr_fun (chainsRepr_comp_fromFinsupp X n) c

/-- The genuine continuous-simplex basis of native integral singular chains. -/
def chainBasis (X : Type) [TopologicalSpace X] (n : ℕ) :
    Module.Basis (SingularSimplex X n) ℤ
      ((AlgebraicTopology.SingularCochains.chains X).X n) :=
  Module.Basis.ofRepr (chainsEquivFinsupp X n)

/-- The coordinate map of the simplex basis is `chainsEquivFinsupp`. -/
@[simp]
theorem chainBasis_repr (X : Type) [TopologicalSpace X] (n : ℕ) :
    (chainBasis X n).repr = chainsEquivFinsupp X n := rfl

/-- The basis vector at a singular simplex `σ` is the generator chain of `σ`. -/
@[simp]
theorem chainBasis_apply (X : Type) [TopologicalSpace X] (n : ℕ)
    (sigma : SingularSimplex X n) : chainBasis X n sigma = simplexChain X n sigma := by
  change chainsFromFinsupp X n (Finsupp.single sigma 1) = _
  rw [chainsFromFinsupp_single, one_smul]

/-- Membership in a span of native simplex generators is detected by finitely supported
coordinates. -/
theorem mem_simplex_span_iff (X : Type) [TopologicalSpace X] (n : ℕ)
    (S : Set (SingularSimplex X n))
    (c : (AlgebraicTopology.SingularCochains.chains X).X n) :
    c ∈ Submodule.span ℤ (simplexChain X n '' S) ↔
      ↑(chainsEquivFinsupp X n c).support ⊆ S := by
  simpa only [chainBasis_apply, chainBasis_repr] using
    (chainBasis X n).mem_span_image (m := c) (s := S)

/-- A simplex is small when one member of the family contains its image. -/
def IsSmallSimplex {X : Type} [TopologicalSpace X] {I : Type}
    (U : I → Set X) {n : ℕ} (sigma : SingularSimplex X n) : Prop :=
  ∃ i, Set.range sigma ⊆ U i

/-- The submodule generated by simplices carried by one member of `U`. -/
def submodule {X : Type} [TopologicalSpace X] {I : Type}
    (U : I → Set X) (n : ℕ) :
  Submodule ℤ ((AlgebraicTopology.SingularCochains.chains X).X n) :=
  Submodule.span ℤ
    (simplexChain X n '' (IsSmallSimplex U : Set (SingularSimplex X n)))

/-- A carried simplex belongs to the cover-small submodule. -/
theorem simplexChain_mem {X : Type} [TopologicalSpace X] {I : Type}
    (U : I → Set X) (n : ℕ) (sigma : SingularSimplex X n)
    (hsigma : IsSmallSimplex U sigma) :
    simplexChain X n sigma ∈ submodule U n :=
  Submodule.subset_span ⟨sigma, hsigma, rfl⟩

/-- The standard face inclusion deleting vertex `i`. -/
def simplexFace (n : ℕ) (i : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 2))) :=
  ⟨stdSimplex.map (SimplexCategory.δ i).toOrderHom,
    stdSimplex.continuous_map (SimplexCategory.δ i).toOrderHom⟩

/-- The `i`-th face of the index of a singular simplex `σ` is the index of the restriction of
`σ` to the `i`-th face of the standard simplex. -/
theorem simplexIndex_face (X : Type) [TopologicalSpace X] (n : ℕ)
    (sigma : SingularSimplex X (n + 1)) (i : Fin (n + 2)) :
    (singularSet X).δ i (simplexIndex X (n + 1) sigma) =
      simplexIndex X n (sigma.comp (simplexFace n i)) := by
  rfl

/-- The alternating face formula on a native simplex generator. -/
theorem boundary_simplex (X : Type) [TopologicalSpace X] (n : ℕ)
    (sigma : SingularSimplex X (n + 1)) :
    (AlgebraicTopology.SingularCochains.chains X).d (n + 1) n
        (simplexChain X (n + 1) sigma) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        simplexChain X n (sigma.comp (simplexFace n i)) := by
  have h := (singularSet X).ιChainComplex_d
    (R := ModuleCat.of ℤ ℤ) (simplexIndex X (n + 1) sigma)
  let ev : (ModuleCat.of ℤ ℤ ⟶
      (AlgebraicTopology.SingularCochains.chains X).X n) →+
      (AlgebraicTopology.SingularCochains.chains X).X n :=
    { toFun := fun f => f.hom 1
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have he := congrArg ev h
  change (AlgebraicTopology.SingularCochains.chains X).d (n + 1) n
      (simplexChain X (n + 1) sigma) =
    ev (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
      (singularSet X).ιChainComplex
        ((singularSet X).δ i (simplexIndex X (n + 1) sigma))) at he
  simp only [map_sum, simplexIndex_face] at he
  refine he.trans ?_
  apply Finset.sum_congr rfl
  intro i hi
  exact ev.map_zsmul ((-1 : ℤ) ^ i.val)
    ((singularSet X).ιChainComplex
      (simplexIndex X n (sigma.comp (simplexFace n i))))

/-- A face of a simplex carried by `V` is still carried by `V`. -/
theorem simplex_face_subset {X : Type} [TopologicalSpace X]
    (V : Set X) (n : ℕ) (sigma : SingularSimplex X (n + 1))
    (hsigma : Set.range sigma ⊆ V) (i : Fin (n + 2)) :
    Set.range (sigma.comp (simplexFace n i)) ⊆ V := by
  rintro x ⟨s, rfl⟩
  exact hsigma ⟨simplexFace n i s, rfl⟩

/-- Native singular boundaries preserve cover-small chains. -/
theorem boundary_mem {X : Type} [TopologicalSpace X] {I : Type}
    (U : I → Set X) (i j : ℕ)
    (c : (AlgebraicTopology.SingularCochains.chains X).X i)
    (hc : c ∈ submodule U i) :
    ((AlgebraicTopology.SingularCochains.chains X).d i j).hom c ∈ submodule U j := by
  by_cases hij : (ComplexShape.down ℕ).Rel i j
  · have he : j + 1 = i := hij
    subst i
    have hle : submodule U (j + 1) ≤
        (submodule U j).comap
          ((AlgebraicTopology.SingularCochains.chains X).d (j + 1) j).hom := by
      apply Submodule.span_le.mpr
      rintro _ ⟨sigma, ⟨index, hsigma⟩, rfl⟩
      change ((AlgebraicTopology.SingularCochains.chains X).d (j + 1) j).hom
        (simplexChain X (j + 1) sigma) ∈ submodule U j
      rw [boundary_simplex]
      apply Submodule.sum_mem
      intro k hk
      apply (submodule U j).toAddSubgroup.zsmul_mem
      apply simplexChain_mem
      exact ⟨index, simplex_face_subset (U index) j sigma hsigma k⟩
    exact hle hc
  · have he := congrArg
      (fun f : (AlgebraicTopology.SingularCochains.chains X).X i ⟶
          (AlgebraicTopology.SingularCochains.chains X).X j => f.hom c)
      ((AlgebraicTopology.SingularCochains.chains X).shape i j hij)
    rw [he]
    exact Submodule.zero_mem _

/-- The `ℤ`-module structure on the submodule of `𝒰`-small chains. -/
instance smallChainModule {X : Type} [TopologicalSpace X] {I : Type}
    (U : I → Set X) (n : ℕ) : Module ℤ (submodule U n) :=
  (submodule U n).module

/-- The native differential restricted to cover-small chains. -/
def differential {X : Type} [TopologicalSpace X] {I : Type}
    (U : I → Set X) (i j : ℕ) : submodule U i →ₗ[ℤ] submodule U j :=
  ((((AlgebraicTopology.SingularCochains.chains X).d i j).hom.comp
    (submodule U i).subtype).codRestrict _
      (fun c => boundary_mem U i j c.1 c.2))

/-- The differential of the small-chain subcomplex is the restriction of the singular
boundary. -/
@[simp]
theorem differential_val {X : Type} [TopologicalSpace X] {I : Type}
    (U : I → Set X) (i j : ℕ) (c : submodule U i) :
    (differential U i j c).1 =
      ((AlgebraicTopology.SingularCochains.chains X).d i j).hom c.1 := rfl

/-- The genuine cover-small subcomplex of native integral singular chains. -/
def complex {X : Type} [TopologicalSpace X] {I : Type}
    (U : I → Set X) : ChainComplex (ModuleCat ℤ) ℕ where
  X n := ModuleCat.of ℤ (submodule U n)
  d i j := ModuleCat.ofHom (differential U i j)
  shape i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact congrArg
      (fun f : (AlgebraicTopology.SingularCochains.chains X).X i ⟶
          (AlgebraicTopology.SingularCochains.chains X).X j => f.hom c.1)
      ((AlgebraicTopology.SingularCochains.chains X).shape i j hij)
  d_comp_d' i j k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact congrArg
      (fun f : (AlgebraicTopology.SingularCochains.chains X).X i ⟶
          (AlgebraicTopology.SingularCochains.chains X).X k => f.hom c.1)
      ((AlgebraicTopology.SingularCochains.chains X).d_comp_d i j k)

/-- Literal inclusion of cover-small chains into native singular chains. -/
def inclusion {X : Type} [TopologicalSpace X] {I : Type}
    (U : I → Set X) : complex U ⟶ AlgebraicTopology.SingularCochains.chains X where
  f n := ModuleCat.ofHom (submodule U n).subtype
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    rfl

/-- In each degree the inclusion of the small-chain subcomplex is the underlying chain. -/
@[simp]
theorem inclusion_f_apply {X : Type} [TopologicalSpace X] {I : Type}
    (U : I → Set X) (n : ℕ) (c : (complex U).X n) :
    (inclusion U).f n c = c.1 := rfl

/-- The inclusion of the small-chain subcomplex is injective in each degree. -/
theorem inclusion_f_injective {X : Type} [TopologicalSpace X] {I : Type}
    (U : I → Set X) (n : ℕ) :
    Function.Injective ((inclusion U).f n) :=
  Subtype.val_injective

/-- The type indexing the genuine small-simplex basis. -/
abbrev SmallSimplex {X : Type} [TopologicalSpace X] {I : Type}
    (U : I → Set X) (n : ℕ) :=
  {sigma : SingularSimplex X n // IsSmallSimplex U sigma}

/-- The generator chains of the `𝒰`-small singular simplices are linearly independent. -/
theorem smallSimplex_linearIndependent {X : Type} [TopologicalSpace X] {I : Type}
    (U : I → Set X) (n : ℕ) :
    LinearIndependent ℤ (fun sigma : SmallSimplex U n => simplexChain X n sigma.1) := by
  have hbasis : LinearIndependent ℤ (chainBasis X n) := (chainBasis X n).linearIndependent
  have hcomp := hbasis.comp (fun sigma : SmallSimplex U n => sigma.1) Subtype.val_injective
  change LinearIndependent ℤ (fun sigma : SmallSimplex U n => chainBasis X n sigma.1)
    at hcomp
  simpa only [chainBasis_apply] using hcomp

/-- The range of the small-simplex generator family is the image of the set of `𝒰`-small
simplices. -/
theorem smallSimplex_range {X : Type} [TopologicalSpace X] {I : Type}
    (U : I → Set X) (n : ℕ) :
    Set.range (fun sigma : SmallSimplex U n => simplexChain X n sigma.1) =
      simplexChain X n '' (IsSmallSimplex U : Set (SingularSimplex X n)) := by
  ext c
  constructor
  · rintro ⟨sigma, rfl⟩
    exact ⟨sigma.1, sigma.2, rfl⟩
  · rintro ⟨sigma, hsigma, rfl⟩
    exact ⟨⟨sigma, hsigma⟩, rfl⟩

/-- The subset of the native simplex basis carried by the cover. -/
def smallChainBasis {X : Type} [TopologicalSpace X] {I : Type}
    (U : I → Set X) (n : ℕ) : Module.Basis (SmallSimplex U n) ℤ (submodule U n) := by
  letI : Module ℤ
      (Submodule.span ℤ
        (Set.range (fun sigma : SmallSimplex U n => simplexChain X n sigma.1))) :=
    (Submodule.span ℤ
      (Set.range (fun sigma : SmallSimplex U n => simplexChain X n sigma.1))).module
  exact (Module.Basis.span (smallSimplex_linearIndependent U n)).map
    (LinearEquiv.ofEq _ _ (congrArg (Submodule.span ℤ) (smallSimplex_range U n)))

/-- The basis vector of the small-chain subcomplex at a `𝒰`-small simplex `σ` is the generator
chain of `σ`. -/
@[simp]
theorem smallChainBasis_apply_val {X : Type} [TopologicalSpace X] {I : Type}
    (U : I → Set X) (n : ℕ) (sigma : SmallSimplex U n) :
    (smallChainBasis U n sigma).1 = simplexChain X n sigma.1 := by
  let : Module ℤ
      (Submodule.span ℤ
        (Set.range (fun tau : SmallSimplex U n => simplexChain X n tau.1))) :=
    (Submodule.span ℤ
      (Set.range (fun tau : SmallSimplex U n => simplexChain X n tau.1))).module
  change (Module.Basis.span (smallSimplex_linearIndependent U n) sigma :
    (AlgebraicTopology.SingularCochains.chains X).X n) = simplexChain X n sigma.1
  exact Module.Basis.coe_span_apply (smallSimplex_linearIndependent U n) sigma

/-- Every small-chain group is projective, with no hypothesis on the cover. -/
theorem smallChain_projective {X : Type} [TopologicalSpace X] {I : Type}
    (U : I → Set X) (n : ℕ) : CategoryTheory.Projective ((complex U).X n) :=
  ModuleCat.projective_of_free (smallChainBasis U n)

/-- Degreewise projection onto cover-small simplex coordinates.  This is deliberately not
asserted to commute with the boundary. -/
def chainProjection {X : Type} [TopologicalSpace X] {I : Type}
    (U : I → Set X) (n : ℕ) :
    (AlgebraicTopology.SingularCochains.chains X).X n →ₗ[ℤ] submodule U n := by
  classical
  exact chainLift X n fun sigma =>
    if hsigma : IsSmallSimplex U sigma then
      ⟨simplexChain X n sigma, simplexChain_mem U n sigma hsigma⟩
    else 0

/-- The projection onto small chains fixes the generator chain of a `𝒰`-small simplex. -/
@[simp]
theorem chainProjection_small_simplex {X : Type} [TopologicalSpace X] {I : Type}
    (U : I → Set X) (n : ℕ) (sigma : SingularSimplex X n)
    (hsigma : IsSmallSimplex U sigma) :
    chainProjection U n (simplexChain X n sigma) =
      ⟨simplexChain X n sigma, simplexChain_mem U n sigma hsigma⟩ := by
  classical
  simp only [chainProjection, chainLift_simplex, dif_pos hsigma]

/-- Restriction of native singular cochains to cover-small chains. -/
def cochainRestriction {X : Type} [TopologicalSpace X] {I : Type}
    (A : AddCommGrpCat.{0}) (U : I → Set X) :
    AlgebraicTopology.SingularCochains.complex X A ⟶
      AlgebraicTopology.SingularCochains.dualComplex A (complex U) :=
  AlgebraicTopology.SingularCochains.dualMap A (inclusion U)

/-- Extend a small cochain by zero on all non-small simplex coordinates. -/
def cochainExtension {X : Type} [TopologicalSpace X] {I : Type}
    (A : AddCommGrpCat.{0}) (U : I → Set X) (n : ℕ)
    (phi : (AlgebraicTopology.SingularCochains.dualComplex A (complex U)).X n) :
    (AlgebraicTopology.SingularCochains.complex X A).X n :=
  phi.comp (chainProjection U n).toAddMonoidHom

/-- Regard an additive map as integer-linear for any specified integer module structures. -/
def addHomToIntLinearMap {M N : Type} [AddCommGroup M] [AddCommGroup N]
    [modM : Module ℤ M] [modN : Module ℤ N] (f : M →+ N) : M →ₗ[ℤ] N where
  toFun := f
  map_add' := f.map_add
  map_smul' z x := by
    change f (modM.smul z x) = modN.smul z (f x)
    rw [int_smul_eq_zsmul, int_smul_eq_zsmul]
    exact f.map_zsmul z x

/-- An additive homomorphism of abelian groups, read as a `ℤ`-linear map, has the same
underlying function. -/
@[simp]
theorem addHomToIntLinearMap_apply {M N : Type} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N] (f : M →+ N) (x : M) :
    addHomToIntLinearMap f x = f x := rfl

/-- The extension has exactly the prescribed values on cover-small chains. -/
theorem cochainRestriction_extension {X : Type} [TopologicalSpace X] {I : Type}
    (A : AddCommGrpCat.{0}) (U : I → Set X) (n : ℕ)
    (phi : (AlgebraicTopology.SingularCochains.dualComplex A (complex U)).X n) :
    (cochainRestriction A U).f n (cochainExtension A U n phi) = phi := by
  let phi' : submodule U n →+ A := phi
  have he :
      addHomToIntLinearMap
          ((cochainRestriction A U).f n (cochainExtension A U n phi)) =
        addHomToIntLinearMap phi' := by
    apply (smallChainBasis U n).ext
    intro sigma
    change phi' (chainProjection U n (smallChainBasis U n sigma).1) =
      phi' (smallChainBasis U n sigma)
    rw [smallChainBasis_apply_val,
      chainProjection_small_simplex U n sigma.1 sigma.2]
    apply congrArg phi'
    apply Subtype.ext
    exact (smallChainBasis_apply_val U n sigma).symm
  change
    ((cochainRestriction A U).f n (cochainExtension A U n phi) :
      submodule U n →+ A) = phi'
  exact congrArg LinearMap.toAddMonoidHom he

/-- Cover-small cochain restriction is surjective in every degree. -/
theorem cochainRestriction_surjective {X : Type} [TopologicalSpace X] {I : Type}
    (A : AddCommGrpCat.{0}) (U : I → Set X) (n : ℕ) :
    Function.Surjective ((cochainRestriction A U).f n) := fun phi =>
  ⟨cochainExtension A U n phi, cochainRestriction_extension A U n phi⟩

/-- Additive duality takes a native chain-homotopy equivalence to a cochain one. -/
def dualHomotopyEquiv (A : AddCommGrpCat.{0})
    {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (e : HomotopyEquiv K L) :
    HomotopyEquiv
      (AlgebraicTopology.SingularCochains.dualComplex A L)
      (AlgebraicTopology.SingularCochains.dualComplex A K) where
  hom := AlgebraicTopology.SingularCochains.dualMap A e.hom
  inv := AlgebraicTopology.SingularCochains.dualMap A e.inv
  homotopyHomInvId := by
    simpa only [AlgebraicTopology.SingularCochains.dualMap_comp,
      AlgebraicTopology.SingularCochains.dualMap_id] using
        AlgebraicTopology.SingularCochains.dualHomotopy A e.homotopyInvHomId
  homotopyInvHomId := by
    simpa only [AlgebraicTopology.SingularCochains.dualMap_comp,
      AlgebraicTopology.SingularCochains.dualMap_id] using
        AlgebraicTopology.SingularCochains.dualHomotopy A e.homotopyHomInvId

/-- A chain-homotopy equivalence whose forward map is the small-chain inclusion gives the
literal restriction map as the forward cochain equivalence. -/
def cochainRestrictionHomotopyEquiv {X : Type} [TopologicalSpace X] {I : Type}
    (A : AddCommGrpCat.{0}) (U : I → Set X)
    (e : HomotopyEquiv (complex U) (AlgebraicTopology.SingularCochains.chains X))
    (he : e.hom = inclusion U) :
    HomotopyEquiv
      (AlgebraicTopology.SingularCochains.complex X A)
      (AlgebraicTopology.SingularCochains.dualComplex A (complex U)) := by
  let d := dualHomotopyEquiv A e
  have hd : d.hom = cochainRestriction A U := by
    change AlgebraicTopology.SingularCochains.dualMap A e.hom =
      AlgebraicTopology.SingularCochains.dualMap A (inclusion U)
    exact congrArg (AlgebraicTopology.SingularCochains.dualMap A) he
  exact
    { hom := cochainRestriction A U
      inv := d.inv
      homotopyHomInvId := hd ▸ d.homotopyHomInvId
      homotopyInvHomId := hd ▸ d.homotopyInvHomId }

/-- A cochain map commutes with the differential when evaluated on an actual cochain. -/
theorem cochainMap_d {K L : CochainComplex AddCommGrpCat.{0} ℕ}
    (f : K ⟶ L) (i j : ℕ) (x : K.X i) :
    L.d i j (f.f i x) = f.f j (K.d i j x) :=
  congrArg (fun k : K.X i ⟶ L.X j => k x) (f.comm i j)

/-- Evaluation of a cochain homotopy on a degree-one cocycle. -/
theorem homotopy_on_cocycle_one {K L : CochainComplex AddCommGrpCat.{0} ℕ}
    {f g : K ⟶ L} (h : _root_.Homotopy f g) (x : K.X 1)
    (hx : K.d 1 2 x = 0) :
    f.f 1 x = L.d 0 1 (h.hom 1 0 x) + g.f 1 x := by
  have he := h.comm 1
  rw [dNext_eq h.hom (show (ComplexShape.up ℕ).Rel 1 2 from rfl),
    prevD_eq h.hom (show (ComplexShape.up ℕ).Rel 0 1 from rfl)] at he
  have hx' := congrArg (fun k : K.X 1 ⟶ L.X 1 => k x) he
  change f.f 1 x = h.hom 2 1 (K.d 1 2 x) +
    L.d 0 1 (h.hom 1 0 x) + g.f 1 x at hx'
  simpa only [hx, map_zero, zero_add] using hx'

/-- Under the literal small-chain homotopy equivalence, every degree-one small cocycle is the
exact restriction of a global cocycle.  Only cochain degrees zero through two occur. -/
theorem smallCochain_cocycle_lift_exact_one
    {X : Type} [TopologicalSpace X] {I : Type}
    (A : AddCommGrpCat.{0}) (U : I → Set X)
    (e : HomotopyEquiv (complex U) (AlgebraicTopology.SingularCochains.chains X))
    (he : e.hom = inclusion U)
    (phi : (AlgebraicTopology.SingularCochains.dualComplex A (complex U)).X 1)
    (hphi : (AlgebraicTopology.SingularCochains.dualComplex A (complex U)).d 1 2 phi = 0) :
    ∃ psi : (AlgebraicTopology.SingularCochains.complex X A).X 1,
      (AlgebraicTopology.SingularCochains.complex X A).d 1 2 psi = 0 ∧
      (cochainRestriction A U).f 1 psi = phi := by
  let E := cochainRestrictionHomotopyEquiv A U e he
  let psi := E.inv.f 1 phi
  let chi := E.homotopyInvHomId.hom 1 0 phi
  have hpsi : (AlgebraicTopology.SingularCochains.complex X A).d 1 2 psi = 0 := by
    rw [cochainMap_d E.inv 1 2, hphi, map_zero]
  have hchi : (cochainRestriction A U).f 1 psi =
      (AlgebraicTopology.SingularCochains.dualComplex A (complex U)).d 0 1 chi + phi := by
    exact homotopy_on_cocycle_one E.homotopyInvHomId phi hphi
  let eta := cochainExtension A U 0 chi
  refine ⟨psi - (AlgebraicTopology.SingularCochains.complex X A).d 0 1 eta, ?_, ?_⟩
  · rw [map_sub, hpsi]
    have hz := congrArg
      (fun f : (AlgebraicTopology.SingularCochains.complex X A).X 0 ⟶
        (AlgebraicTopology.SingularCochains.complex X A).X 2 => f eta)
      ((AlgebraicTopology.SingularCochains.complex X A).d_comp_d 0 1 2)
    change (AlgebraicTopology.SingularCochains.complex X A).d 1 2
      ((AlgebraicTopology.SingularCochains.complex X A).d 0 1 eta) = 0 at hz
    rw [hz, sub_self]
  · rw [map_sub, ← cochainMap_d (cochainRestriction A U) 0 1 eta,
      cochainRestriction_extension A U 0 chi, hchi, add_sub_cancel_left]

/-- Under the literal small-chain homotopy equivalence, a global degree-one cocycle whose small
restriction has a primitive has an actual global primitive. -/
theorem smallCochain_boundary_of_restriction_boundary_one
    {X : Type} [TopologicalSpace X] {I : Type}
    (A : AddCommGrpCat.{0}) (U : I → Set X)
    (e : HomotopyEquiv (complex U) (AlgebraicTopology.SingularCochains.chains X))
    (he : e.hom = inclusion U)
    (phi : (AlgebraicTopology.SingularCochains.complex X A).X 1)
    (hphi : (AlgebraicTopology.SingularCochains.complex X A).d 1 2 phi = 0)
    (chi : (AlgebraicTopology.SingularCochains.dualComplex A (complex U)).X 0)
    (hchi : (AlgebraicTopology.SingularCochains.dualComplex A (complex U)).d 0 1 chi =
      (cochainRestriction A U).f 1 phi) :
    ∃ psi : (AlgebraicTopology.SingularCochains.complex X A).X 0,
      (AlgebraicTopology.SingularCochains.complex X A).d 0 1 psi = phi := by
  let E := cochainRestrictionHomotopyEquiv A U e he
  refine ⟨E.inv.f 0 chi - E.homotopyHomInvId.hom 1 0 phi, ?_⟩
  rw [map_sub, cochainMap_d E.inv 0 1 chi, hchi]
  have hh := homotopy_on_cocycle_one E.homotopyHomInvId phi hphi
  change E.inv.f 1 ((cochainRestriction A U).f 1 phi) =
    (AlgebraicTopology.SingularCochains.complex X A).d 0 1
      (E.homotopyHomInvId.hom 1 0 phi) + phi at hh
  rw [hh, add_sub_cancel_left]

/-- In particular, cover-small restriction is an isomorphism on actual degree-one cohomology. -/
theorem cochainRestriction_homologyMap_isIso_one
    {X : Type} [TopologicalSpace X] {I : Type}
    (A : AddCommGrpCat.{0}) (U : I → Set X)
    (e : HomotopyEquiv (complex U) (AlgebraicTopology.SingularCochains.chains X))
    (he : e.hom = inclusion U) :
    IsIso (HomologicalComplex.homologyMap (cochainRestriction A U) 1) := by
  let E := cochainRestrictionHomotopyEquiv A U e he
  apply (quasiIsoAt_iff_isIso_homologyMap (cochainRestriction A U) 1).mp
  change QuasiIsoAt E.hom 1
  exact E.quasiIsoAt_hom 1

end TopCat.SingularSmallChains
