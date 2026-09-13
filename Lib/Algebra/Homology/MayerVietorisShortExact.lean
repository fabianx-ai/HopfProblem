/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib

/-!
# The Mayer–Vietoris short exact sequence of chain complexes

For chain complexes of ℤ-modules `K`, `L`, `J`, `T` with chain maps `a : J ⟶ K`, `b : J ⟶ L`,
`u : K ⟶ T`, `v : L ⟶ T` commuting in the square `a ≫ u = b ≫ v`, the biproduct construction
produces a short complex

`SmallChainBiprod.shortComplexOfComplexes a b u v w :
  CategoryTheory.ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ)`

with left leg `J →^{⟨a, -b⟩} K ⊞ L` and right leg `K ⊞ L →^{⟨u, v⟩} T`. Under the degreewise
Mayer–Vietoris conditions — `a` degreewise injective, `u` and `v` jointly degreewise
surjective, and the overlap condition `u x = v y → ∃ z, a z = x ∧ b z = y` — it is short
exact:

* `SmallChainBiprod.shortExactOfComplexes` :
  `(shortComplexOfComplexes a b u v w).ShortExact`.

This is the algebraic engine of the Mayer–Vietoris sequence
(`Lib/AlgebraicTopology/SingularHomology/MayerVietoris.lean`): for two open sets `U`, `V`
covering `X`, take `J = C(U ∩ V)`, `K = C(U)`, `L = C(V)`, `T = C^{U,V}(X)`.

## Outline of the proof

This is the biproduct half of [hatcher02], proof of Theorem 2.20, in four steps.

1. *Element calculus of biproducts in `ModuleCat ℤ`.*  `fst_lift_apply`, `snd_lift_apply`,
   `desc_inl_apply`, `desc_inr_apply`, `total_apply`, `element_ext`, `desc_apply`: elements of
   `A ⊞ B` are pairs, and `biprod.lift`/`biprod.desc` act componentwise.
2. *The module-level short complex.*  `shortComplex a b u v w` assembles
   `I →^{⟨a, -b⟩} A ⊞ B →^{⟨u, v⟩} S`; `left_injective` and `right_surjective` compute the
   image of the left leg and the kernel of the right leg, giving exactness (`exact`) and
   short exactness (`shortExact`).
3. *Lifting to chain complexes.*  `shortComplexOfComplexes` repeats the construction for
   chain maps; per degree it is the module-level complex of step 2 through the iso
   `shortComplexOfComplexesEvalIso`, built from `lift_f_biprodXIso_hom`,
   `biprodXIso_inv_desc_f`, `biprodXIso_hom_desc_f` and `square_f`.
4. *Degreewise short exact implies short exact.*  `shortExactOfComplexes` applies
   `HomologicalComplex.shortExact_of_degreewise_shortExact` and
   `CategoryTheory.ShortComplex.shortExact_of_iso` with the iso of step 3.

## Main definitions and results

* `SmallChainBiprod.shortComplex`, `SmallChainBiprod.exact`, `SmallChainBiprod.shortExact` :
  the module-level sequence.
* `SmallChainBiprod.shortComplexOfComplexes`,
  `SmallChainBiprod.shortComplexOfComplexesEvalIso` : the chain-complex-level sequence and
  its per-degree presentation.
* `SmallChainBiprod.shortExactOfComplexes` : short exactness under the Mayer–Vietoris
  conditions.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], proof of Theorem 2.20

## Tags

chain complexes, short exact sequence, biproducts, Mayer–Vietoris
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

@[expose] public noncomputable section

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-! ### Element calculus of biproducts in `ModuleCat ℤ` -/

/-- `biprod.fst` after `biprod.lift` is the first component. -/
theorem SmallChainBiprod.fst_lift_apply {A B I : ModuleCat.{0} ℤ} (a : I ⟶ A) (b : I ⟶ B)
    (z : I) :
    (CategoryTheory.Limits.biprod.fst : A ⊞ B ⟶ A).hom
        ((CategoryTheory.Limits.biprod.lift a b).hom z) =
      a.hom z := by
  exact congrArg (fun f : I ⟶ A => f.hom z) (CategoryTheory.Limits.biprod.lift_fst a b)

/-- The second projection of a biprod lift applied to `z` recovers `b z`. -/
theorem SmallChainBiprod.snd_lift_apply {A B I : ModuleCat.{0} ℤ} (a : I ⟶ A) (b : I ⟶ B)
    (z : I) :
    (CategoryTheory.Limits.biprod.snd : A ⊞ B ⟶ B).hom
        ((CategoryTheory.Limits.biprod.lift a b).hom z) =
      b.hom z := by
  exact congrArg (fun f : I ⟶ B => f.hom z) (CategoryTheory.Limits.biprod.lift_snd a b)

/-- A descended biprod map applied to a left inclusion computes the `u`-component. -/
theorem SmallChainBiprod.desc_inl_apply {A B S : ModuleCat.{0} ℤ} (u : A ⟶ S) (v : B ⟶ S)
    (x : A) :
    (CategoryTheory.Limits.biprod.desc u v).hom
        ((CategoryTheory.Limits.biprod.inl : A ⟶ A ⊞ B).hom x) =
      u.hom x := by
  exact congrArg (fun f : A ⟶ S => f.hom x) (CategoryTheory.Limits.biprod.inl_desc u v)

/-- A descended biprod map applied to a right inclusion computes the `v`-component. -/
theorem SmallChainBiprod.desc_inr_apply {A B S : ModuleCat.{0} ℤ} (u : A ⟶ S) (v : B ⟶ S)
    (y : B) :
    (CategoryTheory.Limits.biprod.desc u v).hom
        ((CategoryTheory.Limits.biprod.inr : B ⟶ A ⊞ B).hom y) =
      v.hom y := by
  exact congrArg (fun f : B ⟶ S => f.hom y) (CategoryTheory.Limits.biprod.inr_desc u v)

/-- Recombining the two biprod components of an element recovers the element. -/
theorem SmallChainBiprod.total_apply {A B : ModuleCat.{0} ℤ} (z : (A ⊞ B : ModuleCat ℤ)) :
    (CategoryTheory.Limits.biprod.inl : A ⟶ A ⊞ B).hom
          ((CategoryTheory.Limits.biprod.fst : A ⊞ B ⟶ A).hom z) +
        (CategoryTheory.Limits.biprod.inr : B ⟶ A ⊞ B).hom
          ((CategoryTheory.Limits.biprod.snd : A ⊞ B ⟶ B).hom z) =
      z := by exact congrArg (fun f : A ⊞ B ⟶ A ⊞ B => f.hom z) CategoryTheory.Limits.biprod.total

/-- Two elements of a biprod with equal components are equal. -/
theorem SmallChainBiprod.element_ext {A B : ModuleCat.{0} ℤ} {z z' : (A ⊞ B : ModuleCat ℤ)}
    (hfst :
      (CategoryTheory.Limits.biprod.fst : A ⊞ B ⟶ A).hom z =
        (CategoryTheory.Limits.biprod.fst : A ⊞ B ⟶ A).hom z')
    (hsnd :
      (CategoryTheory.Limits.biprod.snd : A ⊞ B ⟶ B).hom z =
        (CategoryTheory.Limits.biprod.snd : A ⊞ B ⟶ B).hom z') :
    z = z' := by
  calc
    z =
        (CategoryTheory.Limits.biprod.inl : A ⟶ A ⊞ B).hom
            ((CategoryTheory.Limits.biprod.fst : A ⊞ B ⟶ A).hom z) +
          (CategoryTheory.Limits.biprod.inr : B ⟶ A ⊞ B).hom
            ((CategoryTheory.Limits.biprod.snd : A ⊞ B ⟶ B).hom z) :=
      (total_apply z).symm
    _ =
        (CategoryTheory.Limits.biprod.inl : A ⟶ A ⊞ B).hom
            ((CategoryTheory.Limits.biprod.fst : A ⊞ B ⟶ A).hom z') +
          (CategoryTheory.Limits.biprod.inr : B ⟶ A ⊞ B).hom
            ((CategoryTheory.Limits.biprod.snd : A ⊞ B ⟶ B).hom z') := by rw [hfst, hsnd]
    _ = z' := total_apply z'

/-- A descended biprod map applied to an element is the sum of the two component maps. -/
theorem SmallChainBiprod.desc_apply {A B S : ModuleCat.{0} ℤ} (u : A ⟶ S) (v : B ⟶ S)
    (z : (A ⊞ B : ModuleCat ℤ)) :
    (CategoryTheory.Limits.biprod.desc u v).hom z =
      u.hom ((CategoryTheory.Limits.biprod.fst : A ⊞ B ⟶ A).hom z) +
        v.hom ((CategoryTheory.Limits.biprod.snd : A ⊞ B ⟶ B).hom z) := by
  calc
    (CategoryTheory.Limits.biprod.desc u v).hom z =
        (CategoryTheory.Limits.biprod.desc u v).hom
          ((CategoryTheory.Limits.biprod.inl : A ⟶ A ⊞ B).hom
              ((CategoryTheory.Limits.biprod.fst : A ⊞ B ⟶ A).hom z) +
            (CategoryTheory.Limits.biprod.inr : B ⟶ A ⊞ B).hom
              ((CategoryTheory.Limits.biprod.snd : A ⊞ B ⟶ B).hom z)) :=
      congrArg (CategoryTheory.Limits.biprod.desc u v).hom (total_apply z).symm
    _ = _ := by rw [map_add, desc_inl_apply, desc_inr_apply]

/-! ### The module-level short complex -/

/-- The short complex `I → A ⊞ B → S` assembled from a commuting square `a ≫ u = b ≫ v`. -/
def SmallChainBiprod.shortComplex {A B I S : ModuleCat.{0} ℤ} (a : I ⟶ A) (b : I ⟶ B) (u : A ⟶ S)
    (v : B ⟶ S) (w : a ≫ u = b ≫ v) : CategoryTheory.ShortComplex (ModuleCat.{0} ℤ) :=
  CategoryTheory.ShortComplex.mk (CategoryTheory.Limits.biprod.lift a (-b))
    (CategoryTheory.Limits.biprod.desc u v)
    (by
      rw [CategoryTheory.Limits.biprod.lift_desc, CategoryTheory.Preadditive.neg_comp, w,
        add_neg_cancel])

/-- Injectivity of `a` makes the lifted map into the biprod injective. -/
theorem SmallChainBiprod.left_injective {A B I : ModuleCat.{0} ℤ} (a : I ⟶ A) (b : I ⟶ B)
    (ha : Function.Injective a.hom) :
    Function.Injective (CategoryTheory.Limits.biprod.lift a (-b)).hom := by
  intro z z' h
  apply ha
  have hf := congrArg (CategoryTheory.Limits.biprod.fst : A ⊞ B ⟶ A).hom h
  simpa only [fst_lift_apply] using hf

/-- Joint surjectivity of `u` and `v` makes the descended map surjective. -/
theorem SmallChainBiprod.right_surjective {A B S : ModuleCat.{0} ℤ} (u : A ⟶ S) (v : B ⟶ S)
    (hjoint : ∀ s : S, ∃ x : A, ∃ y : B, u.hom x + v.hom y = s) :
    Function.Surjective (CategoryTheory.Limits.biprod.desc u v).hom := by
  intro s
  obtain ⟨x, y, hxy⟩ := hjoint s
  refine
    ⟨(CategoryTheory.Limits.biprod.inl : A ⟶ A ⊞ B).hom x +
        (CategoryTheory.Limits.biprod.inr : B ⟶ A ⊞ B).hom y,
      ?_⟩
  simpa only [map_add, desc_inl_apply, desc_inr_apply] using hxy

/-- The biprod short complex is exact when every pair with equal images comes from the source. -/
theorem SmallChainBiprod.exact {A B I S : ModuleCat.{0} ℤ} (a : I ⟶ A) (b : I ⟶ B) (u : A ⟶ S)
    (v : B ⟶ S) (w : a ≫ u = b ≫ v)
    (hoverlap : ∀ (x : A) (y : B), u.hom x = v.hom y → ∃ z : I, a.hom z = x ∧ b.hom z = y) :
    (shortComplex a b u v w).Exact := by
  apply (CategoryTheory.ShortComplex.moduleCat_exact_iff _).mpr
  intro q hq
  change (CategoryTheory.Limits.biprod.desc u v).hom q = 0 at hq
  have hsum :
    u.hom ((CategoryTheory.Limits.biprod.fst : A ⊞ B ⟶ A).hom q) +
        v.hom ((CategoryTheory.Limits.biprod.snd : A ⊞ B ⟶ B).hom q) =
      0 :=
    (desc_apply u v q).symm.trans hq
  have heq :
    u.hom ((CategoryTheory.Limits.biprod.fst : A ⊞ B ⟶ A).hom q) =
      v.hom (-(CategoryTheory.Limits.biprod.snd : A ⊞ B ⟶ B).hom q) := by
    rw [map_neg]
    exact eq_neg_iff_add_eq_zero.mpr hsum
  obtain ⟨z, haz, hbz⟩ := hoverlap _ _ heq
  refine ⟨z, ?_⟩
  change (CategoryTheory.Limits.biprod.lift a (-b)).hom z = q
  apply element_ext
  · simpa only [fst_lift_apply] using haz
  · rw [snd_lift_apply]
    change -b.hom z = (CategoryTheory.Limits.biprod.snd : A ⊞ B ⟶ B).hom q
    rw [hbz, neg_neg]

/-- The biprod short complex is short exact under injectivity, joint surjectivity, and the overlap condition. -/
theorem SmallChainBiprod.shortExact {A B I S : ModuleCat.{0} ℤ} (a : I ⟶ A) (b : I ⟶ B)
    (u : A ⟶ S) (v : B ⟶ S) (w : a ≫ u = b ≫ v) (ha : Function.Injective a.hom)
    (hjoint : ∀ s : S, ∃ x : A, ∃ y : B, u.hom x + v.hom y = s)
    (hoverlap : ∀ (x : A) (y : B), u.hom x = v.hom y → ∃ z : I, a.hom z = x ∧ b.hom z = y) :
    (shortComplex a b u v w).ShortExact
    where
  exact := exact a b u v w hoverlap
  mono_f := (ModuleCat.mono_iff_injective _).mpr (left_injective a b ha)
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (right_surjective u v hjoint)

/-! ### The short complex of chain complexes -/

/-- In each degree, a biprod lift commutes with the biprod isomorphism on chain complexes. -/
theorem SmallChainBiprod.lift_f_biprodXIso_hom {K L J : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (a : J ⟶ K) (b : J ⟶ L) (n : ℕ) :
    (CategoryTheory.Limits.biprod.lift a b).f n ≫ (HomologicalComplex.biprodXIso K L n).hom =
      CategoryTheory.Limits.biprod.lift (a.f n) (b.f n) := by
  apply CategoryTheory.Limits.biprod.hom_ext
  · simp only [CategoryTheory.Category.assoc, HomologicalComplex.biprodXIso_hom_fst,
      HomologicalComplex.biprod_lift_fst_f, CategoryTheory.Limits.biprod.lift_fst]
  · simp only [CategoryTheory.Category.assoc, HomologicalComplex.biprodXIso_hom_snd,
      HomologicalComplex.biprod_lift_snd_f, CategoryTheory.Limits.biprod.lift_snd]

/-- In each degree, the inverse biprod isomorphism commutes with a descended chain map. -/
theorem SmallChainBiprod.biprodXIso_inv_desc_f {K L T : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (u : K ⟶ T) (v : L ⟶ T) (n : ℕ) :
    (HomologicalComplex.biprodXIso K L n).inv ≫ (CategoryTheory.Limits.biprod.desc u v).f n =
      CategoryTheory.Limits.biprod.desc (u.f n) (v.f n) := by
  apply CategoryTheory.Limits.biprod.hom_ext'
  · simp only [← CategoryTheory.Category.assoc, HomologicalComplex.inl_biprodXIso_inv,
      HomologicalComplex.biprod_inl_desc_f, CategoryTheory.Limits.biprod.inl_desc]
  · simp only [← CategoryTheory.Category.assoc, HomologicalComplex.inr_biprodXIso_inv,
      HomologicalComplex.biprod_inr_desc_f, CategoryTheory.Limits.biprod.inr_desc]

/-- In each degree, the biprod isomorphism commutes with a descended chain map. -/
theorem SmallChainBiprod.biprodXIso_hom_desc_f {K L T : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (u : K ⟶ T) (v : L ⟶ T) (n : ℕ) :
    (HomologicalComplex.biprodXIso K L n).hom ≫
        CategoryTheory.Limits.biprod.desc (u.f n) (v.f n) =
      (CategoryTheory.Limits.biprod.desc u v).f n := by
  rw [← biprodXIso_inv_desc_f u v n, CategoryTheory.Iso.hom_inv_id_assoc]

/-- The short complex of chain complexes assembled from a commuting square of chain maps. -/
def SmallChainBiprod.shortComplexOfComplexes {K L J T : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (a : J ⟶ K) (b : J ⟶ L) (u : K ⟶ T) (v : L ⟶ T) (w : a ≫ u = b ≫ v) :
    CategoryTheory.ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  CategoryTheory.ShortComplex.mk (CategoryTheory.Limits.biprod.lift a (-b))
    (CategoryTheory.Limits.biprod.desc u v)
    (by
      rw [CategoryTheory.Limits.biprod.lift_desc, CategoryTheory.Preadditive.neg_comp, w,
        add_neg_cancel])

/-- A commuting square of chain maps still commutes after evaluation in degree `n`. -/
theorem SmallChainBiprod.square_f {K L J T : ChainComplex (ModuleCat.{0} ℤ) ℕ} (a : J ⟶ K)
    (b : J ⟶ L) (u : K ⟶ T) (v : L ⟶ T) (w : a ≫ u = b ≫ v) (n : ℕ) :
    a.f n ≫ u.f n = b.f n ≫ v.f n :=
  congrArg (fun f : J ⟶ T => f.f n) w

/-- Evaluating the complex-level short complex in degree `n` is the module-level short complex. -/
def SmallChainBiprod.shortComplexOfComplexesEvalIso {K L J T : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (a : J ⟶ K) (b : J ⟶ L) (u : K ⟶ T) (v : L ⟶ T) (w : a ≫ u = b ≫ v) (n : ℕ) :
    (shortComplexOfComplexes a b u v w).map
        (HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n) ≅
      shortComplex (a.f n) (b.f n) (u.f n) (v.f n) (square_f a b u v w n) := by
  refine
    CategoryTheory.ShortComplex.isoMk (CategoryTheory.Iso.refl _)
      (HomologicalComplex.biprodXIso K L n) (CategoryTheory.Iso.refl _) ?_ ?_
  · change
      𝟙 _ ≫ CategoryTheory.Limits.biprod.lift (a.f n) (-(b.f n)) =
        (CategoryTheory.Limits.biprod.lift a (-b)).f n ≫ (HomologicalComplex.biprodXIso K L n).hom
    simpa only [CategoryTheory.Category.id_comp, HomologicalComplex.neg_f_apply] using
      (lift_f_biprodXIso_hom a (-b) n).symm
  · change
      (HomologicalComplex.biprodXIso K L n).hom ≫
          CategoryTheory.Limits.biprod.desc (u.f n) (v.f n) =
        (CategoryTheory.Limits.biprod.desc u v).f n ≫ 𝟙 _
    simpa only [CategoryTheory.Category.comp_id] using biprodXIso_hom_desc_f u v n

/-- Degreewise injectivity, joint surjectivity, and overlap make a square of chain maps short exact. -/
theorem SmallChainBiprod.shortExactOfComplexes {K L J T : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (a : J ⟶ K) (b : J ⟶ L) (u : K ⟶ T) (v : L ⟶ T) (w : a ≫ u = b ≫ v)
    (ha : ∀ n : ℕ, Function.Injective (a.f n).hom)
    (hjoint : ∀ (n : ℕ) (s : T.X n), ∃ x : K.X n, ∃ y : L.X n, (u.f n).hom x + (v.f n).hom y = s)
    (hoverlap :
      ∀ (n : ℕ) (x : K.X n) (y : L.X n),
        (u.f n).hom x = (v.f n).hom y → ∃ z : J.X n, (a.f n).hom z = x ∧ (b.f n).hom z = y) :
    (shortComplexOfComplexes a b u v w).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact
    CategoryTheory.ShortComplex.shortExact_of_iso
      (shortComplexOfComplexesEvalIso a b u v w n).symm
      (shortExact (a.f n) (b.f n) (u.f n) (v.f n) (square_f a b u v w n) (ha n) (hjoint n)
        (hoverlap n))
