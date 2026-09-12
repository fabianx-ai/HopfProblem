/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.CubeTriangulation
import Lib.AlgebraicTopology.Hurewicz.Subdivision

set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

noncomputable section

namespace Mathoverflow1973

def Hurewicz.CubicalBoundary.cubeFacet (n : ℕ) (i : Fin (n + 1)) (ε : (unitInterval)) :
    C(Fin n → (unitInterval), Fin (n + 1) → (unitInterval))
    where
  toFun u := Fin.insertNth (α := fun _ => (unitInterval)) i ε u
  continuous_toFun := by
    apply continuous_pi
    intro j
    refine Fin.succAboveCases i ?_ (fun k => ?_) j
    · simpa only [Fin.insertNth_apply_same] using
        (continuous_const : Continuous fun _ : Fin n → (unitInterval) => ε)
    · simpa only [Fin.insertNth_apply_succAbove] using
        (continuous_apply k : Continuous fun u : Fin n → (unitInterval) => u k)

@[simp]
theorem Hurewicz.CubicalBoundary.cubeFacet_apply_self (n : ℕ) (i : Fin (n + 1))
    (ε : (unitInterval)) (u : Fin n → (unitInterval)) : cubeFacet n i ε u i = ε :=
  Fin.insertNth_apply_same (α := fun _ => (unitInterval)) i ε u

@[simp]
theorem Hurewicz.CubicalBoundary.cubeFacet_apply_succAbove (n : ℕ) (i : Fin (n + 1))
    (ε : (unitInterval)) (u : Fin n → (unitInterval)) (j : Fin n) :
    cubeFacet n i ε u (i.succAbove j) = u j :=
  Fin.insertNth_apply_succAbove (α := fun _ => (unitInterval)) i ε u j

theorem Hurewicz.SimplexGeometry.simplexQuotient_bottom_not_last_twoBoundary (n : ℕ)
    (i : Fin (n + 1)) (hi : i ≠ Fin.last n) (u : Fin n → (unitInterval)) :
    simplexQuotient (n + 1) (Hurewicz.CubicalBoundary.cubeFacet n i 0 u) ∈
      simplexTwoBoundary (n + 1) := by
  have hil : i < Fin.last n := lt_of_le_of_ne (Fin.le_last i) hi
  exact
    ⟨(Fin.last n).castSucc, Fin.last (n + 1), Fin.castSucc_ne_last _,
      simplexQuotient_castSucc_eq_zero_of_earlier_zero
        (Hurewicz.CubicalBoundary.cubeFacet n i 0 u) i (Fin.last n) hil
        (Hurewicz.CubicalBoundary.cubeFacet_apply_self n i 0 u),
      simplexQuotient_last_eq_zero_of_zero (Hurewicz.CubicalBoundary.cubeFacet n i 0 u) i
        (Hurewicz.CubicalBoundary.cubeFacet_apply_self n i 0 u)⟩

def Hurewicz.CubicalBoundary.BasedCubicalCell (n : ℕ) {X : Type*} [TopologicalSpace X]
    (x : X) :=
  { F : C(Fin n → (unitInterval), X) //
    ∀ u i j, i ≠ j → (u i = 0 ∨ u i = 1) → (u j = 0 ∨ u j = 1) → F u = x }

def Hurewicz.CubicalBoundary.cubicalFace {X : Type*} [TopologicalSpace X] {x : X} {n : ℕ}
    (F : BasedCubicalCell (n + 1) x) (i : Fin (n + 1)) (ε : (unitInterval)) (hε : ε = 0 ∨ ε = 1) :
    GenLoop (Fin n) X x :=
  ⟨F.val.comp (cubeFacet n i ε), fun u ⟨j, hj⟩ =>
    by
    apply F.property _ i (i.succAbove j) (Fin.ne_succAbove i j)
    · simpa only [cubeFacet_apply_self] using hε
    · simpa only [cubeFacet_apply_succAbove] using hj⟩

@[simp]
theorem Hurewicz.CubicalBoundary.cubicalFace_apply {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} (F : BasedCubicalCell (n + 1) x) (i : Fin (n + 1)) (ε : (unitInterval))
    (hε : ε = 0 ∨ ε = 1) (u : Fin n → (unitInterval)) :
    cubicalFace F i ε hε u = F.val (cubeFacet n i ε u) :=
  rfl

abbrev Hurewicz.CubicalBoundary.cubicalLowerFace {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} (F : BasedCubicalCell (n + 1) x) (i : Fin (n + 1)) : GenLoop (Fin n) X x :=
  cubicalFace F i 0 (Or.inl rfl)

abbrev Hurewicz.CubicalBoundary.cubicalUpperFace {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} (F : BasedCubicalCell (n + 1) x) (i : Fin (n + 1)) : GenLoop (Fin n) X x :=
  cubicalFace F i 1 (Or.inr rfl)

structure Hurewicz.CubicalBoundary.CubicalEvaluator {X : Type*} [TopologicalSpace X] (n : ℕ)
    (x : X) (A : Type*) [AddCommGroup A] where
  evaluate : GenLoop (Fin n) X x → A
  map_const : evaluate GenLoop.const = 0
  map_homotopic : ∀ {p q}, GenLoop.Homotopic p q → evaluate p = evaluate q
  map_transAt : ∀ i p q, evaluate (GenLoop.transAt i p q) = evaluate p + evaluate q
  map_symmAt : ∀ i p, evaluate (GenLoop.symmAt i p) = -evaluate p
  map_swap :
    ∀ p i j,
      i ≠ j →
        evaluate (Hurewicz.NativeSubdivision.permuteCubeLoop p (Equiv.swap i j)) =
          -evaluate p

instance Hurewicz.CubicalBoundary.instCoeFun1 {X : Type*} [TopologicalSpace X] {n : ℕ}
    {x : X} {A : Type*} [AddCommGroup A] :
    CoeFun (CubicalEvaluator n x A) (fun _ => GenLoop (Fin n) X x → A) :=
  ⟨CubicalEvaluator.evaluate⟩

theorem Hurewicz.CubicalBoundary.CubicalEvaluator.map_permutation {X : Type*}
    [TopologicalSpace X] {n : ℕ} {x : X} {A : Type*} [AddCommGroup A]
    (E : Hurewicz.CubicalBoundary.CubicalEvaluator n x A) (p : GenLoop (Fin n) X x)
    (e : Equiv.Perm (Fin n)) :
    E (Hurewicz.NativeSubdivision.permuteCubeLoop p e) =
      ((Equiv.Perm.sign e : ℤˣ) : ℤ) • E p := by
  induction e using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul e i j hij
    ih =>
    rw [Hurewicz.NativeSubdivision.permuteCubeLoop_mul, E.map_swap _ i j hij, ih]
    simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]

theorem Hurewicz.CubicalBoundary.CubicalEvaluator.map_finRotate {X : Type*}
    [TopologicalSpace X] {n : ℕ} {x : X} {A : Type*} [AddCommGroup A]
    (E : Hurewicz.CubicalBoundary.CubicalEvaluator n x A) (p : GenLoop (Fin n) X x) :
    E (Hurewicz.NativeSubdivision.permuteCubeLoop p (finRotate n)) =
      (-1 : ℤ) ^ (n - 1) • E p := by
  rw [E.map_permutation, sign_finRotate]
  simp

def Hurewicz.CubicalBoundary.cubicalBoundaryValue {X : Type*} [TopologicalSpace X] {n : ℕ}
    {x : X} {A : Type*} [AddCommGroup A] (E : CubicalEvaluator n x A)
    (F : BasedCubicalCell (n + 1) x) : A :=
  ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • (E (cubicalUpperFace F i) - E (cubicalLowerFace F i))

def Hurewicz.CubicalBoundary.nativeCubicalEvaluator {X : Type*} [TopologicalSpace X] (n : ℕ)
    (x : X) : CubicalEvaluator (n + 2) x (Additive (π_ (n + 2) X x))
    where
  evaluate := Hurewicz.NativeSubdivision.nativeClass
  map_const := Hurewicz.NativeSubdivision.nativeClass_const
  map_homotopic := Hurewicz.NativeSubdivision.nativeClass_homotopic
  map_transAt := Hurewicz.NativeSubdivision.nativeClass_transAt
  map_symmAt := Hurewicz.NativeSubdivision.nativeClass_symmAt
  map_swap := Hurewicz.NativeSubdivision.permuteCubeLoop_swap_additiveClass

theorem Hurewicz.SimplexGeometry.extendedMinimum_cubeFacet_one_le {n : ℕ} (i : Fin (n + 1))
    (u : Fin n → (unitInterval)) (k : ℕ) (hk : k ≤ i.val) :
    extendedMinimum (Hurewicz.CubicalBoundary.cubeFacet n i 1 u) k = extendedMinimum u k := by
  have hkn : k ≤ n := hk.trans (Nat.le_of_lt_succ i.isLt)
  rw [extendedMinimum_of_le _ k (hkn.trans (Nat.le_succ n)), extendedMinimum_of_le u k hkn]
  exact prefixMinimum_insertNth_one_le i u k hk

theorem Hurewicz.SimplexGeometry.extendedMinimum_cubeFacet_one_succ {n : ℕ}
    (i : Fin (n + 1)) (u : Fin n → (unitInterval)) (k : ℕ) (hk : i.val ≤ k) :
    extendedMinimum (Hurewicz.CubicalBoundary.cubeFacet n i 1 u) (k + 1) =
      extendedMinimum u k := by
  by_cases hkn : k ≤ n
  · rw [extendedMinimum_of_le _ (k + 1) (Nat.succ_le_succ hkn), extendedMinimum_of_le u k hkn]
    exact prefixMinimum_insertNth_one_succ i u k hk
  · simp only [extendedMinimum, if_neg hkn,
      if_neg (show ¬k + 1 ≤ n + 1 from fun h => hkn (Nat.succ_le_succ_iff.mp h))]

theorem Hurewicz.SimplexGeometry.extendedMinimum_cubeFacet_last_zero {n : ℕ}
    (u : Fin n → (unitInterval)) (k : ℕ) :
    extendedMinimum (Hurewicz.CubicalBoundary.cubeFacet n (Fin.last n) 0 u) k =
      extendedMinimum u k := by
  by_cases hkn : k ≤ n
  · rw [extendedMinimum_of_le _ k (hkn.trans (Nat.le_succ n)), extendedMinimum_of_le u k hkn]
    exact prefixMinimum_insertNth_last_le u 0 k hkn
  · by_cases hks : k ≤ n + 1
    · have hk : k = n + 1 := by omega
      subst k
      rw [extendedMinimum_of_le _ (n + 1) le_rfl, extendedMinimum_last_succ]
      change prefixMinimum (Fin.insertNth (Fin.last n) 0 u) (n + 1) = 0
      rw [prefixMinimum_insertNth_succ (Fin.last n) 0 u n le_rfl]
      exact min_eq_left (show (0 : (unitInterval)) ≤ prefixMinimum u n from bot_le)
    · simp only [extendedMinimum, if_neg hkn, if_neg hks]

theorem Hurewicz.SimplexGeometry.simplexQuotient_cubeFacet_one_apply (n : ℕ)
    (i : Fin (n + 1)) (u : Fin n → (unitInterval)) :
    simplexQuotient (n + 1) (Hurewicz.CubicalBoundary.cubeFacet n i 1 u) =
      SingularChains.simplexFace n i.castSucc (simplexQuotient n u) := by
  apply Subtype.ext
  funext k
  change
    simplexQuotient (n + 1) (Hurewicz.CubicalBoundary.cubeFacet n i 1 u) k =
      SingularChains.simplexFace n i.castSucc (simplexQuotient n u) k
  refine Fin.succAboveCases i.castSucc ?_ (fun j => ?_) k
  · rw [SingularChains.simplexFace_apply_self]
    exact
      simplexQuotient_castSucc_eq_zero_of_one _ i
        (Hurewicz.CubicalBoundary.cubeFacet_apply_self n i 1 u)
  · rw [SingularChains.simplexFace_apply_succAbove]
    by_cases hji : j < i
    · rw [Fin.succAbove_of_castSucc_lt i.castSucc j (show j.castSucc < i.castSucc from hji)]
      simp only [simplexQuotient_apply, Fin.val_castSucc]
      rw [extendedMinimum_cubeFacet_one_le i u j.val (le_of_lt hji),
        extendedMinimum_cubeFacet_one_le i u (j.val + 1) (Nat.succ_le_of_lt hji)]
    · rw [Fin.succAbove_of_le_castSucc i.castSucc j
          (show i.castSucc ≤ j.castSucc from le_of_not_gt hji)]
      simp only [simplexQuotient_apply, Fin.val_succ]
      rw [extendedMinimum_cubeFacet_one_succ i u j.val (le_of_not_gt hji),
        extendedMinimum_cubeFacet_one_succ i u (j.val + 1)
          ((show i.val ≤ j.val from le_of_not_gt hji).trans (Nat.le_succ j.val))]

theorem Hurewicz.SimplexGeometry.simplexQuotient_cubeFacet_last_zero_apply (n : ℕ)
    (u : Fin n → (unitInterval)) :
    simplexQuotient (n + 1) (Hurewicz.CubicalBoundary.cubeFacet n (Fin.last n) 0 u) =
      SingularChains.simplexFace n (Fin.last (n + 1)) (simplexQuotient n u) := by
  apply Subtype.ext
  funext k
  change
    simplexQuotient (n + 1) (Hurewicz.CubicalBoundary.cubeFacet n (Fin.last n) 0 u) k =
      SingularChains.simplexFace n (Fin.last (n + 1)) (simplexQuotient n u) k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · rw [SingularChains.simplexFace_apply_self]
    exact
      simplexQuotient_last_eq_zero_of_zero _ (Fin.last n)
        (Hurewicz.CubicalBoundary.cubeFacet_apply_self n (Fin.last n) 0 u)
  · rw [show j.castSucc = (Fin.last (n + 1)).succAbove j by simp,
      SingularChains.simplexFace_apply_succAbove]
    simp only [Fin.succAbove_last, simplexQuotient_apply, Fin.val_castSucc,
      extendedMinimum_cubeFacet_last_zero]

def Hurewicz.SimplexGeometry.simplexBoundaryCube {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} (τ : BasedSimplexBoundary n x) :
    Hurewicz.CubicalBoundary.BasedCubicalCell n x :=
  ⟨τ.val.comp (simplexQuotient n), fun u i j hij hi hj =>
    τ.property _ (simplexQuotient_codimTwo u ⟨i, j, hij, hi, hj⟩)⟩

theorem Hurewicz.SimplexGeometry.simplexBoundaryCube_upper {X : Type*} [TopologicalSpace X]
    {x : X} {n : ℕ} (τ : BasedSimplexBoundary (n + 1) x) (i : Fin (n + 1)) :
    Hurewicz.CubicalBoundary.cubicalUpperFace (simplexBoundaryCube τ) i =
      basedSimplexLoop (basedSimplexBoundaryFace τ i.castSucc) := by
  apply GenLoop.ext
  intro u
  change
    τ.val (simplexQuotient (n + 1) (Hurewicz.CubicalBoundary.cubeFacet n i 1 u)) =
      τ.val (SingularChains.simplexFace n i.castSucc (simplexQuotient n u))
  rw [simplexQuotient_cubeFacet_one_apply]

theorem Hurewicz.SimplexGeometry.simplexBoundaryCube_lower_last {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (τ : BasedSimplexBoundary (n + 1) x) :
    Hurewicz.CubicalBoundary.cubicalLowerFace (simplexBoundaryCube τ) (Fin.last n) =
      basedSimplexLoop (basedSimplexBoundaryFace τ (Fin.last (n + 1))) := by
  apply GenLoop.ext
  intro u
  change
    τ.val
        (simplexQuotient (n + 1) (Hurewicz.CubicalBoundary.cubeFacet n (Fin.last n) 0 u)) =
      τ.val (SingularChains.simplexFace n (Fin.last (n + 1)) (simplexQuotient n u))
  rw [simplexQuotient_cubeFacet_last_zero_apply]

theorem Hurewicz.SimplexGeometry.simplexBoundaryCube_lower_constant {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (τ : BasedSimplexBoundary (n + 1) x) (i : Fin (n + 1))
    (hi : i ≠ Fin.last n) :
    Hurewicz.CubicalBoundary.cubicalLowerFace (simplexBoundaryCube τ) i = GenLoop.const := by
  apply GenLoop.ext
  intro u
  exact τ.property _ (simplexQuotient_bottom_not_last_twoBoundary n i hi u)

theorem Hurewicz.SimplexGeometry.simplexBoundaryCube_boundaryValue {X : Type*}
    [TopologicalSpace X] {x : X} {A : Type*} [AddCommGroup A] {n : ℕ}
    (E : Hurewicz.CubicalBoundary.CubicalEvaluator n x A)
    (τ : BasedSimplexBoundary (n + 1) x) :
    Hurewicz.CubicalBoundary.cubicalBoundaryValue E (simplexBoundaryCube τ) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • E (basedSimplexLoop (basedSimplexBoundaryFace τ i)) :=
  by
  have hzero (i : Fin n) :
    E (Hurewicz.CubicalBoundary.cubicalLowerFace (simplexBoundaryCube τ) i.castSucc) = 0 := by
    rw [simplexBoundaryCube_lower_constant τ i.castSucc (Fin.castSucc_ne_last i)]
    exact E.map_const
  have hlower :
    (∑ i : Fin (n + 1),
        (-1 : ℤ) ^ i.val •
          E (Hurewicz.CubicalBoundary.cubicalLowerFace (simplexBoundaryCube τ) i)) =
      (-1 : ℤ) ^ n • E (basedSimplexLoop (basedSimplexBoundaryFace τ (Fin.last (n + 1)))) := by
    rw [Fin.sum_univ_castSucc]
    simp only [hzero, smul_zero, Finset.sum_const_zero, zero_add, Fin.val_last,
      simplexBoundaryCube_lower_last]
  unfold Hurewicz.CubicalBoundary.cubicalBoundaryValue
  simp_rw [simplexBoundaryCube_upper, smul_sub]
  rw [Finset.sum_sub_distrib, hlower]
  conv_rhs => rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, pow_succ', neg_mul, one_mul, neg_smul,
    sub_eq_add_neg]

def Hurewicz.CubicalBoundary.whiskerStartTrack :
    Path ((0 : (unitInterval)), (0 : (unitInterval))) ((0 : (unitInterval)), (1 : (unitInterval)))
    where
  toFun s := (0, s)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

def Hurewicz.CubicalBoundary.whiskerMiddleTrack :
    Path ((0 : (unitInterval)), (1 : (unitInterval))) ((1 : (unitInterval)), (1 : (unitInterval)))
    where
  toFun s := (s, 1)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

def Hurewicz.CubicalBoundary.whiskerFinishTrack :
    Path ((1 : (unitInterval)), (0 : (unitInterval))) ((1 : (unitInterval)), (1 : (unitInterval)))
    where
  toFun s := (1, s)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

def Hurewicz.CubicalBoundary.whiskerTrack :
    Path ((0 : (unitInterval)), (0 : (unitInterval)))
      ((1 : (unitInterval)), (0 : (unitInterval))) :=
  whiskerStartTrack.trans (whiskerMiddleTrack.trans whiskerFinishTrack.symm)

theorem Hurewicz.CubicalBoundary.whiskerTrack_boundary (s : (unitInterval)) :
    ((whiskerTrack s).1 = 0 ∨ (whiskerTrack s).1 = 1) ∨ (whiskerTrack s).2 = 1 := by
  unfold whiskerTrack
  rw [Path.trans_apply]
  split_ifs
  · exact Or.inl (Or.inl rfl)
  · rw [Path.trans_apply]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl (Or.inr rfl)

def Hurewicz.CubicalBoundary.whiskerMap (n : ℕ) :
    C((Fin (n + 1) → (unitInterval)) × (unitInterval), Fin (n + 2) → (unitInterval))
    where
  toFun
    z :=
    Fin.cons (whiskerTrack z.2).1
      (Fin.snoc (Fin.init z.1) ((whiskerTrack z.2).2 * z.1 (Fin.last n)))
  continuous_toFun := by
    apply Continuous.finCons
    · exact (whiskerTrack.continuous.comp continuous_snd).fst
    · apply Continuous.finSnoc
      · apply continuous_pi
        intro i
        exact (continuous_apply i.castSucc).comp continuous_fst
      · apply Continuous.subtype_mk
        exact
          (continuous_subtype_val.comp (whiskerTrack.continuous.comp continuous_snd).snd).mul
            (continuous_subtype_val.comp ((continuous_apply (Fin.last n)).comp continuous_fst))

@[simp]
theorem Hurewicz.CubicalBoundary.whiskerMap_apply (n : ℕ) (u : Fin (n + 1) → (unitInterval))
    (s : (unitInterval)) :
    whiskerMap n (u, s) =
      Fin.cons (whiskerTrack s).1 (Fin.snoc (Fin.init u) ((whiskerTrack s).2 * u (Fin.last n))) :=
  rfl

@[simp]
theorem Hurewicz.CubicalBoundary.whiskerMap_first (n : ℕ) (u : Fin (n + 1) → (unitInterval))
    (s : (unitInterval)) : whiskerMap n (u, s) 0 = (whiskerTrack s).1 := by simp

@[simp]
theorem Hurewicz.CubicalBoundary.whiskerMap_middle (n : ℕ)
    (u : Fin (n + 1) → (unitInterval)) (s : (unitInterval)) (i : Fin n) :
    whiskerMap n (u, s) i.castSucc.succ = u i.castSucc := by simp [Fin.init]

@[simp]
theorem Hurewicz.CubicalBoundary.whiskerMap_start (n : ℕ)
    (u : Fin (n + 1) → (unitInterval)) :
    whiskerMap n (u, 0) = Fin.cons 0 (Fin.snoc (Fin.init u) 0) := by simp

@[simp]
theorem Hurewicz.CubicalBoundary.whiskerMap_finish (n : ℕ)
    (u : Fin (n + 1) → (unitInterval)) :
    whiskerMap n (u, 1) = Fin.cons 1 (Fin.snoc (Fin.init u) 0) := by simp

theorem Hurewicz.CubicalBoundary.whiskerMap_last_zero (n : ℕ)
    (u : Fin (n + 1) → (unitInterval)) (s : (unitInterval)) (hu : u (Fin.last n) = 0) :
    whiskerMap n (u, s) (Fin.last n).succ = 0 := by simp [hu]

theorem Hurewicz.CubicalBoundary.whiskerCorner_based {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x) (ε : (unitInterval))
    (hε : ε = 0 ∨ ε = 1) (v : Fin n → (unitInterval)) : F.val (Fin.cons ε (Fin.snoc v 0)) = x := by
  apply F.property _ 0 (Fin.last n).succ (by simp)
  · simpa only [Fin.cons_zero] using hε
  · exact Or.inl (by simp)

theorem Hurewicz.CubicalBoundary.whiskerMap_based_of_two_prefix {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x)
    (u : Fin (n + 1) → (unitInterval)) (s : (unitInterval)) (i j : Fin n) (hij : i ≠ j)
    (hi : u i.castSucc = 0 ∨ u i.castSucc = 1) (hj : u j.castSucc = 0 ∨ u j.castSucc = 1) :
    F.val (whiskerMap n (u, s)) = x := by
  apply F.property _ i.castSucc.succ j.castSucc.succ (by simpa using hij)
  · simpa only [whiskerMap_middle] using hi
  · simpa only [whiskerMap_middle] using hj

theorem Hurewicz.CubicalBoundary.whiskerMap_based_of_prefix_last {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x)
    (u : Fin (n + 1) → (unitInterval)) (s : (unitInterval)) (i : Fin n)
    (hi : u i.castSucc = 0 ∨ u i.castSucc = 1) (hz : u (Fin.last n) = 0 ∨ u (Fin.last n) = 1) :
    F.val (whiskerMap n (u, s)) = x := by
  rcases hz with hz | hz
  · apply F.property _ i.castSucc.succ (Fin.last n).succ (by simp)
    · simpa only [whiskerMap_middle] using hi
    · exact Or.inl (whiskerMap_last_zero n u s hz)
  · rcases whiskerTrack_boundary s with ht | hr
    · apply F.property _ 0 i.castSucc.succ (Fin.succ_ne_zero i.castSucc).symm
      · simpa only [whiskerMap_first] using ht
      · simpa only [whiskerMap_middle] using hi
    · apply F.property _ i.castSucc.succ (Fin.last n).succ (by simp)
      · simpa only [whiskerMap_middle] using hi
      · exact Or.inr (by simp [hr, hz])

theorem Hurewicz.CubicalBoundary.whiskerMap_codimTwo_based {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x)
    (u : Fin (n + 1) → (unitInterval)) (s : (unitInterval)) (i j : Fin (n + 1)) (hij : i ≠ j)
    (hi : u i = 0 ∨ u i = 1) (hj : u j = 0 ∨ u j = 1) : F.val (whiskerMap n (u, s)) = x := by
  cases i using Fin.lastCases with
  | last =>
    cases j using Fin.lastCases with
    | last => exact (hij rfl).elim
    | cast j => exact whiskerMap_based_of_prefix_last F u s j hj hi
  | cast i =>
    cases j using Fin.lastCases with
    | last => exact whiskerMap_based_of_prefix_last F u s i hi hj
    | cast j => exact whiskerMap_based_of_two_prefix F u s i j (by simpa using hij) hi hj

theorem Hurewicz.CubicalBoundary.cubeFacet_succ_cons (n : ℕ) (i : Fin (n + 1))
    (ε s : (unitInterval)) (u : Fin n → (unitInterval)) :
    cubeFacet (n + 1) i.succ ε (Fin.cons s u) = Fin.cons s (cubeFacet n i ε u) :=
  Fin.insertNth_succ_cons i ε s u

theorem Hurewicz.CubicalBoundary.whiskerFacetNormal_arm_based {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x) (i : Fin (n + 1))
    (ε : (unitInterval)) (hε : ε = 0 ∨ ε = 1) (h : i ≠ Fin.last n ∨ ε = 0)
    (u : Fin n → (unitInterval)) (a : (unitInterval)) (ha : a = 0 ∨ a = 1) (r : (unitInterval)) :
    F.val
        (Fin.cons a
          (Fin.snoc (Fin.init (cubeFacet n i ε u)) (r * cubeFacet n i ε u (Fin.last n)))) =
      x := by
  cases i using Fin.lastCases with
  | last =>
    have hzero : ε = 0 := h.resolve_left (not_not_intro rfl)
    subst ε
    apply F.property _ 0 (Fin.last n).succ (by simp)
    · simpa only [Fin.cons_zero] using ha
    · exact Or.inl (by simp)
  | cast i =>
    apply F.property _ 0 i.castSucc.succ (Fin.succ_ne_zero i.castSucc).symm
    · simpa only [Fin.cons_zero] using ha
    · simpa [Fin.init] using hε

def Hurewicz.CubicalBoundary.whiskeredLoop {n : ℕ} {X : Type*} [TopologicalSpace X] {x : X}
    (F : BasedCubicalCell (n + 2) x) (u : Fin (n + 1) → (unitInterval)) : GenLoop (Fin 1) X x :=
  ⟨⟨fun q => F.val (whiskerMap n (u, q 0)), by fun_prop⟩,
    by
    intro q hq
    obtain ⟨i, hi⟩ := hq
    have he : i = 0 := Subsingleton.elim _ _
    subst i
    rcases hi with hi | hi
    · change F.val (whiskerMap n (u, q 0)) = x
      rw [hi, whiskerMap_start]
      exact whiskerCorner_based F 0 (Or.inl rfl) (Fin.init u)
    · change F.val (whiskerMap n (u, q 0)) = x
      rw [hi, whiskerMap_finish]
      exact whiskerCorner_based F 1 (Or.inr rfl) (Fin.init u)⟩

def Hurewicz.CubicalBoundary.whiskeredLoopMap {n : ℕ} {X : Type*} [TopologicalSpace X]
    {x : X} (F : BasedCubicalCell (n + 2) x) :
    C(Fin (n + 1) → (unitInterval), GenLoop (Fin 1) X x)
    where
  toFun := whiskeredLoop F
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply ContinuousMap.continuous_of_continuous_uncurry
    change
      Continuous
        (fun z : (Fin (n + 1) → (unitInterval)) × (Fin 1 → (unitInterval)) =>
          F.val (whiskerMap n (z.1, z.2 0)))
    exact F.val.continuous.comp ((whiskerMap n).continuous.comp (by fun_prop))

def Hurewicz.CubicalBoundary.whiskeredCell {n : ℕ} {X : Type*} [TopologicalSpace X] {x : X}
    (F : BasedCubicalCell (n + 2) x) :
    BasedCubicalCell (n + 1) (GenLoop.const : GenLoop (Fin 1) X x) :=
  ⟨whiskeredLoopMap F, by
    intro u i j hij hi hj
    apply GenLoop.ext
    intro q
    exact whiskerMap_codimTwo_based F u (q 0) i j hij hi hj⟩

@[simp]
theorem Hurewicz.CubicalBoundary.whiskeredCell_apply {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x)
    (u : Fin (n + 1) → (unitInterval)) (q : Fin 1 → (unitInterval)) :
    (whiskeredCell F).val u q = F.val (whiskerMap n (u, q 0)) :=
  rfl

theorem Hurewicz.CubicalBoundary.whiskerTrack_concat (s : (unitInterval)) :
    whiskerTrack s =
      if (s : ℝ) ≤ 1 / 2 then (0, Set.projIcc 0 1 zero_le_one (2 * (s : ℝ)))
      else
        let t := Set.projIcc 0 1 zero_le_one (2 * (s : ℝ) - 1)
        if (t : ℝ) ≤ 1 / 2 then (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ)), 1)
        else (1, (unitInterval.symm) (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1))) :=
  rfl

theorem Hurewicz.CubicalBoundary.whiskerMap_concat (n : ℕ)
    (u : Fin (n + 1) → (unitInterval)) (s : (unitInterval)) :
    whiskerMap n (u, s) =
      if (s : ℝ) ≤ 1 / 2 then
        Fin.cons 0
          (Fin.snoc (Fin.init u) (Set.projIcc 0 1 zero_le_one (2 * (s : ℝ)) * u (Fin.last n)))
      else
        let t := Set.projIcc 0 1 zero_le_one (2 * (s : ℝ) - 1)
        if (t : ℝ) ≤ 1 / 2 then Fin.cons (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ))) u
        else
          Fin.cons 1
            (Fin.snoc (Fin.init u)
              ((unitInterval.symm) (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1)) *
                u (Fin.last n))) := by
  rw [whiskerMap_apply, whiskerTrack_concat]
  dsimp only
  split_ifs
  · rfl
  · simp only [one_mul, Fin.snoc_init_self]
  · rfl

def Hurewicz.CubicalBoundary.uncurryLoop {X : Type*} [TopologicalSpace X] {x : X} {n : ℕ}
    (p : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const) : GenLoop (Fin (n + 1)) X x :=
  ⟨⟨fun u => p (fun i => u i.succ) (fun _ => u 0), by fun_prop⟩,
    by
    intro u hu
    obtain ⟨i, hi⟩ := hu
    cases i using Fin.cases with
    | zero => exact GenLoop.boundary (p (fun i => u i.succ)) (fun _ => u 0) ⟨0, hi⟩
    | succ j =>
      change p (fun i => u i.succ) (fun _ => u 0) = x
      rw [GenLoop.boundary p _ ⟨j, hi⟩]
      rfl⟩

@[simp]
theorem Hurewicz.CubicalBoundary.uncurryLoop_apply {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} (p : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const)
    (u : Fin (n + 1) → (unitInterval)) : uncurryLoop p u = p (fun i => u i.succ) (fun _ => u 0) :=
  rfl

@[simp]
theorem Hurewicz.CubicalBoundary.uncurryLoop_const {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} :
    uncurryLoop (GenLoop.const : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const) =
      (GenLoop.const : GenLoop (Fin (n + 1)) X x) := by
  apply GenLoop.ext
  intro u
  rfl

def Hurewicz.CubicalBoundary.uncurryLoopHomotopy {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} {p q : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const}
    (H : p.val.HomotopyRel q.val (Cube.boundary (Fin n))) :
    (uncurryLoop p).val.HomotopyRel (uncurryLoop q).val (Cube.boundary (Fin (n + 1)))
    where
  toFun z := H (z.1, fun i => z.2 i.succ) (fun _ => z.2 0)
  continuous_toFun := by fun_prop
  map_zero_left
    u := by
    change H (0, fun i => u i.succ) (fun _ => u 0) = _
    rw [ContinuousMap.HomotopyWith.apply_zero]
    rfl
  map_one_left
    u := by
    change H (1, fun i => u i.succ) (fun _ => u 0) = _
    rw [ContinuousMap.HomotopyWith.apply_one]
    rfl
  prop' t u
    hu := by
    change H (t, fun i => u i.succ) (fun _ => u 0) = uncurryLoop p u
    rw [GenLoop.boundary (uncurryLoop p) u hu]
    obtain ⟨i, hi⟩ := hu
    cases i using Fin.cases with
    | zero => exact GenLoop.boundary (H (t, fun i => u i.succ)) (fun _ => u 0) ⟨0, hi⟩
    | succ j =>
      rw [H.eq_fst t ⟨j, hi⟩]
      change p (fun i => u i.succ) (fun _ => u 0) = x
      rw [GenLoop.boundary p _ ⟨j, hi⟩]
      rfl

theorem Hurewicz.CubicalBoundary.uncurryLoop_homotopic {X : Type*} [TopologicalSpace X]
    {x : X} {n : ℕ} {p q : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const}
    (h : GenLoop.Homotopic p q) : GenLoop.Homotopic (uncurryLoop p) (uncurryLoop q) := by
  obtain ⟨H⟩ := h
  exact ⟨uncurryLoopHomotopy H⟩

theorem Hurewicz.CubicalBoundary.whiskeredCell_face_normal {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x) (i : Fin (n + 1))
    (ε : (unitInterval)) (hε : ε = 0 ∨ ε = 1) (h : i ≠ Fin.last n ∨ ε = 0) :
    uncurryLoop (cubicalFace (whiskeredCell F) i ε hε) =
      GenLoop.transAt 0 GenLoop.const
        (GenLoop.transAt 0 (cubicalFace F i.succ ε hε) GenLoop.const) := by
  apply GenLoop.ext
  intro u
  have hcons (s : (unitInterval)) : Function.update u 0 s = Fin.cons s (fun j => u j.succ) := by
    funext j
    cases j using Fin.cases with
    | zero => simp
    | succ j => simp
  change
    F.val (whiskerMap n (cubeFacet n i ε (fun j => u j.succ), u 0)) =
      GenLoop.transAt 0 GenLoop.const
        (GenLoop.transAt 0 (cubicalFace F i.succ ε hε) GenLoop.const) u
  rw [whiskerMap_concat]
  simp only [GenLoop.transAt, GenLoop.coe_copy, GenLoop.const_apply, Function.update_self,
    Function.update_idem]
  split_ifs with hs ht
  · exact whiskerFacetNormal_arm_based F i ε hε h _ 0 (Or.inl rfl) _
  · rw [cubicalFace_apply, hcons, cubeFacet_succ_cons]
  · exact whiskerFacetNormal_arm_based F i ε hε h _ 1 (Or.inr rfl) _

theorem Hurewicz.CubicalBoundary.whiskerFacet_rotate_coordinates {n : ℕ}
    (u : Fin (n + 1) → (unitInterval)) :
    (fun i => u (finRotate (n + 1) i)) = Fin.snoc (Fin.tail u) (u 0) := by
  simpa only [Fin.cons_self_tail] using (Fin.snoc_eq_cons_rotate (Fin.tail u) (u 0)).symm

theorem Hurewicz.CubicalBoundary.whiskerFacet_zero_coordinates {n : ℕ} (ε : (unitInterval))
    (u : Fin (n + 1) → (unitInterval)) : cubeFacet (n + 1) 0 ε u = Fin.cons ε u :=
  Fin.insertNth_zero' ε u

theorem Hurewicz.CubicalBoundary.whiskerFacet_last_coordinates {n : ℕ} (ε : (unitInterval))
    (u : Fin n → (unitInterval)) : cubeFacet n (Fin.last n) ε u = Fin.snoc u ε :=
  Fin.insertNth_last' ε u

theorem Hurewicz.CubicalBoundary.whiskerFacet_rotated_face_apply {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x) (ε : (unitInterval))
    (hε : ε = 0 ∨ ε = 1) (u : Fin (n + 1) → (unitInterval)) :
    Hurewicz.NativeSubdivision.permuteCubeLoop (cubicalFace F 0 ε hε) (finRotate (n + 1))
        u =
      F.val (Fin.cons ε (Fin.snoc (Fin.tail u) (u 0))) := by
  rw [Hurewicz.NativeSubdivision.permuteCubeLoop_apply, cubicalFace_apply,
    whiskerFacet_zero_coordinates, whiskerFacet_rotate_coordinates]

theorem Hurewicz.CubicalBoundary.whiskerFacet_last_upper_apply {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x)
    (u : Fin (n + 1) → (unitInterval)) :
    cubicalUpperFace F (Fin.last (n + 1)) u = F.val (Fin.cons (u 0) (Fin.snoc (Fin.tail u) 1)) := by
  rw [cubicalFace_apply, whiskerFacet_last_coordinates, Fin.cons_snoc_eq_snoc_cons,
    Fin.cons_self_tail]

theorem Hurewicz.CubicalBoundary.whiskerFacet_symmAt_zero_apply {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin (n + 1)) X x)
    (u : Fin (n + 1) → (unitInterval)) :
    GenLoop.symmAt 0 p u = p (Function.update u 0 ((unitInterval.symm) (u 0))) := by
  change p (fun j => if j = 0 then (unitInterval.symm) (u 0) else u j) = _
  congr 1
  funext j
  simp only [Function.update_apply]

theorem Hurewicz.CubicalBoundary.whiskerFacet_reflected_rotated_face_apply {n : ℕ}
    {X : Type*} [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x) (ε : (unitInterval))
    (hε : ε = 0 ∨ ε = 1) (u : Fin (n + 1) → (unitInterval)) :
    GenLoop.symmAt 0
        (Hurewicz.NativeSubdivision.permuteCubeLoop (cubicalFace F 0 ε hε)
          (finRotate (n + 1)))
        u =
      F.val (Fin.cons ε (Fin.snoc (Fin.tail u) ((unitInterval.symm) (u 0)))) := by
  rw [whiskerFacet_symmAt_zero_apply, whiskerFacet_rotated_face_apply]
  simp only [Fin.tail_update_zero, Function.update_self]

theorem Hurewicz.CubicalBoundary.whiskerFacet_last_upper_uncurry_apply {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x)
    (u : Fin (n + 1) → (unitInterval)) :
    uncurryLoop (cubicalUpperFace (whiskeredCell F) (Fin.last n)) u =
      F.val (Fin.cons (whiskerTrack (u 0)).1 (Fin.snoc (Fin.tail u) (whiskerTrack (u 0)).2)) := by
  rw [uncurryLoop_apply, cubicalFace_apply, whiskeredCell_apply, whiskerFacet_last_coordinates,
    whiskerMap_apply]
  simp only [Fin.init_snoc, Fin.snoc_last, mul_one]
  rfl

theorem Hurewicz.CubicalBoundary.whiskerFacet_transAt_zero_apply {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p q : GenLoop (Fin (n + 1)) X x)
    (u : Fin (n + 1) → (unitInterval)) :
    GenLoop.transAt 0 p q u =
      if (u 0 : ℝ) ≤ 1 / 2 then
        p (Function.update u 0 (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ))))
      else q (Function.update u 0 (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1))) :=
  rfl

theorem Hurewicz.CubicalBoundary.whiskeredCell_face_last_upper {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x) :
    uncurryLoop (cubicalUpperFace (whiskeredCell F) (Fin.last n)) =
      GenLoop.transAt 0
        (Hurewicz.NativeSubdivision.permuteCubeLoop (cubicalLowerFace F 0)
          (finRotate (n + 1)))
        (GenLoop.transAt 0 (cubicalUpperFace F (Fin.last (n + 1)))
          (GenLoop.symmAt 0
            (Hurewicz.NativeSubdivision.permuteCubeLoop (cubicalUpperFace F 0)
              (finRotate (n + 1))))) := by
  apply GenLoop.ext
  intro u
  rw [whiskerFacet_last_upper_uncurry_apply, whiskerTrack_concat, whiskerFacet_transAt_zero_apply]
  by_cases h₀ : (u 0 : ℝ) ≤ 1 / 2
  · simp only [if_pos h₀, whiskerFacet_rotated_face_apply, Fin.tail_update_zero,
      Function.update_self]
  · simp only [if_neg h₀]
    rw [whiskerFacet_transAt_zero_apply]
    simp only [Function.update_self]
    split_ifs
    · rw [whiskerFacet_last_upper_apply]
      simp only [Fin.tail_update_zero, Function.update_self]
    · rw [whiskerFacet_reflected_rotated_face_apply]
      simp only [Fin.tail_update_zero, Function.update_self]

theorem Hurewicz.CubicalBoundary.uncurryTail_update_succ {n : ℕ}
    (u : Fin (n + 1) → (unitInterval)) (i : Fin n) (t : (unitInterval)) :
    (fun j : Fin n => Function.update u i.succ t j.succ) =
      Function.update (fun j : Fin n => u j.succ) i t := by
  funext j
  simp only [Function.update_apply, Fin.succ_inj]

@[simp]
theorem Hurewicz.CubicalBoundary.uncurryHead_update_succ {n : ℕ}
    (u : Fin (n + 1) → (unitInterval)) (i : Fin n) (t : (unitInterval)) :
    Function.update u i.succ t 0 = u 0 := by
  simp only [Function.update_apply, (Fin.succ_ne_zero i).symm, if_false]

theorem Hurewicz.CubicalBoundary.uncurryLoop_transAt {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (i : Fin n)
    (p q : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const) :
    uncurryLoop (GenLoop.transAt i p q) =
      GenLoop.transAt i.succ (uncurryLoop p) (uncurryLoop q) := by
  apply GenLoop.ext
  intro u
  change
    ((if (u i.succ : ℝ) ≤ 1 / 2 then _ else _) : GenLoop (Fin 1) X x) (fun _ => u 0) =
      if (u i.succ : ℝ) ≤ 1 / 2 then _ else _
  split_ifs <;> simp only [uncurryLoop_apply, uncurryTail_update_succ, uncurryHead_update_succ]

theorem Hurewicz.CubicalBoundary.uncurryLoop_symmAt {n : ℕ} {X : Type*} [TopologicalSpace X]
    {x : X} (i : Fin n) (p : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const) :
    uncurryLoop (GenLoop.symmAt i p) = GenLoop.symmAt i.succ (uncurryLoop p) := by
  apply GenLoop.ext
  intro u
  change
    p (fun j => if j = i then (unitInterval.symm) (u i.succ) else u j.succ) (fun _ => u 0) =
      p (fun j => if j.succ = i.succ then (unitInterval.symm) (u i.succ) else u j.succ)
        (fun _ => if (0 : Fin (n + 1)) = i.succ then (unitInterval.symm) (u i.succ) else u 0)
  simp only [Fin.succ_inj, (Fin.succ_ne_zero i).symm, if_false]

theorem Hurewicz.CubicalBoundary.uncurryLoop_swap {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} (p : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const) (i j : Fin n) :
    uncurryLoop (Hurewicz.NativeSubdivision.permuteCubeLoop p (Equiv.swap i j)) =
      Hurewicz.NativeSubdivision.permuteCubeLoop (uncurryLoop p)
        (Equiv.swap i.succ j.succ) := by
  have hzero : Equiv.swap i.succ j.succ (0 : Fin (n + 1)) = 0 :=
    Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i).symm (Fin.succ_ne_zero j).symm
  have hsucc (k : Fin n) : Equiv.swap i.succ j.succ k.succ = (Equiv.swap i j k).succ := by
    by_cases hki : k = i
    · subst k
      simp
    by_cases hkj : k = j
    · subst k
      simp
    have hki' : k.succ ≠ i.succ := fun h => hki (Fin.succ_inj.mp h)
    have hkj' : k.succ ≠ j.succ := fun h => hkj (Fin.succ_inj.mp h)
    rw [Equiv.swap_apply_of_ne_of_ne hki' hkj', Equiv.swap_apply_of_ne_of_ne hki hkj]
  apply GenLoop.ext
  intro u
  change
    p (fun k => u (Equiv.swap i j k).succ) (fun _ => u 0) =
      p (fun k => u (Equiv.swap i.succ j.succ k.succ)) (fun _ => u (Equiv.swap i.succ j.succ 0))
  simp only [hsucc, hzero]

def Hurewicz.CubicalBoundary.CubicalEvaluator.uncurry {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} {A : Type*} [AddCommGroup A]
    (E : Hurewicz.CubicalBoundary.CubicalEvaluator (n + 1) x A) :
    Hurewicz.CubicalBoundary.CubicalEvaluator n (GenLoop.const : GenLoop (Fin 1) X x) A
    where
  evaluate p := E (Hurewicz.CubicalBoundary.uncurryLoop p)
  map_const := by rw [Hurewicz.CubicalBoundary.uncurryLoop_const]; exact E.map_const
  map_homotopic h := E.map_homotopic (Hurewicz.CubicalBoundary.uncurryLoop_homotopic h)
  map_transAt i p
    q := by
    rw [Hurewicz.CubicalBoundary.uncurryLoop_transAt]
    exact E.map_transAt i.succ _ _
  map_symmAt i
    p := by
    rw [Hurewicz.CubicalBoundary.uncurryLoop_symmAt]
    exact E.map_symmAt i.succ _
  map_swap p i j
    hij := by
    rw [Hurewicz.CubicalBoundary.uncurryLoop_swap]
    exact E.map_swap _ i.succ j.succ (fun h => hij (Fin.succ_inj.mp h))

@[simp]
theorem Hurewicz.CubicalBoundary.CubicalEvaluator.uncurry_apply {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} {A : Type*} [AddCommGroup A]
    (E : Hurewicz.CubicalBoundary.CubicalEvaluator (n + 1) x A)
    (p : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const) :
    E.uncurry p = E (Hurewicz.CubicalBoundary.uncurryLoop p) :=
  rfl

theorem Hurewicz.CubicalBoundary.CubicalEvaluator.map_constantClosingPaths {n : ℕ}
    {X : Type*} [TopologicalSpace X] {x : X} {A : Type*} [AddCommGroup A]
    (E : Hurewicz.CubicalBoundary.CubicalEvaluator (n + 1) x A)
    (p : GenLoop (Fin (n + 1)) X x) :
    E (GenLoop.transAt 0 GenLoop.const (GenLoop.transAt 0 p GenLoop.const)) = E p := by
  rw [E.map_transAt, E.map_transAt, E.map_const, zero_add, add_zero]

theorem Hurewicz.CubicalBoundary.CubicalEvaluator.map_cyclicClosingPaths {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} {A : Type*} [AddCommGroup A]
    (E : Hurewicz.CubicalBoundary.CubicalEvaluator (n + 1) x A)
    (l p r : GenLoop (Fin (n + 1)) X x) :
    E
        (GenLoop.transAt 0
          (Hurewicz.NativeSubdivision.permuteCubeLoop l (finRotate (n + 1)))
          (GenLoop.transAt 0 p
            (GenLoop.symmAt 0
              (Hurewicz.NativeSubdivision.permuteCubeLoop r (finRotate (n + 1)))))) =
      E p - (-1 : ℤ) ^ n • (E r - E l) := by
  rw [E.map_transAt, E.map_transAt, E.map_symmAt, E.map_finRotate, E.map_finRotate]
  simp only [Nat.add_sub_cancel, smul_sub]
  abel

theorem Hurewicz.CubicalBoundary.alternatingSign_smul_involution {A : Type*}
    [AddCommGroup A] (n : ℕ) (a : A) : (-1 : ℤ) ^ n • ((-1 : ℤ) ^ n • a) = a := by
  rw [smul_smul, ← mul_pow]
  simp

theorem Hurewicz.CubicalBoundary.alternatingSum_head {A : Type*} [AddCommGroup A] (n : ℕ)
    (a : Fin (n + 2) → A) :
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • a i) =
      a 0 - ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • a i.succ := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ', neg_mul, one_mul,
    neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem Hurewicz.CubicalBoundary.alternatingSum_dimension_reduction {A : Type*}
    [AddCommGroup A] (n : ℕ) (a : Fin (n + 2) → A) (b : Fin (n + 1) → A)
    (hmid : ∀ i : Fin n, b i.castSucc = a i.castSucc.succ)
    (hlast : b (Fin.last n) = a (Fin.last (n + 1)) - (-1 : ℤ) ^ n • a 0) :
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • a i) = -(∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • b i) := by
  have htail :
    (∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • b i) =
      (∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • a i.succ) - a 0 := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [hmid, hlast, Fin.val_castSucc, Fin.val_last, Fin.succ_last, smul_sub,
      alternatingSign_smul_involution]
    abel
  rw [alternatingSum_head, htail]
  abel

theorem Hurewicz.CubicalBoundary.whiskeredCell_lower_value {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} {A : Type*} [AddCommGroup A] (E : CubicalEvaluator (n + 1) x A)
    (F : BasedCubicalCell (n + 2) x) (i : Fin (n + 1)) :
    E.uncurry (cubicalLowerFace (whiskeredCell F) i) = E (cubicalLowerFace F i.succ) := by
  rw [CubicalEvaluator.uncurry_apply, whiskeredCell_face_normal F i 0 (Or.inl rfl) (Or.inr rfl)]
  exact E.map_constantClosingPaths _

theorem Hurewicz.CubicalBoundary.whiskeredCell_upper_value {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} {A : Type*} [AddCommGroup A] (E : CubicalEvaluator (n + 1) x A)
    (F : BasedCubicalCell (n + 2) x) (i : Fin n) :
    E.uncurry (cubicalUpperFace (whiskeredCell F) i.castSucc) =
      E (cubicalUpperFace F i.castSucc.succ) := by
  rw [CubicalEvaluator.uncurry_apply,
    whiskeredCell_face_normal F i.castSucc 1 (Or.inr rfl) (Or.inl (Fin.castSucc_ne_last i))]
  exact E.map_constantClosingPaths _

theorem Hurewicz.CubicalBoundary.whiskeredCell_last_upper_value {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} {A : Type*} [AddCommGroup A] (E : CubicalEvaluator (n + 1) x A)
    (F : BasedCubicalCell (n + 2) x) :
    E.uncurry (cubicalUpperFace (whiskeredCell F) (Fin.last n)) =
      E (cubicalUpperFace F (Fin.last (n + 1))) -
        (-1 : ℤ) ^ n • (E (cubicalUpperFace F 0) - E (cubicalLowerFace F 0)) := by
  rw [CubicalEvaluator.uncurry_apply, whiskeredCell_face_last_upper]
  exact E.map_cyclicClosingPaths _ _ _

theorem Hurewicz.CubicalBoundary.cubicalBoundaryValue_dimension_reduction {n : ℕ}
    {X : Type*} [TopologicalSpace X] {x : X} {A : Type*} [AddCommGroup A]
    (E : CubicalEvaluator (n + 1) x A) (F : BasedCubicalCell (n + 2) x) :
    cubicalBoundaryValue E F = -cubicalBoundaryValue E.uncurry (whiskeredCell F) := by
  unfold cubicalBoundaryValue
  apply alternatingSum_dimension_reduction n
  · intro i
    rw [whiskeredCell_upper_value, whiskeredCell_lower_value]
  · rw [whiskeredCell_last_upper_value, whiskeredCell_lower_value, Fin.succ_last]
    abel

def Hurewicz.CubicalBoundary.squareLowerRoute :
    C(Fin 1 → (unitInterval), Fin 2 → (unitInterval))
    where
  toFun
    u :=
    ![Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ)),
      Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1)]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp
    · exact continuous_projIcc.comp (by fun_prop)
    · exact continuous_projIcc.comp (by fun_prop)

def Hurewicz.CubicalBoundary.squareUpperRoute :
    C(Fin 1 → (unitInterval), Fin 2 → (unitInterval))
    where
  toFun
    u :=
    ![Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1),
      Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ))]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp
    · exact continuous_projIcc.comp (by fun_prop)
    · exact continuous_projIcc.comp (by fun_prop)

@[simp]
theorem Hurewicz.CubicalBoundary.squareLowerRoute_zero (u : Fin 1 → (unitInterval))
    (hu : u 0 = 0) : squareLowerRoute u = fun _ => 0 := by
  funext i
  fin_cases i <;> apply Subtype.ext <;> norm_num [squareLowerRoute, hu, Set.projIcc]

@[simp]
theorem Hurewicz.CubicalBoundary.squareLowerRoute_one (u : Fin 1 → (unitInterval))
    (hu : u 0 = 1) : squareLowerRoute u = fun _ => 1 := by
  funext i
  fin_cases i <;> apply Subtype.ext <;> norm_num [squareLowerRoute, hu, Set.projIcc]

@[simp]
theorem Hurewicz.CubicalBoundary.squareUpperRoute_zero (u : Fin 1 → (unitInterval))
    (hu : u 0 = 0) : squareUpperRoute u = fun _ => 0 := by
  funext i
  fin_cases i <;> apply Subtype.ext <;> norm_num [squareUpperRoute, hu, Set.projIcc]

@[simp]
theorem Hurewicz.CubicalBoundary.squareUpperRoute_one (u : Fin 1 → (unitInterval))
    (hu : u 0 = 1) : squareUpperRoute u = fun _ => 1 := by
  funext i
  fin_cases i <;> apply Subtype.ext <;> norm_num [squareUpperRoute, hu, Set.projIcc]

theorem Hurewicz.CubicalBoundary.squareLowerRoute_of_le (u : Fin 1 → (unitInterval))
    (hu : (u 0 : ℝ) ≤ 1 / 2) :
    squareLowerRoute u = ![Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ)), 0] := by
  funext i
  fin_cases i
  · rfl
  · exact Set.projIcc_of_le_left zero_le_one (by linarith)

theorem Hurewicz.CubicalBoundary.squareLowerRoute_of_not_le (u : Fin 1 → (unitInterval))
    (hu : ¬(u 0 : ℝ) ≤ 1 / 2) :
    squareLowerRoute u = ![1, Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1)] := by
  funext i
  fin_cases i
  · exact Set.projIcc_of_right_le zero_le_one (by linarith)
  · rfl

theorem Hurewicz.CubicalBoundary.squareUpperRoute_of_le (u : Fin 1 → (unitInterval))
    (hu : (u 0 : ℝ) ≤ 1 / 2) :
    squareUpperRoute u = ![0, Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ))] := by
  funext i
  fin_cases i
  · exact Set.projIcc_of_le_left zero_le_one (by linarith)
  · rfl

theorem Hurewicz.CubicalBoundary.squareUpperRoute_of_not_le (u : Fin 1 → (unitInterval))
    (hu : ¬(u 0 : ℝ) ≤ 1 / 2) :
    squareUpperRoute u = ![Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1), 1] := by
  funext i
  fin_cases i
  · rfl
  · exact Set.projIcc_of_right_le zero_le_one (by linarith)

def Hurewicz.CubicalBoundary.squareRoutesBlend :
    C((unitInterval) × (Fin 1 → (unitInterval)), Fin 2 → (unitInterval))
    where
  toFun
    u :=
    Hurewicz.NativeSubdivision.nativeCubeBlend u.1 (squareLowerRoute u.2)
      (squareUpperRoute u.2)
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact
      Set.Icc.continuous_convexComb_prod.comp
        (((continuous_apply i).comp (squareLowerRoute.continuous.comp continuous_snd)).prodMk
          (((continuous_apply i).comp (squareUpperRoute.continuous.comp continuous_snd)).prodMk
            continuous_fst))

@[simp]
theorem Hurewicz.CubicalBoundary.squareRoutesBlend_zero (u : Fin 1 → (unitInterval)) :
    squareRoutesBlend (0, u) = squareLowerRoute u :=
  Hurewicz.NativeSubdivision.nativeCubeBlend_zero _ _

@[simp]
theorem Hurewicz.CubicalBoundary.squareRoutesBlend_one (u : Fin 1 → (unitInterval)) :
    squareRoutesBlend (1, u) = squareUpperRoute u :=
  Hurewicz.NativeSubdivision.nativeCubeBlend_one _ _

theorem Hurewicz.CubicalBoundary.squareRoutesBlend_endpoint_zero (t : (unitInterval))
    (u : Fin 1 → (unitInterval)) (hu : u 0 = 0) : squareRoutesBlend (t, u) = fun _ => 0 := by
  funext i
  simp [squareRoutesBlend, Hurewicz.NativeSubdivision.nativeCubeBlend,
    squareLowerRoute_zero u hu, squareUpperRoute_zero u hu]

theorem Hurewicz.CubicalBoundary.squareRoutesBlend_endpoint_one (t : (unitInterval))
    (u : Fin 1 → (unitInterval)) (hu : u 0 = 1) : squareRoutesBlend (t, u) = fun _ => 1 := by
  funext i
  simp [squareRoutesBlend, Hurewicz.NativeSubdivision.nativeCubeBlend,
    squareLowerRoute_one u hu, squareUpperRoute_one u hu]

theorem Hurewicz.CubicalBoundary.squareFacet_zero (ε : (unitInterval))
    (u : Fin 1 → (unitInterval)) : cubeFacet 1 0 ε u = ![ε, u 0] := by
  funext i
  fin_cases i
  · exact cubeFacet_apply_self 1 0 ε u
  · change cubeFacet 1 0 ε u ((0 : Fin 2).succAbove 0) = u 0
    exact cubeFacet_apply_succAbove 1 0 ε u 0

theorem Hurewicz.CubicalBoundary.squareFacet_one (ε : (unitInterval))
    (u : Fin 1 → (unitInterval)) : cubeFacet 1 1 ε u = ![u 0, ε] := by
  funext i
  fin_cases i
  · change cubeFacet 1 1 ε u ((1 : Fin 2).succAbove 0) = u 0
    exact cubeFacet_apply_succAbove 1 1 ε u 0
  · exact cubeFacet_apply_self 1 1 ε u

theorem Hurewicz.CubicalBoundary.squareLowerRoute_transAt_apply {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell 2 x) (u : Fin 1 → (unitInterval)) :
    GenLoop.transAt 0 (cubicalLowerFace F 1) (cubicalUpperFace F 0) u =
      F.val (squareLowerRoute u) := by
  change
    (if (u 0 : ℝ) ≤ 1 / 2 then
        F.val
          (cubeFacet 1 1 0 (Function.update u 0 (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ)))))
      else
        F.val
          (cubeFacet 1 0 1
            (Function.update u 0 (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1))))) =
      _
  by_cases hu : (u 0 : ℝ) ≤ 1 / 2
  · rw [if_pos hu, squareLowerRoute_of_le u hu]
    simp only [squareFacet_one, Function.update_self]
  · rw [if_neg hu, squareLowerRoute_of_not_le u hu]
    simp only [squareFacet_zero, Function.update_self]

theorem Hurewicz.CubicalBoundary.squareUpperRoute_transAt_apply {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell 2 x) (u : Fin 1 → (unitInterval)) :
    GenLoop.transAt 0 (cubicalLowerFace F 0) (cubicalUpperFace F 1) u =
      F.val (squareUpperRoute u) := by
  change
    (if (u 0 : ℝ) ≤ 1 / 2 then
        F.val
          (cubeFacet 1 0 0 (Function.update u 0 (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ)))))
      else
        F.val
          (cubeFacet 1 1 1
            (Function.update u 0 (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1))))) =
      _
  by_cases hu : (u 0 : ℝ) ≤ 1 / 2
  · rw [if_pos hu, squareUpperRoute_of_le u hu]
    simp only [squareFacet_zero, Function.update_self]
  · rw [if_neg hu, squareUpperRoute_of_not_le u hu]
    simp only [squareFacet_one, Function.update_self]

def Hurewicz.CubicalBoundary.squareCubicalFacesHomotopy {X : Type*} [TopologicalSpace X]
    {x : X} (F : BasedCubicalCell 2 x) :
    (GenLoop.transAt 0 (cubicalLowerFace F 1) (cubicalUpperFace F 0)).val.HomotopyRel
      (GenLoop.transAt 0 (cubicalLowerFace F 0) (cubicalUpperFace F 1)).val
      (Cube.boundary (Fin 1))
    where
  toFun z := F.val (squareRoutesBlend z)
  continuous_toFun := F.val.continuous.comp squareRoutesBlend.continuous
  map_zero_left
    u := by
    rw [squareRoutesBlend_zero]
    exact (squareLowerRoute_transAt_apply F u).symm
  map_one_left
    u := by
    rw [squareRoutesBlend_one]
    exact (squareUpperRoute_transAt_apply F u).symm
  prop' t u
    hu := by
    change
      F.val (squareRoutesBlend (t, u)) =
        GenLoop.transAt 0 (cubicalLowerFace F 1) (cubicalUpperFace F 0) u
    refine
      Eq.trans (b := x) ?_
        ((GenLoop.transAt 0 (cubicalLowerFace F 1) (cubicalUpperFace F 0)).property u hu).symm
    obtain ⟨i, hi⟩ := hu
    have hi0 : u 0 = 0 ∨ u 0 = 1 := by simpa only [Fin.fin_one_eq_zero] using hi
    rcases hi0 with hi0 | hi0
    · exact
        (congrArg F.val (squareRoutesBlend_endpoint_zero t u hi0)).trans
          (F.property (fun _ => 0) 0 1 (by decide) (Or.inl rfl) (Or.inl rfl))
    · exact
        (congrArg F.val (squareRoutesBlend_endpoint_one t u hi0)).trans
          (F.property (fun _ => 1) 0 1 (by decide) (Or.inr rfl) (Or.inr rfl))

theorem Hurewicz.CubicalBoundary.squareCubicalFaces_homotopic {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell 2 x) :
    GenLoop.Homotopic (GenLoop.transAt 0 (cubicalLowerFace F 1) (cubicalUpperFace F 0))
      (GenLoop.transAt 0 (cubicalLowerFace F 0) (cubicalUpperFace F 1)) :=
  ⟨squareCubicalFacesHomotopy F⟩

theorem Hurewicz.CubicalBoundary.cubicalBoundaryValue_square {X : Type*}
    [TopologicalSpace X] {x : X} {A : Type*} [AddCommGroup A] (E : CubicalEvaluator 1 x A)
    (F : BasedCubicalCell 2 x) : cubicalBoundaryValue E F = 0 := by
  have h := E.map_homotopic (squareCubicalFaces_homotopic F)
  rw [E.map_transAt, E.map_transAt] at h
  unfold cubicalBoundaryValue
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ,
    Nat.zero_add, pow_zero, pow_one, one_zsmul, neg_one_zsmul, ← sub_eq_add_neg]
  change
    (E (cubicalUpperFace F 0) - E (cubicalLowerFace F 0)) -
        (E (cubicalUpperFace F 1) - E (cubicalLowerFace F 1)) =
      0
  apply sub_eq_zero.mpr
  apply sub_eq_sub_iff_add_eq_add.mpr
  simpa only [add_comm] using h

theorem Hurewicz.CubicalBoundary.cubicalBoundaryValue_eq_zero (n : ℕ) :
    ∀ {X : Type u} [TopologicalSpace X] {x : X} {A : Type v} [AddCommGroup A]
      (E : CubicalEvaluator (n + 1) x A) (F : BasedCubicalCell (n + 2) x),
      cubicalBoundaryValue E F = 0 := by
  induction n with
  | zero =>
    intro X _ x A _ E F
    exact cubicalBoundaryValue_square E F
  | succ n ih =>
    intro X _ x A _ E F
    rw [cubicalBoundaryValue_dimension_reduction, ih E.uncurry (whiskeredCell F), neg_zero]

theorem Hurewicz.SimplexGeometry.basedSimplexBoundary_evaluation {X : Type*}
    [TopologicalSpace X] {x : X} {A : Type*} [AddCommGroup A] {n : ℕ}
    (E : Hurewicz.CubicalBoundary.CubicalEvaluator (n + 1) x A)
    (τ : BasedSimplexBoundary (n + 2) x) :
    (∑ i : Fin (n + 3), (-1 : ℤ) ^ i.val • E (basedSimplexLoop (basedSimplexBoundaryFace τ i))) =
      0 := by
  rw [← simplexBoundaryCube_boundaryValue]
  exact Hurewicz.CubicalBoundary.cubicalBoundaryValue_eq_zero n E (simplexBoundaryCube τ)

theorem Hurewicz.SimplexGeometry.basedSimplexBoundary_signed_relation {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (τ : BasedSimplexBoundary (n + 3) x) :
    (∑ i : Fin (n + 4), (-1 : ℤ) ^ i.val • basedSimplexClass (basedSimplexBoundaryFace τ i)) =
      0 :=
  basedSimplexBoundary_evaluation (Hurewicz.CubicalBoundary.nativeCubicalEvaluator n x) τ

def Hurewicz.CubeGluing.CubeCompatible {n : ℕ} {X : Type} [TopologicalSpace X]
    (F : Equiv.Perm (Fin n) → C((unitInterval) × SingularChains.Simplex n, X)) : Prop :=
  ∀ (e f : Equiv.Perm (Fin n)) (s t : SingularChains.Simplex n),
    Hurewicz.CubeTriangulation.cubeSimplex e s =
        Hurewicz.CubeTriangulation.cubeSimplex f t →
      ∀ r : (unitInterval), F e (r, s) = F f (r, t)

def Hurewicz.CubeGluing.cubeFamilyMap {n : ℕ} {X : Type} [TopologicalSpace X]
    (F : Equiv.Perm (Fin n) → C((unitInterval) × SingularChains.Simplex n, X)) :
    C((Σ _e : Equiv.Perm (Fin n), (unitInterval) × SingularChains.Simplex n), X)
    where
  toFun a := F a.fst a.snd
  continuous_toFun := continuous_sigma fun e => (F e).continuous

theorem Hurewicz.CubeGluing.cubeFamilyMap_factorsThrough {n : ℕ} {X : Type}
    [TopologicalSpace X] (F : Equiv.Perm (Fin n) → C((unitInterval) × SingularChains.Simplex n, X))
    (hF : CubeCompatible F) :
    Function.FactorsThrough (cubeFamilyMap F)
      (Hurewicz.CubeTriangulation.cubeCylinderCover n) := by
  rintro ⟨e, r, s⟩ ⟨f, q, t⟩ h
  have hr : r = q := congrArg Prod.fst h
  have hs :
    Hurewicz.CubeTriangulation.cubeSimplex e s =
      Hurewicz.CubeTriangulation.cubeSimplex f t :=
    congrArg Prod.snd h
  subst q
  exact hF e f s t hs r

def Hurewicz.CubeGluing.glueCubeHomotopies {n : ℕ} {X : Type} [TopologicalSpace X]
    (F : Equiv.Perm (Fin n) → C((unitInterval) × SingularChains.Simplex n, X))
    (hF : CubeCompatible F) : C((unitInterval) × Hurewicz.CubeTriangulation.CubeN n, X) :=
  (Hurewicz.CubeTriangulation.cubeCylinderCover_isQuotientMap n).lift (cubeFamilyMap F)
    (cubeFamilyMap_factorsThrough F hF)

@[simp]
theorem Hurewicz.CubeGluing.glueCubeHomotopies_cell {n : ℕ} {X : Type} [TopologicalSpace X]
    (F : Equiv.Perm (Fin n) → C((unitInterval) × SingularChains.Simplex n, X))
    (hF : CubeCompatible F) (e : Equiv.Perm (Fin n)) (r : (unitInterval))
    (s : SingularChains.Simplex n) :
    glueCubeHomotopies F hF (r, Hurewicz.CubeTriangulation.cubeSimplex e s) = F e (r, s) :=
  DFunLike.congr_fun
    ((Hurewicz.CubeTriangulation.cubeCylinderCover_isQuotientMap n).lift_comp
      (cubeFamilyMap F) (cubeFamilyMap_factorsThrough F hF))
    ⟨e, (r, s)⟩

theorem Hurewicz.CubeGluing.glueCubeHomotopies_time {n : ℕ} {X : Type} [TopologicalSpace X]
    (F : Equiv.Perm (Fin n) → C((unitInterval) × SingularChains.Simplex n, X))
    (hF : CubeCompatible F) (r : (unitInterval))
    (g : Hurewicz.CubeTriangulation.CubeN n → X)
    (h :
      ∀ (e : Equiv.Perm (Fin n)) (s : SingularChains.Simplex n),
        F e (r, s) = g (Hurewicz.CubeTriangulation.cubeSimplex e s))
    (u : Hurewicz.CubeTriangulation.CubeN n) : glueCubeHomotopies F hF (r, u) = g u := by
  obtain ⟨e, s, rfl⟩ := Hurewicz.CubeTriangulation.exists_cubeSimplex u
  exact (glueCubeHomotopies_cell F hF e r s).trans (h e s)

theorem Hurewicz.CubeGluing.glueCubeHomotopies_zero {n : ℕ} {X : Type} [TopologicalSpace X]
    (F : Equiv.Perm (Fin n) → C((unitInterval) × SingularChains.Simplex n, X))
    (hF : CubeCompatible F) (g : C(Hurewicz.CubeTriangulation.CubeN n, X))
    (h :
      ∀ (e : Equiv.Perm (Fin n)) (s : SingularChains.Simplex n),
        F e (0, s) = g (Hurewicz.CubeTriangulation.cubeSimplex e s))
    (u : Hurewicz.CubeTriangulation.CubeN n) : glueCubeHomotopies F hF (0, u) = g u :=
  glueCubeHomotopies_time F hF 0 g h u

theorem Hurewicz.CubeGluing.cubeOriginal_face_zero {n : ℕ} {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin (n + 1)) X x) (e : Equiv.Perm (Fin (n + 1))) :
    (p.val.comp (Hurewicz.CubeTriangulation.cubeSimplex e)).comp
        (SingularChains.simplexFace n 0) =
      ContinuousMap.const (SingularChains.Simplex n) x := by
  ext s
  exact GenLoop.boundary p _ (Hurewicz.CubeTriangulation.cubeSimplex_face_zero_boundary e s)

theorem Hurewicz.CubeGluing.cubeOriginal_face_last {n : ℕ} {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin (n + 1)) X x) (e : Equiv.Perm (Fin (n + 1))) :
    (p.val.comp (Hurewicz.CubeTriangulation.cubeSimplex e)).comp
        (SingularChains.simplexFace n (Fin.last (n + 1))) =
      ContinuousMap.const (SingularChains.Simplex n) x := by
  ext s
  exact GenLoop.boundary p _ (Hurewicz.CubeTriangulation.cubeSimplex_face_last_boundary e s)

theorem Hurewicz.CubeGluing.cubeOriginal_face_swap {n : ℕ} {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin (n + 1)) X x) (e : Equiv.Perm (Fin (n + 1))) (i : Fin n) :
    (p.val.comp (Hurewicz.CubeTriangulation.cubeSimplex e)).comp
        (SingularChains.simplexFace n i.succ.castSucc) =
      (p.val.comp
            (Hurewicz.CubeTriangulation.cubeSimplex
              ((Equiv.swap i.castSucc i.succ).trans e))).comp
        (SingularChains.simplexFace n i.succ.castSucc) := by
  simpa only [ContinuousMap.comp_assoc] using
    congrArg
      (fun f : C(SingularChains.Simplex n, Hurewicz.CubeTriangulation.CubeN (n + 1)) =>
        p.val.comp f)
      (Hurewicz.CubeTriangulation.cubeSimplex_face_swap e i)

theorem Hurewicz.CubeGluing.coherentCubeCell_face {n : ℕ} {X : Type} [TopologicalSpace X]
    {x : X} (H₀ : C(SingularChains.Simplex n, X) → C((unitInterval) × SingularChains.Simplex n, X))
    (H₁ :
      C(SingularChains.Simplex (n + 1), X) → C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H₀ H₁)
    (p : GenLoop (Fin (n + 1)) X x) (e : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 2))
    (r : (unitInterval)) (s : SingularChains.Simplex n) :
    H₁ (p.val.comp (Hurewicz.CubeTriangulation.cubeSimplex e))
        (r, SingularChains.simplexFace n i s) =
      H₀
        ((p.val.comp (Hurewicz.CubeTriangulation.cubeSimplex e)).comp
          (SingularChains.simplexFace n i))
        (r, s) :=
  DFunLike.congr_fun (hface (p.val.comp (Hurewicz.CubeTriangulation.cubeSimplex e)) i)
    (r, s)

theorem Hurewicz.CubeGluing.coherentCubeCell_swap {n : ℕ} {X : Type} [TopologicalSpace X]
    {x : X} (H₀ : C(SingularChains.Simplex n, X) → C((unitInterval) × SingularChains.Simplex n, X))
    (H₁ :
      C(SingularChains.Simplex (n + 1), X) → C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H₀ H₁)
    (p : GenLoop (Fin (n + 1)) X x) (e : Equiv.Perm (Fin (n + 1))) (i : Fin n)
    (r : (unitInterval)) (s : SingularChains.Simplex (n + 1)) (hs : s i.succ.castSucc = 0) :
    H₁ (p.val.comp (Hurewicz.CubeTriangulation.cubeSimplex e)) (r, s) =
      H₁
        (p.val.comp
          (Hurewicz.CubeTriangulation.cubeSimplex ((Equiv.swap i.castSucc i.succ).trans e)))
        (r, s) := by
  let t := SecondHurewicz.SimplyConnected.simplexFaceInverse n i.succ.castSucc ⟨s, hs⟩
  have ht : SingularChains.simplexFace n i.succ.castSucc t = s :=
    SecondHurewicz.SimplyConnected.simplexFace_inverse n i.succ.castSucc ⟨s, hs⟩
  rw [← ht, coherentCubeCell_face H₀ H₁ hface, coherentCubeCell_face H₀ H₁ hface,
    cubeOriginal_face_swap]

theorem Hurewicz.CubeGluing.coherentCubeCell_boundary {n : ℕ} {X : Type}
    [TopologicalSpace X] {x : X}
    (H₀ : C(SingularChains.Simplex n, X) → C((unitInterval) × SingularChains.Simplex n, X))
    (H₁ :
      C(SingularChains.Simplex (n + 1), X) → C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H₀ H₁)
    (hconst :
      H₀ (ContinuousMap.const (SingularChains.Simplex n) x) =
        ContinuousMap.const ((unitInterval) × SingularChains.Simplex n) x)
    (p : GenLoop (Fin (n + 1)) X x) (e : Equiv.Perm (Fin (n + 1))) (r : (unitInterval))
    (s : SingularChains.Simplex (n + 1))
    (hs : Hurewicz.CubeTriangulation.cubeSimplex e s ∈ Cube.boundary (Fin (n + 1))) :
    H₁ (p.val.comp (Hurewicz.CubeTriangulation.cubeSimplex e)) (r, s) = x := by
  rcases (Hurewicz.CubeTriangulation.cubeSimplex_mem_boundary_iff e s).mp hs with hs | hs
  · let t := SecondHurewicz.SimplyConnected.simplexFaceInverse n 0 ⟨s, hs⟩
    have ht : SingularChains.simplexFace n 0 t = s :=
      SecondHurewicz.SimplyConnected.simplexFace_inverse n 0 ⟨s, hs⟩
    rw [← ht, coherentCubeCell_face H₀ H₁ hface, cubeOriginal_face_zero, hconst]
    rfl
  · let t := SecondHurewicz.SimplyConnected.simplexFaceInverse n (Fin.last (n + 1)) ⟨s, hs⟩
    have ht : SingularChains.simplexFace n (Fin.last (n + 1)) t = s :=
      SecondHurewicz.SimplyConnected.simplexFace_inverse n (Fin.last (n + 1)) ⟨s, hs⟩
    rw [← ht, coherentCubeCell_face H₀ H₁ hface, cubeOriginal_face_last, hconst]
    rfl

theorem Hurewicz.CubeGluing.coherentCubeFamily_compatible {n : ℕ} {X : Type}
    [TopologicalSpace X] {x : X}
    (H₀ : C(SingularChains.Simplex n, X) → C((unitInterval) × SingularChains.Simplex n, X))
    (H₁ :
      C(SingularChains.Simplex (n + 1), X) → C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H₀ H₁)
    (p : GenLoop (Fin (n + 1)) X x) :
    CubeCompatible (fun e => H₁ (p.val.comp (Hurewicz.CubeTriangulation.cubeSimplex e))) := by
  intro e f s t h r
  have hst := Hurewicz.CubeTriangulation.cubeSimplex_overlap_preimage e f s t h
  subst t
  have hf :
    Hurewicz.CubeTriangulation.SortedCoordinates
      (Hurewicz.CubeTriangulation.cubeSimplex e s) f := by
    rw [h]
    exact Hurewicz.CubeTriangulation.cubeSimplex_sorted f s
  apply
    Hurewicz.CubeTriangulation.eq_of_sorted_adjacent
      (Hurewicz.CubeTriangulation.cubeSimplex e s)
      (fun g => H₁ (p.val.comp (Hurewicz.CubeTriangulation.cubeSimplex g)) (r, s)) ?_
      (Hurewicz.CubeTriangulation.cubeSimplex_sorted e s) hf
  intro g hg i ht
  apply coherentCubeCell_swap H₀ H₁ hface p g i r s
  apply Hurewicz.CubeTriangulation.cubeSimplex_tie g s i
  simpa only [Hurewicz.CubeTriangulation.cubeSimplex_eq_of_sorted e g s hg] using ht

def Hurewicz.CubeGluing.coherentCubeHomotopyMap {n : ℕ} {X : Type} [TopologicalSpace X]
    {x : X} (H₀ : C(SingularChains.Simplex n, X) → C((unitInterval) × SingularChains.Simplex n, X))
    (H₁ :
      C(SingularChains.Simplex (n + 1), X) → C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H₀ H₁)
    (p : GenLoop (Fin (n + 1)) X x) :
    C((unitInterval) × Hurewicz.CubeTriangulation.CubeN (n + 1), X) :=
  glueCubeHomotopies (fun e => H₁ (p.val.comp (Hurewicz.CubeTriangulation.cubeSimplex e)))
    (coherentCubeFamily_compatible H₀ H₁ hface p)

@[simp]
theorem Hurewicz.CubeGluing.coherentCubeHomotopyMap_cell {n : ℕ} {X : Type}
    [TopologicalSpace X] {x : X}
    (H₀ : C(SingularChains.Simplex n, X) → C((unitInterval) × SingularChains.Simplex n, X))
    (H₁ :
      C(SingularChains.Simplex (n + 1), X) → C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H₀ H₁)
    (p : GenLoop (Fin (n + 1)) X x) (e : Equiv.Perm (Fin (n + 1))) (r : (unitInterval))
    (s : SingularChains.Simplex (n + 1)) :
    coherentCubeHomotopyMap H₀ H₁ hface p (r, Hurewicz.CubeTriangulation.cubeSimplex e s) =
      H₁ (p.val.comp (Hurewicz.CubeTriangulation.cubeSimplex e)) (r, s) :=
  glueCubeHomotopies_cell _ _ e r s

theorem Hurewicz.CubeGluing.coherentCubeHomotopyMap_zero {n : ℕ} {X : Type}
    [TopologicalSpace X] {x : X}
    (H₀ : C(SingularChains.Simplex n, X) → C((unitInterval) × SingularChains.Simplex n, X))
    (H₁ :
      C(SingularChains.Simplex (n + 1), X) → C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H₀ H₁)
    (hzero :
      ∀ (smp : C(SingularChains.Simplex (n + 1), X)) (s : SingularChains.Simplex (n + 1)),
        H₁ smp (0, s) = smp s)
    (p : GenLoop (Fin (n + 1)) X x) (u : Hurewicz.CubeTriangulation.CubeN (n + 1)) :
    coherentCubeHomotopyMap H₀ H₁ hface p (0, u) = p u :=
  glueCubeHomotopies_zero _ _ p.val
    (fun e s => hzero (p.val.comp (Hurewicz.CubeTriangulation.cubeSimplex e)) s) u

theorem Hurewicz.CubeGluing.coherentCubeHomotopyMap_boundary {n : ℕ} {X : Type}
    [TopologicalSpace X] {x : X}
    (H₀ : C(SingularChains.Simplex n, X) → C((unitInterval) × SingularChains.Simplex n, X))
    (H₁ :
      C(SingularChains.Simplex (n + 1), X) → C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H₀ H₁)
    (hconst :
      H₀ (ContinuousMap.const (SingularChains.Simplex n) x) =
        ContinuousMap.const ((unitInterval) × SingularChains.Simplex n) x)
    (p : GenLoop (Fin (n + 1)) X x) (r : (unitInterval))
    (u : Hurewicz.CubeTriangulation.CubeN (n + 1)) (hu : u ∈ Cube.boundary (Fin (n + 1))) :
    coherentCubeHomotopyMap H₀ H₁ hface p (r, u) = x := by
  obtain ⟨e, s, rfl⟩ := Hurewicz.CubeTriangulation.exists_cubeSimplex u
  rw [coherentCubeHomotopyMap_cell]
  exact coherentCubeCell_boundary H₀ H₁ hface hconst p e r s hu

def Hurewicz.CubeGluing.coherentCubeEndpoint {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (H₀ : C(SingularChains.Simplex n, X) → C((unitInterval) × SingularChains.Simplex n, X))
    (H₁ :
      C(SingularChains.Simplex (n + 1), X) → C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H₀ H₁)
    (hconst :
      H₀ (ContinuousMap.const (SingularChains.Simplex n) x) =
        ContinuousMap.const ((unitInterval) × SingularChains.Simplex n) x)
    (p : GenLoop (Fin (n + 1)) X x) : GenLoop (Fin (n + 1)) X x :=
  ⟨SecondHurewicz.SimplyConnected.timeSlice (coherentCubeHomotopyMap H₀ H₁ hface p) 1, fun u hu =>
    coherentCubeHomotopyMap_boundary H₀ H₁ hface hconst p 1 u hu⟩

theorem Hurewicz.CubeGluing.coherentCubeEndpoint_cell {n : ℕ} {X : Type}
    [TopologicalSpace X] {x : X}
    (H₀ : C(SingularChains.Simplex n, X) → C((unitInterval) × SingularChains.Simplex n, X))
    (H₁ :
      C(SingularChains.Simplex (n + 1), X) → C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H₀ H₁)
    (hconst :
      H₀ (ContinuousMap.const (SingularChains.Simplex n) x) =
        ContinuousMap.const ((unitInterval) × SingularChains.Simplex n) x)
    (p : GenLoop (Fin (n + 1)) X x) (e : Equiv.Perm (Fin (n + 1))) :
    (coherentCubeEndpoint H₀ H₁ hface hconst p).val.comp
        (Hurewicz.CubeTriangulation.cubeSimplex e) =
      SecondHurewicz.SimplyConnected.timeSlice
        (H₁ (p.val.comp (Hurewicz.CubeTriangulation.cubeSimplex e))) 1 := by
  ext s
  exact coherentCubeHomotopyMap_cell H₀ H₁ hface p e 1 s

def Hurewicz.CubeGluing.coherentCubeHomotopy {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (H₀ : C(SingularChains.Simplex n, X) → C((unitInterval) × SingularChains.Simplex n, X))
    (H₁ :
      C(SingularChains.Simplex (n + 1), X) → C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H₀ H₁)
    (hconst :
      H₀ (ContinuousMap.const (SingularChains.Simplex n) x) =
        ContinuousMap.const ((unitInterval) × SingularChains.Simplex n) x)
    (hzero :
      ∀ (smp : C(SingularChains.Simplex (n + 1), X)) (s : SingularChains.Simplex (n + 1)),
        H₁ smp (0, s) = smp s)
    (p : GenLoop (Fin (n + 1)) X x) :
    p.val.HomotopyRel (coherentCubeEndpoint H₀ H₁ hface hconst p).val
      (Cube.boundary (Fin (n + 1)))
    where
  toHomotopy :=
    { toContinuousMap := coherentCubeHomotopyMap H₀ H₁ hface p
      map_zero_left := coherentCubeHomotopyMap_zero H₀ H₁ hface hzero p
      map_one_left _ := rfl }
  prop' r u
    hu :=
    (coherentCubeHomotopyMap_boundary H₀ H₁ hface hconst p r u hu).trans
      (GenLoop.boundary p u hu).symm

end Mathoverflow1973
