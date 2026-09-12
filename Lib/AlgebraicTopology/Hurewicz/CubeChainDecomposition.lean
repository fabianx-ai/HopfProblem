/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.CubeTriangulation
import Lib.AlgebraicTopology.Hurewicz.PrismOperator

set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

noncomputable section

namespace Mathoverflow1973

theorem FourthHurewicz.CubeSubdivision.signed_sum_eq_zero_of_swap_invariant {n : ℕ} {A : Type*}
    [AddCommGroup A] (i j : Fin n) (hij : i ≠ j) (f : Equiv.Perm (Fin n) → A)
    (hf : ∀ e, f ((Equiv.swap i j).trans e) = f e) :
    ∑ e, HigherHurewicz.CubeTriangulation.cubeOrientation e • f e = 0 := by
  classical
  apply Finset.sum_ninvolution (fun e => (Equiv.swap i j).trans e)
  · intro e
    rw [HigherHurewicz.CubeTriangulation.cubeOrientation_swap e hij, hf, neg_smul, add_neg_cancel]
  · intro e _ he
    have h := congrArg (fun k : Equiv.Perm (Fin n) => k i) he
    have h' : e j = e i := by simpa using h
    exact hij (e.injective h').symm
  · intro e
    exact Finset.mem_univ _
  · intro e
    ext k
    simp

theorem FourthHurewicz.CubeSubdivision.signed_sum_constant_eq_zero {n : ℕ} [Nontrivial (Fin n)]
    {A : Type*} [AddCommGroup A] (a : A) :
    ∑ e : Equiv.Perm (Fin n), HigherHurewicz.CubeTriangulation.cubeOrientation e • a = 0 := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne (Fin n)
  exact signed_sum_eq_zero_of_swap_invariant i j hij (fun _ => a) (fun _ => rfl)

def FourthHurewicz.CubeSubdivision.prismCubeVertex {n : ℕ} (e : Equiv.Perm (Fin n))
    (z : Fin 2 × Fin (n + 1)) : HigherHurewicz.CubeTriangulation.CubeN (n + 1) :=
  Fin.cases (SingularChains.pathSimplex Path.id (SingularMayerVietoris.stdVertices 1 z.1))
    (HigherHurewicz.CubeTriangulation.cubeVertex e z.2)

@[simp]
theorem FourthHurewicz.CubeSubdivision.prismCubeVertex_succ {n : ℕ} (e : Equiv.Perm (Fin n))
    (z : Fin 2 × Fin (n + 1)) (i : Fin n) :
    prismCubeVertex e z i.succ = HigherHurewicz.CubeTriangulation.cubeVertex e z.2 i :=
  rfl

def FourthHurewicz.CubeSubdivision.prismCubeSimplex {m n : ℕ} (e : Equiv.Perm (Fin n))
    (v : Fin (m + 1) → Fin 2 × Fin (n + 1)) :
    C(SingularChains.Simplex m, HigherHurewicz.CubeTriangulation.CubeN (n + 1)) :=
  HigherHurewicz.CubeTriangulation.cubeAffineSimplex (fun j => prismCubeVertex e (v j))

theorem FourthHurewicz.CubeSubdivision.prismCubeVertex_swap_of_ne {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (i : Fin n) (z : Fin 2 × Fin (n + 2))
    (hz : z.2 ≠ i.succ.castSucc) :
    prismCubeVertex e z = prismCubeVertex ((Equiv.swap i.castSucc i.succ).trans e) z := by
  funext coord
  refine Fin.cases ?_ (fun k => ?_) coord
  · rfl
  · exact congrFun (HigherHurewicz.CubeTriangulation.cubeVertex_swap_of_ne e i z.2 hz) k

theorem FourthHurewicz.CubeSubdivision.prismCubeSimplex_swap_of_omitted {m n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (i : Fin n) (v : Fin (m + 1) → Fin 2 × Fin (n + 2))
    (hv : ∀ j, (v j).2 ≠ i.succ.castSucc) :
    prismCubeSimplex e v = prismCubeSimplex ((Equiv.swap i.castSucc i.succ).trans e) v := by
  apply congrArg HigherHurewicz.CubeTriangulation.cubeAffineSimplex
  funext j
  exact prismCubeVertex_swap_of_ne e i (v j) (hv j)

theorem FourthHurewicz.CubeSubdivision.prismCubeSimplex_zero_of_left_zero {m n : ℕ}
    (e : Equiv.Perm (Fin n)) (v : Fin (m + 1) → Fin 2 × Fin (n + 1)) (hv : ∀ j, (v j).1 = 0)
    (s : SingularChains.Simplex m) : prismCubeSimplex e v s 0 = 0 := by
  apply HigherHurewicz.CubeTriangulation.cubeAffineSimplex_constant_coordinate
  intro j
  simp [prismCubeVertex, hv j, SingularMayerVietoris.stdVertices]

theorem FourthHurewicz.CubeSubdivision.prismCubeSimplex_zero_of_last_omitted {m n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (v : Fin (m + 1) → Fin 2 × Fin (n + 2))
    (hv : ∀ j, (v j).2 ≠ Fin.last (n + 1)) (s : SingularChains.Simplex m) :
    prismCubeSimplex e v s (e (Fin.last n)).succ = 0 := by
  apply HigherHurewicz.CubeTriangulation.cubeAffineSimplex_constant_coordinate
  intro j
  simp only [prismCubeVertex_succ, HigherHurewicz.CubeTriangulation.cubeVertex,
    Equiv.symm_apply_apply, Fin.val_last]
  apply if_neg
  have hne : (v j).2.val ≠ n + 1 := by
    intro h
    exact hv j (Fin.ext h)
  have hlt := (v j).2.isLt
  omega

def FourthHurewicz.CubeSubdivision.prismCubeRealization {X : Type} [TopologicalSpace X] {n : ℕ}
    (p : C(HigherHurewicz.CubeTriangulation.CubeN (n + 1), X)) (e : Equiv.Perm (Fin n)) (m : ℕ) :
    SingularMayerVietoris.FormalChains (Fin 2 × Fin (n + 1)) (m + 1) →ₗ[ℤ]
      SingularChains.Chains X m :=
  SingularMayerVietoris.formalLift fun v =>
    SingularChains.simplexChain X m (p.comp (prismCubeSimplex e v))

@[simp]
theorem FourthHurewicz.CubeSubdivision.prismCubeRealization_simplex {X : Type}
    [TopologicalSpace X] {n : ℕ} (p : C(HigherHurewicz.CubeTriangulation.CubeN (n + 1), X))
    (e : Equiv.Perm (Fin n)) (m : ℕ) (v : Fin (m + 1) → Fin 2 × Fin (n + 1)) :
    prismCubeRealization p e m (SingularMayerVietoris.formalSimplex v) =
      SingularChains.simplexChain X m (p.comp (prismCubeSimplex e v)) :=
  SingularMayerVietoris.formalLift_simplex _ _

def FourthHurewicz.CubeSubdivision.orientedPrismRealization {X : Type} [TopologicalSpace X]
    {n : ℕ} (p : C(HigherHurewicz.CubeTriangulation.CubeN (n + 1), X)) (m : ℕ) :
    SingularMayerVietoris.FormalChains (Fin 2 × Fin (n + 1)) (m + 1) →ₗ[ℤ]
      SingularChains.Chains X m :=
  SingularMayerVietoris.formalLift fun v =>
    ∑ e : Equiv.Perm (Fin n),
      HigherHurewicz.CubeTriangulation.cubeOrientation e •
        SingularChains.simplexChain X m (p.comp (prismCubeSimplex e v))

@[simp]
theorem FourthHurewicz.CubeSubdivision.orientedPrismRealization_simplex {X : Type}
    [TopologicalSpace X] {n : ℕ} (p : C(HigherHurewicz.CubeTriangulation.CubeN (n + 1), X))
    (m : ℕ) (v : Fin (m + 1) → Fin 2 × Fin (n + 1)) :
    orientedPrismRealization p m (SingularMayerVietoris.formalSimplex v) =
      ∑ e : Equiv.Perm (Fin n),
        HigherHurewicz.CubeTriangulation.cubeOrientation e •
          SingularChains.simplexChain X m (p.comp (prismCubeSimplex e v)) :=
  SingularMayerVietoris.formalLift_simplex _ _

def FourthHurewicz.CubeSubdivision.evalLeft (X : Type) [TopologicalSpace X] :
    C((unitInterval) × C((unitInterval), X), X)
    where
  toFun z := z.2 z.1
  continuous_toFun := by fun_prop

theorem FourthHurewicz.CubeSubdivision.cubeAffineSimplex_comp {k m n : ℕ}
    (v : Fin (n + 1) → HigherHurewicz.CubeTriangulation.CubeN k)
    (w : Fin (m + 1) → SingularChains.Simplex n) :
    (HigherHurewicz.CubeTriangulation.cubeAffineSimplex v).comp
        (SingularMayerVietoris.affineSimplex w) =
      HigherHurewicz.CubeTriangulation.cubeAffineSimplex
        (fun j => HigherHurewicz.CubeTriangulation.cubeAffineSimplex v (w j)) := by
  ext t i
  change
    (HigherHurewicz.CubeTriangulation.cubeAffineSimplex v
          (SingularMayerVietoris.affineSimplex w t) i :
        ℝ) =
      (HigherHurewicz.CubeTriangulation.cubeAffineSimplex
          (fun j => HigherHurewicz.CubeTriangulation.cubeAffineSimplex v (w j)) t i :
        ℝ)
  simp only [HigherHurewicz.CubeTriangulation.cubeAffineSimplex_coordinate,
    SingularMayerVietoris.affineSimplex_coordinate, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem FourthHurewicz.CubeSubdivision.cubeAffineSimplex_comp_selectedVertices {k m n : ℕ}
    (v : Fin (n + 1) → HigherHurewicz.CubeTriangulation.CubeN k) (a : Fin (m + 1) → Fin (n + 1)) :
    (HigherHurewicz.CubeTriangulation.cubeAffineSimplex v).comp
        (SingularMayerVietoris.affineSimplex
          (fun j => SingularMayerVietoris.stdVertices n (a j))) =
      HigherHurewicz.CubeTriangulation.cubeAffineSimplex (fun j => v (a j)) := by
  rw [cubeAffineSimplex_comp]
  simp only [HigherHurewicz.CubeTriangulation.cubeAffineSimplex_vertex]

def FourthHurewicz.CubeSubdivision.prismCubeMap {n : ℕ} (e : Equiv.Perm (Fin n)) :
    C(SingularChains.Simplex 1 × SingularChains.Simplex n,
      HigherHurewicz.CubeTriangulation.CubeN (n + 1))
    where
  toFun
    z :=
    Fin.cases (SingularChains.pathSimplex Path.id z.1)
      (HigherHurewicz.CubeTriangulation.cubeSimplex e z.2)
  continuous_toFun := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (SingularChains.pathSimplex Path.id).continuous.comp continuous_fst
    · exact
        (continuous_apply j).comp
          ((HigherHurewicz.CubeTriangulation.cubeSimplex e).continuous.comp continuous_snd)

theorem FourthHurewicz.CubeSubdivision.prismCubeMap_affine {m n : ℕ} (e : Equiv.Perm (Fin n))
    (v : Fin (m + 1) → Fin 2 × Fin (n + 1)) :
    (prismCubeMap e).comp
        (PeriodTorusHigherHomology.productAffineSimplex
          (fun j =>
            (SingularMayerVietoris.stdVertices 1 (v j).1,
              SingularMayerVietoris.stdVertices n (v j).2))) =
      prismCubeSimplex e v := by
  apply ContinuousMap.ext
  intro t
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · apply Subtype.ext
    change
      SingularMayerVietoris.affineSimplex (fun j => SingularMayerVietoris.stdVertices 1 (v j).1) t
          1 =
        ∑ j, t j * SingularMayerVietoris.stdVertices 1 (v j).1 1
    exact SingularMayerVietoris.affineSimplex_coordinate _ _ _
  · change
      ((HigherHurewicz.CubeTriangulation.cubeAffineSimplex
                (HigherHurewicz.CubeTriangulation.cubeVertex e)).comp
            (SingularMayerVietoris.affineSimplex
              (fun j => SingularMayerVietoris.stdVertices n (v j).2)))
          t k =
        _
    rw [cubeAffineSimplex_comp_selectedVertices]
    rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FourthHurewicz.CubeSubdivision.prismCubeRealization_eq_induced {X : Type}
    [TopologicalSpace X] {n : ℕ} (p : C(HigherHurewicz.CubeTriangulation.CubeN (n + 1), X))
    (e : Equiv.Perm (Fin n)) (m : ℕ) :
    prismCubeRealization p e m =
      (SingularChains.inducedChain (p.comp (prismCubeMap e)) m).comp
        ((PeriodTorusHigherHomology.productAffineChainMap 1 n m).comp
          (SingularMayerVietoris.formalMap
            (Prod.map (SingularMayerVietoris.stdVertices 1) (SingularMayerVietoris.stdVertices n))
            (m + 1))) := by
  apply SingularMayerVietoris.formalChains_ext
  intro v
  simp only [prismCubeRealization_simplex, LinearMap.comp_apply,
    SingularMayerVietoris.formalMap_simplex,
    PeriodTorusHigherHomology.productAffineChainMap_simplex, SingularChains.inducedChain_simplex]
  apply congrArg (SingularChains.simplexChain X m)
  change
    p.comp (prismCubeSimplex e v) =
      p.comp
        ((prismCubeMap e).comp
          (PeriodTorusHigherHomology.productAffineSimplex
            (fun j =>
              (SingularMayerVietoris.stdVertices 1 (v j).1,
                SingularMayerVietoris.stdVertices n (v j).2))))
  rw [prismCubeMap_affine]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FourthHurewicz.CubeSubdivision.prismCubeRealization_edgeCrossProduct {X : Type}
    [TopologicalSpace X] {n : ℕ} (p : C(HigherHurewicz.CubeTriangulation.CubeN (n + 1), X))
    (e : Equiv.Perm (Fin n)) :
    prismCubeRealization p e (n + 1)
        (PeriodTorusHigherHomology.formalEdgeCrossProduct n
          (SingularMayerVietoris.formalSimplex (fun i : Fin 2 => i))
          (SingularMayerVietoris.formalSimplex (fun j : Fin (n + 1) => j))) =
      SingularChains.inducedChain (p.comp (prismCubeMap e)) (n + 1)
        (PeriodTorusHigherHomology.productAffineChainMap 1 n (n + 1)
          (PeriodTorusHigherHomology.formalEdgeCrossProduct n
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) := by
  rw [prismCubeRealization_eq_induced]
  simp only [LinearMap.comp_apply]
  rw [PeriodTorusHigherHomology.formalMap_edgeCrossProduct]
  simp only [SingularMayerVietoris.formalMap_simplex, Function.comp_def]

def FourthHurewicz.CubeSubdivision.badPrism (q m : ℕ) :
    Submodule ℤ (SingularMayerVietoris.FormalChains (Fin 2 × Fin (q + 1)) m) :=
  SingularMayerVietoris.formalChainsSupported {z | z.1 = 0} m ⊔
    ⨆ i : { i : Fin (q + 1) // i ≠ 0 },
      SingularMayerVietoris.formalChainsSupported {z | z.2 ≠ i.val} m

theorem FourthHurewicz.CubeSubdivision.mem_badPrism_of_left_zero {q m : ℕ}
    {c : SingularMayerVietoris.FormalChains (Fin 2 × Fin (q + 1)) m}
    (hc : c ∈ SingularMayerVietoris.formalChainsSupported {z | z.1 = 0} m) : c ∈ badPrism q m :=
  Submodule.mem_sup_left hc

theorem FourthHurewicz.CubeSubdivision.mem_badPrism_of_omit {q m : ℕ} (i : Fin (q + 1))
    (hi : i ≠ 0) {c : SingularMayerVietoris.FormalChains (Fin 2 × Fin (q + 1)) m}
    (hc : c ∈ SingularMayerVietoris.formalChainsSupported {z | z.2 ≠ i} m) : c ∈ badPrism q m :=
  Submodule.mem_sup_right (Submodule.mem_iSup_of_mem ⟨i, hi⟩ hc)

theorem FourthHurewicz.CubeSubdivision.badPrism_le {q m : ℕ}
    {P : Submodule ℤ (SingularMayerVietoris.FormalChains (Fin 2 × Fin (q + 1)) m)}
    (hzero : SingularMayerVietoris.formalChainsSupported {z | z.1 = 0} m ≤ P)
    (homit :
      ∀ i : Fin (q + 1),
        i ≠ 0 → SingularMayerVietoris.formalChainsSupported {z | z.2 ≠ i} m ≤ P) :
    badPrism q m ≤ P :=
  sup_le hzero (iSup_le fun i => homit i.val i.property)

theorem FourthHurewicz.CubeSubdivision.badPrism_le_ker {q m : ℕ} {M : Type*} [AddCommGroup M]
    [Module ℤ M] (f : SingularMayerVietoris.FormalChains (Fin 2 × Fin (q + 1)) m →ₗ[ℤ] M)
    (hzero : ∀ v, (∀ j, (v j).1 = 0) → f (SingularMayerVietoris.formalSimplex v) = 0)
    (homit :
      ∀ i : Fin (q + 1),
        i ≠ 0 → ∀ v, (∀ j, (v j).2 ≠ i) → f (SingularMayerVietoris.formalSimplex v) = 0) :
    badPrism q m ≤ LinearMap.ker f := by
  apply badPrism_le
  · exact SingularMayerVietoris.formalChainsSupported_le hzero
  · intro i hi
    exact SingularMayerVietoris.formalChainsSupported_le (homit i hi)

theorem FourthHurewicz.CubeSubdivision.formalCone_mem_badPrism {q m : ℕ}
    {c : SingularMayerVietoris.FormalChains (Fin 2 × Fin (q + 1)) m} (hc : c ∈ badPrism q m) :
    SingularMayerVietoris.formalCone (0, 0) m c ∈ badPrism q (m + 1) := by
  have hle :
    badPrism q m ≤ (badPrism q (m + 1)).comap (SingularMayerVietoris.formalCone (0, 0) m) := by
    apply badPrism_le
    · intro d hd
      exact
        mem_badPrism_of_left_zero
          (SingularMayerVietoris.formalCone_mem_supported (S :=
            {z : Fin 2 × Fin (q + 1) | z.1 = 0}) (a := (0, 0)) rfl hd)
    · intro i hi d hd
      exact
        mem_badPrism_of_omit i hi (SingularMayerVietoris.formalCone_mem_supported (Ne.symm hi) hd)
  exact hle hc

theorem FourthHurewicz.CubeSubdivision.formalMap_succ_mem_badPrism {q m : ℕ}
    {c : SingularMayerVietoris.FormalChains (Fin 2 × Fin (q + 1)) m} (hc : c ∈ badPrism q m) :
    SingularMayerVietoris.formalMap (Prod.map id (Fin.succ : Fin (q + 1) → Fin (q + 2))) m c ∈
      badPrism (q + 1) m := by
  have hle :
    badPrism q m ≤
      (badPrism (q + 1) m).comap
        (SingularMayerVietoris.formalMap (Prod.map id (Fin.succ : Fin (q + 1) → Fin (q + 2)))
          m) := by
    apply badPrism_le
    · intro d hd
      apply mem_badPrism_of_left_zero
      exact
        SingularMayerVietoris.formalMap_mem_supported (S := {z : Fin 2 × Fin (q + 1) | z.1 = 0})
          (T := {z : Fin 2 × Fin (q + 2) | z.1 = 0}) (Prod.map id Fin.succ) (fun _ hz => hz) hd
    · intro i hi d hd
      apply mem_badPrism_of_omit i.succ (Fin.succ_ne_zero i)
      exact
        SingularMayerVietoris.formalMap_mem_supported (S := {z : Fin 2 × Fin (q + 1) | z.2 ≠ i})
          (T := {z : Fin 2 × Fin (q + 2) | z.2 ≠ i.succ}) (Prod.map id Fin.succ)
          (fun _ hz h => hz (Fin.succ_injective _ h)) hd
  exact hle hc

theorem FourthHurewicz.CubeSubdivision.formalEdgeCrossProduct_mem_badPrism_of_omit {q r : ℕ}
    (i : Fin (q + 1)) (hi : i ≠ 0) (c : SingularMayerVietoris.FormalChains (Fin 2) 2)
    {d : SingularMayerVietoris.FormalChains (Fin (q + 1)) (r + 1)}
    (hd : d ∈ SingularMayerVietoris.formalChainsSupported {j | j ≠ i} (r + 1)) :
    PeriodTorusHigherHomology.formalEdgeCrossProduct r c d ∈ badPrism q (r + 2) := by
  apply mem_badPrism_of_omit i hi
  apply
    SingularMayerVietoris.formalChainsSupported_mono (S :=
      (Set.univ : Set (Fin 2)) ×ˢ {j : Fin (q + 1) | j ≠ i}) (fun _ hz => hz.2)
  exact
    PeriodTorusHigherHomology.formalEdgeCrossProduct_mem_supported r (S := Set.univ) (by simp) hd

def FourthHurewicz.CubeSubdivision.retainedFirstBoundary {W : Type*} (q : ℕ) :
    SingularMayerVietoris.FormalChains W (q + 2) →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W (q + 1) :=
  SingularMayerVietoris.formalLift fun w =>
    ∑ i : Fin (q + 1),
      (-1 : ℤ) ^ (i.val + 1) • SingularMayerVietoris.formalSimplex (w ∘ i.succ.succAbove)

@[simp]
theorem FourthHurewicz.CubeSubdivision.retainedFirstBoundary_simplex {W : Type*} (q : ℕ)
    (w : Fin (q + 2) → W) :
    retainedFirstBoundary q (SingularMayerVietoris.formalSimplex w) =
      ∑ i : Fin (q + 1),
        (-1 : ℤ) ^ (i.val + 1) • SingularMayerVietoris.formalSimplex (w ∘ i.succ.succAbove) :=
  SingularMayerVietoris.formalLift_simplex _ _

theorem FourthHurewicz.CubeSubdivision.formalBoundary_firstFace_split_simplex {W : Type*} (q : ℕ)
    (w : Fin (q + 2) → W) :
    SingularMayerVietoris.formalBoundary (q + 1) (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalSimplex (Fin.tail w) +
        retainedFirstBoundary q (SingularMayerVietoris.formalSimplex w) := by
  rw [SingularMayerVietoris.formalBoundary_simplex, Fin.sum_univ_succ,
    retainedFirstBoundary_simplex]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, Fin.succAbove_zero]
  rfl

def FourthHurewicz.CubeSubdivision.shufflePrismVertices {V W : Type*} {q : ℕ} (v : Fin 2 → V)
    (w : Fin (q + 1) → W) (i : Fin (q + 1)) : Fin (q + 2) → V × W := fun k =>
  (if k ≤ i.castSucc then v 0 else v 1, w (i.predAbove k))

@[simp]
theorem FourthHurewicz.CubeSubdivision.shufflePrismVertices_first {V W : Type*} {q : ℕ}
    (v : Fin 2 → V) (w : Fin (q + 1) → W) (i : Fin (q + 1)) :
    shufflePrismVertices v w i 0 = (v 0, w 0) := by simp [shufflePrismVertices]

theorem FourthHurewicz.CubeSubdivision.shufflePrismVertices_zero_index {V W : Type*} {q : ℕ}
    (v : Fin 2 → V) (w : Fin (q + 1) → W) :
    shufflePrismVertices v w 0 = Fin.cons (v 0, w 0) (fun j => (v 1, w j)) := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp
  · simp [shufflePrismVertices]

theorem FourthHurewicz.CubeSubdivision.shufflePrismVertices_succ_index {V W : Type*} {q : ℕ}
    (v : Fin 2 → V) (w : Fin (q + 2) → W) (i : Fin (q + 1)) :
    shufflePrismVertices v w i.succ =
      Fin.cons (v 0, w 0) (shufflePrismVertices v (Fin.tail w) i) := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp
  · simp [shufflePrismVertices, Fin.tail, Fin.le_castSucc_iff]

theorem FourthHurewicz.CubeSubdivision.shufflePrismVertices_map {V W V' W' : Type*} {q : ℕ}
    (f : V → V') (g : W → W') (v : Fin 2 → V) (w : Fin (q + 1) → W) (i : Fin (q + 1)) :
    Prod.map f g ∘ shufflePrismVertices v w i = shufflePrismVertices (f ∘ v) (g ∘ w) i := by
  funext k
  simp only [shufflePrismVertices, Function.comp_apply, Prod.map_apply]
  split_ifs <;> rfl

def FourthHurewicz.CubeSubdivision.standardPrism {V W : Type*} (q : ℕ) (v : Fin 2 → V)
    (w : Fin (q + 1) → W) : SingularMayerVietoris.FormalChains (V × W) (q + 2) :=
  ∑ i : Fin (q + 1),
    (-1 : ℤ) ^ i.val • SingularMayerVietoris.formalSimplex (shufflePrismVertices v w i)

theorem FourthHurewicz.CubeSubdivision.standardPrism_zero {V W : Type*} (v : Fin 2 → V)
    (w : Fin 1 → W) :
    standardPrism 0 v w = SingularMayerVietoris.formalSimplex (fun i => (v i, w 0)) := by
  rw [standardPrism, Fin.sum_univ_one]
  simp only [Fin.val_zero, pow_zero, one_smul, shufflePrismVertices_zero_index]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rw [Fin.eq_zero j]
    rfl

theorem FourthHurewicz.CubeSubdivision.standardPrism_succ {V W : Type*} (q : ℕ) (v : Fin 2 → V)
    (w : Fin (q + 2) → W) :
    standardPrism (q + 1) v w =
      SingularMayerVietoris.formalCone (v 0, w 0) (q + 2)
        (SingularMayerVietoris.formalMap (fun z => (v 1, z)) (q + 2)
            (SingularMayerVietoris.formalSimplex w) -
          standardPrism q v (Fin.tail w)) := by
  rw [standardPrism, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, shufflePrismVertices_zero_index, map_sub,
    SingularMayerVietoris.formalMap_simplex, SingularMayerVietoris.formalCone_simplex,
    standardPrism, map_sum, map_smul, SingularMayerVietoris.formalCone_simplex]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Fin.val_succ, pow_succ, mul_neg_one, neg_smul, shufflePrismVertices_succ_index]

theorem FourthHurewicz.CubeSubdivision.formalMap_standardPrism {V W V' W' : Type*} (f : V → V')
    (g : W → W') (q : ℕ) (v : Fin 2 → V) (w : Fin (q + 1) → W) :
    SingularMayerVietoris.formalMap (Prod.map f g) (q + 2) (standardPrism q v w) =
      standardPrism q (f ∘ v) (g ∘ w) := by
  simp only [standardPrism, map_sum, map_smul, SingularMayerVietoris.formalMap_simplex,
    shufflePrismVertices_map]

def FourthHurewicz.CubeSubdivision.prismDiscrepancy {V W : Type*} (q : ℕ) (v : Fin 2 → V)
    (w : Fin (q + 1) → W) : SingularMayerVietoris.FormalChains (V × W) (q + 2) :=
  PeriodTorusHigherHomology.formalEdgeCrossProduct q (SingularMayerVietoris.formalSimplex v)
      (SingularMayerVietoris.formalSimplex w) -
    standardPrism q v w

@[simp]
theorem FourthHurewicz.CubeSubdivision.prismDiscrepancy_zero {V W : Type*} (v : Fin 2 → V)
    (w : Fin 1 → W) : prismDiscrepancy 0 v w = 0 := by
  simp only [prismDiscrepancy,
    PeriodTorusHigherHomology.formalEdgeCrossProduct_zero_simplex_right,
    SingularMayerVietoris.formalMap_simplex, standardPrism_zero, Function.comp_def, sub_self]

theorem FourthHurewicz.CubeSubdivision.formalMap_prismDiscrepancy {V W V' W' : Type*} (f : V → V')
    (g : W → W') (q : ℕ) (v : Fin 2 → V) (w : Fin (q + 1) → W) :
    SingularMayerVietoris.formalMap (Prod.map f g) (q + 2) (prismDiscrepancy q v w) =
      prismDiscrepancy q (f ∘ v) (g ∘ w) := by
  simp only [prismDiscrepancy, map_sub, PeriodTorusHigherHomology.formalMap_edgeCrossProduct,
    formalMap_standardPrism, SingularMayerVietoris.formalMap_simplex]

def FourthHurewicz.CubeSubdivision.canonicalPrismDiscrepancy (q : ℕ) :
    SingularMayerVietoris.FormalChains (Fin 2 × Fin (q + 1)) (q + 2) :=
  prismDiscrepancy q (fun i => i) (fun j => j)

@[simp]
theorem FourthHurewicz.CubeSubdivision.canonicalPrismDiscrepancy_zero :
    canonicalPrismDiscrepancy 0 = 0 :=
  prismDiscrepancy_zero _ _

theorem FourthHurewicz.CubeSubdivision.prismDiscrepancy_eq_map_canonical {V W : Type*} (q : ℕ)
    (v : Fin 2 → V) (w : Fin (q + 1) → W) :
    prismDiscrepancy q v w =
      SingularMayerVietoris.formalMap (Prod.map v w) (q + 2) (canonicalPrismDiscrepancy q) := by
  simpa only [canonicalPrismDiscrepancy, Function.comp_def] using
    (formalMap_prismDiscrepancy v w q (fun i => i) (fun j => j)).symm

theorem FourthHurewicz.CubeSubdivision.prismDiscrepancy_succ {V W : Type*} (q : ℕ) (v : Fin 2 → V)
    (w : Fin (q + 2) → W) :
    prismDiscrepancy (q + 1) v w =
      SingularMayerVietoris.formalCone (v 0, w 0) (q + 2)
        (-SingularMayerVietoris.formalMap (fun z => (v 0, z)) (q + 2)
                (SingularMayerVietoris.formalSimplex w) -
            PeriodTorusHigherHomology.formalEdgeCrossProduct q
              (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalBoundary (q + 1)
                (SingularMayerVietoris.formalSimplex w)) +
          standardPrism q v (Fin.tail w)) := by
  rw [prismDiscrepancy, PeriodTorusHigherHomology.formalEdgeCrossProduct_simplex_succ,
    PeriodTorusHigherHomology.formalPointCrossProduct_edge_boundary, standardPrism_succ]
  simp only [map_sub, map_add, map_neg]
  abel

theorem FourthHurewicz.CubeSubdivision.prismDiscrepancy_succ_retained {V W : Type*} (q : ℕ)
    (v : Fin 2 → V) (w : Fin (q + 2) → W) :
    prismDiscrepancy (q + 1) v w =
      SingularMayerVietoris.formalCone (v 0, w 0) (q + 2)
        (-SingularMayerVietoris.formalMap (fun z => (v 0, z)) (q + 2)
                (SingularMayerVietoris.formalSimplex w) -
            prismDiscrepancy q v (Fin.tail w) -
          PeriodTorusHigherHomology.formalEdgeCrossProduct q
            (SingularMayerVietoris.formalSimplex v)
            (retainedFirstBoundary q (SingularMayerVietoris.formalSimplex w))) := by
  rw [prismDiscrepancy_succ, formalBoundary_firstFace_split_simplex, map_add, prismDiscrepancy]
  simp only [map_sub, map_add, map_neg]
  abel

theorem FourthHurewicz.CubeSubdivision.canonicalPrismDiscrepancy_succ (q : ℕ) :
    canonicalPrismDiscrepancy (q + 1) =
      SingularMayerVietoris.formalCone ((0 : Fin 2), (0 : Fin (q + 2))) (q + 2)
        (-SingularMayerVietoris.formalSimplex (fun j : Fin (q + 2) => ((0 : Fin 2), j)) -
            SingularMayerVietoris.formalMap (Prod.map (fun i : Fin 2 => i) Fin.succ) (q + 2)
              (canonicalPrismDiscrepancy q) -
          ∑ i : Fin (q + 1),
            (-1 : ℤ) ^ (i.val + 1) •
              PeriodTorusHigherHomology.formalEdgeCrossProduct q
                (SingularMayerVietoris.formalSimplex (fun j : Fin 2 => j))
                (SingularMayerVietoris.formalSimplex i.succ.succAbove)) := by
  change prismDiscrepancy (q + 1) (fun i : Fin 2 => i) (fun j : Fin (q + 2) => j) = _
  rw [prismDiscrepancy_succ_retained, prismDiscrepancy_eq_map_canonical]
  simp only [retainedFirstBoundary_simplex, map_sum, map_smul,
    SingularMayerVietoris.formalMap_simplex, Function.comp_def]
  rfl

theorem FourthHurewicz.CubeSubdivision.canonicalPrismDiscrepancy_mem_badPrism (q : ℕ) :
    canonicalPrismDiscrepancy q ∈ badPrism q (q + 2) := by
  induction q with
  | zero =>
    rw [canonicalPrismDiscrepancy_zero]
    exact Submodule.zero_mem _
  | succ q ih =>
    rw [canonicalPrismDiscrepancy_succ]
    apply formalCone_mem_badPrism
    apply Submodule.sub_mem
    · apply Submodule.sub_mem
      · apply Submodule.neg_mem
        exact
          mem_badPrism_of_left_zero
            (SingularMayerVietoris.formalSimplex_mem_supported fun _ => rfl)
      · exact formalMap_succ_mem_badPrism ih
    · apply Submodule.sum_mem
      intro i hi
      apply Submodule.smul_mem
      exact
        formalEdgeCrossProduct_mem_badPrism_of_omit i.succ (Fin.succ_ne_zero i) _
          (SingularMayerVietoris.formalSimplex_mem_supported fun j => Fin.succAbove_ne i.succ j)

theorem FourthHurewicz.CubeSubdivision.orientedPrismRealization_left_zero {X : Type}
    [TopologicalSpace X] {x : X} {m n : ℕ} (p : GenLoop (Fin (n + 3)) X x)
    (v : Fin (m + 1) → Fin 2 × Fin (n + 3)) (hv : ∀ j, (v j).1 = 0) :
    orientedPrismRealization p.val m (SingularMayerVietoris.formalSimplex v) = 0 := by
  have hconst (e : Equiv.Perm (Fin (n + 2))) :
    p.val.comp (prismCubeSimplex e v) = ContinuousMap.const (SingularChains.Simplex m) x := by
    ext s
    exact GenLoop.boundary p _ ⟨0, Or.inl (prismCubeSimplex_zero_of_left_zero e v hv s)⟩
  simp only [orientedPrismRealization_simplex, hconst]
  exact signed_sum_constant_eq_zero _

theorem FourthHurewicz.CubeSubdivision.orientedPrismRealization_last_omitted {X : Type}
    [TopologicalSpace X] {x : X} {m n : ℕ} (p : GenLoop (Fin (n + 3)) X x)
    (v : Fin (m + 1) → Fin 2 × Fin (n + 3)) (hv : ∀ j, (v j).2 ≠ Fin.last (n + 2)) :
    orientedPrismRealization p.val m (SingularMayerVietoris.formalSimplex v) = 0 := by
  have hconst (e : Equiv.Perm (Fin (n + 2))) :
    p.val.comp (prismCubeSimplex e v) = ContinuousMap.const (SingularChains.Simplex m) x := by
    ext s
    exact
      GenLoop.boundary p _
        ⟨(e (Fin.last (n + 1))).succ, Or.inl (prismCubeSimplex_zero_of_last_omitted e v hv s)⟩
  simp only [orientedPrismRealization_simplex, hconst]
  exact signed_sum_constant_eq_zero _

theorem FourthHurewicz.CubeSubdivision.orientedPrismRealization_interior_omitted {X : Type}
    [TopologicalSpace X] {x : X} {m n : ℕ} (p : GenLoop (Fin (n + 3)) X x) (i : Fin (n + 1))
    (v : Fin (m + 1) → Fin 2 × Fin (n + 3)) (hv : ∀ j, (v j).2 ≠ i.succ.castSucc) :
    orientedPrismRealization p.val m (SingularMayerVietoris.formalSimplex v) = 0 := by
  rw [orientedPrismRealization_simplex]
  apply
    signed_sum_eq_zero_of_swap_invariant i.castSucc i.succ
      (by
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_castSucc, Fin.val_succ] at this
        omega)
  intro e
  exact
    congrArg (fun f => SingularChains.simplexChain X m (p.val.comp f))
      (prismCubeSimplex_swap_of_omitted e i v hv).symm

theorem FourthHurewicz.CubeSubdivision.orientedPrismRealization_nonzero_omitted {X : Type}
    [TopologicalSpace X] {x : X} {m n : ℕ} (p : GenLoop (Fin (n + 3)) X x) (i : Fin (n + 3))
    (hi : i ≠ 0) (v : Fin (m + 1) → Fin 2 × Fin (n + 3)) (hv : ∀ j, (v j).2 ≠ i) :
    orientedPrismRealization p.val m (SingularMayerVietoris.formalSimplex v) = 0 := by
  by_cases hlast : i = Fin.last (n + 2)
  · subst i
    exact orientedPrismRealization_last_omitted p v hv
  have hi0 : i.val ≠ 0 := by
    intro h
    exact hi (Fin.ext h)
  have hilast : i.val ≠ n + 2 := by
    intro h
    exact hlast (Fin.ext h)
  have hi_lt := i.isLt
  let j : Fin (n + 1) := ⟨i.val - 1, by omega⟩
  have hj : j.succ.castSucc = i := by
    apply Fin.ext
    dsimp [j]
    omega
  apply orientedPrismRealization_interior_omitted p j v
  simpa only [hj] using hv

theorem FourthHurewicz.CubeSubdivision.badPrism_le_ker_orientedPrismRealization {X : Type}
    [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin (n + 3)) X x) (m : ℕ) :
    badPrism (n + 2) (m + 1) ≤ LinearMap.ker (orientedPrismRealization p.val m) :=
  badPrism_le_ker _ (fun v hv => orientedPrismRealization_left_zero p v hv)
    (fun i hi v hv => orientedPrismRealization_nonzero_omitted p i hi v hv)

theorem FourthHurewicz.CubeSubdivision.orientedPrismRealization_canonicalPrismDiscrepancy
    {X : Type} [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin (n + 3)) X x) :
    orientedPrismRealization p.val (n + 3) (canonicalPrismDiscrepancy (n + 2)) = 0 :=
  badPrism_le_ker_orientedPrismRealization p (n + 3)
    (canonicalPrismDiscrepancy_mem_badPrism (n + 2))

theorem FourthHurewicz.CubeSubdivision.orientedPrismRealization_edge_eq_standard {X : Type}
    [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin (n + 3)) X x) :
    orientedPrismRealization p.val (n + 3)
        (PeriodTorusHigherHomology.formalEdgeCrossProduct (n + 2)
          (SingularMayerVietoris.formalSimplex (fun i : Fin 2 => i))
          (SingularMayerVietoris.formalSimplex (fun j : Fin (n + 3) => j))) =
      orientedPrismRealization p.val (n + 3)
        (standardPrism (n + 2) (fun i : Fin 2 => i) (fun j : Fin (n + 3) => j)) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact orientedPrismRealization_canonicalPrismDiscrepancy p

private theorem FourthHurewicz.CubeSubdivision.linearMap_zsmul_apply_mo1973_8057 {M N : Type*}
    [AddCommGroup M] [AddCommGroup N] [Module ℤ M] [Module ℤ N] (r : ℤ) (f : M →ₗ[ℤ] N) (a : M) :
    (r • f) a = r • f a :=
  map_zsmul (LinearMap.evalAddMonoidHom a) r f

theorem FourthHurewicz.CubeSubdivision.orientedPrismRealization_eq_sum {X : Type}
    [TopologicalSpace X] {n : ℕ} (p : C(HigherHurewicz.CubeTriangulation.CubeN (n + 1), X))
    (m : ℕ) (c : SingularMayerVietoris.FormalChains (Fin 2 × Fin (n + 1)) (m + 1)) :
    orientedPrismRealization p m c =
      ∑ e : Equiv.Perm (Fin n),
        HigherHurewicz.CubeTriangulation.cubeOrientation e • prismCubeRealization p e m c := by
  classical
  have h :
    orientedPrismRealization p m =
      ∑ e : Equiv.Perm (Fin n),
        HigherHurewicz.CubeTriangulation.cubeOrientation e • prismCubeRealization p e m := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    simp only [orientedPrismRealization_simplex, LinearMap.sum_apply,
      linearMap_zsmul_apply_mo1973_8057, prismCubeRealization_simplex]
  simpa only [LinearMap.sum_apply, linearMap_zsmul_apply_mo1973_8057] using
    LinearMap.congr_fun h c

def FourthHurewicz.CubeSubdivision.PermutationInsertion.insert {n : ℕ} (k : Fin (n + 1))
    (e : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.Perm.decomposeFin.symm (0, e) * k.cycleRange

@[simp]
theorem FourthHurewicz.CubeSubdivision.PermutationInsertion.insert_apply_self {n : ℕ}
    (k : Fin (n + 1)) (e : Equiv.Perm (Fin n)) :
    FourthHurewicz.CubeSubdivision.PermutationInsertion.insert k e k = 0 := by
  simp [FourthHurewicz.CubeSubdivision.PermutationInsertion.insert]

@[simp]
theorem FourthHurewicz.CubeSubdivision.PermutationInsertion.insert_apply_succAbove {n : ℕ}
    (k : Fin (n + 1)) (e : Equiv.Perm (Fin n)) (j : Fin n) :
    FourthHurewicz.CubeSubdivision.PermutationInsertion.insert k e (k.succAbove j) = (e j).succ :=
  by simp [FourthHurewicz.CubeSubdivision.PermutationInsertion.insert]

@[simp]
theorem FourthHurewicz.CubeSubdivision.PermutationInsertion.insert_symm_apply_zero {n : ℕ}
    (k : Fin (n + 1)) (e : Equiv.Perm (Fin n)) :
    (FourthHurewicz.CubeSubdivision.PermutationInsertion.insert k e).symm 0 = k := by
  apply (FourthHurewicz.CubeSubdivision.PermutationInsertion.insert k e).injective
  simp

@[simp]
theorem FourthHurewicz.CubeSubdivision.PermutationInsertion.insert_symm_apply_succ {n : ℕ}
    (k : Fin (n + 1)) (e : Equiv.Perm (Fin n)) (j : Fin n) :
    (FourthHurewicz.CubeSubdivision.PermutationInsertion.insert k e).symm j.succ =
      k.succAbove (e.symm j) := by
  apply (FourthHurewicz.CubeSubdivision.PermutationInsertion.insert k e).injective
  simp

@[simp]
theorem FourthHurewicz.CubeSubdivision.PermutationInsertion.sign_insert {n : ℕ} (k : Fin (n + 1))
    (e : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign (FourthHurewicz.CubeSubdivision.PermutationInsertion.insert k e) =
      (-1) ^ (k : ℕ) * Equiv.Perm.sign e := by
  simp [FourthHurewicz.CubeSubdivision.PermutationInsertion.insert, mul_comm]

theorem FourthHurewicz.CubeSubdivision.PermutationInsertion.sign_insert_int {n : ℕ}
    (k : Fin (n + 1)) (e : Equiv.Perm (Fin n)) :
    (Equiv.Perm.sign (FourthHurewicz.CubeSubdivision.PermutationInsertion.insert k e) : ℤ) =
      (-1 : ℤ) ^ (k : ℕ) * (Equiv.Perm.sign e : ℤ) := by simp

theorem FourthHurewicz.CubeSubdivision.lt_predAbove_iff_succAbove_lt {n : ℕ} (k : Fin (n + 1))
    (j : Fin n) (r : Fin (n + 2)) : j.val < (k.predAbove r).val ↔ (k.succAbove j).val < r.val := by
  simp only [Fin.succAbove, Fin.predAbove, Fin.lt_def, Fin.val_castSucc, apply_dite Fin.val,
    Fin.val_pred, Fin.coe_castPred, dite_eq_ite, apply_ite Fin.val, Fin.val_succ]
  split_ifs <;> omega

theorem FourthHurewicz.CubeSubdivision.prismCubeVertex_shuffle {n : ℕ} (e : Equiv.Perm (Fin n))
    (k : Fin (n + 1)) (r : Fin (n + 2)) :
    prismCubeVertex e (shufflePrismVertices (fun i : Fin 2 => i) (fun j : Fin (n + 1) => j) k r) =
      HigherHurewicz.CubeTriangulation.cubeVertex (PermutationInsertion.insert k e) r := by
  funext coord
  refine Fin.cases ?_ (fun j => ?_) coord
  · by_cases h : r ≤ k.castSucc
    · have h' : ¬k.val < r.val := by
        simpa only [prismCubeVertex, Fin.le_def, Fin.val_castSucc, not_lt] using h
      simp [prismCubeVertex, shufflePrismVertices, h, HigherHurewicz.CubeTriangulation.cubeVertex,
        h', SingularMayerVietoris.stdVertices]
    · have h' : k.val < r.val := by
        simpa only [prismCubeVertex, Fin.le_def, Fin.val_castSucc, not_le] using h
      simp [prismCubeVertex, shufflePrismVertices, h, HigherHurewicz.CubeTriangulation.cubeVertex,
        h', SingularMayerVietoris.stdVertices]
  · simp only [shufflePrismVertices, prismCubeVertex_succ,
      HigherHurewicz.CubeTriangulation.cubeVertex, PermutationInsertion.insert_symm_apply_succ]
    simp only [lt_predAbove_iff_succAbove_lt]

theorem FourthHurewicz.CubeSubdivision.prismCubeSimplex_shuffle {n : ℕ} (e : Equiv.Perm (Fin n))
    (k : Fin (n + 1)) :
    prismCubeSimplex e (shufflePrismVertices (fun i : Fin 2 => i) (fun j : Fin (n + 1) => j) k) =
      HigherHurewicz.CubeTriangulation.cubeSimplex (PermutationInsertion.insert k e) := by
  apply congrArg HigherHurewicz.CubeTriangulation.cubeAffineSimplex
  funext r
  exact prismCubeVertex_shuffle e k r

theorem FourthHurewicz.CubeSubdivision.PermutationInsertion.insert_injective {n : ℕ} :
    Function.Injective
      (fun p : Fin (n + 1) × Equiv.Perm (Fin n) =>
        FourthHurewicz.CubeSubdivision.PermutationInsertion.insert p.1 p.2) := by
  rintro ⟨k, e⟩ ⟨l, f⟩ h
  have hk : k = l := by simpa using congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ.symm 0) h
  subst l
  refine Prod.ext rfl ?_
  apply Equiv.ext
  intro j
  apply Fin.succ_injective n
  simpa using congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ (k.succAbove j)) h

theorem FourthHurewicz.CubeSubdivision.PermutationInsertion.insert_bijective {n : ℕ} :
    Function.Bijective
      (fun p : Fin (n + 1) × Equiv.Perm (Fin n) =>
        FourthHurewicz.CubeSubdivision.PermutationInsertion.insert p.1 p.2) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨insert_injective, by simp [Fintype.card_perm, Nat.factorial_succ]⟩

theorem FourthHurewicz.CubeSubdivision.PermutationInsertion.sum_insert {n : ℕ} {A : Type*}
    [AddCommMonoid A] (f : Equiv.Perm (Fin (n + 1)) → A) :
    (∑ k : Fin (n + 1),
        ∑ e : Equiv.Perm (Fin n),
          f (FourthHurewicz.CubeSubdivision.PermutationInsertion.insert k e)) =
      ∑ σ : Equiv.Perm (Fin (n + 1)), f σ := by
  rw [← Fintype.sum_prod_type']
  exact insert_bijective.sum_comp f

theorem FourthHurewicz.CubeSubdivision.PermutationInsertion.sum_sign_insert {n : ℕ} {A : Type*}
    [AddCommGroup A] (f : Equiv.Perm (Fin (n + 1)) → A) :
    (∑ k : Fin (n + 1),
        ∑ e : Equiv.Perm (Fin n),
          ((-1 : ℤ) ^ (k : ℕ) * (Equiv.Perm.sign e : ℤ)) •
            f (FourthHurewicz.CubeSubdivision.PermutationInsertion.insert k e)) =
      ∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) • f σ := by
  simpa only [sign_insert_int] using sum_insert (fun σ => (Equiv.Perm.sign σ : ℤ) • f σ)

theorem FourthHurewicz.CubeSubdivision.PermutationInsertion.sum_sign_smul_insert {n : ℕ}
    {A : Type*} [AddCommGroup A] (f : Equiv.Perm (Fin (n + 1)) → A) :
    (∑ k : Fin (n + 1),
        ∑ e : Equiv.Perm (Fin n),
          (-1 : ℤ) ^ (k : ℕ) •
            ((Equiv.Perm.sign e : ℤ) •
              f (FourthHurewicz.CubeSubdivision.PermutationInsertion.insert k e))) =
      ∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) • f σ := by
  simpa only [SemigroupAction.mul_smul] using sum_sign_insert f

theorem FourthHurewicz.CubeSubdivision.orientedPrismRealization_standardPrism {X : Type}
    [TopologicalSpace X] {n : ℕ} (p : C(HigherHurewicz.CubeTriangulation.CubeN (n + 1), X)) :
    orientedPrismRealization p (n + 1)
        (standardPrism n (fun i : Fin 2 => i) (fun j : Fin (n + 1) => j)) =
      ∑ perm : Equiv.Perm (Fin (n + 1)),
        HigherHurewicz.CubeTriangulation.cubeOrientation perm •
          SingularChains.simplexChain X (n + 1)
            (p.comp (HigherHurewicz.CubeTriangulation.cubeSimplex perm)) := by
  simp only [standardPrism, map_sum, map_zsmul, orientedPrismRealization_simplex,
    prismCubeSimplex_shuffle, ← Finset.sum_zsmul,
    HigherHurewicz.CubeTriangulation.cubeOrientation]
  exact
    PermutationInsertion.sum_sign_smul_insert
      (fun perm =>
        SingularChains.simplexChain X (n + 1)
          (p.comp (HigherHurewicz.CubeTriangulation.cubeSimplex perm)))

/-! ## The cube chain in every degree and its Kuhn decomposition (textbook §10.3) -/

/-- Dropping the zeroth coordinate of an `n + 1`-cube: the remaining coordinates as a
continuous map. -/
def HigherHurewicz.cubeRemainingCoordinates (n : ℕ) :
    C(Fin n → (unitInterval), { j : Fin (n + 1) // j ≠ 0 } → (unitInterval)) where
  toFun u j := u (j.1.pred j.2)
  continuous_toFun := by fun_prop

/-- Uncurrying a cube: the continuous map `I × (Fin n → I) → Fin (n + 1) → I` inserting the
first coordinate at position `0`. General-`n` form of `SecondHurewicz.squareCoordinates`. -/
def HigherHurewicz.cubeCoordinates (n : ℕ) :
    C((unitInterval) × (Fin n → (unitInterval)), Fin (n + 1) → (unitInterval)) where
  toFun z := Cube.insertAt (0 : Fin (n + 1)) (z.1, HigherHurewicz.cubeRemainingCoordinates n z.2)
  continuous_toFun := by
    apply (Cube.insertAt (0 : Fin (n + 1))).continuous.comp
    fun_prop

@[simp]
theorem HigherHurewicz.cubeCoordinates_zero (n : ℕ)
    (z : (unitInterval) × (Fin n → (unitInterval))) :
    HigherHurewicz.cubeCoordinates n z 0 = z.1 := by
  simp [HigherHurewicz.cubeCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply]

@[simp]
theorem HigherHurewicz.cubeCoordinates_succ (n : ℕ)
    (z : (unitInterval) × (Fin n → (unitInterval))) (j : Fin n) :
    HigherHurewicz.cubeCoordinates n z j.succ = z.2 j := by
  simp [HigherHurewicz.cubeCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply,
    HigherHurewicz.cubeRemainingCoordinates]

/-- The uncurrying preserves the boundary in the second argument. -/
theorem HigherHurewicz.cubeCoordinates_boundary_right (n : ℕ) (s : (unitInterval))
    {u : Fin n → (unitInterval)} (hu : u ∈ Cube.boundary (Fin n)) :
    HigherHurewicz.cubeCoordinates n (s, u) ∈ Cube.boundary (Fin (n + 1)) := by
  obtain ⟨i, hi⟩ := hu
  exact ⟨i.succ, by simpa using hi⟩

/-- A based `n + 1`-cube as a map from the product `I × (Fin n → I)`. -/
def HigherHurewicz.cubeMap {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin (n + 1)) X x) : C((unitInterval) × (Fin n → (unitInterval)), X) :=
  p.val.comp (HigherHurewicz.cubeCoordinates n)

/-- Currying a based `n + 1`-cube to a based `n`-cube of paths. -/
def HigherHurewicz.curryLoop {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin (n + 1)) X x) :
    GenLoop (Fin n) C((unitInterval), X) (ContinuousMap.const (unitInterval) x) :=
  ⟨((HigherHurewicz.cubeMap p).comp ContinuousMap.prodSwap).curry, by
    intro u hu
    apply ContinuousMap.ext
    intro s
    exact GenLoop.boundary p _ (HigherHurewicz.cubeCoordinates_boundary_right n s hu)⟩

/-- Evaluation of the curried cube recovers the cube map. -/
theorem HigherHurewicz.evalLeft_comp_curryLoop {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin (n + 1)) X x) :
    (FourthHurewicz.CubeSubdivision.evalLeft X).comp
        ((ContinuousMap.id (unitInterval)).prodMap (HigherHurewicz.curryLoop p).val) =
      HigherHurewicz.cubeMap p := by
  ext z
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
/-- The fundamental singular chain of the topological `n`-cube `Fin n → I`, defined
recursively: the `0`-cube is the point chain, the `1`-cube is the interval chain transported
along `(Fin 1 → I) ≃ₜ I`, and the `n + 2`-cube is the cross product of the interval chain with
the `n + 1`-cube chain, transported along the uncurrying map. -/
def HigherHurewicz.fundamentalCubeChain :
    (n : ℕ) → SingularChains.Chains (Fin n → (unitInterval)) n
  | 0 => SingularChains.pointChain 0
  | 1 => SingularChains.inducedChain
      ((Homeomorph.funUnique (Fin 1) (unitInterval)).symm : C((unitInterval), Fin 1 →
        (unitInterval))) 1 SecondHurewicz.intervalChain
  | n + 2 =>
    SingularChains.inducedChain (HigherHurewicz.cubeCoordinates (n + 1)) (n + 2)
      (PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin (n + 1) → (unitInterval))
        (n + 1) SecondHurewicz.intervalChain (HigherHurewicz.fundamentalCubeChain (n + 1)))

/-- The cube chain of a based `n`-cube: the image of the fundamental chain. -/
def HigherHurewicz.cubeChain {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin n) X x) : SingularChains.Chains X n :=
  SingularChains.inducedChain p.val n (HigherHurewicz.fundamentalCubeChain n)

theorem HigherHurewicz.fundamentalCubeChain_succ (n : ℕ) :
    HigherHurewicz.fundamentalCubeChain (n + 2) =
      SingularChains.inducedChain (HigherHurewicz.cubeCoordinates (n + 1)) (n + 2)
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval)
          (Fin (n + 1) → (unitInterval)) (n + 1) SecondHurewicz.intervalChain
          (HigherHurewicz.fundamentalCubeChain (n + 1))) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
/-- The recursion for the cube chain: the `n + 2`-cube chain is the evaluation of the cross
product of the interval chain with the curried `n + 1`-cube chain. -/
theorem HigherHurewicz.cubeChain_succ {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin (n + 2)) X x) :
    HigherHurewicz.cubeChain p =
      (SingularChains.inducedChain (FourthHurewicz.CubeSubdivision.evalLeft X) ((n + 1) + 1))
        ((PeriodTorusHigherHomology.crossProductEdge (unitInterval) C((unitInterval), X)
            (n + 1)) SecondHurewicz.intervalChain
          (HigherHurewicz.cubeChain (HigherHurewicz.curryLoop p))) := by
  unfold HigherHurewicz.cubeChain
  show (SingularChains.inducedChain p.val (n + 2) (HigherHurewicz.fundamentalCubeChain (n + 2))) =
    _
  rw [HigherHurewicz.fundamentalCubeChain_succ, ← LinearMap.comp_apply,
    ← SingularChains.inducedChain_comp,
    show p.val.comp (HigherHurewicz.cubeCoordinates (n + 1)) = HigherHurewicz.cubeMap p from rfl,
    ← HigherHurewicz.evalLeft_comp_curryLoop p, SingularChains.inducedChain_comp,
    LinearMap.comp_apply, PeriodTorusHigherHomology.crossProductEdge_natural,
    SingularChains.inducedChain_id, LinearMap.id_apply]

/-- The prism cube map factors through the uncurrying map: inserting the path simplex and the
`e`-th permutation simplex along coordinate `0` gives the prism cube map. General-`n` form of
`FourthHurewicz.CubeSubdivision.prismCubeMap_three`. -/
theorem HigherHurewicz.cubeCoordinates_comp_prismCubeMap {n : ℕ} (e : Equiv.Perm (Fin n)) :
    (HigherHurewicz.cubeCoordinates n).comp
        ((SingularChains.pathSimplex Path.id).prodMap
          (HigherHurewicz.CubeTriangulation.cubeSimplex e)) =
      FourthHurewicz.CubeSubdivision.prismCubeMap e := by
  apply ContinuousMap.ext
  intro z
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact HigherHurewicz.cubeCoordinates_zero n _
  · show HigherHurewicz.cubeCoordinates n _ j.succ = _
    rw [HigherHurewicz.cubeCoordinates_succ]
    rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
/-- The key term identification of the induction step: the cross product of the interval chain
with the `e`-th simplex chain of the curried cube evaluates to the `e`-th prism realization.
General-`n` form of
`FourthHurewicz.CubeSubdivision.intervalTetrahedronChain_eq_prismCubeRealization`. -/
theorem HigherHurewicz.evalLeft_crossProductEdge_intervalChain_simplex {n : ℕ} {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin (n + 1)) X x) (e : Equiv.Perm (Fin n)) :
    (SingularChains.inducedChain (FourthHurewicz.CubeSubdivision.evalLeft X) (n + 1))
        ((PeriodTorusHigherHomology.crossProductEdge (unitInterval) C((unitInterval), X) n)
          SecondHurewicz.intervalChain
          (SingularChains.simplexChain C((unitInterval), X) n
            ((HigherHurewicz.curryLoop p).val.comp
              (HigherHurewicz.CubeTriangulation.cubeSimplex e)))) =
      FourthHurewicz.CubeSubdivision.prismCubeRealization p.val e (n + 1)
        ((PeriodTorusHigherHomology.formalEdgeCrossProduct n)
          (SingularMayerVietoris.formalSimplex (fun i : Fin 2 => i))
          (SingularMayerVietoris.formalSimplex (fun j : Fin (n + 1) => j))) := by
  rw [SecondHurewicz.intervalChain, SingularChains.pathChain,
    PeriodTorusHigherHomology.crossProductEdge_simplex,
    FourthHurewicz.CubeSubdivision.prismCubeRealization_edgeCrossProduct]
  rw [← LinearMap.comp_apply, ← SingularChains.inducedChain_comp]
  have h : (FourthHurewicz.CubeSubdivision.evalLeft X).comp
        ((SingularChains.pathSimplex Path.id).prodMap
          ((HigherHurewicz.curryLoop p).val.comp
            (HigherHurewicz.CubeTriangulation.cubeSimplex e))) =
      p.val.comp (FourthHurewicz.CubeSubdivision.prismCubeMap e) := by
    rw [show (SingularChains.pathSimplex Path.id).prodMap
            ((HigherHurewicz.curryLoop p).val.comp
              (HigherHurewicz.CubeTriangulation.cubeSimplex e)) =
          ((ContinuousMap.id (unitInterval)).prodMap (HigherHurewicz.curryLoop p).val).comp
            ((SingularChains.pathSimplex Path.id).prodMap
              (HigherHurewicz.CubeTriangulation.cubeSimplex e)) from
        by apply ContinuousMap.ext; intro z; rfl]
    rw [← ContinuousMap.comp_assoc, HigherHurewicz.evalLeft_comp_curryLoop p]
    rw [HigherHurewicz.cubeMap, ContinuousMap.comp_assoc,
      HigherHurewicz.cubeCoordinates_comp_prismCubeMap]
  rw [h]


/-- The canonical identification of the interval with the `1`-cube, pulled back along the
identity path simplex, is the permutation simplex of the identity: the `n = 1` corner of the
cube-simplex dictionary. -/
theorem HigherHurewicz.funUniqueSymm_pathSimplex_eq_cubeSimplex_one :
    ((Homeomorph.funUnique (Fin 1) (unitInterval)).symm : C((unitInterval),
        Fin 1 → (unitInterval))).comp (SingularChains.pathSimplex Path.id) =
      HigherHurewicz.CubeTriangulation.cubeSimplex (1 : Equiv.Perm (Fin 1)) := by
  apply ContinuousMap.ext
  intro s
  funext j
  apply Subtype.ext
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  show (s 1 : ℝ) = _
  rw [HigherHurewicz.CubeTriangulation.cubeSimplex,
    HigherHurewicz.CubeTriangulation.cubeAffineSimplex_coordinate]
  simp [HigherHurewicz.CubeTriangulation.cubeVertex, Fin.sum_univ_two]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
/-- The cube chain in degree `1` is the single permutation simplex: the base case of the Kuhn
decomposition. -/
theorem HigherHurewicz.cubeChain_one {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 1) X x) :
    HigherHurewicz.cubeChain p = ∑ e : Equiv.Perm (Fin 1),
      HigherHurewicz.CubeTriangulation.cubeOrientation e •
        SingularChains.simplexChain X 1
          (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)) := by
  have h1 : ∀ e : Equiv.Perm (Fin 1), e = 1 := fun e => by
    apply Equiv.ext
    intro j
    exact Subsingleton.elim _ _
  rw [Finset.sum_eq_single 1 (fun e _ he => absurd (h1 e) he) (by simp)]
  have hsign : HigherHurewicz.CubeTriangulation.cubeOrientation (1 : Equiv.Perm (Fin 1)) = 1 := by
    simp [HigherHurewicz.CubeTriangulation.cubeOrientation]
  rw [hsign, one_zsmul]
  unfold HigherHurewicz.cubeChain
  rw [show HigherHurewicz.fundamentalCubeChain 1 =
      SingularChains.inducedChain
        ((Homeomorph.funUnique (Fin 1) (unitInterval)).symm : C((unitInterval),
          Fin 1 → (unitInterval))) 1 SecondHurewicz.intervalChain from rfl]
  rw [SecondHurewicz.intervalChain, SingularChains.pathChain, SingularChains.inducedChain_simplex,
    SingularChains.inducedChain_simplex]
  congr 1
  rw [HigherHurewicz.funUniqueSymm_pathSimplex_eq_cubeSimplex_one]

/-- The uncurrying map in degree `2`, pulled back along the `(Fin 1 → I) ≃ₜ I` identification,
is the square coordinates map. -/
theorem HigherHurewicz.cubeCoordinates_one_comp_eq_squareCoordinates :
    (HigherHurewicz.cubeCoordinates 1).comp
        ((ContinuousMap.id (unitInterval)).prodMap
          ((Homeomorph.funUnique (Fin 1) (unitInterval)).symm : C((unitInterval),
            Fin 1 → (unitInterval)))) =
      SecondHurewicz.squareCoordinates := by
  apply ContinuousMap.ext
  intro z
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · show HigherHurewicz.cubeCoordinates 1 _ 0 = SecondHurewicz.squareCoordinates z 0
    rw [HigherHurewicz.cubeCoordinates_zero, SecondHurewicz.squareCoordinates_zero]
    rfl
  · have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    show HigherHurewicz.cubeCoordinates 1 _ (0 : Fin 1).succ = SecondHurewicz.squareCoordinates z 1
    rw [HigherHurewicz.cubeCoordinates_succ, SecondHurewicz.squareCoordinates_one]
    rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
/-- The fundamental chain of the `2`-cube is the fundamental square chain. -/
theorem HigherHurewicz.fundamentalCubeChain_two :
    HigherHurewicz.fundamentalCubeChain 2 = SecondHurewicz.fundamentalSquareChain := by
  have key : (PeriodTorusHigherHomology.crossProductEdge (unitInterval)
        (Fin 1 → (unitInterval)) 1) SecondHurewicz.intervalChain
        ((SingularChains.inducedChain
          ((Homeomorph.funUnique (Fin 1) (unitInterval)).symm : C((unitInterval),
            Fin 1 → (unitInterval))) 1) SecondHurewicz.intervalChain) =
      (SingularChains.inducedChain
        ((ContinuousMap.id (unitInterval)).prodMap
          ((Homeomorph.funUnique (Fin 1) (unitInterval)).symm : C((unitInterval),
            Fin 1 → (unitInterval)))) 2) SecondHurewicz.productSquareChain := by
    rw [SecondHurewicz.productSquareChain,
      PeriodTorusHigherHomology.crossProductEdge_natural, SingularChains.inducedChain_id,
      LinearMap.id_apply]
  rw [HigherHurewicz.fundamentalCubeChain_succ 0,
    show HigherHurewicz.fundamentalCubeChain (0 + 1) =
        SingularChains.inducedChain
          ((Homeomorph.funUnique (Fin 1) (unitInterval)).symm : C((unitInterval),
            Fin 1 → (unitInterval))) 1 SecondHurewicz.intervalChain from rfl,
    key, ← LinearMap.comp_apply, ← SingularChains.inducedChain_comp,
    HigherHurewicz.cubeCoordinates_one_comp_eq_squareCoordinates]
  rfl

/-- The lower triangle of the square is the identity permutation simplex. -/
theorem HigherHurewicz.lowerSquareTriangle_eq_cubeSimplex_one :
    SecondHurewicz.SimplyConnected.lowerSquareTriangle =
      HigherHurewicz.CubeTriangulation.cubeSimplex (1 : Equiv.Perm (Fin 2)) := by
  apply ContinuousMap.ext
  intro s
  funext i
  apply Subtype.ext
  refine Fin.cases ?_ (fun j => ?_) i
  · show (↑(SecondHurewicz.SimplyConnected.lowerSquareTriangle s 0) : ℝ) =
      ↑((HigherHurewicz.CubeTriangulation.cubeSimplex (1 : Equiv.Perm (Fin 2))) s
        ((1 : Equiv.Perm (Fin 2)) 0))
    rw [SecondHurewicz.SimplyConnected.lowerSquareTriangle_zero,
      HigherHurewicz.CubeTriangulation.cubeSimplex_coordinate]
    simp [Fin.sum_univ_three]
  · have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    show (↑(SecondHurewicz.SimplyConnected.lowerSquareTriangle s 1) : ℝ) =
      ↑((HigherHurewicz.CubeTriangulation.cubeSimplex (1 : Equiv.Perm (Fin 2))) s
        ((1 : Equiv.Perm (Fin 2)) 1))
    rw [SecondHurewicz.SimplyConnected.lowerSquareTriangle_one,
      HigherHurewicz.CubeTriangulation.cubeSimplex_coordinate]
    simp [Fin.sum_univ_three]

/-- The upper triangle of the square is the transposition permutation simplex. -/
theorem HigherHurewicz.upperSquareTriangle_eq_cubeSimplex_swap :
    SecondHurewicz.SimplyConnected.upperSquareTriangle =
      HigherHurewicz.CubeTriangulation.cubeSimplex (Equiv.swap 0 1) := by
  apply ContinuousMap.ext
  intro s
  funext i
  apply Subtype.ext
  refine Fin.cases ?_ (fun j => ?_) i
  · show (↑(SecondHurewicz.SimplyConnected.upperSquareTriangle s 0) : ℝ) =
      ↑((HigherHurewicz.CubeTriangulation.cubeSimplex (Equiv.swap 0 1)) s
        ((Equiv.swap (0 : Fin 2) 1) 1))
    rw [SecondHurewicz.SimplyConnected.upperSquareTriangle_zero,
      HigherHurewicz.CubeTriangulation.cubeSimplex_coordinate]
    simp [Fin.sum_univ_three]
  · have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    show (↑(SecondHurewicz.SimplyConnected.upperSquareTriangle s 1) : ℝ) =
      ↑((HigherHurewicz.CubeTriangulation.cubeSimplex (Equiv.swap 0 1)) s
        ((Equiv.swap (0 : Fin 2) 1) 0))
    rw [SecondHurewicz.SimplyConnected.upperSquareTriangle_one,
      HigherHurewicz.CubeTriangulation.cubeSimplex_coordinate]
    simp [Fin.sum_univ_three]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
/-- The cube chain in degree `2` is the alternating sum of the two permutation simplices: the
second base case of the Kuhn decomposition. -/
theorem HigherHurewicz.cubeChain_two {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) :
    HigherHurewicz.cubeChain p = ∑ e : Equiv.Perm (Fin 2),
      HigherHurewicz.CubeTriangulation.cubeOrientation e •
        SingularChains.simplexChain X 2
          (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)) := by
  have hub : HigherHurewicz.cubeChain p = SecondHurewicz.squareChain p := by
    unfold HigherHurewicz.cubeChain
    rw [HigherHurewicz.fundamentalCubeChain_two, SecondHurewicz.squareChain,
      SecondHurewicz.suspensionOne_toLoop, SecondHurewicz.fundamentalSquareChain,
      ← LinearMap.comp_apply, ← SingularChains.inducedChain_comp]
    rfl
  rw [hub, SecondHurewicz.SimplyConnected.squareChain_two_triangles,
    HigherHurewicz.lowerSquareTriangle_eq_cubeSimplex_one,
    HigherHurewicz.upperSquareTriangle_eq_cubeSimplex_swap]
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]
  have hsign1 : HigherHurewicz.CubeTriangulation.cubeOrientation (1 : Equiv.Perm (Fin 2)) = 1 := by
    simp [HigherHurewicz.CubeTriangulation.cubeOrientation]
  have hsign2 : HigherHurewicz.CubeTriangulation.cubeOrientation (Equiv.swap (0 : Fin 2) 1) = -1 := by
    simp [HigherHurewicz.CubeTriangulation.cubeOrientation]
  rw [hsign1, hsign2]
  simp only [one_zsmul, neg_one_zsmul, sub_eq_add_neg]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
/-- The induction step of the Kuhn decomposition: from the decomposition in degree `k + 2` to
degree `k + 3`, through the prism realization (textbook §10.3). -/
theorem HigherHurewicz.cubeChain_eq_sum_simplices_step {k : ℕ} {X : Type} [TopologicalSpace X]
    {x : X}
    (ih : ∀ {Y : Type} [TopologicalSpace Y] {y : Y} (q : GenLoop (Fin ((k + 1) + 1)) Y y),
      HigherHurewicz.cubeChain q = ∑ e : Equiv.Perm (Fin ((k + 1) + 1)),
        HigherHurewicz.CubeTriangulation.cubeOrientation e •
          SingularChains.simplexChain Y ((k + 1) + 1)
            (q.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)))
    (p : GenLoop (Fin (k + 3)) X x) :
    HigherHurewicz.cubeChain p = ∑ e : Equiv.Perm (Fin (k + 3)),
      HigherHurewicz.CubeTriangulation.cubeOrientation e •
        SingularChains.simplexChain X (k + 3)
          (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)) := by
  rw [HigherHurewicz.cubeChain_succ (n := k + 1) p, ih (HigherHurewicz.curryLoop p)]
  simp only [map_sum, map_zsmul,
    HigherHurewicz.evalLeft_crossProductEdge_intervalChain_simplex]
  rw [← FourthHurewicz.CubeSubdivision.orientedPrismRealization_eq_sum]
  show FourthHurewicz.CubeSubdivision.orientedPrismRealization p.val (k + 3)
      (PeriodTorusHigherHomology.formalEdgeCrossProduct (k + 2)
        (SingularMayerVietoris.formalSimplex (fun i : Fin 2 => i))
        (SingularMayerVietoris.formalSimplex (fun j : Fin (k + 3) => j))) = _
  rw [FourthHurewicz.CubeSubdivision.orientedPrismRealization_edge_eq_standard]
  show FourthHurewicz.CubeSubdivision.orientedPrismRealization p.val ((k + 2) + 1)
      (FourthHurewicz.CubeSubdivision.standardPrism (k + 2) (fun i : Fin 2 => i)
        (fun j : Fin ((k + 2) + 1) => j)) =
    ∑ e : Equiv.Perm (Fin ((k + 2) + 1)),
      HigherHurewicz.CubeTriangulation.cubeOrientation e •
        SingularChains.simplexChain X ((k + 2) + 1)
          (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e))
  rw [FourthHurewicz.CubeSubdivision.orientedPrismRealization_standardPrism]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
/-- The Kuhn decomposition of the cube chain in every degree: the chain of a based `n`-cube is
the alternating sum of its `n!` permutation simplices. This is the chain identity
`[Π n] = Σ_σ sign(σ)·σ_e` of the lane's textbook (§9, L5), proved by induction through the
prism realization (§10.3). -/
theorem HigherHurewicz.cubeChain_eq_sum_simplices (n : ℕ) {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin n) X x) :
    HigherHurewicz.cubeChain p = ∑ e : Equiv.Perm (Fin n),
      HigherHurewicz.CubeTriangulation.cubeOrientation e •
        SingularChains.simplexChain X n
          (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)) := by
  have aux : ∀ (m : ℕ) {Y : Type} [TopologicalSpace Y] {y : Y} (q : GenLoop (Fin m) Y y),
      HigherHurewicz.cubeChain q = ∑ e : Equiv.Perm (Fin m),
        HigherHurewicz.CubeTriangulation.cubeOrientation e •
          SingularChains.simplexChain Y m
            (q.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ihm =>
      intro Y inst y q
      cases m with
      | zero =>
        have h1 : ∀ e : Equiv.Perm (Fin 0), e = 1 := fun e => by
          apply Equiv.ext
          intro j
          exact j.elim0
        rw [Finset.sum_eq_single 1 (fun e _ he => absurd (h1 e) he) (by simp)]
        have hsign : HigherHurewicz.CubeTriangulation.cubeOrientation (1 : Equiv.Perm (Fin 0)) =
            1 := by
          simp [HigherHurewicz.CubeTriangulation.cubeOrientation]
        rw [hsign, one_zsmul]
        unfold HigherHurewicz.cubeChain
        rw [show HigherHurewicz.fundamentalCubeChain 0 = SingularChains.pointChain 0 from rfl,
          SingularChains.pointChain, SingularChains.inducedChain_simplex]
        congr 1
        apply ContinuousMap.ext
        intro s
        apply congrArg q.val
        funext i
        exact i.elim0
      | succ m =>
        cases m with
        | zero => exact HigherHurewicz.cubeChain_one q
        | succ m =>
          cases m with
          | zero => exact HigherHurewicz.cubeChain_two q
          | succ k =>
            exact HigherHurewicz.cubeChain_eq_sum_simplices_step (k := k)
              (fun q' => ihm ((k + 1) + 1) (by omega) q') q
  exact aux n p
/-- The face trichotomy for sums over `Fin (m + 3)`: the zeroth face, the interior faces
`j.succ.castSucc`, and the last face. -/
theorem HigherHurewicz.CubeTriangulation.sum_face_trichotomy {m : ℕ} {A : Type*}
    [AddCommGroup A] (f : Fin (m + 3) → A) :
    (∑ i : Fin (m + 3), f i) =
      f 0 + (∑ j : Fin (m + 1), f j.succ.castSucc) + f (Fin.last (m + 2)) := by
  calc (∑ i : Fin (m + 3), f i) = f 0 + ∑ i : Fin (m + 2), f i.succ :=
    Fin.sum_univ_succ f
  _ = f 0 + (∑ i : Fin (m + 1), f (i.castSucc).succ + f ((Fin.last (m + 1)).succ)) := by
    rw [Fin.sum_univ_castSucc]
  _ = (f 0 + ∑ i : Fin (m + 1), f i.succ.castSucc) + f (Fin.last (m + 2)) := by
    rw [show (Fin.last (m + 1)).succ = Fin.last (m + 2) from Fin.ext rfl]
    rw [← add_assoc]
    congr 1

/-- The chamber-face sum with alternating signs vanishes: the interior faces cancel in pairs
by the transposition gluing of the Kuhn triangulation, and the two boundary-face
contributions are constant over the chambers with vanishing total orientation. This is the
combinatorial core of "the cube chain of a loop is a cycle" and of the evaluation-cancel
lemmas (textbook §9). -/
theorem HigherHurewicz.CubeTriangulation.sum_cubeOrientation_faces {m : ℕ} {A : Type*}
    [AddCommGroup A]
    (T : Equiv.Perm (Fin (m + 2)) → Fin (m + 3) → A)
    (hT : ∀ (e : Equiv.Perm (Fin (m + 2))) (j : Fin (m + 1)),
      T ((Equiv.swap j.castSucc j.succ).trans e) j.succ.castSucc = T e j.succ.castSucc)
    (C : A) (hC₀ : ∀ e, T e 0 = C) (hC₁ : ∀ e, T e (Fin.last (m + 2)) = C) :
    ∑ e : Equiv.Perm (Fin (m + 2)), HigherHurewicz.CubeTriangulation.cubeOrientation e •
        (∑ i : Fin (m + 3), (-1 : ℤ) ^ i.val • T e i) = 0 := by
  classical
  have hinner : ∀ e : Equiv.Perm (Fin (m + 2)),
      (∑ i : Fin (m + 3), (-1 : ℤ) ^ i.val • T e i) =
        T e 0 + (∑ j : Fin (m + 1), (-1 : ℤ) ^ (j.val + 1) • T e j.succ.castSucc) +
          (-1 : ℤ) ^ (m + 2) • T e (Fin.last (m + 2)) := by
    intro e
    rw [HigherHurewicz.CubeTriangulation.sum_face_trichotomy
      (f := fun i => (-1 : ℤ) ^ i.val • T e i)]
    simp
  have hmid : ∀ j : Fin (m + 1),
      ∑ e : Equiv.Perm (Fin (m + 2)),
        HigherHurewicz.CubeTriangulation.cubeOrientation e • T e j.succ.castSucc = 0 :=
    fun j =>
    FourthHurewicz.CubeSubdivision.signed_sum_eq_zero_of_swap_invariant
      j.castSucc j.succ (Fin.castSucc_lt_succ (i := j)).ne
      (fun e => T e j.succ.castSucc) (fun e => hT e j)
  have hsum (C' : A) :
      (∑ e : Equiv.Perm (Fin (m + 2)),
          HigherHurewicz.CubeTriangulation.cubeOrientation e • C') = 0 :=
    FourthHurewicz.CubeSubdivision.signed_sum_constant_eq_zero C'
  have hmid' :
      (∑ e : Equiv.Perm (Fin (m + 2)), HigherHurewicz.CubeTriangulation.cubeOrientation e •
          ∑ j : Fin (m + 1), (-1 : ℤ) ^ (j.val + 1) • T e j.succ.castSucc) = 0 := by
    simp_rw [Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    calc
      ∑ e : Equiv.Perm (Fin (m + 2)),
            HigherHurewicz.CubeTriangulation.cubeOrientation e •
              ((-1 : ℤ) ^ (j.val + 1) • T e j.succ.castSucc) =
          ∑ e, ((-1 : ℤ) ^ (j.val + 1)) •
            (HigherHurewicz.CubeTriangulation.cubeOrientation e • T e j.succ.castSucc) := by
        apply Finset.sum_congr rfl
        intro e _
        rw [smul_smul, mul_comm, ← smul_smul]
      _ = ((-1 : ℤ) ^ (j.val + 1)) •
            ∑ e, HigherHurewicz.CubeTriangulation.cubeOrientation e • T e j.succ.castSucc := by
        rw [Finset.smul_sum]
      _ = ((-1 : ℤ) ^ (j.val + 1)) • 0 := by rw [hmid j]
      _ = 0 := smul_zero _
  simp only [hinner]
  simp only [smul_add, Finset.sum_add_distrib]
  rw [show (∑ e : Equiv.Perm (Fin (m + 2)),
          HigherHurewicz.CubeTriangulation.cubeOrientation e • T e 0) = 0 from by
      simp_rw [hC₀]
      exact hsum C]
  rw [show (∑ e : Equiv.Perm (Fin (m + 2)),
          HigherHurewicz.CubeTriangulation.cubeOrientation e •
            ((-1 : ℤ) ^ (m + 2) • T e (Fin.last (m + 2)))) = 0 from by
      rw [show (∑ e : Equiv.Perm (Fin (m + 2)),
              HigherHurewicz.CubeTriangulation.cubeOrientation e •
                ((-1 : ℤ) ^ (m + 2) • T e (Fin.last (m + 2)))) =
            (-1 : ℤ) ^ (m + 2) •
              (∑ e : Equiv.Perm (Fin (m + 2)),
                HigherHurewicz.CubeTriangulation.cubeOrientation e • C) from by
          rw [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro e _
          rw [hC₁ e, smul_smul, mul_comm, ← smul_smul]]
      rw [hsum C, smul_zero]]
  rw [hmid']
  simp

/-- The cube chain of a based loop is a cycle: its boundary is the chamber-face sum, which
vanishes by the transposition gluing on interior faces and the loop's boundary constancy on
the outer faces. General-`n` form of the per-degree `boundary*_cubeChain` facts. -/
theorem HigherHurewicz.cubeChain_boundary {m : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin (m + 2)) X x) :
    ((SingularChains.singularComplex X).d (m + 2) (m + 1)).hom
        (HigherHurewicz.cubeChain p) = 0 := by
  rw [HigherHurewicz.cubeChain_eq_sum_simplices, map_sum]
  simp only [map_zsmul, SingularChains.boundary_simplex]
  apply HigherHurewicz.CubeTriangulation.sum_cubeOrientation_faces
    (C := SingularChains.simplexChain X (m + 1)
      (ContinuousMap.const (SingularChains.Simplex (m + 1)) x))
  · intro e j
    show SingularChains.simplexChain X (m + 1)
        ((p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex
            ((Equiv.swap j.castSucc j.succ).trans e))).comp
          (SingularChains.simplexFace (m + 1) j.succ.castSucc)) = _
    rw [ContinuousMap.comp_assoc, ContinuousMap.comp_assoc,
      ← HigherHurewicz.CubeTriangulation.cubeSimplex_face_swap]
  · intro e
    apply congrArg (SingularChains.simplexChain X (m + 1))
    apply ContinuousMap.ext
    intro s
    show p.val (HigherHurewicz.CubeTriangulation.cubeSimplex e
        (SingularChains.simplexFace (m + 1) 0 s)) = x
    exact GenLoop.boundary p _
      (HigherHurewicz.CubeTriangulation.cubeSimplex_face_zero_boundary e s)
  · intro e
    apply congrArg (SingularChains.simplexChain X (m + 1))
    apply ContinuousMap.ext
    intro s
    show p.val (HigherHurewicz.CubeTriangulation.cubeSimplex e
        (SingularChains.simplexFace (m + 1) (Fin.last (m + 2)) s)) = x
    exact GenLoop.boundary p _
      (HigherHurewicz.CubeTriangulation.cubeSimplex_face_last_boundary e s)

/-- The cube cycle of a based loop: the triangulated cube chain, which is a cycle by
`cubeChain_boundary`. -/
def HigherHurewicz.cubeCycle {m : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin (m + 2)) X x) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) (m + 2) :=
  SingularMayerVietoris.ModuleHomology.mkCycle (SingularChains.singularComplex X) (m + 2)
    (HigherHurewicz.cubeChain p) (by
      show ((SingularChains.singularComplex X).d (m + 2) (m + 1)).hom
          (HigherHurewicz.cubeChain p) = 0
      exact HigherHurewicz.cubeChain_boundary p)

@[simp]
theorem HigherHurewicz.cubeCycle_val {m : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin (m + 2)) X x) :
    (HigherHurewicz.cubeCycle p).1 = HigherHurewicz.cubeChain p :=
  rfl

/-- The cube homology class of a based loop: the class of its cube cycle. This is the
Hurewicz image of the loop's homotopy class. -/
def HigherHurewicz.cubeHomologyClass {m : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin (m + 2)) X x) : SingularMayerVietoris.SingularHomology X (m + 2) :=
  SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) (m + 2)
    (HigherHurewicz.cubeCycle p)

/-- The cube class of the constant loop vanishes: its cube chain is literally zero, the
chamber orientations summing to zero. -/
theorem HigherHurewicz.cubeHomologyClass_const {m : ℕ} {X : Type} [TopologicalSpace X]
    {x : X} :
    HigherHurewicz.cubeHomologyClass (GenLoop.const : GenLoop (Fin (m + 2)) X x) = 0 := by
  have hconst : ∀ e : Equiv.Perm (Fin (m + 2)),
      (GenLoop.const : GenLoop (Fin (m + 2)) X x).val.comp
          (HigherHurewicz.CubeTriangulation.cubeSimplex e) =
        ContinuousMap.const (SingularChains.Simplex (m + 2)) x := by
    intro e
    apply ContinuousMap.ext
    intro s
    rfl
  have hchain : HigherHurewicz.cubeChain (GenLoop.const : GenLoop (Fin (m + 2)) X x) = 0 := by
    rw [HigherHurewicz.cubeChain_eq_sum_simplices]
    simp_rw [hconst]
    have h := (map_sum (zmultiplesHom _ (SingularChains.simplexChain X (m + 2)
        (ContinuousMap.const (SingularChains.Simplex (m + 2)) x)))
      (HigherHurewicz.CubeTriangulation.cubeOrientation (n := m + 2)) Finset.univ).symm
    rw [HigherHurewicz.CubeTriangulation.cubeOrientation_sum, map_zero] at h
    exact h
  unfold HigherHurewicz.cubeHomologyClass
  rw [show HigherHurewicz.cubeCycle (GenLoop.const : GenLoop (Fin (m + 2)) X x) = 0 from
    Subtype.ext hchain]
  exact map_zero _


end Mathoverflow1973
