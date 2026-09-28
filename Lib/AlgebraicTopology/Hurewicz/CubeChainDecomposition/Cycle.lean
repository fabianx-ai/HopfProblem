/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition.KuhnDecomposition

/-!
# The cube cycle of a based cube

The cube chain of a based cube `p : GenLoop (Fin (m + 2)) X x` is a cycle
(`Hurewicz.cubeChain_boundary`): by the Kuhn decomposition its boundary is the signed
sum over the chambers `e` of the faces of the Kuhn simplices, and the face trichotomy
(`CubeTriangulation.sum_face_trichotomy`) sorts them into the zeroth face, the interior
faces and the last face. The interior faces are shared by the chambers `e` and
`(swap j j+1) ∘ e`, which carry opposite orientations, so they cancel
(`CubeTriangulation.sum_cubeOrientation_faces`); the two outer faces lie on the cube
boundary, where `p` is constant, and their constant simplices cancel because the
orientations sum to zero.

`Hurewicz.cubeCycle p` packages the chain as a cycle and `Hurewicz.cubeHomologyClass p`
is its homology class — the Hurewicz image of `p` — which vanishes for the constant
cube (`cubeHomologyClass_const`).

This is the statement that the Hurewicz map is well defined on chains (Hatcher,
*Algebraic Topology*, §4.2, before Theorem 4.32).

## Main definitions

* `Hurewicz.cubeCycle`, `Hurewicz.cubeHomologyClass`

## Main results

* `Hurewicz.CubeTriangulation.sum_face_trichotomy`, `Hurewicz.CubeTriangulation.sum_cubeOrientation_faces`
* `Hurewicz.cubeChain_boundary`
* `Hurewicz.cubeHomologyClass_const`
-/

open Set Function Topology

noncomputable section

/-! ### The chamber-face sum -/

/-- The face trichotomy for sums over `Fin (m + 3)`: the zeroth face, the interior faces
`j.succ.castSucc`, and the last face. -/
theorem Hurewicz.CubeTriangulation.sum_face_trichotomy {m : ℕ} {A : Type*}
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
lemmas (cf. Hatcher, §4.2). -/
theorem Hurewicz.CubeTriangulation.sum_cubeOrientation_faces {m : ℕ} {A : Type*}
    [AddCommGroup A]
    (T : Equiv.Perm (Fin (m + 2)) → Fin (m + 3) → A)
    (hT : ∀ (e : Equiv.Perm (Fin (m + 2))) (j : Fin (m + 1)),
      T ((Equiv.swap j.castSucc j.succ).trans e) j.succ.castSucc = T e j.succ.castSucc)
    (C : A) (hC₀ : ∀ e, T e 0 = C) (hC₁ : ∀ e, T e (Fin.last (m + 2)) = C) :
    ∑ e : Equiv.Perm (Fin (m + 2)), Hurewicz.CubeTriangulation.cubeOrientation e •
        (∑ i : Fin (m + 3), (-1 : ℤ) ^ i.val • T e i) = 0 := by
  classical
  have hinner : ∀ e : Equiv.Perm (Fin (m + 2)),
      (∑ i : Fin (m + 3), (-1 : ℤ) ^ i.val • T e i) =
        T e 0 + (∑ j : Fin (m + 1), (-1 : ℤ) ^ (j.val + 1) • T e j.succ.castSucc) +
          (-1 : ℤ) ^ (m + 2) • T e (Fin.last (m + 2)) := by
    intro e
    rw [Hurewicz.CubeTriangulation.sum_face_trichotomy
      (f := fun i => (-1 : ℤ) ^ i.val • T e i)]
    simp
  have hmid : ∀ j : Fin (m + 1),
      ∑ e : Equiv.Perm (Fin (m + 2)),
        Hurewicz.CubeTriangulation.cubeOrientation e • T e j.succ.castSucc = 0 :=
    fun j =>
    Hurewicz.CubeSubdivision.signed_sum_eq_zero_of_swap_invariant
      j.castSucc j.succ (Fin.castSucc_lt_succ (i := j)).ne
      (fun e => T e j.succ.castSucc) (fun e => hT e j)
  have hsum (C' : A) :
      (∑ e : Equiv.Perm (Fin (m + 2)),
          Hurewicz.CubeTriangulation.cubeOrientation e • C') = 0 :=
    Hurewicz.CubeSubdivision.signed_sum_constant_eq_zero C'
  have hmid' :
      (∑ e : Equiv.Perm (Fin (m + 2)), Hurewicz.CubeTriangulation.cubeOrientation e •
          ∑ j : Fin (m + 1), (-1 : ℤ) ^ (j.val + 1) • T e j.succ.castSucc) = 0 := by
    simp_rw [Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    calc
      ∑ e : Equiv.Perm (Fin (m + 2)),
            Hurewicz.CubeTriangulation.cubeOrientation e •
              ((-1 : ℤ) ^ (j.val + 1) • T e j.succ.castSucc) =
          ∑ e, ((-1 : ℤ) ^ (j.val + 1)) •
            (Hurewicz.CubeTriangulation.cubeOrientation e • T e j.succ.castSucc) := by
        apply Finset.sum_congr rfl
        intro e _
        rw [smul_smul, mul_comm, ← smul_smul]
      _ = ((-1 : ℤ) ^ (j.val + 1)) •
            ∑ e, Hurewicz.CubeTriangulation.cubeOrientation e • T e j.succ.castSucc := by
        rw [Finset.smul_sum]
      _ = ((-1 : ℤ) ^ (j.val + 1)) • 0 := by rw [hmid j]
      _ = 0 := smul_zero _
  simp only [hinner]
  simp only [smul_add, Finset.sum_add_distrib]
  rw [show (∑ e : Equiv.Perm (Fin (m + 2)),
          Hurewicz.CubeTriangulation.cubeOrientation e • T e 0) = 0 from by
      simp_rw [hC₀]
      exact hsum C]
  rw [show (∑ e : Equiv.Perm (Fin (m + 2)),
          Hurewicz.CubeTriangulation.cubeOrientation e •
            ((-1 : ℤ) ^ (m + 2) • T e (Fin.last (m + 2)))) = 0 from by
      rw [show (∑ e : Equiv.Perm (Fin (m + 2)),
              Hurewicz.CubeTriangulation.cubeOrientation e •
                ((-1 : ℤ) ^ (m + 2) • T e (Fin.last (m + 2)))) =
            (-1 : ℤ) ^ (m + 2) •
              (∑ e : Equiv.Perm (Fin (m + 2)),
                Hurewicz.CubeTriangulation.cubeOrientation e • C) from by
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
theorem Hurewicz.cubeChain_boundary {m : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin (m + 2)) X x) :
    ((SingularChains.singularComplex X).d (m + 2) (m + 1)).hom
        (Hurewicz.cubeChain p) = 0 := by
  rw [Hurewicz.cubeChain_eq_sum_simplices, map_sum]
  simp only [map_zsmul, SingularChains.boundary_simplex]
  apply Hurewicz.CubeTriangulation.sum_cubeOrientation_faces
    (C := SingularChains.simplexChain X (m + 1)
      (ContinuousMap.const (SingularChains.Simplex (m + 1)) x))
  · intro e j
    show SingularChains.simplexChain X (m + 1)
        ((p.val.comp (Hurewicz.CubeTriangulation.cubeSimplex
            ((Equiv.swap j.castSucc j.succ).trans e))).comp
          (SingularChains.simplexFace (m + 1) j.succ.castSucc)) = _
    rw [ContinuousMap.comp_assoc, ContinuousMap.comp_assoc,
      ← Hurewicz.CubeTriangulation.cubeSimplex_face_swap]
  · intro e
    apply congrArg (SingularChains.simplexChain X (m + 1))
    apply ContinuousMap.ext
    intro s
    show p.val (Hurewicz.CubeTriangulation.cubeSimplex e
        (SingularChains.simplexFace (m + 1) 0 s)) = x
    exact GenLoop.boundary p _
      (Hurewicz.CubeTriangulation.cubeSimplex_face_zero_boundary e s)
  · intro e
    apply congrArg (SingularChains.simplexChain X (m + 1))
    apply ContinuousMap.ext
    intro s
    show p.val (Hurewicz.CubeTriangulation.cubeSimplex e
        (SingularChains.simplexFace (m + 1) (Fin.last (m + 2)) s)) = x
    exact GenLoop.boundary p _
      (Hurewicz.CubeTriangulation.cubeSimplex_face_last_boundary e s)

/-- The cube cycle of a based loop: the triangulated cube chain, which is a cycle by
`cubeChain_boundary`. -/
def Hurewicz.cubeCycle {m : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin (m + 2)) X x) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) (m + 2) :=
  SingularMayerVietoris.ModuleHomology.mkCycle (SingularChains.singularComplex X) (m + 2)
    (Hurewicz.cubeChain p) (by
      show ((SingularChains.singularComplex X).d (m + 2) (m + 1)).hom
          (Hurewicz.cubeChain p) = 0
      exact Hurewicz.cubeChain_boundary p)

/-- The underlying chain of `cubeCycle p` is `cubeChain p`. -/
@[simp]
theorem Hurewicz.cubeCycle_val {m : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin (m + 2)) X x) :
    (Hurewicz.cubeCycle p).1 = Hurewicz.cubeChain p :=
  rfl

/-- The cube homology class of a based loop: the class of its cube cycle. This is the
Hurewicz image of the loop's homotopy class. -/
def Hurewicz.cubeHomologyClass {m : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin (m + 2)) X x) : SingularMayerVietoris.SingularHomology X (m + 2) :=
  SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) (m + 2)
    (Hurewicz.cubeCycle p)

/-- The cube class of the constant loop vanishes: its cube chain is literally zero, the
chamber orientations summing to zero. -/
theorem Hurewicz.cubeHomologyClass_const {m : ℕ} {X : Type} [TopologicalSpace X]
    {x : X} :
    Hurewicz.cubeHomologyClass (GenLoop.const : GenLoop (Fin (m + 2)) X x) = 0 := by
  have hconst : ∀ e : Equiv.Perm (Fin (m + 2)),
      (GenLoop.const : GenLoop (Fin (m + 2)) X x).val.comp
          (Hurewicz.CubeTriangulation.cubeSimplex e) =
        ContinuousMap.const (SingularChains.Simplex (m + 2)) x := by
    intro e
    apply ContinuousMap.ext
    intro s
    rfl
  have hchain : Hurewicz.cubeChain (GenLoop.const : GenLoop (Fin (m + 2)) X x) = 0 := by
    rw [Hurewicz.cubeChain_eq_sum_simplices]
    simp_rw [hconst]
    have h := (map_sum (zmultiplesHom _ (SingularChains.simplexChain X (m + 2)
        (ContinuousMap.const (SingularChains.Simplex (m + 2)) x)))
      (Hurewicz.CubeTriangulation.cubeOrientation (n := m + 2)) Finset.univ).symm
    rw [Hurewicz.CubeTriangulation.cubeOrientation_sum, map_zero] at h
    exact h
  unfold Hurewicz.cubeHomologyClass
  rw [show Hurewicz.cubeCycle (GenLoop.const : GenLoop (Fin (m + 2)) X x) = 0 from
    Subtype.ext hchain]
  exact map_zero _
