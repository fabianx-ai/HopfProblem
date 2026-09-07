/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PLACEHOLDER (Fabian decides attribution)
-/
-- Reference copy of Mathlib PR fabianx-ai/mathlib4#4 (branch first-hurewicz-structure, commit 6a94f8af). Kept verbatim except for import paths.
module

public import Lib.AlgebraicTopology.Hurewicz.Degree1
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Topology.Subpath
public import Mathlib.Tactic.Positivity

/-!
# Homology classes of periodic loops

For a continuous one-periodic map `f : ℝ → X`, the loop `t ↦ f (n * t)` traverses the basic
loop `n` times, and its singular first-homology class is `n` times the class of the basic loop
(`loopHomologyClass_periodicScaledLoop`). The proof splits the `(n + 1)`-fold loop at time
`n / (n + 1)` into the `n`-fold loop followed by the basic loop, up to path homotopy
(`periodicScaledLoop_succ_homotopic`), and applies additivity of the loop class.
-/

@[expose] public noncomputable section

open Set Function Topology
open scoped ContinuousMap

namespace AlgebraicTopology.Hurewicz.PeriodicLoop

variable {X : Type} [TopologicalSpace X]

/-- The loop obtained by traversing a one-periodic map `n` times. -/
def periodicScaledLoop (f : C(ℝ, X)) (hf : Function.Periodic f 1) (n : ℕ) : Path (f 0) (f 0) where
  toFun t := f ((n : ℝ) * (t : ℝ))
  continuous_toFun :=
    f.continuous.comp (continuous_const.mul continuous_subtype_val)
  source' := by simp
  target' := by
    change f ((n : ℝ) * 1) = f 0
    simpa using hf.nat_mul_eq n

theorem periodicScaledLoop_apply
    (f : C(ℝ, X)) (hf : Function.Periodic f 1) (n : ℕ) (t : unitInterval) :
    periodicScaledLoop f hf n t = f ((n : ℝ) * (t : ℝ)) := rfl

theorem periodicScaledLoop_zero (f : C(ℝ, X)) (hf : Function.Periodic f 1) :
    periodicScaledLoop f hf 0 = Path.refl (f 0) := by
  apply Path.ext
  funext t
  simp [periodicScaledLoop]

theorem periodicScaledLoop_one (f : C(ℝ, X)) (hf : Function.Periodic f 1) (t : unitInterval) :
    periodicScaledLoop f hf 1 t = f (t : ℝ) := by
  simp [periodicScaledLoop]

theorem periodicScaledLoop_succ_homotopic (f : C(ℝ, X)) (hf : Function.Periodic f 1) (n : ℕ) :
    (periodicScaledLoop f hf (n + 1)).Homotopic
      ((periodicScaledLoop f hf n).trans (periodicScaledLoop f hf 1)) := by
  let P := periodicScaledLoop f hf (n + 1)
  let a : unitInterval :=
    ⟨(n : ℝ) / (n + 1 : ℝ), by
      constructor
      · positivity
      · apply (div_le_one (by positivity)).2
        norm_num⟩
  have ha : P a = f 0 := by
    change f (((n + 1 : ℕ) : ℝ) * ((n : ℝ) / (n + 1 : ℝ))) = f 0
    rw [show (((n + 1 : ℕ) : ℝ) * ((n : ℝ) / (n + 1 : ℝ))) =
        (n : ℝ) by
      field_simp
      all_goals push_cast
      all_goals ring]
    simpa using hf.nat_mul_eq n
  let left : Path (f 0) (f 0) :=
    (P.subpath 0 a).cast P.source.symm ha.symm
  let right : Path (f 0) (f 0) :=
    (P.subpath a 1).cast ha.symm P.target.symm
  have hleft : left = periodicScaledLoop f hf n := by
    apply Path.ext
    funext t
    change
      f (((n + 1 : ℕ) : ℝ) *
        ((1 - (t : ℝ)) * 0 + (t : ℝ) * ((n : ℝ) / (n + 1 : ℝ)))) =
        f ((n : ℝ) * (t : ℝ))
    congr 1
    field_simp
    all_goals push_cast
    all_goals ring
  have hright : right = periodicScaledLoop f hf 1 := by
    apply Path.ext
    funext t
    have heval : right t = P (Icc.convexComb a 1 t) := rfl
    rw [heval, periodicScaledLoop_apply, periodicScaledLoop_apply]
    rw [Icc.coe_convexComb]
    norm_num
    have ha_val : (a : ℝ) = (n : ℝ) / (n + 1 : ℝ) := rfl
    rw [ha_val]
    rw [show ((n : ℝ) + 1) *
        ((1 - (t : ℝ)) * ((n : ℝ) / (n + 1 : ℝ)) + (t : ℝ)) =
          (t : ℝ) + (n : ℝ) by
      field_simp
      all_goals ring]
    simpa using hf.nat_mul n (t : ℝ)
  have hraw :
      ((P.subpath 0 a).trans (P.subpath a 1)).Homotopic (P.subpath 0 1) :=
    ⟨Path.Homotopy.subpathTransSubpath P 0 a 1⟩
  have hcast := hraw.pathCast P.source.symm P.target.symm
  have hcast' :
      (left.trans right).Homotopic
        ((P.subpath 0 1).cast P.source.symm P.target.symm) := by
    convert hcast using 1
    all_goals apply Path.ext
    all_goals funext t
    all_goals rfl
  have hwhole :
      ((P.subpath 0 1).cast P.source.symm P.target.symm) = P := by
    apply Path.ext
    funext t
    simp [Path.subpath]
  have hfinal : (left.trans right).Homotopic P := by
    simpa only [hwhole] using hcast'
  rw [hleft, hright] at hfinal
  exact hfinal.symm

theorem loopHomologyClass_periodicScaledLoop (f : C(ℝ, X)) (hf : Function.Periodic f 1) (n : ℕ) :
    loopHomologyClass (periodicScaledLoop f hf n) =
      (n : ℤ) • loopHomologyClass (periodicScaledLoop f hf 1) := by
  induction n with
  | zero =>
      rw [periodicScaledLoop_zero, loopHomologyClass_refl]
      simp
  | succ n ih =>
      rw [loopHomologyClass_homotopic
          (periodicScaledLoop_succ_homotopic f hf n),
        loopHomologyClass_trans, ih]
      push_cast
      rw [add_zsmul, one_zsmul]

end AlgebraicTopology.Hurewicz.PeriodicLoop
