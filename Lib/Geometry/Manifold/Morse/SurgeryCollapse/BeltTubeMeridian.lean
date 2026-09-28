/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.AlgebraicTopology.SingularHomology.LinearSphereAction
import Lib.AlgebraicTopology.SingularHomology.LocalDegree
import Lib.AlgebraicTopology.SingularHomology.LocalDegreeNeighborhoods
import Lib.Analysis.Calculus.MorseLemma
import Lib.Geometry.Manifold.Flow.HeightTranslating
import Lib.Geometry.Manifold.Morse.BeltCancellation
import Lib.Geometry.Manifold.Morse.Handle
import Lib.Geometry.Manifold.Morse.HandleAttachment
import Lib.Geometry.Manifold.Morse.SublevelSets
import Lib.Geometry.Manifold.Morse.SurgeryWindows
import Lib.Geometry.Manifold.Transversality.Basic
import Lib.Geometry.Manifold.Morse.OrderedCancellation.BeltTube
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.PuncturedBall

/-!
# Loops in the belt tube are homotopic to meridians

A map into the tubular neighbourhood of a belt sphere whose belt-sphere component is
null-homotopic is homotopic to a meridian composed with the normalised normal component
(`MorseCancellation.nativeBeltTube_homotopic_meridian`); in particular the boundary of a small
parameter ball mapped into the belt tube is homotopic to a meridian
(`beltBallBoundary_homotopic_meridian`, `normal_boundary_homotopic_native_meridian`).  The
meridian of `Lib.Geometry.Manifold.Morse.OrderedCancellation.BeltTube` agrees with the upper
meridian of an adapted window (`nativeBeltTubeMeridian_eq`).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

noncomputable section

/-- Let `a : X → S(P)` be homotopic to the constant map at `v` and `b : X → punctured unit ball`.
Then `nativeBeltTubeInComplement d ∘ (a, b)` is homotopic to the meridian
`nativeBeltTubeMeridian d v r hr hr1` composed with the normalisation `toSphere 1 ∘ b`. -/
theorem MorseCancellation.nativeBeltTube_homotopic_meridian {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) {X : Type} [TopologicalSpace X]
    (a : C(X, Metric.sphere (0 : d.chart.PositiveCoordinates) 1))
    (b : C(X, PuncturedBall.Space d.chart.NegativeCoordinates 1))
    (v : Metric.sphere (0 : d.chart.PositiveCoordinates) 1)
    (ha : a.Homotopic (ContinuousMap.const _ v)) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ((nativeBeltTubeInComplement d).comp (a.prodMk b)).Homotopic
      ((nativeBeltTubeMeridian d v r hr hr1).comp ((PuncturedBall.toSphere 1).comp b)) := by
  let c := (PuncturedBall.toSphere 1).comp b
  let b' := (PuncturedBall.fromSphere 1 r hr hr1).comp c
  have hb : b.Homotopic b' := by
    have H := (PuncturedBall.deformation 1 r hr hr1).compContinuousMap b
    exact ⟨H⟩
  have hpair := ha.prodMk hb
  have hh := (ContinuousMap.Homotopic.refl (nativeBeltTubeInComplement d)).comp hpair
  have heq :
    (nativeBeltTubeInComplement d).comp ((ContinuousMap.const _ v).prodMk b') =
      (nativeBeltTubeMeridian d v r hr hr1).comp c := by
    apply ContinuousMap.ext
    intro x
    rfl
  rw [heq] at hh
  exact hh

/-- For an adapted window `S` at `q`, the belt tube meridian `nativeBeltTubeMeridian (S.data q) v r`
is the upper meridian `nativeUpperMeridianInComplement S q v ⟨r, _, _⟩ hr`. -/
theorem MorseCancellation.nativeBeltTubeMeridian_eq {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] (S : AdaptedWindows E f)
    (q : ManifoldMorse.criticalPoints E f)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1) :
    nativeBeltTubeMeridian (S.data q) v r hr hr1 =
      nativeUpperMeridianInComplement S q v ⟨r, hr.le, hr1.le⟩ hr := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  apply Subtype.ext
  change
    (S.data q).chart.splitChart.symm
        ((MorseHandle.ambientMap (S.data q).radius (v.val, r • u.val)).swap) =
      (S.data q).chart.splitChart.symm (BeltPassage.upper (S.data q).radius r u.val v.val)
  congr 1
  simp only [MorseHandle.ambientMap, BeltPassage.upper, Prod.swap, norm_smul,
    Real.norm_eq_abs, abs_of_pos hr, mem_sphere_zero_iff_norm.mp u.property, mul_one, smul_smul]

/-- The boundary map `beltBallBoundaryInComplement d ε hε F hsmall hne` of a parameter ball in the
belt neighbourhood is homotopic to the meridian through the belt component of `F 0` at radius
`r`, composed with the normalised normal map `toSphere 1 ∘ beltBallBoundaryNormal`. -/
theorem MorseCancellation.beltBallBoundary_homotopic_meridian {E M A : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    [NormedAddCommGroup A] [NormedSpace ℝ A] (d : ManifoldMorse.MorseSurgeryData E f p)
    (ε : ℝ) (hε : 0 < ε) (F : C(Metric.closedBall (0 : A) ε, d.chart.beltTarget d.radius))
    (hsmall : ∀ z, ‖(beltBallCoordinates d ε F z).2‖ < 1)
    (hne : ∀ u, (beltBallCoordinates d ε F (parameterBallBoundary ε hε u)).2 ≠ 0) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) :
    (beltBallBoundaryInComplement d ε hε F hsmall hne).Homotopic
      ((nativeBeltTubeMeridian d (beltBallCoordinates d ε F (parameterBallCenter ε hε)).1 r hr
            hr1).comp
        ((PuncturedBall.toSphere 1).comp (beltBallBoundaryNormal d ε hε F hsmall hne))) := by
  let a := ContinuousMap.fst.comp (beltBallCoordinates d ε F)
  have ha := parameterBall_boundary_nullhomotopic ε hε a
  exact
    nativeBeltTube_homotopic_meridian d (a.comp (parameterBallBoundary ε hε))
      (beltBallBoundaryNormal d ε hε F hsmall hne) (a (parameterBallCenter ε hε)) ha r hr hr1

/-- Let `g : A → d.UpperLevel` be continuous on `s`, with values in the belt normal domain and
normal component of norm `< 1`, and let `b : BoundaryData (d.beltNormal ∘ g) L s`.  Then there is
a map `J : S(A) → (belt sphere)ᶜ` with `J u = g (b.radius • u)` which is homotopic to a meridian
`nativeBeltTubeMeridian d v r` composed with the normalised map `b.normalizedMap`. -/
theorem MorseCancellation.normal_boundary_homotopic_native_meridian {E M A : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (d : ManifoldMorse.MorseSurgeryData E f p) (g : A → d.UpperLevel)
    {L : A ≃L[ℝ] d.chart.NegativeCoordinates} {s : Set A}
    (b : LocalDegree.BoundaryData (d.beltNormal ∘ g) L s) (hc : ContinuousOn g s)
    (hdomain : ∀ z ∈ s, g z ∈ d.beltNormalDomain)
    (hsmall : ∀ z ∈ s, ‖d.radius⁻¹ • d.beltNormal (g z)‖ < 1) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ∃ J : C(Metric.sphere (0 : A) 1, ((Set.range d.surgery.beltSphere)ᶜ : Set d.UpperLevel)),
      (∀ u, (J u).val = g (b.radius • u.val)) ∧
        ∃ v : Metric.sphere (0 : d.chart.PositiveCoordinates) 1,
          J.Homotopic ((nativeBeltTubeMeridian d v r hr hr1).comp b.normalizedMap) := by
  let F : C(Metric.closedBall (0 : A) b.radius, d.chart.beltTarget d.radius) :=
    { toFun := fun z => ⟨g z.val, hdomain z.val (b.ball_subset z.property)⟩
      continuous_toFun :=
        (hc.comp_continuous continuous_subtype_val (fun z => b.ball_subset z.property)).subtype_mk
          _ }
  have hsmallF : ∀ z, ‖(beltBallCoordinates d b.radius F z).2‖ < 1 := by
    intro z
    rw [beltBallCoordinates_normal]
    exact hsmall z.val (b.ball_subset z.property)
  have hne :
    ∀ u,
      (beltBallCoordinates d b.radius F (parameterBallBoundary b.radius b.radius_pos u)).2 ≠ 0 := by
    intro u
    rw [beltBallCoordinates_normal]
    exact smul_ne_zero (inv_ne_zero d.radius_pos.ne') (b.map u).property
  let J := beltBallBoundaryInComplement d b.radius b.radius_pos F hsmallF hne
  have hJ : ∀ u, (J u).val = g (b.radius • u.val) := by
    intro u
    exact beltBallBoundaryInComplement_coe d b.radius b.radius_pos F hsmallF hne u
  let v := (beltBallCoordinates d b.radius F (parameterBallCenter b.radius b.radius_pos)).1
  have hH := beltBallBoundary_homotopic_meridian d b.radius b.radius_pos F hsmallF hne r hr hr1
  have heq :
    (PuncturedBall.toSphere 1).comp
        (beltBallBoundaryNormal d b.radius b.radius_pos F hsmallF hne) =
      b.normalizedMap := by
    apply ContinuousMap.ext
    intro u
    apply Subtype.ext
    exact beltBallBoundary_normalized_coe d b.radius b.radius_pos F hsmallF hne u
  rw [heq] at hH
  exact ⟨J, hJ, v, hH⟩

end
