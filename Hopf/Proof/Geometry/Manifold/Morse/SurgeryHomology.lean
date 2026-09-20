/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Handle
import Lib.Analysis.Calculus.MorseLemma
import Lib.Geometry.Manifold.Flow.Compact
import Lib.Geometry.Manifold.RegularLevel
import Lib.Geometry.Manifold.Morse.HandleAttachment
import Lib.Geometry.Manifold.Flow.HeightTranslating
import Lib.Geometry.Manifold.Morse.Existence
import Lib.Analysis.ODE.SmoothFlow
import Lib.Geometry.Manifold.WhitneyEmbedding
import Lib.Geometry.Manifold.VectorBundle.ProjectionBundle
import Lib.Geometry.Manifold.Collar
import Lib.Geometry.Manifold.Morse.SurgeryWindows
import Lib.Geometry.Manifold.Morse.Cancellation
import Lib.Geometry.Manifold.Transversality.Basic
import Lib.Geometry.Manifold.Immersion.Relative
import Lib.Geometry.Manifold.Morse.Rearrangement
import Lib.Geometry.Manifold.Morse.Connection
import Lib.Topology.Homotopy.HandleRetraction
import Lib.Algebra.Homology.MayerVietorisShortExact
import Lib.AlgebraicTopology.SingularHomology.Chains
import Lib.AlgebraicTopology.SingularHomology.ModuleHomology
import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Lib.AlgebraicTopology.SingularHomology.LocalDegree
import Lib.Topology.Homotopy.LoopSubdivision
import Lib.AlgebraicTopology.FundamentalGroupoid.SimplyConnectedSphere
import Lib.Geometry.Manifold.Whitney.BigonModel
import Lib.Topology.Homotopy.CellAttachment
import Lib.Topology.Homotopy.Suspension
import Lib.AlgebraicTopology.SingularHomology.Sphere
import Lib.AlgebraicTopology.SingularHomology.Suspension
import Lib.AlgebraicTopology.SingularHomology.Sum
import Lib.AlgebraicTopology.SingularHomology.CircleProduct
import Lib.AlgebraicTopology.SingularHomology.SphereHomology
import Lib.AlgebraicTopology.SingularHomology.Coproduct
import Lib.Algebra.Module.IntegerPresentation
import Lib.AlgebraicTopology.SingularHomology.LocalContributions
import Lib.Topology.OnePointCollapse
import Lib.AlgebraicTopology.SingularHomology.Naturality
import Lib.AlgebraicTopology.SingularHomology.LinearSphereAction
import Lib.Geometry.Manifold.Morse.SublevelSets
import Lib.Geometry.Manifold.Morse.Index
import Lib.Geometry.Manifold.Morse.RearrangementTheorem
import Lib.Geometry.Manifold.Morse.Birth
import Lib.Geometry.Manifold.Morse.CellStructure
import Lib.Geometry.Manifold.Morse.Reeb
import Lib.AlgebraicTopology.SingularHomology.OnePointCover
import Lib.Geometry.Manifold.Morse.SurgeryHomology

/-!
# Upper level of a Morse surgery window (proof-specific)

Proof-specific material of the six-sphere formalization: this module is not
library mathematics and is not registered in `Lib.lean`.  It is the part of
`Lib.Geometry.Manifold.Morse.SurgeryHomology` that no `Lib` module consumes:

* `ManifoldMorse.MorseSurgeryData.upperLevelInclusion`, the inclusion of the
  upper level of a surgery step into the sublevel set above it;
* `ManifoldMorse.SurgeryWindows.lastUpperHomeomorph`, the homeomorphism between
  the upper level of the last window and the whole manifold.

Both are stated over `{E M : Type}` for the project's `SurgeryWindows` data and
are used only by the recognition argument in `Hopf/`.

Moved verbatim from `Hopf/SphereTopology.lean` via
`Lib/Geometry/Manifold/Morse/SurgeryHomology.lean`; statements unchanged.
-/
open Set Function Filter Manifold Topology

open scoped ContDiff

universe u v

noncomputable section


def ManifoldMorse.MorseSurgeryData.upperLevelInclusion {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) :
    C(d.UpperLevel, { y : M // f y ≤ f p + d.radius ^ 2 }) :=
  ⟨Set.inclusion (fun _ hx => hx.le), continuous_inclusion _⟩


def ManifoldMorse.SurgeryWindows.lastUpperHomeomorph {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] {f : M → ℝ} (S : ManifoldMorse.SurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (h : 0 < S.count) :
    { x : M // f x ≤ S.upper (S.last h) } ≃ₜ M :=
  (Homeomorph.setCongr (S.last_upper_univ hf h)).trans (Homeomorph.Set.univ M)

end
