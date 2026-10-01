/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Lib.Analysis.Calculus.MorseLemma.PartialDiffeomorph
public import Lib.Analysis.Calculus.MorseLemma.PartitionOfUnity
public import Lib.Analysis.Calculus.MorseLemma.Cutoff
public import Lib.Analysis.Calculus.MorseLemma.SymmetricForm
public import Lib.Analysis.Calculus.MorseLemma.SignedCoordinates
public import Lib.Analysis.Calculus.MorseLemma.ParametricIntegral
public import Lib.Analysis.Calculus.MorseLemma.TaylorFactor
public import Lib.Analysis.Calculus.MorseLemma.Congruence
public import Lib.Analysis.Calculus.MorseLemma.MorseChart
public import Lib.Analysis.Calculus.MorseLemma.LinearPerturbation
public import Lib.Analysis.Calculus.MorseLemma.CriticalPoints
public import Lib.Analysis.Calculus.MorseLemma.SignedMorseChart
public import Lib.Analysis.Calculus.MorseLemma.SplitChart
public import Lib.Analysis.Calculus.MorseLemma.DescentField
public import Lib.Analysis.Calculus.MorseLemma.AdaptedDescentField
public import Lib.Analysis.Calculus.MorseLemma.Existence

/-!
# The Morse lemma and existence of Morse functions (facade)

This module only re-exports its pieces under `Lib/Analysis/Calculus/MorseLemma/`:

* `PartialDiffeomorph` — inverse function theorem as partial diffeomorphisms; restriction,
  translation, maximal-atlas charts as partial diffeomorphisms.
* `PartitionOfUnity` — smooth partitions of unity equal to one near a closed set.
* `Cutoff` — smooth cutoff functions and smooth extensions of germs.
* `SymmetricForm` — continuous symmetric bilinear forms, symmetrization, congruence.
* `SignedCoordinates` — Sylvester's law of inertia for a nondegenerate symmetric form.
* `ParametricIntegral` — smoothness of parametric interval integrals.
* `TaylorFactor` — the second-order Taylor factor `2 ∫₀¹ (1 - t) D²f(t x) dt`.
* `Congruence` — smooth congruence of symmetric forms near a nondegenerate one.
* `MorseChart` — the Morse lemma in a finite-dimensional normed space
  (Milnor, *Morse Theory*, Lemma 2.2), headline
  `SmoothMorseLemma.exists_signed_morse_chart_of_contDiffOn`.
* `LinearPerturbation` — the Morse condition in a vector space and linear perturbations.
* `CriticalPoints` — nondegenerate critical points on a manifold; finiteness on compact manifolds.
* `SignedMorseChart` — signed Morse charts on a manifold and their existence.
* `SplitChart` — negative/positive splitting of a signed chart, closed handle blocks.
* `DescentField` — gluing descent vector fields, prescribed derivatives.
* `AdaptedDescentField` — descent fields equal to the Morse model near critical points.
* `Existence` — existence of Morse functions on compact manifolds
  (Milnor, *Lectures on the h-cobordism theorem*, Theorem 2.5),
  headline `ManifoldMorse.exists_morse_function`.
-/
