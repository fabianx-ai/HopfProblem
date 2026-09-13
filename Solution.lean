/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

This file is a formalization of the claim that the six-sphere admits a complex
manifold structure compatible with its standard topology.

The mathematical content is drawn from "A compact complex threefold fibred by
tori over the projective line, and the six-sphere" (https://alpo.ge/s6.pdf),
originally shared by Levent Alpöge on X:
https://x.com/__alpoge__/status/2091639597193368014

The majority of the Lean code in this formalization is written by Codex.

The statement of the final result is adapted from the Formal Conjectures
formalization of MathOverflow question 1973:
https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Mathoverflow/1973.lean

Parts of the complex-analysis development, including the Riemann mapping
theorem, Hurwitz's theorem, analytic factorization, normal-family arguments,
and unit-disc automorphisms, were adapted from Yury Kudryashov's Mathlib work:
https://github.com/leanprover-community/mathlib4/pull/33505
Source commit: d43061d911b1aeae0788591da437a3b115098962
Upstream files:
  Mathlib/Analysis/Complex/RiemannMapping.lean
  Mathlib/Analysis/Complex/UnitDisc/Shift.lean

Additional preliminary Riemann-mapping lemmas were adapted from
Mathlib/Analysis/Complex/RiemannMapping.lean in Mathlib v4.33.0:
https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Analysis/Complex/RiemannMapping.lean

Parts of the topology development, including simple connectedness of spheres,
the path-factorization portion of the van Kampen development, and associated
compatibility lemmas, were adapted from Sebastian Kumar's Mathlib work:
https://github.com/leanprover-community/mathlib4/pull/28246
Source commit: 037ad801e1e5a5b7aa1750957c07f7769812effc
Upstream files:
  Mathlib/AlgebraicTopology/FundamentalGroupoid/SimplyConnectedSphere.lean
  Mathlib/AlgebraicTopology/FundamentalGroupoid/VanKampen.lean
  Mathlib/Topology/Path.lean
  Mathlib/Logic/Equiv/PartialEquiv.lean

The reused upstream materials were released under the Apache License,
Version 2.0. They were modified, reorganized, and adapted for this
formalization; some results were also strengthened. Their copyright
and author notices are retained below.

Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Authors: Yury Kudryashov

Copyright (c) 2026 Sebastian Kumar. All rights reserved.
Authors: Sebastian Kumar

Copyright 2025 The Formal Conjectures Authors.
-/

import Hopf.Proof.Final

#print axioms mathoverflow_1973
-- 'mathoverflow_1973' depends on axioms: [propext, Classical.choice, Quot.sound]
