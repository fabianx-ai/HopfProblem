/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.Analysis.Complex.RiemannMapping.Existence
import Lib.Analysis.Complex.RiemannMapping.DiscBoundaryEscape
import Lib.Analysis.Complex.RiemannMapping.HalfStripChart
import Lib.Analysis.Complex.RiemannMapping.RectanglePrimitive
import Lib.Analysis.Complex.RiemannMapping.ModulusOneReflection
import Lib.Analysis.Complex.RiemannMapping.BoundaryDerivative
import Lib.Analysis.Complex.RiemannMapping.ConformalExtension
import Lib.Analysis.Complex.RiemannMapping.PrincipalRoot
import Lib.Analysis.Complex.RiemannMapping.DiscCompactification
import Lib.Analysis.Complex.RiemannMapping.TriangleNormalization
import Lib.Analysis.Complex.RiemannMapping.SectorRoots

/-!
# The Riemann mapping theorem and boundary behaviour of conformal maps (facade)

This module only imports its pieces:

* `RiemannMapping/Existence` — the Riemann mapping theorem
  (`RiemannMapping.exists_bijOn_unitBall_deriv_ne_zero_map_eq_zero`; Ahlfors, *Complex Analysis*,
  Ch. 6 §1; Rudin, *Real and Complex Analysis*, Thm 14.8), with the computational steps in
  `RiemannMapping/Steps`;
* `RiemannMapping/DiscBoundaryEscape` — a homeomorphism onto the disc sends the boundary to the
  unit circle (`‖e z‖ → 1`);
* `RiemannMapping/HalfStripChart` — the logarithmic chart of a half-strip and its one-point
  compactification;
* `RiemannMapping/RectanglePrimitive` — primitives of holomorphic functions on open rectangles;
* `RiemannMapping/ModulusOneReflection` — analytic continuation across a boundary arc on which
  `‖f‖ → 1` (Schwarz reflection in the circle);
* `RiemannMapping/BoundaryDerivative` — nonvanishing derivative at a boundary point of the upper
  half-plane;
* `RiemannMapping/ConformalExtension` — conformal extension of a disc map across analytic
  boundary arcs and at infinite strip ends;
* `RiemannMapping/PrincipalRoot` — the principal `n`-th root as corner-straightening map;
* `RiemannMapping/DiscCompactification` — extension of a homeomorphism onto the disc to the
  closure (topological Carathéodory theorem).

* `RiemannMapping/TriangleNormalization`, `RiemannMapping/SectorRoots` — the triangle
  normalization and the exponent-specific sector roots used by the project.
-/
