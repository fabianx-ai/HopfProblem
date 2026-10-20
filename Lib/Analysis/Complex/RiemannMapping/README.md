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
  (moved: now `Lib.Analysis.Complex.ModulusOneReflection`)
* `RiemannMapping/BoundaryDerivative` — nonvanishing derivative at a boundary point of the upper
  half-plane;
* `RiemannMapping/ConformalExtension` — conformal extension of a disc map across analytic
  boundary arcs and at infinite strip ends;
* `RiemannMapping/PrincipalRoot` — the principal `n`-th root as corner-straightening map;
* `RiemannMapping/DiscCompactification` — extension of a homeomorphism onto the disc to the
  closure (topological Carathéodory theorem).

The triangle normalization and the exponent-specific sector roots used by the project live in
`Hopf/Proof/Analysis/Complex/RiemannMapping/`.

## Modules

This directory replaces the former facade module `Lib.Analysis.Complex.RiemannMapping` (deleted; its module docstring is the text
above, verbatim). Import the pieces directly:

* `Lib.Analysis.Complex.RiemannMapping.BoundaryDerivative`
* `Lib.Analysis.Complex.RiemannMapping.ConformalExtension`
* `Lib.Analysis.Complex.RiemannMapping.DiscBoundaryEscape`
* `Lib.Analysis.Complex.RiemannMapping.DiscCompactification`
* `Lib.Analysis.Complex.RiemannMapping.Existence`
* `Lib.Analysis.Complex.RiemannMapping.HalfStripChart`
* `Lib.Analysis.Complex.RiemannMapping.PrincipalRoot`
* `Lib.Analysis.Complex.RiemannMapping.RectanglePrimitive`
* `Lib.Analysis.Complex.RiemannMapping.Steps`
