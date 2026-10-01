/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Lib.Geometry.Manifold.Whitney.RankThreeModel.GraphMotion
import Lib.Geometry.Manifold.Whitney.RankThreeModel.Model
import Lib.Geometry.Manifold.Whitney.RankThreeModel.SheetRetiming
import Lib.Geometry.Manifold.Whitney.RankThreeModel.SheetCorrection
import Lib.Geometry.Manifold.Whitney.RankThreeModel.TangentAdaptedChart
import Lib.Geometry.Manifold.Whitney.RankThreeModel.CorrectedCoordinates
import Lib.Geometry.Manifold.Whitney.RankThreeModel.SheetRecognition
import Lib.Geometry.Manifold.Whitney.RankThreeModel.SheetParametrizedChart
import Lib.Geometry.Manifold.Whitney.RankThreeModel.CompatibleChart
import Lib.Geometry.Manifold.Whitney.RankThreeModel.ModelGraphMotion
import Lib.Geometry.Manifold.Whitney.RankThreeModel.IntersectionRemoval
import Lib.Geometry.Manifold.Whitney.RankThreeModel.Cancellation

/-!
# The rank-three Whitney model

Whitney's lemma in the rank-three model (`TubularBigon.exists_rankThree_relative_cancellation`):
a tubular bigon whose two corner intersection signs are opposite yields an ambient isotopy,
supported away from the other intersection points, removing exactly those two points from the
intersection of the two sheets. This module only imports its pieces:

* `RankThreeModel.GraphMotion`: the graph motion of the Whitney pair model pushing the lower sheet
  across the bigon;
* `RankThreeModel.Model`: the rank-three model, its two sheets and their intersection;
* `RankThreeModel.SheetRetiming`: the retimed sheet transitions of a strip;
* `RankThreeModel.SheetCorrection`: correcting a map along the two model sheets;
* `RankThreeModel.TangentAdaptedChart`: charts of a tubular bigon adapted to the sheet tangents;
* `RankThreeModel.CorrectedCoordinates`: the corrected coordinates of a tangent-adapted chart;
* `RankThreeModel.SheetRecognition`: recognising a sheet in a chart near a compact set;
* `RankThreeModel.SheetParametrizedChart`: charts parametrising the two sheets;
* `RankThreeModel.CompatibleChart`: charts meeting the two sheets exactly in the model sheets;
* `RankThreeModel.ModelGraphMotion`: the rank-three graph motion and its transport to a manifold;
* `RankThreeModel.IntersectionRemoval`: set lemmas on maps supported in a set;
* `RankThreeModel.Cancellation`: Whitney's lemma in the rank-three model.

## References

* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65], §§5–6 (Whitney's lemma and the
  cancellation of a pair of intersection points of opposite sign).

## Twin

No Mathlib counterpart exists.

## Tags

Morse theory, Whitney trick, handle cancellation
-/
