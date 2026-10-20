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

## Modules

This directory replaces the former facade module `Lib.Geometry.Manifold.Whitney.RankThreeModel` (deleted; its module docstring is the text
above, verbatim). Import the pieces directly:

* `Lib.Geometry.Manifold.Whitney.RankThreeModel.Cancellation`
* `Lib.Geometry.Manifold.Whitney.RankThreeModel.CompatibleChart`
* `Lib.Geometry.Manifold.Whitney.RankThreeModel.CorrectedCoordinates`
* `Lib.Geometry.Manifold.Whitney.RankThreeModel.GraphMotion`
* `Lib.Geometry.Manifold.Whitney.RankThreeModel.IntersectionRemoval`
* `Lib.Geometry.Manifold.Whitney.RankThreeModel.Model`
* `Lib.Geometry.Manifold.Whitney.RankThreeModel.ModelGraphMotion`
* `Lib.Geometry.Manifold.Whitney.RankThreeModel.SheetCorrection`
* `Lib.Geometry.Manifold.Whitney.RankThreeModel.SheetParametrizedChart`
* `Lib.Geometry.Manifold.Whitney.RankThreeModel.SheetRecognition`
* `Lib.Geometry.Manifold.Whitney.RankThreeModel.SheetRetiming`
* `Lib.Geometry.Manifold.Whitney.RankThreeModel.TangentAdaptedChart`
