/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Analysis.Calculus.MorseLemma
public import Lib.Geometry.Manifold.Morse.Handle
public import Lib.Geometry.Manifold.Flow.Compact
public import Lib.Geometry.Manifold.RegularLevel
public import Lib.Geometry.Manifold.Morse.HandleAttachment
public import Lib.Geometry.Manifold.Flow.HeightTranslating.EntryTime
public import Lib.Geometry.Manifold.Flow.HeightTranslating.FlowCollar
public import Lib.Geometry.Manifold.Flow.HeightTranslating.DescentFlow
public import Lib.Geometry.Manifold.Flow.HeightTranslating.AbsorbingSublevel
public import Lib.Geometry.Manifold.Flow.HeightTranslating.HandleCoordinates
public import Lib.Geometry.Manifold.Flow.HeightTranslating.DescentModel
public import Lib.Geometry.Manifold.Flow.HeightTranslating.AttachingUnion

/-!
# Flows across regular and critical levels: entry times, collars, handles

This module re-exports the pieces of the flow argument of Milnor, *Morse Theory*, §3
(Theorems 3.1 and 3.2):

* `Flow.HeightTranslating.EntryTime` : the entry time of a flow into a closed absorbing set, its
  continuity, the entry retraction and deformation (`FlowConstruction.entryTime`,
  `FlowConstruction.entryHomotopyEquiv`).
* `Flow.HeightTranslating.FlowCollar` : the homeomorphism `B ≃ₜ A` along the orbits between two
  nested absorbing sets (`FlowConstruction.FlowCollarData`, `FlowCollarData.homeomorph`).
* `Flow.HeightTranslating.DescentFlow` : flows along which a function decreases; existence for a
  band of regular values and for a Morse function (`FlowConstruction.exists_regularBandFlow`,
  `FlowConstruction.exists_adaptedDescentFlow`).
* `Flow.HeightTranslating.AbsorbingSublevel` : uniform entry times of a descent flow; an
  absorbing set is a deformation retract of, and homeomorphic to, the sublevel
  (`FlowConstruction.exists_absorbingSublevelHomotopyEquiv`,
  `FlowConstruction.exists_absorbingSublevelHomeomorph_with_boundary_orbits`).
* `Flow.HeightTranslating.HandleCoordinates` : ball coordinates, boundary data and the core
  attaching map of the handle of a signed Morse chart
  (`ManifoldMorse.SignedMorseChart.attachingCoreMap`).
* `Flow.HeightTranslating.DescentModel` : a flow that agrees with the model descent field in a
  Morse chart is the model flow (`ManifoldMorse.SignedMorseChart.flow_eqOn_descentModel`).
* `Flow.HeightTranslating.AttachingUnion` : the sublevel with the handle attached is a
  deformation retract of the next sublevel
  (`ManifoldMorse.SignedMorseChart.exists_attachingUnionHomotopyEquiv`).

## References

* [John Milnor, *Morse Theory*][milnor63], §3
* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65], §3

## Tags

flow, entry time, collar, sublevel set, handle attachment
-/
