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
  (moved: now `Lib.Geometry.Manifold.Morse.HandleAttachment.HandleCoordinates`)
* `Flow.HeightTranslating.DescentModel` : a flow that agrees with the model descent field in a
  Morse chart is the model flow (`ManifoldMorse.SignedMorseChart.flow_eqOn_descentModel`).
  (moved: now `Lib.Geometry.Manifold.Morse.HandleAttachment.DescentModel`)
* `Flow.HeightTranslating.AttachingUnion` : the sublevel with the handle attached is a
  deformation retract of the next sublevel
  (`ManifoldMorse.SignedMorseChart.exists_attachingUnionHomotopyEquiv`).
  (moved: now `Lib.Geometry.Manifold.Morse.HandleAttachment.AttachingUnion`)

## References

* [John Milnor, *Morse Theory*][milnor63], §3
* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65], §3

## Tags

flow, entry time, collar, sublevel set, handle attachment

## Modules

This directory replaces the former facade module `Lib.Geometry.Manifold.Flow.HeightTranslating` (deleted; its module docstring is the text
above, verbatim). Import the pieces directly:

* `Lib.Geometry.Manifold.Flow.HeightTranslating.AbsorbingSublevel`
* `Lib.Geometry.Manifold.Flow.HeightTranslating.DescentFlow`
* `Lib.Geometry.Manifold.Flow.HeightTranslating.EntryTime`
* `Lib.Geometry.Manifold.Flow.HeightTranslating.FlowCollar`
