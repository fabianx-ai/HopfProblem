/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

module

public import Lib.CategoryTheory.Sites.Leray.ResolutionTransgression

/-!
# Degree-zero higher direct images

For a continuous map `f : X ⟶ Y`, this file exposes Mathlib's canonical comparison between the
degree-zero right-derived sheaf pushforward `R⁰f_*` and ordinary sheaf pushforward `f_*`.  The
second definition is its value on an abelian sheaf.

This file does not compute an ordinary pushforward, identify any positive-degree higher direct
image, construct a local system or a Leray spectral sequence, or specialize to a geometric family.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace CategoryTheory.Sheaf.Leray

/-- The canonical degree-zero right-derived pushforward isomorphism. -/
def higherDirectImageZeroIsoPushforward {X Y : TopCat.{0}} (f : X ⟶ Y) :
    higherDirectImage f 0 ≅ pushforward f :=
  (pushforward f).rightDerivedZeroIsoSelf

/-- The canonical degree-zero right-derived pushforward isomorphism evaluated on a sheaf. -/
def higherDirectImageZeroSheafIsoPushforward {X Y : TopCat.{0}} (f : X ⟶ Y)
    (F : AbelianSheaf X) :
    higherDirectImageSheaf f F 0 ≅ (pushforward f).obj F :=
  (higherDirectImageZeroIsoPushforward f).app F

end CategoryTheory.Sheaf.Leray
