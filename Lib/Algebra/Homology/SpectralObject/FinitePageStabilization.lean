/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.SpectralObject.StableEndpoint
public import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

/-!
# Finite-page stabilization of a first-quadrant spectral object

This file compares a finite spectral-object subquotient with its stable endpoint.  If the two
outer interval terms which are removed in passing to the stable endpoints are zero, Mathlib's
endpoint-extension maps are isomorphisms.  Composing those two isomorphisms gives
`finiteEIsoStableE`.

For a first-quadrant spectral object, the required zero terms follow from the quadrant axioms.
Consequently the object in bidegree `(p,q)` on page `r` is isomorphic to the stable endpoint as
soon as `r ≥ max(p,q) + 2`; this is `firstQuadrantPageIsoStableE`.

No convergence datum is assumed.  The comparison is constructed directly from the exact
sequences of the spectral object.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows

namespace CategoryTheory.Abelian.SpectralObject

variable (X : SpectralObject AddCommGrpCat EInt)

/-- A finite subquotient is the stable endpoint when its omitted left and right tails have the
required adjacent cohomology groups equal to zero. -/
noncomputable def finiteEIsoStableE (a b n q : ℤ)
    (ha : a ≤ q) (hb : q + 1 ≤ b)
    (hleft : IsZero ((X.H (n + 1)).obj
      (mk₁ (homOfLE (show (⊥ : EInt) ≤ (a : EInt) by simp)))))
    (hright : IsZero ((X.H (n - 1)).obj
      (mk₁ (homOfLE (show (b : EInt) ≤ ⊤ by simp))))) :
    X.E
        (homOfLE (show (a : EInt) ≤ (q : EInt) by simpa))
        (homOfLE (show (q : EInt) ≤ ((q + 1 : ℤ) : EInt) by simp))
        (homOfLE (show ((q + 1 : ℤ) : EInt) ≤ (b : EInt) by simpa))
        (n - 1) n (n + 1) ≅
      X.stableE n q :=
  (X.isoMapFourδ₁Toδ₀'
      (⊥ : EInt) (a : EInt) (q : EInt) ((q + 1 : ℤ) : EInt) (b : EInt)
      (by simp)
      (by simpa)
      (by simp)
      (by simpa)
      (n - 1) n (n + 1) hleft).symm ≪≫
    X.isoMapFourδ₄Toδ₃'
      (⊥ : EInt) (q : EInt) ((q + 1 : ℤ) : EInt) (b : EInt) ⊤
      (by simp)
      (by simp)
      (by simpa)
      (by simp)
      (n - 1) n (n + 1) hright

variable [X.IsFirstQuadrant]

/-- In a first-quadrant `E₂` spectral sequence, page `r` at `(p,q)` is already the stable
endpoint when `r ≥ max(p,q) + 2`.

The safe uniform bound makes the two textbook conditions transparent: the left endpoint
`q-r+2` is nonpositive, and the right endpoint `q+r-1` is strictly above total degree minus one.
-/
noncomputable def firstQuadrantPageIsoStableE (r : ℤ) (p q : ℕ)
    (h : max (p : ℤ) (q : ℤ) + 2 ≤ r) :
    ((X.E₂SpectralSequenceNat.page r).X (p, q)) ≅
      X.stableE (p + q : ℤ) q :=
  X.spectralSequencePageXIso coreE₂CohomologicalNat r (by omega) (p, q)
      (((q : ℤ) - r + 2 : ℤ) : EInt) (q : EInt) (((q : ℤ) + 1 : ℤ) : EInt)
      (((q : ℤ) + r - 1 : ℤ) : EInt)
      rfl rfl rfl rfl
      (((p + q : ℕ) : ℤ) - 1) (p + q : ℤ) (((p + q : ℕ) : ℤ) + 1) (by simp) ≪≫
    X.finiteEIsoStableE ((q : ℤ) - r + 2) ((q : ℤ) + r - 1)
      (p + q : ℤ) q
      (by omega) (by omega)
      (X.isZero₁_of_isFirstQuadrant
        (⊥ : EInt) (((q : ℤ) - r + 2 : ℤ) : EInt) (by simp) (by
          have hq : (q : ℤ) - r + 2 ≤ 0 := by omega
          simpa using hq) _)
      (X.isZero₂_of_isFirstQuadrant
        (((q : ℤ) + r - 1 : ℤ) : EInt) ⊤ (by simp) _ (by
          have hp : ((p + q : ℕ) : ℤ) - 1 < (q : ℤ) + r - 1 := by omega
          simpa using hp))

end CategoryTheory.Abelian.SpectralObject
