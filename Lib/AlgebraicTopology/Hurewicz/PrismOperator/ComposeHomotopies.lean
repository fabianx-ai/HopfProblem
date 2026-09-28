/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.HomotopyExtension
import Lib.AlgebraicTopology.Hurewicz.SimplexCube
import Lib.AlgebraicTopology.Hurewicz.PrismOperator.Basic
import Lib.AlgebraicTopology.Hurewicz.PrismOperator.VertexEdgeStraightening
/-!
# Composing simplex-indexed homotopy families

Two families `H`, `G` of homotopies starting at each singular simplex compose to the family
`composeSimplexHomotopies H G`, which first runs `H smp` and then `G` at the endpoint of
`H smp` (the concatenation `ContinuousMap.Homotopy.trans`).  Composition preserves face
compatibility (`composeSimplexHomotopies_face`) and stationarity on the constant simplex
(`composeSimplexHomotopies_const`); the coherent extension of a family that is stationary on
constant simplices is stationary as well (`extendCoherentSimplexHomotopy_const`).  These are
the bookkeeping lemmas for iterating straightening homotopies (cf. Hatcher, Thm 4.32, proof).

## Main definitions

* `Hurewicz.cylinderHomotopy`, `Hurewicz.simplexFamilyHomotopy`.
* `Hurewicz.homotopyTrans_compContinuousMap`, `homotopyTrans_const`, `homotopyTrans_congr`.
* `Hurewicz.composeSimplexHomotopies`, `composeSimplexHomotopies_face`,
  `composeSimplexHomotopies_const`.
* `Hurewicz.coherentFaceBoundaryHomotopy_const`, `Hurewicz.extendCoherentSimplexHomotopy_const`.
-/

open Set Function Topology

noncomputable section

/-! ### Composing homotopy families -/

/-- A continuous cylinder map `I × A → X` viewed as a `Homotopy` between its
time-`0` and time-`1` slices. -/
def Hurewicz.cylinderHomotopy {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
    (H : C((unitInterval) × A, X)) :
    ContinuousMap.Homotopy (Hurewicz.Prism.timeSlice H 0)
      (Hurewicz.Prism.timeSlice H 1)
    where
  toContinuousMap := H
  map_zero_left _ := rfl
  map_one_left _ := rfl

/-- Transitivity of homotopies commutes with precomposition by a continuous map. -/
theorem Hurewicz.homotopyTrans_compContinuousMap {A B X : Type} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace X] {f₀ f₁ f₂ : C(A, X)} (F : f₀.Homotopy f₁)
    (G : f₁.Homotopy f₂) (f : C(B, A)) :
    (F.trans G).toContinuousMap.comp ((ContinuousMap.id (unitInterval)).prodMap f) =
      ((F.compContinuousMap f).trans (G.compContinuousMap f)).toContinuousMap := by
  ext z
  change (F.trans G) (z.1, f z.2) = ((F.compContinuousMap f).trans (G.compContinuousMap f)) z
  simp only [ContinuousMap.Homotopy.trans_apply]
  split_ifs <;> rfl

/-- The concatenation of two constant homotopies is the constant homotopy. -/
theorem Hurewicz.homotopyTrans_const {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
    {f₀ f₁ f₂ : C(A, X)} (F : f₀.Homotopy f₁) (G : f₁.Homotopy f₂) (x : X)
    (hF : F.toContinuousMap = ContinuousMap.const ((unitInterval) × A) x)
    (hG : G.toContinuousMap = ContinuousMap.const ((unitInterval) × A) x) :
    (F.trans G).toContinuousMap = ContinuousMap.const ((unitInterval) × A) x := by
  ext z
  change (F.trans G) z = x
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact ContinuousMap.congr_fun hF _
  · exact ContinuousMap.congr_fun hG _

/-- `HomotopyRel` transitivity respects equality of the homotopies. -/
theorem Hurewicz.homotopyTrans_congr {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
    {f₀ f₁ f₂ g₀ g₁ g₂ : C(A, X)} (F : f₀.Homotopy f₁) (G : f₁.Homotopy f₂) (F' : g₀.Homotopy g₁)
    (G' : g₁.Homotopy g₂) (hF : F.toContinuousMap = F'.toContinuousMap)
    (hG : G.toContinuousMap = G'.toContinuousMap) :
    (F.trans G).toContinuousMap = (F'.trans G').toContinuousMap := by
  ext z
  change (F.trans G) z = (F'.trans G') z
  simp only [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact ContinuousMap.congr_fun hF _
  · exact ContinuousMap.congr_fun hG _

/-- A simplex-indexed family `H` starting at `smp` viewed as a `Homotopy` from
`smp` to its time-`1` endpoint. -/
def Hurewicz.simplexFamilyHomotopy {X : Type} [TopologicalSpace X] {n : ℕ}
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (h₀ : ∀ smp s, H smp (0, s) = smp s) (smp : SingularChains.SingularSimplex X n) :
    smp.Homotopy (Hurewicz.Prism.timeSlice (H smp) 1) :=
  (cylinderHomotopy (H smp)).cast (by ext s; exact h₀ smp s) rfl

/-- The composition of two coherent simplex homotopy families (first `H₀` then
`H₁`), staying face-compatible. -/
def Hurewicz.composeSimplexHomotopies {X : Type} [TopologicalSpace X] {n : ℕ}
    (H G : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s) (hG₀ : ∀ smp s, G smp (0, s) = smp s)
    (smp : SingularChains.SingularSimplex X n) : C((unitInterval) × SingularChains.Simplex n, X) :=
  ((simplexFamilyHomotopy H hH₀ smp).trans
      (simplexFamilyHomotopy G hG₀
        (Hurewicz.Prism.timeSlice (H smp) 1))).toContinuousMap

/-- At time `0`, `composeSimplexHomotopies H₀ H₁` is `H₀` at time `0`. -/
@[simp]
theorem Hurewicz.composeSimplexHomotopies_zero {X : Type} [TopologicalSpace X] {n : ℕ}
    (H G : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s) (hG₀ : ∀ smp s, G smp (0, s) = smp s)
    (smp : SingularChains.SingularSimplex X n) (s : SingularChains.Simplex n) :
    composeSimplexHomotopies H G hH₀ hG₀ smp (0, s) = smp s :=
  ContinuousMap.Homotopy.apply_zero _ s

/-- At time `1`, `composeSimplexHomotopies H G` evaluates `G` at the time-`1`
endpoint of `H smp`. -/
@[simp]
theorem Hurewicz.composeSimplexHomotopies_one {X : Type} [TopologicalSpace X] {n : ℕ}
    (H G : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s) (hG₀ : ∀ smp s, G smp (0, s) = smp s)
    (smp : SingularChains.SingularSimplex X n) (s : SingularChains.Simplex n) :
    composeSimplexHomotopies H G hH₀ hG₀ smp (1, s) =
      G (Hurewicz.Prism.timeSlice (H smp) 1) (1, s) :=
  ContinuousMap.Homotopy.apply_one _ s

/-- The time-`1` slice of the composed homotopy is the time-`1` slice of `G`
applied to the time-`1` endpoint of `H smp`. -/
@[simp]
theorem Hurewicz.timeSlice_composeSimplexHomotopies_one {X : Type} [TopologicalSpace X]
    {n : ℕ}
    (H G : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s) (hG₀ : ∀ smp s, G smp (0, s) = smp s)
    (smp : SingularChains.SingularSimplex X n) :
    Hurewicz.Prism.timeSlice (composeSimplexHomotopies H G hH₀ hG₀ smp) 1 =
      Hurewicz.Prism.timeSlice
        (G (Hurewicz.Prism.timeSlice (H smp) 1)) 1 := by
  ext s
  exact composeSimplexHomotopies_one H G hH₀ hG₀ smp s

/-- The face restriction of the composed homotopy is the composition of the face
homotopies. -/
theorem Hurewicz.composeSimplexHomotopies_face {X : Type} [TopologicalSpace X] {n : ℕ}
    (H G : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' G' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s) (hG₀ : ∀ smp s, G smp (0, s) = smp s)
    (hH'₀ : ∀ smp s, H' smp (0, s) = smp s) (hG'₀ : ∀ smp s, G' smp (0, s) = smp s)
    (hH : Hurewicz.Prism.FaceCompatibleHomotopies n H H')
    (hG : Hurewicz.Prism.FaceCompatibleHomotopies n G G') :
    Hurewicz.Prism.FaceCompatibleHomotopies n
      (composeSimplexHomotopies H G hH₀ hG₀) (composeSimplexHomotopies H' G' hH'₀ hG'₀) := by
  intro smp i
  unfold composeSimplexHomotopies
  rw [homotopyTrans_compContinuousMap]
  apply homotopyTrans_congr
  · change
      (H' smp).comp ((ContinuousMap.id (unitInterval)).prodMap (SingularChains.simplexFace n i)) =
        H (smp.comp (SingularChains.simplexFace n i))
    exact hH smp i
  · change
      (G' (Hurewicz.Prism.timeSlice (H' smp) 1)).comp
          ((ContinuousMap.id (unitInterval)).prodMap (SingularChains.simplexFace n i)) =
        G
          (Hurewicz.Prism.timeSlice (H (smp.comp (SingularChains.simplexFace n i)))
            1)
    rw [hG (Hurewicz.Prism.timeSlice (H' smp) 1) i,
      Hurewicz.Prism.timeSlice_face hH smp i 1]

/-- If `H` and `G` are both stationary on the constant simplex at `x`, so is
their composition on the constant simplex. -/
theorem Hurewicz.composeSimplexHomotopies_const {X : Type} [TopologicalSpace X] {n : ℕ}
    (H G : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s) (hG₀ : ∀ smp s, G smp (0, s) = smp s) (x : X)
    (hH :
      H (ContinuousMap.const (SingularChains.Simplex n) x) =
        ContinuousMap.const ((unitInterval) × SingularChains.Simplex n) x)
    (hG :
      G (ContinuousMap.const (SingularChains.Simplex n) x) =
        ContinuousMap.const ((unitInterval) × SingularChains.Simplex n) x) :
    composeSimplexHomotopies H G hH₀ hG₀ (ContinuousMap.const (SingularChains.Simplex n) x) =
      ContinuousMap.const ((unitInterval) × SingularChains.Simplex n) x := by
  have h₁ :
    Hurewicz.Prism.timeSlice (H (ContinuousMap.const (SingularChains.Simplex n) x))
        1 =
      ContinuousMap.const (SingularChains.Simplex n) x := by
    rw [hH]
    rfl
  unfold composeSimplexHomotopies
  apply homotopyTrans_const
  · exact hH
  · change
      G
          (Hurewicz.Prism.timeSlice
            (H (ContinuousMap.const (SingularChains.Simplex n) x)) 1) =
        _
    rw [h₁]
    exact hG

/-- The glued boundary map of a constant family is the constant map. -/
theorem Hurewicz.gluedBoundaryMap_constant_value {X : Type} [TopologicalSpace X] {n : ℕ}
    (f : C(SingularChains.Simplex n, X))
    (g : C((unitInterval) × Hurewicz.DegreeTwo.SimplyConnected.SimplexBoundary n, X))
    (h₀ : ∀ s, g (0, s) = f s.val) (x : X) (hf : ∀ s, f s = x) (hg : ∀ u, g u = x)
    (u : ↥(Hurewicz.DegreeTwo.SimplyConnected.bottomOrSide n)) :
    Hurewicz.DegreeTwo.SimplyConnected.gluedBoundaryMap f g h₀ u = x := by
  rcases u.property with hb | hs
  · have hu : u = Hurewicz.DegreeTwo.SimplyConnected.bottomInclusion n u.val.2 := by
      apply Subtype.ext
      exact Prod.ext hb rfl
    exact
      (congrArg (Hurewicz.DegreeTwo.SimplyConnected.gluedBoundaryMap f g h₀) hu).trans
        ((Hurewicz.DegreeTwo.SimplyConnected.gluedBoundaryMap_bottomInclusion f g h₀ _).trans (hf _))
  · have hu : u = Hurewicz.DegreeTwo.SimplyConnected.sideInclusion n (u.val.1, ⟨u.val.2, hs⟩) := by
      apply Subtype.ext
      rfl
    exact
      (congrArg (Hurewicz.DegreeTwo.SimplyConnected.gluedBoundaryMap f g h₀) hu).trans
        ((Hurewicz.DegreeTwo.SimplyConnected.gluedBoundaryMap_sideInclusion f g h₀ _).trans (hg _))

/-- The coherent boundary homotopy of the constant family is stationary. -/
theorem Hurewicz.coherentFaceBoundaryHomotopy_const {X : Type} [TopologicalSpace X] {n : ℕ}
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (h : Hurewicz.Prism.FaceCompatibleHomotopies n H H') (x : X)
    (hc :
      H' (ContinuousMap.const (SingularChains.Simplex (n + 1)) x) =
        ContinuousMap.const ((unitInterval) × SingularChains.Simplex (n + 1)) x) :
    Hurewicz.DegreeTwo.SimplyConnected.coherentFaceBoundaryHomotopy H H' h
        (ContinuousMap.const (SingularChains.Simplex (n + 2)) x) =
      ContinuousMap.const
        ((unitInterval) × Hurewicz.DegreeTwo.SimplyConnected.SimplexBoundary (n + 2)) x := by
  unfold Hurewicz.DegreeTwo.SimplyConnected.coherentFaceBoundaryHomotopy
  apply
    (Hurewicz.DegreeTwo.SimplyConnected.glueFaceHomotopies_unique _ _ (ContinuousMap.const _ x)
        ?_).symm
  intro i r s
  change x = H' (ContinuousMap.const (SingularChains.Simplex (n + 1)) x) (r, s)
  rw [hc]
  rfl

/-- The coherent extension of the constant family is stationary. -/
theorem Hurewicz.extendCoherentSimplexHomotopy_const {X : Type} [TopologicalSpace X] {n : ℕ}
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (h : Hurewicz.Prism.FaceCompatibleHomotopies n H H')
    (h₀ : ∀ smp s, H' smp (0, s) = smp s) (x : X)
    (hc :
      H' (ContinuousMap.const (SingularChains.Simplex (n + 1)) x) =
        ContinuousMap.const ((unitInterval) × SingularChains.Simplex (n + 1)) x) :
    Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy H H' h h₀
        (ContinuousMap.const (SingularChains.Simplex (n + 2)) x) =
      ContinuousMap.const ((unitInterval) × SingularChains.Simplex (n + 2)) x := by
  unfold Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy
  ext u
  change
    Hurewicz.DegreeTwo.SimplyConnected.gluedBoundaryMap
        (ContinuousMap.const (SingularChains.Simplex (n + 2)) x)
        (Hurewicz.DegreeTwo.SimplyConnected.coherentFaceBoundaryHomotopy H H' h
          (ContinuousMap.const (SingularChains.Simplex (n + 2)) x))
        (Hurewicz.DegreeTwo.SimplyConnected.coherentFaceBoundaryHomotopy_zero H H' h h₀
          (ContinuousMap.const (SingularChains.Simplex (n + 2)) x))
        (Hurewicz.DegreeTwo.SimplyConnected.cylinderRetraction (n + 2) u) =
      x
  apply gluedBoundaryMap_constant_value _ _ _ x (fun _ => rfl)
  intro v
  exact
    congrArg
      (fun F : C((unitInterval) × Hurewicz.DegreeTwo.SimplyConnected.SimplexBoundary (n + 2), X) =>
        F v)
      (coherentFaceBoundaryHomotopy_const H H' h x hc)
