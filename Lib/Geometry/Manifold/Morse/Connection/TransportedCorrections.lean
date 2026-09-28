/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Rearrangement

/-!
# Transport of supported isotopies through transverse charts

* `compose_supported_isotopies`: two supported relative isotopies (from the identity to `D₁`
  and to `D₂`, supported in `K₁`, `K₂`, fixed on `S`) compose to one from the identity to
  `D₁.trans D₂` supported in `K₁ ∪ K₂`.
* `exists_transported_transition_correction`: given charts `Q P : E → Z` and a transition `H`
  with `P ∘ H = Q`, supported isotopies `Dₛ` on the source and `Dₜ` on the target are pushed
  forward to a supported isotopy `D` of `Z` fixing `0` with `D (Q z) = P (Dₜ (H (Dₛ z)))`.
* `exists_common_transverse_range`, `exists_common_transverse_coordinates`: two charts of
  `Z` around `0` can be restricted to a common target `U` and related by the transition
  `H = e ∘ P⁻¹ ∘ Q ∘ e⁻¹`.
* `exists_restricted_native_cylinder`: a vertical flow-box chart restricts to an open subset of
  its base.

cf. Milnor, *Lectures on the h-cobordism theorem*, §5 (the modification of the field is an
isotopy of a level surface supported in a compact set).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff NNReal

noncomputable section

/-! ### Transported corrections -/

/-- Supported isotopies compose. -/
def TransverseGerms.compose_supported_isotopies {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {D₁ D₂ : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞} {K₁ K₂ S : Set E}
    (A : SupportedDiffeomorph.SupportedRelativeIsotopy D₁ K₁ S)
    (B : SupportedDiffeomorph.SupportedRelativeIsotopy D₂ K₂ S) :
    SupportedDiffeomorph.SupportedRelativeIsotopy (D₁.trans D₂) (K₁ ∪ K₂) S
    where
  family := fun p => B.family (p.1, A.family p)
  smooth := B.smooth.comp (contMDiff_fst.prodMk A.smooth)
  zero := fun x => by rw [A.zero, B.zero]
  one := fun x => by change B.family (1, A.family (1, x)) = D₂ (D₁ x); rw [A.one, B.one]
  slices := by
    intro t
    obtain ⟨d₁, hd₁⟩ := A.slices t
    obtain ⟨d₂, hd₂⟩ := B.slices t
    refine ⟨d₁.trans d₂, ?_⟩
    intro x
    change d₂ (d₁ x) = B.family (t, A.family (t, x))
    rw [hd₁, hd₂]
  fixedOutside := by
    intro t x hx
    rw [A.fixedOutside t x (fun h => hx (Or.inl h)), B.fixedOutside t x (fun h => hx (Or.inr h))]
  fixedOn := by
    intro t x hx
    rw [A.fixedOn t x hx, B.fixedOn t x hx]

attribute [local instance 100] Classical.propDecidable in
/-- A transported transition correction exists. -/
theorem TransverseGerms.exists_transported_transition_correction {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q P : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Z) E Z ∞)
    (H : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (hQ0 : (0 : E) ∈ Q.source)
    (hP0 : (0 : E) ∈ P.source) (hQzero : Q 0 = 0) (hPzero : P 0 = 0) (hHs : H.source ⊆ Q.source)
    (hHt : H.target ⊆ P.source) (hdiagram : ∀ z ∈ H.source, P (H z) = Q z)
    (Dₛ Dₜ : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) {Kₛ Kₜ Sₛ Sₜ : Set E} (hKₛ : IsCompact Kₛ)
    (hKₜ : IsCompact Kₜ) (hKs : Kₛ ⊆ H.source) (hKt : Kₜ ⊆ H.target) (hSₛ : (0 : E) ∈ Sₛ)
    (hSₜ : (0 : E) ∈ Sₜ) (A : SupportedDiffeomorph.SupportedRelativeIsotopy Dₛ Kₛ Sₛ)
    (B : SupportedDiffeomorph.SupportedRelativeIsotopy Dₜ Kₜ Sₜ) :
    ∃ (D : Diffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) Z Z ∞) (K : Set Z),
      IsCompact K ∧
        K = Q '' Kₛ ∪ P '' Kₜ ∧
          K ⊆ Q.target ∩ P.target ∧
            Nonempty (SupportedDiffeomorph.SupportedRelativeIsotopy D K {(0 : Z)}) ∧
              D 0 = 0 ∧ ∀ z ∈ H.source, D (Q z) = P (Dₜ (H (Dₛ z))) := by
  have hKQ : Kₛ ⊆ Q.source := hKs.trans hHs
  have hKP : Kₜ ⊆ P.source := hKt.trans hHt
  have hfixedQ (z : E) (hz : z ∈ Q.source) (h : Q z ∈ ({(0 : Z)} : Set Z)) : z ∈ Sₛ := by
    have he : z = 0 :=
      Q.toOpenPartialHomeomorph.injOn hz hQ0 ((Set.mem_singleton_iff.mp h).trans hQzero.symm)
    exact he.symm ▸ hSₛ
  have hfixedP (z : E) (hz : z ∈ P.source) (h : P z ∈ ({(0 : Z)} : Set Z)) : z ∈ Sₜ := by
    have he : z = 0 :=
      P.toOpenPartialHomeomorph.injOn hz hP0 ((Set.mem_singleton_iff.mp h).trans hPzero.symm)
    exact he.symm ▸ hSₜ
  let A' := A.extension Q hKₛ hKQ hfixedQ
  let B' := B.extension P hKₜ hKP hfixedP
  let DQ := SupportedDiffeomorph.extension Q Dₛ hKₛ hKQ A.endpoint_fixed_outside
  let DP := SupportedDiffeomorph.extension P Dₜ hKₜ hKP B.endpoint_fixed_outside
  let D := DQ.trans DP
  let K := Q '' Kₛ ∪ P '' Kₜ
  have hK : IsCompact K :=
    (hKₛ.image_of_continuousOn (Q.contMDiffOn_toFun.continuousOn.mono hKQ)).union
      (hKₜ.image_of_continuousOn (P.contMDiffOn_toFun.continuousOn.mono hKP))
  have I : SupportedDiffeomorph.SupportedRelativeIsotopy D K {(0 : Z)} :=
    compose_supported_isotopies A' B'
  have hKU : K ⊆ Q.target ∩ P.target := by
    rintro y (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    · refine ⟨Q.map_source' (hKQ hz), ?_⟩
      rw [← hdiagram z (hKs hz)]
      exact P.map_source' (hHt (H.map_source' (hKs hz)))
    · refine ⟨?_, P.map_source' (hKP hz)⟩
      have hh := hdiagram (H.symm z) (H.map_target' (hKt hz))
      have hi : H (H.symm z) = z := H.right_inv' (hKt hz)
      rw [hi] at hh
      rw [hh]
      exact Q.map_source' (hHs (H.map_target' (hKt hz)))
  refine ⟨D, K, hK, rfl, hKU, ⟨I⟩, I.endpoint_fixed_on 0 rfl, ?_⟩
  intro z hz
  have hDz : Dₛ z ∈ H.source :=
    SupportedDiffeomorph.mapsTo_source H Dₛ.toEquiv hKs A.endpoint_fixed_outside hz
  change DP (DQ (Q z)) = P (Dₜ (H (Dₛ z)))
  rw [SupportedDiffeomorph.extension_chart Q Dₛ hKₛ hKQ A.endpoint_fixed_outside (hHs hz)]
  rw [← hdiagram (Dₛ z) hDz]
  exact
    SupportedDiffeomorph.extension_chart P Dₜ hKₜ hKP B.endpoint_fixed_outside
      (hHt (H.map_source' hDz))

attribute [local instance 100] Classical.propDecidable in
/-- A common transverse range exists. -/
theorem TransverseGerms.exists_common_transverse_range {E Z : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q P : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Z) E Z ∞)
    (H : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (h0 : (0 : E) ∈ H.source) (hQzero : Q 0 = 0)
    (hHs : H.source ⊆ Q.source) (hHt : H.target ⊆ P.source)
    (hdiagram : ∀ z ∈ H.source, P (H z) = Q z) :
    ∃ (Q' P' : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Z) E Z ∞) (U : Set Z),
      IsOpen U ∧
        (0 : Z) ∈ U ∧
          Q'.source = H.source ∧
            P'.source = H.target ∧
              Q'.target = U ∧
                P'.target = U ∧ U ⊆ Q.target ∩ P.target ∧ (∀ z, Q' z = Q z) ∧ (∀ z, P' z = P z) :=
  by
  let Q' := PartialChart.restrictSource Q H.open_source
  let P' := PartialChart.restrictSource P H.open_target
  have hQs : Q'.source = H.source := Set.inter_eq_right.mpr hHs
  have hPs : P'.source = H.target := Set.inter_eq_right.mpr hHt
  have hsame : Q'.target = P'.target := by
    ext y
    constructor
    · intro hy
      have hz : Q'.symm y ∈ H.source := hQs ▸ Q'.map_target' hy
      have hw : H (Q'.symm y) ∈ P'.source := hPs.symm ▸ H.map_source' hz
      have heq : P' (H (Q'.symm y)) = y := (hdiagram _ hz).trans (Q'.right_inv' hy)
      exact heq ▸ P'.map_source' hw
    · intro hy
      have hz : P'.symm y ∈ H.target := hPs ▸ P'.map_target' hy
      have hw : H.symm (P'.symm y) ∈ Q'.source := hQs.symm ▸ H.map_target' hz
      have heq : Q' (H.symm (P'.symm y)) = y := by
        have hh := hdiagram (H.symm (P'.symm y)) (H.map_target' hz)
        have hi : H (H.symm (P'.symm y)) = P'.symm y := H.right_inv' hz
        rw [hi] at hh
        exact hh.symm.trans (P'.right_inv' hy)
      exact heq ▸ Q'.map_source' hw
  have h0U : (0 : Z) ∈ Q'.target := by
    have hh := Q'.map_source' (hQs.symm ▸ h0)
    change Q 0 ∈ Q'.target at hh
    rwa [hQzero] at hh
  refine
    ⟨Q', P', Q'.target, Q'.open_target, h0U, hQs, hPs, rfl, hsame.symm, ?_, fun _ => rfl, fun _ =>
      rfl⟩
  intro y hy
  have hyP : y ∈ P'.target := hsame ▸ hy
  exact ⟨hy.1, hyP.1⟩

/-- Common transverse coordinates exist. -/
theorem TransverseGerms.exists_common_transverse_coordinates {D B Z : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] (e : D ≃L[ℝ] B)
    (Q P : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, Z) D Z ∞) (hQ0 : (0 : D) ∈ Q.source)
    (hP0 : (0 : D) ∈ P.source) (hQfix : Q 0 = 0) (hPfix : P 0 = 0) :
    ∃ (Q' P' : PartialDiffeomorph 𝓘(ℝ, B) 𝓘(ℝ, Z) B Z ∞) (H :
      PartialDiffeomorph 𝓘(ℝ, B) 𝓘(ℝ, B) B B ∞) (U : Set Z),
      IsOpen U ∧
        (0 : Z) ∈ U ∧
          (0 : B) ∈ H.source ∧
            H 0 = 0 ∧
              Q' 0 = 0 ∧
                P' 0 = 0 ∧
                  Q'.source = H.source ∧
                    P'.source = H.target ∧
                      Q'.target = U ∧
                        P'.target = U ∧
                          U ⊆ Q.target ∩ P.target ∧
                            (∀ u ∈ Q'.source, e.symm u ∈ Q.source) ∧
                              (∀ u ∈ P'.source, e.symm u ∈ P.source) ∧
                                (∀ u, Q' u = Q (e.symm u)) ∧
                                  (∀ u, P' u = P (e.symm u)) ∧
                                    (∀ u ∈ H.source, P' (H u) = Q' u) ∧
                                      ∀ u, H u = e (P.symm (Q (e.symm u))) := by
  let R := e.symm.toDiffeomorph.toPartialDiffeomorph
  let Qe := R.trans Q
  let Pe := R.trans P
  have hQe0 : (0 : B) ∈ Qe.source := by
    change (0 : B) ∈ Set.univ ∧ e.symm 0 ∈ Q.source
    rw [map_zero]
    exact ⟨Set.mem_univ _, hQ0⟩
  have hPe0 : (0 : B) ∈ Pe.source := by
    change (0 : B) ∈ Set.univ ∧ e.symm 0 ∈ P.source
    rw [map_zero]
    exact ⟨Set.mem_univ _, hP0⟩
  have hQezero : Qe 0 = 0 := by change Q (e.symm 0) = 0; rw [map_zero, hQfix]
  have hPezero : Pe 0 = 0 := by change P (e.symm 0) = 0; rw [map_zero, hPfix]
  let H := Qe.trans Pe.symm
  have h0 : (0 : B) ∈ H.source := by
    refine ⟨hQe0, ?_⟩
    change Qe 0 ∈ Pe.target
    rw [hQezero, ← hPezero]
    exact Pe.map_source' hPe0
  have hH0 : H 0 = 0 := by
    change Pe.symm (Qe 0) = 0
    rw [hQezero, ← hPezero]
    exact Pe.left_inv' hPe0
  have hHs : H.source ⊆ Qe.source := fun _ hu => hu.1
  have hHt : H.target ⊆ Pe.source := fun _ hu => hu.1
  have hdiagram (u : B) (hu : u ∈ H.source) : Pe (H u) = Qe u := Pe.right_inv' hu.2
  obtain ⟨Q', P', U, hU, h0U, hQs, hPs, hQt, hPt, hUsub, hQmap, hPmap⟩ :=
    exists_common_transverse_range Qe Pe H h0 hQezero hHs hHt hdiagram
  refine
    ⟨Q', P', H, U, hU, h0U, h0, hH0, (hQmap 0).trans hQezero, (hPmap 0).trans hPezero, hQs, hPs,
      hQt, hPt, ?_, ?_, ?_, hQmap, hPmap, ?_, fun _ => rfl⟩
  · intro z hz
    exact ⟨(hUsub hz).1.1, (hUsub hz).2.1⟩
  · intro u hu
    exact (hHs (hQs ▸ hu)).2
  · intro u hu
    exact (hHt (hPs ▸ hu)).2
  · intro u hu
    exact (hPmap (H u)).trans ((hdiagram u hu).trans (hQmap u).symm)

/-- A restricted native cylinder exists. -/
theorem TransverseGerms.exists_restricted_native_cylinder {Z E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (A : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞) {U O : Set Z}
    (hsource : A.source = U ×ˢ Set.univ) (hO : IsOpen O) (hOU : O ⊆ U)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hA :
      ∀ y ∈ A.target,
        V y = FlowConstruction.partialChartField A.symm (fun _ : Z × ℝ => (0, 1)) y) :
    ∃ B : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞,
      B.source = O ×ˢ Set.univ ∧
        B.source ⊆ A.source ∧
          B.target ⊆ A.target ∧
            (∀ z, B z = A z) ∧
              ∀ y ∈ B.target,
                V y =
                  FlowConstruction.partialChartField B.symm (fun _ : Z × ℝ => (0, 1)) y := by
  let B := PartialChart.restrictSource A (hO.prod isOpen_univ)
  have hsub : O ×ˢ (Set.univ : Set ℝ) ⊆ A.source := by
    rw [hsource]
    exact fun z hz => ⟨hOU hz.1, hz.2⟩
  have hBs : B.source = O ×ˢ Set.univ := Set.inter_eq_right.mpr hsub
  exact ⟨B, hBs, fun _ hz => hz.1, fun _ hy => hy.1, fun _ => rfl, fun y hy => hA y hy.1⟩

end
