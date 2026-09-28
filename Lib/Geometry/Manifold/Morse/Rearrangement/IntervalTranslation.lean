/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.Existence
public import Lib.Geometry.Manifold.RegularLevel
public import Lib.Geometry.Manifold.WhitneyEmbedding
public import Lib.Geometry.Manifold.Collar
public import Lib.Geometry.Manifold.Morse.SurgeryWindows
public import Lib.Geometry.Manifold.Morse.CubicFlow
public import Lib.Geometry.Manifold.Transversality.Basic
public import Lib.Geometry.Manifold.Immersion.Relative
public import Lib.Geometry.Manifold.LocalDiffeomorph
/-!
# Supported translations of an interval and blended heights

`MorseRearrangement.IntervalTranslation a b x y` says that some diffeomorphism `D` of `ℝ`
is the identity outside `Ioo a b` and equals the translation `z ↦ z + (y - x)` near `x`.
The relation is reflexive, symmetric and transitive (`intervalTranslation_refl`, `_symm`,
`_trans`) and locally constant in `y` (`exists_local_interval_translation`, built from a bump
function and `SmallPerturbation`), so on the connected interval any two interior points are
related (`exists_supported_interval_translation`). A diffeomorphism of `ℝ` fixed outside an
interval is strictly increasing with positive derivative (`strictMono_of_fixed_exterior`,
`deriv_pos_of_strictMono_diffeomorph`); the main statement
`exists_increasing_interval_translation_with_exterior_germs` collects: `D` fixed outside
`Ioo a b`, `D = (· + (y - x))` near `x`, `D x = y`, `StrictMono D`, `0 < deriv D`, and
`D = id` near every point outside `Ioo a b`.

`blendHeight θ P Q s = θ * P s + (1 - θ) * Q s` is the convex blend of two height functions;
the blended slope is positive when both slopes are (`positive_blended_slope`), and
`hasDerivAt_blended_height` gives the derivative of `s ↦ blendHeight (θ s) P Q (f s)` where
`θ` is locally constant.

This is the one-dimensional ingredient of the rearrangement theorem: the new Morse function on
a band is `G ∘ f` for a monotone `G : ℝ → ℝ` moving one critical value past another
(Milnor, *Lectures on the h-cobordism theorem*, §4, proof of Theorem 4.1).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-! ### Interval translations -/

/-- A compactly supported translation of the interval. -/
def MorseRearrangement.IntervalTranslation (a b x y : ℝ) : Prop :=
  ∃ D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
    (∀ z, z ∉ Set.Ioo a b → D z = z) ∧ D =ᶠ[𝓝 x] fun z => z + (y - x)

/-- The translation germ computes the shifted value. -/
theorem MorseRearrangement.translation_germ_apply (D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞)
    {x y : ℝ} (hD : D =ᶠ[𝓝 x] fun z => z + (y - x)) : D x = y := by
  have h := hD.self_of_nhds
  linarith

/-- The identity interval translation. -/
theorem MorseRearrangement.intervalTranslation_refl (a b x : ℝ) :
    IntervalTranslation a b x x := by
  refine ⟨Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞, fun _ _ => rfl, Filter.Eventually.of_forall ?_⟩
  intro z
  change z = z + (x - x)
  ring

/-- The inverse of an interval translation. -/
theorem MorseRearrangement.intervalTranslation_symm {a b x y : ℝ}
    (h : IntervalTranslation a b x y) : IntervalTranslation a b y x := by
  obtain ⟨D, hfix, hgerm⟩ := h
  have hxy := translation_germ_apply D hgerm
  have hback : D.symm y = x := by rw [← hxy, D.symm_apply_apply]
  have ht : Filter.Tendsto D.symm (𝓝 y) (𝓝 x) := hback ▸ D.symm.continuous.continuousAt.tendsto
  refine ⟨D.symm, ?_, ?_⟩
  · intro z hz
    have hh := D.symm_apply_apply z
    rwa [hfix z hz] at hh
  · filter_upwards [hgerm.comp_tendsto ht] with z hz
    change D (D.symm z) = D.symm z + (y - x) at hz
    rw [D.apply_symm_apply] at hz
    linarith

/-- Composition of interval translations. -/
theorem MorseRearrangement.intervalTranslation_trans {a b x y z : ℝ}
    (hxy : IntervalTranslation a b x y) (hyz : IntervalTranslation a b y z) :
    IntervalTranslation a b x z := by
  obtain ⟨D, hDfix, hD⟩ := hxy
  obtain ⟨G, hGfix, hG⟩ := hyz
  have hxy := translation_germ_apply D hD
  have ht : Filter.Tendsto D (𝓝 x) (𝓝 y) := hxy ▸ D.continuous.continuousAt.tendsto
  refine ⟨D.trans G, ?_, ?_⟩
  · intro w hw
    change G (D w) = w
    rw [hDfix w hw, hGfix w hw]
  · filter_upwards [hD, hG.comp_tendsto ht] with w hwD hwG
    change G (D w) = w + (z - x)
    change G (D w) = D w + (z - y) at hwG
    rw [hwG, hwD]
    ring

/-- A local value extends to a supported interval translation. -/
theorem MorseRearrangement.exists_local_interval_translation {a b x : ℝ}
    (hx : x ∈ Set.Ioo a b) : ∃ ε, 0 < ε ∧ ∀ y, Dist.dist y x < ε → IntervalTranslation a b x y := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (isOpen_Ioo.mem_nhds hx)
  let β : ContDiffBump x := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hsupp : tsupport (fun z : ℝ => β z) ⊆ Set.Ioo a b := by
    rw [β.tsupport_eq]
    intro z hz
    apply hsub
    have hh : Dist.dist z x ≤ r / 2 := hz
    change Dist.dist z x < r
    linarith
  have hcompact : HasCompactSupport (fun z : ℝ => β z) := by
    change IsCompact (tsupport (fun z : ℝ => β z))
    rw [β.tsupport_eq]
    exact ProperSpace.isCompact_closedBall _ _
  obtain ⟨ε, hε, hmove⟩ :=
    SmallPerturbation.exists_radius_bumpTranslation β.contDiff hcompact
  refine ⟨ε, hε, ?_⟩
  intro y hy
  have hnorm : ‖y - x‖ < ε := by simpa only [dist_eq_norm] using hy
  obtain ⟨D, hD, hfix⟩ := hmove (y - x) hnorm
  refine ⟨D, fun z hz => hfix z (fun h => hz (hsupp h)), ?_⟩
  filter_upwards [Metric.ball_mem_nhds x β.rIn_pos] with z hz
  rw [hD, β.one_of_mem_closedBall (Metric.ball_subset_closedBall hz), one_smul]

/-- An interval translation supported on a compact interval. -/
theorem MorseRearrangement.exists_supported_interval_translation {a b x y : ℝ}
    (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo a b) : IntervalTranslation a b x y := by
  let U := Set.Ioo a b
  let P : U → Prop := fun z => IntervalTranslation a b x z
  have hlocal : IsLocallyConstant P := by
    apply (IsLocallyConstant.iff_eventually_eq P).mpr
    intro z
    obtain ⟨ε, hε, hmove⟩ := exists_local_interval_translation z.property
    filter_upwards [Metric.ball_mem_nhds z hε] with w hw
    have hzw : IntervalTranslation a b z w := hmove w hw
    apply propext
    exact
      ⟨fun hw => intervalTranslation_trans hw (intervalTranslation_symm hzw), fun hz =>
        intervalTranslation_trans hz hzw⟩
  let _ : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  have heq : P ⟨x, hx⟩ = P ⟨y, hy⟩ := hlocal.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩
  have hstart : P ⟨x, hx⟩ := intervalTranslation_refl a b x
  have hfinish : P ⟨y, hy⟩ := heq ▸ hstart
  exact hfinish

/-- A diffeomorphism fixed outside an interval is strictly monotone on it. -/
theorem MorseRearrangement.strictMono_of_fixed_exterior
    (D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞) {a b : ℝ} (hfix : ∀ z, z ∉ Set.Ioo a b → D z = z) :
    StrictMono D := by
  rcases D.continuous.strictMono_of_inj D.injective with hm | ha
  · exact hm
  · have hanti := ha (show b < b + 1 by linarith)
    rw [hfix b (fun h => (lt_irrefl b) h.2), hfix (b + 1) (fun h => by linarith [h.2])] at hanti
    linarith

/-- A strictly monotone diffeomorphism has positive derivative. -/
theorem MorseRearrangement.deriv_pos_of_strictMono_diffeomorph
    (D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞) (hm : StrictMono D) (x : ℝ) : 0 < deriv D x := by
  have hd := (D.mdifferentiable (by simp) x).differentiableAt.hasDerivAt
  have hi := (D.symm.mdifferentiable (by simp) (D x)).differentiableAt.hasDerivAt
  have hc := hi.comp x hd
  have heq : D.symm ∘ D = id := funext D.symm_apply_apply
  rw [heq] at hc
  have hh := hc.unique (hasDerivAt_id x)
  have hn : deriv D x ≠ 0 := by
    intro hz
    rw [hz, MulZeroClass.mul_zero] at hh
    norm_num at hh
  exact lt_of_le_of_ne hm.monotone.deriv_nonneg (Ne.symm hn)

/-- An increasing supported translation of the interval. -/
theorem MorseRearrangement.exists_increasing_interval_translation {a b x y : ℝ}
    (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo a b) :
    ∃ D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      (∀ z, z ∉ Set.Ioo a b → D z = z) ∧
        (D =ᶠ[𝓝 x] fun z => z + (y - x)) ∧ D x = y ∧ StrictMono D ∧ ∀ z, 0 < deriv D z := by
  obtain ⟨D, hfix, hgerm⟩ := exists_supported_interval_translation hx hy
  have hm := strictMono_of_fixed_exterior D hfix
  exact
    ⟨D, hfix, hgerm, translation_germ_apply D hgerm, hm, deriv_pos_of_strictMono_diffeomorph D hm⟩

/-- An increasing translation with prescribed exterior germs. -/
theorem MorseRearrangement.exists_increasing_interval_translation_with_exterior_germs
    {a b x y : ℝ} (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo a b) :
    ∃ D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      (∀ z, z ∉ Set.Ioo a b → D z = z) ∧
        (D =ᶠ[𝓝 x] fun z => z + (y - x)) ∧
          D x = y ∧ StrictMono D ∧ (∀ z, 0 < deriv D z) ∧ ∀ z, z ∉ Set.Ioo a b → D =ᶠ[𝓝 z] id := by
  obtain ⟨a', haa', ha'⟩ := exists_between (lt_min hx.1 hy.1)
  obtain ⟨b', hb', hb'b⟩ := exists_between (max_lt hx.2 hy.2)
  have hx' : x ∈ Set.Ioo a' b' := ⟨ha'.trans_le (min_le_left _ _), (le_max_left _ _).trans_lt hb'⟩
  have hy' : y ∈ Set.Ioo a' b' :=
    ⟨ha'.trans_le (min_le_right _ _), (le_max_right _ _).trans_lt hb'⟩
  obtain ⟨D, hfix, hgerm, hpoint, hmono, hderiv⟩ := exists_increasing_interval_translation hx' hy'
  have hsub : Set.Icc a' b' ⊆ Set.Ioo a b := fun z hz => ⟨haa'.trans_le hz.1, hz.2.trans_lt hb'b⟩
  have hout (z : ℝ) (hz : z ∉ Set.Ioo a b) : D =ᶠ[𝓝 z] id := by
    have hz' : z ∈ (Set.Icc a' b')ᶜ := fun h => hz (hsub h)
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hz'] with w hw
    exact hfix w (fun h => hw ⟨h.1.le, h.2.le⟩)
  exact ⟨D, fun z hz => (hout z hz).self_of_nhds, hgerm, hpoint, hmono, hderiv, hout⟩

/-! ### Blending heights -/

/-- The convex blend of two height functions along a cutoff. -/
def MorseRearrangement.blendHeight (θ : ℝ) (P Q : ℝ → ℝ) (s : ℝ) : ℝ :=
  θ * P s + (1 - θ) * Q s

/-- At cutoff zero the blend is the first height. -/
theorem MorseRearrangement.blendHeight_zero (P Q : ℝ → ℝ) (s : ℝ) :
    blendHeight 0 P Q s = Q s := by simp [blendHeight]

/-- At cutoff one the blend is the second height. -/
theorem MorseRearrangement.blendHeight_one (P Q : ℝ → ℝ) (s : ℝ) :
    blendHeight 1 P Q s = P s := by simp [blendHeight]

/-- Where the heights agree the blend is fixed. -/
theorem MorseRearrangement.blendHeight_fixed {P Q : ℝ → ℝ} {s : ℝ} (hP : P s = s)
    (hQ : Q s = s) (θ : ℝ) : blendHeight θ P Q s = s := by
  rw [blendHeight, hP, hQ]
  ring

/-- The blended slope stays positive when both slopes are. -/
theorem MorseRearrangement.positive_blended_slope {θ a b : ℝ} (hθ : θ ∈ Set.Icc 0 1)
    (ha : 0 < a) (hb : 0 < b) : 0 < θ * a + (1 - θ) * b := by
  by_cases hzero : θ = 0
  · simpa only [hzero, MulZeroClass.zero_mul, sub_zero, one_mul, zero_add] using hb
  · exact
      add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne hθ.1 (Ne.symm hzero)) ha)
        (mul_nonneg (sub_nonneg.mpr hθ.2) hb.le)

/-- The blended height has the blended derivative. -/
theorem MorseRearrangement.hasDerivAt_blended_height {f θ P Q : ℝ → ℝ} {t f' p' q' : ℝ}
    (hf : HasDerivAt f f' t) (hθ : HasDerivAt θ 0 t) (hP : HasDerivAt P p' (f t))
    (hQ : HasDerivAt Q q' (f t)) :
    HasDerivAt (fun s => blendHeight (θ s) P Q (f s)) ((θ t * p' + (1 - θ t) * q') * f') t := by
  convert!
    (hθ.mul (hP.comp t hf)).add (((hasDerivAt_const t (1 : ℝ)).sub hθ).mul (hQ.comp t hf)) using 1
  simp only [Pi.sub_apply]
  ring
