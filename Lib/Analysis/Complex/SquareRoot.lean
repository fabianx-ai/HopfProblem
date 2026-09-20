/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/



import Lib.Analysis.Complex.RiemannMapping
import Lib.Analysis.Complex.RiemannMapping.Steps
import Lib.Analysis.Calculus.MorseLemma
import Lib.Geometry.Manifold.Instances.RiemannSphere
import Mathlib

/-!
# Holomorphic square roots on simply connected domains

A nowhere-zero holomorphic function on a simply connected domain has a holomorphic square
root (Rudin 13.11); here specialized to the analytic root covers used by the source
development (`AnalyticRootCover.*`, `AnalyticRootCoverContinuation.*`), with the
`exists_analytic_unit_root` step.

## Main definitions and results

* `AnalyticRootCover.exists_analytic_square_root`, `.exists_analytic_square_root_ball` :
  square roots of nonvanishing analytic functions on discs/simply connected sets.
* `AnalyticRootCoverContinuation.*` : continuation of the root along cover refinements.
* `AnalyticRootCover.exists_analytic_unit_root` : the unit-root step - an analytic
  `m`-th root of a nonvanishing analytic germ (renamed from the project prefix
  `SpecialPeriods` per review A item 3; no external consumers).

## References

* [Walter Rudin, *Real and Complex Analysis*][rudin87], Theorem 13.11

## Tags

holomorphic square root, simply connected, analytic continuation
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-! ### Local roots and the ambient section -/

/-- An analytic root of a unit exists locally. -/
theorem AnalyticRootCover.exists_analytic_unit_root {g : ℂ → ℂ} {a : ℂ} {m : ℕ}
    (hg : AnalyticAt ℂ g a) (hga : g a ≠ 0) (hm : 0 < m) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r a ∧ r a ≠ 0 ∧ ∀ᶠ w in 𝓝 a, r w ^ m = g w := by
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (g a) hm
  have hb0 : b ≠ 0 := by
    intro h
    apply hga
    rw [← hb, h, zero_pow hm.ne']
  have hpow : AnalyticAt ℂ (fun w : ℂ => w ^ m) b := analyticAt_id.pow m
  have hderiv : deriv (fun w : ℂ => w ^ m) b ≠ 0 := by
    rw [deriv_pow_field]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hm.ne') (pow_ne_zero _ hb0)
  let R : ℂ → ℂ := hpow.hasStrictDerivAt.localInverse (fun w : ℂ => w ^ m) _ b hderiv
  have hRa : AnalyticAt ℂ R (g a) := by
    rw [← hb]
    exact hpow.analyticAt_localInverse hderiv
  have hRb : R (g a) = b := by
    rw [← hb]
    exact HasStrictFDerivAt.localInverse_apply_image ..
  have hRpow : ∀ᶠ y in 𝓝 (g a), R y ^ m = y := by
    rw [← hb]
    exact hpow.hasStrictDerivAt.eventually_right_inverse hderiv
  refine ⟨fun w => R (g w), hRa.comp hg, ?_, ?_⟩
  · change R (g a) ≠ 0
    rw [hRb]
    exact hb0
  · exact hg.continuousAt.tendsto.eventually hRpow

/-- The ambient value of a section germ. -/
def AnalyticRootCover.ambientVal (S : TopologicalSpace.Opens ℂ) (V : TopologicalSpace.Opens S)
    (x : V) : ℂ :=
  ((x : S) : ℂ)

/-- The ambient value is injective on germs. -/
theorem AnalyticRootCover.ambientVal_injective (S : TopologicalSpace.Opens ℂ)
    (V : TopologicalSpace.Opens S) : Function.Injective (ambientVal S V) :=
  Subtype.val_injective.comp Subtype.val_injective

/-- The ambient open set of the cover. -/
def AnalyticRootCover.ambientOpen (S : TopologicalSpace.Opens ℂ) (V : TopologicalSpace.Opens S) :
    TopologicalSpace.Opens ℂ :=
  ⟨Subtype.val '' (V : Set S), S.isOpen.isOpenMap_subtype_val _ V.isOpen⟩

/-- The ambient value lies in the ambient open. -/
theorem AnalyticRootCover.ambientVal_mem (S : TopologicalSpace.Opens ℂ)
    (V : TopologicalSpace.Opens S) (x : V) : ambientVal S V x ∈ ambientOpen S V :=
  ⟨(x : S), x.2, rfl⟩

/-- Membership in the ambient open. -/
theorem AnalyticRootCover.mem_ambientOpen (S : TopologicalSpace.Opens ℂ)
    (V : TopologicalSpace.Opens S) {z : ℂ} :
    z ∈ ambientOpen S V ↔ ∃ x : V, ambientVal S V x = z := by
  constructor
  · rintro ⟨x, hx, hxz⟩
    exact ⟨⟨x, hx⟩, hxz⟩
  · rintro ⟨x, rfl⟩
    exact ambientVal_mem S V x

/-- A coerced point lies in the ambient open. -/
@[simp]
theorem AnalyticRootCover.coe_mem_ambientOpen (S : TopologicalSpace.Opens ℂ)
    (V : TopologicalSpace.Opens S) (x : S) : (x : ℂ) ∈ ambientOpen S V ↔ x ∈ V := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have he : y = x := Subtype.ext hyx
    subst y
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The section extended to the ambient open. -/
def AnalyticRootCover.extendSection (S : TopologicalSpace.Opens ℂ) (V : TopologicalSpace.Opens S)
    (s : V → ℂ) : ℂ → ℂ :=
  Function.extend (ambientVal S V) s 0

/-- The extended section computes the ambient value. -/
@[simp]
theorem AnalyticRootCover.extendSection_apply (S : TopologicalSpace.Opens ℂ)
    (V : TopologicalSpace.Opens S) (s : V → ℂ) (x : V) :
    extendSection S V s (ambientVal S V x) = s x :=
  (ambientVal_injective S V).extend_apply s 0 x

/-- The extended section agrees with the original. -/
theorem AnalyticRootCover.extendSection_agrees (S : TopologicalSpace.Opens ℂ)
    (V : TopologicalSpace.Opens S) (s : V → ℂ) (f : ℂ → ℂ)
    (hf : ∀ x, s x = f (ambientVal S V x)) : Set.EqOn (extendSection S V s) f (ambientOpen S V) :=
  by
  intro z hz
  obtain ⟨x, rfl⟩ := (mem_ambientOpen S V).mp hz
  rw [extendSection_apply]
  exact hf x

/-- Two extensions agreeing on germs are equal. -/
theorem AnalyticRootCover.extension_agreement (S : TopologicalSpace.Opens ℂ)
    (V : TopologicalSpace.Opens S) (f : ℂ → ℂ) :
    Set.EqOn (extendSection S V (fun x => f (ambientVal S V x))) f (ambientOpen S V) :=
  extendSection_agrees S V _ f (fun _ => rfl)

/-- The restricted extension agrees with the original. -/
theorem AnalyticRootCover.extendSection_restrict_agrees (S : TopologicalSpace.Opens ℂ)
    {U V : TopologicalSpace.Opens S} (i : U ⟶ V) (s : V → ℂ) :
    Set.EqOn (extendSection S U (fun x => s (Set.inclusion i.le x))) (extendSection S V s)
      (ambientOpen S U) := by
  intro z hz
  obtain ⟨x, rfl⟩ := (mem_ambientOpen S U).mp hz
  rw [extendSection_apply]
  exact (extendSection_apply S V s (Set.inclusion i.le x)).symm

/-- The restricted extension eventually equals the original. -/
theorem AnalyticRootCover.extendSection_restrict_eventuallyEq (S : TopologicalSpace.Opens ℂ)
    {U V : TopologicalSpace.Opens S} (i : U ⟶ V) (s : V → ℂ) (x : U) :
    extendSection S U (fun y => s (Set.inclusion i.le y)) =ᶠ[𝓝 (ambientVal S U x)]
      extendSection S V s := by
  filter_upwards [(ambientOpen S U).isOpen.mem_nhds (ambientVal_mem S U x)] with z hz
  exact extendSection_restrict_agrees S i s hz

/-! ### The root presheaf -/

/-- A section whose square is the function. -/
def AnalyticRootCover.IsRootSection (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ)
    {V : TopologicalSpace.Opens S} (s : V → ℂ) : Prop :=
  ∀ x : V, AnalyticAt ℂ (extendSection S V s) (ambientVal S V x) ∧ s x ^ 2 = F (ambientVal S V x)

/-- The local predicate defining root sections. -/
def AnalyticRootCover.rootLocalPredicate (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ) :
    TopCat.LocalPredicate (fun _ : TopCat.of S => ℂ)
    where
  pred {_} s := IsRootSection S F s
  res {_ _} i s
    hs := by
    intro x
    refine ⟨?_, (hs (Set.inclusion i.le x)).2⟩
    exact (hs (Set.inclusion i.le x)).1.congr (extendSection_restrict_eventuallyEq S i s x).symm
  locality {U} s
    hs := by
    intro x
    obtain ⟨V, hxV, i, hV⟩ := hs x
    let y : V := ⟨(x : S), hxV⟩
    have hix : Set.inclusion i.le y = x := Subtype.ext rfl
    refine ⟨?_, ?_⟩
    · exact (hV y).1.congr (extendSection_restrict_eventuallyEq S i s y)
    · have hsq : s (Set.inclusion i.le y) ^ 2 = F (ambientVal S U x) := (hV y).2
      rwa [hix] at hsq

/-- The presheaf of local square roots. -/
def AnalyticRootCover.rootPresheaf (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ) :
    (TopCat.of S).Presheaf (Type 0) :=
  TopCat.subpresheafToTypes (rootLocalPredicate S F).toPrelocalPredicate

/-- A square-root section of an analytic function. -/
abbrev AnalyticRootCover.RootSection (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ)
    (V : TopologicalSpace.Opens S) :=
  (rootPresheaf S F).obj (Opposite.op V)

/-- A root section is analytic. -/
theorem AnalyticRootCover.rootSection_analytic (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ)
    {V : TopologicalSpace.Opens S} (s : RootSection S F V) (x : V) :
    AnalyticAt ℂ (extendSection S V s.1) (ambientVal S V x) :=
  (s.2 x).1

/-- A root section squares to the function. -/
theorem AnalyticRootCover.rootSection_sq (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ)
    {V : TopologicalSpace.Opens S} (s : RootSection S F V) (x : V) :
    s.1 x ^ 2 = F (ambientVal S V x) :=
  (s.2 x).2

/-- The presheaf restriction computes the extended section. -/
@[simp]
theorem AnalyticRootCover.rootPresheaf_map_apply (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ)
    {U V : TopologicalSpace.Opens S} (i : U ⟶ V) (s : RootSection S F V) (x : U) :
    ((rootPresheaf S F).map i.op s).1 x = s.1 (Set.inclusion i.le x) :=
  rfl

/-- The extended root section is analytic. -/
theorem AnalyticRootCover.RootSection.analyticOnNhd_extend {S : TopologicalSpace.Opens ℂ}
    {F : ℂ → ℂ} {V : TopologicalSpace.Opens S} (s : AnalyticRootCover.RootSection S F V) :
    AnalyticOnNhd ℂ (AnalyticRootCover.extendSection S V s.1)
      (AnalyticRootCover.ambientOpen S V) := by
  intro z hz
  obtain ⟨x, rfl⟩ := (AnalyticRootCover.mem_ambientOpen S V).mp hz
  exact AnalyticRootCover.rootSection_analytic S F s x

/-- The extended section squares to the function. -/
theorem AnalyticRootCover.RootSection.square_eq {S : TopologicalSpace.Opens ℂ} {F : ℂ → ℂ}
    {V : TopologicalSpace.Opens S} (s : AnalyticRootCover.RootSection S F V) {z : ℂ}
    (hz : z ∈ AnalyticRootCover.ambientOpen S V) :
    AnalyticRootCover.extendSection S V s.1 z ^ 2 = F z := by
  obtain ⟨x, rfl⟩ := (AnalyticRootCover.mem_ambientOpen S V).mp hz
  rw [AnalyticRootCover.extendSection_apply]
  exact AnalyticRootCover.rootSection_sq S F s x

/-- Root sections equal on germs are equal. -/
@[ext]
theorem AnalyticRootCover.RootSection.ext {S : TopologicalSpace.Opens ℂ} {F : ℂ → ℂ}
    {V : TopologicalSpace.Opens S} {s t : AnalyticRootCover.RootSection S F V}
    (he : ∀ x, s.1 x = t.1 x) : s = t :=
  Subtype.ext (funext he)

/-- A root section built from an analytic square root. -/
def AnalyticRootCover.rootSectionOfAnalytic (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ)
    {V : TopologicalSpace.Opens S} (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (ambientOpen S V))
    (hsq : ∀ x : V, f (ambientVal S V x) ^ 2 = F (ambientVal S V x)) : RootSection S F V := by
  refine ⟨fun x => f (ambientVal S V x), fun x => ⟨?_, hsq x⟩⟩
  apply (hf _ (ambientVal_mem S V x)).congr
  filter_upwards [(ambientOpen S V).isOpen.mem_nhds (ambientVal_mem S V x)] with z hz
  exact (extension_agreement S V f hz).symm

/-- The extension of an analytic root agrees with it. -/
theorem AnalyticRootCover.extend_rootSectionOfAnalytic_eqOn (S : TopologicalSpace.Opens ℂ)
    (F : ℂ → ℂ) {V : TopologicalSpace.Opens S} (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (ambientOpen S V))
    (hsq : ∀ x : V, f (ambientVal S V x) ^ 2 = F (ambientVal S V x)) :
    Set.EqOn (extendSection S V (rootSectionOfAnalytic S F f hf hsq).1) f (ambientOpen S V) :=
  extension_agreement S V f

/-! ### Uniqueness and existence of local roots -/

/-- A product of analytic functions vanishing gives a vanishing factor. -/
theorem AnalyticRootCover.eventuallyEq_zero_or_eventuallyEq_zero_of_mul_eq_zero {r s : ℂ → ℂ}
    {a : ℂ} (hr : AnalyticAt ℂ r a) (hs : AnalyticAt ℂ s a) (hmul : ∀ᶠ z in 𝓝 a, r z * s z = 0) :
    r =ᶠ[𝓝 a] 0 ∨ s =ᶠ[𝓝 a] 0 := by
  have hfrequent : ∃ᶠ z in 𝓝[≠] a, r z = 0 ∨ s z = 0 := by
    apply (hmul.filter_mono nhdsWithin_le_nhds).frequently.mono
    intro z hz
    exact mul_eq_zero.mp hz
  rcases Filter.frequently_or_distrib.mp hfrequent with hrzero | hszero
  · exact Or.inl (hr.frequently_zero_iff_eventually_zero.mp hrzero)
  · exact Or.inr (hs.frequently_zero_iff_eventually_zero.mp hszero)

/-- Two analytic square roots agree up to sign. -/
theorem AnalyticRootCover.eventuallyEq_or_neg_of_sq_eq {r s : ℂ → ℂ} {a : ℂ}
    (hr : AnalyticAt ℂ r a) (hs : AnalyticAt ℂ s a)
    (hsq : (fun z => r z ^ 2) =ᶠ[𝓝 a] (fun z => s z ^ 2)) :
    r =ᶠ[𝓝 a] s ∨ r =ᶠ[𝓝 a] (fun z => -s z) := by
  have hmul : ∀ᶠ z in 𝓝 a, (r - s) z * (r + s) z = 0 := by
    filter_upwards [hsq] with z hz
    calc
      (r - s) z * (r + s) z = r z ^ 2 - s z ^ 2 := by dsimp; ring
      _ = 0 := sub_eq_zero.mpr hz
  rcases eventuallyEq_zero_or_eventuallyEq_zero_of_mul_eq_zero (hr.sub hs) (hr.add hs) hmul with
    hsub | hadd
  · exact Or.inl (hsub.mono fun z hz => sub_eq_zero.mp hz)
  · exact Or.inr (hadd.mono fun z hz => eq_neg_iff_add_eq_zero.mpr hz)

/-- Two analytic functions on a preconnected set that have equal germs at one point of the set agree on the whole set. -/
theorem AnalyticRootCover.eqOn_of_eventuallyEq {r s : ℂ → ℂ} {V : Set ℂ} {a : ℂ}
    (hr : AnalyticOnNhd ℂ r V) (hs : AnalyticOnNhd ℂ s V) (hV : IsPreconnected V) (ha : a ∈ V)
    (heq : r =ᶠ[𝓝 a] s) : Set.EqOn r s V :=
  hr.eqOn_of_preconnected_of_eventuallyEq hs hV ha heq

/-- An analytic germ of finite even order `2 * n` has a square-root germ of order `n`. -/
theorem AnalyticRootCover.exists_analytic_square_root {F : ℂ → ℂ} {a : ℂ} {n : ℕ}
    (hF : AnalyticAt ℂ F a) (horder : analyticOrderAt F a = (2 * n : ℕ)) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r a ∧ (∀ᶠ z in 𝓝 a, r z ^ 2 = F z) ∧ analyticOrderAt r a = n := by
  obtain ⟨u, hu, hua, hFu⟩ := hF.analyticOrderAt_eq_natCast.mp horder
  obtain ⟨q, hq, hqa, hqpow⟩ :=
    AnalyticRootCover.exists_analytic_unit_root hu hua (by norm_num : 0 < (2 : ℕ))
  let r : ℂ → ℂ := fun z => (z - a) ^ n * q z
  have hr : AnalyticAt ℂ r a := ((analyticAt_id.sub analyticAt_const).pow n).mul hq
  refine ⟨r, hr, ?_, ?_⟩
  · filter_upwards [hFu, hqpow] with z hFz hqz
    change ((z - a) ^ n * q z) ^ 2 = F z
    rw [mul_pow, hqz, ← pow_mul, Nat.mul_comm n 2]
    simpa only [smul_eq_mul] using hFz.symm
  · apply hr.analyticOrderAt_eq_natCast.mpr
    refine ⟨q, hq, hqa, ?_⟩
    exact Filter.Eventually.of_forall (fun _ => rfl)

/-- A square-root germ at a point of finite even analytic order is represented on a sufficiently small ball inside the prescribed neighborhood. -/
theorem AnalyticRootCover.exists_analytic_square_root_ball {F : ℂ → ℂ} {a : ℂ} {n : ℕ} {S : Set ℂ}
    (hF : AnalyticAt ℂ F a) (horder : analyticOrderAt F a = (2 * n : ℕ)) (hS : S ∈ 𝓝 a) :
    ∃ ε > 0,
      ∃ r : ℂ → ℂ,
        Metric.ball a ε ⊆ S ∧
          AnalyticOnNhd ℂ r (Metric.ball a ε) ∧
            Set.EqOn (fun z => r z ^ 2) F (Metric.ball a ε) ∧ analyticOrderAt r a = n := by
  obtain ⟨r, hr, hroot, horderR⟩ := exists_analytic_square_root hF horder
  have hn : {z | z ∈ S ∧ AnalyticAt ℂ r z ∧ r z ^ 2 = F z} ∈ 𝓝 a :=
    Filter.Eventually.and hS (hr.eventually_analyticAt.and hroot)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨ε, hε, r, ?_, ?_, ?_, horderR⟩
  · exact fun z hz => (hball hz).1
  · exact fun z hz => (hball hz).2.1
  · exact fun z hz => (hball hz).2.2

/-! ### The root stalk -/

/-- Germs are equal exactly when the sections eventually agree. -/
theorem AnalyticRootCover.germ_eq_iff_eventuallyEq (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ)
    {U V : TopologicalSpace.Opens (TopCat.of S)} (x : S) (hxU : x ∈ U) (hxV : x ∈ V)
    (s : RootSection S F U) (t : RootSection S F V) :
    (rootPresheaf S F).germ U x hxU s = (rootPresheaf S F).germ V x hxV t ↔
      extendSection S U s.1 =ᶠ[𝓝 (x : ℂ)] extendSection S V t.1 := by
  constructor
  · intro h
    obtain ⟨W, hxW, iU, iV, hst⟩ := (rootPresheaf S F).germ_eq x hxU hxV s t h
    have hxA : (x : ℂ) ∈ ambientOpen S W := ambientVal_mem S W ⟨x, hxW⟩
    filter_upwards [(ambientOpen S W).isOpen.mem_nhds hxA] with z hz
    obtain ⟨y, hyW, rfl⟩ := hz
    have hval := congrArg (fun r : RootSection S F W => r.1 ⟨y, hyW⟩) hst
    rw [rootPresheaf_map_apply, rootPresheaf_map_apply] at hval
    calc
      extendSection S U s.1 (y : ℂ) = s.1 (Set.inclusion iU.le ⟨y, hyW⟩) :=
        extendSection_apply S U s.1 (Set.inclusion iU.le ⟨y, hyW⟩)
      _ = t.1 (Set.inclusion iV.le ⟨y, hyW⟩) := hval
      _ = extendSection S V t.1 (y : ℂ) :=
        (extendSection_apply S V t.1 (Set.inclusion iV.le ⟨y, hyW⟩)).symm
  · intro h
    obtain ⟨A, hA, hAo, hxA⟩ := mem_nhds_iff.mp h
    let B : TopologicalSpace.Opens (TopCat.of S) :=
      TopologicalSpace.Opens.comap ⟨Subtype.val, continuous_subtype_val⟩ ⟨A, hAo⟩
    let W : TopologicalSpace.Opens (TopCat.of S) := (U ⊓ V) ⊓ B
    have hxW : x ∈ W := ⟨⟨hxU, hxV⟩, hxA⟩
    let iU : W ⟶ U := CategoryTheory.homOfLE (inf_le_left.trans inf_le_left)
    let iV : W ⟶ V := CategoryTheory.homOfLE (inf_le_left.trans inf_le_right)
    apply (rootPresheaf S F).germ_ext W hxW iU iV
    apply Subtype.ext
    funext y
    rw [rootPresheaf_map_apply, rootPresheaf_map_apply]
    calc
      s.1 (Set.inclusion iU.le y) = extendSection S U s.1 (ambientVal S W y) :=
        (extendSection_apply S U s.1 (Set.inclusion iU.le y)).symm
      _ = extendSection S V t.1 (ambientVal S W y) := (hA y.2.2)
      _ = t.1 (Set.inclusion iV.le y) := extendSection_apply S V t.1 (Set.inclusion iV.le y)

/-- The negative of a root section. -/
def AnalyticRootCover.RootSection.neg {S : TopologicalSpace.Opens ℂ} {F : ℂ → ℂ}
    {U : TopologicalSpace.Opens S} (s : AnalyticRootCover.RootSection S F U) :
    AnalyticRootCover.RootSection S F U :=
  AnalyticRootCover.rootSectionOfAnalytic S F
    (fun z => -AnalyticRootCover.extendSection S U s.1 z) (analyticOnNhd_extend s).neg
    (fun x => by
      rw [neg_sq]
      exact square_eq s (AnalyticRootCover.ambientVal_mem S U x))

/-- The extension of the negated section is the negated extension. -/
theorem AnalyticRootCover.RootSection.extend_neg_eqOn {S : TopologicalSpace.Opens ℂ} {F : ℂ → ℂ}
    {U : TopologicalSpace.Opens S} (s : AnalyticRootCover.RootSection S F U) :
    Set.EqOn (AnalyticRootCover.extendSection S U s.neg.1)
      (fun z => -AnalyticRootCover.extendSection S U s.1 z) (AnalyticRootCover.ambientOpen S U) :=
  by exact AnalyticRootCover.extend_rootSectionOfAnalytic_eqOn S F _ _ _

/-- A root germ equals the given section or its negative. -/
theorem AnalyticRootCover.germ_eq_or_neg {S : TopologicalSpace.Opens ℂ} {F : ℂ → ℂ}
    {U V : TopologicalSpace.Opens S} (x : S) (hxU : x ∈ U) (hxV : x ∈ V) (s : RootSection S F U)
    (t : RootSection S F V) :
    (rootPresheaf S F).germ V x hxV t = (rootPresheaf S F).germ U x hxU s ∨
      (rootPresheaf S F).germ V x hxV t = (rootPresheaf S F).germ U x hxU s.neg := by
  have hxUA : (x : ℂ) ∈ ambientOpen S U := (coe_mem_ambientOpen S U x).mpr hxU
  have hxVA : (x : ℂ) ∈ ambientOpen S V := (coe_mem_ambientOpen S V x).mpr hxV
  have hsquare :
    (fun z => extendSection S V t.1 z ^ 2) =ᶠ[𝓝 (x : ℂ)] (fun z => extendSection S U s.1 z ^ 2) :=
    by
    filter_upwards [(ambientOpen S U).isOpen.mem_nhds hxUA,
      (ambientOpen S V).isOpen.mem_nhds hxVA] with z hzU hzV
    exact (RootSection.square_eq t hzV).trans (RootSection.square_eq s hzU).symm
  rcases
    eventuallyEq_or_neg_of_sq_eq (RootSection.analyticOnNhd_extend t _ hxVA)
      (RootSection.analyticOnNhd_extend s _ hxUA) hsquare with
    hpos | hneg
  · exact Or.inl ((germ_eq_iff_eventuallyEq S F x hxV hxU t s).mpr hpos)
  · apply Or.inr
    apply (germ_eq_iff_eventuallyEq S F x hxV hxU t s.neg).mpr
    filter_upwards [hneg, (ambientOpen S U).isOpen.mem_nhds hxUA] with z hz hzU
    exact hz.trans (RootSection.extend_neg_eqOn s hzU).symm

/-- The germ map is injective. -/
theorem AnalyticRootCover.germ_injective {S : TopologicalSpace.Opens ℂ} {F : ℂ → ℂ}
    {U : TopologicalSpace.Opens S} (hU : IsPreconnected (ambientOpen S U : Set ℂ)) (x : S)
    (hx : x ∈ U) : Function.Injective ((rootPresheaf S F).germ U x hx) := by
  intro s t hst
  have he :=
    eqOn_of_eventuallyEq (RootSection.analyticOnNhd_extend s) (RootSection.analyticOnNhd_extend t)
      hU ((coe_mem_ambientOpen S U x).mpr hx) ((germ_eq_iff_eventuallyEq S F x hx hx s t).mp hst)
  apply RootSection.ext
  intro y
  simpa only [extendSection_apply] using he (ambientVal_mem S U y)

/-- Every root germ comes from a section. -/
theorem AnalyticRootCover.germ_surjective {S : TopologicalSpace.Opens ℂ} {F : ℂ → ℂ}
    {U : TopologicalSpace.Opens S} (s : RootSection S F U) (x : S) (hx : x ∈ U) :
    Function.Surjective ((rootPresheaf S F).germ U x hx) := by
  intro g
  obtain ⟨V, hxV, t, ht⟩ := (rootPresheaf S F).exists_germ_eq g
  rcases germ_eq_or_neg x hx hxV s t with hpos | hneg
  · exact ⟨s, hpos.symm.trans ht⟩
  · exact ⟨s.neg, hneg.symm.trans ht⟩

/-- The root stalk is bijective with the two roots. -/
theorem AnalyticRootCover.germ_bijective {S : TopologicalSpace.Opens ℂ} {F : ℂ → ℂ}
    {U : TopologicalSpace.Opens S} (hU : IsPreconnected (ambientOpen S U : Set ℂ))
    (s : RootSection S F U) (x : S) (hx : x ∈ U) :
    Function.Bijective ((rootPresheaf S F).germ U x hx) :=
  ⟨germ_injective hU x hx, germ_surjective s x hx⟩

/-- The comap of the ambient open along a subset. -/
theorem AnalyticRootCover.ambientOpen_comap_of_subset (S : TopologicalSpace.Opens ℂ)
    (A : TopologicalSpace.Opens ℂ) (hAS : A ≤ S) :
    ambientOpen S (TopologicalSpace.Opens.comap ⟨Subtype.val, continuous_subtype_val⟩ A) = A := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hz
    exact ⟨⟨z, hAS hz⟩, hz, rfl⟩

/-- A neighborhood where the section is a root exists. -/
theorem AnalyticRootCover.exists_root_neighborhood (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F S) (horder : ∀ a ∈ S, ∃ n : ℕ, analyticOrderAt F a = (2 * n : ℕ))
    (x : S) :
    ∃ U : TopologicalSpace.Opens S,
      x ∈ U ∧ IsPreconnected (ambientOpen S U : Set ℂ) ∧ Nonempty (RootSection S F U) := by
  obtain ⟨n, hn⟩ := horder x x.2
  obtain ⟨ε, hε, r, hball, hr, hsquare, _⟩ :=
    exists_analytic_square_root_ball (hF x x.2) hn (S.isOpen.mem_nhds x.2)
  let A : TopologicalSpace.Opens ℂ := ⟨Metric.ball (x : ℂ) ε, Metric.isOpen_ball⟩
  let U : TopologicalSpace.Opens S :=
    TopologicalSpace.Opens.comap ⟨Subtype.val, continuous_subtype_val⟩ A
  have hUA : ambientOpen S U = A := ambientOpen_comap_of_subset S A hball
  have hxU : x ∈ U := Metric.mem_ball_self hε
  refine ⟨U, hxU, ?_, ?_⟩
  · rw [hUA]
    exact (convex_ball (x : ℂ) ε).isPreconnected
  · have hrU : AnalyticOnNhd ℂ r (ambientOpen S U) := by rwa [hUA]
    refine ⟨rootSectionOfAnalytic S F r hrU (fun y => hsquare ?_)⟩
    have hy := ambientVal_mem S U y
    rwa [hUA] at hy

/-- The root presheaf is locally bijective on stalks. -/
theorem AnalyticRootCover.rootPresheaf_locally_bijective (S : TopologicalSpace.Opens ℂ)
    (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F S)
    (horder : ∀ a ∈ S, ∃ n : ℕ, analyticOrderAt F a = (2 * n : ℕ)) :
    ∀ x : S,
      ∃ U : TopologicalSpace.Opens S,
        x ∈ U ∧ ∀ y (hy : y ∈ U), Function.Bijective ((rootPresheaf S F).germ U y hy) := by
  intro x
  obtain ⟨U, hx, hU, ⟨s⟩⟩ := exists_root_neighborhood S F hF horder x
  exact ⟨U, hx, fun y hy => germ_bijective hU s y hy⟩

/-- The root stalk over a nonzero point is nonempty. -/
theorem AnalyticRootCover.rootStalk_nonempty (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F S) (horder : ∀ a ∈ S, ∃ n : ℕ, analyticOrderAt F a = (2 * n : ℕ))
    (x : S) : Nonempty ((rootPresheaf S F).stalk x) := by
  obtain ⟨U, hx, _, ⟨s⟩⟩ := exists_root_neighborhood S F hF horder x
  exact ⟨(rootPresheaf S F).germ U x hx s⟩

/-- The order of a square root is half the order of the function. -/
theorem AnalyticRootCover.square_root_order {f r : ℂ → ℂ} {a : ℂ} {n : ℕ} (hr : AnalyticAt ℂ r a)
    (heq : (fun z => r z ^ 2) =ᶠ[𝓝 a] f) (horder : analyticOrderAt f a = (2 * n : ℕ)) :
    analyticOrderAt r a = n := by
  have hpow : 2 • analyticOrderAt r a = (2 * n : ℕ) := by
    rw [← analyticOrderAt_pow hr 2]
    exact (analyticOrderAt_congr heq).trans horder
  have hfin : analyticOrderAt r a ≠ ⊤ := by
    intro ht
    simp only [ht, two_nsmul, top_add, ENat.top_ne_natCast] at hpow
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← hk] at hpow
  have hkn : k = n := by
    rw [two_nsmul] at hpow
    have he : k + k = 2 * n := by exact_mod_cast hpow
    omega
  rw [← hk, hkn]

/-- If an analytic function has finite even order at each zero, it has finite even analytic order at every point of the domain. -/
theorem AnalyticRootCover.even_order_at_all_points {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U)
    (hzero : ∀ a ∈ U, f a = 0 → ∃ n : ℕ, analyticOrderAt f a = (2 * n : ℕ)) :
    ∀ a ∈ U, ∃ n : ℕ, analyticOrderAt f a = (2 * n : ℕ) := by
  intro a ha
  by_cases hfa : f a = 0
  · exact hzero a ha hfa
  · exact
      ⟨0, by
        simpa only [MulZeroClass.mul_zero, Nat.cast_zero] using
          (hf a ha).analyticOrderAt_eq_zero.mpr hfa⟩

/-! ### Étale continuation of sections -/

/-- The presheaf defined by a local predicate. -/
abbrev AnalyticRootCoverContinuation.predicatePresheaf {X : TopCat.{0}} {Y : Type}
    (P : TopCat.LocalPredicate (fun _ : X => Y)) : TopCat.Presheaf (Type) X :=
  TopCat.subpresheafToTypes P.toPrelocalPredicate

/-- The value of an étale section germ. -/
def AnalyticRootCoverContinuation.etaleValue {X : TopCat.{0}} {Y : Type}
    (P : TopCat.LocalPredicate (fun _ : X => Y)) (g : (predicatePresheaf P).EtaleSpace) : Y :=
  TopCat.stalkToFiber P g.base g.germ

/-- The germ of a section at a point. -/
def AnalyticRootCoverContinuation.sectionGerm {X : TopCat.{0}} {Y : Type}
    (P : TopCat.LocalPredicate (fun _ : X => Y)) (U : TopologicalSpace.Opens X)
    (s : (predicatePresheaf P).obj (Opposite.op U)) (x : U) : (predicatePresheaf P).EtaleSpace :=
  ⟨x.1, (predicatePresheaf P).germ U x.1 x.2 s⟩

/-- The étale value of a section germ is the value. -/
theorem AnalyticRootCoverContinuation.etaleValue_sectionGerm {X : TopCat.{0}} {Y : Type}
    (P : TopCat.LocalPredicate (fun _ : X => Y)) (U : TopologicalSpace.Opens X)
    (s : (predicatePresheaf P).obj (Opposite.op U)) (x : U) :
    etaleValue P (sectionGerm P U s x) = s.1 x :=
  TopCat.stalkToFiber_germ P U x.1 x.2 s

/-- An étale section is locally the germs of sections. -/
theorem AnalyticRootCoverContinuation.etaleSection_localGerms {X : TopCat.{0}} {Y : Type}
    (P : TopCat.LocalPredicate (fun _ : X => Y)) (σ : C(X, (predicatePresheaf P).EtaleSpace))
    (hσ : ∀ x : X, (σ x).base = x) (x : X) :
    ∃ (U : TopologicalSpace.Opens X) (_hx : x ∈ U) (s :
      (predicatePresheaf P).obj (Opposite.op U)),
      ∀ (y : X) (hy : y ∈ U), σ y = sectionGerm P U s ⟨y, hy⟩ := by
  obtain ⟨U, hxU, s, hs⟩ :=
    TopCat.Presheaf.EtaleSpace.exists_section_of_tendsto (σ.continuous.continuousAt (x := x))
  have hvalues : ∀ᶠ y in 𝓝 x, ∃ hy : y ∈ U, σ y = sectionGerm P U s ⟨y, hy⟩ := by
    filter_upwards [hs] with y hy
    obtain ⟨hyU, hg⟩ := hy
    refine ⟨hσ y ▸ hyU, ?_⟩
    calc
      σ y = sectionGerm P U s ⟨(σ y).base, hyU⟩ := by
        change σ y = ⟨(σ y).base, (predicatePresheaf P).germ U (σ y).base hyU s⟩
        rw [← hg]
      _ = sectionGerm P U s ⟨y, hσ y ▸ hyU⟩ := congrArg (sectionGerm P U s) (Subtype.ext (hσ y))
  obtain ⟨V, hV, hVo, hxV⟩ := eventually_nhds_iff.mp hvalues
  let W : TopologicalSpace.Opens X := ⟨V, hVo⟩
  have hWU : W ≤ U := fun y hy => (hV y hy).choose
  let i : W ⟶ U := CategoryTheory.homOfLE hWU
  refine ⟨W, hxV, (predicatePresheaf P).map i.op s, ?_⟩
  intro y hy
  have hg := (hV y hy).choose_spec
  convert hg using 1
  dsimp only [sectionGerm]
  rw [(predicatePresheaf P).germ_res_apply]

/-- An étale section locally agrees with a section. -/
theorem AnalyticRootCoverContinuation.etaleSection_locally {X : TopCat.{0}} {Y : Type}
    (P : TopCat.LocalPredicate (fun _ : X => Y)) (σ : C(X, (predicatePresheaf P).EtaleSpace))
    (hσ : ∀ x : X, (σ x).base = x) (x : X) :
    ∃ (U : TopologicalSpace.Opens X) (_hx : x ∈ U) (s :
      (predicatePresheaf P).obj (Opposite.op U)),
      ∀ (y : X) (hy : y ∈ U), etaleValue P (σ y) = s.1 ⟨y, hy⟩ := by
  obtain ⟨U, hxU, s, hs⟩ := etaleSection_localGerms P σ hσ x
  refine ⟨U, hxU, s, ?_⟩
  intro y hy
  rw [hs y hy, etaleValue_sectionGerm]

/-- An étale section satisfies the predicate. -/
theorem AnalyticRootCoverContinuation.etaleSection_pred {X : TopCat.{0}} {Y : Type}
    (P : TopCat.LocalPredicate (fun _ : X => Y)) (σ : C(X, (predicatePresheaf P).EtaleSpace))
    (hσ : ∀ x : X, (σ x).base = x) : P.pred (U := ⊤) (fun x => etaleValue P (σ x.1)) := by
  apply P.locality
  intro x
  obtain ⟨U, hxU, s, hs⟩ := etaleSection_locally P σ hσ x.1
  refine ⟨U, hxU, CategoryTheory.homOfLE le_top, ?_⟩
  convert s.2 using 1
  funext y
  exact hs y.1 y.2

/-- A global section built from an étale section. -/
def AnalyticRootCoverContinuation.sectionOfEtaleSection {X : TopCat.{0}} {Y : Type}
    (P : TopCat.LocalPredicate (fun _ : X => Y)) (σ : C(X, (predicatePresheaf P).EtaleSpace))
    (hσ : ∀ x : X, (σ x).base = x) : (predicatePresheaf P).obj (Opposite.op ⊤) :=
  ⟨fun x => etaleValue P (σ x.1), etaleSection_pred P σ hσ⟩

/-- The built section's germ is the étale value. -/
theorem AnalyticRootCoverContinuation.sectionOfEtaleSection_germ {X : TopCat.{0}} {Y : Type}
    (P : TopCat.LocalPredicate (fun _ : X => Y)) (σ : C(X, (predicatePresheaf P).EtaleSpace))
    (hσ : ∀ x : X, (σ x).base = x) (x : X) :
    sectionGerm P ⊤ (sectionOfEtaleSection P σ hσ) ⟨x, trivial⟩ = σ x := by
  obtain ⟨U, hxU, s, hs⟩ := etaleSection_localGerms P σ hσ x
  let i : U ⟶ (⊤ : TopologicalSpace.Opens X) := CategoryTheory.homOfLE le_top
  have heq : (predicatePresheaf P).map i.op (sectionOfEtaleSection P σ hσ) = s := by
    apply Subtype.ext
    funext y
    change etaleValue P (σ y.1) = s.1 y
    rw [hs y.1 y.2, etaleValue_sectionGerm]
  have hg :
    (predicatePresheaf P).germ ⊤ x trivial (sectionOfEtaleSection P σ hσ) =
      (predicatePresheaf P).germ U x hxU s := by
    rw [← (predicatePresheaf P).germ_res_apply i x hxU, heq]
  calc
    sectionGerm P ⊤ (sectionOfEtaleSection P σ hσ) ⟨x, trivial⟩ = sectionGerm P U s ⟨x, hxU⟩ := by
      dsimp only [sectionGerm]
      rw [hg]
    _ = σ x := (hs x hxU).symm

/-- A germ-bijective predicate yields a global section with a prescribed germ. -/
theorem AnalyticRootCoverContinuation.exists_global_section_with_germ_of_germ_bijective
    {X : TopCat.{0}} {Y : Type} [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (P : TopCat.LocalPredicate (fun _ : X => Y))
    (hbij :
      ∀ x : X,
        ∃ U : TopologicalSpace.Opens X,
          x ∈ U ∧ ∀ (y : X) (hy : y ∈ U), Function.Bijective ((predicatePresheaf P).germ U y hy))
    (x₀ : X) (g₀ : (predicatePresheaf P).stalk x₀) :
    ∃ s : (predicatePresheaf P).obj (Opposite.op ⊤),
      (predicatePresheaf P).germ ⊤ x₀ trivial s = g₀ := by
  have hc : IsCoveringMap (TopCat.Presheaf.EtaleSpace.base (F := predicatePresheaf P)) :=
    TopCat.Presheaf.EtaleSpace.isCoveringMap_base hbij
  obtain ⟨σ, hσ, -⟩ := hc.existsUnique_continuousMap_lifts (ContinuousMap.id X) x₀ ⟨x₀, g₀⟩ rfl
  have hbase (x : X) : (σ x).base = x := congrFun hσ.2 x
  refine ⟨sectionOfEtaleSection P σ hbase, ?_⟩
  have hg := (sectionOfEtaleSection_germ P σ hbase x₀).trans hσ.1
  simpa only [sectionGerm, TopCat.Presheaf.EtaleSpace.mk.injEq, heq_eq_eq, true_and] using hg

/-! ### Global square roots -/

/-- The ambient open of the whole space is everything. -/
theorem AnalyticRootCover.ambientOpen_top (S : TopologicalSpace.Opens ℂ) : ambientOpen S ⊤ = S := by
  ext z
  constructor
  · rintro ⟨x, _, rfl⟩
    exact x.2
  · intro hz
    exact ⟨⟨z, hz⟩, trivial, rfl⟩

/-- A global root section with a prescribed germ exists. -/
theorem AnalyticRootCover.exists_global_rootSection_with_germ (S : TopologicalSpace.Opens ℂ)
    (F : ℂ → ℂ) [SimplyConnectedSpace S] (hF : AnalyticOnNhd ℂ F S)
    (horder : ∀ a ∈ S, ∃ n : ℕ, analyticOrderAt F a = (2 * n : ℕ)) (x : S)
    (g : (rootPresheaf S F).stalk x) :
    ∃ s : RootSection S F ⊤, (rootPresheaf S F).germ ⊤ x trivial s = g := by
  let : LocallyPathConnectedSpace S := S.isOpen.locallyPathConnectedSpace
  exact
    AnalyticRootCoverContinuation.exists_global_section_with_germ_of_germ_bijective
      (rootLocalPredicate S F) (rootPresheaf_locally_bijective S F hF horder) x g

/-- A global root section exists. -/
theorem AnalyticRootCover.exists_global_rootSection (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ)
    [SimplyConnectedSpace S] (hF : AnalyticOnNhd ℂ F S)
    (horder : ∀ a ∈ S, ∃ n : ℕ, analyticOrderAt F a = (2 * n : ℕ)) :
    Nonempty (RootSection S F ⊤) := by
  let x : S := Classical.choice inferInstance
  obtain ⟨g⟩ := rootStalk_nonempty S F hF horder x
  obtain ⟨s, _⟩ := exists_global_rootSection_with_germ S F hF horder x g
  exact ⟨s⟩

/-- An analytic function of finite even order at every point of a simply connected open complex domain has an analytic square root, with each order halved. -/
theorem AnalyticRootCover.exists_analytic_square_root_on (S : TopologicalSpace.Opens ℂ)
    (F : ℂ → ℂ) [SimplyConnectedSpace S] (hF : AnalyticOnNhd ℂ F S)
    (horder : ∀ a ∈ S, ∃ n : ℕ, analyticOrderAt F a = (2 * n : ℕ)) :
    ∃ r : ℂ → ℂ,
      AnalyticOnNhd ℂ r S ∧
        Set.EqOn (fun z => r z ^ 2) F S ∧
          ∀ a ∈ S, ∀ n : ℕ, analyticOrderAt F a = (2 * n : ℕ) → analyticOrderAt r a = n := by
  obtain ⟨s⟩ := exists_global_rootSection S F hF horder
  have hr : AnalyticOnNhd ℂ (extendSection S ⊤ s.1) S := by
    simpa only [ambientOpen_top] using RootSection.analyticOnNhd_extend s
  have hsquare : Set.EqOn (fun z => extendSection S ⊤ s.1 z ^ 2) F S := by
    intro z hz
    apply RootSection.square_eq (S := S) (F := F) (V := ⊤) s
    rw [ambientOpen_top]
    exact hz
  refine ⟨extendSection S ⊤ s.1, hr, hsquare, ?_⟩
  intro a ha n hn
  exact
    square_root_order (hr a ha)
      (Filter.eventually_of_mem (S.isOpen.mem_nhds ha) (fun _ hz => hsquare hz)) hn

/-- An analytic function on a simply connected open complex domain has an analytic square root if every zero has finite even order. -/
theorem AnalyticRootCover.exists_analytic_square_root_on_of_even_zeros
    (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ) [SimplyConnectedSpace S] (hF : AnalyticOnNhd ℂ F S)
    (hzero : ∀ a ∈ S, F a = 0 → ∃ n : ℕ, analyticOrderAt F a = (2 * n : ℕ)) :
    ∃ r : ℂ → ℂ,
      AnalyticOnNhd ℂ r S ∧
        Set.EqOn (fun z => r z ^ 2) F S ∧
          ∀ a ∈ S, ∀ n : ℕ, analyticOrderAt F a = (2 * n : ℕ) → analyticOrderAt r a = n :=
  exists_analytic_square_root_on S F hF (even_order_at_all_points hF hzero)

/-! ### Square roots on the upper half-plane -/

/-- The upper half-plane as an open set. -/
def AnalyticRootCover.upperHalfPlaneOpen : TopologicalSpace.Opens ℂ :=
  ⟨UpperHalfPlane.upperHalfPlaneSet, UpperHalfPlane.isOpen_upperHalfPlaneSet⟩

/-- The upper half-plane is contractible. -/
instance AnalyticRootCover.instContractibleSpace1 : ContractibleSpace upperHalfPlaneOpen :=
  (convex_halfSpace_im_gt 0).contractibleSpace ⟨Complex.I, by simp⟩

/-- An analytic function on the upper half-plane whose zeros have finite even order has an analytic square root with halved orders. -/
theorem AnalyticRootCover.exists_analytic_square_root_upperHalfPlane (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F UpperHalfPlane.upperHalfPlaneSet)
    (hzero :
      ∀ a ∈ UpperHalfPlane.upperHalfPlaneSet,
        F a = 0 → ∃ n : ℕ, analyticOrderAt F a = (2 * n : ℕ)) :
    ∃ r : ℂ → ℂ,
      AnalyticOnNhd ℂ r UpperHalfPlane.upperHalfPlaneSet ∧
        Set.EqOn (fun z => r z ^ 2) F UpperHalfPlane.upperHalfPlaneSet ∧
          ∀ a ∈ UpperHalfPlane.upperHalfPlaneSet,
            ∀ n : ℕ, analyticOrderAt F a = (2 * n : ℕ) → analyticOrderAt r a = n :=
  exists_analytic_square_root_on_of_even_zeros upperHalfPlaneOpen F hF hzero

/-- A holomorphic function on the upper half-plane whose zeros have finite even order admits a holomorphic square root with halved orders. -/
theorem AnalyticRootCover.exists_holomorphic_square_root_upperHalfPlane (f : ℍ → ℂ)
    (hf : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f)
    (hzero :
      ∀ a : ℍ,
        f a = 0 → ∃ n : ℕ, analyticOrderAt (f ∘ UpperHalfPlane.ofComplex) (a : ℂ) = (2 * n : ℕ)) :
    ∃ r : ℍ → ℂ,
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω r ∧
        (∀ a : ℍ, r a ^ 2 = f a) ∧
          ∀ a : ℍ,
            ∀ n : ℕ,
              analyticOrderAt (f ∘ UpperHalfPlane.ofComplex) (a : ℂ) = (2 * n : ℕ) →
                analyticOrderAt (r ∘ UpperHalfPlane.ofComplex) (a : ℂ) = n := by
  let F : ℂ → ℂ := f ∘ UpperHalfPlane.ofComplex
  have hF : AnalyticOnNhd ℂ F UpperHalfPlane.upperHalfPlaneSet :=
    (UpperHalfPlane.mdifferentiable_iff.mp hf).analyticOnNhd
      UpperHalfPlane.isOpen_upperHalfPlaneSet
  have hzeroF :
    ∀ a ∈ UpperHalfPlane.upperHalfPlaneSet,
      F a = 0 → ∃ n : ℕ, analyticOrderAt F a = (2 * n : ℕ) := by
    intro a ha hfa
    apply hzero ⟨a, ha⟩
    simpa only [F, Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos ha] using hfa
  obtain ⟨g, hg, hgsquare, hgorder⟩ := exists_analytic_square_root_upperHalfPlane F hF hzeroF
  let r : ℍ → ℂ := fun a => g a
  refine ⟨r, ?_, ?_, ?_⟩
  · intro a
    exact (hg a a.im_pos).contDiffAt.contMDiffAt.comp a (UpperHalfPlane.contMDiff_coe a)
  · intro a
    simpa only [r, F, Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hgsquare a.im_pos
  · intro a n hn
    have he : (r ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝 (a : ℂ)] g := by
      filter_upwards [UpperHalfPlane.eventuallyEq_coe_comp_ofComplex a.im_pos] with z hz
      exact congrArg g hz
    exact (analyticOrderAt_congr he).trans (hgorder a a.im_pos n hn)
