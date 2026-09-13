/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
public import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance

/-!
# Punctured spaces, linking spheres, and local degree data

The topology behind local degree (Hatcher, Prop 2.30): the punctured normed space
`E \ {0}` deformation-retracts onto its unit sphere, radial cylinders identify punctured
balls with spheres, and maps that are near-linear at a point have well-defined boundary data
on small spheres:

* `Smale.PuncturedRadial.sphereHomotopyEquiv` — `S(E) ≃ₕ {x : E | x ≠ 0}` (radial
  deformation `deformation`);
* `Smale.LocalDegree.exists_pos_remainder_bound` — the derivative approximation at `0`;
* `Smale.LocalDegree.BoundaryData` — for `f` differentiable at `0` with `f 0 = 0`, the small
  sphere on which `f` avoids `0`, with `homology_compare` (the boundary map and the linear
  map agree in homology — the definition of the local degree's sign datum);
* `PassageHomology.*` — punctured spaces, the two-puncture extension, linking
  spheres, cylinder puncture/slice/link, and the punctured passage trace (the "linking
  relation" of a path with a sphere).

The radial-cylinder chart family that needs `Smale.PartialChart`/diffeomorphic glue stays in
`Hopf/` (see Lib/reports/A.md, obstruction 3).

## Outline of the proof

1. *Punctured balls and spheres.*  `puncturedVectorSpace`, `twoPunctureSet`, the inclusion
   of the two punctures; `homology_ext_of_ambient_vanishing` /
   `two_puncture_homology_ext` identify the homology of a twice-punctured space from the
   ambient vanishing.
2. *Punctured sphere maps.*  `puncturedSphereMap`, homotopy in radius/center/family
   (`puncturedSphereMap_homotopic_of_family`, `_radius_homotopic`, `_center_homotopic`),
   null-homotopy outside (`puncturedSphereMap_outside_nullhomotopic`).
3. *Linking.*  `innerSphere`, `outerSphere`, `linkingSphere`; the radial-sphere homology
   relation `radial_sphere_homology_relation` (Hatcher Prop 2.30's local relation);
   cylinder puncture/slice/link with their trace relations (`clampTime`,
   `puncturedPassageTrace`).
4. *Radial retraction.*  `PuncturedRadial.toSphere`/`fromSphere`/`deformation` give the
   deformation retraction; `LocalDegree.exists_pos_remainder_bound` is the quantified
   derivative estimate; `BoundaryData` packages the boundary map on a small sphere with
   `nonempty_boundaryData` (from differentiability) and `homology_compare` (independence up
   to homotopy = the local degree datum).

## Main definitions and results

* `Smale.PuncturedRadial.sphereHomotopyEquiv` : the radial homotopy equivalence.
* `Smale.LocalDegree.BoundaryData` and `.homology_compare` : the local degree boundary datum.
* `PassageHomology.radial_sphere_homology_relation` : the linking relation.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], Proposition 2.30 (local degree) and the
  degree-zero section of §2.2

## Tags

local degree, linking number, punctured space, radial retraction
-/



set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

@[expose] public noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

def PassageHomology.twoPunctureSet {X : Type} (a b : X) : Set X :=
  ({ a }ᶜ : Set X) ∩ { b }ᶜ

def PassageHomology.firstPunctureInclusion {X : Type} [TopologicalSpace X] (a b : X) :
    C(twoPunctureSet a b, ({ a }ᶜ : Set X)) :=
  ContinuousMap.inclusion Set.inter_subset_left

def PassageHomology.secondPunctureInclusion {X : Type} [TopologicalSpace X] (a b : X) :
    C(twoPunctureSet a b, ({ b }ᶜ : Set X)) :=
  ContinuousMap.inclusion Set.inter_subset_right

theorem PassageHomology.homology_ext_of_ambient_vanishing {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = Set.univ) (n : ℕ)
    [Subsingleton (SingularMayerVietoris.SingularHomology X (n + 1))]
    {a b : SingularMayerVietoris.SingularHomology (U ∩ V : Set X) n}
    (hfirst :
      SingularMayerVietoris.singularHomologyMap
          (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n a =
        SingularMayerVietoris.singularHomologyMap
          (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n b)
    (hsecond :
      SingularMayerVietoris.singularHomologyMap
          (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V)) n a =
        SingularMayerVietoris.singularHomologyMap
          (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V)) n b) :
    a = b := by
  have hz : SingularMayerVietoris.connectingHomomorphism U V hU hV hc n = 0 := by
    apply LinearMap.ext
    intro c
    have hc0 : c = 0 := Subsingleton.elim _ _
    rw [hc0, map_zero]
    rfl
  have hi : Function.Injective (SingularMayerVietoris.leftHomologyMap U V n) := by
    apply LinearMap.ker_eq_bot.mp
    rw [← SingularMayerVietoris.exact_at_intersection U V hU hV hc n, hz, LinearMap.range_zero]
  apply hi
  rw [SingularMayerVietoris.leftHomologyMap_apply, SingularMayerVietoris.leftHomologyMap_apply,
    hfirst, hsecond]

theorem PassageHomology.two_puncture_homology_ext {X : Type} [TopologicalSpace X]
    [T1Space X] [ContractibleSpace X] {p q : X} (hpq : p ≠ q) (n : ℕ)
    {a b : SingularMayerVietoris.SingularHomology (twoPunctureSet p q) n}
    (hfirst :
      SingularMayerVietoris.singularHomologyMap (firstPunctureInclusion p q) n a =
        SingularMayerVietoris.singularHomologyMap (firstPunctureInclusion p q) n b)
    (hsecond :
      SingularMayerVietoris.singularHomologyMap (secondPunctureInclusion p q) n a =
        SingularMayerVietoris.singularHomologyMap (secondPunctureInclusion p q) n b) :
    a = b := by
  have hc : ({ p }ᶜ : Set X) ∪ { q }ᶜ = Set.univ := by
    ext z
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    by_cases hz : z = p
    · exact Or.inr (fun hq => hpq (hz.symm.trans hq))
    · exact Or.inl hz
  let _ :=
    SingularHomology.contractible_homology_subsingleton X (n + 1) (Nat.succ_ne_zero n)
  exact
    homology_ext_of_ambient_vanishing _ _ isOpen_compl_singleton isOpen_compl_singleton hc n
      hfirst hsecond

theorem PassageHomology.affine_sphere_ne_of_norm_ne {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {p c : E} {r : ℝ} (hr : 0 ≤ r) (h : ‖c - p‖ ≠ r)
    (u : Metric.sphere (0 : E) 1) : c + r • u.val ≠ p := by
  intro he
  apply h
  have hvalue : r • u.val = p - c := by rw [← he, add_sub_cancel_left]
  calc
    ‖c - p‖ = ‖p - c‖ := norm_sub_rev c p
    _ = ‖r • u.val‖ := (congrArg Norm.norm hvalue.symm)
    _ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, mem_sphere_zero_iff_norm.mp u.property,
        mul_one]

def PassageHomology.puncturedSphereMap {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p c : E) (r : ℝ) (h : ∀ u : Metric.sphere (0 : E) 1, c + r • u.val ≠ p) :
    C(Metric.sphere (0 : E) 1, ({ p }ᶜ : Set E))
    where
  toFun u := ⟨c + r • u.val, h u⟩
  continuous_toFun :=
    (continuous_const.add (continuous_const.smul continuous_subtype_val)).subtype_mk _

theorem PassageHomology.puncturedSphereMap_homotopic_of_family {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (p : E) (c : C(unitInterval, E))
    (r : C(unitInterval, ℝ)) {c₀ c₁ : E} {r₀ r₁ : ℝ} (hc₀ : c 0 = c₀) (hc₁ : c 1 = c₁)
    (hr₀ : r 0 = r₀) (hr₁ : r 1 = r₁)
    (h : ∀ t, ∀ u : Metric.sphere (0 : E) 1, c t + r t • u.val ≠ p)
    (h₀ : ∀ u : Metric.sphere (0 : E) 1, c₀ + r₀ • u.val ≠ p)
    (h₁ : ∀ u : Metric.sphere (0 : E) 1, c₁ + r₁ • u.val ≠ p) :
    (puncturedSphereMap p c₀ r₀ h₀).Homotopic (puncturedSphereMap p c₁ r₁ h₁) := by
  refine
    ⟨{  toFun := fun z => ⟨c z.1 + r z.1 • z.2.val, h z.1 z.2⟩
        continuous_toFun :=
          ((c.continuous.comp continuous_fst).add
                ((r.continuous.comp continuous_fst).smul
                  (continuous_subtype_val.comp continuous_snd))).subtype_mk
            _
        map_zero_left := ?_
        map_one_left := ?_ }⟩
  · intro u
    apply Subtype.ext
    change c 0 + r 0 • u.val = c₀ + r₀ • u.val
    rw [hc₀, hr₀]
  · intro u
    apply Subtype.ext
    change c 1 + r 1 • u.val = c₁ + r₁ • u.val
    rw [hc₁, hr₁]

theorem PassageHomology.puncturedSphereMap_radius_homotopic {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (p : E) {r₀ r₁ : ℝ} (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (h₀ : ∀ u : Metric.sphere (0 : E) 1, p + r₀ • u.val ≠ p)
    (h₁ : ∀ u : Metric.sphere (0 : E) 1, p + r₁ • u.val ≠ p) :
    (puncturedSphereMap p p r₀ h₀).Homotopic (puncturedSphereMap p p r₁ h₁) := by
  let r : C(unitInterval, ℝ) :=
    ⟨fun t => (1 - (t : ℝ)) * r₀ + (t : ℝ) * r₁,
      ((continuous_const.sub continuous_subtype_val).mul continuous_const).add
        (continuous_subtype_val.mul continuous_const)⟩
  apply
    puncturedSphereMap_homotopic_of_family p (ContinuousMap.const _ p) r rfl rfl (by simp [r])
      (by simp [r]) _ h₀ h₁
  intro t u
  have hrt : 0 < r t := by
    change 0 < (1 - (t : ℝ)) * r₀ + (t : ℝ) * r₁
    exact
      (convex_Ioi (0 : ℝ)) hr₀ hr₁ (sub_nonneg.mpr t.property.2) t.property.1
        (sub_add_cancel 1 (t : ℝ))
  exact affine_sphere_ne_of_norm_ne hrt.le (by simpa using hrt.ne) u

theorem PassageHomology.puncturedSphereMap_center_homotopic {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (p c : E) {r : ℝ} (hinside : ‖c - p‖ < r)
    (h₀ : ∀ u : Metric.sphere (0 : E) 1, c + r • u.val ≠ p)
    (h₁ : ∀ u : Metric.sphere (0 : E) 1, p + r • u.val ≠ p) :
    (puncturedSphereMap p c r h₀).Homotopic (puncturedSphereMap p p r h₁) := by
  let cpath : C(unitInterval, E) :=
    ⟨fun t => p + (1 - (t : ℝ)) • (c - p),
      continuous_const.add ((continuous_const.sub continuous_subtype_val).smul continuous_const)⟩
  have hc0 : cpath 0 = c := by simp [cpath]
  have hc1 : cpath 1 = p := by simp [cpath]
  apply
    puncturedSphereMap_homotopic_of_family p cpath (ContinuousMap.const _ r) hc0 hc1 rfl rfl _ h₀
      h₁
  intro t u
  have hn : ‖cpath t - p‖ ≤ ‖c - p‖ := by
    change ‖(p + (1 - (t : ℝ)) • (c - p)) - p‖ ≤ _
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr t.property.2)]
    exact mul_le_of_le_one_left (norm_nonneg _) (sub_le_self _ t.property.1)
  exact
    affine_sphere_ne_of_norm_ne ((norm_nonneg _).trans_lt hinside).le (hn.trans_lt hinside).ne u

theorem PassageHomology.puncturedSphereMap_outside_nullhomotopic {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (p c : E) {r : ℝ} (hr : 0 ≤ r)
    (houtside : r < ‖c - p‖) (h : ∀ u : Metric.sphere (0 : E) 1, c + r • u.val ≠ p) :
    ∃ q : ({ p }ᶜ : Set E), (puncturedSphereMap p c r h).Homotopic (ContinuousMap.const _ q) := by
  have hcp : c ≠ p := by
    intro he
    rw [he, sub_self, norm_zero] at houtside
    exact (not_lt_of_ge hr) houtside
  have hzero : ∀ u : Metric.sphere (0 : E) 1, c + (0 : ℝ) • u.val ≠ p := by
    intro u
    simpa only [zero_smul, add_zero] using hcp
  let rpath : C(unitInterval, ℝ) :=
    ⟨fun t => (1 - (t : ℝ)) * r,
      (continuous_const.sub continuous_subtype_val).mul continuous_const⟩
  have H :=
    puncturedSphereMap_homotopic_of_family p (ContinuousMap.const _ c) rpath rfl rfl
      (by simp [rpath]) (by simp [rpath]) (h₀ := h) (h₁ := hzero)
      (by
        intro t u
        have hrt : 0 ≤ rpath t := mul_nonneg (sub_nonneg.mpr t.property.2) hr
        have hle : rpath t ≤ r := mul_le_of_le_one_left hr (sub_le_self _ t.property.1)
        exact affine_sphere_ne_of_norm_ne hrt (hle.trans_lt houtside).ne' u)
  have he :
    puncturedSphereMap p c 0 hzero = ContinuousMap.const _ (⟨c, hcp⟩ : ({ p }ᶜ : Set E)) := by
    apply ContinuousMap.ext
    intro u
    apply Subtype.ext
    change c + (0 : ℝ) • u.val = c
    rw [zero_smul, add_zero]
  exact ⟨⟨c, hcp⟩, he ▸ H⟩

def PassageHomology.twoPunctureSphereMap {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (p q c : E) (r : ℝ) (hp : ∀ u : Metric.sphere (0 : E) 1, c + r • u.val ≠ p)
    (hq : ∀ u : Metric.sphere (0 : E) 1, c + r • u.val ≠ q) :
    C(Metric.sphere (0 : E) 1, twoPunctureSet p q)
    where
  toFun u := ⟨c + r • u.val, hp u, hq u⟩
  continuous_toFun :=
    (continuous_const.add (continuous_const.smul continuous_subtype_val)).subtype_mk _

def PassageHomology.innerSphere {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (b : E)
    (r : ℝ) (hr : 0 < r) (hrb : r < ‖b‖) : C(Metric.sphere (0 : E) 1, twoPunctureSet 0 b) :=
  twoPunctureSphereMap 0 b 0 r
    (affine_sphere_ne_of_norm_ne hr.le (by simpa only [sub_self, norm_zero] using hr.ne))
    (affine_sphere_ne_of_norm_ne hr.le (by simpa only [zero_sub, norm_neg] using hrb.ne'))

def PassageHomology.outerSphere {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (b : E)
    (R : ℝ) (hbR : ‖b‖ < R) : C(Metric.sphere (0 : E) 1, twoPunctureSet 0 b) :=
  twoPunctureSphereMap 0 b 0 R
    (affine_sphere_ne_of_norm_ne ((norm_nonneg b).trans_lt hbR).le
      (by simpa only [sub_self, norm_zero] using ((norm_nonneg b).trans_lt hbR).ne))
    (affine_sphere_ne_of_norm_ne ((norm_nonneg b).trans_lt hbR).le
      (by simpa only [zero_sub, norm_neg] using hbR.ne))

def PassageHomology.linkingSphere {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : E) (ε : ℝ) (hε : 0 < ε) (hεb : ε < ‖b‖) :
    C(Metric.sphere (0 : E) 1, twoPunctureSet 0 b) :=
  twoPunctureSphereMap 0 b b ε
    (affine_sphere_ne_of_norm_ne hε.le (by simpa only [sub_zero] using hεb.ne'))
    (affine_sphere_ne_of_norm_ne hε.le (by simpa only [sub_self, norm_zero] using hε.ne))

theorem PassageHomology.radial_sphere_homology_relation {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (b : E) {r R ε : ℝ} (hr : 0 < r) (hrb : r < ‖b‖) (hbR : ‖b‖ < R)
    (hε : 0 < ε) (hεb : ε < ‖b‖) (n : ℕ) (hn : n ≠ 0) :
    SingularMayerVietoris.singularHomologyMap (outerSphere b R hbR) n =
      SingularMayerVietoris.singularHomologyMap (innerSphere b r hr hrb) n +
        SingularMayerVietoris.singularHomologyMap (linkingSphere b ε hε hεb) n := by
  have hb : b ≠ 0 := norm_pos_iff.mp (hr.trans hrb)
  have hR : 0 < R := (norm_nonneg b).trans_lt hbR
  let i := firstPunctureInclusion (0 : E) b
  let j := secondPunctureInclusion (0 : E) b
  let inner := innerSphere b r hr hrb
  let outer := outerSphere b R hbR
  let link := linkingSphere b ε hε hεb
  have hio : (i.comp outer).Homotopic (i.comp inner) :=
    puncturedSphereMap_radius_homotopic 0 hR hr (fun u => (outer u).property.1)
      (fun u => (inner u).property.1)
  have hil : (i.comp link).Nullhomotopic :=
    puncturedSphereMap_outside_nullhomotopic 0 b hε.le (by simpa only [sub_zero] using hεb)
      (fun u => (link u).property.1)
  have hji : (j.comp inner).Nullhomotopic :=
    puncturedSphereMap_outside_nullhomotopic b 0 hr.le
      (by simpa only [zero_sub, norm_neg] using hrb) (fun u => (inner u).property.2)
  have hcenter : ∀ u : Metric.sphere (0 : E) 1, b + R • u.val ≠ b :=
    affine_sphere_ne_of_norm_ne hR.le (by simpa only [sub_self, norm_zero] using hR.ne)
  let center := puncturedSphereMap b b R hcenter
  have hoc : (j.comp outer).Homotopic center :=
    puncturedSphereMap_center_homotopic b 0 (by simpa only [zero_sub, norm_neg] using hbR)
      (fun u => (outer u).property.2) hcenter
  have hcl : center.Homotopic (j.comp link) :=
    puncturedSphereMap_radius_homotopic b hR hε hcenter (fun u => (link u).property.2)
  have hjo := hoc.trans hcl
  have hioMap := SingularHomology.homotopic_homologyMap hio n
  have hjoMap := SingularHomology.homotopic_homologyMap hjo n
  have hilMap :=
    Suspension.singularHomologyMap_eq_zero_of_nullhomotopic (i.comp link) hil n hn
  have hjiMap :=
    Suspension.singularHomologyMap_eq_zero_of_nullhomotopic (j.comp inner) hji n hn
  apply LinearMap.ext
  intro a
  change
    SingularMayerVietoris.singularHomologyMap outer n a =
      SingularMayerVietoris.singularHomologyMap inner n a +
        SingularMayerVietoris.singularHomologyMap link n a
  apply two_puncture_homology_ext hb.symm n
  · change
      SingularMayerVietoris.singularHomologyMap i n
          (SingularMayerVietoris.singularHomologyMap outer n a) =
        _
    rw [map_add]
    have ho :
      SingularMayerVietoris.singularHomologyMap i n
          (SingularMayerVietoris.singularHomologyMap outer n a) =
        SingularMayerVietoris.singularHomologyMap i n
          (SingularMayerVietoris.singularHomologyMap inner n a) := by
      simpa only [SingularHomology.singularHomologyMap_comp, LinearMap.comp_apply] using
        LinearMap.congr_fun hioMap a
    have hl :
      SingularMayerVietoris.singularHomologyMap i n
          (SingularMayerVietoris.singularHomologyMap link n a) =
        0 := by
      simpa only [SingularHomology.singularHomologyMap_comp, LinearMap.comp_apply,
        LinearMap.zero_apply] using LinearMap.congr_fun hilMap a
    rw [ho, hl, add_zero]
  · change
      SingularMayerVietoris.singularHomologyMap j n
          (SingularMayerVietoris.singularHomologyMap outer n a) =
        _
    rw [map_add]
    have ho :
      SingularMayerVietoris.singularHomologyMap j n
          (SingularMayerVietoris.singularHomologyMap outer n a) =
        SingularMayerVietoris.singularHomologyMap j n
          (SingularMayerVietoris.singularHomologyMap link n a) := by
      simpa only [SingularHomology.singularHomologyMap_comp, LinearMap.comp_apply] using
        LinearMap.congr_fun hjoMap a
    have hi :
      SingularMayerVietoris.singularHomologyMap j n
          (SingularMayerVietoris.singularHomologyMap inner n a) =
        0 := by
      simpa only [SingularHomology.singularHomologyMap_comp, LinearMap.comp_apply,
        LinearMap.zero_apply] using LinearMap.congr_fun hjiMap a
    rw [ho, hi, zero_add]

def PassageHomology.cylinderPuncture {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (τ : ℝ) (u : Metric.sphere (0 : E) 1) : E :=
  Real.exp τ • u.val

theorem PassageHomology.norm_cylinderPuncture {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (τ : ℝ) (u : Metric.sphere (0 : E) 1) :
    ‖cylinderPuncture τ u‖ = Real.exp τ := by
  rw [cylinderPuncture, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos τ),
    mem_sphere_zero_iff_norm.mp u.property, mul_one]

def PassageHomology.cylinderSlice {E : Type} [NormedAddCommGroup E] (τ : ℝ)
    (u : Metric.sphere (0 : E) 1) (t : ℝ) (ht : t ≠ τ) :
    C(Metric.sphere (0 : E) 1, ({(τ, u)}ᶜ : Set (ℝ × Metric.sphere (0 : E) 1)))
    where
  toFun v := ⟨(t, v), fun h => ht (congrArg Prod.fst h)⟩
  continuous_toFun := (continuous_const.prodMk continuous_id).subtype_mk _

def PassageHomology.clampTime : C(ℝ, ℝ) :=
  ⟨fun t => Max.max 0 (Min.min 1 t), continuous_const.max (continuous_const.min continuous_id)⟩

theorem PassageHomology.clampTime_mem (t : ℝ) : clampTime t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem PassageHomology.clampTime_of_mem {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    clampTime t = t := by
  change Max.max 0 (Min.min 1 t) = t
  rw [min_eq_right ht.2, max_eq_right ht.1]

theorem PassageHomology.clampTime_eq_interior_iff {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) 1)
    (t : ℝ) : clampTime t = τ ↔ t = τ := by
  constructor
  · intro he
    by_cases ht0 : t ≤ 0
    · have hc : clampTime t = 0 := by
        change Max.max 0 (Min.min 1 t) = 0
        rw [min_eq_right (ht0.trans zero_le_one), max_eq_left ht0]
      exact (hτ.1.ne (hc.symm.trans he)).elim
    by_cases ht1 : 1 ≤ t
    · have hc : clampTime t = 1 := by
        change Max.max 0 (Min.min 1 t) = 1
        rw [min_eq_left ht1, max_eq_right zero_le_one]
      exact (hτ.2.ne' (hc.symm.trans he)).elim
    exact (clampTime_of_mem ⟨(lt_of_not_ge ht0).le, (lt_of_not_ge ht1).le⟩).symm.trans he
  · intro he
    subst t
    exact clampTime_of_mem ⟨hτ.1.le, hτ.2.le⟩

def PassageHomology.puncturedPassageTrace {E X : Type} [NormedAddCommGroup E]
    [TopologicalSpace X] (H : C(ℝ × Metric.sphere (0 : E) 1, X)) (S : Set X) {τ : ℝ}
    (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) (u : Metric.sphere (0 : E) 1)
    (hcross :
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ v : Metric.sphere (0 : E) 1, H (t, v) ∈ S ↔ t = τ ∧ v = u) :
    C(({(τ, u)}ᶜ : Set (ℝ × Metric.sphere (0 : E) 1)), (Sᶜ : Set X))
    where
  toFun
    p :=
    ⟨H (clampTime p.val.1, p.val.2), by
      intro hp
      have he := (hcross _ (clampTime_mem _) p.val.2).mp hp
      exact p.property (Prod.ext ((clampTime_eq_interior_iff hτ _).mp he.1) he.2)⟩
  continuous_toFun := by
    have ht :
      Continuous (fun p : ({(τ, u)}ᶜ : Set (ℝ × Metric.sphere (0 : E) 1)) => clampTime p.val.1) :=
      clampTime.continuous.comp (continuous_fst.comp continuous_subtype_val)
    have hv : Continuous (fun p : ({(τ, u)}ᶜ : Set (ℝ × Metric.sphere (0 : E) 1)) => p.val.2) :=
      continuous_snd.comp continuous_subtype_val
    exact (H.continuous.comp (ht.prodMk hv)).subtype_mk _

theorem PassageHomology.puncturedPassageTrace_on_interval {E X : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
    (H : C(ℝ × Metric.sphere (0 : E) 1, X)) (S : Set X) {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) 1)
    (u : Metric.sphere (0 : E) 1)
    (hcross :
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ v : Metric.sphere (0 : E) 1, H (t, v) ∈ S ↔ t = τ ∧ v = u)
    (p : ({(τ, u)}ᶜ : Set (ℝ × Metric.sphere (0 : E) 1))) (hp : p.val.1 ∈ Set.Icc (0 : ℝ) 1) :
    (puncturedPassageTrace H S hτ u hcross p).val = H p.val := by
  change H (clampTime p.val.1, p.val.2) = H p.val
  rw [clampTime_of_mem hp]

def PassageHomology.puncturedVectorSpace (E : Type) [NormedAddCommGroup E] :
    TopologicalSpace.Opens E :=
  ⟨({0}ᶜ : Set E), isOpen_compl_singleton⟩

abbrev Smale.PuncturedRadial.Space (N : Type*) [Zero N] :=
  { u : N // u ≠ 0 }

def Smale.PuncturedRadial.fromSphere {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] (r : ℝ)
    (hr : 0 < r) : C(Metric.sphere (0 : N) 1, Space N) :=
  ⟨fun u => ⟨r • (u : N), smul_ne_zero hr.ne' (ne_zero_of_mem_unit_sphere u)⟩,
    (continuous_const.smul continuous_subtype_val).subtype_mk _⟩

def Smale.PuncturedRadial.blendVector {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] (r : ℝ)
    (q : (unitInterval) × Space N) : N :=
  ((1 - (q.1 : ℝ)) + (q.1 : ℝ) * (r / ‖q.2.val‖)) • q.2.val

theorem Smale.PuncturedRadial.continuous_blendVector {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (r : ℝ) : Continuous (blendVector (N := N) r) := by
  have ht : Continuous (fun q : (unitInterval) × Space N => (q.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hu : Continuous (fun q : (unitInterval) × Space N => q.2.val) :=
    continuous_subtype_val.comp continuous_snd
  exact
    ((continuous_const.sub ht).add
          (ht.mul
            (continuous_const.div hu.norm (fun q => norm_ne_zero_iff.mpr q.2.property)))).smul
      hu

theorem Smale.PuncturedRadial.blendVector_ne_zero {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (r : ℝ) (hr : 0 < r) (q : (unitInterval) × Space N) : blendVector r q ≠ 0 :=
  by
  have hu : 0 < ‖q.2.val‖ := norm_pos_iff.mpr q.2.property
  have hpos : 0 < (1 - (q.1 : ℝ)) + (q.1 : ℝ) * (r / ‖q.2.val‖) := by
    have h :=
      (convex_Ioi (𝕜 := ℝ) (0 : ℝ)) (by norm_num : (1 : ℝ) ∈ Ioi 0) (div_pos hr hu)
        (sub_nonneg.mpr q.1.property.2) q.1.property.1 (sub_add_cancel 1 (q.1 : ℝ))
    simpa only [smul_eq_mul, mul_one, Set.mem_Ioi] using h
  exact smul_ne_zero hpos.ne' q.2.property

theorem Smale.LocalDegree.exists_pos_remainder_bound {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (L : E ≃L[ℝ] F)
    (hf : HasFDerivAt f L.toContinuousLinearMap 0) (hzero : f 0 = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Metric.ball (0 : E) ε, ‖f x - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖ := by
  have herr : (fun x : E => f x - L x) =o[𝓝 (0 : E)] (fun x : E => x) := by
    convert hf.isLittleO using 1
    · rfl
    · rfl
    · simp only [hzero, sub_zero]
      rfl
    · simp only [sub_zero]
  have hbig : (fun x : E => x) =O[𝓝 (0 : E)] (fun x : E => L x) := by
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨‖L.symm.toContinuousLinearMap‖, Filter.Eventually.of_forall ?_⟩
    intro x
    have h := L.symm.toContinuousLinearMap.le_opNorm (L x)
    simpa only [ContinuousLinearEquiv.coe_coe, L.symm_apply_apply] using h
  exact
    Metric.eventually_nhds_iff_ball.mp
      ((herr.trans_isBigO hbig).bound (by norm_num : (0 : ℝ) < 1 / 2))

def Smale.LocalDegree.blend {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (L : E ≃L[ℝ] F) (t : (unitInterval))
    (x : E) : F :=
  L x + (t : ℝ) • (f x - L x)

theorem Smale.LocalDegree.blend_ne_zero {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (L : E ≃L[ℝ] F) (t : (unitInterval))
    {x : E} (hx : x ≠ 0) (hbound : ‖f x - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖) : blend f L t x ≠ 0 := by
  have hL : L x ≠ 0 := fun h => hx (L.injective (h.trans (map_zero L).symm))
  have hsmall : ‖(t : ℝ) • (f x - L x)‖ < ‖L x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
    calc
      (t : ℝ) * ‖f x - L x‖ ≤ ‖f x - L x‖ := mul_le_of_le_one_left (norm_nonneg _) t.property.2
      _ ≤ (1 / 2 : ℝ) * ‖L x‖ := hbound
      _ < ‖L x‖ := by nlinarith [norm_pos_iff.mpr hL]
  intro h
  have heq : (t : ℝ) • (f x - L x) = -L x := by
    change L x + (t : ℝ) • (f x - L x) = 0 at h
    rw [add_comm] at h
    exact add_eq_zero_iff_eq_neg.mp h
  rw [heq, norm_neg] at hsmall
  exact (lt_irrefl _ hsmall)

theorem Smale.LocalDegree.image_ne_zero {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (L : E ≃L[ℝ] F) {x : E} (hx : x ≠ 0)
    (hbound : ‖f x - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖) : f x ≠ 0 := by
  have h := blend_ne_zero L (1 : (unitInterval)) hx hbound
  change L x + (1 : ℝ) • (f x - L x) ≠ 0 at h
  simpa using h

def Smale.LocalDegree.linearSphereMap {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E ≃L[ℝ] F) (r : ℝ) (hr : 0 < r) :
    C(Metric.sphere (0 : E) 1, Smale.PuncturedRadial.Space F) :=
  ⟨fun u =>
    ⟨L (r • (u : E)), fun h =>
      (smul_ne_zero hr.ne' (ne_zero_of_mem_unit_sphere u))
        (L.injective (h.trans (map_zero L).symm))⟩,
    (L.continuous.comp (continuous_const.smul continuous_subtype_val)).subtype_mk _⟩

def Smale.LocalDegree.boundaryMap {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (L : E ≃L[ℝ] F) (r : ℝ) (hr : 0 < r)
    (hc : Continuous (fun u : Metric.sphere (0 : E) 1 => f (r • (u : E))))
    (hb :
      ∀ u : Metric.sphere (0 : E) 1,
        ‖f (r • (u : E)) - L (r • (u : E))‖ ≤ (1 / 2 : ℝ) * ‖L (r • (u : E))‖) :
    C(Metric.sphere (0 : E) 1, Smale.PuncturedRadial.Space F) :=
  ⟨fun u =>
    ⟨f (r • (u : E)),
      image_ne_zero L (smul_ne_zero hr.ne' (ne_zero_of_mem_unit_sphere u)) (hb u)⟩,
    hc.subtype_mk _⟩

def Smale.LocalDegree.boundaryHomotopy {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (L : E ≃L[ℝ] F) (r : ℝ) (hr : 0 < r)
    (hc : Continuous (fun u : Metric.sphere (0 : E) 1 => f (r • (u : E))))
    (hb :
      ∀ u : Metric.sphere (0 : E) 1,
        ‖f (r • (u : E)) - L (r • (u : E))‖ ≤ (1 / 2 : ℝ) * ‖L (r • (u : E))‖) :
    (linearSphereMap L r hr).Homotopy (boundaryMap f L r hr hc hb)
    where
  toFun
    q :=
    ⟨blend f L q.1 (r • (q.2 : E)),
      blend_ne_zero L q.1 (smul_ne_zero hr.ne' (ne_zero_of_mem_unit_sphere q.2)) (hb q.2)⟩
  continuous_toFun := by
    have ht : Continuous (fun q : (unitInterval) × Metric.sphere (0 : E) 1 => (q.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hL :
      Continuous (fun q : (unitInterval) × Metric.sphere (0 : E) 1 => L (r • (q.2 : E))) :=
      L.continuous.comp (continuous_const.smul (continuous_subtype_val.comp continuous_snd))
    exact (hL.add (ht.smul ((hc.comp continuous_snd).sub hL))).subtype_mk _
  map_zero_left
    u := by
    apply Subtype.ext
    simp [blend, linearSphereMap]
  map_one_left
    u := by
    apply Subtype.ext
    simp [blend, boundaryMap]

structure Smale.LocalDegree.BoundaryData {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (L : E ≃L[ℝ] F) (s : Set E) where
  radius : ℝ
  radius_pos : 0 < radius
  ball_subset : Metric.closedBall 0 radius ⊆ s
  continuous : Continuous (fun u : Metric.sphere (0 : E) 1 => f (radius • (u : E)))
  remainder_bound :
    ∀ u : Metric.sphere (0 : E) 1,
      ‖f (radius • (u : E)) - L (radius • (u : E))‖ ≤ (1 / 2 : ℝ) * ‖L (radius • (u : E))‖

theorem Smale.LocalDegree.norm_radius_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (hr : 0 < r) (u : Metric.sphere (0 : E) 1) : ‖r • (u : E)‖ = r := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mem_sphere_zero_iff_norm.mp u.property, mul_one]

theorem Smale.LocalDegree.nonempty_boundaryData {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (L : E ≃L[ℝ] F)
    {s : Set E} (hf : HasFDerivAt f L.toContinuousLinearMap 0) (hzero : f 0 = 0)
    (hs : s ∈ 𝓝 (0 : E)) (hc : ContinuousOn f s) : Nonempty (BoundaryData f L s) := by
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhds_iff.mp hs
  obtain ⟨ε, hε, hεb⟩ := exists_pos_remainder_bound L hf hzero
  let r : ℝ := Min.min δ ε / 2
  have hr : 0 < r := half_pos (lt_min hδ hε)
  have hrδ : r < δ := (half_lt_self (lt_min hδ hε)).trans_le (min_le_left δ ε)
  have hrε : r < ε := (half_lt_self (lt_min hδ hε)).trans_le (min_le_right δ ε)
  have hball : Metric.closedBall (0 : E) r ⊆ s := (Metric.closedBall_subset_ball hrδ).trans hδs
  have hparam (u : Metric.sphere (0 : E) 1) : r • (u : E) ∈ Metric.closedBall (0 : E) r := by
    rw [mem_closedBall_zero_iff, norm_radius_smul r hr u]
  have hparamc : Continuous (fun u : Metric.sphere (0 : E) 1 => r • (u : E)) :=
    continuous_const.smul continuous_subtype_val
  refine ⟨⟨r, hr, hball, hc.comp_continuous hparamc (fun u => hball (hparam u)), ?_⟩⟩
  intro u
  apply hεb
  rw [mem_ball_zero_iff, norm_radius_smul r hr u]
  exact hrε

theorem Smale.LocalDegree.nonempty_boundaryData_of_contDiffAt {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (L : E ≃L[ℝ] F)
    {s : Set E} (hf : HasFDerivAt f L.toContinuousLinearMap 0) (hzero : f 0 = 0)
    (hs : s ∈ 𝓝 (0 : E)) (hc : ContDiffAt ℝ ∞ f 0) : Nonempty (BoundaryData f L s) := by
  obtain ⟨t, ht, htc⟩ := contDiffAt_zero.mp (hc.of_le (by simp))
  obtain ⟨b⟩ :=
    nonempty_boundaryData L hf hzero (Filter.inter_mem hs ht) (htc.mono Set.inter_subset_right)
  exact ⟨{ b with ball_subset := b.ball_subset.trans Set.inter_subset_left }⟩

def Smale.LocalDegree.BoundaryData.map {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {L : E ≃L[ℝ] F} {s : Set E}
    (b : Smale.LocalDegree.BoundaryData f L s) :
    C(Metric.sphere (0 : E) 1, Smale.PuncturedRadial.Space F) :=
  Smale.LocalDegree.boundaryMap f L b.radius b.radius_pos b.continuous b.remainder_bound

theorem Smale.LocalDegree.BoundaryData.map_coe {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {L : E ≃L[ℝ] F}
    {s : Set E} (b : Smale.LocalDegree.BoundaryData f L s) (u : Metric.sphere (0 : E) 1) :
    (b.map u).val = f (b.radius • (u : E)) :=
  rfl

def Smale.LocalDegree.BoundaryData.homotopy {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {L : E ≃L[ℝ] F} {s : Set E}
    (b : Smale.LocalDegree.BoundaryData f L s) :
    (Smale.LocalDegree.linearSphereMap L b.radius b.radius_pos).Homotopy b.map :=
  Smale.LocalDegree.boundaryHomotopy f L b.radius b.radius_pos b.continuous b.remainder_bound

def Smale.LocalDegree.puncturedLinearHomeomorph {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E ≃L[ℝ] F) :
    Smale.PuncturedRadial.Space E ≃ₜ Smale.PuncturedRadial.Space F :=
  L.toHomeomorph.subtype
    (fun x => by
      change x ≠ 0 ↔ L x ≠ 0
      constructor
      · intro hx h
        exact hx (L.injective (h.trans (map_zero L).symm))
      · intro hx h
        exact hx (h ▸ map_zero L))

theorem Smale.LocalDegree.BoundaryData.homology_compare {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {L : E ≃L[ℝ] F}
    {s : Set E} (b : Smale.LocalDegree.BoundaryData f L s) (k : ℕ) :
    SingularMayerVietoris.singularHomologyMap b.map k =
      SingularMayerVietoris.singularHomologyMap
        (Smale.LocalDegree.linearSphereMap L b.radius b.radius_pos) k :=
  (SingularHomology.homotopy_homologyMap b.homotopy k).symm
end Mathoverflow1973
