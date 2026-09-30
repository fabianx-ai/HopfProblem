module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Data.ENNReal.BigOperators

/-!
# Absolute continuity across finite weak subdivisions

Clipping each interval of a disjoint family at a common endpoint preserves
disjointness and bounds both domain-length sums. The triangle inequality
then joins the two absolute-continuity estimates. Iterating this argument
glues a finite weak subdivision, with singleton pieces handling repeated cuts.
-/

@[expose] public section
noncomputable section
open Set Finset
open scoped Topology
namespace AbsolutelyContinuousOnInterval
universe u
variable {X : Type u} [PseudoMetricSpace X]

/-- Absolute continuity of the same function on adjacent closed intervals
implies absolute continuity on their union. Clip arbitrary unordered interval
families at the join, use half of the requested tolerance on each side, and
combine their image-distance sums by the triangle inequality. -/
theorem trans_of_le {f : ℝ → X} {a c b : ℝ}
    (hleft : AbsolutelyContinuousOnInterval f a c)
    (hright : AbsolutelyContinuousOnInterval f c b)
    (hac : a ≤ c) (hcb : c ≤ b) :
    AbsolutelyContinuousOnInterval f a b := by
  -- M01: actual unordered half-open clipping subsets, both directions.
  have clip_left_subset (c x y : ℝ) :
      Set.uIoc (min x c) (min y c) ⊆ Set.uIoc x y := by
    intro z hz
    simp only [Set.mem_uIoc] at *
    grind
  have clip_right_subset (c x y : ℝ) :
      Set.uIoc (max x c) (max y c) ⊆ Set.uIoc x y := by
    intro z hz
    simp only [Set.mem_uIoc] at *
    grind

  -- M02: full SAME-index disjWithin transport and both closed endpoint conditions.
  have clip_family {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
      (E : ℕ × (ℕ → ℝ × ℝ)) (hE : E ∈ disjWithin a b) :
      (E.1, fun i => (min (E.2 i).1 c, min (E.2 i).2 c)) ∈ disjWithin a c ∧
      (E.1, fun i => (max (E.2 i).1 c, max (E.2 i).2 c)) ∈ disjWithin c b := by
    rcases hE with ⟨hend, hdisj⟩
    constructor
    · constructor
      · intro i hi
        have he := hend i hi
        simp only [Set.uIcc_of_le (hac.trans hcb), Set.mem_Icc] at he
        simp only [Set.uIcc_of_le hac, Set.mem_Icc]
        grind
      · exact hdisj.mono_on (fun i hi => clip_left_subset c _ _)
    · constructor
      · intro i hi
        have he := hend i hi
        simp only [Set.uIcc_of_le (hac.trans hcb), Set.mem_Icc] at he
        simp only [Set.uIcc_of_le hcb, Set.mem_Icc]
        grind
      · exact hdisj.mono_on (fun i hi => clip_right_subset c _ _)

  -- M03: literal real domain-length split, independent of disjointness.
  have clip_dist_split (c x y : ℝ) :
      dist (min x c) (min y c) + dist (max x c) (max y c) = dist x y := by
    rcases le_total x c with hx | hx <;> rcases le_total y c with hy | hy
    · simp [min_eq_left hx, min_eq_left hy, max_eq_right hx, max_eq_right hy]
    · simp only [min_eq_left hx, min_eq_right hy, max_eq_right hx, max_eq_left hy,
        Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx),
        abs_of_nonpos (sub_nonpos.mpr hy),
        abs_of_nonpos (sub_nonpos.mpr (hx.trans hy))]
      ring
    · simp only [min_eq_right hx, min_eq_left hy, max_eq_left hx, max_eq_right hy,
        Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hy),
        abs_of_nonneg (sub_nonneg.mpr hx),
        abs_of_nonneg (sub_nonneg.mpr (hy.trans hx))]
      ring
    · simp [min_eq_right hx, min_eq_right hy, max_eq_left hx, max_eq_left hy]

  -- M04: both complete finite domain-sum bounds, with empty/reversed pairs retained.
  have clip_sums (c : ℝ) (E : ℕ × (ℕ → ℝ × ℝ)) :
      (∑ i ∈ range E.1, dist (min (E.2 i).1 c) (min (E.2 i).2 c)) ≤
        ∑ i ∈ range E.1, dist (E.2 i).1 (E.2 i).2 ∧
      (∑ i ∈ range E.1, dist (max (E.2 i).1 c) (max (E.2 i).2 c)) ≤
        ∑ i ∈ range E.1, dist (E.2 i).1 (E.2 i).2 := by
    constructor <;> apply Finset.sum_le_sum
    · intro i hi
      have hs := clip_dist_split c (E.2 i).1 (E.2 i).2
      linarith [dist_nonneg (x := max (E.2 i).1 c) (y := max (E.2 i).2 c)]
    · intro i hi
      have hs := clip_dist_split c (E.2 i).1 (E.2 i).2
      linarith [dist_nonneg (x := min (E.2 i).1 c) (y := min (E.2 i).2 c)]

  -- M05: actual pseudo-metric image triangle with SAME joining value.
  have clip_image_le (f : ℝ → X) (c x y : ℝ) :
      dist (f x) (f y) ≤
        dist (f (min x c)) (f (min y c)) + dist (f (max x c)) (f (max y c)) := by
    rcases le_total x c with hx | hx <;> rcases le_total y c with hy | hy
    · simp [min_eq_left hx, min_eq_left hy, max_eq_right hx, max_eq_right hy]
    · simpa only [min_eq_left hx, min_eq_right hy, max_eq_right hx, max_eq_left hy]
        using dist_triangle (f x) (f c) (f y)
    · simpa only [min_eq_right hx, min_eq_left hy, max_eq_left hx, max_eq_right hy, add_comm]
        using dist_triangle (f x) (f c) (f y)
    · simp [min_eq_right hx, min_eq_right hy, max_eq_left hx, max_eq_left hy]

  -- M06: complete image sum, actual finite sum addition.
  have clip_image_sums (f : ℝ → X) (c : ℝ) (E : ℕ × (ℕ → ℝ × ℝ)) :
      (∑ i ∈ range E.1, dist (f (E.2 i).1) (f (E.2 i).2)) ≤
        (∑ i ∈ range E.1, dist (f (min (E.2 i).1 c)) (f (min (E.2 i).2 c))) +
        ∑ i ∈ range E.1, dist (f (max (E.2 i).1 c)) (f (max (E.2 i).2 c)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i hi => clip_image_le f c _ _)
  apply (absolutelyContinuousOnInterval_iff f a b).mpr
  intro ε hε
  obtain ⟨δL, hL, hleft'⟩ :=
    (absolutelyContinuousOnInterval_iff f a c).mp hleft (ε / 2) (half_pos hε)
  obtain ⟨δR, hR, hright'⟩ :=
    (absolutelyContinuousOnInterval_iff f c b).mp hright (ε / 2) (half_pos hε)
  refine ⟨min δL δR, lt_min hL hR, ?_⟩
  intro E hE ht
  have hmem := clip_family hac hcb E hE
  have hsums := clip_sums c E
  have hl := hleft' (E.1, fun i => (min (E.2 i).1 c, min (E.2 i).2 c))
    hmem.1 (hsums.1.trans_lt (ht.trans_le (min_le_left _ _)))
  have hr := hright' (E.1, fun i => (max (E.2 i).1 c, max (E.2 i).2 c))
    hmem.2 (hsums.2.trans_lt (ht.trans_le (min_le_right _ _)))
  have himage := clip_image_sums f c E
  dsimp only at hl hr
  linarith

/-- Absolute continuity on the strict pieces of a finite weak subdivision
implies absolute continuity on the whole interval. Equal consecutive cuts are
singletons; induction joins each piece to its prefix without requiring matching
derivatives or any regularity outside the interval. -/
theorem of_monotone_subdivision {f : ℝ → X} {a b : ℝ} {n : ℕ}
    (cut : Fin (n + 1) → ℝ) (hcut : Monotone cut)
    (hfirst : cut 0 = a) (hlast : cut (Fin.last n) = b)
    (hpiece : ∀ i : Fin n, cut i.castSucc < cut i.succ →
      AbsolutelyContinuousOnInterval f (cut i.castSucc) (cut i.succ)) :
    AbsolutelyContinuousOnInterval f a b := by
  have singleton_ac (f : ℝ → X) (a : ℝ) :
      AbsolutelyContinuousOnInterval f a a := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := 0)
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    simp only [Set.uIcc_self, Set.mem_singleton_iff] at hx hy
    subst x
    subst y
    simp
  have hpieces (i : Fin n) :
      AbsolutelyContinuousOnInterval f (cut i.castSucc) (cut i.succ) := by
    have hle : cut i.castSucc ≤ cut i.succ :=
      hcut (by change i.val ≤ i.val + 1; omega)
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hpiece i hlt
    · rw [heq]
      exact singleton_ac f _
  have hprefix : ∀ k, 0 ≤ k → ∀ hk : k ≤ n,
      AbsolutelyContinuousOnInterval f (cut 0) (cut ⟨k, by omega⟩) := by
    apply Nat.le_induction
    · intro hk
      exact singleton_ac f (cut 0)
    · intro k hk ih hkn
      have hlt : k < n := by omega
      exact trans_of_le (ih (by omega)) (hpieces ⟨k, hlt⟩)
        (hcut (by change 0 ≤ k; omega)) (hcut (by change k ≤ k + 1; omega))
  have hfinal := hprefix n (Nat.zero_le n) le_rfl
  simpa only [hfirst, show (⟨n, by omega⟩ : Fin (n+1)) = Fin.last n from rfl, hlast]
    using hfinal

/-! ## Scalar absolute continuity and total variation -/

open MeasureTheory
open scoped ENNReal

/-- Every weak partition of a compact interval has its sum of absolute
increments bounded by the integral of the absolute derivative. Restrict the
same function to each piece, apply the absolute-continuity fundamental theorem,
then add adjacent integrals and enlarge the interval using nonnegativity. -/
theorem sum_abs_sub_le_integral_abs_deriv
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hab : a ≤ b)
    (N : ℕ) (u : ℕ → ℝ) (hu : Monotone u)
    (hu_mem : ∀ i, u i ∈ Set.Icc a b) :
    (∑ i ∈ Finset.range N, |f (u (i + 1)) - f (u i)|) ≤
      ∫ t in a..b, |deriv f t| := by
  have hsub (k : ℕ) : uIcc (u k) (u (k+1)) ⊆ uIcc a b := by
    rw [uIcc_of_le (hu (Nat.le_succ k)), uIcc_of_le hab]
    intro t ht
    exact ⟨(hu_mem k).1.trans ht.1, ht.2.trans (hu_mem (k+1)).2⟩
  have hg := hf.intervalIntegrable_deriv.abs
  have hincrement (k : ℕ) :
      |f (u (k+1)) - f (u k)| ≤ ∫ t in u k..u (k+1), |deriv f t| := by
    rw [← (hf.mono (hsub k)).integral_deriv_eq_sub]
    exact intervalIntegral.abs_integral_le_integral_abs (hu (Nat.le_succ k))
  calc
    (∑ i ∈ range N, |f (u (i+1)) - f (u i)|) ≤
        ∑ i ∈ range N, ∫ t in u i..u (i+1), |deriv f t| :=
      Finset.sum_le_sum (fun i hi => hincrement i)
    _ = ∫ t in u 0..u N, |deriv f t| :=
      intervalIntegral.sum_integral_adjacent_intervals (fun k hk => hg.mono_set (hsub k))
    _ ≤ ∫ t in a..b, |deriv f t| :=
      intervalIntegral.integral_mono_interval (hu_mem 0).1
        (hu (Nat.zero_le N)) (hu_mem N).2
        (Filter.Eventually.of_forall (fun t => abs_nonneg (deriv f t))) hg

/-- The extended total variation of a real absolutely continuous function is
bounded by the finite integral of its absolute derivative. Convert each actual
variation partition to its nonnegative real sum before taking the supremum;
no finiteness of the variation is assumed. -/
theorem eVariationOn_le_ofReal_integral_abs_deriv
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hab : a ≤ b) :
    eVariationOn f (Set.Icc a b) ≤
      ENNReal.ofReal (∫ t in a..b, |deriv f t|) := by
  unfold eVariationOn
  apply iSup_le
  intro p
  calc
    (∑ i ∈ range p.1, edist (f (p.2.1 (i+1))) (f (p.2.1 i))) =
        ENNReal.ofReal (∑ i ∈ range p.1, |f (p.2.1 (i+1)) - f (p.2.1 i)|) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => abs_nonneg _)]
      simp only [edist_dist, Real.dist_eq]
    _ ≤ ENNReal.ofReal (∫ t in a..b, |deriv f t|) :=
      ENNReal.ofReal_le_ofReal
        (sum_abs_sub_le_integral_abs_deriv hf hab p.1 p.2.1 p.2.2.1 p.2.2.2)

/-- Total variation is finite before it is interpreted as a real number;
that real variation lies between the absolute endpoint increment and the
integral of the absolute derivative. The endpoint estimate is the existing
bounded-variation inequality, while the upper bound comes from the extended
partition supremum. This states inequalities, not an equality characterization. -/
theorem variation_bounds_integral_abs_deriv
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hab : a ≤ b) :
    eVariationOn f (Set.Icc a b) ≠ ⊤ ∧
      |f b - f a| ≤ (eVariationOn f (Set.Icc a b)).toReal ∧
      (eVariationOn f (Set.Icc a b)).toReal ≤
        ∫ t in a..b, |deriv f t| := by
  have hbound := eVariationOn_le_ofReal_integral_abs_deriv hf hab
  have hfinite : eVariationOn f (Icc a b) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  have hJ : 0 ≤ ∫ t in a..b, |deriv f t| :=
    intervalIntegral.integral_nonneg_of_forall hab (fun t => abs_nonneg _)
  refine ⟨hfinite, ?_, ?_⟩
  · have hvariation : BoundedVariationOn f (Icc a b) := hfinite
    simpa only [Real.dist_eq] using
      hvariation.dist_le (show b ∈ Icc a b from ⟨hab, le_rfl⟩)
        (show a ∈ Icc a b from ⟨le_rfl, hab⟩)
  · exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
      (ENNReal.toReal_ofReal hJ)

/-- Equality between the integral of the absolute derivative and the net increase
forces a real absolutely continuous function to be nondecreasing on the whole
closed interval. The nonnegative integrable loss `|f'| - f'` has zero integral,
so the derivative is nonnegative almost everywhere. Restricting the same function
and applying the fundamental theorem gives every ordered endpoint increment.
Singleton intervals, constant portions and arbitrary exterior values are allowed. -/
theorem monotoneOn_of_integral_abs_deriv_eq_sub {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hab : a ≤ b)
    (heq : (∫ t in a..b, |deriv f t|) = f b - f a) :
    MonotoneOn f (Icc a b) := by
  have hi := hf.intervalIntegrable_deriv
  have hloss : IntervalIntegrable (fun t => |deriv f t| - deriv f t) volume a b :=
    hi.abs.sub hi
  have hz : (∫ t in a..b, |deriv f t| - deriv f t) = 0 := by
    rw [intervalIntegral.integral_sub hi.abs hi, heq, hf.integral_deriv_eq_sub, sub_self]
  have hzero : (fun t => |deriv f t| - deriv f t) =ᵐ[volume.restrict (Ioc a b)] 0 :=
    (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hab
      (Filter.Eventually.of_forall (fun t => sub_nonneg.mpr (le_abs_self (deriv f t))))
      hloss).mp hz
  have hsign : 0 ≤ᵐ[volume.restrict (Ioc a b)] deriv f := by
    filter_upwards [hzero] with t ht
    have he : |deriv f t| = deriv f t := sub_eq_zero.mp ht
    rw [← he]
    exact abs_nonneg _
  have hclosed : 0 ≤ᵐ[volume.restrict (Icc a b)] deriv f := by
    simpa only [MeasureTheory.restrict_Ioc_eq_restrict_Icc] using hsign
  intro x hx y hy hxy
  have hs : Icc x y ⊆ Icc a b :=
    fun _ ht => ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩
  have hus : uIcc x y ⊆ uIcc a b := by
    simpa only [uIcc_of_le hxy, uIcc_of_le hab] using hs
  have hrestricted := hf.mono hus
  have hnonneg : 0 ≤ ∫ t in x..y, deriv f t :=
    intervalIntegral.integral_nonneg_of_ae_restrict hxy
      (ae_restrict_of_ae_restrict_of_subset hs hclosed)
  rw [hrestricted.integral_deriv_eq_sub] at hnonneg
  exact sub_nonneg.mp hnonneg

end AbsolutelyContinuousOnInterval
