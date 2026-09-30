module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

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

end AbsolutelyContinuousOnInterval
