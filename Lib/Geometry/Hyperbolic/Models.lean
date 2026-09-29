module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Upper-half-plane and hyperboloid coordinates

The rational map `(x,y) ↦ (x/y,(x²+y²-1)/(2y),(x²+y²+1)/(2y))`
identifies the open upper half-plane with the positive sheet of
`X²+Y²-T²=-1`. Its literal inverse is `(X/(T-Y),1/(T-Y))`.
We prove the domain inequalities, both auxiliary coordinates `T-Y` and
`T+Y`, and both inverse identities before packaging the same maps as an
equivalence. The subsequent real smooth-coordinate section identifies the
actual ambient tangent image with the Lorentz perpendicular kernel, with
the literal inverse differential. Tensor, angle and length preservation
are separate later results and are not asserted here.

Textbook source: the reviewed ideal-reflection model bridge, section 2,
coordinate formulas and inverse (G01.a/b/c, canonical lines 82–89).
-/

@[expose] public section
noncomputable section
namespace Hyperbolic

/-- The positive sheet of the Lorentz hyperboloid, with coordinates ordered `X,Y,T`. -/
abbrev Hyperboloid : Type :=
  {p : Fin 3 → ℝ // p 0 ^ 2 + p 1 ^ 2 - p 2 ^ 2 = -1 ∧ 0 < p 2}

/-- The ambient rational formula for upper-half-plane to hyperboloid coordinates. -/
def upperHalfPlaneToHyperboloidCoords (z : ℂ) : Fin 3 → ℝ :=
  ![z.re / z.im,
    (z.re ^ 2 + z.im ^ 2 - 1) / (2 * z.im),
    (z.re ^ 2 + z.im ^ 2 + 1) / (2 * z.im)]

/-- The literal inverse rational coordinates; on the positive sheet its height is positive. -/
def hyperboloidToUpperHalfPlaneCoords (p : Fin 3 → ℝ) : ℂ :=
  ⟨p 0 / (p 2 - p 1), 1 / (p 2 - p 1)⟩

/-- A point of positive height maps to the hyperboloid equation and the positive sheet. -/
theorem upperHalfPlaneToHyperboloidCoords_mem (z : UpperHalfPlane) :
    (upperHalfPlaneToHyperboloidCoords (z : ℂ)) 0 ^ 2 +
      (upperHalfPlaneToHyperboloidCoords (z : ℂ)) 1 ^ 2 -
      (upperHalfPlaneToHyperboloidCoords (z : ℂ)) 2 ^ 2 = -1 ∧
    0 < (upperHalfPlaneToHyperboloidCoords (z : ℂ)) 2 := by
  change (z.re / z.im) ^ 2 + ((z.re ^ 2 + z.im ^ 2 - 1) / (2 * z.im)) ^ 2 -
    ((z.re ^ 2 + z.im ^ 2 + 1) / (2 * z.im)) ^ 2 = -1 ∧
    0 < (z.re ^ 2 + z.im ^ 2 + 1) / (2 * z.im)
  constructor
  · field_simp [z.im_ne_zero]
    <;> ring
  · exact div_pos (by nlinarith [sq_nonneg z.re, sq_nonneg z.im])
      (mul_pos (by norm_num) z.im_pos)

/-- The auxiliary null coordinate `T-Y` is the reciprocal of the original height. -/
theorem upperHalfPlaneToHyperboloidCoords_sub (z : UpperHalfPlane) :
    (upperHalfPlaneToHyperboloidCoords (z : ℂ)) 2 -
      (upperHalfPlaneToHyperboloidCoords (z : ℂ)) 1 = 1 / z.im := by
  change (z.re ^ 2 + z.im ^ 2 + 1) / (2 * z.im) -
    (z.re ^ 2 + z.im ^ 2 - 1) / (2 * z.im) = 1 / z.im
  field_simp [z.im_ne_zero]
  <;> ring

/-- The other auxiliary coordinate `T+Y` is `(x²+y²)/y`. -/
theorem upperHalfPlaneToHyperboloidCoords_add (z : UpperHalfPlane) :
    (upperHalfPlaneToHyperboloidCoords (z : ℂ)) 2 +
      (upperHalfPlaneToHyperboloidCoords (z : ℂ)) 1 =
      (z.re ^ 2 + z.im ^ 2) / z.im := by
  change (z.re ^ 2 + z.im ^ 2 + 1) / (2 * z.im) +
    (z.re ^ 2 + z.im ^ 2 - 1) / (2 * z.im) = (z.re ^ 2 + z.im ^ 2) / z.im
  field_simp [z.im_ne_zero]
  <;> ring

/-- The hyperboloid equation and positive sheet imply `|Y|<T`. -/
theorem hyperboloid_abs_y_lt_t (p : Hyperboloid) : |p.val 1| < p.val 2 := by
  apply abs_lt_of_sq_lt_sq ?_ p.property.2.le
  nlinarith [p.property.1, sq_nonneg (p.val 0)]

/-- The denominator of the literal inverse is strictly positive on the upper sheet. -/
theorem hyperboloid_denominator_pos (p : Hyperboloid) : 0 < p.val 2 - p.val 1 := by
  exact sub_pos.mpr ((le_abs_self (p.val 1)).trans_lt (hyperboloid_abs_y_lt_t p))

/-- The literal inverse coordinates have positive imaginary part. -/
theorem hyperboloidToUpperHalfPlaneCoords_im_pos (p : Hyperboloid) :
    0 < (hyperboloidToUpperHalfPlaneCoords p.val).im := by
  exact div_pos (by norm_num) (hyperboloid_denominator_pos p)

/-- Substitution of `T-Y=1/y` recovers both coordinates of every upper-half-plane point. -/
theorem hyperboloidCoords_left_inv (z : UpperHalfPlane) :
    hyperboloidToUpperHalfPlaneCoords
      (upperHalfPlaneToHyperboloidCoords (z : ℂ)) = (z : ℂ) := by
  apply Complex.ext
  · change (upperHalfPlaneToHyperboloidCoords (z : ℂ)) 0 /
      ((upperHalfPlaneToHyperboloidCoords (z : ℂ)) 2 -
       (upperHalfPlaneToHyperboloidCoords (z : ℂ)) 1) = z.re
    rw [upperHalfPlaneToHyperboloidCoords_sub]
    change (z.re / z.im) / (1 / z.im) = z.re
    field_simp [z.im_ne_zero]
  · change 1 / ((upperHalfPlaneToHyperboloidCoords (z : ℂ)) 2 -
      (upperHalfPlaneToHyperboloidCoords (z : ℂ)) 1) = z.im
    rw [upperHalfPlaneToHyperboloidCoords_sub]
    simp

/-- Substitution of the inverse recovers all three coordinates on the entire positive sheet. -/
theorem hyperboloidCoords_right_inv (p : Hyperboloid) :
    upperHalfPlaneToHyperboloidCoords
      (hyperboloidToUpperHalfPlaneCoords p.val) = p.val := by
  have hd : p.val 2 - p.val 1 ≠ 0 := ne_of_gt (hyperboloid_denominator_pos p)
  funext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  · change (p.val 0 / (p.val 2 - p.val 1)) / (1 / (p.val 2 - p.val 1)) = p.val 0
    field_simp [hd]
  · change ((p.val 0 / (p.val 2 - p.val 1)) ^ 2 +
      (1 / (p.val 2 - p.val 1)) ^ 2 - 1) /
      (2 * (1 / (p.val 2 - p.val 1))) = p.val 1
    field_simp [hd]
    nlinarith [p.property.1]
  · change ((p.val 0 / (p.val 2 - p.val 1)) ^ 2 +
      (1 / (p.val 2 - p.val 1)) ^ 2 + 1) /
      (2 * (1 / (p.val 2 - p.val 1))) = p.val 2
    field_simp [hd]
    nlinarith [p.property.1]

/-- The rational forward map with its proved positive-sheet membership. -/
def toHyperboloid (z : UpperHalfPlane) : Hyperboloid :=
  ⟨upperHalfPlaneToHyperboloidCoords (z : ℂ),
    upperHalfPlaneToHyperboloidCoords_mem z⟩

/-- The literal rational inverse, with its proved positive imaginary part. -/
def fromHyperboloid (p : Hyperboloid) : UpperHalfPlane :=
  ⟨hyperboloidToUpperHalfPlaneCoords p.val,
    hyperboloidToUpperHalfPlaneCoords_im_pos p⟩

/-- The underlying forward coordinates are exactly the displayed ambient formula. -/
theorem toHyperboloid_val (z : UpperHalfPlane) :
    (toHyperboloid z).val = upperHalfPlaneToHyperboloidCoords (z : ℂ) := rfl

/-- The underlying inverse coordinates are exactly the displayed ambient formula. -/
theorem fromHyperboloid_coe (p : Hyperboloid) :
    (fromHyperboloid p : ℂ) = hyperboloidToUpperHalfPlaneCoords p.val := rfl

/-- The actual-domain inverse after the forward map is identity. -/
theorem fromHyperboloid_toHyperboloid (z : UpperHalfPlane) :
    fromHyperboloid (toHyperboloid z) = z :=
  UpperHalfPlane.coe_injective (hyperboloidCoords_left_inv z)

/-- The actual-domain forward map after the inverse is identity. -/
theorem toHyperboloid_fromHyperboloid (p : Hyperboloid) :
    toHyperboloid (fromHyperboloid p) = p :=
  Subtype.ext (hyperboloidCoords_right_inv p)

/-- The explicit coordinate equivalence between the upper half-plane and the positive hyperboloid. -/
def upperHalfPlaneEquivHyperboloid : UpperHalfPlane ≃ Hyperboloid where
  toFun := toHyperboloid
  invFun := fromHyperboloid
  left_inv := fromHyperboloid_toHyperboloid
  right_inv := toHyperboloid_fromHyperboloid

/-- The equivalence uses the literal forward coordinate map. -/
theorem upperHalfPlaneEquivHyperboloid_apply (z : UpperHalfPlane) :
    upperHalfPlaneEquivHyperboloid z = toHyperboloid z := rfl

/-- The inverse equivalence uses the literal backward coordinate map. -/
theorem upperHalfPlaneEquivHyperboloid_symm_apply (p : Hyperboloid) :
    upperHalfPlaneEquivHyperboloid.symm p = fromHyperboloid p := rfl

open scoped Manifold ContDiff Topology
local notation "V" => (Fin 3 → ℝ)
local notation "F" => upperHalfPlaneToHyperboloidCoords
local notation "B" => hyperboloidToUpperHalfPlaneCoords
local notation "I" => 𝓘(ℝ, ℂ)
local notation "J" => 𝓘(ℝ, V)

/-- The displayed forward coordinates are real smooth on positive height (G01.d). -/
theorem contDiffOn_upperHalfPlaneToHyperboloidCoords :
    ContDiffOn ℝ ∞ F {z : ℂ | 0 < z.im} := by
  apply contDiffOn_pi.mpr
  intro i
  have hr : ContDiffOn ℝ ∞ Complex.re {z : ℂ | 0 < z.im} := Complex.reCLM.contDiff.contDiffOn
  have hi : ContDiffOn ℝ ∞ Complex.im {z : ℂ | 0 < z.im} := Complex.imCLM.contDiff.contDiffOn
  have hn : ∀ z ∈ {z : ℂ | 0 < z.im}, z.im ≠ 0 := fun z hz => ne_of_gt hz
  have h2 : ∀ z ∈ {z : ℂ | 0 < z.im}, 2 * z.im ≠ 0 :=
    fun z hz => mul_ne_zero (by norm_num) (hn z hz)
  fin_cases i
  · exact hr.div hi hn
  · exact ((hr.pow 2).add (hi.pow 2) |>.sub contDiffOn_const).div
      (contDiffOn_const.mul hi) h2
  · exact ((hr.pow 2).add (hi.pow 2) |>.add contDiffOn_const).div
      (contDiffOn_const.mul hi) h2

/-- The displayed inverse coordinates are real smooth where their denominator is positive (G01.d). -/
theorem contDiffOn_hyperboloidToUpperHalfPlaneCoords :
    ContDiffOn ℝ ∞ B {p : V | 0 < p 2 - p 1} := by
  have hp (i : Fin 3) : ContDiffOn ℝ ∞ (fun p : V => p i) {p : V | 0 < p 2 - p 1} :=
    (contDiff_apply ℝ ℝ i).contDiffOn
  have hd := (hp 2).sub (hp 1)
  have hn : ∀ p ∈ {p : V | 0 < p 2 - p 1}, p 2 - p 1 ≠ 0 := fun p hp => ne_of_gt hp
  have h := (Complex.equivRealProdCLM.symm.comp_contDiffOn_iff).mpr
    (((hp 0).div hd hn).prodMk ((contDiffOn_const (c := (1 : ℝ))).div hd hn))
  convert h using 1
  funext p
  apply Complex.ext <;> rfl

/-- The forward map is continuous for the ordinary hyperboloid subtype topology (G01.d). -/
theorem continuous_toHyperboloid : Continuous toHyperboloid := by
  apply Continuous.subtype_mk
  exact contDiffOn_upperHalfPlaneToHyperboloidCoords.continuousOn.comp_continuous
    UpperHalfPlane.continuous_coe (fun z => z.im_pos)

/-- The literal inverse is continuous for the existing upper-half-plane topology (G01.d). -/
theorem continuous_fromHyperboloid : Continuous fromHyperboloid := by
  apply UpperHalfPlane.isOpenEmbedding_coe.isEmbedding.continuous_iff.mpr
  exact contDiffOn_hyperboloidToUpperHalfPlaneCoords.continuousOn.comp_continuous
    continuous_subtype_val hyperboloid_denominator_pos

/-- The literal coordinate equivalence is a homeomorphism for the ordinary topologies (G01.d). -/
def upperHalfPlaneHomeomorphHyperboloid : UpperHalfPlane ≃ₜ Hyperboloid where
  toEquiv := upperHalfPlaneEquivHyperboloid
  continuous_toFun := continuous_toHyperboloid
  continuous_invFun := continuous_fromHyperboloid

/-- The topological equivalence retains exactly the original two maps (G01.d). -/
theorem upperHalfPlaneHomeomorphHyperboloid_toEquiv :
    upperHalfPlaneHomeomorphHyperboloid.toEquiv = upperHalfPlaneEquivHyperboloid := rfl

/-- The inverse coordinates give a global open chart on the hyperboloid (G01.d). -/
theorem isOpenEmbedding_hyperboloidCoords :
    Topology.IsOpenEmbedding (fun p : Hyperboloid => B p.val) :=
  UpperHalfPlane.isOpenEmbedding_coe.comp upperHalfPlaneHomeomorphHyperboloid.symm.isOpenEmbedding

/-- The global coordinate chart has exactly the positive-height half-plane as target (G01.d). -/
theorem range_hyperboloidCoords :
    Set.range (fun p : Hyperboloid => B p.val) = {z : ℂ | 0 < z.im} := by
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    exact hyperboloidToUpperHalfPlaneCoords_im_pos p
  · intro hz
    exact ⟨toHyperboloid ⟨z, hz⟩, hyperboloidCoords_left_inv ⟨z, hz⟩⟩

/-- The positive sheet contains the image of an upper-half-plane point (G01.d). -/
instance hyperboloidNonempty : Nonempty Hyperboloid := ⟨toHyperboloid default⟩
/-- The literal inverse coordinates define the singleton atlas on the ordinary subtype (G01.d). -/
instance hyperboloidChartedSpace : ChartedSpace ℂ Hyperboloid :=
  isOpenEmbedding_hyperboloidCoords.singletonChartedSpace
/-- The singleton atlas is a real smooth manifold atlas (G01.d). -/
instance hyperboloidIsManifoldReal : IsManifold I ∞ Hyperboloid :=
  isOpenEmbedding_hyperboloidCoords.isManifold_singleton
/-- The existing upper-half-plane atlas is used over the real scalar field (G01.d). -/
instance upperHalfPlaneIsManifoldReal : IsManifold I ∞ UpperHalfPlane :=
  UpperHalfPlane.isOpenEmbedding_coe.isManifold_singleton

/-- Every hyperboloid chart is the same prescribed inverse coordinate function (G01.d). -/
theorem hyperboloid_chartAt (p : Hyperboloid) :
    (chartAt ℂ p : Hyperboloid → ℂ) = fun q => B q.val := rfl
/-- The extended real chart retains the same inverse coordinates (G01.d). -/
theorem hyperboloid_extChartAt (p : Hyperboloid) :
    (extChartAt I p : Hyperboloid → ℂ) = fun q => B q.val := rfl
/-- On positive height the inverse chart has exactly the displayed ambient coordinates (G01.d). -/
theorem hyperboloid_extChartAt_symm_val (p : Hyperboloid) (z : ℂ) (hz : 0 < z.im) :
    ((extChartAt I p).symm z).val = F z := by
  have hr : z ∈ Set.range (fun q : Hyperboloid => B q.val) := by
    rw [range_hyperboloidCoords]
    exact hz
  have hq := Topology.IsOpenEmbedding.toOpenPartialHomeomorph_right_inv
    (fun q : Hyperboloid => B q.val) isOpenEmbedding_hyperboloidCoords hr
  change B ((extChartAt I p).symm z).val = z at hq
  exact (hyperboloidCoords_right_inv ((extChartAt I p).symm z)).symm.trans (congrArg F hq)

/-- The forward coordinate equivalence is real smooth in the stated atlases (G01.d). -/
theorem contMDiff_toHyperboloid : ContMDiff I I ∞ toHyperboloid := by
  apply ContMDiff.of_comp_isOpenEmbedding isOpenEmbedding_hyperboloidCoords
  have h : (fun p : Hyperboloid => B p.val) ∘ toHyperboloid = ((↑) : UpperHalfPlane → ℂ) := by
    funext z
    exact hyperboloidCoords_left_inv z
  rw [h]
  exact contMDiff_isOpenEmbedding UpperHalfPlane.isOpenEmbedding_coe

/-- The prescribed inverse is also real smooth, on the entire positive sheet (G01.d). -/
theorem contMDiff_fromHyperboloid : ContMDiff I I ∞ fromHyperboloid := by
  apply ContMDiff.of_comp_isOpenEmbedding UpperHalfPlane.isOpenEmbedding_coe
  exact contMDiff_isOpenEmbedding isOpenEmbedding_hyperboloidCoords

/-- The ordinary ambient inclusion is real smooth in the explicit surface chart (G01.d). -/
theorem contMDiff_hyperboloid_val : ContMDiff I J ∞ (fun p : Hyperboloid => p.val) := by
  intro p
  rw [contMDiffAt_iff]
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  simp only [mfld_simps]
  change ContDiffWithinAt ℝ ∞ (fun z : ℂ => ((extChartAt I p).symm z).val)
    Set.univ (B p.val)
  have hp : {z : ℂ | 0 < z.im} ∈ nhds (B p.val) :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds
      (hyperboloidToUpperHalfPlaneCoords_im_pos p)
  have h := (contDiffOn_upperHalfPlaneToHyperboloidCoords (B p.val)
    (hyperboloidToUpperHalfPlaneCoords_im_pos p)).contDiffAt hp
  apply h.contDiffWithinAt.congr_of_eventuallyEq
  · rw [nhdsWithin_univ]
    exact Filter.mem_of_superset hp (fun z hz => hyperboloid_extChartAt_symm_val p z hz)
  · exact hyperboloid_extChartAt_symm_val p (B p.val) (hyperboloidToUpperHalfPlaneCoords_im_pos p)

/-- The real differential of the forward rational coordinates, component by component (G01.e). -/
theorem fderiv_upperHalfPlaneToHyperboloidCoords (z : UpperHalfPlane) (v : ℂ) :
    fderiv ℝ F (z : ℂ) v =
      ![v.re / z.im - z.re * v.im / z.im ^ 2,
        z.re * v.re / z.im + (z.im ^ 2 - z.re ^ 2 + 1) * v.im / (2 * z.im ^ 2),
        z.re * v.re / z.im + (z.im ^ 2 - z.re ^ 2 - 1) * v.im / (2 * z.im ^ 2)] := by
  have hr : HasFDerivAt Complex.re Complex.reCLM (z : ℂ) := Complex.reCLM.hasFDerivAt
  have hi : HasFDerivAt Complex.im Complex.imCLM (z : ℂ) := Complex.imCLM.hasFDerivAt
  have hden := (hasFDerivAt_const (2 : ℝ) (z : ℂ)).mul hi
  have hn : 2 * z.im ≠ 0 := mul_ne_zero (by norm_num) z.im_ne_zero
  have hrec := (hasFDerivAt_inv z.im_ne_zero).comp (z : ℂ) hi
  have hrec2 := (hasFDerivAt_inv hn).comp (z : ℂ) hden
  have h0 := hr.mul hrec
  have h1 := (((hr.pow 2).add (hi.pow 2)).sub (hasFDerivAt_const (1 : ℝ) (z : ℂ))).mul hrec2
  have h2 := (((hr.pow 2).add (hi.pow 2)).add (hasFDerivAt_const (1 : ℝ) (z : ℂ))).mul hrec2
  simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Function.comp_apply] at h0 h1 h2
  change HasFDerivAt (fun w : ℂ => w.re * w.im⁻¹) _ _ at h0
  change HasFDerivAt (fun w : ℂ => (w.re ^ 2 + w.im ^ 2 - 1) * (2 * w.im)⁻¹) _ _ at h1
  change HasFDerivAt (fun w : ℂ => (w.re ^ 2 + w.im ^ 2 + 1) * (2 * w.im)⁻¹) _ _ at h2
  have hf : DifferentiableAt ℝ F (z : ℂ) :=
    ((contDiffOn_upperHalfPlaneToHyperboloidCoords (z : ℂ) z.im_pos).contDiffAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds z.im_pos)).differentiableAt (by simp)
  ext i
  have hc := (hasFDerivAt_pi'.mp hf.hasFDerivAt i).fderiv
  change ((ContinuousLinearMap.proj i).comp (fderiv ℝ F (z : ℂ))) v = _
  rw [← hc]
  fin_cases i
  · change fderiv ℝ (fun w : ℂ => w.re / w.im) (z : ℂ) v =
      v.re / z.im - z.re * v.im / z.im ^ 2
    simp only [div_eq_mul_inv]
    rw [h0.fderiv]
    simp
    ring
  · change fderiv ℝ (fun w : ℂ => (w.re ^ 2 + w.im ^ 2 - 1) / (2 * w.im)) (z : ℂ) v =
      z.re * v.re / z.im + (z.im ^ 2 - z.re ^ 2 + 1) * v.im / (2 * z.im ^ 2)
    simp only [div_eq_mul_inv]
    rw [h1.fderiv]
    simp
    field_simp [z.im_ne_zero]
    ring
  · change fderiv ℝ (fun w : ℂ => (w.re ^ 2 + w.im ^ 2 + 1) / (2 * w.im)) (z : ℂ) v =
      z.re * v.re / z.im + (z.im ^ 2 - z.re ^ 2 - 1) * v.im / (2 * z.im ^ 2)
    simp only [div_eq_mul_inv]
    rw [h2.fderiv]
    simp
    field_simp [z.im_ne_zero]
    ring

/-- The real differential of the inverse rational coordinates (G01.e). -/
theorem fderiv_hyperboloidToUpperHalfPlaneCoords (p : Hyperboloid) (w : V) :
    fderiv ℝ B p.val w =
      (⟨w 0 / (p.val 2 - p.val 1) - p.val 0 * (w 2 - w 1) / (p.val 2 - p.val 1) ^ 2,
        -(w 2 - w 1) / (p.val 2 - p.val 1) ^ 2⟩ : ℂ) := by
  have hd := (hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) p.val).sub
    (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) p.val)
  have hn := ne_of_gt (hyperboloid_denominator_pos p)
  have hi := (hasFDerivAt_inv hn).comp p.val hd
  have hr := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) p.val).mul hi
  have h := Complex.equivRealProdCLM.symm.toContinuousLinearMap.hasFDerivAt.comp p.val
    (hr.prodMk hi)
  change HasFDerivAt (fun q : V => Complex.equivRealProdCLM.symm
    (q 0 * (q 2 - q 1)⁻¹, (q 2 - q 1)⁻¹)) _ _ at h
  have he : B = fun q : V => Complex.equivRealProdCLM.symm
      (q 0 * (q 2 - q 1)⁻¹, (q 2 - q 1)⁻¹) := by
    funext q
    apply Complex.ext <;> simp [hyperboloidToUpperHalfPlaneCoords, div_eq_mul_inv]
  rw [he, h.fderiv]
  apply Complex.ext <;> simp [div_eq_mul_inv] <;> ring

/-- The Lorentz pairing with a fixed ambient vector, as a continuous linear functional (G01.e). -/
def lorentzFunctional (p : V) : V →L[ℝ] ℝ :=
  p 0 • ContinuousLinearMap.proj 0 + p 1 • ContinuousLinearMap.proj 1 -
    p 2 • ContinuousLinearMap.proj 2

/-- Evaluation of the Lorentz functional in ambient coordinates (G01.e). -/
theorem lorentzFunctional_apply (p w : V) :
    lorentzFunctional p w = p 0 * w 0 + p 1 * w 1 - p 2 * w 2 := rfl

/-- Forward coordinate derivatives are Lorentz-perpendicular to the image point (G01.e). -/
theorem fderiv_toHyperboloid_mem_ker (z : UpperHalfPlane) (v : ℂ) :
    fderiv ℝ F (z : ℂ) v ∈ (lorentzFunctional (toHyperboloid z).val).ker := by
  change lorentzFunctional (toHyperboloid z).val (fderiv ℝ F (z : ℂ) v) = 0
  rw [fderiv_upperHalfPlaneToHyperboloidCoords, lorentzFunctional_apply]
  simp [toHyperboloid, upperHalfPlaneToHyperboloidCoords]
  field_simp [z.im_ne_zero]
  ring

/-- The backward differential is a left inverse to the forward differential (G01.e). -/
theorem fderiv_hyperboloid_left_inv (z : UpperHalfPlane) (v : ℂ) :
    fderiv ℝ B (toHyperboloid z).val (fderiv ℝ F (z : ℂ) v) = v := by
  rw [fderiv_hyperboloidToUpperHalfPlaneCoords, fderiv_upperHalfPlaneToHyperboloidCoords]
  simp only [toHyperboloid_val, upperHalfPlaneToHyperboloidCoords_sub]
  apply Complex.ext <;> simp [upperHalfPlaneToHyperboloidCoords] <;>
    field_simp [z.im_ne_zero] <;> ring

/-- On the Lorentz-perpendicular kernel, the forward differential inverts the same backward differential (G01.e). -/
theorem fderiv_hyperboloid_right_inv (p : Hyperboloid) (w : V)
    (hw : w ∈ (lorentzFunctional p.val).ker) :
    fderiv ℝ F (fromHyperboloid p : ℂ) (fderiv ℝ B p.val w) = w := by
  have hd : p.val 2 - p.val 1 ≠ 0 := ne_of_gt (hyperboloid_denominator_pos p)
  change p.val 0 * w 0 + p.val 1 * w 1 - p.val 2 * w 2 = 0 at hw
  rw [fderiv_upperHalfPlaneToHyperboloidCoords, fderiv_hyperboloidToUpperHalfPlaneCoords]
  ext i
  fin_cases i <;> simp [fromHyperboloid, hyperboloidToUpperHalfPlaneCoords] <;>
    field_simp [hd]
  · ring
  · nlinarith [congrArg (fun t : ℝ => t * w 1) p.property.1,
      congrArg (fun t : ℝ => t * w 2) p.property.1,
      congrArg (fun t : ℝ => t * p.val 1) hw,
      congrArg (fun t : ℝ => t * p.val 2) hw]
  · nlinarith [congrArg (fun t : ℝ => t * w 1) p.property.1,
      congrArg (fun t : ℝ => t * w 2) p.property.1,
      congrArg (fun t : ℝ => t * p.val 1) hw,
      congrArg (fun t : ℝ => t * p.val 2) hw]

/-- The forward differential has exactly the Lorentz-perpendicular kernel as its ambient image (G01.e). -/
theorem range_fderiv_toHyperboloid (p : Hyperboloid) :
    (fderiv ℝ F (fromHyperboloid p : ℂ)).range = (lorentzFunctional p.val).ker := by
  ext w
  constructor
  · rintro ⟨v, rfl⟩
    have h := fderiv_toHyperboloid_mem_ker (fromHyperboloid p) v
    rw [toHyperboloid_fromHyperboloid] at h
    exact h
  · intro hw
    exact ⟨fderiv ℝ B p.val w, fderiv_hyperboloid_right_inv p w hw⟩

/-- The forward differential is injective because its literal backward differential is a left inverse (G01.e). -/
theorem injective_fderiv_toHyperboloid (z : UpperHalfPlane) :
    Function.Injective (fderiv ℝ F (z : ℂ)) :=
  Function.LeftInverse.injective (fderiv_hyperboloid_left_inv z)

/-- In the actual real singleton chart, the inclusion differential is the displayed forward derivative (G01.e). -/
theorem mfderiv_hyperboloid_val (p : Hyperboloid) :
    mfderiv I J (fun q : Hyperboloid => q.val) p = fderiv ℝ F (fromHyperboloid p : ℂ) := by
  apply HasMFDerivAt.mfderiv
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  simp only [mfld_simps]
  change HasFDerivWithinAt (fun z : ℂ => ((extChartAt I p).symm z).val)
    (fderiv ℝ F (fromHyperboloid p : ℂ)) Set.univ (fromHyperboloid p : ℂ)
  have hp : {z : ℂ | 0 < z.im} ∈ nhds (fromHyperboloid p : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds (fromHyperboloid p).im_pos
  have hf := ((contDiffOn_upperHalfPlaneToHyperboloidCoords _ (fromHyperboloid p).im_pos).contDiffAt
    hp).differentiableAt (by simp)
  apply HasFDerivAt.hasFDerivWithinAt
  apply hf.hasFDerivAt.congr_of_eventuallyEq
  exact Filter.mem_of_superset hp (fun z hz => hyperboloid_extChartAt_symm_val p z hz)

/-- The actual inclusion derivative has precisely the Lorentz-perpendicular image (G01.e). -/
theorem range_mfderiv_hyperboloid_val (p : Hyperboloid) :
    (mfderiv I J (fun q : Hyperboloid => q.val) p).range = (lorentzFunctional p.val).ker := by
  rw [mfderiv_hyperboloid_val]
  exact range_fderiv_toHyperboloid p

/-- Intrinsic backward-after-forward differentials compose to identity (G01.e). -/
theorem mfderiv_fromHyperboloid_comp_toHyperboloid (z : UpperHalfPlane) :
    (mfderiv I I fromHyperboloid (toHyperboloid z)).comp (mfderiv I I toHyperboloid z) =
      ContinuousLinearMap.id ℝ (TangentSpace I z) := by
  rw [← mfderiv_comp z
    (contMDiff_fromHyperboloid.mdifferentiable (by simp) (toHyperboloid z))
    (contMDiff_toHyperboloid.mdifferentiable (by simp) z)]
  have h : fromHyperboloid ∘ toHyperboloid = id := funext fromHyperboloid_toHyperboloid
  rw [h, mfderiv_id]

/-- Intrinsic forward-after-backward differentials compose to identity (G01.e). -/
theorem mfderiv_toHyperboloid_comp_fromHyperboloid (p : Hyperboloid) :
    (mfderiv I I toHyperboloid (fromHyperboloid p)).comp (mfderiv I I fromHyperboloid p) =
      ContinuousLinearMap.id ℝ (TangentSpace I p) := by
  rw [← mfderiv_comp p
    (contMDiff_toHyperboloid.mdifferentiable (by simp) (fromHyperboloid p))
    (contMDiff_fromHyperboloid.mdifferentiable (by simp) p)]
  have h : toHyperboloid ∘ fromHyperboloid = id := funext toHyperboloid_fromHyperboloid
  rw [h, mfderiv_id]

set_option backward.isDefEq.respectTransparency false in
/-- Intrinsic tangent vectors identify continuously and linearly with the ambient Lorentz kernel,
with inverse the restriction of the literal backward differential (G01.e). -/
def hyperboloidTangentEquivKer (p : Hyperboloid) :
    TangentSpace I p ≃L[ℝ] (lorentzFunctional p.val).ker :=
  { (mfderiv I J (fun q : Hyperboloid => q.val) p).codRestrict
      (lorentzFunctional p.val).ker (fun v => by
        rw [← range_mfderiv_hyperboloid_val p]
        exact ⟨v, rfl⟩) with
    invFun := (fderiv ℝ B p.val).domRestrict (lorentzFunctional p.val).ker
    continuous_toFun := ((mfderiv I J (fun q : Hyperboloid => q.val) p).codRestrict
      (lorentzFunctional p.val).ker (fun v => by
        rw [← range_mfderiv_hyperboloid_val p]
        exact ⟨v, rfl⟩)).continuous
    continuous_invFun := ((fderiv ℝ B p.val).domRestrict (lorentzFunctional p.val).ker).continuous
    left_inv := fun v => by
      change fderiv ℝ B p.val (mfderiv I J (fun q : Hyperboloid => q.val) p v) = v
      rw [mfderiv_hyperboloid_val]
      have h := fderiv_hyperboloid_left_inv (fromHyperboloid p) v
      rw [toHyperboloid_fromHyperboloid] at h
      exact h
    right_inv := fun w => by
      apply Subtype.ext
      change mfderiv I J (fun q : Hyperboloid => q.val) p (fderiv ℝ B p.val w.val) = w.val
      rw [mfderiv_hyperboloid_val]
      exact fderiv_hyperboloid_right_inv p w.val w.property }

/-- The forward tangent identification is exactly the actual inclusion derivative (G01.e). -/
theorem hyperboloidTangentEquivKer_apply (p : Hyperboloid) (v : TangentSpace I p) :
    (hyperboloidTangentEquivKer p v).val = mfderiv I J (fun q : Hyperboloid => q.val) p v := rfl

/-- The inverse tangent identification is exactly the same restricted backward derivative (G01.e). -/
theorem hyperboloidTangentEquivKer_symm_apply (p : Hyperboloid)
    (w : (lorentzFunctional p.val).ker) :
    (hyperboloidTangentEquivKer p).symm w = fderiv ℝ B p.val w.val := rfl

/-- The actual inverse chart agrees locally with the ambient forward coordinates (G01.d/e). -/
theorem hyperboloid_chart_inverse_eventually (p : Hyperboloid) :
    (fun z : ℂ => ((extChartAt I p).symm z).val) =ᶠ[nhds (fromHyperboloid p : ℂ)] F :=
  Filter.mem_of_superset ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds
    (fromHyperboloid p).im_pos) (fun z hz => hyperboloid_extChartAt_symm_val p z hz)

end Hyperbolic
