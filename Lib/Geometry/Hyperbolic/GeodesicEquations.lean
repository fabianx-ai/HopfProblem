module

public import Lib.Geometry.Hyperbolic.Models
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic

@[expose] public section
noncomputable section
namespace Hyperbolic
open Hyperbolic
open scoped BigOperators

/-- The coefficient functional giving a real plane equation in the fixed coordinates.
Textbook source: G05.A, lines 48–52. -/
def planeCoefficientFunctional (a b c : ℝ) : (Fin 3 → ℝ) →ₗ[ℝ] ℝ :=
  a • LinearMap.proj 0 + b • LinearMap.proj 1 + c • LinearMap.proj 2

/-- The coefficient functional evaluates to its ordinary coordinate equation.
Textbook source: G05.A, lines 51–52. -/
theorem planeCoefficientFunctional_apply (a b c : ℝ) (u : Fin 3 → ℝ) :
    planeCoefficientFunctional a b c u = a * u 0 + b * u 1 + c * u 2 := by
  rfl

/-- Every two-dimensional real plane admits nonzero equation coefficients and the
corresponding signed Lorentz normal. Extending a plane basis by one vector and
using its third coordinate proves both kernel inclusions; coordinate expansion
then gives the seven stated coefficient and normal identities.
Textbook source: G05.A, lines 48–54, with the fixed Context conventions. -/
theorem exists_planeCoefficientNormal
    (P : Submodule ℝ (Fin 3 → ℝ)) (hP : Module.finrank ℝ P = 2) :
    ∃ a b c : ℝ,
      ![a,b,c] ≠ (0 : Fin 3 → ℝ) ∧
      P = LinearMap.ker (planeCoefficientFunctional a b c) ∧
      P = (Hyperbolic.lorentzFunctional ![a,b,-c]).ker ∧
      ![a,b,-c] ≠ (0 : Fin 3 → ℝ) ∧
      Hyperbolic.lorentzBilinear ![a,b,-c] ![a,b,-c] = a^2+b^2-c^2 ∧
      (∀ u : Fin 3 → ℝ, u ∈ P ↔ a*u 0+b*u 1+c*u 2=0) ∧
      (∀ u : Fin 3 → ℝ, u ∈ P ↔
        Hyperbolic.lorentzBilinear u ![a,b,-c]=0) := by
  classical
  let bP : Module.Basis (Fin 2) ℝ P :=
    Module.finBasisOfFinrankEq ℝ P hP
  let v : Fin 2 → (Fin 3 → ℝ) := fun i => (bP i : Fin 3 → ℝ)
  have hv : LinearIndependent ℝ v := by
    exact bP.linearIndependent.map' P.subtype (Submodule.ker_subtype P)
  have hspan : Submodule.span ℝ (Set.range v) ≤ P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact (bP i).property
  have hex : ∃ w : Fin 3 → ℝ, w ∉ P := by
    by_contra! hn
    have htop : P = ⊤ := by
      ext u
      simp [hn u]
    have hf : Module.finrank ℝ P = 3 := by
      rw [htop]
      simp
    omega
  obtain ⟨w,hw⟩ := hex
  have hwspan : w ∉ Submodule.span ℝ (Set.range v) :=
    fun hm => hw (hspan hm)
  have hv3 : LinearIndependent ℝ (Fin.snoc v w : Fin 3 → (Fin 3 → ℝ)) :=
    linearIndependent_finSnoc.mpr ⟨hv,hwspan⟩
  let e : Module.Basis (Fin 3) ℝ (Fin 3 → ℝ) :=
    basisOfLinearIndependentOfCardEqFinrank hv3 (by simp)
  have he : (e : Fin 3 → (Fin 3 → ℝ)) = Fin.snoc v w := by
    exact coe_basisOfLinearIndependentOfCardEqFinrank hv3 (by simp)
  have he0 : e 0 = v 0 := by
    rw [he]
    simp
  have he1 : e 1 = v 1 := by
    rw [he]
    exact Fin.snoc_castSucc (α := fun _ : Fin 3 => Fin 3 → ℝ) w v (1 : Fin 2)
  have he2 : e 2 = w := by
    rw [he]
    exact Fin.snoc_last (α := fun _ : Fin 3 => Fin 3 → ℝ) w v
  let f : (Fin 3 → ℝ) →ₗ[ℝ] ℝ := e.coord 2
  have hf0 : f (v 0) = 0 := by
    rw [← he0]
    simp [f,Module.Basis.coord_apply]
  have hf1 : f (v 1) = 0 := by
    rw [← he1]
    simp [f,Module.Basis.coord_apply]
  have hfw : f w = 1 := by
    rw [← he2]
    simp [f,Module.Basis.coord_apply]
  have hPker : P = LinearMap.ker f := by
    ext u
    change u ∈ P ↔ f u = 0
    constructor
    · intro hu
      have hu' := congrArg P.subtype (bP.sum_repr ⟨u,hu⟩)
      have hu'' : (bP.repr ⟨u,hu⟩ 0) • v 0 +
          (bP.repr ⟨u,hu⟩ 1) • v 1 = u := by
        simpa only [Fin.sum_univ_two, map_add, map_smul, Submodule.subtype_apply, v]
          using hu'
      rw [← hu'']
      simp [hf0,hf1]
    · intro hfu
      have hz : e.repr u 2 = 0 := by
        simpa [f,Module.Basis.coord_apply] using hfu
      have hu' : (e.repr u 0) • v 0 + (e.repr u 1) • v 1 = u := by
        simpa only [Fin.sum_univ_three,he0,he1,he2,hz,zero_smul,add_zero]
          using e.sum_repr u
      rw [← hu']
      exact P.add_mem (P.smul_mem _ (bP 0).property)
        (P.smul_mem _ (bP 1).property)
  let a : ℝ := f ![1,0,0]
  let b : ℝ := f ![0,1,0]
  let c : ℝ := f ![0,0,1]
  have hfexpr (u : Fin 3 → ℝ) :
      f u = a*u 0+b*u 1+c*u 2 := by
    have hu : u = u 0 • (![1,0,0] : Fin 3 → ℝ) +
        u 1 • (![0,1,0] : Fin 3 → ℝ) +
        u 2 • (![0,0,1] : Fin 3 → ℝ) := by
      ext i
      fin_cases i <;> simp
    calc
      f u = f (u 0 • (![1,0,0] : Fin 3 → ℝ) +
          u 1 • (![0,1,0] : Fin 3 → ℝ) +
          u 2 • (![0,0,1] : Fin 3 → ℝ)) := congrArg f hu
      _ = a*u 0+b*u 1+c*u 2 := by
        simp only [map_add, map_smul, smul_eq_mul, a, b, c]
        ring
  have hfcoeff : f = planeCoefficientFunctional a b c := by
    apply LinearMap.ext
    intro u
    exact hfexpr u
  have hcoeff : ![a,b,c] ≠ (0 : Fin 3 → ℝ) := by
    intro hz
    have ha : a = 0 := by simpa using congrFun hz 0
    have hb : b = 0 := by simpa using congrFun hz 1
    have hc : c = 0 := by simpa using congrFun hz 2
    have hfzero : f w = 0 := by simp [hfexpr,ha,hb,hc]
    linarith
  have hnormal : ![a,b,-c] ≠ (0 : Fin 3 → ℝ) := by
    intro hz
    apply hcoeff
    have ha : a = 0 := by simpa using congrFun hz 0
    have hb : b = 0 := by simpa using congrFun hz 1
    have hc : c = 0 := by simpa using congrFun hz 2
    ext i
    fin_cases i <;> simp [ha,hb,hc]
  have hkernel : P = LinearMap.ker (planeCoefficientFunctional a b c) := by
    simpa only [hfcoeff] using hPker
  have hmem (u : Fin 3 → ℝ) :
      u ∈ P ↔ a*u 0+b*u 1+c*u 2=0 := by
    rw [hkernel]
    rfl
  have hLorentzKernel : P = (lorentzFunctional ![a,b,-c]).ker := by
    ext u
    change u ∈ P ↔ a*u 0+b*u 1-(-c)*u 2=0
    rw [hmem]
    ring_nf
  have hsq : lorentzBilinear ![a,b,-c] ![a,b,-c] = a^2+b^2-c^2 := by
    change a*a+b*b-(-c)*(-c)=a^2+b^2-c^2
    ring
  have hperp (u : Fin 3 → ℝ) :
      u ∈ P ↔ lorentzBilinear u ![a,b,-c]=0 := by
    change u ∈ P ↔ u 0*a+u 1*b-u 2*(-c)=0
    rw [hmem]
    ring_nf
  exact ⟨a,b,c,hcoeff,hkernel,hLorentzKernel,hnormal,hsq,hmem,hperp⟩

/-- A nonzero coefficient plane meeting the upper hyperboloid has positive Lorentz
normal discriminant. The signed normal is perpendicular to the given point, so
the positive Lorentz form on that point's tangent plane applies.
Textbook source: G05.B, lines 59–72, including the nonempty-section conclusion. -/
theorem planeCoefficient_discriminant_pos_of_mem
    (a b c : ℝ) (hcoeff : ![a,b,c] ≠ (0 : Fin 3 → ℝ))
    (p : Hyperboloid)
    (hp : p.val ∈ LinearMap.ker (planeCoefficientFunctional a b c)) :
    0 < a^2 + b^2 - c^2 := by
  have hn : ![a,b,-c] ≠ (0 : Fin 3 → ℝ) := by
    intro hz
    apply hcoeff
    have ha : a = 0 := by simpa using congrFun hz 0
    have hb : b = 0 := by simpa using congrFun hz 1
    have hc : c = 0 := by simpa using congrFun hz 2
    ext i
    fin_cases i <;> simp [ha,hb,hc]
  have hpn : lorentzBilinear p.val ![a,b,-c] = 0 := by
    change a*p.val 0+b*p.val 1+c*p.val 2=0 at hp
    change p.val 0*a+p.val 1*b-p.val 2*(-c)=0
    nlinarith only [hp]
  have hk : ![a,b,-c] ∈ (lorentzFunctional p.val).ker := by
    change lorentzFunctional p.val ![a,b,-c] = 0
    rw [← lorentzBilinear_eq_functional]
    exact hpn
  have hpos := lorentzKer_quadratic_pos p ![a,b,-c] hk hn
  have hsq : lorentzBilinear ![a,b,-c] ![a,b,-c] = a^2+b^2-c^2 := by
    change a*a+b*b-(-c)*(-c)=a^2+b^2-c^2
    ring
  rwa [hsq] at hpos

/-- A timelike coefficient plane has positive Lorentz normal discriminant.
The existing timelike-plane construction normalizes a negative vector and
chooses positive time; its upper-sheet point reduces to the pointwise result.
Textbook source: G05.B, lines 56–59 and 70–72. -/
theorem planeCoefficient_discriminant_pos_of_timelike
    (a b c : ℝ) (hcoeff : ![a,b,c] ≠ (0 : Fin 3 → ℝ))
    (hP : IsLorentzTimelikePlane
      (LinearMap.ker (planeCoefficientFunctional a b c))) :
    0 < a^2 + b^2 - c^2 := by
  obtain ⟨p,v,hvp,hvv,hpP,hvP,hspan,hrange⟩ :=
    IsLorentzTimelikePlane.exists_hyperboloidGeodesic hP
  exact planeCoefficient_discriminant_pos_of_mem a b c hcoeff p hpP

/-- Substituting the actual upper-half-plane coordinates into any coefficient
functional and clearing the positive height denominator gives its expanded
quadratic numerator. Textbook source: G05.D, lines 90–94. -/
theorem planeCoefficient_toHyperboloid_mul (a b c : ℝ) (z : UpperHalfPlane) :
    (2 * z.im) * planeCoefficientFunctional a b c (toHyperboloid z).val =
      2 * a * z.re + b * (z.re ^ 2 + z.im ^ 2 - 1) +
        c * (z.re ^ 2 + z.im ^ 2 + 1) := by
  change (2 * z.im) * (a * (z.re / z.im) +
    b * ((z.re ^ 2 + z.im ^ 2 - 1) / (2 * z.im)) +
    c * ((z.re ^ 2 + z.im ^ 2 + 1) / (2 * z.im))) = _
  field_simp [z.im_ne_zero]
  <;> ring

/-- The exact pullback of every real coefficient equation under the actual
model map is its collected quadratic equation. The equivalence includes the
zero coefficient triple. Textbook source: G05.D, lines 90–96 and 98. -/
theorem planeCoefficient_toHyperboloid_iff (a b c : ℝ) (z : UpperHalfPlane) :
    planeCoefficientFunctional a b c (toHyperboloid z).val = 0 ↔
      (b + c) * (z.re ^ 2 + z.im ^ 2) + 2 * a * z.re + (c - b) = 0 := by
  have hd : 2 * z.im ≠ 0 := mul_ne_zero (by norm_num) z.im_ne_zero
  have hcollect :
      2 * a * z.re + b * (z.re ^ 2 + z.im ^ 2 - 1) +
          c * (z.re ^ 2 + z.im ^ 2 + 1) =
        (b + c) * (z.re ^ 2 + z.im ^ 2) + 2 * a * z.re + (c - b) := by ring
  rw [← mul_eq_zero_iff_left hd, planeCoefficient_toHyperboloid_mul, hcollect]

/-- Positive discriminant gives the positive square roots and their exact squares,
and excludes the zero coefficient triple. Textbook source: G05.C, lines 74–75. -/
theorem planeCoefficient_positiveScalars (a b c : ℝ) (hD : 0 < a^2+b^2-c^2) :
    0 < Real.sqrt (a^2+b^2) ∧
    (Real.sqrt (a^2+b^2))^2 = a^2+b^2 ∧
    c^2 < (Real.sqrt (a^2+b^2))^2 ∧
    0 < Real.sqrt (a^2+b^2-c^2) ∧
    (Real.sqrt (a^2+b^2-c^2))^2 = a^2+b^2-c^2 ∧
    ![a,b,c] ≠ (0 : Fin 3 → ℝ) := by
  have hab : 0 < a^2+b^2 := by nlinarith [sq_nonneg c]
  have hs := Real.sqrt_pos.mpr hab
  have hs2 := Real.sq_sqrt hab.le
  have hd := Real.sqrt_pos.mpr hD
  have hd2 := Real.sq_sqrt hD.le
  refine ⟨hs,hs2,?_,hd,hd2,?_⟩
  · nlinarith
  · intro hz
    have ha : a = 0 := by simpa using congrFun hz 0
    have hb : b = 0 := by simpa using congrFun hz 1
    have hc : c = 0 := by simpa using congrFun hz 2
    simp [ha,hb,hc] at hD

/-- The explicit unit-direction coordinates of the coefficient plane.
Textbook source: G05.C, lines 76–78. -/
def planeCoefficientUnitDirection (a b : ℝ) : Fin 3 → ℝ :=
  ![-b / Real.sqrt (a^2+b^2), a / Real.sqrt (a^2+b^2), 0]

/-- The explicit negative-vector coordinates of the coefficient plane.
Textbook source: G05.C, lines 76–78. -/
def planeCoefficientNegativeVector (a b c : ℝ) : Fin 3 → ℝ :=
  ![-c*a / (Real.sqrt (a^2+b^2))^2,
    -c*b / (Real.sqrt (a^2+b^2))^2, 1]

/-- The displayed coefficient frame lies in the actual kernel and has the stated
Lorentz Gram entries and time coordinates. Textbook source: G05.C, lines 78–81. -/
theorem planeCoefficientFrame_spec (a b c : ℝ) (hD : 0 < a^2+b^2-c^2) :
    let e := planeCoefficientUnitDirection a b
    let w := planeCoefficientNegativeVector a b c
    e ∈ (planeCoefficientFunctional a b c).ker ∧
    w ∈ (planeCoefficientFunctional a b c).ker ∧
    lorentzBilinear e e = 1 ∧
    lorentzBilinear w w = -(a^2+b^2-c^2) / (Real.sqrt (a^2+b^2))^2 ∧
    lorentzBilinear e w = 0 ∧ e 2 = 0 ∧ w 2 = 1 ∧
    lorentzBilinear w w < 0 := by
  rcases planeCoefficient_positiveScalars a b c hD with ⟨hs,hs2,_,_,_,_⟩
  have hsn : Real.sqrt (a^2+b^2) ≠ 0 := ne_of_gt hs
  have hab : a^2+b^2 ≠ 0 := by rw [← hs2]; exact pow_ne_zero 2 hsn
  have he : planeCoefficientUnitDirection a b ∈ (planeCoefficientFunctional a b c).ker := by
    change a * (-b / Real.sqrt (a^2+b^2)) + b * (a / Real.sqrt (a^2+b^2)) + c * 0 = 0
    field_simp
    <;> ring
  have hw : planeCoefficientNegativeVector a b c ∈ (planeCoefficientFunctional a b c).ker := by
    change a * (-c*a / (Real.sqrt (a^2+b^2))^2) +
      b * (-c*b / (Real.sqrt (a^2+b^2))^2) + c * 1 = 0
    rw [hs2]
    field_simp
    <;> ring
  have hee : lorentzBilinear (planeCoefficientUnitDirection a b)
      (planeCoefficientUnitDirection a b) = 1 := by
    change (-b / Real.sqrt (a^2+b^2)) * (-b / Real.sqrt (a^2+b^2)) +
      (a / Real.sqrt (a^2+b^2)) * (a / Real.sqrt (a^2+b^2)) - 0 * 0 = 1
    field_simp
    nlinarith [hs2]
  have hww : lorentzBilinear (planeCoefficientNegativeVector a b c)
      (planeCoefficientNegativeVector a b c) = -(a^2+b^2-c^2) / (Real.sqrt (a^2+b^2))^2 := by
    change (-c*a / (Real.sqrt (a^2+b^2))^2) * (-c*a / (Real.sqrt (a^2+b^2))^2) +
      (-c*b / (Real.sqrt (a^2+b^2))^2) * (-c*b / (Real.sqrt (a^2+b^2))^2) - 1 * 1 =
        -(a^2+b^2-c^2) / (Real.sqrt (a^2+b^2))^2
    rw [hs2]
    field_simp
    <;> ring
  have hew : lorentzBilinear (planeCoefficientUnitDirection a b)
      (planeCoefficientNegativeVector a b c) = 0 := by
    change (-b / Real.sqrt (a^2+b^2)) * (-c*a / (Real.sqrt (a^2+b^2))^2) +
      (a / Real.sqrt (a^2+b^2)) * (-c*b / (Real.sqrt (a^2+b^2))^2) - 0 * 1 = 0
    field_simp
    <;> ring
  refine ⟨he,hw,hee,hww,hew,rfl,rfl,?_⟩
  rw [hww]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hD) (sq_pos_of_pos hs)

/-- The explicit frame is independent and spans the two-dimensional actual
coefficient kernel. Textbook source: G05.C, lines 80–82. -/
theorem planeCoefficientFrame_basis (a b c : ℝ) (hD : 0 < a^2+b^2-c^2) :
    let e := planeCoefficientUnitDirection a b
    let w := planeCoefficientNegativeVector a b c
    LinearIndependent ℝ ![e,w] ∧
    Module.finrank ℝ (planeCoefficientFunctional a b c).ker = 2 ∧
    Submodule.span ℝ ({e,w} : Set (Fin 3 → ℝ)) = (planeCoefficientFunctional a b c).ker := by
  rcases planeCoefficientFrame_spec a b c hD with ⟨he,hw,hee,_,_,het,hwt,_⟩
  let e := planeCoefficientUnitDirection a b
  let w := planeCoefficientNegativeVector a b c
  have hene : e ≠ 0 := by
    intro hz
    have h := hee
    change lorentzBilinear e e = 1 at h
    simp [hz,lorentzBilinear_apply] at h
  have hwne : w ≠ 0 := by
    intro hz
    have h := congrFun hz 2
    change w 2 = 0 at h
    change w 2 = 1 at hwt
    linarith
  have hli : LinearIndependent ℝ ![e,w] := by
    apply linearIndependent_fin2.mpr
    refine ⟨hwne,?_⟩
    intro α h
    change α • w = e at h
    have ht := congrFun h 2
    change α * w 2 = e 2 at ht
    change e 2 = 0 at het
    change w 2 = 1 at hwt
    rw [het,hwt,mul_one] at ht
    apply hene
    rw [← h,ht,zero_smul]
  have hf : planeCoefficientFunctional a b c ≠ 0 := by
    intro hz
    have ha : a = 0 := by
      simpa [planeCoefficientFunctional_apply] using
        congrArg (fun f : (Fin 3 → ℝ) →ₗ[ℝ] ℝ => f ![1,0,0]) hz
    have hb : b = 0 := by
      simpa [planeCoefficientFunctional_apply] using
        congrArg (fun f : (Fin 3 → ℝ) →ₗ[ℝ] ℝ => f ![0,1,0]) hz
    have hc : c = 0 := by
      simpa [planeCoefficientFunctional_apply] using
        congrArg (fun f : (Fin 3 → ℝ) →ₗ[ℝ] ℝ => f ![0,0,1]) hz
    simp [ha,hb,hc] at hD
  have hdim : Module.finrank ℝ (planeCoefficientFunctional a b c).ker = 2 := by
    have hr : Module.finrank ℝ (planeCoefficientFunctional a b c).ker + 1 = 3 := by
      simpa using Module.Dual.finrank_ker_add_one_of_ne_zero hf
    omega
  have hr : Set.range ![e,w] = ({e,w} : Set (Fin 3 → ℝ)) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
  have hspanDim : Module.finrank ℝ (Submodule.span ℝ ({e,w} : Set (Fin 3 → ℝ))) = 2 := by
    have h := finrank_span_eq_card hli
    rw [hr] at h
    exact h
  have hle : Submodule.span ℝ ({e,w} : Set (Fin 3 → ℝ)) ≤
      (planeCoefficientFunctional a b c).ker := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with rfl | hx
    · exact he
    · have : x = w := Set.mem_singleton_iff.mp hx
      subst x
      exact hw
  exact ⟨hli,hdim,Submodule.eq_of_le_of_finrank_eq hle (hspanDim.trans hdim.symm)⟩

/-- The restricted Lorentz quadratic form has one positive and one negative
square in the explicit frame. Textbook source: G05.C, lines 78–82. -/
theorem planeCoefficientFrame_gram (a b c : ℝ) (hD : 0 < a^2+b^2-c^2)
    (α β : ℝ) :
    lorentzBilinear
      (α • planeCoefficientUnitDirection a b + β • planeCoefficientNegativeVector a b c)
      (α • planeCoefficientUnitDirection a b + β • planeCoefficientNegativeVector a b c) =
      α^2 - ((a^2+b^2-c^2) / (Real.sqrt (a^2+b^2))^2) * β^2 := by
  rcases planeCoefficientFrame_spec a b c hD with ⟨_,_,hee,hww,hew,_,_,_⟩
  have hcalc :
      lorentzBilinear
        (α • planeCoefficientUnitDirection a b + β • planeCoefficientNegativeVector a b c)
        (α • planeCoefficientUnitDirection a b + β • planeCoefficientNegativeVector a b c) =
      α^2 * lorentzBilinear (planeCoefficientUnitDirection a b) (planeCoefficientUnitDirection a b) +
      2*α*β * lorentzBilinear (planeCoefficientUnitDirection a b) (planeCoefficientNegativeVector a b c) +
      β^2 * lorentzBilinear (planeCoefficientNegativeVector a b c) (planeCoefficientNegativeVector a b c) := by
    simp only [lorentzBilinear_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [hcalc,hee,hww,hew]
  ring

/-- The literal positive normalization of the displayed negative vector.
Textbook source: G05.C, line 83. -/
def planeCoefficientBaseCoords (a b c : ℝ) : Fin 3 → ℝ :=
  (Real.sqrt (a^2+b^2) / Real.sqrt (a^2+b^2-c^2)) • planeCoefficientNegativeVector a b c

/-- The normalized coordinates have square minus one and positive time.
Textbook source: G05.C, line 83. -/
theorem planeCoefficientBaseCoords_mem (a b c : ℝ) (hD : 0 < a^2+b^2-c^2) :
    (planeCoefficientBaseCoords a b c 0)^2 + (planeCoefficientBaseCoords a b c 1)^2 -
      (planeCoefficientBaseCoords a b c 2)^2 = -1 ∧
    0 < planeCoefficientBaseCoords a b c 2 := by
  rcases planeCoefficient_positiveScalars a b c hD with ⟨hs,hs2,_,hd,hd2,_⟩
  rcases planeCoefficientFrame_spec a b c hD with ⟨_,_,_,hww,_,_,hwt,_⟩
  let k := Real.sqrt (a^2+b^2) / Real.sqrt (a^2+b^2-c^2)
  let w := planeCoefficientNegativeVector a b c
  have hk : 0 < k := div_pos hs hd
  have hscale : lorentzBilinear (k • w) (k • w) = k^2 * lorentzBilinear w w := by
    simp only [lorentzBilinear_apply,Pi.smul_apply,smul_eq_mul]
    ring
  have hnorm : lorentzBilinear (k • w) (k • w) = -1 := by
    rw [hscale]
    change k^2 * lorentzBilinear (planeCoefficientNegativeVector a b c)
      (planeCoefficientNegativeVector a b c) = -1
    rw [hww]
    dsimp [k]
    rw [div_pow,hs2,hd2]
    have hab : a^2+b^2 ≠ 0 := by rw [← hs2]; exact pow_ne_zero 2 (ne_of_gt hs)
    field_simp
    <;> ring
  constructor
  · change (k • w) 0 ^ 2 + (k • w) 1 ^ 2 - (k • w) 2 ^ 2 = -1
    simpa only [lorentzBilinear_apply,pow_two] using hnorm
  · change 0 < k * w 2
    change w 2 = 1 at hwt
    rw [hwt,mul_one]
    exact hk

/-- The actual hyperboloid point with the explicitly normalized coordinates.
Textbook source: G05.C, line 83. -/
def planeCoefficientBasePoint (a b c : ℝ) (hD : 0 < a^2+b^2-c^2) : Hyperboloid :=
  ⟨planeCoefficientBaseCoords a b c, planeCoefficientBaseCoords_mem a b c hD⟩

/-- The same normalized point and explicit unit direction lie in and span the
coefficient kernel, with the required orthogonality. Textbook source: G05.C, lines 83–85. -/
theorem planeCoefficientBasePoint_spec (a b c : ℝ) (hD : 0 < a^2+b^2-c^2) :
    let p := planeCoefficientBasePoint a b c hD
    let e := planeCoefficientUnitDirection a b
    p.val ∈ (planeCoefficientFunctional a b c).ker ∧
    lorentzBilinear e p.val = 0 ∧ lorentzBilinear e e = 1 ∧
    Submodule.span ℝ ({p.val,e} : Set (Fin 3 → ℝ)) = (planeCoefficientFunctional a b c).ker := by
  rcases planeCoefficient_positiveScalars a b c hD with ⟨hs,_,_,hd,_,_⟩
  rcases planeCoefficientFrame_spec a b c hD with ⟨he,hw,hee,_,hew,_,_,_⟩
  have hspan := (planeCoefficientFrame_basis a b c hD).2.2
  let p := planeCoefficientBasePoint a b c hD
  let e := planeCoefficientUnitDirection a b
  let w := planeCoefficientNegativeVector a b c
  let k := Real.sqrt (a^2+b^2) / Real.sqrt (a^2+b^2-c^2)
  have hk : k ≠ 0 := ne_of_gt (div_pos hs hd)
  have hpval : p.val = k • w := rfl
  have hp : p.val ∈ (planeCoefficientFunctional a b c).ker := by
    rw [hpval]
    exact Submodule.smul_mem _ k hw
  have hep : lorentzBilinear e p.val = 0 := by
    have hscale : lorentzBilinear e p.val = k * lorentzBilinear e w := by
      rw [hpval]
      simp only [lorentzBilinear_apply,Pi.smul_apply,smul_eq_mul]
      ring
    rw [hscale,hew,mul_zero]
  have hle : Submodule.span ℝ ({p.val,e} : Set (Fin 3 → ℝ)) ≤
      (planeCoefficientFunctional a b c).ker := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with rfl | hx
    · exact hp
    · have : x = e := Set.mem_singleton_iff.mp hx
      subst x
      exact he
  have hge : (planeCoefficientFunctional a b c).ker ≤
      Submodule.span ℝ ({p.val,e} : Set (Fin 3 → ℝ)) := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with rfl | hx
    · exact Submodule.subset_span (by simp [e])
    · have : x = w := Set.mem_singleton_iff.mp hx
      subst x
      have hwp : k⁻¹ • p.val = w := by
        rw [hpval,smul_smul,inv_mul_cancel₀ hk,one_smul]
      change w ∈ Submodule.span ℝ ({p.val,e} : Set (Fin 3 → ℝ))
      rw [← hwp]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  exact ⟨hp,hep,hee,le_antisymm hle hge⟩

/-- Positive discriminant makes the actual coefficient kernel timelike, using
the displayed negative vector and derived dimension. Textbook source: G05.C, lines 80–83. -/
theorem planeCoefficient_timelike_of_discriminant_pos
    (a b c : ℝ) (hD : 0 < a^2+b^2-c^2) :
    IsLorentzTimelikePlane (planeCoefficientFunctional a b c).ker := by
  rcases planeCoefficientFrame_spec a b c hD with ⟨_,hw,_,_,_,_,_,hneg⟩
  have hdim := (planeCoefficientFrame_basis a b c hD).2.1
  exact ⟨hdim,planeCoefficientNegativeVector a b c,hw,hneg⟩

/-- The geodesic of the explicit point and direction parametrizes the entire
upper-sheet coefficient section for all real times; that section is nonempty.
Textbook source: G05.C, lines 83–88. -/
theorem planeCoefficient_whole_section (a b c : ℝ) (hD : 0 < a^2+b^2-c^2) :
    let p := planeCoefficientBasePoint a b c hD
    let e := planeCoefficientUnitDirection a b
    let hs := planeCoefficientBasePoint_spec a b c hD
    Set.range (hyperboloidGeodesic p e hs.2.1 hs.2.2.1) =
      {q : Hyperboloid | q.val ∈ (planeCoefficientFunctional a b c).ker} ∧
    ({q : Hyperboloid | q.val ∈ (planeCoefficientFunctional a b c).ker} : Set Hyperboloid).Nonempty := by
  let p := planeCoefficientBasePoint a b c hD
  let e := planeCoefficientUnitDirection a b
  have hs := planeCoefficientBasePoint_spec a b c hD
  have hr := (hyperboloidGeodesic_plane p e hs.2.1 hs.2.2.1).2.2.2
  have hr := hr.trans (congrArg
    (fun P : Submodule ℝ (Fin 3 → ℝ) => {q : Hyperboloid | q.val ∈ P}) hs.2.2.2)
  exact ⟨hr,p,hs.1⟩

/-- For every nonzero coefficient triple, the actual plane is timelike exactly
when its discriminant is positive. Textbook source: G05, lines 54 and 82. -/
theorem planeCoefficient_timelike_iff
    (a b c : ℝ) (hcoeff : ![a,b,c] ≠ (0 : Fin 3 → ℝ)) :
    IsLorentzTimelikePlane (planeCoefficientFunctional a b c).ker ↔ 0 < a^2+b^2-c^2 := by
  exact ⟨planeCoefficient_discriminant_pos_of_timelike a b c hcoeff,
    planeCoefficient_timelike_of_discriminant_pos a b c⟩

end Hyperbolic
