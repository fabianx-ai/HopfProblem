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

end Hyperbolic
