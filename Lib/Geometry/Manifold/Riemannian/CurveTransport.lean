module
public import Lib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Order.Fin.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.Basic
public import Lib.Order.Fin.Refinement
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Order.Interval.Set.Union
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Tactic
public import Mathlib.Geometry.Manifold.Riemannian.PathELength
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.ENNReal.BigOperators
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Topology.Order.Compact
/-!
# Pointwise speed, inverse differentials, curve transport and finite well-defined length

For the SAME positive smooth tangent metrics, differentiating a composed
curve applies the map's differential to its original velocity. The tensor
identity makes that very differential a linear isometry, hence preserves
both real and extended speed. The within version uses the same parameter
set and its unique differential, so includes one-sided velocities on
nondegenerate closed pieces. No inverse map, integrated length, global
extension across joints, or distance conclusion is asserted here.

This is the generic pointwise part of the ordinary Riemannian chain-rule
argument; finite-piece length transport is a separate later result.

For a smooth diffeomorphism, differentiating both inverse identities gives
the two inverse differential laws. Forward tensor preservation then yields
inverse tensor preservation at every target point, using its actual base
identity, and hence both inverse norm equalities for the same metrics.

Smooth composition also preserves the full class of continuous curves that
are C1 on each strict closed piece of a fixed weak subdivision. A smooth
diffeomorphism gives both inverse transports with the same cuts and literal
endpoints, independently of the tensor results. No length assertion is made.
-/

@[expose] public section
noncomputable section
open scoped Bundle Manifold ContDiff Topology ENNReal
namespace Manifold
universe uE uH uM uF uK uN
/-- A smooth forward tensor-preserving map preserves the real and extended
speed of a differentiable curve: the chain rule uses the SAME differential
whose inner-product identity supplies its linear isometry. -/
theorem speed_comp_of_tensorPreserving
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    {K : Type uK} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
    {N : Type uN} [TopologicalSpace N] [ChartedSpace K N]
    [IsManifold J ∞ N]
    (G : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M => TangentSpace I x))
    (G' : Bundle.ContMDiffRiemannianMetric J ∞ F (fun y : N => TangentSpace J y))
    (f : M → N) (hf : ContMDiff I J ∞ f)
    (hTensor : ∀ (x : M) (v w : TangentSpace I x),
      G'.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) = G.inner x v w)
    (γ : ℝ → M) (t : ℝ) (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨G.toRiemannianMetric⟩
    letI : Bundle.RiemannianBundle (fun y : N => TangentSpace J y) :=
      ⟨G'.toRiemannianMetric⟩
    ‖mfderiv 𝓘(ℝ, ℝ) J (f ∘ γ) t (1 : ℝ)‖ = ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ ∧
      ‖mfderiv 𝓘(ℝ, ℝ) J (f ∘ γ) t (1 : ℝ)‖ₑ = ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ := by
  letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨G.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle (fun y : N => TangentSpace J y) :=
    ⟨G'.toRiemannianMetric⟩
  let A : TangentSpace I (γ t) →ₗ[ℝ] TangentSpace J (f (γ t)) :=
    (mfderiv I J f (γ t)).toLinearMap
  let L : TangentSpace I (γ t) →ₗᵢ[ℝ] TangentSpace J (f (γ t)) :=
    A.isometryOfInner (hTensor (γ t))
  have hchain := mfderiv_comp_apply t
    (hf.mdifferentiable (by simp) (γ t)) hγ (1 : ℝ)
  constructor
  · rw [hchain]
    exact L.norm_map _
  · rw [hchain]
    exact L.enorm_map _

/-- The same speed equality holds for a within velocity on the SAME parameter
set, using its unique differential. On a nondegenerate closed piece this
retains that piece's one-sided endpoint velocities, without a global extension. -/
theorem speedWithin_comp_of_tensorPreserving
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    {K : Type uK} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
    {N : Type uN} [TopologicalSpace N] [ChartedSpace K N]
    [IsManifold J ∞ N]
    (G : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M => TangentSpace I x))
    (G' : Bundle.ContMDiffRiemannianMetric J ∞ F (fun y : N => TangentSpace J y))
    (f : M → N) (hf : ContMDiff I J ∞ f)
    (hTensor : ∀ (x : M) (v w : TangentSpace I x),
      G'.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) = G.inner x v w)
    (γ : ℝ → M) (s : Set ℝ) (t : ℝ)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    (hs : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) s t) :
    letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨G.toRiemannianMetric⟩
    letI : Bundle.RiemannianBundle (fun y : N => TangentSpace J y) :=
      ⟨G'.toRiemannianMetric⟩
    ‖mfderivWithin 𝓘(ℝ, ℝ) J (f ∘ γ) s t (1 : ℝ)‖ =
        ‖mfderivWithin 𝓘(ℝ, ℝ) I γ s t (1 : ℝ)‖ ∧
      ‖mfderivWithin 𝓘(ℝ, ℝ) J (f ∘ γ) s t (1 : ℝ)‖ₑ =
        ‖mfderivWithin 𝓘(ℝ, ℝ) I γ s t (1 : ℝ)‖ₑ := by
  letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨G.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle (fun y : N => TangentSpace J y) :=
    ⟨G'.toRiemannianMetric⟩
  let A : TangentSpace I (γ t) →ₗ[ℝ] TangentSpace J (f (γ t)) :=
    (mfderiv I J f (γ t)).toLinearMap
  let L : TangentSpace I (γ t) →ₗᵢ[ℝ] TangentSpace J (f (γ t)) :=
    A.isometryOfInner (hTensor (γ t))
  have hchain := congrArg (fun B => B (1 : ℝ))
    (mfderiv_comp_mfderivWithin t (hf.mdifferentiable (by simp) (γ t)) hγ hs)
  constructor
  · rw [hchain]
    exact L.norm_map _
  · rw [hchain]
    exact L.enorm_map _

/-- Differentiating the inverse-after-forward identity gives the identity on
the original tangent module, together with its actual inverse base equality. -/
theorem mfderiv_symm_comp_of_diffeomorph
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    {K : Type uK} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
    {N : Type uN} [TopologicalSpace N] [ChartedSpace K N]
    [IsManifold J ∞ N]
    (e : M ≃ₘ⟮I, J⟯ N) (x : M) :
    e.symm (e x) = x ∧
      (mfderiv J I e.symm (e x)).comp (mfderiv I J e x) =
        ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  have hchain := mfderiv_comp x
    (e.symm.mdifferentiable (by simp) (e x)) (e.mdifferentiable (by simp) x)
  have hfun : (e.symm : N → M) ∘ (e : M → N) = id :=
    funext e.symm_apply_apply
  have hcongr : mfderiv I I ((e.symm : N → M) ∘ (e : M → N)) x =
      mfderiv I I (id : M → M) x := mfderiv_congr hfun
  have hid : mfderiv I I (id : M → M) x =
      ContinuousLinearMap.id ℝ (TangentSpace I x) := mfderiv_id
  exact ⟨e.symm_apply_apply x, hchain.symm.trans (hcongr.trans hid)⟩

/-- Differentiating forward-after-inverse gives the identity at every target
point, together with the actual target base equality. -/
theorem mfderiv_comp_symm_of_diffeomorph
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    {K : Type uK} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
    {N : Type uN} [TopologicalSpace N] [ChartedSpace K N]
    [IsManifold J ∞ N]
    (e : M ≃ₘ⟮I, J⟯ N) (y : N) :
    e (e.symm y) = y ∧
      (mfderiv I J e (e.symm y)).comp (mfderiv J I e.symm y) =
        ContinuousLinearMap.id ℝ (TangentSpace J y) := by
  have hchain := mfderiv_comp y
    (e.mdifferentiable (by simp) (e.symm y)) (e.symm.mdifferentiable (by simp) y)
  have hfun : (e : M → N) ∘ (e.symm : N → M) = id :=
    funext e.apply_symm_apply
  have hcongr : mfderiv J J ((e : M → N) ∘ (e.symm : N → M)) y =
      mfderiv J J (id : N → N) y := mfderiv_congr hfun
  have hid : mfderiv J J (id : N → N) y =
      ContinuousLinearMap.id ℝ (TangentSpace J y) := mfderiv_id
  exact ⟨e.apply_symm_apply y, hchain.symm.trans (hcongr.trans hid)⟩

/-- Forward tensor preservation implies inverse tensor preservation: substitute
the inverse differential vectors and transport the metric along the actual
inverse base equality before evaluating the differentiated inverse identity. -/
theorem symm_tensorPreserving_of_diffeomorph
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    {K : Type uK} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
    {N : Type uN} [TopologicalSpace N] [ChartedSpace K N]
    [IsManifold J ∞ N]
    (G : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M => TangentSpace I x))
    (G' : Bundle.ContMDiffRiemannianMetric J ∞ F (fun y : N => TangentSpace J y))
    (e : M ≃ₘ⟮I, J⟯ N)
    (hTensor : ∀ (x : M) (v w : TangentSpace I x),
      G'.inner (e x) (mfderiv I J e x v) (mfderiv I J e x w) = G.inner x v w)
    (y : N) (u v : TangentSpace J y) :
    G.inner (e.symm y) (mfderiv J I e.symm y u) (mfderiv J I e.symm y v) =
      G'.inner y u v := by
  have hright := (mfderiv_comp_symm_of_diffeomorph e y).2
  have heval (w : TangentSpace J y) :
      mfderiv I J e (e.symm y) (mfderiv J I e.symm y w) = w :=
    congrArg (fun L => L w) hright
  have hcastN {z z' : N} (hz : z = z') (w : TangentSpace J z) :
      cast (congrArg (TangentSpace J) hz) w = w := by
    cases hz
    rfl
  have hmetricBase {z z' : N} (hz : z = z') (a b : TangentSpace J z) :
      G'.inner z a b = G'.inner z'
        (cast (congrArg (TangentSpace J) hz) a)
        (cast (congrArg (TangentSpace J) hz) b) := by
    cases hz
    rfl
  have hsub := hTensor (e.symm y)
    (mfderiv J I e.symm y u) (mfderiv J I e.symm y v)
  have hbase := hmetricBase (e.apply_symm_apply y)
    (mfderiv I J e (e.symm y) (mfderiv J I e.symm y u))
    (mfderiv I J e (e.symm y) (mfderiv J I e.symm y v))
  have hbaseEval :
      G'.inner (e (e.symm y))
        (mfderiv I J e (e.symm y) (mfderiv J I e.symm y u))
        (mfderiv I J e (e.symm y) (mfderiv J I e.symm y v)) = G'.inner y u v :=
    hbase.trans ((congrArg₂ (fun a b : TangentSpace J y => G'.inner y a b)
      (hcastN (e.apply_symm_apply y) _)
      (hcastN (e.apply_symm_apply y) _)).trans
        (congrArg₂ (fun a b : TangentSpace J y => G'.inner y a b) (heval u) (heval v)))
  exact hsub.symm.trans hbaseEval

/-- The inverse differential preserves both real and extended norms for the
SAME given metrics, by its derived tensor identity and the induced isometry. -/
theorem symm_norm_enorm_of_tensorPreserving
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    {K : Type uK} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
    {N : Type uN} [TopologicalSpace N] [ChartedSpace K N]
    [IsManifold J ∞ N]
    (G : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M => TangentSpace I x))
    (G' : Bundle.ContMDiffRiemannianMetric J ∞ F (fun y : N => TangentSpace J y))
    (e : M ≃ₘ⟮I, J⟯ N)
    (hTensor : ∀ (x : M) (v w : TangentSpace I x),
      G'.inner (e x) (mfderiv I J e x v) (mfderiv I J e x w) = G.inner x v w)
    (y : N) (u : TangentSpace J y) :
    letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨G.toRiemannianMetric⟩
    letI : Bundle.RiemannianBundle (fun y : N => TangentSpace J y) :=
      ⟨G'.toRiemannianMetric⟩
    ‖mfderiv J I e.symm y u‖ = ‖u‖ ∧
      ‖mfderiv J I e.symm y u‖ₑ = ‖u‖ₑ := by
  letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨G.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle (fun y : N => TangentSpace J y) :=
    ⟨G'.toRiemannianMetric⟩
  let A : TangentSpace J y →ₗ[ℝ] TangentSpace I (e.symm y) :=
    (mfderiv J I e.symm y).toLinearMap
  have hInner (u v : TangentSpace J y) : inner ℝ (A u) (A v) = inner ℝ u v :=
    symm_tensorPreserving_of_diffeomorph G G' e hTensor y u v
  let L : TangentSpace J y →ₗᵢ[ℝ] TangentSpace I (e.symm y) :=
    A.isometryOfInner hInner
  exact ⟨L.norm_map u, L.enorm_map u⟩

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : Type uK} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  {N : Type uN} [TopologicalSpace N] [ChartedSpace K N]

/-- Continuous curves on a fixed weak subdivision, C1 on each strict closed piece.
Repeated cuts impose no singleton derivative condition. -/
def IsPiecewiseC1On (I : ModelWithCorners ℝ E H)
    (γ : ℝ → M) (a b : ℝ) (n : ℕ) (cut : Fin (n + 1) → ℝ) : Prop :=
  Monotone cut ∧ cut 0 = a ∧ cut (Fin.last n) = b ∧
  ContinuousOn γ (Set.Icc a b) ∧
  ∀ i : Fin n, cut i.castSucc < cut i.succ →
    ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc (cut i.castSucc) (cut i.succ))

/-- Fixed-subdivision piecewise C1 curves with literal endpoints and arbitrary
values outside the parameter interval. -/
def PiecewiseC1CurveOn (I : ModelWithCorners ℝ E H)
    (a b : ℝ) (n : ℕ) (cut : Fin (n + 1) → ℝ) (p q : M) :=
  {γ : ℝ → M // IsPiecewiseC1On I γ a b n cut ∧ γ a = p ∧ γ b = q}

/-- Smooth composition preserves the same weak subdivision and closed pieces. -/
theorem IsPiecewiseC1On.comp_contMDiff
    {γ : ℝ → M} {a b : ℝ} {n : ℕ} {cut : Fin (n + 1) → ℝ}
    (hγ : IsPiecewiseC1On I γ a b n cut)
    {f : M → N} (hf : ContMDiff I J ∞ f) :
    IsPiecewiseC1On J (f ∘ γ) a b n cut := by
  refine ⟨hγ.1, hγ.2.1, hγ.2.2.1,
    hf.continuous.comp_continuousOn hγ.2.2.2.1, ?_⟩
  intro i hi
  exact (hf.of_le (by simp)).comp_contMDiffOn (hγ.2.2.2.2 i hi)

/-- Compose a fixed-subdivision curve with a smooth map, preserving both endpoints. -/
def PiecewiseC1CurveOn.map
    {a b : ℝ} {n : ℕ} {cut : Fin (n + 1) → ℝ} {p q : M}
    (f : M → N) (hf : ContMDiff I J ∞ f)
    (γ : PiecewiseC1CurveOn I a b n cut p q) :
    PiecewiseC1CurveOn J a b n cut (f p) (f q) :=
  ⟨f ∘ γ.val, γ.property.1.comp_contMDiff hf,
    congrArg f γ.property.2.1, congrArg f γ.property.2.2⟩

/-- The mapped curve is pointwise the actual composition, at every parameter. -/
theorem PiecewiseC1CurveOn.map_apply
    {a b : ℝ} {n : ℕ} {cut : Fin (n + 1) → ℝ} {p q : M}
    (f : M → N) (hf : ContMDiff I J ∞ f)
    (γ : PiecewiseC1CurveOn I a b n cut p q) (t : ℝ) :
    (PiecewiseC1CurveOn.map f hf γ).val t = f (γ.val t) := rfl

/-- A diffeomorphism gives an equivalence of the full fixed-subdivision curve
classes; its inverse is composition with the actual inverse diffeomorphism. -/
def PiecewiseC1CurveOn.mapEquiv
    {a b : ℝ} {n : ℕ} {cut : Fin (n + 1) → ℝ} {p q : M}
    (e : M ≃ₘ⟮I, J⟯ N) :
    PiecewiseC1CurveOn I a b n cut p q ≃
      PiecewiseC1CurveOn J a b n cut (e p) (e q) :=
  { toFun := PiecewiseC1CurveOn.map e e.contMDiff
    invFun := fun η =>
      ⟨e.symm ∘ η.val, η.property.1.comp_contMDiff e.symm.contMDiff,
        (congrArg e.symm η.property.2.1).trans (e.symm_apply_apply p),
        (congrArg e.symm η.property.2.2).trans (e.symm_apply_apply q)⟩
    left_inv := fun γ => Subtype.ext (funext (fun t =>
      (congrArg e.symm (PiecewiseC1CurveOn.map_apply e e.contMDiff γ t)).trans
        (e.symm_apply_apply (γ.val t))))
    right_inv := fun η => Subtype.ext (funext (fun t =>
      (PiecewiseC1CurveOn.map_apply e e.contMDiff
        ⟨e.symm ∘ η.val, η.property.1.comp_contMDiff e.symm.contMDiff,
          (congrArg e.symm η.property.2.1).trans (e.symm_apply_apply p),
          (congrArg e.symm η.property.2.2).trans (e.symm_apply_apply q)⟩ t).trans
        (e.apply_symm_apply (η.val t)))) }

/-- The forward equivalence function is the smooth composition constructor. -/
theorem PiecewiseC1CurveOn.mapEquiv_apply
    {a b : ℝ} {n : ℕ} {cut : Fin (n + 1) → ℝ} {p q : M}
    (e : M ≃ₘ⟮I, J⟯ N)
    (γ : PiecewiseC1CurveOn I a b n cut p q) :
    PiecewiseC1CurveOn.mapEquiv e γ =
      PiecewiseC1CurveOn.map e e.contMDiff γ := rfl

/-- The inverse equivalence evaluates to the actual inverse composition. -/
theorem PiecewiseC1CurveOn.mapEquiv_symm_apply
    {a b : ℝ} {n : ℕ} {cut : Fin (n + 1) → ℝ} {p q : M}
    (e : M ≃ₘ⟮I, J⟯ N)
    (η : PiecewiseC1CurveOn J a b n cut (e p) (e q)) (t : ℝ) :
    ((PiecewiseC1CurveOn.mapEquiv e).symm η).val t = e.symm (η.val t) := rfl


/-! ## Finite well-defined length (textbook j.3–j.6) -/
open scoped BigOperators
open Set MeasureTheory Filter
section LengthUpstream
variable [IsManifold I ∞ M]
local instance lengthTangentT2 (x : M) : T2Space (TangentSpace I x) :=
  FiberBundle.t2Space E (fun x : M => TangentSpace I x) x

/-- j.5: real length is the finite sum of the closed-piece speed integrals. -/
def piecewiseC1Length
    [FiniteDimensional ℝ E]
    (G : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M => TangentSpace I x))
    (γ : ℝ → M) {n : ℕ} (cut : Fin (n + 1) → ℝ) : ℝ :=
  letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨G.toRiemannianMetric⟩
  ∑ i : Fin n, ∫ t in cut i.castSucc..cut i.succ,
    ‖mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc (cut i.castSucc) (cut i.succ)) t (1 : ℝ)‖

/-- j.3: actual intrinsic speed is continuous on each strict closed C1 piece. -/
theorem continuousOn_pieceSpeed
    [FiniteDimensional ℝ E]
    (G : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M => TangentSpace I x))
    (γ : ℝ → M) {a b : ℝ} (hab : a < b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b)) :
    letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨G.toRiemannianMetric⟩
    ContinuousOn
      (fun t => ‖mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc a b) t (1 : ℝ)‖)
      (Icc a b) := by
  have pieceDirect {l r : ℝ} (hlr : l < r)
      (hpiece : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc l r)) :
      letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨G.toRiemannianMetric⟩
      ContinuousOn
        (fun t => ‖mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc l r) t (1 : ℝ)‖)
        (Icc l r) := by
    let S : Set ℝ := Icc l r
    let V : (t : ℝ) → TangentSpace I (γ t) :=
      fun t => mfderivWithin 𝓘(ℝ, ℝ) I γ S t (1 : ℝ)
    let Vtotal : ℝ → TangentBundle I M :=
      fun t => Bundle.TotalSpace.mk' E (γ t) (V t)

    -- P01: actual source total space, original bundle topology, real unit section.
    let u : ℝ → TangentBundle 𝓘(ℝ, ℝ) ℝ :=
      fun t => (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm (t, (1 : ℝ))
    let πsource : TangentBundle 𝓘(ℝ, ℝ) ℝ → ℝ :=
      Bundle.TotalSpace.proj
    have hu : Continuous u :=
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
        (continuous_id.prodMk continuous_const)
    have huPoint (t : ℝ) :
        u t = Bundle.TotalSpace.mk' ℝ t (1 : ℝ) := rfl
    have huProj (t : ℝ) : πsource (u t) = t := rfl
    have hs : UniqueMDiffOn 𝓘(ℝ, ℝ) S :=
      fun t ht => (uniqueDiffOn_Icc hlr t ht).uniqueMDiffWithinAt
    have hT : ContinuousOn
        (tangentMapWithin 𝓘(ℝ, ℝ) I γ S :
          TangentBundle 𝓘(ℝ, ℝ) ℝ → TangentBundle I M)
        (πsource ⁻¹' S) :=
      hpiece.continuousOn_tangentMapWithin (by simp) hs
    have hmap : MapsTo u S (πsource ⁻¹' S) := by
      intro t ht
      change πsource (u t) ∈ S
      simpa only [huProj] using ht
    have hEval (t : ℝ) :
        tangentMapWithin 𝓘(ℝ, ℝ) I γ S (u t) =
          Bundle.TotalSpace.mk' E (γ t)
            (mfderivWithin 𝓘(ℝ, ℝ) I γ S t (1 : ℝ)) := rfl
    have hcomp : ContinuousOn
        ((tangentMapWithin 𝓘(ℝ, ℝ) I γ S) ∘ u) S :=
      hT.comp hu.continuousOn hmap
    have hVelocity : ContinuousOn Vtotal S := by
      simpa only [Function.comp_def, hEval] using hcomp
    have hLeft : ContinuousWithinAt Vtotal S l :=
      hVelocity l ⟨le_rfl, hlr.le⟩
    have hRight : ContinuousWithinAt Vtotal S r :=
      hVelocity r ⟨hlr.le, le_rfl⟩

    -- P02: capture ORIGINAL topology before the SAME metric registration.
    let tE : (x : M) → TopologicalSpace (TangentSpace I x) := fun _ => inferInstance
    let tTotal : TopologicalSpace (TangentBundle I M) := inferInstance
    letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨G.toRiemannianMetric⟩
    have hTopology (x : M) :
        (inferInstance : NormedAddCommGroup (TangentSpace I x)).toMetricSpace.toUniformSpace.toTopologicalSpace =
          tE x := rfl
    have hTotalTopology :
        (inferInstance : TopologicalSpace (TangentBundle I M)) = tTotal := rfl
    have hInner (x : M) (v w : TangentSpace I x) :
        inner ℝ v w = G.inner x v w := rfl
    have hNorm (x : M) (v : TangentSpace I x) :
        ‖v‖ = Real.sqrt (G.inner x v v) := norm_eq_sqrt_real_inner v
    have hEnorm (x : M) (v : TangentSpace I x) :
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x v v)) := by
      rw [← hNorm x v]
      exact (ofReal_norm v).symm
    have hFinite (x : M) (v : TangentSpace I x) : ‖v‖ₑ < (∞ : ℝ≥0∞) :=
      enorm_lt_top
    have hSmooth : IsContMDiffRiemannianBundle I ∞ E
        (fun x : M => TangentSpace I x) := inferInstance
    letI hContinuous : IsContinuousRiemannianBundle E
        (fun x : M => TangentSpace I x) :=
      ⟨⟨G.toContinuousRiemannianMetric.inner,
        G.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
    have hContinuousInstance : IsContinuousRiemannianBundle E
        (fun x : M => TangentSpace I x) := inferInstance
    have hVelocityInner : ContinuousOn
        (fun t => G.inner (γ t) (V t) (V t)) S :=
      hVelocity.inner_bundle hVelocity
    have hVelocitySqrt : ContinuousOn
        (fun t => Real.sqrt (G.inner (γ t) (V t) (V t))) S :=
      hVelocityInner.sqrt
    let σ : ℝ → ℝ := fun t => ‖V t‖
    have hcDirect : ContinuousOn σ S := by
      simpa only [σ, hNorm] using hVelocitySqrt
    exact hcDirect

  exact pieceDirect hab hγ

/-- j.4–j.5: every allowed speed representative is integrable and computes the finite piece-sum length. -/
theorem IsPiecewiseC1On.speedRepresentative_length
    [FiniteDimensional ℝ E]
    (G : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M => TangentSpace I x))
    {γ : ℝ → M} {a b : ℝ} {n : ℕ} {cut : Fin (n + 1) → ℝ}
    (hγ : IsPiecewiseC1On I γ a b n cut) (σ : ℝ → ℝ) :
    letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨G.toRiemannianMetric⟩
    (∀ i : Fin n, EqOn σ
      (fun t => ‖mfderivWithin 𝓘(ℝ, ℝ) I γ
        (Icc (cut i.castSucc) (cut i.succ)) t (1 : ℝ)‖)
      (Ioo (cut i.castSucc) (cut i.succ))) →
    (∀ t ∈ range cut, 0 ≤ σ t) →
    Measurable (fun t : Icc a b => σ t.val) ∧
    IntegrableOn σ (Icc a b) volume ∧
    (∀ t ∈ Icc a b, 0 ≤ σ t) ∧
    (σ =ᵐ[volume.restrict (Icc a b)]
      fun t => ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖) ∧
    (∫ t in a..b, σ t) = piecewiseC1Length G γ cut ∧
    (∫ t in Icc a b, σ t) = piecewiseC1Length G γ cut ∧
    (∫⁻ t in Icc a b, ENNReal.ofReal (σ t)) =
      ENNReal.ofReal (piecewiseC1Length G γ cut) := by
  letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨G.toRiemannianMetric⟩
  intro σrep cutNonneg
  -- Same topology and metric registration in the shared piece/whole context.
  let tE : (x : M) → TopologicalSpace (TangentSpace I x) := fun _ => inferInstance
  letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨G.toRiemannianMetric⟩
  have hTopology (x : M) :
      (inferInstance : NormedAddCommGroup (TangentSpace I x)).toMetricSpace.toUniformSpace.toTopologicalSpace =
        tE x := rfl
  have hInner (x : M) (v w : TangentSpace I x) : inner ℝ v w = G.inner x v w := rfl
  have hEnorm (x : M) (v : TangentSpace I x) : ENNReal.ofReal ‖v‖ = ‖v‖ₑ := ofReal_norm v
  let S : Set ℝ := Icc a b
  let C : Set ℝ := range cut
  let P : Fin n → Set ℝ := fun i => Icc (cut i.castSucc) (cut i.succ)
  let U : Fin n → Set ℝ := fun i => Ioo (cut i.castSucc) (cut i.succ)
  let V : (t : ℝ) → TangentSpace I (γ t) :=
    fun t => mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)
  let W : (i : Fin n) → (t : ℝ) → TangentSpace I (γ t) :=
    fun i t => mfderivWithin 𝓘(ℝ, ℝ) I γ (P i) t (1 : ℝ)
  let q : Fin n → ℝ → ℝ := fun i t => ‖W i t‖
  let v : ℝ → ℝ := fun t => ‖V t‖
  have hfinite : C.Finite := Set.finite_range cut
  have hcuts : C ⊆ S := by
    rintro t ⟨k, rfl⟩
    exact ⟨hγ.2.1 ▸ hγ.1 (show (0 : Fin (n + 1)) ≤ k by change 0 ≤ k.val; omega),
      hγ.2.2.1 ▸ hγ.1 (show k ≤ Fin.last n by change k.val ≤ n; omega)⟩
  have hab : a ≤ b := by
    simpa only [hγ.2.1, hγ.2.2.1] using
      hγ.1 (show (0 : Fin (n + 1)) ≤ Fin.last n by change 0 ≤ n; omega)
  have hzero : n = 0 → a = b := by
    intro hn
    have hidx : (0 : Fin (n + 1)) = Fin.last n := by apply Fin.ext; simp [hn]
    exact hγ.2.1.symm.trans ((congrArg cut hidx).trans hγ.2.2.1)
  have hopenSub : ∀ i : Fin n, U i ⊆ P i := fun _ _ ht => ⟨ht.1.le, ht.2.le⟩
  have hpieceSub : ∀ i : Fin n, P i ⊆ S := by
    intro i t ht
    exact ⟨(hcuts ⟨i.castSucc, rfl⟩).1.trans ht.1,
      ht.2.trans (hcuts ⟨i.succ, rfl⟩).2⟩
  have hrepeated : ∀ i : Fin n, cut i.castSucc = cut i.succ → U i = ∅ := by
    intro i hi
    simp [U, hi]
  let cN : ℕ → ℝ := fun k =>
    if hk : k < n + 1 then cut ⟨k, hk⟩ else cut (Fin.last n)
  have hN0 : cN 0 = cut 0 := by simp [cN]
  have hNlast : cN n = cut (Fin.last n) := by simp [cN, Fin.last]
  have hNleft : ∀ i : Fin n, cN i.val = cut i.castSucc := by
    intro i
    simp only [cN, dif_pos (show i.val < n + 1 by omega)]
    rfl
  have hNright : ∀ i : Fin n, cN (i.val + 1) = cut i.succ := by
    intro i
    simp only [cN, dif_pos (show i.val + 1 < n + 1 by omega)]
    rfl
  have hNcover : Ico (cN 0) (cN n) ⊆
      ⋃ k ∈ Finset.range n, Ico (cN k) (cN (k + 1)) :=
    Ico_subset_biUnion_Ico n cN
  have hindex : (⋃ k ∈ Finset.range n, Ico (cN k) (cN (k + 1))) =
      ⋃ i : Fin n, Ico (cut i.castSucc) (cut i.succ) := by
    ext t
    constructor
    · intro ht
      rcases mem_iUnion.1 ht with ⟨k, hk⟩
      rcases mem_iUnion.1 hk with ⟨hk, ht⟩
      let i : Fin n := ⟨k, Finset.mem_range.1 hk⟩
      exact mem_iUnion.2 ⟨i, by simpa only [← hNleft i, ← hNright i] using ht⟩
    · intro ht
      rcases mem_iUnion.1 ht with ⟨i, ht⟩
      exact mem_iUnion.2 ⟨i.val, mem_iUnion.2 ⟨Finset.mem_range.2 i.isLt,
        by simpa only [hNleft i, hNright i] using ht⟩⟩
  have hcoverOff : S \ C ⊆ ⋃ i : Fin n, U i := by
    intro t ht
    have htb : t < b := lt_of_le_of_ne ht.1.2 (by
      intro h
      exact ht.2 ⟨Fin.last n, hγ.2.2.1.trans h.symm⟩)
    have hmem : t ∈ Ico (cN 0) (cN n) := by
      simpa only [hN0, hNlast, hγ.2.1, hγ.2.2.1] using ⟨ht.1.1, htb⟩
    have hm := hNcover hmem
    rw [hindex] at hm
    rcases mem_iUnion.1 hm with ⟨i, hi⟩
    exact mem_iUnion.2 ⟨i, lt_of_le_of_ne hi.1 (by
      intro heq
      exact ht.2 ⟨i.castSucc, heq⟩), hi.2⟩
  have hcover : S = C ∪ ⋃ i : Fin n, U i := by
    ext t
    constructor
    · intro ht
      by_cases hc : t ∈ C
      · exact Or.inl hc
      · exact Or.inr (hcoverOff ⟨ht, hc⟩)
    · rintro (hc | hu)
      · exact hcuts hc
      · rcases mem_iUnion.1 hu with ⟨i, hi⟩
        exact hpieceSub i (hopenSub i hi)
  have hdisjoint : Pairwise (fun i j : Fin n => Disjoint (U i) (U j)) := by
    intro i j hij
    apply Set.disjoint_left.2
    intro t hi hj
    rcases lt_or_gt_of_ne hij with hij | hji
    · have h := hγ.1 (show i.succ ≤ j.castSucc by
        change i.val + 1 ≤ j.val
        change i.val < j.val at hij
        omega)
      exact (not_lt_of_ge h) (hj.1.trans hi.2)
    · have h := hγ.1 (show j.succ ≤ i.castSucc by
        change j.val + 1 ≤ i.val
        change j.val < i.val at hji
        omega)
      exact (not_lt_of_ge h) (hi.1.trans hj.2)
  have hdiff : ∀ (i : Fin n) (t : ℝ), t ∈ U i →
      MDifferentiableAt 𝓘(ℝ, ℝ) I γ t := by
    intro i t ht
    exact ((hγ.2.2.2.2 i (ht.1.trans ht.2)).mdifferentiableOn
      (by simp) t ⟨ht.1.le, ht.2.le⟩).mdifferentiableAt
        (Icc_mem_nhds ht.1 ht.2)
  have hvelocity : ∀ (i : Fin n) (t : ℝ), t ∈ U i → W i t = V t := by
    intro i t ht
    exact congrArg (fun L => L (1 : ℝ))
      (mfderivWithin_of_mem_nhds (I := 𝓘(ℝ, ℝ)) (I' := I)
        (f := γ) (Icc_mem_nhds ht.1 ht.2))
  have hspeed : ∀ (i : Fin n) (t : ℝ), t ∈ U i → q i t = v t := by
    intro i t ht
    exact congrArg (fun w : TangentSpace I (γ t) => ‖w‖) (hvelocity i t ht)
  -- Actual copied direct j.3 calculation, NOT a temporary P02 contract.
  have hqcont : ∀ i : Fin n, cut i.castSucc < cut i.succ → ContinuousOn (q i) (P i) := by
    intro i hi
    exact continuousOn_pieceSpeed G γ hi (hγ.2.2.2.2 i hi)
  have hqint : ∀ i : Fin n, cut i.castSucc < cut i.succ → IntegrableOn (q i) (P i) volume := by
    intro i hi
    exact (hqcont i hi).integrableOn_Icc
  have hpieceLe : ∀ i : Fin n, cut i.castSucc ≤ cut i.succ := by
    intro i
    exact hγ.1 (show i.castSucc ≤ i.succ by change i.val ≤ i.val + 1; omega)
  -- Accepted REAL PIECE SUM, independent of the chosen whole representative.
  let L : ℝ := ∑ i : Fin n, ∫ t in cut i.castSucc..cut i.succ, q i t


  have hσUi : ∀ i : Fin n, Measurable (fun t : U i => σ t.val) := by
    intro i
    by_cases hi : cut i.castSucc < cut i.succ
    · exact ((hqcont i hi).mono (hopenSub i) |>.congr (σrep i)).domRestrict.measurable
    · have he : U i = ∅ := Ioo_eq_empty_of_le (le_of_not_gt hi)
      have hc : ContinuousOn σ (U i) := he.symm ▸ continuousOn_empty σ
      exact hc.domRestrict.measurable
  have hcompat : ∀ (i j : Fin n) (t : ℝ) (hi : t ∈ U i) (hj : t ∈ U j),
      (fun x : U i => σ x.val) ⟨t, hi⟩ = (fun x : U j => σ x.val) ⟨t, hj⟩ :=
    fun _ _ _ _ _ => rfl
  have hUiMeas : ∀ i : Fin n, MeasurableSet (U i) := fun _ => measurableSet_Ioo
  have hlift := measurable_iUnionLift hcompat hcoverOff hUiMeas hσUi
  have hliftEq : Set.iUnionLift U (fun i (x : U i) => σ x.val)
      hcompat (S \ C) hcoverOff = (fun t : ↥(S \ C) => σ t.val) := by
    funext t
    rcases mem_iUnion.1 (hcoverOff t.property) with ⟨i, hi⟩
    exact Set.iUnionLift_of_mem t hi
  have hσoff : Measurable (fun t : ↥(S \ C) => σ t.val) := hliftEq ▸ hlift
  let CS : Set S := {t | t.val ∈ C}
  have hCSfinite : CS.Finite := hfinite.preimage Subtype.val_injective.injOn
  let toOff : (CSᶜ : Set S) → ↥(S \ C) :=
    fun t => ⟨t.val.val, t.val.property, t.property⟩
  have htoOff : Measurable toOff :=
    (measurable_subtype_coe.comp measurable_subtype_coe).subtype_mk
  have hσsubOff : Measurable (fun t : (CSᶜ : Set S) => σ t.val.val) :=
    hσoff.comp htoOff
  have hσmeas : Measurable (fun t : S => σ t.val) :=
    measurable_of_measurable_on_compl_finite CS hCSfinite hσsubOff
  have hσUiInt : ∀ i : Fin n, IntegrableOn σ (U i) volume := by
    intro i
    by_cases hi : cut i.castSucc < cut i.succ
    · exact ((hqint i hi).mono_set (hopenSub i)).congr_fun
        (fun t ht => (σrep i ht).symm) measurableSet_Ioo
    · have he : U i = ∅ := Ioo_eq_empty_of_le (le_of_not_gt hi)
      exact he.symm ▸ integrableOn_empty
  have hσUnionInt : IntegrableOn σ (⋃ i : Fin n, U i) volume :=
    integrableOn_finite_iUnion.2 hσUiInt
  have hσCutsInt : IntegrableOn σ C volume := .of_measure_zero (hfinite.measure_zero volume)
  have hσint : IntegrableOn σ S volume := hcover.symm ▸ hσCutsInt.union hσUnionInt
  have hσnonneg : ∀ t ∈ S, 0 ≤ σ t := by
    intro t ht
    rw [hcover] at ht
    rcases ht with hc | hu
    · exact cutNonneg t hc
    · rcases mem_iUnion.1 hu with ⟨i, hi⟩
      rw [σrep i hi]
      exact norm_nonneg _
  -- Link J4.06 to this actual finite cover, not an assumed global helper.
  have hExtensionMaterial : ∀ δ : ℝ → M, EqOn δ γ S →
      let vδ : ℝ → ℝ := fun t => ‖mfderiv 𝓘(ℝ, ℝ) I δ t (1 : ℝ)‖
      EqOn vδ σ (S \ C) ∧
      Measurable (fun t : S => vδ t.val) ∧ IntegrableOn vδ S volume ∧
      (∫ t in S, vδ t) = (∫ t in S, σ t) ∧
      (∫⁻ t in S, ENNReal.ofReal (vδ t)) =
        (∫⁻ t in S, ENNReal.ofReal (σ t)) := by
    intro δ hextension
    let vδ : ℝ → ℝ := fun t => ‖mfderiv 𝓘(ℝ, ℝ) I δ t (1 : ℝ)‖
    have heq : EqOn vδ σ (S \ C) := by
      intro t ht
      rcases mem_iUnion.1 (hcoverOff ht) with ⟨i, hi⟩
      have hbase : δ t = γ t := hextension ht.1
      have hlocal : δ =ᶠ[𝓝 t] γ :=
        Filter.eventuallyEq_of_mem (Icc_mem_nhds hi.1 hi.2)
          (fun x hx => hextension (hpieceSub i hx))
      have hδdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I δ t :=
        hlocal.mdifferentiableAt_iff.2 (hdiff i t hi)
      have hraw := hlocal.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I)
      have hvec := congrArg (fun L => L (1 : ℝ)) hraw
      have htransport : cast (congrArg (fun x : M => TangentSpace I x) hbase)
          (mfderiv 𝓘(ℝ, ℝ) I δ t (1 : ℝ)) = V t := by
        have hcastEq : congrArg (fun x : M => TangentSpace I x) hbase =
            (rfl : E = E) := Subsingleton.elim _ _
        rw [hcastEq]
        exact hvec
      have htotal : Bundle.TotalSpace.mk' E (δ t)
          (mfderiv 𝓘(ℝ, ℝ) I δ t (1 : ℝ)) =
          Bundle.TotalSpace.mk' E (γ t) (V t) :=
        (Bundle.TotalSpace.mk_cast (F := E) hbase
          (mfderiv 𝓘(ℝ, ℝ) I δ t (1 : ℝ))).symm.trans
            (congrArg (Bundle.TotalSpace.mk' E (γ t)) htransport)
      have hn : vδ t = v t :=
        congrArg (fun z : TangentBundle I M => ‖z.2‖) htotal
      have hen : ‖mfderiv 𝓘(ℝ, ℝ) I δ t (1 : ℝ)‖ₑ = ‖V t‖ₑ :=
        congrArg (fun z : TangentBundle I M => ‖z.2‖ₑ) htotal
      exact hn.trans ((hspeed i t hi).symm.trans (σrep i hi).symm)
    have hae : vδ =ᵐ[volume.restrict S] σ := by
      filter_upwards [hfinite.countable.ae_notMem (volume.restrict S),
        ae_restrict_mem measurableSet_Icc] with t hnot ht
      exact heq ⟨ht, hnot⟩
    have hexcept : {t : S | σ t.val ≠ vδ t.val} ⊆ CS := by
      intro t ht
      by_contra hn
      exact ht (heq ⟨t.property, hn⟩).symm
    have hm : Measurable (fun t : S => vδ t.val) :=
      hσmeas.measurable_of_countable_ne (hCSfinite.subset hexcept).countable
    exact ⟨heq, hm, hσint.congr_fun_ae hae.symm, integral_congr_ae hae,
      lintegral_congr_ae (hae.mono (fun _ h => congrArg ENNReal.ofReal h))⟩

  -- Eighth pending j.5 input supplied by the actual finite cover/interior velocity.
  have hwholeAE : σ =ᵐ[volume.restrict S] v := by
    filter_upwards [hfinite.countable.ae_notMem (volume.restrict S),
      ae_restrict_mem measurableSet_Icc] with t hnot ht
    rcases mem_iUnion.1 (hcoverOff ⟨ht, hnot⟩) with ⟨i, hi⟩
    exact (σrep i hi).trans (hspeed i t hi)
  have hqintStrict : ∀ i : Fin n, cut i.castSucc < cut i.succ →
      IntegrableOn (q i) (P i) volume := hqint
  -- Literal j.5 application body, now no pending-input lambda.
  -- J5.01: piece integrability comes BEFORE extended conversion, repeats separate.
  have hqint (i : Fin n) : IntegrableOn (q i) (P i) volume := by
    rcases lt_or_eq_of_le (hpieceLe i) with hi | hi
    · exact hqintStrict i hi
    · apply IntegrableOn.of_measure_zero
      simp only [P, hi, Icc_self]
      exact measure_singleton _
  have hqnonneg (i : Fin n) (t : ℝ) : 0 ≤ q i t := norm_nonneg (W i t)
  have hPieceConversion (i : Fin n) :
      ENNReal.ofReal (∫ t in P i, q i t) =
        ∫⁻ t in P i, ENNReal.ofReal (q i t) :=
    ofReal_integral_eq_lintegral_ofReal (hqint i)
      (Eventually.of_forall (hqnonneg i))
  have hPieceEnorm (i : Fin n) :
      (∫⁻ t in P i, ENNReal.ofReal (q i t)) = ∫⁻ t in P i, ‖W i t‖ₑ := by
    apply lintegral_congr_ae
    exact Eventually.of_forall (fun t => hEnorm (γ t) (W i t))
  have hPieceFinite (i : Fin n) : (∫⁻ t in P i, ‖W i t‖ₑ) < (⊤ : ℝ≥0∞) := by
    rw [← hPieceEnorm i, ← hPieceConversion i]
    exact ENNReal.ofReal_lt_top
  have hWholeNonnegAE : 0 ≤ᵐ[volume.restrict S] σ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hσnonneg t ht
  have hWholeConversion :
      ENNReal.ofReal (∫ t in S, σ t) = ∫⁻ t in S, ENNReal.ofReal (σ t) :=
    ofReal_integral_eq_lintegral_ofReal hσint hWholeNonnegAE
  have hWholeFinite : (∫⁻ t in S, ENNReal.ofReal (σ t)) < (⊤ : ℝ≥0∞) := by
    rw [← hWholeConversion]
    exact ENNReal.ofReal_lt_top

  -- J5.02: endpoints may differ; equality on OPEN piece yields restricted AE.
  have hPieceAE (i : Fin n) : σ =ᵐ[volume.restrict (P i)] q i := by
    change σ =ᵐ[volume.restrict (Icc (cut i.castSucc) (cut i.succ))] q i
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact σrep i ht
  have hPieceReal (i : Fin n) :
      (∫ t in P i, σ t) = ∫ t in P i, q i t :=
    integral_congr_ae (hPieceAE i)
  have hWholePieceInt (i : Fin n) : IntegrableOn σ (P i) volume :=
    hσint.mono_set (hpieceSub i)
  have hWholePieceInterval (i : Fin n) :
      IntervalIntegrable σ volume (cut i.castSucc) (cut i.succ) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (hpieceLe i)).mpr
      (hWholePieceInt i)
  have hPieceConvention (f : ℝ → ℝ) (i : Fin n) :
      (∫ t in cut i.castSucc..cut i.succ, f t) = ∫ t in P i, f t :=
    (intervalIntegral.integral_of_le (hpieceLe i)).trans
      MeasureTheory.integral_Icc_eq_integral_Ioc.symm
  have hPieceIntervalEq (i : Fin n) :
      (∫ t in cut i.castSucc..cut i.succ, σ t) =
        ∫ t in cut i.castSucc..cut i.succ, q i t :=
    (hPieceConvention σ i).trans ((hPieceReal i).trans (hPieceConvention (q i) i).symm)

  -- J5.03: literal Fin/Nat correspondence, no replacement subdivision.
  have hN0 : cN 0 = cut 0 := by simp [cN]
  have hNlast : cN n = cut (Fin.last n) := by
    simp only [cN, dif_pos (Nat.lt_succ_self n)]
    rfl
  have hNleft (i : Fin n) : cN i.val = cut i.castSucc := by
    simp only [cN, dif_pos (Nat.lt_succ_of_lt i.isLt)]
    rfl
  have hNright (i : Fin n) : cN (i.val+1) = cut i.succ := by
    simp only [cN, dif_pos (Nat.succ_lt_succ i.isLt)]
    rfl
  have hNint (k : ℕ) (hk : k < n) :
      IntervalIntegrable σ volume (cN k) (cN (k+1)) := by
    simpa only [hNleft ⟨k, hk⟩, hNright ⟨k, hk⟩] using
      hWholePieceInterval ⟨k, hk⟩
  have hNatSum :
      (∑ k ∈ Finset.range n, ∫ t in cN k..cN (k+1), σ t) =
        ∫ t in cN 0..cN n, σ t :=
    intervalIntegral.sum_integral_adjacent_intervals hNint
  have hFinRange :
      (∑ i : Fin n, ∫ t in cN i.val..cN (i.val+1), σ t) =
        ∑ k ∈ Finset.range n, ∫ t in cN k..cN (k+1), σ t :=
    Fin.sum_univ_eq_sum_range (fun k => ∫ t in cN k..cN (k+1), σ t) n
  have hFinSum :
      (∑ i : Fin n, ∫ t in cut i.castSucc..cut i.succ, σ t) =
        ∫ t in a..b, σ t := by
    simpa only [hNleft, hNright, hN0, hNlast, hγ.2.1, hγ.2.2.1]
      using hFinRange.trans hNatSum
  have hSumPieceEq :
      (∑ i : Fin n, ∫ t in cut i.castSucc..cut i.succ, σ t) = L := by
    exact Finset.sum_congr rfl (fun i _ => hPieceIntervalEq i)

  -- J5.04: length definition is the piece sum; whole/extended formulas are outputs.
  have hWholeReal : (∫ t in a..b, σ t) = L := hFinSum.symm.trans hSumPieceEq
  have hWholeConvention : (∫ t in a..b, σ t) = ∫ t in S, σ t :=
    (intervalIntegral.integral_of_le hab).trans
      MeasureTheory.integral_Icc_eq_integral_Ioc.symm
  have hWholeSetReal : (∫ t in S, σ t) = L :=
    hWholeConvention.symm.trans hWholeReal
  have hExtendedLength :
      (∫⁻ t in S, ENNReal.ofReal (σ t)) = ENNReal.ofReal L := by
    rw [← hWholeConversion, hWholeSetReal]
  have hPieceIntegralNonneg (i : Fin n) :
      0 ≤ ∫ t in cut i.castSucc..cut i.succ, q i t :=
    intervalIntegral.integral_nonneg (hpieceLe i) (fun t _ => hqnonneg i t)
  have hLengthNonneg : 0 ≤ L :=
    Finset.sum_nonneg (fun i _ => hPieceIntegralNonneg i)
  have hOfRealSum :
      ENNReal.ofReal L =
        ∑ i : Fin n, ENNReal.ofReal (∫ t in cut i.castSucc..cut i.succ, q i t) :=
    ENNReal.ofReal_sum_of_nonneg (fun i _ => hPieceIntegralNonneg i)
  have hExtendedPieceSum :
      ENNReal.ofReal L = ∑ i : Fin n, ∫⁻ t in P i, ‖W i t‖ₑ := by
    refine hOfRealSum.trans (Finset.sum_congr rfl (fun i _ => ?_))
    rw [hPieceConvention (q i) i]
    exact (hPieceConversion i).trans (hPieceEnorm i)
  have hFiniteLength : ENNReal.ofReal L < (⊤ : ℝ≥0∞) := ENNReal.ofReal_lt_top

  -- J5.05: actual registered enorm/pathELength, not a replacement real definition.
  have hActualWholeIntegrand :
      (fun t => ENNReal.ofReal (σ t)) =ᵐ[volume.restrict S]
        (fun t => ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ) := by
    filter_upwards [hwholeAE] with t ht
    exact (congrArg ENNReal.ofReal ht).trans
      (hEnorm (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))
  have hPathLength : Manifold.pathELength I γ a b = ENNReal.ofReal L :=
    (Manifold.pathELength_eq_lintegral_mfderiv_Icc).trans
      ((lintegral_congr_ae hActualWholeIntegrand).symm.trans hExtendedLength)
  have hPathFinite : Manifold.pathELength I γ a b < (⊤ : ℝ≥0∞) := by
    rw [hPathLength]
    exact hFiniteLength
  have hPiecePath (i : Fin n) :
      Manifold.pathELength I γ (cut i.castSucc) (cut i.succ) =
        ∫⁻ t in P i, ‖W i t‖ₑ :=
    Manifold.pathELength_eq_lintegral_mfderivWithin_Icc

  -- Repeated piece uses no strict-piece derivative uniqueness or C1 hypothesis.
  have hRepeated (i : Fin n) (hi : cut i.castSucc = cut i.succ) :
      (∫ t in cut i.castSucc..cut i.succ, q i t) = 0 ∧
        Manifold.pathELength I γ (cut i.castSucc) (cut i.succ) = 0 := by
    rw [hi]
    exact ⟨intervalIntegral.integral_same, Manifold.pathELength_self⟩
  have hDegenerateLength (habEq : a = b) : L = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hc (j : Fin (n+1)) : cut j = a := by
      apply le_antisymm
      · have hj := hγ.1 (Fin.le_last j)
        simpa only [hγ.2.2.1, ← habEq] using hj
      · have hj := hγ.1 (Fin.zero_le j)
        simpa only [hγ.2.1] using hj
    rw [hc i.castSucc, hc i.succ]
    exact intervalIntegral.integral_same

  exact ⟨hσmeas, hσint, hσnonneg, hwholeAE, hWholeReal, hWholeSetReal, hExtendedLength⟩

/-- j.5: ordinary intrinsic speed and all piece integrals have the same finite real/extended interpretation. -/
theorem IsPiecewiseC1On.speed_length
    [FiniteDimensional ℝ E]
    (G : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M => TangentSpace I x))
    {γ : ℝ → M} {a b : ℝ} {n : ℕ} {cut : Fin (n + 1) → ℝ}
    (hγ : IsPiecewiseC1On I γ a b n cut) :
    letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨G.toRiemannianMetric⟩
    let P : Fin n → Set ℝ := fun i => Icc (cut i.castSucc) (cut i.succ)
    let W : (i : Fin n) → (t : ℝ) → TangentSpace I (γ t) :=
      fun i t => mfderivWithin 𝓘(ℝ, ℝ) I γ (P i) t (1 : ℝ)
    let q : Fin n → ℝ → ℝ := fun i t => ‖W i t‖
    let v : ℝ → ℝ := fun t => ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖
    (∀ i : Fin n, IntegrableOn (q i) (P i) volume) ∧
    (∀ i : Fin n, IntervalIntegrable (q i) volume (cut i.castSucc) (cut i.succ)) ∧
    Measurable (fun t : Icc a b => v t.val) ∧
    IntegrableOn v (Icc a b) volume ∧
    (∫ t in a..b, v t) = piecewiseC1Length G γ cut ∧
    (∫ t in Icc a b, v t) = piecewiseC1Length G γ cut ∧
    0 ≤ piecewiseC1Length G γ cut ∧
    (∀ i : Fin n,
      ENNReal.ofReal (∫ t in cut i.castSucc..cut i.succ, q i t) =
        ∫⁻ t in P i, ‖W i t‖ₑ) ∧
    (∀ i : Fin n, (∫⁻ t in P i, ‖W i t‖ₑ) < (⊤ : ℝ≥0∞)) ∧
    ENNReal.ofReal (piecewiseC1Length G γ cut) =
      (∑ i : Fin n, ∫⁻ t in P i, ‖W i t‖ₑ) ∧
    (∫⁻ t in Icc a b, ENNReal.ofReal (v t)) =
      ENNReal.ofReal (piecewiseC1Length G γ cut) ∧
    pathELength I γ a b = ENNReal.ofReal (piecewiseC1Length G γ cut) ∧
    pathELength I γ a b < (⊤ : ℝ≥0∞) := by
  letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨G.toRiemannianMetric⟩
  let P : Fin n → Set ℝ := fun i => Icc (cut i.castSucc) (cut i.succ)
  let W : (i : Fin n) → (t : ℝ) → TangentSpace I (γ t) :=
    fun i t => mfderivWithin 𝓘(ℝ, ℝ) I γ (P i) t (1 : ℝ)
  let q : Fin n → ℝ → ℝ := fun i t => ‖W i t‖
  let v : ℝ → ℝ := fun t => ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖
  have hrep : ∀ i : Fin n, EqOn v (q i) (Ioo (cut i.castSucc) (cut i.succ)) := by
    intro i t ht
    exact (congrArg (fun L => ‖L (1 : ℝ)‖)
      (mfderivWithin_of_mem_nhds (I := 𝓘(ℝ, ℝ)) (I' := I)
        (f := γ) (Icc_mem_nhds ht.1 ht.2))).symm
  have hcut : ∀ t ∈ range cut, 0 ≤ v t := fun t _ => norm_nonneg _
  rcases hγ.speedRepresentative_length G v hrep hcut with
    ⟨hm, hint, hnonneg, hae, hreal, hset, hext⟩
  have hle (i : Fin n) : cut i.castSucc ≤ cut i.succ :=
    hγ.1 (show i.castSucc ≤ i.succ by change i.val ≤ i.val+1; omega)
  have hqint (i : Fin n) : IntegrableOn (q i) (P i) volume := by
    rcases lt_or_eq_of_le (hle i) with hi | hi
    · exact (continuousOn_pieceSpeed G γ hi (hγ.2.2.2.2 i hi)).integrableOn_Icc
    · apply IntegrableOn.of_measure_zero
      simp only [P, hi, Icc_self]
      exact measure_singleton _
  have hinterval (i : Fin n) : IntervalIntegrable (q i) volume (cut i.castSucc) (cut i.succ) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (hle i)).mpr (hqint i)
  have hconv (i : Fin n) :
      (∫ t in cut i.castSucc..cut i.succ, q i t) = ∫ t in P i, q i t :=
    (intervalIntegral.integral_of_le (hle i)).trans MeasureTheory.integral_Icc_eq_integral_Ioc.symm
  have hpiece (i : Fin n) :
      ENNReal.ofReal (∫ t in cut i.castSucc..cut i.succ, q i t) =
        ∫⁻ t in P i, ‖W i t‖ₑ := by
    rw [hconv i]
    exact (ofReal_integral_eq_lintegral_ofReal (hqint i)
      (Eventually.of_forall (fun t => norm_nonneg (W i t)))).trans
      (lintegral_congr_ae (Eventually.of_forall (fun t => ofReal_norm (W i t))))
  have hfinite (i : Fin n) : (∫⁻ t in P i, ‖W i t‖ₑ) < ⊤ := by
    rw [← hpiece i]
    exact ENNReal.ofReal_lt_top
  have hnonnegPiece (i : Fin n) : 0 ≤ ∫ t in cut i.castSucc..cut i.succ, q i t :=
    intervalIntegral.integral_nonneg (hle i) (fun t _ => norm_nonneg (W i t))
  have hlength : 0 ≤ piecewiseC1Length G γ cut :=
    Finset.sum_nonneg (fun i _ => hnonnegPiece i)
  have hsum : ENNReal.ofReal (piecewiseC1Length G γ cut) =
      ∑ i : Fin n, ∫⁻ t in P i, ‖W i t‖ₑ :=
    (ENNReal.ofReal_sum_of_nonneg (fun i _ => hnonnegPiece i)).trans
      (Finset.sum_congr rfl (fun i _ => hpiece i))
  have hnorm :
      (fun t => ENNReal.ofReal (v t)) =ᵐ[volume.restrict (Icc a b)]
        (fun t => ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ) :=
    Eventually.of_forall (fun t => ofReal_norm _)
  have hpath : pathELength I γ a b = ENNReal.ofReal (piecewiseC1Length G γ cut) :=
    pathELength_eq_lintegral_mfderiv_Icc.trans ((lintegral_congr_ae hnorm).symm.trans hext)
  exact ⟨hqint, hinterval, hm, hint, hreal, hset, hlength, hpiece, hfinite,
    hsum, hext, hpath, by rw [hpath]; exact ENNReal.ofReal_lt_top⟩

/-- j.4: arbitrary outside extensions preserve off-cut actual velocities and both speed integrals. -/
theorem IsPiecewiseC1On.speed_extension
    [FiniteDimensional ℝ E]
    (G : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M => TangentSpace I x))
    {γ : ℝ → M} {a b : ℝ} {n : ℕ} {cut : Fin (n + 1) → ℝ}
    (hγ : IsPiecewiseC1On I γ a b n cut)
    (δ : ℝ → M) (hextension : EqOn δ γ (Icc a b)) :
    letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨G.toRiemannianMetric⟩
    let vγ : ℝ → ℝ := fun t => ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖
    let vδ : ℝ → ℝ := fun t => ‖mfderiv 𝓘(ℝ, ℝ) I δ t (1 : ℝ)‖
    (∀ t ∈ Icc a b \ range cut,
      Bundle.TotalSpace.mk' E (δ t) (mfderiv 𝓘(ℝ, ℝ) I δ t (1 : ℝ)) =
        Bundle.TotalSpace.mk' E (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))) ∧
    EqOn vδ vγ (Icc a b \ range cut) ∧
    Measurable (fun t : Icc a b => vδ t.val) ∧
    IntegrableOn vδ (Icc a b) volume ∧
    (∫ t in Icc a b, vδ t) = (∫ t in Icc a b, vγ t) ∧
    (∫⁻ t in Icc a b, ENNReal.ofReal (vδ t)) =
      (∫⁻ t in Icc a b, ENNReal.ofReal (vγ t)) := by
  -- Same topology and metric registration in the shared piece/whole context.
  let tE : (x : M) → TopologicalSpace (TangentSpace I x) := fun _ => inferInstance
  letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨G.toRiemannianMetric⟩
  have hTopology (x : M) :
      (inferInstance : NormedAddCommGroup (TangentSpace I x)).toMetricSpace.toUniformSpace.toTopologicalSpace =
        tE x := rfl
  have hInner (x : M) (v w : TangentSpace I x) : inner ℝ v w = G.inner x v w := rfl
  have hEnorm (x : M) (v : TangentSpace I x) : ENNReal.ofReal ‖v‖ = ‖v‖ₑ := ofReal_norm v
  let S : Set ℝ := Icc a b
  let C : Set ℝ := range cut
  let P : Fin n → Set ℝ := fun i => Icc (cut i.castSucc) (cut i.succ)
  let U : Fin n → Set ℝ := fun i => Ioo (cut i.castSucc) (cut i.succ)
  let V : (t : ℝ) → TangentSpace I (γ t) :=
    fun t => mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)
  let W : (i : Fin n) → (t : ℝ) → TangentSpace I (γ t) :=
    fun i t => mfderivWithin 𝓘(ℝ, ℝ) I γ (P i) t (1 : ℝ)
  let q : Fin n → ℝ → ℝ := fun i t => ‖W i t‖
  let v : ℝ → ℝ := fun t => ‖V t‖
  have hfinite : C.Finite := Set.finite_range cut
  have hcuts : C ⊆ S := by
    rintro t ⟨k, rfl⟩
    exact ⟨hγ.2.1 ▸ hγ.1 (show (0 : Fin (n + 1)) ≤ k by change 0 ≤ k.val; omega),
      hγ.2.2.1 ▸ hγ.1 (show k ≤ Fin.last n by change k.val ≤ n; omega)⟩
  have hab : a ≤ b := by
    simpa only [hγ.2.1, hγ.2.2.1] using
      hγ.1 (show (0 : Fin (n + 1)) ≤ Fin.last n by change 0 ≤ n; omega)
  have hzero : n = 0 → a = b := by
    intro hn
    have hidx : (0 : Fin (n + 1)) = Fin.last n := by apply Fin.ext; simp [hn]
    exact hγ.2.1.symm.trans ((congrArg cut hidx).trans hγ.2.2.1)
  have hopenSub : ∀ i : Fin n, U i ⊆ P i := fun _ _ ht => ⟨ht.1.le, ht.2.le⟩
  have hpieceSub : ∀ i : Fin n, P i ⊆ S := by
    intro i t ht
    exact ⟨(hcuts ⟨i.castSucc, rfl⟩).1.trans ht.1,
      ht.2.trans (hcuts ⟨i.succ, rfl⟩).2⟩
  have hrepeated : ∀ i : Fin n, cut i.castSucc = cut i.succ → U i = ∅ := by
    intro i hi
    simp [U, hi]
  let cN : ℕ → ℝ := fun k =>
    if hk : k < n + 1 then cut ⟨k, hk⟩ else cut (Fin.last n)
  have hN0 : cN 0 = cut 0 := by simp [cN]
  have hNlast : cN n = cut (Fin.last n) := by simp [cN, Fin.last]
  have hNleft : ∀ i : Fin n, cN i.val = cut i.castSucc := by
    intro i
    simp only [cN, dif_pos (show i.val < n + 1 by omega)]
    rfl
  have hNright : ∀ i : Fin n, cN (i.val + 1) = cut i.succ := by
    intro i
    simp only [cN, dif_pos (show i.val + 1 < n + 1 by omega)]
    rfl
  have hNcover : Ico (cN 0) (cN n) ⊆
      ⋃ k ∈ Finset.range n, Ico (cN k) (cN (k + 1)) :=
    Ico_subset_biUnion_Ico n cN
  have hindex : (⋃ k ∈ Finset.range n, Ico (cN k) (cN (k + 1))) =
      ⋃ i : Fin n, Ico (cut i.castSucc) (cut i.succ) := by
    ext t
    constructor
    · intro ht
      rcases mem_iUnion.1 ht with ⟨k, hk⟩
      rcases mem_iUnion.1 hk with ⟨hk, ht⟩
      let i : Fin n := ⟨k, Finset.mem_range.1 hk⟩
      exact mem_iUnion.2 ⟨i, by simpa only [← hNleft i, ← hNright i] using ht⟩
    · intro ht
      rcases mem_iUnion.1 ht with ⟨i, ht⟩
      exact mem_iUnion.2 ⟨i.val, mem_iUnion.2 ⟨Finset.mem_range.2 i.isLt,
        by simpa only [hNleft i, hNright i] using ht⟩⟩
  have hcoverOff : S \ C ⊆ ⋃ i : Fin n, U i := by
    intro t ht
    have htb : t < b := lt_of_le_of_ne ht.1.2 (by
      intro h
      exact ht.2 ⟨Fin.last n, hγ.2.2.1.trans h.symm⟩)
    have hmem : t ∈ Ico (cN 0) (cN n) := by
      simpa only [hN0, hNlast, hγ.2.1, hγ.2.2.1] using ⟨ht.1.1, htb⟩
    have hm := hNcover hmem
    rw [hindex] at hm
    rcases mem_iUnion.1 hm with ⟨i, hi⟩
    exact mem_iUnion.2 ⟨i, lt_of_le_of_ne hi.1 (by
      intro heq
      exact ht.2 ⟨i.castSucc, heq⟩), hi.2⟩
  have hcover : S = C ∪ ⋃ i : Fin n, U i := by
    ext t
    constructor
    · intro ht
      by_cases hc : t ∈ C
      · exact Or.inl hc
      · exact Or.inr (hcoverOff ⟨ht, hc⟩)
    · rintro (hc | hu)
      · exact hcuts hc
      · rcases mem_iUnion.1 hu with ⟨i, hi⟩
        exact hpieceSub i (hopenSub i hi)
  have hdisjoint : Pairwise (fun i j : Fin n => Disjoint (U i) (U j)) := by
    intro i j hij
    apply Set.disjoint_left.2
    intro t hi hj
    rcases lt_or_gt_of_ne hij with hij | hji
    · have h := hγ.1 (show i.succ ≤ j.castSucc by
        change i.val + 1 ≤ j.val
        change i.val < j.val at hij
        omega)
      exact (not_lt_of_ge h) (hj.1.trans hi.2)
    · have h := hγ.1 (show j.succ ≤ i.castSucc by
        change j.val + 1 ≤ i.val
        change j.val < i.val at hji
        omega)
      exact (not_lt_of_ge h) (hi.1.trans hj.2)
  have hdiff : ∀ (i : Fin n) (t : ℝ), t ∈ U i →
      MDifferentiableAt 𝓘(ℝ, ℝ) I γ t := by
    intro i t ht
    exact ((hγ.2.2.2.2 i (ht.1.trans ht.2)).mdifferentiableOn
      (by simp) t ⟨ht.1.le, ht.2.le⟩).mdifferentiableAt
        (Icc_mem_nhds ht.1 ht.2)
  have hvelocity : ∀ (i : Fin n) (t : ℝ), t ∈ U i → W i t = V t := by
    intro i t ht
    exact congrArg (fun L => L (1 : ℝ))
      (mfderivWithin_of_mem_nhds (I := 𝓘(ℝ, ℝ)) (I' := I)
        (f := γ) (Icc_mem_nhds ht.1 ht.2))
  have hspeed : ∀ (i : Fin n) (t : ℝ), t ∈ U i → q i t = v t := by
    intro i t ht
    exact congrArg (fun w : TangentSpace I (γ t) => ‖w‖) (hvelocity i t ht)

  have hp := hγ.speed_length G
  have hm : Measurable (fun t : S => v t.val) := hp.2.2.1
  have hint : IntegrableOn v S volume := hp.2.2.2.1
  let vδ : ℝ → ℝ := fun t => ‖mfderiv 𝓘(ℝ, ℝ) I δ t (1 : ℝ)‖
  have htotal (t : ℝ) (ht : t ∈ S \ C) :
      Bundle.TotalSpace.mk' E (δ t) (mfderiv 𝓘(ℝ, ℝ) I δ t (1 : ℝ)) =
        Bundle.TotalSpace.mk' E (γ t) (V t) := by
    rcases mem_iUnion.1 (hcoverOff ht) with ⟨i, hi⟩
    have hbase : δ t = γ t := hextension ht.1
    have hlocal : δ =ᶠ[𝓝 t] γ :=
      Filter.eventuallyEq_of_mem (Icc_mem_nhds hi.1 hi.2)
        (fun x hx => hextension (hpieceSub i hx))
    have hraw := hlocal.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I)
    have hvec := congrArg (fun L => L (1 : ℝ)) hraw
    have htransport : cast (congrArg (fun x : M => TangentSpace I x) hbase)
        (mfderiv 𝓘(ℝ, ℝ) I δ t (1 : ℝ)) = V t := by
      have hcastEq : congrArg (fun x : M => TangentSpace I x) hbase =
          (rfl : E = E) := Subsingleton.elim _ _
      rw [hcastEq]
      exact hvec
    exact (Bundle.TotalSpace.mk_cast (F := E) hbase
      (mfderiv 𝓘(ℝ, ℝ) I δ t (1 : ℝ))).symm.trans
        (congrArg (Bundle.TotalSpace.mk' E (γ t)) htransport)
  have heq : EqOn vδ v (S \ C) := fun t ht =>
    congrArg (fun z : TangentBundle I M => ‖z.2‖) (htotal t ht)
  have hae : vδ =ᵐ[volume.restrict S] v := by
    filter_upwards [hfinite.countable.ae_notMem (volume.restrict S),
      ae_restrict_mem measurableSet_Icc] with t hnot ht
    exact heq ⟨ht,hnot⟩
  let CS : Set S := {t | t.val ∈ C}
  have hCSfinite : CS.Finite := hfinite.preimage Subtype.val_injective.injOn
  have hExcept : {t : S | v t.val ≠ vδ t.val} ⊆ CS := by
    intro t ht
    by_contra hn
    exact ht (heq ⟨t.property,hn⟩).symm
  have hmδ : Measurable (fun t : S => vδ t.val) :=
    hm.measurable_of_countable_ne (hCSfinite.subset hExcept).countable
  exact ⟨htotal, heq, hmδ, hint.congr_fun_ae hae.symm, integral_congr_ae hae,
    lintegral_congr_ae (hae.mono (fun _ h => congrArg ENNReal.ofReal h))⟩

/-- j.5: equal outer endpoints give zero length, even with repeated positive-count cuts. -/
theorem IsPiecewiseC1On.piecewiseC1Length_eq_zero
    [FiniteDimensional ℝ E]
    (G : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M => TangentSpace I x))
    {γ : ℝ → M} {a b : ℝ} {n : ℕ} {cut : Fin (n + 1) → ℝ}
    (hγ : IsPiecewiseC1On I γ a b n cut) (hab : a = b) :
    piecewiseC1Length G γ cut = 0 := by
  letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨G.toRiemannianMetric⟩
  unfold piecewiseC1Length
  apply Finset.sum_eq_zero
  intro i _
  have hc (j : Fin (n+1)) : cut j = a := by
    apply le_antisymm
    · have hj := hγ.1 (Fin.le_last j)
      simpa only [hγ.2.2.1, ← hab] using hj
    · have hj := hγ.1 (Fin.zero_le j)
      simpa only [hγ.2.1] using hj
  rw [hc i.castSucc, hc i.succ]
  exact intervalIntegral.integral_same

end LengthUpstream

/-- j.6.E: inserting weak cuts derives the new piecewise-C1 witness from the old witness. -/
theorem IsPiecewiseC1On.refine
    {γ : ℝ → M} {a b : ℝ} {n m : ℕ}
    {c : Fin (n+1) → ℝ} (hγ : IsPiecewiseC1On I γ a b n c)
    (r : Fin (m+1) → ℝ) (hr : Monotone r)
    (hr0 : r 0 = a) (hrm : r (Fin.last m) = b)
    (hvalues : range c ⊆ range r) :
    IsPiecewiseC1On I γ a b m r := by
  refine ⟨hr, hr0, hrm, hγ.2.2.2.1, ?_⟩
  intro j hj
  obtain ⟨i, hi, hsub⟩ :=
    Fin.exists_strict_piece_containing_of_range_subset c r a b
      hγ.1 hr hγ.2.1 hγ.2.2.1 hr0 hrm hvalues j hj
  exact (hγ.2.2.2.2 i hi).mono hsub

local instance lengthRefinementT2 [IsManifold I ∞ M] (x : M) : T2Space (TangentSpace I x) :=
  FiberBundle.t2Space E (fun x : M => TangentSpace I x) x

/-- j.6.F: split each old integral using its same speed, then identify refined integrals almost everywhere. -/
theorem IsPiecewiseC1On.pieceIntegral_eq_sum_rankBlock
    [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    (G : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M => TangentSpace I x))
    {γ : ℝ → M} {a b : ℝ} {n m : ℕ}
    {c : Fin (n+1) → ℝ} (hγ : IsPiecewiseC1On I γ a b n c)
    (r : Fin (m+1) → ℝ) (hr : StrictMono r)
    (hr0 : r 0 = a) (hrm : r (Fin.last m) = b)
    (ρ : Fin (n+1) → Fin (m+1)) (hρ : Monotone ρ)
    (hρ0 : ρ 0 = 0) (hρn : ρ (Fin.last n) = Fin.last m)
    (hvalue : ∀ i, r (ρ i) = c i) (i : Fin n) :
    letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨G.toRiemannianMetric⟩
    (∫ t in c i.castSucc..c i.succ,
      ‖mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc (c i.castSucc) (c i.succ)) t (1 : ℝ)‖) =
    ∑ j ∈ Fin.rankBlock ρ i, ∫ t in r j.castSucc..r j.succ,
      ‖mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc (r j.castSucc) (r j.succ)) t (1 : ℝ)‖ := by
  classical
  letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨G.toRiemannianMetric⟩
  have hvalues : range c ⊆ range r := by
    rintro x ⟨i, rfl⟩
    exact ⟨ρ i, hvalue i⟩
  have hNew : IsPiecewiseC1On I γ a b m r :=
    hγ.refine r hr.monotone hr0 hrm hvalues
  let P : Fin n → Set ℝ := fun i => Icc (c i.castSucc) (c i.succ)
  let R : Fin m → Set ℝ := fun j => Icc (r j.castSucc) (r j.succ)
  let W : (i : Fin n) → (t : ℝ) → TangentSpace I (γ t) :=
    fun i t => mfderivWithin 𝓘(ℝ, ℝ) I γ (P i) t (1 : ℝ)
  let Z : (j : Fin m) → (t : ℝ) → TangentSpace I (γ t) :=
    fun j t => mfderivWithin 𝓘(ℝ, ℝ) I γ (R j) t (1 : ℝ)
  let q : Fin n → ℝ → ℝ := fun i t => ‖W i t‖
  let z : Fin m → ℝ → ℝ := fun j t => ‖Z j t‖
  have hOldPack := hγ.speed_length G
  have hNewPack := hNew.speed_length G
  have hOldInt (i : Fin n) : IntegrableOn (q i) (P i) volume := hOldPack.1 i
  have hSub (i : Fin n) (j : Fin m) (hj : j ∈ Fin.rankBlock ρ i) :
      R j ⊆ P i := by
    simpa only [P, R, hvalue] using
      Fin.rankBlock_interval_subset r hr.monotone ρ i j hj
  have hVelocity (i : Fin n) (j : Fin m) (hj : j ∈ Fin.rankBlock ρ i)
      (t : ℝ) (ht : t ∈ Ioo (r j.castSucc) (r j.succ)) : W i t = Z j t := by
    have hNewNhds : R j ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
    have hOldNhds : P i ∈ 𝓝 t := Filter.mem_of_superset hNewNhds (hSub i j hj)
    exact congrArg (fun L => L (1 : ℝ))
      ((mfderivWithin_of_mem_nhds (I := 𝓘(ℝ, ℝ)) (I' := I)
        (f := γ) hOldNhds).trans
       (mfderivWithin_of_mem_nhds (I := 𝓘(ℝ, ℝ)) (I' := I)
        (f := γ) hNewNhds).symm)
  have hSpeed (i : Fin n) (j : Fin m) (hj : j ∈ Fin.rankBlock ρ i)
      (t : ℝ) (ht : t ∈ Ioo (r j.castSucc) (r j.succ)) :
      q i t = z j t ∧ ‖W i t‖ₑ = ‖Z j t‖ₑ :=
    ⟨congrArg (fun v : TangentSpace I (γ t) => ‖v‖) (hVelocity i j hj t ht),
     congrArg (fun v : TangentSpace I (γ t) => ‖v‖ₑ) (hVelocity i j hj t ht)⟩
  have hAE (i : Fin n) (j : Fin m) (hj : j ∈ Fin.rankBlock ρ i) :
      q i =ᵐ[volume.restrict (R j)] z j := by
    change q i =ᵐ[volume.restrict (Icc (r j.castSucc) (r j.succ))] z j
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (hSpeed i j hj t ht).1
  have hLe (j : Fin m) : r j.castSucc ≤ r j.succ :=
    hr.monotone (by change j.val ≤ j.val+1; omega)
  have hSameInt (i : Fin n) (j : Fin m) (hj : j ∈ Fin.rankBlock ρ i) :
      IntervalIntegrable (q i) volume (r j.castSucc) (r j.succ) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (hLe j)).mpr
      ((hOldInt i).mono_set (hSub i j hj))
  have hConvention (f : ℝ → ℝ) (j : Fin m) :
      (∫ t in r j.castSucc..r j.succ, f t) = ∫ t in R j, f t :=
    (intervalIntegral.integral_of_le (hLe j)).trans
      MeasureTheory.integral_Icc_eq_integral_Ioc.symm
  have hIntegral (i : Fin n) (j : Fin m) (hj : j ∈ Fin.rankBlock ρ i) :
      (∫ t in r j.castSucc..r j.succ, q i t) =
        ∫ t in r j.castSucc..r j.succ, z j t :=
    (hConvention (q i) j).trans
      ((integral_congr_ae (hAE i j hj)).trans (hConvention (z j) j).symm)

  -- The local Fin/Nat list is the ACTUAL B/C list, not an assumed partition.
  have actualF (i : Fin n) :
      (∫ t in c i.castSucc..c i.succ, q i t) =
        ∑ j ∈ Fin.rankBlock ρ i, ∫ t in r j.castSucc..r j.succ, z j t := by
    let s := Fin.rankBlockSize ρ i
    let ℓ : Fin (s+1) → ℝ := Fin.rankBlockCuts r ρ hρ i
    let e : Fin s ≃ {j : Fin m // j ∈ Fin.rankBlock ρ i} := Fin.rankBlockEquiv ρ hρ i
    let cN : ℕ → ℝ := fun k => if hk : k < s+1 then ℓ ⟨k,hk⟩ else ℓ (Fin.last s)
    have hEnds : ℓ 0 = c i.castSucc ∧ ℓ (Fin.last s) = c i.succ := by
      simpa only [ℓ, hvalue] using Fin.rankBlockCuts_endpoints r ρ hρ i
    have hAdjacent (k : Fin s) :
        ℓ k.castSucc = r (e k).val.castSucc ∧ ℓ k.succ = r (e k).val.succ :=
      Fin.rankBlockCuts_adjacent r ρ hρ i k
    have hLocalInt (k : Fin s) :
        IntervalIntegrable (q i) volume (ℓ k.castSucc) (ℓ k.succ) := by
      rw [(hAdjacent k).1, (hAdjacent k).2]
      exact hSameInt i (e k).val (e k).property
    have hN0 : cN 0 = ℓ 0 := by simp [cN]
    have hNlast : cN s = ℓ (Fin.last s) := by
      simp only [cN, dif_pos (Nat.lt_succ_self s)]
      rfl
    have hNleft (k : Fin s) : cN k.val = ℓ k.castSucc := by
      simp only [cN, dif_pos (Nat.lt_succ_of_lt k.isLt)]
      rfl
    have hNright (k : Fin s) : cN (k.val+1) = ℓ k.succ := by
      simp only [cN, dif_pos (Nat.succ_lt_succ k.isLt)]
      rfl
    have hNint (k : ℕ) (hk : k < s) :
        IntervalIntegrable (q i) volume (cN k) (cN (k+1)) := by
      simpa only [hNleft ⟨k,hk⟩, hNright ⟨k,hk⟩] using hLocalInt ⟨k,hk⟩
    have hNatSum :
        (∑ k ∈ Finset.range s, ∫ t in cN k..cN (k+1), q i t) =
          ∫ t in cN 0..cN s, q i t :=
      intervalIntegral.sum_integral_adjacent_intervals hNint
    have hFinRange :
        (∑ k : Fin s, ∫ t in cN k.val..cN (k.val+1), q i t) =
        ∑ k ∈ Finset.range s, ∫ t in cN k..cN (k+1), q i t :=
      Fin.sum_univ_eq_sum_range (fun k => ∫ t in cN k..cN (k+1), q i t) s
    have hSplit :
        (∑ k : Fin s, ∫ t in ℓ k.castSucc..ℓ k.succ, q i t) =
          ∫ t in c i.castSucc..c i.succ, q i t := by
      simpa only [hNleft, hNright, hN0, hNlast, hEnds.1, hEnds.2]
        using hFinRange.trans hNatSum
    have hReplace (k : Fin s) :
        (∫ t in ℓ k.castSucc..ℓ k.succ, q i t) =
          ∫ t in r (e k).val.castSucc..r (e k).val.succ, z (e k).val t := by
      rw [(hAdjacent k).1, (hAdjacent k).2]
      exact hIntegral i (e k).val (e k).property
    let w : Fin m → ℝ := fun j => ∫ t in r j.castSucc..r j.succ, z j t
    have hReindex : (∑ k : Fin s, w (e k).val) = ∑ j ∈ Fin.rankBlock ρ i, w j :=
      (Fintype.sum_equiv e (fun k => w (e k).val) (fun j => w j.val)
        (fun _ => rfl)).trans (Finset.sum_coe_sort (s := Fin.rankBlock ρ i) (f := w))
    -- These three exact terms are F's local recipe, not an assumed equality.
    have hLocalRecipe :
        (∫ t in c i.castSucc..c i.succ, q i t) = ∑ j ∈ Fin.rankBlock ρ i, w j :=
      hSplit.symm.trans ((Finset.sum_congr rfl (fun k _ => hReplace k)).trans hReindex)
    exact hLocalRecipe

  exact actualF i

/-- j.6.G: sum local identities and regroup blocks before converting to finite extended length. -/
theorem IsPiecewiseC1On.length_eq_of_strictRefinement
    [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    (G : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M => TangentSpace I x))
    {γ : ℝ → M} {a b : ℝ} {n m : ℕ}
    {c : Fin (n+1) → ℝ} (hγ : IsPiecewiseC1On I γ a b n c)
    (r : Fin (m+1) → ℝ) (hr : StrictMono r)
    (hr0 : r 0 = a) (hrm : r (Fin.last m) = b)
    (ρ : Fin (n+1) → Fin (m+1)) (hρ : Monotone ρ)
    (hρ0 : ρ 0 = 0) (hρn : ρ (Fin.last n) = Fin.last m)
    (hvalue : ∀ i, r (ρ i) = c i) :
    letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨G.toRiemannianMetric⟩
    let Lc : ℝ≥0∞ := ∑ i : Fin n, ∫⁻ t in Icc (c i.castSucc) (c i.succ),
      ‖mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc (c i.castSucc) (c i.succ)) t (1 : ℝ)‖ₑ
    let Lr : ℝ≥0∞ := ∑ j : Fin m, ∫⁻ t in Icc (r j.castSucc) (r j.succ),
      ‖mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc (r j.castSucc) (r j.succ)) t (1 : ℝ)‖ₑ
    piecewiseC1Length G γ c = piecewiseC1Length G γ r ∧
      Lc = Lr ∧ Lc < ⊤ ∧ Lr < ⊤ := by
  classical
  letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨G.toRiemannianMetric⟩
  have hvalues : range c ⊆ range r := by
    rintro x ⟨i, rfl⟩
    exact ⟨ρ i, hvalue i⟩
  have hNew : IsPiecewiseC1On I γ a b m r :=
    hγ.refine r hr.monotone hr0 hrm hvalues
  let P : Fin n → Set ℝ := fun i => Icc (c i.castSucc) (c i.succ)
  let R : Fin m → Set ℝ := fun j => Icc (r j.castSucc) (r j.succ)
  let W : (i : Fin n) → (t : ℝ) → TangentSpace I (γ t) :=
    fun i t => mfderivWithin 𝓘(ℝ, ℝ) I γ (P i) t (1 : ℝ)
  let Z : (j : Fin m) → (t : ℝ) → TangentSpace I (γ t) :=
    fun j t => mfderivWithin 𝓘(ℝ, ℝ) I γ (R j) t (1 : ℝ)
  let q : Fin n → ℝ → ℝ := fun i t => ‖W i t‖
  let z : Fin m → ℝ → ℝ := fun j t => ‖Z j t‖
  have hOldPack := hγ.speed_length G
  have hNewPack := hNew.speed_length G
  have hOldInt (i : Fin n) : IntegrableOn (q i) (P i) volume := hOldPack.1 i
  -- G uses the proposed F output for ALL pieces and existing D, not U04's whole integral.
  let w : Fin m → ℝ := fun j => ∫ t in r j.castSucc..r j.succ, z j t
  have publicFContract (i : Fin n) :
      (∫ t in c i.castSucc..c i.succ, q i t) = ∑ j ∈ Fin.rankBlock ρ i, w j :=
    hγ.pieceIntegral_eq_sum_rankBlock G r hr hr0 hrm ρ hρ hρ0 hρn hvalue i
  have hSumF :
      (∑ i : Fin n, ∫ t in c i.castSucc..c i.succ, q i t) =
        ∑ i : Fin n, ∑ j ∈ Fin.rankBlock ρ i, w j :=
    Finset.sum_congr rfl (fun i _ => publicFContract i)
  have hD : (∑ j : Fin m, w j) = ∑ i : Fin n, ∑ j ∈ Fin.rankBlock ρ i, w j := by
    simpa only [Fin.rankBlock_cover ρ hρ hρ0 hρn] using
      (Finset.sum_biUnion (f := w) (Fin.rankBlock_disjoint ρ hρ))
  have hReal : piecewiseC1Length G γ c = piecewiseC1Length G γ r := by
    change (∑ i : Fin n, ∫ t in c i.castSucc..c i.succ, q i t) = ∑ j : Fin m, w j
    exact hSumF.trans hD.symm
  -- Consume only the finite-piece conversion fields, never compare whole integrals.
  have hOldConversion :
      ENNReal.ofReal (piecewiseC1Length G γ c) = ∑ i : Fin n, ∫⁻ t in P i, ‖W i t‖ₑ :=
    hOldPack.2.2.2.2.2.2.2.2.2.1
  have hNewConversion :
      ENNReal.ofReal (piecewiseC1Length G γ r) = ∑ j : Fin m, ∫⁻ t in R j, ‖Z j t‖ₑ :=
    hNewPack.2.2.2.2.2.2.2.2.2.1
  have hExtended :
      (∑ i : Fin n, ∫⁻ t in P i, ‖W i t‖ₑ) =
      ∑ j : Fin m, ∫⁻ t in R j, ‖Z j t‖ₑ :=
    hOldConversion.symm.trans ((congrArg ENNReal.ofReal hReal).trans hNewConversion)
  have hFiniteOld : (∑ i : Fin n, ∫⁻ t in P i, ‖W i t‖ₑ) < ⊤ := by
    rw [← hOldConversion]
    exact ENNReal.ofReal_lt_top
  have hFiniteNew : (∑ j : Fin m, ∫⁻ t in R j, ‖Z j t‖ₑ) < ⊤ := by
    rw [← hNewConversion]
    exact ENNReal.ofReal_lt_top
  -- Null old pieces: equality of rank endpoints, empty sum, integral_same.
  have hZero (i : Fin n) (heq : c i.castSucc = c i.succ) :
      (∫ t in c i.castSucc..c i.succ, q i t) = 0 ∧ Fin.rankBlock ρ i = ∅ := by
    have heqρ := hr.injective ((hvalue _).trans (heq.trans (hvalue _).symm))
    exact ⟨by rw [heq, intervalIntegral.integral_same], (Fin.rankBlock_empty ρ i heqρ).1⟩
  exact ⟨hReal, hExtended, hFiniteOld, hFiniteNew⟩

/-- j.6.H: compare two weak subdivisions through the same common cut-value list. -/
theorem IsPiecewiseC1On.length_eq
    [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    (G : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M => TangentSpace I x))
    {γ : ℝ → M} {a b : ℝ} {n m : ℕ}
    {c : Fin (n+1) → ℝ} {r : Fin (m+1) → ℝ}
    (hγ : IsPiecewiseC1On I γ a b n c)
    (hγr : IsPiecewiseC1On I γ a b m r) :
    letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨G.toRiemannianMetric⟩
    let Lc : ℝ≥0∞ := ∑ i : Fin n, ∫⁻ t in Icc (c i.castSucc) (c i.succ),
      ‖mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc (c i.castSucc) (c i.succ)) t (1 : ℝ)‖ₑ
    let Lr : ℝ≥0∞ := ∑ j : Fin m, ∫⁻ t in Icc (r j.castSucc) (r j.succ),
      ‖mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc (r j.castSucc) (r j.succ)) t (1 : ℝ)‖ₑ
    piecewiseC1Length G γ c = piecewiseC1Length G γ r ∧
      Lc = Lr ∧ Lc < ⊤ ∧ Lr < ⊤ := by
  let s := Fin.commonCut c r
  let ρ := Fin.commonCutRankLeft c r
  let τ := Fin.commonCutRankRight c r
  obtain ⟨hr, hRange, hLeft, hRight⟩ := Fin.commonCut_properties c r
  change ∀ i, s (ρ i) = c i at hLeft
  change ∀ i, s (τ i) = r i at hRight
  obtain ⟨hr0, hrm, hρ, hτ, hρ0, hρn, hτ0, hτm⟩ :=
    Fin.commonCut_order_endpoints c r a b hγ.1 hγr.1
      hγ.2.1 hγ.2.2.1 hγr.2.1 hγr.2.2.1
  have hLeftG := hγ.length_eq_of_strictRefinement G s hr hr0 hrm ρ hρ hρ0 hρn hLeft
  have hRightG := hγr.length_eq_of_strictRefinement G s hr hr0 hrm τ hτ hτ0 hτm hRight
  have hReal : piecewiseC1Length G γ c = piecewiseC1Length G γ r :=
    hLeftG.1.trans hRightG.1.symm
  letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨G.toRiemannianMetric⟩
  have hExtended :
      (∑ i : Fin n, ∫⁻ t in Icc (c i.castSucc) (c i.succ),
        ‖mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc (c i.castSucc) (c i.succ)) t (1 : ℝ)‖ₑ) =
      ∑ i : Fin m, ∫⁻ t in Icc (r i.castSucc) (r i.succ),
        ‖mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc (r i.castSucc) (r i.succ)) t (1 : ℝ)‖ₑ :=
    hLeftG.2.1.trans hRightG.2.1.symm
  have hFiniteLeft := hLeftG.2.2.1
  have hFiniteRight := hRightG.2.2.1
  exact ⟨hReal, hExtended, hFiniteLeft, hFiniteRight⟩

/-- j.6.H: one old witness yields inserted-list regularity and real/extended length equality. -/
theorem IsPiecewiseC1On.refine_length
    [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    (G : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M => TangentSpace I x))
    {γ : ℝ → M} {a b : ℝ} {n m : ℕ}
    {c : Fin (n+1) → ℝ} (hγ : IsPiecewiseC1On I γ a b n c)
    (r : Fin (m+1) → ℝ) (hr : Monotone r)
    (hr0 : r 0 = a) (hrm : r (Fin.last m) = b)
    (hvalues : range c ⊆ range r) :
    IsPiecewiseC1On I γ a b m r ∧
    (letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨G.toRiemannianMetric⟩
    let Lc : ℝ≥0∞ := ∑ i : Fin n, ∫⁻ t in Icc (c i.castSucc) (c i.succ),
      ‖mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc (c i.castSucc) (c i.succ)) t (1 : ℝ)‖ₑ
    let Lr : ℝ≥0∞ := ∑ j : Fin m, ∫⁻ t in Icc (r j.castSucc) (r j.succ),
      ‖mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc (r j.castSucc) (r j.succ)) t (1 : ℝ)‖ₑ
    piecewiseC1Length G γ c = piecewiseC1Length G γ r ∧
      Lc = Lr ∧ Lc < ⊤ ∧ Lr < ⊤) := by
  have hNew := hγ.refine r hr hr0 hrm hvalues
  exact ⟨hNew, hγ.length_eq G hNew⟩

end Manifold
