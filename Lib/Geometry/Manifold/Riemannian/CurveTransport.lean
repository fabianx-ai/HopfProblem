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
/-!
# Pointwise speed, inverse differentials and fixed-subdivision curve transport

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

end Manifold
