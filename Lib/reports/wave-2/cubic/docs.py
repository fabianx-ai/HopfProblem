#!/usr/bin/env python3
"""Comment-only: replace the docstring of each listed declaration in the Cubic pieces."""
import re, glob, textwrap, sys
D='/home/goblin/hopf-w2-cubic/Lib/Geometry/Manifold/Morse/Cubic/'
FLOW="Let `f`, `D : X → ℝ` be continuous such that `s ↦ f (F s x)` has derivative `D (F t x)` at `t`, for all `x` and `t`. "
DOCS={
# Model
'MorseCancellation.Model':"The model space `ℝ × (Fin m → ℝ)` of the cubic birth–death family: one axis coordinate and `m` transverse coordinates.",
'MorseCancellation.cubic':"The cubic family `cubic σ t (x, y) = x ^ 3 / 3 + t * x + ∑ i, σ i * y i ^ 2` on `Model m`.",
'MorseCancellation.differential':"The derivative of `cubic σ t` at `p = (x, y)` (see `hasFDerivAt_cubic`): the continuous linear form `v ↦ (x ^ 2 + t) * v.1 + ∑ i, 2 * σ i * y i * v.2 i`.",
'MorseCancellation.differential_apply':"`differential σ t p v = (p.1 ^ 2 + t) * v.1 + ∑ i, 2 * σ i * p.2 i * v.2 i`.",
'MorseCancellation.contDiff_cubic_family':"The cubic family is smooth jointly in the parameter and the point: `(t, p) ↦ cubic σ t p` is `C^∞`.",
'MorseCancellation.contDiff_cubic':"For fixed `σ` and `t` the function `cubic σ t` is `C^∞`.",
'MorseCancellation.hasFDerivAt_cubic':"`cubic σ t` has Fréchet derivative `differential σ t p` at `p`.",
'MorseCancellation.fderiv_cubic':"`fderiv ℝ (cubic σ t) p = differential σ t p`.",
'MorseCancellation.critical_iff':"If all `σ i ≠ 0`, then `p` is a critical point of `cubic σ t` iff `p.1 ^ 2 + t = 0` and `p.2 = 0`.",
'MorseCancellation.cubic_zero_unique_critical':"If all `σ i ≠ 0`, then `p` is a critical point of `cubic σ 0` iff `p = 0`.",
'MorseCancellation.positive_parameter_no_critical':"If all `σ i ≠ 0` and `0 < t`, then `cubic σ t` has no critical point.",
'MorseCancellation.negative_parameter_critical_iff':"If all `σ i ≠ 0`, the critical points of `cubic σ (-a ^ 2)` are exactly `(a, 0)` and `(-a, 0)`.",
'MorseCancellation.cubic_critical_values':"The values of `cubic σ (-a ^ 2)` at `(a, 0)` and `(-a, 0)` are `-(2 * a ^ 3 / 3)` and `2 * a ^ 3 / 3`.",
# SublevelFlow
'FlowCancellation.exists_local_strict_flow_descent':FLOW+"If `D x < 0`, then `t ↦ f (F t x)` is strictly decreasing on `[-ε, ε]` for some `ε > 0`.",
'FlowCancellation.exists_local_strict_sublevel_entry':FLOW+"If `D < 0` on the level `f = c` and `f x ≤ c`, then there is `ε > 0` with `f (F t x) < c` for all `t ∈ (0, ε]`.",
'FlowCancellation.forwardInvariant_sublevel_of_boundary':FLOW+"If `D < 0` on the level `f = c`, then the sublevel set `{f ≤ c}` is forward invariant: `f x ≤ c` and `0 ≤ t` imply `f (F t x) ≤ c`.",
'FlowCancellation.interior_sublevel_eq_of_boundary':"Let `f : X → ℝ` be continuous such that `s ↦ f (F s x)` has derivative `D (F t x)` at `t`, for all `x` and `t`. If `D < 0` on the level `f = c`, then the interior of `{f ≤ c}` is `{f < c}`.",
'FlowCancellation.strict_sublevel_entry_of_boundary':FLOW+"If `D < 0` on the level `f = c`, then every positive time maps `{f ≤ c}` into `{f < c}`: `f x ≤ c` and `0 < t` imply `f (F t x) < c`.",
'FlowCancellation.flow_level_time_unique':FLOW+"If `D < 0` on the level `f = c`, then an orbit meets that level at most once: `f (F s x) = c` and `f (F t x) = c` imply `s = t`.",
# LevelOrbit
'MorseCancellation.contMDiff_directionalDerivative':"For a smooth function `f` and a smooth vector field `V` on a manifold `M`, the directional derivative `x ↦ mvfderiv 𝓘(ℝ, E) f x (V x)` is smooth.",
'MorseCancellation.native_same_level_orbit_points':"Let `f` and the vector field `V` be smooth, `F` a flow whose orbits are integral curves of `V`, and suppose the derivative of `f` along `V` is negative on the level `f = c`. Then two points `x`, `y` of that level on a common orbit (`F s x = F t y`) are equal.",
# SurgeryWindowsExistence
'MorseCancellation.nonempty_adaptedSurgeryWindows':"A smooth Morse function `f` on a compact Hausdorff manifold modelled on a finite-dimensional space which is injective on its critical points admits adapted surgery windows: `Nonempty (AdaptedWindows E f)`.",
# EndpointChart
'MorseCancellation.endpointCoordinate':"The Morse coordinate `u = (s - e * a) * √(a + e * (s - e * a) / 3)` of the cubic `s ^ 3 / 3 - a ^ 2 * s` at its critical point `e * a`, `e = ±1` (see `cubic_endpoint_square`).",
'MorseCancellation.endpointDomain':"The set `{s | 0 < a + e * (s - e * a) / 3}`, on which `endpointCoordinate a e` is smooth.",
'MorseCancellation.endpointDomain_open':"`endpointDomain a e` is open.",
'MorseCancellation.endpoint_mem_domain':"For `0 < a` the point `e * a` lies in `endpointDomain a e`.",
'MorseCancellation.endpointCoordinate_center':"`endpointCoordinate a e (e * a) = 0`.",
'MorseCancellation.contDiffOn_endpointCoordinate':"`endpointCoordinate a e` is `C^∞` on `endpointDomain a e`.",
'MorseCancellation.hasDerivAt_endpointCoordinate':"For `0 < a`, `endpointCoordinate a e` has derivative `√a` at `e * a`.",
'MorseCancellation.cubic_endpoint_square':"Morse normal form of the cubic model: if `e ^ 2 = 1` and `p.1 ∈ endpointDomain a e`, then `cubic σ (-a ^ 2) p = cubic σ (-a ^ 2) (e * a, 0) + e * u ^ 2 + ∑ i, σ i * p.2 i ^ 2` with `u = endpointCoordinate a e p.1`.",
'MorseCancellation.exists_endpoint_scalar_chart':"For `0 < a` there is a smooth partial diffeomorphism `Φ` of `ℝ` whose source contains `e * a` and is contained in `endpointDomain a e`, whose underlying function is `endpointCoordinate a e`, and with `Φ (e * a) = 0`.",
'MorseCancellation.scalarProductChart':"The product of a smooth partial diffeomorphism `Φ` of `ℝ` with the identity of `V`: the partial diffeomorphism `(s, y) ↦ (Φ s, y)` of `ℝ × V` with source `Φ.source ×ˢ univ`.",
'MorseCancellation.exists_endpoint_product_chart':"For `0 < a` and `e ^ 2 = 1` there is a smooth partial diffeomorphism `P` of `Model m` with `(e * a, 0) ∈ P.source`, `P (e * a, 0) = 0`, preserving the transverse coordinates, such that for `p ∈ P.source`: `cubic σ (-a ^ 2) p = cubic σ (-a ^ 2) (e * a, 0) + e * (P p).1 ^ 2 + ∑ i, σ i * (P p).2 i ^ 2`.",
# LocalReplacement
'LocalFunctionReplacement.replace':"`replace Φ f b y` is `b (Φ.symm y)` for `y ∈ Φ.target` and `f y` otherwise: the function `f` with `b`, read in the chart `Φ`, substituted on the image of `Φ`.",
'LocalFunctionReplacement.replace_of_mem':"For `y ∈ Φ.target`, `replace Φ f b y = b (Φ.symm y)`.",
'LocalFunctionReplacement.replace_of_notMem':"For `y ∉ Φ.target`, `replace Φ f b y = f y`.",
'LocalFunctionReplacement.replace_chart':"For `x ∈ Φ.source`, `replace Φ f b (Φ x) = b x`.",
'LocalFunctionReplacement.replace_germ_chart':"Near a point `y ∈ Φ.target` the function `replace Φ f b` coincides with `b ∘ Φ.symm`.",
'LocalFunctionReplacement.replace_self':"If `f (Φ x) = b x` for all `x ∈ Φ.source`, then `replace Φ f b = f`.",
'LocalFunctionReplacement.replace_eq_off_support':"If `f (Φ x) = b₀ x` on `Φ.source` and `b₁ = b₀` outside `K`, then `replace Φ f b₁ y = f y` for every `y ∉ Φ '' K`.",
'LocalFunctionReplacement.replace_germ_off_support':"Let `M` be Hausdorff, `K ⊆ Φ.source` compact, `f (Φ x) = b₀ x` on `Φ.source` and `b₁ = b₀` outside `K`. Then `replace Φ f b₁` coincides with `f` near every `y ∉ Φ '' K`.",
'LocalFunctionReplacement.contMDiff_replace':"Let `M` be Hausdorff, `f : M → ℝ` and `b₁ : E → ℝ` smooth, `K ⊆ Φ.source` compact, `f (Φ x) = b₀ x` on `Φ.source` and `b₁ = b₀` outside `K`. Then `replace Φ f b₁` is smooth.",
'LocalFunctionReplacement.replace_critical_iff':"For smooth `b` and `y ∈ Φ.target`, the derivative of `replace Φ f b` vanishes at `y` iff the derivative of `b` vanishes at `Φ.symm y`.",
# Tanh
'Real.hasDerivAt_tanh':"`Real.tanh` has derivative `1 - tanh t ^ 2` at `t`.",
'Real.strictMono_tanh':"`Real.tanh` is strictly monotone.",
'Real.tendsto_tanh_atTop':"`Real.tanh` tends to `1` at `+∞`.",
'Real.tendsto_tanh_atBot':"`Real.tanh` tends to `-1` at `-∞`.",
'Real.contDiffAt_artanh':"`Real.artanh` is `C^∞` at every point of `(-1, 1)`.",
# AxisParameter
'MorseCancellation.cubicAxisParameter':"`cubicAxisParameter a t = a * tanh (a * t)`: the solution of `s' = a ^ 2 - s ^ 2` with `s 0 = 0` (see `hasDerivAt_cubicAxisParameter`), i.e. the axis coordinate of the orbit of the cubic descent field through the origin.",
'MorseCancellation.hasDerivAt_cubicAxisParameter':"`cubicAxisParameter a` has derivative `a ^ 2 - cubicAxisParameter a t ^ 2` at `t`.",
'MorseCancellation.cubicAxisParameter_mem':"For `0 < a`, `cubicAxisParameter a t ∈ (-a, a)`.",
'MorseCancellation.range_cubicAxisParameter':"For `0 < a` the range of `cubicAxisParameter a` is `(-a, a)`.",
'MorseCancellation.tendsto_cubicAxisParameter_atTop':"For `0 < a`, `cubicAxisParameter a t → a` as `t → +∞`.",
'MorseCancellation.tendsto_cubicAxisParameter_atBot':"For `0 < a`, `cubicAxisParameter a t → -a` as `t → -∞`.",
'MorseCancellation.cubicModelOrbit':"The curve `t ↦ (cubicAxisParameter a t, 0)` in `Model m`.",
'MorseCancellation.cubicModelOrbit_zero':"`cubicModelOrbit a 0 = 0`.",
'MorseCancellation.hasDerivAt_cubicModelOrbit':"`cubicModelOrbit a` is an integral curve of `cubicDescent σ (-a ^ 2)`: its derivative at `t` is the value of the field at `cubicModelOrbit a t`.",
'MorseCancellation.range_cubicModelOrbit':"For `0 < a` the range of `cubicModelOrbit a` is the open axis segment `(-a, a) ×ˢ {0}`.",
'MorseCancellation.tendsto_cubicModelOrbit_atTop':"For `0 < a`, `cubicModelOrbit a t → (a, 0)` as `t → +∞`.",
'MorseCancellation.tendsto_cubicModelOrbit_atBot':"For `0 < a`, `cubicModelOrbit a t → (-a, 0)` as `t → -∞`.",
'MorseCancellation.contDiff_cubicAxisParameter':"`cubicAxisParameter a` is `C^∞`.",
'MorseCancellation.cubicAxisClock':"`cubicAxisClock a s = artanh (s / a) / a`: the time at which `cubicAxisParameter a` takes the value `s`.",
'MorseCancellation.cubicAxisClock_parameter':"For `0 < a`, `cubicAxisClock a (cubicAxisParameter a t) = t`.",
'MorseCancellation.cubicAxisParameter_clock':"For `0 < a` and `s ∈ (-a, a)`, `cubicAxisParameter a (cubicAxisClock a s) = s`.",
'MorseCancellation.contDiffOn_cubicAxisClock':"For `0 < a`, `cubicAxisClock a` is `C^∞` on `(-a, a)`.",
# DescentField
'MorseCancellation.cubicDescent':"The descent field of the cubic model: `cubicDescent σ t (x, y) = (-(x ^ 2 + t), fun i => -σ i * y i)`.",
'MorseCancellation.differential_cubicDescent':"`differential σ t p (cubicDescent σ t p) = -(p.1 ^ 2 + t) ^ 2 - 2 * ∑ i, (σ i * p.2 i) ^ 2`.",
'MorseCancellation.cubicDescent_strict':"At a point `p` which is not critical for `cubic σ t`, the derivative of `cubic σ t` in the direction `cubicDescent σ t p` is negative.",
'MorseCancellation.cubicDescent_zero_of_critical':"`cubicDescent σ t` vanishes at every critical point of `cubic σ t`.",
'MorseCancellation.nativeCubicDescent':"The cubic descent field `cubicDescent σ t` transported to `M` by a chart `Φ : Model m → M`, namely `FlowConstruction.partialChartField Φ.symm (cubicDescent σ t)`.",
'MorseCancellation.endpointFieldCoordinate':"The coordinate `u = (s - e * a) / (a + e * s)`, which linearises the field `a ^ 2 - s ^ 2` at its zero `e * a`, `e = ±1` (see `endpointFieldCoordinate_pushforward`).",
'MorseCancellation.endpointFieldDomain':"The set `{s | 0 < a + e * s}`, on which `endpointFieldCoordinate a e` is smooth.",
'MorseCancellation.endpointFieldDomain_open':"`endpointFieldDomain a e` is open.",
'MorseCancellation.endpointField_mem_domain':"For `0 < a` and `e ^ 2 = 1` the point `e * a` lies in `endpointFieldDomain a e`.",
'MorseCancellation.endpointFieldCoordinate_center':"`endpointFieldCoordinate a e (e * a) = 0`.",
'MorseCancellation.contDiffOn_endpointFieldCoordinate':"`endpointFieldCoordinate a e` is `C^∞` on `endpointFieldDomain a e`.",
'MorseCancellation.hasDerivAt_endpointFieldCoordinate':"For `e ^ 2 = 1` and `s ∈ endpointFieldDomain a e`, `endpointFieldCoordinate a e` has derivative `2 * a / (a + e * s) ^ 2` at `s`.",
'MorseCancellation.endpointFieldCoordinate_pushforward':"For `e ^ 2 = 1` and `s ∈ endpointFieldDomain a e`, the coordinate `u = endpointFieldCoordinate a e` pushes the field `a ^ 2 - s ^ 2` forward to the linear field `-2 * e * a * u`: `deriv u s * (a ^ 2 - s ^ 2) = (-2 * e * a) * u s`.",
'MorseCancellation.exists_endpoint_field_scalar_chart':"For `0 < a` and `e ^ 2 = 1` there is a smooth partial diffeomorphism `P` of `ℝ` whose source contains `e * a` and is contained in `endpointFieldDomain a e`, whose underlying function is `endpointFieldCoordinate a e`, and with `P (e * a) = 0`.",
'MorseCancellation.endpointLinearField':"The linear field `(u, y) ↦ (-2 * e * a * u, fun i => -σ i * y i)` on `Model m`: the form of the cubic descent field at the critical point `(e * a, 0)` in the coordinates `endpointFieldProduct a e`.",
'MorseCancellation.endpointFieldProduct':"The map `(s, y) ↦ (endpointFieldCoordinate a e s, y)` of `Model m`.",
'MorseCancellation.fderiv_endpointFieldProduct_cubic':"For `e ^ 2 = 1` and `p.1 ∈ endpointFieldDomain a e`, the derivative of `endpointFieldProduct a e` at `p` maps `cubicDescent σ (-a ^ 2) p` to `endpointLinearField σ a e (endpointFieldProduct a e p)`.",
'MorseCancellation.exists_endpoint_field_product_chart':"For `0 < a` and `e ^ 2 = 1` there is a smooth partial diffeomorphism `P` of `Model m` with `(e * a, 0) ∈ P.source`, `P (e * a, 0) = 0` and underlying function `endpointFieldProduct a e`, whose derivative maps `cubicDescent σ (-a ^ 2) p` to `endpointLinearField σ a e (P p)` for every `p ∈ P.source`.",
'MorseCancellation.partialChartField_of_model_conjugacy':"If the derivative of the partial diffeomorphism `P` maps the field `W` to the field `U` at every point of `P.source`, then `W` transported by the chart `P.trans Q` and `U` transported by the chart `Q` agree on `(P.trans Q).target`.",
'MorseCancellation.exists_native_cubic_field_endpoint':"Let `0 < a`, `e ^ 2 = 1`, and let `Q : Model m → M` be a chart with `0 ∈ Q.source` such that on `Q.target` the field `V` is `endpointLinearField σ a e` transported by `Q`. Then there is a chart `Φ` with `(e * a, 0) ∈ Φ.source`, `Φ (e * a, 0) = Q 0`, `Φ.target ⊆ Q.target` and underlying function `Q ∘ endpointFieldProduct a e`, such that `V = nativeCubicDescent σ Φ (-a ^ 2)` on `Φ.target`.",
}
done=set()
for f in sorted(glob.glob(D+'*.lean')):
    L=open(f).read().split('\n'); out=[]; i=0; n=len(L)
    # find decl lines
    idx={}
    for k,l in enumerate(L):
        m=re.match(r'(?:theorem|def|abbrev) (\S+)',l)
        if m and m.group(1) in DOCS: idx[k]=m.group(1)
    kill=set(); ins={}
    for k,name in idx.items():
        j=k-1
        while L[j].startswith('attribute') or L[j].startswith('@['): j-=1
        e=j; assert L[e].rstrip().endswith('-/'),(name,L[e])
        while not L[j].startswith('/--'): j-=1
        kill.update(range(j,e+1))
        w=textwrap.wrap('/-- '+DOCS[name]+' -/',width=100,break_long_words=False,break_on_hyphens=False)
        ins[j]=w; done.add(name)
    for k,l in enumerate(L):
        if k in ins: out.extend(ins[k])
        if k in kill: continue
        out.append(l)
    open(f,'w').write('\n'.join(out))
print(len(done),'docstrings rewritten; missing:',set(DOCS)-done)
