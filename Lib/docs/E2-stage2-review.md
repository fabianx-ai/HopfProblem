# Lane E2 — Stage-2 independent review (textbook §§1–12)

Reviewed: `~/s6-notes/review/E2.md` (stable copy), Axis 1 (§§1–12) only, once, as mathematics.
No Lean was built or run; the code was consulted only to confirm the hypotheses the document
intends to record (the pinned `exists_immersion_on_compact_rel` carries `Disjoint L C`; the
general-position theorems carry `IsClosed (Set.range g)` resp. `CompactSpace Y`).

**Verdict: NOT correct as written.** Two statements are false as printed (Findings 1–2,
BLOCKER), four further items need exact corrections (Findings 3–6, CORRECTION); twelve remarks
(Findings 7–18). The proof architecture is sound, and the specific checks requested pass except
where flagged: §4's translate direction is consistent; §5's bump-diffeomorphism claim is correct
modulo a one-line bijectivity argument; the plateau reduction is correct modulo a wrong citation
(T4 → T2) and a chart-restriction clause; the padding corollary's dimension logic is correct;
§8's GL⁺/normal-flip step is correct as a basis pre-adjustment, but the displayed shrinking
isotopy cannot exist as written and the realized-germ clause is garbled; §10's codimension
computation (codim n−k+1 of rank-deficient frames; the pullback count k + kn − (n−k+1) < kn ⟺
2k+1 ≤ n) is correct, but the lemma's stated hypotheses are insufficient; §11's approximation
hypotheses are fine; §12's crossing-chart and discrete+compact argument is correct in
conclusion, with the chart construction to be made explicit. No circularity: nothing in §§1–12
uses homology, the Hopf degree theorem, or π_n(Sⁿ).

## Verified correct (no action)

- **§4 (translate direction).** Φ(x,y) = g(y) − f(x); dΦ_(x,y) = dg_y − df_x surjective ⟺
  im df_x + im dg_y = F; Φ(x,y) = a ⟺ g(y) = f(x) + a; Sard (T1) applies since
  dim(X×Y) = D+Z = m = dim F; a regular value of Φ ⟺ (f+a) ⋔ g. The direction of translation
  is consistent throughout, and T2's stated form f ⋔ (g+a) follows by a ↦ −a (co-null sets are
  symmetric). See Remark 14 for the one-word clause to add.
- **§5 corollary (padding).** d = dim N − dim X − dim Y ≥ 1; X × S^d compact and
  dim(X×S^d) + dim Y = dim N, so T3 applies; at a meeting point the coproduct image has
  dimension ≤ dim X + dim Y < dim N, so transversality of the padded pair is possible only
  vacuously, forcing range(e∘f) ∩ range g = ∅. Correct.
- **§6 (dimension count).** Bad parameters lie in the image of a smooth map from a
  (dim X + dim Y)-dimensional source into ℝⁿ with dim X + dim Y < n; dim_H ≤ dim X + dim Y < n
  ⟹ empty interior ⟹ dense good set. Correct (with the sentence completion in Remark 10 and
  the T4 hypothesis fix in Correction 5).
- **§9 (homogeneity).** Orbits open via the §5 bump with a = y − x; an open partition of a
  connected space has one piece; support control inside U by choosing balls inside U. Correct.
- **§10 (codimension computation).** {rank ≤ r} ⊂ Hom(ℝᵏ,ℝⁿ) has codimension (n−r)(k−r); the
  top rank-deficient stratum r = k−1 has codim n−k+1; the evaluation (x, A) ↦ df_x + A is a
  submersion, so preimages of strata keep codimension; projecting over the k-dimensional core
  gives dim_H(bad) ≤ k + kn − (n−k+1) < kn ⟺ k < n−k+1 ⟺ 2k+1 ≤ n. Correct, and the sanity
  checks match the pins (k=1: 3 ≤ n; k=2: 5 ≤ n). The embedding half's count (expected
  double-point dimension 2k − n < 0; avoidance at codim n−2k ≥ 1) is also correct.
- **§11.** Whitney approximation applies to continuous f (empty closed set);
  dim_H(image) ≤ dim X < n ⟹ empty interior ⟹ p ∉ range exists; Sⁿ∖{p} ≅ ℝⁿ is contractible.
  Correct. (See Remark 16 on the Sard parenthetical.)
- **§12.** dim N + dim P = dim M plus transversality ⟹ the sum is direct; crossing chart ⟹
  isolated intersections ⟹ discrete; the intersection is closed in the compact range F, hence
  compact; discrete + compact ⟹ finite. Correct (with the explicit chart construction in
  Remark 17).
- **§16, open item 2** (restating §10's hypothesis): the disposition — perturbation proof at
  2k+1 ≤ n, Whitney's sharp 2k ≤ n recorded as needing the Stiefel-bundle argument — is
  correct.

## Findings

### 1. BLOCKER — T6 is false as stated at dim D = dim M (orientation)

**§1 (T6), "D a finite-dimensional inner-product space with dim D ≤ dim M … Then there is a
diffeomorphism P of M, isotopic to the identity, with P ∘ f = g on the unit ball" (lines
59–64); proved in §8.**

At k = n the conclusion fails without an orientation-compatibility hypothesis. An isotopy from
the identity has det dP > 0 everywhere (a path of nonzero determinants starting at +1), so
P ∘ f = g on the ball forces the derivative frames of f and g to have the same determinant
sign. Counterexample: M = ℝ², f the unit-disk inclusion, g = f ∘ ρ with ρ a reflection;
f(0) = g(0) = 0 and both are injective immersions on the ball, but P ∘ f = g on the ball would
force dP = ρ there. The proof's own Step 2 uses k < n ("available since k < n: the normal space
is nonzero, flip one normal vector").

**Fix.** Change the statement to `dim D < dim M` (matching the code, as the parenthetical
already records), or add the equal-dimensional clause: "if dim D = dim M, assume in addition
that the extended frames of df_0 and dg_0 have the same determinant sign; then no flip is
needed and the same proof applies."

### 2. BLOCKER — §10's immersion-creation lemma is false under its stated hypotheses

**§10, Lemma (immersion creation, general k), "f immersive on (a neighborhood of) K ∩ C-side…
precisely: f has injective derivative on K; then there is g, homotopic to f rel C (with
K ∩ C ⊆ int C-type hygiene), immersive on K ∪ L" (lines 264–267).**

Homotopy rel C pins the *values* of g on C, not the derivatives. If df fails to be injective on
a positive-length part of C ∩ L, no g with g|_C = f|_C can be immersive on L. Counterexample at
the pinned dimensions (k = 1, n = 3, so 2k+1 = 3 ≤ n): X = ℝ, N = ℝ³, f smooth with f ≡ 0 on
C := [0,1], L := [0,1], K := ∅. The stated hypothesis (injective derivative on K) holds
vacuously, but every g homotopic to f rel C is constant on [0,1], hence has dg = 0 on
(0,1) ⊆ L. The "K ∩ C ⊆ int C-type hygiene" clause does not exclude this.

**Fix — this is exactly the hypothesis of the pinned code `exists_immersion_on_compact_rel`,
which carries `(hdis : Disjoint L C)`.** State: "…C ⊆ X closed with **L ∩ C = ∅**, f with
injective derivative on K; then there is g, homotopic to f rel C, immersive on K ∪ L." The
proof then goes through unchanged: patches covering L are chosen with closures disjoint from C
(possible since L ∩ C = ∅), and the cutoff makes the perturbation rel C. Add the reduction of
the classical relative form (T8, first bullet: f already an immersion on a neighborhood of C)
to this form: with U an immersive neighborhood of C, split L into L ∩ Ū (already immersive;
fold into K) and L ∖ U (compact, disjoint from C; apply the lemma). Also repair T8's first
bullet, whose "more precisely on any compact K: … immersive on K ∪ L for a second compact L"
has the roles garbled: K is the already-immersive compact, L the target compact.

### 3. CORRECTION — §8 Step 1: the displayed shrinking family cannot satisfy the stated properties

**§8 Step 1, "the radial family R_t(x) = φ(t·‖x‖²)·x for a suitable bump φ is a diffeomorphism
isotopy moving the unit disk to the ε-disk, fixed outside a slightly larger ball" (lines
217–220).**

No single-variable bump φ can do this. R_0 = id forces φ(0) = 1. Fixedness outside a slightly
larger ball B_ρ for all t forces φ(t·‖x‖²) = 1 for all ‖x‖ ≥ ρ and all t ∈ [0,1]; since t·ρ²
sweeps all of [0, ρ²] as t varies, this forces φ ≡ 1 on [0, ρ²], in particular φ(1) = 1. But
moving the unit disk into the ε-disk requires φ(‖x‖²)·‖x‖ ≤ ε for ‖x‖ ≤ 1, in particular
φ(1) ≤ ε < 1. Contradiction. (Equivalently: for t < 1 the family moves points out to radius
≈ ρ/√t, so the support is not uniform in t — and the extension-by-identity step that follows
needs uniform support.)

**Fix.** Use a joint profile: R_t(x) = ((1−t) + t·ψ(‖x‖²))·x with ψ : [0,∞) → [ε,1] smooth,
ψ = ε on [0,1], ψ = 1 on [ρ²,∞), ψ′ ≥ 0 on the transition annulus. Then R_0 = id; R_1(x) = εx
on the unit ball; R_t = id outside B_ρ for all t; the tangential eigenvalue (1−t) + tψ ≥
min(1,ε) > 0 and the radial eigenvalue (1−t) + t(ψ + 2sψ′) ≥ min(1,ε) > 0, so each R_t is a
diffeomorphism, compactly supported uniformly in t.

### 4. CORRECTION — §3: "regular-value sets are automatically open-dense" is false; the comeager claim of T1 is unproved

**§3, "the complement is the claimed co-null set of regular values, and regular-value sets are
automatically open-dense... (density: a co-null set in a space with a nonzero-on-opens Haar
measure is dense)" (lines 112–114).**

Regular values need not form an open set. Example: f : ℝ → ℝ, f(x) = sin(x)/x (f(0) := 1). Its
nonzero critical points are the roots x_n of tan x = x, with critical values
f(x_n) = cos x_n → 0; but 0 is a regular value (f⁻¹(0) = {nπ : n ≠ 0}, and
f′(nπ) = (−1)ⁿ/(nπ) ≠ 0). So 0 is a non-interior point of the regular-value set. The
parenthetical proves only density (co-null ⟹ dense), not the "comeager" claim made in T1's
statement.

**Fix.** Replace the sentence by: "the complement is the claimed co-null set of regular values.
It is dense (a co-null set in a space with a nonzero-on-opens Haar measure is dense), indeed
comeager: the critical set is closed and X is σ-compact, so the critical set is a countable
union of compacts; each compact critical-value image is compact and null, hence has empty
interior (Haar is positive on nonempty opens), hence is nowhere dense; the critical values are
therefore meager."

### 5. CORRECTION — T4 (map form) needs range g closed (e.g. Y compact); §6's "avoidance is open" uses it

**§1 (T4), "If dim X + dim Y < dim N, X compact, then every smooth f : X → N is homotopic rel
any closed set C already avoiding g to a smooth f′ with range f′ ∩ range g = ∅" (lines 46–51);
§6, "since avoidance is open" (line 180).**

With only X compact, range g need not be closed, and then neither "avoidance is open" nor the
compactness of the bad set f⁻¹(range g) (needed for the finite patch cover) holds. The code
this records carries exactly this hypothesis in both its forms
(`exists_disjoint_smooth_map_homotopicRel_of_isClosed_range` with
`IsClosed (Set.range g)`, and the wrapper `exists_disjoint_smooth_map_homotopicRel` with
`CompactSpace Y`).

**Fix.** State T4's first half as: "If dim X + dim Y < dim N, X compact, and **Y compact (it
suffices that range g be closed)**, then every smooth f …". With that, the §6 proof stands:
compact pieces of f(X) disjoint from the closed range g are at positive distance from it, and
the bad set is compact, so the finite patch induction and the parameter-avoidance count apply.

### 6. CORRECTION — §5 plateau lemma cites T4; the correct citation is T2

**§5, plateau lemma, "…by parametric transversality (T4 applied in the chart; the hypothesis
dim X + dim Y = dim N is the dimension equation)" (lines 152–153).**

T4 is the disjunction theorem, whose hypothesis is dim X + dim Y < dim N — the opposite
inequality from what holds here. The result being applied is parametric transversality, T2
(whose hypothesis dim X + dim Y = dim F is exactly the quoted dimension equation).

**Fix.** "(T2 applied in the chart; the hypothesis dim X + dim Y = dim N is the dimension
equation)".

### 7. REMARK — §5 plateau lemma: applying T2 in the chart requires restricting g to the chart preimage

T2's codomain is a vector space, but g : Y → N. The application is to f|_{f⁻¹(U)} and
g|_{g⁻¹(U)} in chart coordinates. No meeting pairs are lost: for x ∈ K and ‖a‖ small,
e_a(f(x)) = f(x) + a remains in the chart, so any y with g(y) = e_a(f(x)) lies in g⁻¹(U).
Add one clause saying this.

### 8. REMARK — §5 bump family: bijectivity of e_a needs one line

Derivative invertibility (det(id + a ⊗ dβ) = 1 + dβ(a) ≠ 0 for ‖a‖ < (sup‖dβ‖)⁻¹) gives a
local diffeomorphism. For the global claim: e_a is proper (identity off supp β) and a local
diffeomorphism ℝⁿ → ℝⁿ, hence a covering, hence a diffeomorphism (ℝⁿ is simply connected).
Alternatively, ‖e_a(y₁) − e_a(y₂)‖ ≥ (1 − ‖a‖·sup‖dβ‖)·‖y₁ − y₂‖ gives injectivity directly,
with surjectivity from properness plus invariance of domain.

### 9. REMARK — §5 patch induction: the preservation mechanism is C¹-smallness, not support location

"Step i+1 perturbs by a bump supported so close to K_{i+1} and so small…" — the bump support is
fixed once the chart is chosen; what preserves transversality on K₁∪…∪Kᵢ is that e_a → id in
C¹ as a → 0, together with openness of joint surjectivity on the compact pair set
((K₁∪…∪Kᵢ) × Y, using Y compact). Also, each step's a must be small enough that the current
map still sends the not-yet-treated patches K_j into their (open) plateau balls B′_j, so the
plateau lemma remains applicable at later steps. One sentence making both points explicit.

### 10. REMARK — §6: complete the unfinished bad-set sentence

"…the set of bad parameters is the image under the smooth map (x, y) ↦ g(y) − f(x) on the patch
of the…" trails off. Complete it: the bad set for the patch is contained in the image of
(patch ∩ {β > 0}) × Y → ℝⁿ, (x, y) ↦ (g(y) − f(x))/β(x) — a smooth map from a
(dim X + dim Y)-manifold to ℝⁿ with dim X + dim Y < n. On {β = 0} the map is unperturbed; those
points are handled by the other patch cores.

### 11. REMARK — §7: surjectivity of each A(t, ·) should be stated

B(t, ·) is a diffeomorphism of Y only because each A(t, ·) : U → U is bijective; the stated
hypothesis is "diffeomorphisms onto open images". Surjectivity is automatic — A(t, ·) is a
proper local diffeomorphism (the preimage of a compact L ⊆ U lies in L ∪ K), hence a covering,
hence onto on each component of U (it meets every component, being the identity off K) — but
one clause should say so.

### 12. REMARK — §8 Step 2: make the realized-germ construction explicit; the normal flip is fine as stated

The clause "integrate the time-dependent linear map against a cutoff — the realized-germ
machinery: a germ of a diffeomorphism at 0 that is isotopic to the identity through germs with
the same 1-jet variation is realized by a compactly supported diffeomorphism" is garbled.
Replace it by the explicit construction: for the path A_t in GL⁺(n) with A_0 = I, let
X_t(x) = ψ(‖x‖²)·(dA_t/dt ∘ A_t⁻¹)(x) with ψ ≡ 1 near 0 and compactly supported; the flow B_t
of X_t is a compactly supported isotopy of ℝⁿ with B_0 = id, and on the plateau B_t = A_t, so
d(B_1 ∘ g)_0 = A_1 ∘ dg_0 = df_0. The GL⁺-connectedness argument (transvections; positive
determinant scales to 1) is correct, and the reflection is correctly described as a
*pre-adjustment* of the extended basis — a choice of basis, not a map applied to g, so it needs
no realization — available exactly when k < n.

### 13. REMARK — §8/T6: "the proof needs 2 ≤ dim M" is not used by any displayed step

Steps 1–3 work for all n ≥ 1 with k < n (k = 0 is trivial). Record the provenance of the
2 ≤ dim M hypothesis (presumably consumer-side, e.g. avoidance when moving disjoint disks) or
drop the clause.

### 14. REMARK — §4/T2: the proved form is (f + a) ⋔ g; the stated form is f ⋔ (g + a)

The proof concludes "the translates f + a and g (equivalently f and g − a) are everywhere
transverse", while T2's statement quantifies a with f ⋔ (g + a). Add "(equivalently
f ⋔ (g + a), replacing a by −a; co-null sets are symmetric under negation)". The translate
direction itself is consistent (verified above).

### 15. REMARK — §10 embedding half: one clause for double-point compactness; move the non-C sheet

"…is compact (immersion + compactness)" uses that an immersion is locally injective, so the
diagonal is open in D = {(x, y) ∈ K×K : f(x) = f(y)}; D minus that open neighborhood of the
diagonal is closed in the compact K×K. Also, in the relative situation a double point with one
foot in C must be removed by moving the sheet whose foot is not in C (the C-values are pinned);
injectivity of f on K ∩ C plus local injectivity excludes pairs with both feet near C.

### 16. REMARK — §11: the "(equivalently Sard …)" parenthetical cites the wrong tool

"(equivalently Sard (T1-style dimension count): a smooth map from a lower-dimensional manifold
has all values critical, so its image is null)" — T1 as stated in §1 is equal-dimensional only,
and §3's remark says the general Sard is not proved in this lane. The nullness here needs no
Sard at all: a smooth image of a d-manifold has dim_H ≤ d < n, hence is null — the dim_H input
already recorded in §2. Reword the parenthetical to cite the dim_H count only.

### 17. REMARK — §12: give the crossing chart explicitly

The "(flow/pushout construction)" should be replaced by the elementary construction: first
straighten the F-sheet (submanifold chart: F-sheet = ℝ^{dim N} × {0}); the direct-sum
decomposition says the G-sheet's tangent at z projects isomorphically onto the
{0} × ℝ^{dim P} factor, so near z the G-sheet is a graph {(h(b), b)} over {0} × ℝ^{dim P}; the
shear (a, b) ↦ (a − h(b), b) straightens it while preserving the F-sheet. (Equivalently: the
inverse function theorem applied to a locally defined combined parametrization whose
differential at (x, y) is dF_x ⊕ dG_y.) The discrete + compact ⟹ finite conclusion is correct.

### 18. REMARK — §1: theorem-number citations are hedged; verify against the books when bib keys land

The citations carry "pattern"/"form" hedges (Hirsch Ch. 3 Thm. 1.3, 2.1, 2.5; Ch. 8 Thm. 1.3;
Ch. 2 Thms. 1.1, 1.3; Milnor TDV §2; Milnor h-cobordism Thm. 9.6; Guillemin–Pollack Ch. 2). The
cited *forms* are the standard statements of those names, and the mathematics attributed to
them is used correctly; the exact numbers should be verified against the books when the
docstring bib keys are added (open item 4 already records the bib-key issue).

---

**Summary.** Findings 1–2 must be fixed before this document can serve as the lane's textbook
(both are false as printed, with one-line corrections that match the pinned code); Findings
3–6 are definite corrections; Findings 7–18 are remarks. Everything else in §§1–12 checks out,
including all the specific items called out for review (§4 translate direction; §5 bump and
plateau reduction; padding corollary; §8 GL⁺/normal-flip; §10 codimension counts; §11; §12).
