# Stage-2 review — Lib/docs/J.md §§1–8 (mathematics only)

Reviewed: `Lib/docs/J.md` on branch `lib/J-tori` (commit f08cdba), sections 1–8 only
(everything from "# Axes 2–3" onward ignored, per protocol). Reviewed once, as
mathematics; no Lean comments; J.md not edited.

## Verdict

**Not correct as written: six CORRECTIONs are required.** No BLOCKERs — Theorems A–D
are all true and every proof strategy is sound; the defects are local: a wrong-direction
map label in Theorem B's display, a false auxiliary claim ("res is surjective") in §3's
Mayer–Vietoris computation, a garbled MV display, one unfinished/ill-typed formula in §4,
a misidentified fibration in Theorem B's Wang parenthetical, and a wrong Hatcher citation
number (Cor. 3.28) in two theorem headers. With corrections 1–6 applied, the text is
mathematically correct.

Findings are numbered in order of severity. Each cites the section and sentence and
gives the exact fix.

---

## Findings

### 1. CORRECTION — §1, Theorem B display: the first arrow is labeled `pr_{2*}` but points the wrong way (lines 32–33)

The display reads
`0 → H_{n+1}(Y) --pr_{2*}--> H_{n+1}(S¹×Y) --∂--> H_n(Y) → 0`.
But `pr₂ : S¹×Y → Y` induces `pr_{2*} : H_{n+1}(S¹×Y) → H_{n+1}(Y)`; as labeled, the map
has the wrong variance. The injective first map of the sequence is the pushforward of a
slice inclusion `incl_{x₀} : Y → S¹×Y, y ↦ (x₀, y)` (any basepoint `x₀ ∈ S¹`), which is a
section of `pr₂`, so `pr_{2*} ∘ incl_{x₀*} = id`. This is also what the rest of the
document uses: §4 line 129 writes `pr_{2*}^{-1}` for the first-summand inclusion (see
finding 5), i.e. the intended map is unambiguously the slice inclusion.

Exact fix: relabel the display and its surroundings as
`0 → H_{n+1}(Y) --incl_{x₀*}--> H_{n+1}(S¹×Y) --∂--> H_n(Y) → 0`,
"with `incl_{x₀}` the slice inclusion at a basepoint of `S¹` (a section of `pr₂`), split
on the right by the cross product with `[S¹]`".

### 2. CORRECTION — §1, Theorem B parenthetical: the "Wang sequence of the trivial fibration S¹ → S¹×Y → Y" is the wrong fibration (lines 35–36)

The Wang sequence is the long exact sequence of a fibration with *base* `S¹`. The
fibration whose Wang sequence is the displayed SES is `Y → S¹×Y → S¹` — the mapping
torus of `id_Y`, i.e. exactly Hatcher Ex. 2.48 with `f = id`, where `1 − f_* = 0` and the
long exact sequence `… → H_n(Y) --0--> H_n(Y) → H_n(T_f) → H_{n-1}(Y) --0--> …` breaks
into the stated short exact sequences. As written, `S¹ → S¹×Y → Y` has *fiber* `S¹` over
base `Y`; the long exact invariant of that fibration is the Gysin sequence (which for the
trivial bundle has Euler class 0 and yields the same SES — but it is not the Wang
sequence).

Exact fix: replace the parenthetical by
"(This is the Wang sequence of the trivial mapping torus, i.e. the fibration
`Y → S¹×Y → S¹` with identity monodromy — Hatcher Ex. 2.48 with `f = id`; equivalently
the Gysin sequence of the trivial circle bundle, `e = 0`.)"

### 3. CORRECTION — §3, exactness sentence: "res is surjective" is false; the fact that breaks the sequence is coker res ≅ H_n(Y) (lines 88–90)

The sentence "Exactness at the middle of `H_n(Y)² → H_n(Y)²` reads:
`ker res = {(b, −b)} ≅ H_n(Y)`, and `res` is surjective, so the long sequence breaks into
the short exact sequence of Theorem B" is wrong in its second clause. With
`res(u,v) = (u+v, u+v)`, the image is the diagonal `{(w, w)} ⊂ H_n(Y)²`, so `res` is
surjective only when `H_n(Y) = 0` (counterexample: `Y = pt`, where `res : ℤ² → ℤ²` has
cokernel `ℤ` — which is exactly `H₁(S¹)`, so the surjectivity claim would destroy the
very theorem being proved). The kernel computation is correct, but surjectivity is
neither true nor the needed fact: a long exact sequence `… → A --f--> B → C → D --g--> E → …`
always breaks into `0 → coker f → C → ker g → 0`, and here that gives
`0 → coker res_{n+1} → H_{n+1}(S¹×Y) → ker res_n → 0`. The needed computation is
`coker res ≅ H_n(Y)` (the diagonal is a direct summand; `(x, y) ↦ x − y` descends to an
isomorphism `H_n(Y)² / im res ≅ H_n(Y)`), in degree `n+1` as well as `n`.

Exact fix: replace "and `res` is surjective, so the long sequence breaks" by
"and `res` has image the diagonal, hence `coker res ≅ H_n(Y)` via `(x,y) ↦ x−y` (in every
degree); so the long sequence breaks into `0 → coker res_{n+1} → H_{n+1}(S¹×Y) →
ker res_n → 0`, which is".

### 4. CORRECTION — §3, displayed MV segment: the term left of `H_{n+1}(S¹×Y)` is garbled (lines 79–81)

The display begins
`… → H_{n+1}(U ∩ V) ⊗ H_{n+1}-term → H_{n+1}(S¹×Y) --∂--> H_n(U ∩ V × Y) → …`.
The term mapping into `H_{n+1}(S¹×Y)` in the Mayer–Vietoris sequence is the degree-(n+1)
term of the two *pieces*, `H_{n+1}(U×Y) ⊕ H_{n+1}(V×Y)` — not the intersection, and not a
tensor product; the `⊗` is a typo and `H_{n+1}(U ∩ V)` is missing its `×Y`. Later in the
same display, `H_n(U ∩ V × Y)` needs parentheses.

Exact fix: the display should read
`… → H_{n+1}(U×Y) ⊕ H_{n+1}(V×Y) → H_{n+1}(S¹×Y) --∂--> H_n((U∩V)×Y) → H_n(U×Y) ⊕ H_n(V×Y) → …`.

### 5. CORRECTION — §4, basis-theorem proof: "τ_s = pr_{2*}^{-1}…" is an unfinished sentence and an ill-typed map (line 129)

The sentence "…those not containing `1` (giving `τ_s = pr_{2*}^{-1}…`, i.e. the subtorus
classes lying in the `T^r` factor — the first summand)…" trails off into `\ldots`, and
`pr_{2*} : H_n(S¹×T^r) → H_n(T^r)` is surjective, not invertible, so `pr_{2*}^{-1}` does
not denote a map.

Exact fix: "…those not containing `1` (giving `τ_s = incl_{0*}(τ_s^{(r)})`, the
pushforward of the inductively known class along the slice inclusion
`incl₀ : T^r ↪ S¹×T^r` at `0 ∈ S¹` — the first-summand inclusion, a section of `pr_{2*}`)
and those containing `1`…".

### 6. CORRECTION — §1 Theorem A header, §6 theorem header, and the header bibliography line: "Hatcher Cor. 3.28" is a miscitation (lines 2, 22, 185)

Hatcher's Corollary 3.28 states: "If `M` is a closed connected `n`-manifold, the torsion
subgroup of `H_{n−1}(M; ℤ)` is trivial if `M` is orientable and `ℤ₂` if `M` is
nonorientable." It says nothing about tori, so "Hatcher Cor. 3.28, homology form" (used
for both Theorem A and the §6 theorem) points at a result that does not have the stated
form. The correct Hatcher references are: the homology ranks of `T^n` from the Künneth
formula (§3.B; the cellular prototype is Example 2.39 on `T³`); the exterior-algebra
*ring* computation `H^*(T^n; R) ≅ Λ_R[α₁,…,α_n]`, which is Example 3.16 (announced in
Example 3.13 "Exterior Algebras"); and the exact Pontryagin statement
`H_*(T^n; ℤ) ≅ Λ_ℤ[x₁,…,x_n]`, `|x_i| = 1`, which is §3.C, Exercise 11.

Exact fix: in both theorem headers and the contents line, replace "Corollary 3.28" /
"Cor. 3.28, homology form" by "cf. Example 3.16 (cohomology ring form) and §3.C
Exercise 11 (Pontryagin form)". (The other two citations check out: Ex. 2.48 is the
mapping-torus long exact sequence, and §3.C does define the Pontryagin product and states
associativity/graded-commutativity under (homotopy-)associative/commutative μ. For the
record, 3C.4 is the Hopf-algebra structure theorem and 3C.5 is the divided-polynomial
example — neither is the product axioms, and the document does not cite them.)

### 7. REMARK — §5, parenthetical: wrong ledger cross-reference (line 178)

"…and is this lane's new mathematics at general `n`; see ledger row J3)." The
general-`n` wedge map is ledger row **J6** ("Wedge maps (§5 end) — new at general n");
J3 is torus homology. Fix: "see ledger row J6".

### 8. REMARK — §6, proof: the key factorization step deserves its one-line justification (lines 193–194)

"…the Pontryagin product of `[S¹]` with a class of the `T^r` factor is exactly the cross
product `[S¹] × τ_{s'}` (the addition map on the first coordinate acts trivially on
classes supported in the factors)". The fact is correct and the proof rests on it; the
loose parenthetical should be the precise identity: for the slice inclusions
`incl₁ : S¹ → S¹×T^r` and `incl₂ : T^r → S¹×T^r` one has `μ ∘ (incl₁ × incl₂) = id` on the
nose, hence
`μ_*(incl₁* a × incl₂* b) = (μ ∘ (incl₁ × incl₂))_*(a × b) = a × b`.

### 9. REMARK — §3: reconcile the sign convention of `res` with the cited sources (lines 83–90)

With Hatcher's Mayer–Vietoris convention (a minus on the `V`-summand), `res` is
`(u,v) ↦ (u+v, −(u+v))`, not `(u+v, u+v)`; kernel `{(b,−b)}` and cokernel are unchanged.
The document's sign hedges are consistent, but one sentence noting the two displays
differ by the automorphism `(x,y) ↦ (x,−y)` of `H_n(Y)²` would reconcile the text with
the convention of the cited MV sources.

### 10. REMARK — §2: typo (line 71)

"Matlib's" → "Mathlib's".

---

## Checklist items that verify as written (for the record)

- **§3 restriction map.** `res : H_n(Y)² → H_n(Y)²`, `(u,v) ↦ (u+v, u+v)`: correct for
  the actual two-arc cover — each intersection arc × Y is a deformation retract of both
  `U×Y` and `V×Y`, so the restrictions of a `U`-class (resp. `V`-class) to the two
  intersection components agree; up to the sign convention of remark 9. Kernel
  `{(b, −b)} ≅ H_n(Y)`: correct.
- **§3 sign in `∂([S¹]×b) = (±b, ∓b)`.** Correct shape: with the fundamental cycle
  written as the arc sum `a_U + a_V`, `∂(a_U × b) = ∂a_U × b = (p₁ − p₀) × b` by the
  Leibniz rule (`∂b = 0` kills the second term), the two poles lie in different
  intersection components with opposite orientation signs; after fixing conventions
  `∂([S¹]×b) = (b, −b)`, and under `ker res ≅ H_n(Y)`, `(b,−b) ↦ b`, the cross product is
  a right inverse of `∂`. The hedge "up to the chosen isomorphism" is accurate.
- **§4 Pascal induction.** `H_n(T^{r+1}) ≅ H_n(T^r) ⊕ H_{n−1}(T^r) ≅
  ℤ^{C(r,n)} ⊕ ℤ^{C(r,n−1)} = ℤ^{C(r+1,n)}`: correct; the `H_0` base case explicitly uses
  path-connectedness (checklist hypothesis — present); the `n = 0` step with the implicit
  `H_{−1} = 0` is harmless since `n = 0` is covered by the base case; freeness/finiteness
  propagation and vanishing for `n > r` are correct. Coordinate-basis induction and the
  top-class claim are correct (modulo finding 5's formula fix).
- **§5 graded-commutativity sign.** `b·a = μ_*(b×a) = μ_* s_*(b×a) = (−1)^{pq} μ_*(a×b)`:
  correct — the middle equality is `μ ∘ s = μ`, the last is the cited swap law
  `s_*(b×a) = (−1)^{pq} a×b`; matches Hatcher §3.C's statement for homotopy-commutative
  `μ`. Unit and associativity arguments are correct.
- **§5/§6 alternation descent.** `a·a = −a·a` gives `2(a·a) = 0`; 2-torsion-freeness of
  `H_2(G)` gives strict alternation; adjacent-swap antisymmetry plus diagonal vanishing
  make the `n`-fold product an alternating multilinear map `H_1(G)^n → H_n(G)`, which
  descends to `∧ⁿH_1(G) → H_n(G)`. Correct; the hypothesis is stated and is discharged
  for tori in §6 ("all homology free").
- **§6 surjection + Orzech.** The wedge map hits the coordinate-subtorus basis `τ_s`
  (surjective); both sides are finite free of rank `C(r,n)` (§4 and Theorem D's basis
  count); a surjective linear endomorphism of a finite free ℤ-module is an isomorphism
  (Orzech; over ℤ also immediate from determinants). Applied correctly, finiteness
  hypotheses explicit.
- **§7 minor formula.** The expansion, the vanishing of repeated-index terms, the
  permutation sign bookkeeping `e_{i_{σ(1)}} ∧ … ∧ e_{i_{σ(n)}} = sign(σ) e_s`, and the
  collection `Σ_σ sign(σ) ∏_k A_{i_{σ(k)} j_k} = det(A_{s,t})` are all correct;
  Cauchy–Binet from functoriality `∧ⁿ(AB) = ∧ⁿA ∘ ∧ⁿB` is correctly stated.
- **Hidden hypotheses.** Path-connectedness for `H_0` (stated, §4); 2-torsion-freeness
  for alternation (stated, Theorem C; discharged in §6); freeness/finiteness for Orzech
  (explicit, §6); naturality in `Y` (stated in Theorem B and proved in §3). All present.
- **Cited theorems.** Ex. 2.48 = mapping-torus LES ✓; §3.C = Pontryagin product,
  (graded-)commutativity for commutative μ ✓; Cor. 3.28 ✗ — see finding 6.

## Summary

- BLOCKERs: none.
- CORRECTIONs (required before the text is mathematically correct as written): 1–6.
- REMARKs: 7–10.

Theorems A–D are true and the proofs are strategically sound throughout; the six
corrections are local edits (one arrow label, one parenthetical, one exactness clause,
one display, one unfinished formula, one citation number) and do not propagate beyond
their sentences.
