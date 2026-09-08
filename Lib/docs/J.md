# Lane J — textbook, decomposition, placement, and typed ledger

**Homology of tori, the Pontryagin product, and exterior-power coordinates** (Hatcher,
*Algebraic Topology*: Example 2.48 adjacent, Corollary 3.28, §3.C), generalized from the
rank-4-pinned formalization (`Lattice := Fin 4 → ℤ`) to arbitrary rank.

Contents:

* **Axis 1** (§§1–8): the complete textbook proofs, in ordinary mathematical language. No Lean
  names occur in these sections.
* **Axes 2–3** (§9): the additive decomposition in dependency order.
* **Axis 4** (§10): file placement under `Lib/` with Mathlib twins.
* **Axis 5** (§11): the typed ledger, with the seams on lanes A and C recorded.
* **Open items** (§12).

---

# Axis 1 — the textbook proofs

## 1. The theorems

**Theorem A (homology of the torus; Hatcher Cor. 3.28, homology form).**
Let $T^r = (S^1)^r$ be the product $r$-torus. Then $H_n(T^r;\mathbb{Z})$ is free abelian of rank
$\binom{r}{n}$, and the Pontryagin (exterior) map
$$\wedge^n H_1(T^r;\mathbb{Z}) \longrightarrow H_n(T^r;\mathbb{Z}), \qquad
a_1 \wedge \dots \wedge a_n \longmapsto a_1 \cdot \ldots \cdot a_n,$$
is an isomorphism for every $n \geq 0$.

**Theorem B (the circle splitting; the trivial Wang sequence).**
For every space $Y$ and every $n$ there is a natural short exact sequence, split by the cross
product with the positive generator $[S^1] \in H_1(S^1)$,
$$0 \longrightarrow H_{n+1}(Y) \xrightarrow{\;\mathrm{pr}_{2*}\;}
H_{n+1}(S^1 \times Y) \xrightarrow{\;\partial\;} H_n(Y) \longrightarrow 0,$$
so $H_{n+1}(S^1 \times Y) \cong H_{n+1}(Y) \oplus H_n(Y)$, with the second summand embedded by
$b \mapsto [S^1] \times b$. (This is the Wang sequence of the trivial fibration
$S^1 \to S^1 \times Y \to Y$; Hatcher Ex. 2.48 treats the general mapping torus.)

**Theorem C (Pontryagin product; Hatcher §3.C).** For a topological abelian group $G$, singular
homology $H_*(G;\mathbb{Z})$ carries an associative, unital, graded-commutative ring structure
$$a \cdot b := \mu_*(a \times b), \qquad \mu \colon G \times G \to G \text{ the addition},$$
with $a \cdot b = (-1)^{pq}\, b \cdot a$ for $a \in H_p$, $b \in H_q$, and the class of the
identity point as unit. If $H_2(G)$ has no $2$-torsion, the product on $H_1$ is strictly
alternating ($a \cdot a = 0$) and induces maps
$\wedge^n H_1(G) \to H_n(G)$ for every $n$.

**Theorem D (exterior coordinates; the minor formula).** The standard basis
$(e_1, \dots, e_m)$ of $\mathbb{Z}^m$ gives the basis of $\wedge^n \mathbb{Z}^m$ indexed by
$n$-element subsets $s = \{i_1 < \dots < i_n\}$, $e_s := e_{i_1} \wedge \dots \wedge e_{i_n}$.
For an integer matrix $A \in \mathrm{M}_m(\mathbb{Z})$, the induced map $\wedge^n A$ has, in
these bases, the $(s, t)$-entry
$$\big(\wedge^n A\big)_{s, t} \ =\ \det A_{s, t},$$
the determinant of the $n \times n$ submatrix on rows $s$ and columns $t$ (the
minor-determinant formula; its multiplicativity is Cauchy–Binet).

Theorem A's isomorphism is the composite: $\wedge^n H_1(T^r) \to H_n(T^r)$ (Theorem C applied
to $G = T^r$) is an isomorphism because it sends the exterior basis to the coordinate-subtorus
basis of Theorem A's free module (§6). Theorem D is the coordinate description used by every
consumer that computes monodromy actions on $H_n$ of tori.

## 2. Conventions and standing inputs

Singular chains and homology with $\mathbb{Z}$ coefficients, the two-arc cover of the circle,
Mayer–Vietoris, and the homology of a point are lane A material and are cited by name. The
singular cross product $\times \colon H_p(X) \otimes H_q(Y) \to H_{p+q}(X \times Y)$ with its
Leibniz rule, naturality, unitality, swap law
$(\mathrm{swap})_*(a \times b) = (-1)^{pq}\, b \times a$ and associator coherence is lane C
material (`CrossProduct.lean`), cited by name. The circle $S^1$ is the additive circle
$\mathbb{R}/\mathbb{Z}$; $[S^1]$ is the class of the positively oriented fundamental cycle (the
sum of two arcs; the code's `arcSumCycle`). The product torus is $T^r := (S^1)^r$, a
topological abelian group under coordinatewise addition. Exterior powers $\wedge^n M$ are
Matlib's (the quotient of $M^{\otimes n}$ by the alternating relations; universal alternating
map $\iota_n \colon M^n \to \wedge^n M$).

## 3. The circle splitting (proof of Theorem B)

Cover $S^1 = U \cup V$ by two open arcs with intersection two short arcs around the two
"poles", so $U, V \simeq *$, $U \cap V \simeq S^0$, all pulled back to the cover
$\{U \times Y, V \times Y\}$ of $S^1 \times Y$. Mayer–Vietoris for this cover gives
$$\dots \to H_{n+1}(U \cap V) \otimes \textstyle H_{n+1}\text{-term} \;\to\;
H_{n+1}(S^1 \times Y) \xrightarrow{\partial} H_n(U \cap V \times Y) \to H_n(U \times Y) \oplus
H_n(V \times Y) \to \dots$$
and the identifications $H_k(U \times Y) \oplus H_k(V \times Y) \cong H_k(Y)^2$,
$H_k(U \cap V \times Y) \cong H_k(Y)^2$ turn the connecting homomorphism and the restriction
map into
$$\partial \colon H_{n+1}(S^1 \times Y) \to H_n(Y)^2, \qquad
\mathrm{res} \colon H_n(Y)^2 \to H_n(Y)^2,\ (u, v) \mapsto (u + v,\ u + v)$$
(the restrictions of a class on $U \times Y$ and $V \times Y$ to each intersection arc agree,
both being the pullback along the inclusion). Exactness at the middle of
$H_n(Y)^2 \to H_n(Y)^2$ reads: $\ker \mathrm{res} = \{(b, -b)\} \cong H_n(Y)$, and $\mathrm{res}$
is surjective, so the long sequence breaks into the short exact sequence of Theorem B.

**The splitting.** The cross product with $[S^1]$ splits $\partial$: for $b \in H_n(Y)$,
$$\partial\big([S^1] \times b\big) = \big(\pm b, \mp b\big),$$
because the chain-level boundary of the product cycle $[\text{arc sum}] \times b$ is the
difference of the two endpoint contributions (the Leibniz rule kills $b$'s boundary term since
$\partial b = 0$; the boundary of the fundamental cycle of $S^1$ is the difference of the two
poles, and the two intersection arcs contribute with opposite orientation signs). With the sign
conventions of the cover fixed once, $\partial([S^1] \times b) = (b, -b)$ up to the chosen
isomorphism $\ker \mathrm{res} \cong H_n(Y)$; hence $b \mapsto [S^1] \times b$ is a right
inverse of $\partial$, and
$$H_{n+1}(S^1 \times Y) \cong H_{n+1}(Y) \oplus H_n(Y),$$
naturally in $Y$ (naturality of Mayer–Vietoris and of the cross product). This is the code's
`circleProductHomologyEquiv`; the section identification is `positiveCircleCross` with
`circleBoundary_positiveCircleCross`. $\square$

## 4. The homology of the product torus (proof of Theorem A, first half)

**Proposition.** $H_n(T^r)$ is free abelian of rank $\binom{r}{n}$ (zero for $n > r$).

*Proof.* Simultaneous structural recursion on $(r, n)$. $H_0(T^r) = \mathbb{Z}$ since $T^r$ is
path connected. $H_n(T^0) = H_n(\mathrm{pt}) = 0$ for $n \geq 1$. The step: $T^{r+1} = S^1
\times T^r$, so by Theorem B
$$H_n(T^{r+1}) \cong H_n(T^r) \oplus H_{n-1}(T^r)
\cong \mathbb{Z}^{\binom{r}{n}} \oplus \mathbb{Z}^{\binom{r}{n-1}}
= \mathbb{Z}^{\binom{r+1}{n}}$$
by Pascal's rule $\binom{r}{n} + \binom{r}{n-1} = \binom{r+1}{n}$. Freeness and finiteness are
preserved by the splitting; vanishing for $n > r$ follows from $\binom{r}{n} = 0$ in that
range. $\square$

**The coordinate basis.** For each $n$-element subset $s = \{i_1 < \dots < i_n\}$ of
$\{1, \dots, r\}$ let $\iota_s \colon T^n \to T^r$ be the coordinate subtorus (coordinates $s$),
and let $\tau_s := \iota_{s*}[T^n] \in H_n(T^r)$, the pushforward of the top class.

**Proposition (the basis theorem).** *The classes $\tau_s$ are the basis of the free module
$H_n(T^r)$ matching the binomial basis of §4 under the isomorphism constructed there.*

*Proof.* Induction on $r$ following the splitting of §3. $r = 0$ and $n = 0$ are immediate. In
the step $T^{r+1} = S^1 \times T^r$: the subsets of $\{1, \dots, r+1\}$ of size $n$ split into
those not containing $1$ (giving $\tau_s = \mathrm{pr}_{2*}^{-1}\ldots$, i.e. the subtorus
classes lying in the $T^r$ factor — the first summand) and those containing $1$ (giving
$\tau_{\{1\} \cup s'} = [S^1] \times \tau_{s'}$ — the cross product with the positive
generator, which is the second summand inclusion by §3's splitting). So the family
$(\tau_s)$ maps to the union of the two inductively known bases, which is a basis. $\square$

**The top class.** $[T^r] := \tau_{\{1,\dots,r\}} \in H_r(T^r) \cong \mathbb{Z}$ is the
fundamental class; it equals the iterated cross product $[S^1] \times \dots \times [S^1]$ ($r$
factors), by the same induction.

## 5. The Pontryagin product (proof of Theorem C)

Let $G$ be a topological abelian group with addition $\mu \colon G \times G \to G$.

**Definition.** $a \cdot b := \mu_*(a \times b)$ for $a \in H_p(G)$, $b \in H_q(G)$; bilinear,
so $H_*(G)$ becomes a $\mathbb{Z}$-algebra once the axioms are checked.

**Unit.** The class $1 := [\mathrm{pt}_0] \in H_0(G)$ of the identity point is a unit:
$\mu \circ (\mathrm{const}_0, \mathrm{id}) = \mathrm{id}$, and the cross product is unital
($[\mathrm{pt}] \times b = b$ under $G \times \{\mathrm{pt}\} = G$), so $1 \cdot b = b$; the
other side is symmetric.

**Associativity.** $(a \cdot b) \cdot c = \mu_*(\mu_*(a \times b) \times c)$; write the
right-hand side via functoriality as $(\mu \circ (\mu \times \mathrm{id}))_*$ of the threefold
cross product $(a \times b) \times c$. The two bracketings of the threefold cross product differ
by the associator homeomorphism of $X \times (Y \times Z) \cong (X \times Y) \times Z$, under
which the cross product is coherent *up to a canonical chain homotopy* (the associator
homotopy: the two shuffle triangulations of $\Delta^p \times \Delta^q \times \Delta^r$ are
related by an explicit prism family — lane C records this as the associator coherence of the
cross product), and $\mu \circ (\mu \times \mathrm{id}) = \mu \circ (\mathrm{id} \times \mu)$
exactly (associativity of the group). Hence $(a \cdot b) \cdot c = a \cdot (b \cdot c)$.

**Graded commutativity.** For the swap homeomorphism $s \colon G \times G \to G \times G$,
commutativity of $\mu$ gives $\mu \circ s = \mu$, so
$$b \cdot a = \mu_*(b \times a) = \mu_*\, s_* (b \times a)
= (-1)^{pq}\, \mu_*(a \times b) = (-1)^{pq}\, a \cdot b,$$
the third equality being the swap law of the cross product (lane C; proved by an explicit
chain homotopy between the swapped shuffle triangulation and the sign-twisted one).

**Strict alternation on $H_1$.** For $a \in H_1(G)$, graded commutativity gives
$a \cdot a = - a \cdot a$, so $2(a \cdot a) = 0$; if $H_2(G)$ has no $2$-torsion then
$a \cdot a = 0$. The $n$-fold product $a_1 \cdot \ldots \cdot a_n$ is therefore an alternating
multilinear map $H_1(G)^n \to H_n(G)$ — swapping adjacent factors introduces a sign, and a
repeated factor kills the product — so it descends to
$$\wedge^n H_1(G) \longrightarrow H_n(G), \qquad a_1 \wedge \dots \wedge a_n \mapsto
a_1 \cdot \ldots \cdot a_n,$$
for every $n$ (the formalization carries $n = 2, 3$ today; the general-$n$ descent is the same
two properties — adjacent-swap antisymmetry and diagonal vanishing — quantified over the
adjacent-transposition generating set of $S_n$, and is this lane's new mathematics at general
$n$; see ledger row J3).

## 6. The torus is an exterior algebra on $H_1$ (Theorem A, second half)

Apply §5 to $G = T^r$ (all homology free, so no torsion hypothesis is needed).
$H_1(T^r) \cong \mathbb{Z}^r$ with basis the coordinate loops $\ell_i$ ($i = 1, \dots, r$).

**Theorem (Hatcher Cor. 3.28, homology form).** *The wedge map
$\wedge^n H_1(T^r) \to H_n(T^r)$ is an isomorphism for all $n$; explicitly,
$$\ell_{i_1} \wedge \dots \wedge \ell_{i_n} \longmapsto \pm\, \tau_{\{i_1, \dots, i_n\}},$$
the coordinate-subtorus top classes of §4 (the sign is the shuffle orientation of the chosen
ordering; with the conventions of §4 the sign is $+1$).*

*Proof.* The image claim is an induction on $r$ as in §4: the coordinate loop
$\ell_1 \in H_1(T^{r+1})$ is $[S^1]$ in the first factor, and the Pontryagin product of $[S^1]$
with a class of the $T^r$ factor is exactly the cross product $[S^1] \times \tau_{s'}$ (the
addition map on the first coordinate acts trivially on classes supported in the factors), so
the basis of §4 is the set of iterated products of coordinate loops. Hence the wedge map hits a
basis: it is surjective. Both sides are free of rank $\binom{r}{n}$ (§4; Theorem D's basis
count), and a surjective linear map between finite free modules of the same rank is an
isomorphism (the Orzech property: a surjective endomorphism of a noetherian module is
bijective, applied after choosing bases). $\square$

## 7. Exterior coordinates (proof of Theorem D)

Let $M = \mathbb{Z}^m$ with standard basis. The $n$-subsets $s \subseteq \{1, \dots, m\}$ are
indexed increasingly, $s = \{i_1 < \dots < i_n\}$; set $e_s := e_{i_1} \wedge \dots \wedge
e_{i_n} \in \wedge^n M$.

**Lemma (standard basis).** *The family $(e_s)$, $s$ ranging over the
$\binom{m}{n}$ $n$-subsets, is a basis of $\wedge^n M$.* (The $n$-fold tensor power has basis
$e_{i_1} \otimes \dots \otimes e_{i_n}$; the exterior power is its quotient by the alternating
relations, and the increasing-index images survive as a basis — this is Mathlib's
`exteriorPower` basis machinery; the lane records the repackaging into the subset-indexed
basis.)

**Theorem (minor formula).** *For $A \in \mathrm{M}_m(\mathbb{Z})$ and $n$-subsets $s, t$,*
$$\big(\wedge^n A\big)_{s,t} \;=\; \det\big(A_{s,t}\big),$$
*where $A_{s,t}$ is the $n \times n$ submatrix on rows $s$, columns $t$.*

*Proof.* Expand
$$\wedge^n A (e_t) = \big(A e_{j_1}\big) \wedge \dots \wedge \big(A e_{j_n}\big)
= \Big(\sum_i A_{i j_1} e_i\Big) \wedge \dots \wedge \Big(\sum_i A_{i j_n} e_i\Big)
= \sum_{i_1, \dots, i_n} \Big(\prod_k A_{i_k j_k}\Big)\, e_{i_1} \wedge \dots \wedge e_{i_n}.$$
Terms with a repeated index vanish (alternation); the remaining terms are permutations
$\sigma$ of each $s$, and $e_{i_{\sigma(1)}} \wedge \dots \wedge e_{i_{\sigma(n)}} =
\mathrm{sign}(\sigma)\, e_s$; collecting gives
$\sum_s \big(\sum_\sigma \mathrm{sign}(\sigma) \prod_k A_{i_{\sigma(k)} j_k}\big) e_s
= \sum_s \det(A_{s,t})\, e_s$. $\square$

Functoriality $\wedge^n(AB) = \wedge^n A \circ \wedge^n B$ (Mathlib's) applied to the minor
formula is the Cauchy–Binet formula $\det((AB)_{s,t}) = \sum_u \det(A_{s,u}) \det(B_{u,t})$;
the library file records it as a corollary.

**Coordinate matrices.** For the consumers the $n = 2, 3$ coordinate matrices of $\wedge^n A$
get explicit names ($A^{\wedge 2}$, an $\binom{m}{2} \times \binom{m}{2}$ matrix; $A^{\wedge 3}$
likewise) with the subset order fixed lexicographically; the content of "the monodromy acts on
$H_2(T^r)$ by the matrix of $2 \times 2$ minors" is exactly Theorem D read in these bases.

## 8. What stays CHARGED

The concrete rank-4 objects of the project — the lattice $\mathbb{Z}^4$, the quotient torus
$\mathbb{R}^4 / \mathbb{Z}^4$, the named monodromy matrices and their exterior squares/cubes
evaluated `by decide` — are project data and stay in `Hopf/FiniteCore.lean` (and
`Hopf/LCP/LocalModels.lean`). They become thin instantiations: each `by decide` matrix identity
is the generic minor-formula (Theorem D) evaluated at a concrete matrix. The homeomorphism
bridges $\mathbb{R}^4/\mathbb{Z}^4 \cong (S^1)^4$ and their rank-3 cousins
(`splitFlatTorusHomeomorph` etc.) are likewise adapters: the general theorem is about the
*product* torus $(S^1)^r$, and quotient-torus statements transport across the homeomorphism.

---

# Axes 2–3 — additive decomposition, in dependency order

$P = J_1 + \dots + J_8$, all FREE unless noted; dependency order is row order.

| # | Lemma (textbook §) | Inputs | Output | Current `Hopf/` home |
|---|---|---|---|---|
| J1 | Circle splitting, Theorem B (§3) | lane A: `circleProductHomologyEquiv` (SphereTopology 2191) and the two-arc MV; lane C: cross product | natural split exact sequence; section = cross with $[S^1]$ | CuspFilling 14015–15555 (`CirclePaths`, `arcSumCycle`, `positiveCircleCross`, `circleBoundary_positiveCircleCross`) |
| J2 | Product torus model (§2) | topology of `AddCircle` | $T^r := (S^1)^r$; $T^{r+1} \cong S^1 \times T^r$; $T^0 \cong$ pt; coordinate projections | CuspFilling 13745–13832 |
| J3 | Torus homology, Theorem A first half (§4) | J1, J2, Pascal's rule | `productTorusHomologyEquiv : H_n(T^r) ≃ₗ[ℤ] (Fin (r.choose n) → ℤ)`; free/finite/finrank/vanishing corollaries | CuspFilling 15853–15977 (headline at 15901) |
| J4 | Coordinate basis and top class (§4) | J3, subtorus maps | `coordinateTorusBasis`; `productTorusTopClass`; top class = iterated product | Specialization 3348–3682, 6199–6500 |
| J5 | Pontryagin product, Theorem C (§5) | lane C cross product + swap/associator coherences | `product`, `product11/12`, `tripleProduct`; unital, associative, graded-commutative; `product11_self` | Specialization 3142–3347, 3696–4200, 4286–6154 |
| J6 | Wedge maps (§5 end) — **new at general $n$** | J5 + torsion-freeness | $\wedge^n H_1(G) \to H_n(G)$; at $n = 2, 3$ exists as `homologyWedgeTwo/Three` | Specialization 4205–4285, 5971–6154 |
| J7 | Torus exterior theorem (§6) | J4, J6, Orzech | $\wedge^n H_1(T^r) \cong H_n(T^r)$ | rank-4 only today: Specialization 6948–7168; rank-3 re-run: BoundaryTopology 3232–3986 (to be re-routed to the general statement) |
| J8 | Exterior coordinates, Theorem D (§7) | Mathlib `exteriorPower` | `standardExteriorBasis`; the minor formula; Cauchy–Binet corollary; $\wedge^2, \wedge^3$ coordinate matrices at general $m$ | Specialization 6636–6882 (general $m$, $n$ already); FiniteCore 339–392 (CHARGED instantiations, stay) |

**Generalization work items (the lane's new mathematics).**
(G-J1) Replace `Lattice := Fin 4 → ℤ` by `Fin r → ℤ` (equivalently a free ℤ-module with a
chosen basis) throughout the Specialization blocks 6503–6552, 6911–7256: the statements become
rank-general; the proofs are identical with `r` for `4`.
(G-J2) The wedge isomorphism J7 at arbitrary rank $r$ and degree $n$ (today: rank 4, degrees
2, 3; a second copy at rank 3 in BoundaryTopology): the §6 proof is the general one; the only
genuinely new declaration is the $n$-fold wedge map of J6 and the count
$\mathrm{rank}\ \wedge^n \mathbb{Z}^r = \binom{r}{n}$ (J8's basis).
(G-J3) Move the cross-product swap/associator coherence suite (Specialization 3770–5970:
`formalEdgeSwapDefect/Homotopy`, `crossProductSwapHomotopy`, `formalAssociatorDefect/Homotopy`,
`crossProductAssociatorHomotopy`, `crossProductMixedSwapHomotopy`, and the homology-level
laws) into lane C's `CrossProduct.lean` — they are stated for general spaces and belong to the
cross-product API. This is a cross-lane row: the source lines are in J's range, the
destination file is created in C; recorded here and in C's ledger as a landing-time
coordination item. (Equally acceptable: land them in `Pontryagin.lean`; the owner decides at
landing. Default: `CrossProduct.lean`.)

---

# Axis 4 — placement

| File | Rows | Mathlib twin |
|---|---|---|
| `Lib/AlgebraicTopology/SingularHomology/CrossProduct.lean` (lane C file; J appends G-J3) | G-J3 | none existing; shape after `Mathlib/AlgebraicTopology/SingularHomology/Basic.lean` |
| `Lib/AlgebraicTopology/SingularHomology/Pontryagin.lean` | J5, J6 | none existing; shape after `Degree1.lean` (reference example) |
| `Lib/AlgebraicTopology/SingularHomology/Torus.lean` | J1–J4 | none existing; shape after the reference example |
| `Lib/AlgebraicTopology/SingularHomology/TorusExterior.lean` | J7 | none existing |
| `Lib/LinearAlgebra/ExteriorPower/MinorCoordinates.lean` | J8 | `Mathlib/LinearAlgebra/ExteriorPower/Basic.lean` (the pinned Mathlib's exterior power file; the new file is its "coordinates" companion) |

Build order: (C's `CrossProduct`) → `Pontryagin` → `Torus` → `TorusExterior`;
`MinorCoordinates` is independent of the homology files (imports Mathlib only).

Consumers and their re-routing: `Hopf.LCP.IntegralHomology` (Wang-sequence machinery, cusp
coinvariants, `coordinateTopEquiv`, the cup-product interface
`PeriodTorusCohomologyCup.coordinateTorusH2Coordinates_basis_pair`),
`Hopf.LCP.BoundaryTopology` (rank-3 wedge re-run — deleted in favor of the general J7 —,
monodromy actions, `singularH2/H3Equiv`), `Hopf.LCP.Specialization` (the rank-4 adapters
stay and become thin), `Hopf.FiniteCore` (the `by decide` instantiations stay),
`Hopf.Recognition` (only cross-product plumbing through lane C).

---

# Axis 5 — typed ledger

Headline rows; seams on lanes A and C named explicitly. The aggregate interface probes
(`J_InterfaceCheck.lean` / consumer) run after lanes A and C land; commands in §12.

**Row J-headline (the axiom probe).** Current:
`PeriodTorusHigherHomology.productTorusHomologyEquiv : (r n : ℕ) →
SingularMayerVietoris.SingularHomology (ProductTorus r) n ≃ₗ[ℤ] binomialModule r n`
(CuspFilling 15901), by structural recursion on `(r, n)`. Target:
`AlgebraicTopology.SingularHomology.productTorusHomologyEquiv (r n : ℕ) :
SingularHomology (ProductTorus r) n ≃ₗ[ℤ] (Fin (r.choose n) → ℤ)` — the codomain
`binomialModule r n` becomes the plain function space (its only role is the Pascal recursion;
the `binomialModule` API — `binomialModuleSuccEquiv` etc. — is the proof of Pascal's rule for
`Fin (r.choose n) → ℤ` and moves along as private/API material of `Torus.lean`).
Seams: `SingularMayerVietoris.SingularHomology` (A), `circleProductHomologyEquiv` (A),
`connectedHomologyZeroEquiv`, `totallyDisconnected_homology_subsingleton` (A).

**Row J-pontryagin.** Current: `PeriodTorusHigherHomologyPontryagin.product (G : Type)
[TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G] (n : ℕ) : H₁ G →ₗ[ℤ] Hₙ G
→ₗ[ℤ] H_{n+1} G` (Specialization 3189), with `product11_skew`, `product11_self` (needs
`Module.IsTorsionFree ℤ (H₂ G)`), `tripleProduct`, the naturality suite, and the two wedge
maps. Target: `SingularHomology.Pontryagin.product (G : Type*) [TopologicalSpace G]
[AddCommGroup G] [IsTopologicalAddGroup G] : H_p G →ₗ[ℤ] H_q G →ₗ[ℤ] H_{p+q} G` — **note the
generalization from $(1, n)$ to $(p, q)$**: the code's `product` is pinned at left degree 1
because it is built on `crossProductHomology` at $(1, n)$; the graded-commutativity proof needs
the general swap law anyway, so the general $(p, q)$ product is the natural statement and costs
the general cross product (lane C's file records the cross product at general $(p, q)$ — the
current `crossProductEdge`/`crossProductTriangle` are the $p = 1, 2$ cases; generalizing the
cross product itself to all $p$ is recorded in C's ledger as the natural twin-shaped form).
Decision recorded: J's Pontryagin file states the product at general $(p, q)$ *if* C's general
cross product has landed; otherwise at $(1, n)$ as today, with a follow-up item. Flagged for
the owner in §12.

**Row J-wedge.** Current: `homologyWedgeTwo`/`homologyWedgeThree` (4223/6064),
`latticeWedgeTwo`/`latticeWedgeThree` (4242/6083) with the rank-4 `Lattice` pin, the
`surjective_of_coordinateTorusClassAlong_mem_range` family (6554–6625, general-rank over any
`G ≃ₜ ProductTorus r`), and the rank-4 equivs `coordinateTorusWedgeTwoEquiv/ThreeEquiv`
(7068/7073), `coordinateTorusH2/H3ExteriorEquiv` (7078/7083).
Target (G-J2): `SingularHomology.Pontryagin.exteriorMap : (⋀[ℤ]^n (H₁ G)) →ₗ[ℤ] Hₙ G` at
general `n` (torsion-free hypothesis as needed), and
`SingularHomology.productTorusExteriorEquiv (r n : ℕ) : (⋀[ℤ]^n (H₁ (ProductTorus r)))
≃ₗ[ℤ] SingularHomology (ProductTorus r) n`.
**New mathematics**: the general-$n$ descent (J6). The rank-3 re-run in BoundaryTopology is
deleted and re-routed.

**Row J-exterior.** Current: `PeriodTorusHigherHomologyExterior.standardExteriorBasis (m n : ℕ)
: Module.Basis (Set.powersetCard (Fin m) n) ℤ (⋀[ℤ]^n (Fin m → ℤ))` (6636) and
`standardExterior_map_coefficient` (6640, the minor formula). Target:
`LinearAlgebra.ExteriorPower.MinorCoordinates.standardBasis` and
`…_map_coefficient` verbatim (already fully general). Pure move. Q4 recorded: an equivalent
formalization of the minor formula exists outside this tree; moved as-is per decision Q4.

**Row J-charged.** FiniteCore 339–392 (`squareA₁ …`, `cubeM₀_eq` etc.) stays in
`Hopf/FiniteCore.lean`; after J lands its proofs become one-line instantiations of the minor
formula. The generic `LocalSystemMatrices.{pairIndices, exteriorSquare, tripleIndices,
exteriorCube}` (FiniteCore 327–337) is outside the lane's named range but is generic
minor-matrix API: flagged for the owner — recommend moving it into `MinorCoordinates.lean`
with the lane (it is the lexicographic-subset coordinate convention of Theorem D).

**Local instances.** The `attribute [local instance]
PeriodTorusHigherHomology.integerLinearMapModule … integerTensorModule in` wrappers pervade the
moved blocks (dozens of sites in Specialization, plus consumers). Disposition as in lane C
(boundary C1): reproduce in the baseline, then attempt removal in a separate refactor commit;
the two `@[instance_reducible]` defs themselves land in lane C's `CrossProduct.lean`.

---

# Open items, seams, probes

1. **Seams.** Lane A: the whole singular-homology API plus the $S^1 \times Y$ splitting
   (`circleProductHomologyEquiv`, SphereTopology 2191, inside A's S¹×X block) and
   `connectedHomologyZeroEquiv`, `totallyDisconnected_homology_subsingleton`,
   `homeomorphHomologyEquiv`, `singularHomologyMap_*`. Lane C: the cross product file
   (`crossProductHomology`, boundary laws, swap and associator coherences per G-J3). Probe
   commands (after A and C land): `lake env lean
   Lib/AlgebraicTopology/SingularHomology/J_InterfaceCheck.lean`, likewise the consumer probe;
   receipt at `Lib/docs/J-INTERFACE_RECEIPT.md`.
2. **General-$(p,q)$ Pontryagin product** (row J-pontryagin): depends on whether C's cross
   product lands at general $(p,q)$; default is yes, fallback is the current $(1,n)$ shape.
   Owner decision at landing.
3. **Q4 note** (minor formula exists outside the tree): moved as-is; de-duplication is the
   owner's call.
4. **`PeriodTorusHigherHomology.rightTranslation`** is defined in `Hopf/LCP/BoundaryTopology.lean`
   (line 17021), far from the torus API: at landing, check whether it belongs to `Torus.lean`;
   recorded here because it sits outside the lane's named ranges.
5. **Duplications to delete at landing**: `formalMap_comp` = `formalMap_comp_apply`
   (Specialization 3770 vs 4450, identical statements); `productTorusHomologyEquiv_succ_pair`
   (Specialization 6438) is an exact alias of CuspFilling's `productTorusHomologyEquiv_succ_apply`.
6. **Bib keys.** `hatcher02` exists in the pinned Mathlib bib. Hirsch/Milnor keys are not needed
   for this lane.
7. **Review.** Stage-2 independent review of §§1–8: scheduled; report in `~/s6-notes/`.
