# Lane J — textbook, decomposition, placement, and typed ledger

**Implementation update after bbf1dd2:** see the public-module conversion addendum in `Lib/reports/RECEIPTS.md` for the verified current move scope and remaining work. Legacy-provider claims and source coordinates below describe the earlier ledger/probe snapshots where superseded by that addendum; they are not current blockers for the converted providers.

**Homology of tori, the Pontryagin product, and exterior-power coordinates** (Hatcher,
*Algebraic Topology*: Example 2.48 adjacent; §3.B Künneth computations; Example 3.16 for the
exterior-algebra form; §3.C Exercise 11 for the Pontryagin form), generalized from the
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

**Theorem A (homology of the torus; Hatcher §3.B and Example 3.16, homology form).**
Let $T^r = (S^1)^r$ be the product $r$-torus. Then $H_n(T^r;\mathbb{Z})$ is free abelian of rank
$\binom{r}{n}$, and the Pontryagin (exterior) map
$$\wedge^n H_1(T^r;\mathbb{Z}) \longrightarrow H_n(T^r;\mathbb{Z}), \qquad
a_1 \wedge \dots \wedge a_n \longmapsto a_1 \cdot \ldots \cdot a_n,$$
is an isomorphism for every $n \geq 0$.

**Theorem B (the circle splitting; the trivial Wang sequence).**
For every space $Y$ and every $n$ there is a natural short exact sequence, split by the cross
product with the positive generator $[S^1] \in H_1(S^1)$,
$$0 \longrightarrow H_{n+1}(Y) \xrightarrow{\;\mathrm{incl}_{x_0*}\;}
H_{n+1}(S^1 \times Y) \xrightarrow{\;\partial\;} H_n(Y) \longrightarrow 0,$$
where $\mathrm{incl}_{x_0} \colon Y \to S^1 \times Y$, $y \mapsto (x_0, y)$ is a slice
inclusion (a section of the projection $\mathrm{pr}_2$). Then
$H_{n+1}(S^1 \times Y) \cong H_{n+1}(Y) \oplus H_n(Y)$, with the second summand embedded by
$b \mapsto [S^1] \times b$. (This is the Wang sequence of the trivial mapping torus — the
fibration $Y \to S^1 \times Y \to S^1$ with identity monodromy, i.e. Hatcher Ex. 2.48 with
$f = \mathrm{id}$, where $1 - f_* = 0$; equivalently the Gysin sequence of the trivial circle
bundle, $e = 0$.)

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
Mathlib's (the quotient of $M^{\otimes n}$ by the alternating relations; universal alternating
map $\iota_n \colon M^n \to \wedge^n M$).

## 3. The circle splitting (proof of Theorem B)

Cover $S^1 = U \cup V$ by two open arcs with intersection two short arcs around the two
"poles", so $U, V \simeq *$, $U \cap V \simeq S^0$, all pulled back to the cover
$\{U \times Y, V \times Y\}$ of $S^1 \times Y$. Mayer–Vietoris for this cover gives
$$\dots \to H_{n+1}(U \times Y) \oplus H_{n+1}(V \times Y) \;\to\;
H_{n+1}(S^1 \times Y) \xrightarrow{\partial} H_n((U \cap V) \times Y) \to
H_n(U \times Y) \oplus H_n(V \times Y) \to \dots$$
and the identifications $H_k(U \times Y) \oplus H_k(V \times Y) \cong H_k(Y)^2$,
$H_k(U \cap V \times Y) \cong H_k(Y)^2$ turn the connecting homomorphism and the restriction
map into
$$\partial \colon H_{n+1}(S^1 \times Y) \to H_n(Y)^2, \qquad
\mathrm{res} \colon H_n(Y)^2 \to H_n(Y)^2,\ (u, v) \mapsto (u + v,\ u + v)$$
(the restrictions of a class on $U \times Y$ and $V \times Y$ to each intersection arc agree,
both being the pullback along the inclusion; Hatcher's MV convention puts a minus on the
$V$-summand, which conjugates the displayed map by the automorphism $(x, y) \mapsto (x, -y)$
of $H_n(Y)^2$ — kernel and cokernel below are unchanged). The kernel of $\mathrm{res}$ is
$\{(b, -b)\} \cong H_n(Y)$, and its image is the diagonal $\{(w, w)\}$, so
$\mathrm{coker}\, \mathrm{res} \cong H_n(Y)$ via $(x, y) \mapsto x - y$ (in every degree).
A long exact sequence $\dots \to A \to B \to C \to D \to E \to \dots$ always breaks into
$0 \to \mathrm{coker} \to C \to \ker \to 0$; here that gives
$$0 \longrightarrow \mathrm{coker}\, \mathrm{res}_{n+1} \cong H_{n+1}(Y)
\longrightarrow H_{n+1}(S^1 \times Y)
\longrightarrow \ker \mathrm{res}_n \cong H_n(Y) \longrightarrow 0,$$
the short exact sequence of Theorem B.

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
those not containing $1$ (giving $\tau_s = \mathrm{incl}_{0*}(\tau^{(r)}_s)$, the pushforward
of the inductively known class along the slice inclusion
$\mathrm{incl}_0 \colon T^r \hookrightarrow S^1 \times T^r$ — the first-summand inclusion, a
section of $\mathrm{pr}_{2*}$) and those containing $1$ (giving
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
$n$; see ledger row J6).

## 6. The torus is an exterior algebra on $H_1$ (Theorem A, second half)

Apply §5 to $G = T^r$ (all homology free, so no torsion hypothesis is needed).
$H_1(T^r) \cong \mathbb{Z}^r$ with basis the coordinate loops $\ell_i$ ($i = 1, \dots, r$).

**Theorem (exterior form of Theorem A; Hatcher Example 3.16 and §3.C Exercise 11).** *The wedge map
$\wedge^n H_1(T^r) \to H_n(T^r)$ is an isomorphism for all $n$; explicitly,
$$\ell_{i_1} \wedge \dots \wedge \ell_{i_n} \longmapsto \pm\, \tau_{\{i_1, \dots, i_n\}},$$
the coordinate-subtorus top classes of §4 (the sign is the shuffle orientation of the chosen
ordering; with the conventions of §4 the sign is $+1$).*

*Proof.* The image claim is an induction on $r$ as in §4: the coordinate loop
$\ell_1 \in H_1(T^{r+1})$ is $[S^1]$ in the first factor, and the Pontryagin product of $[S^1]$
with a class of the $T^r$ factor is exactly the cross product $[S^1] \times \tau_{s'}$:
for the slice inclusions $\mathrm{incl}_1 \colon S^1 \to S^1 \times T^r$ and
$\mathrm{incl}_2 \colon T^r \to S^1 \times T^r$ one has
$\mu \circ (\mathrm{incl}_1 \times \mathrm{incl}_2) = \mathrm{id}$ on the nose, hence
$\mu_*(\mathrm{incl}_{1*} a \times \mathrm{incl}_{2*} b)
= (\mu \circ (\mathrm{incl}_1 \times \mathrm{incl}_2))_*(a \times b) = a \times b$.
So the basis of §4 is the set of iterated products of coordinate loops. Hence the wedge map hits a
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

$P = J_1 + \dots + J_8$, all FREE unless noted. Dependency order is **not** row order:
J8's basis/rank count (`standardExteriorBasis`, finrank of $\wedge^n \mathbb{Z}^m$) feeds
J7's Orzech step, so the true order is J2 → J1 → J3 → J4 → J5 → J6 → J8 → J7.

| # | Lemma (textbook §) | Inputs | Output | Historical pre-A/C `Hopf/` range (current locations are in Axis 5) |
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
(G-J2) The wedge isomorphism J7 at arbitrary rank $r$ (today: rank 4, degrees
2, 3; a second copy at rank 3 in BoundaryTopology): the §6 proof is the general one.
**Narrowed 2026-09-12 (axis-5 review):** the in-scope part is rank-$r$ at degrees 2
and 3 — it needs only the landed `(1,1)`/`(1,1,1)` coherence laws plus J8's rank
count. The general-degree-$n$ descent additionally needs a general-`(p,q)` cross
product and its coherence laws, which do not exist at head; that part is deferred to
the J-E boundary in the ledger with its missing inputs enumerated.
(G-J3) **Settled 2026-09-12: this item is GLM's, not J's.** The cross-product
swap/associator coherence suite (110 declarations; exact exclusion manifest in the
Axis-5 section below — the earlier "42" counted only the named families) at
Specialization 3771–5987:
`formalEdgeSwapDefect/Homotopy`, `crossProductSwapHomotopy`,
`formalAssociatorDefect/Homotopy`, `crossProductAssociatorHomotopy`,
`crossProductMixedSwapHomotopy`, and the homology-level laws `crossProductHomology_swap`,
`crossProductHomology_pushforward_anticommute`, `crossProductHomology_associative`)
are stated for general spaces and belong to the
cross-product API; they move into `Lib/AlgebraicTopology/SingularHomology/CrossProduct.lean`
by GLM. J imports them from `CrossProduct.lean` when they land and keeps them under
`Hopf/` names until then.

---

# Axis 4 — placement

| File | Rows | Mathlib twin |
|---|---|---|
| `Lib/AlgebraicTopology/SingularHomology/CrossProduct.lean` (**GLM-owned destination for G-J3; J does not append**) | G-J3 | none existing; shape after `Mathlib/AlgebraicTopology/SingularHomology/Basic.lean` |
| `Lib/AlgebraicTopology/SingularHomology/Pontryagin.lean` | J5, J6 | none existing; shape after `Degree1.lean` (reference example) |
| `Lib/AlgebraicTopology/SingularHomology/Torus.lean` | J1–J4 | none existing; shape after the reference example |
| `Lib/AlgebraicTopology/SingularHomology/TorusExterior.lean` | J7 | none existing |
| `Lib/LinearAlgebra/ExteriorPower/MinorCoordinates.lean` | J8 | `Mathlib/LinearAlgebra/ExteriorPower/Basic.lean` (the pinned Mathlib's exterior power file; the new file is its "coordinates" companion) |

Dependency schedule (candidate packets, not permission to implement): J-A before J-D;
J-B1 before J-B2a before J-B2b; J-C1 before J-C2 before J-C3; J-C3 additionally
requires J-B2a; J-D requires J-A, J-B2b and J-C3. J-C1 waits on the public module
seam M-C, J-C2 on S-cross, J-B2a on S-path/S-nat/S-cross, and J-C3 on G-J3.
`Torus.lean` never imports `Pontryagin.lean`; product-valued top-class lemmas belong
to J-C3 in Pontryagin, which may import Torus. `MinorCoordinates` is Mathlib-only.
Every packet still needs its exact aggregate provider/consumer receipt before GO.

Consumers and their re-routing: `Hopf.LCP.IntegralHomology` (Wang-sequence machinery, cusp
coinvariants, `coordinateTopEquiv`, the cup-product interface
`PeriodTorusCohomologyCup.coordinateTorusH2Coordinates_basis_pair`),
`Hopf.LCP.BoundaryTopology` (rank-3 wedge re-run — deleted in favor of the general J7 —,
monodromy actions, `singularH2/H3Equiv`), `Hopf.LCP.Specialization` (the rank-4 adapters
stay and become thin), `Hopf.FiniteCore` (the `by decide` instantiations stay),
`Hopf.Recognition` (only cross-product plumbing through lane C).

---

# Axis 5 — typed ledger

**Review-3 status (15bd5f7 + uncommitted reviewer repairs): J-A GO only.**
J-A's 15-node interface, concrete representation construction and separate importing
consumer have been checked; its reviewed ledger hash and commands are in the
review-3 receipt. This is not a GO for the whole lane. J-B..J-D are explicitly gated
by proof closures and public-module seams below; J-E remains deferred. All newly
added or changed signature shapes were probed before recording, with provisional
inputs identified in the receipt. This status supersedes earlier claims below that
the second-pass repair was complete. Muse must review the uncommitted amendments;
any further change to the J-A packet invalidates its reviewed hash.

**Revision note (2026-09-12, second pass).** The first-pass ledger and its probes were
independently reviewed by seat `devin-axis5-j` → **NO-GO** (nine findings; the review
text is held in `~/s6-notes/J-review-devin-axis5-j.md`, to be committed as
`Lib/docs/J-review.md` alongside the Stage-2 review). This revision:

* fixes both proposed signatures to universe `Type` — `SingularMayerVietoris.SingularHomology`
  takes `Y : Type` (`MayerVietoris.lean:853`) and `crossProductHomology` takes
  `(X Y : Type)` (`CrossProduct.lean:1689`), so `Type*` does not elaborate;
* records the full namespace/elaboration context (below);
* enumerates every in-scope declaration with its exact current signature, source
  location, and disposition — public outputs get exact target signatures, internal
  movers get a name+line manifest (verbatim signatures, unchanged);
* re-orders J8 before J7 and splits each file's boundary into independently green
  sub-boundaries with named unlanded seams;
* narrows the general-`n` wedge (former G-J2 degree-`n` part) into deferred boundary
  J-E with its missing inputs enumerated — the general-degree swap/associativity the
  descent needs do not exist at head (the landed coherence laws are at degrees
  `(1,1)`/`(1,1,1)` only).

## Context and elaboration conventions

* All declarations below live inside `namespace Mathoverflow1973` — the standing Lib
  convention (`CrossProduct.lean:89`; the rename to `AlgebraicTopology.SingularHomology.*`
  is a separate scheduled commit). The ledger records **landing names** (current names
  verbatim); post-rename names are the same identifiers under
  `AlgebraicTopology.SingularHomology.<file-prefix>`.
* `⋀[ℤ]^n M` is pinned-Mathlib notation for `ExteriorAlgebra.exteriorPower ℤ n M`
  (`Mathlib/LinearAlgebra/ExteriorAlgebra/Basic.lean:83`); the bare identifier needs
  `open ExteriorAlgebra`. The root namespace `exteriorPower`
  (`Mathlib/LinearAlgebra/ExteriorPower/Basic.lean:47`) supplies `exteriorPower.ιMulti`
  (:56), `exteriorPower.alternatingMapLinearEquiv` (:212), `exteriorPower.map` (:260).
* `attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
  PeriodTorusHigherHomology.integerTensorModule` must be reproduced at the source's
  cross-product/Pontryagin wrapper sites when comparing nested linear-map types — the two
  `@[instance_reducible]` definitions (`CrossProduct.lean:94`,`:101`) differ from the
  ambient `AddCommGroup.toIntModule`, and signatures written in the wrong instance
  context do not elaborate identically. The definitions themselves land in lane C's
  `CrossProduct.lean` (already present); the `attribute [local instance] … in`
  wrappers are reproduced per-site in the moved code.
* Universes: all spaces are `Type` (universe 0). No `Type*` generalization is promised
  at this boundary.
* `Lattice`/`LatticeMatrix`/`PeriodDomain` are CHARGED rank-4 abbreviations
  (`Hopf/FiniteCore.lean:215`,`:218`; `Hopf/LCP/LocalModels.lean:250`) — they are **not**
  Lib-importable. Every generalized target below replaces `Fin 4` by `Fin r`, or drops
  the lattice pin entirely (`c : M →ₗ[ℤ] SH G 1` for arbitrary `M`).
* `SH X n` in prose is `SingularMayerVietoris.SingularHomology X n`; signatures below
  spell the full name.
* Inside `namespace Mathoverflow1973`, use `open SingularHomology`,
  `open scoped Matrix BigOperators TensorProduct` and `noncomputable section`. The unqualified circle, point-class,
  homology-equivalence and composition APIs in the ledger resolve in `SingularHomology`,
  not via the exports in `Hopf/LibShims.lean`. Inside each declaration's dotted namespace,
  its own earlier landing names are in scope; cross-namespace references must be qualified.
* The degree-one target API is `AlgebraicTopology.SingularH1`,
  `AlgebraicTopology.SingularH1.map` and `AlgebraicTopology.Hurewicz.loopHomologyClass`
  from `Lib.AlgebraicTopology.Hurewicz.Degree1` (106, 334, 726). The first two agree
  definitionally with `SingularMayerVietoris.SingularHomology X 1` and
  `SingularMayerVietoris.singularHomologyMap f 1` (review-3 module probe, `rfl`).
  `SingularChains.singularComplex` is the real chain API. No `Hopf.LibShims` import
  or compatibility alias is permitted in a production packet.
* **Module seam M-C (NOT GO):** `CrossProduct.lean:6–9` and `PathClass.lean:6–18`
  are legacy files at `15bd5f7`, despite living under `Lib/`. A `module` probe rejects
  importing CrossProduct. Its instance/plumbing/coherence API must acquire a public
  module provider before J-C or J-B2 can be certified. Review-3 provisional module
  probes reproduce the two instance definitions in an isolated namespace and use
  signature-only declarations for unlanded inputs; this does not certify M-C.
* Replacing old loop-class aliases by the Degree1 API is **not** a claim that the old
  and new loop-class proof terms are definitionally equal. The unchanged old proof
  closures through legacy PathClass must be re-aligned to the public Degree1 API;
  this is a named J-B2 representation seam, not work silently delegated to Axis 6.

## Boundary J-A — `Lib/LinearAlgebra/ExteriorPower/MinorCoordinates.lean`

```text
commit_boundary   J-A — independently green; imports Mathlib only; lands first.
imports           Mathlib (module file: `module` + `public import`)
visibility        `module`; `public section`; `noncomputable section`;
                  `namespace Mathoverflow1973.PeriodTorusHigherHomologyExterior`
source            Lib/docs/J.md §7, Theorem D and its standard-basis lemma;
                  Specialization.lean 6637–6882 for the existing coordinate proof
destination       Lib/LinearAlgebra/ExteriorPower/MinorCoordinates.lean
focused_check     `lake build Lib.LinearAlgebra.ExteriorPower.MinorCoordinates`
return_seam       Axis 3 if a promised output turns out not to be rank-general
```

Probed 2026 (production `module`/`public` file, Mathlib-only imports): every
signature below elaborates; `exteriorPower_finrank_choose` and
`powersetCardFinEquiv_lt_iff` are already *proved* in the probe. Receipt:
`Lib/docs/J-INTERFACE_RECEIPT.md` §J-A.

Two corrections vs. the second-pass ledger (devin-axis5-j re-review findings 1–2):
the reindex direction is now `(…).reindex (powersetCardFinEquiv m n)` — `reindex`
takes `ι ≃ ι'` where the basis is indexed by `ι` — and the coordinate map uses
`.equivFun` (codomain `Fin _ → ℤ`), not `.repr` (codomain `Fin _ →₀ ℤ`).

### J-A ChallengeNode manifest

For each row, `id = J-A.<output>`, `class = FREE`, `signature` is the exact named
Lean declaration below, and `destination` is that public name in the namespace/file
above. `imports`, `visibility`, `commit_boundary`, `focused_check` and `return_seam`
are inherited from the J-A block. The source text is §7 of this file, whose hash is
covered by the complete ledger SHA-256 in the review-3 receipt. `representation` is
the concrete construction/equation below, independently elaborated in J3A.lean;
rows marked theorem shell require only the substantive proof, not a redesigned type.
All 15 names were checked by a separate importing consumer. Order is table order.

| Output | Exact source sentence | Dependencies / representation | Exact consumer |
|---|---|---|---|
| SortedSubset | §7: subsets indexed increasingly, with fixed coordinate order | Lex; Set.powersetCard | sortedSubsetLinearOrder |
| sortedSubsetFintype | §7: finite n-subsets | SortedSubset; Fintype of powersetCard via inferInstanceAs | sortedSubset_card |
| sortedSubsetLinearOrder | §7: increasing indices and lexicographic coordinate convention | SortedSubset; LinearOrder.lift'; Finset.sort_toFinset; Subtype.ext | powersetCardFinEquiv |
| sortedSubset_card | §7: binomial number of basis subsets | sortedSubsetFintype; Fintype.card_congr toLex.symm; Set.powersetCard.card | powersetCardFinEquiv |
| powersetCardFinEquiv | §7: fixed subset coordinate indices | preceding three outputs; toLex; Equiv.subtypeUnivEquiv; Finset.orderIsoOfFin | standardExteriorBasisFin |
| powersetCardFinEquiv_lt_iff | §7: coordinate matrices use lexicographic subset order | powersetCardFinEquiv; sortedSubsetLinearOrder; OrderIso.lt_iff_lt | Hopf-side rank-four compatibility adapter (not a J-A output) |
| standardExteriorBasis | §7 standard-basis lemma | Pi.basisFun; Module.Basis.exteriorPower | standardExterior_map_coefficient; standardExteriorBasisFin |
| standardExterior_map_coefficient | §7 minor formula | standardExteriorBasis; exteriorPower.map; exteriorPower.basis_repr_apply; exteriorPower.ιMultiDual_apply_ιMulti; Matrix.det_transpose (theorem shell; source Specialization 6641) | rank-four adapter; exteriorPowerMap_toMatrix proof pattern |
| standardExteriorBasisFin | §7 fixed coordinate basis | standardExteriorBasis; powersetCardFinEquiv; Module.Basis.reindex in forward direction | standardExteriorCoordinates; exteriorPowerMap_toMatrix |
| standardExteriorCoordinates | §7 coordinate matrices | standardExteriorBasisFin.equivFun | J-D coordinateTorusH2Coordinates/coordinateTorusH3Coordinates |
| exteriorPower_finrank_choose | §7 binomial rank count | exteriorPower.finrank_eq; Module.finrank_fintype_fun_eq_card; Fintype.card_fin | J-D coordinateTorusWedgeTwo_bijective/coordinateTorusWedgeThree_bijective |
| exteriorMinorMatrix | §7 entrywise minor formula, rectangular instance | powersetCardFinEquiv; Set.powersetCard.ofFinEmbEquiv; Matrix.submatrix; Matrix.det | exteriorPowerMap_toMatrix; cauchyBinet_minors |
| exteriorPowerMap | §7 induced exterior-power map | exteriorPower.map; Matrix.mulVecLin | exteriorPowerMap_toMatrix |
| exteriorPowerMap_toMatrix | §7 minor formula for induced coordinates | preceding basis/map/matrix outputs; LinearMap.toMatrix_apply; exteriorPower.basis_apply/map_comp_ιMulti_family/basis_repr_apply/ιMultiDual_apply_ιMulti; Matrix.det_transpose (theorem shell) | cauchyBinet_minors; J-D coordinate matrix laws |
| cauchyBinet_minors | §7 last paragraph, functoriality gives Cauchy–Binet | exteriorPowerMap_toMatrix; Matrix.mulVecLin_mul; exteriorPower.map_comp; LinearMap.toMatrix_comp (theorem shell) | external rectangular minor-matrix API; downstream coordinate calculations |

J-A has no dependency on J-B..J-E, Hopf, or the legacy CrossProduct provider.
The rank-four compatibility adapters remain separate charged consumers; their old
signatures and coordinates are preserved until the order-theoretic replacement is proved.

### The enumeration (reviewer finding 1)

`Set.powersetCard (Fin m) n` already carries the *subset* `PartialOrder`, so a
lex order cannot be added as an instance on it directly; the lex order lives on
a `Lex` synonym (`Lex α` carries no order passthrough instance):

```lean
public abbrev SortedSubset (m n : ℕ) := Lex (Set.powersetCard (Fin m) n)

public instance sortedSubsetFintype (m n : ℕ) : Fintype (SortedSubset m n) -- inferInstanceAs
public instance sortedSubsetLinearOrder (m n : ℕ) : LinearOrder (SortedSubset m n)
  -- LinearOrder.lift' (fun s ↦ (ofLex s).1.sort (· ≤ ·)) inj
  -- inj: apply ofLex.injective; apply Subtype.ext;
  -- simpa using congrArg List.toFinset h (simp uses Finset.sort_toFinset).

public theorem sortedSubset_card (m n : ℕ) :
    Fintype.card (SortedSubset m n) = m.choose n
  -- first Fintype.card_congr toLex.symm removes the Lex synonym;
  -- then Set.powersetCard.card + Nat.card_eq_fintype_card + Fintype.card_fin.

/-- The lexicographic enumeration of `n`-subsets of `Fin m`. -/
public def powersetCardFinEquiv (m n : ℕ) :
    Set.powersetCard (Fin m) n ≃ Fin (m.choose n)
  -- body (PROBED): toLex.trans ((Equiv.subtypeUnivEquiv mem_univ).symm.trans
  --   ((Finset.orderIsoOfFin univ sortedSubset_card).symm.toEquiv))

/-- The enumeration is pinned by its characterization — `e` is the order-iso
for lex-on-sorted-tuples: -/
public theorem powersetCardFinEquiv_lt_iff {m n : ℕ}
    (s t : Set.powersetCard (Fin m) n) :
    powersetCardFinEquiv m n s < powersetCardFinEquiv m n t ↔
      List.Lex (· < ·) ((s : Finset (Fin m)).sort (· ≤ ·))
        ((t : Finset (Fin m)).sort (· ≤ ·))
```

**Rank-4 compatibility** (reviewer demand — the enumeration must agree with
`pairSubsetEquiv`/`tripleSubsetEquiv`, which stay Hopf-side as charged adapters):
the compatibility equation

```lean
∀ i : Fin 6, powersetCardFinEquiv 4 2
  (PeriodTorusHigherHomologyExterior.pairSubset i) = i
```

is *not* stated in `MinorCoordinates.lean` (it references the charged
`pairSubset`).  It is proved in the Hopf adapter from
`powersetCardFinEquiv_lt_iff` + `pairSubset_ordered` (the sorted tuple of
`pairSubset i` is `pairIndices i`, and `pairIndices` enumerates in lex order —
a `decide`-able check on `Fin 6` literal vectors) + the fact that a strictly
monotone map `Fin k → Fin k` is the identity (`StrictMono` on `Fin` is
uniqueness-forced).  Note: `powersetCardFinEquiv` itself does **not** reduce
under kernel `decide` (probed — `orderIsoOfFin`'s inverse threads through
`List.Sorted.getIso`/`Equiv` machinery that stalls evaluation), so the compat
route is order-theoretic, not computational.

### Basis, coordinates, rank

```lean
-- verbatim move (Specialization 6637):
public noncomputable def standardExteriorBasis (m n : ℕ) :
    Module.Basis (Set.powersetCard (Fin m) n) ℤ (⋀[ℤ]^n (Fin m → ℤ))
  -- body: (Pi.basisFun ℤ (Fin m)).exteriorPower n   (Mathlib
  --   `Module.Basis.exteriorPower`, ExteriorPower/Basis.lean)

-- verbatim move (Specialization 6641):
public theorem standardExterior_map_coefficient (m n : ℕ)
    (A : Matrix (Fin m) (Fin m) ℤ) (s t : Set.powersetCard (Fin m) n) :
    (standardExteriorBasis m n).repr
        (exteriorPower.map n A.mulVecLin (standardExteriorBasis m n t)) s =
      (A.submatrix (Set.powersetCard.ofFinEmbEquiv.symm s)
          (Set.powersetCard.ofFinEmbEquiv.symm t)).det

-- NEW — generalized `squareBasis`/`cubeBasis` (6742/6745).  Direction matches
-- the source `(latticeExteriorBasis 2).reindex pairSubsetEquiv.symm` where
-- `pairSubsetEquiv.symm : powersetCard → Fin 6`; here the equiv already runs
-- `powersetCard → Fin (m.choose n)`, so no `.symm`:
public noncomputable def standardExteriorBasisFin (m n : ℕ) :
    Module.Basis (Fin (m.choose n)) ℤ (⋀[ℤ]^n (Fin m → ℤ))
  -- body: (standardExteriorBasis m n).reindex (powersetCardFinEquiv m n)

-- NEW — generalized `squareCoordinates`/`cubeCoordinates` (6764/6767);
-- `.equivFun` gives the plain function space (source uses `.equivFun` too):
public noncomputable def standardExteriorCoordinates (m n : ℕ) :
    (⋀[ℤ]^n (Fin m → ℤ)) ≃ₗ[ℤ] (Fin (m.choose n) → ℤ)
  -- body: (standardExteriorBasisFin m n).equivFun

-- NEW — the rank count J7's Orzech step consumes; direct corollary of Mathlib's
-- `exteriorPower.finrank_eq` (already in pinned Mathlib — not new math):
public theorem exteriorPower_finrank_choose (m n : ℕ) :
    Module.finrank ℤ (⋀[ℤ]^n (Fin m → ℤ)) = m.choose n
  -- body (PROBED): rw [exteriorPower.finrank_eq,
  --   Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
```

### Minor matrix, induced map, Cauchy–Binet

`exteriorMinorMatrix` is made *rectangular* (row-set ⊆ `Fin p`, column-set ⊆
`Fin m`) rather than square-only — the source `exteriorSquare`/`exteriorCube`
are the `p = m = 4` specializations, and Cauchy–Binet is genuinely rectangular:

```lean
/-- Entry (s,t) = the n×n minor of T on row-set s, column-set t. -/
public def exteriorMinorMatrix (p m n : ℕ) (T : Matrix (Fin p) (Fin m) ℤ) :
    Matrix (Fin (p.choose n)) (Fin (m.choose n)) ℤ
  -- body (PROBED): fun s t ↦ (T.submatrix
  --   ((Set.powersetCard.ofFinEmbEquiv.symm
  --       ((powersetCardFinEquiv p n).symm s) : Fin n → Fin p))
  --   ((Set.powersetCard.ofFinEmbEquiv.symm
  --       ((powersetCardFinEquiv m n).symm t) : Fin n → Fin m))).det

-- generalized `exteriorMap` (6826), rectangular:
public noncomputable def exteriorPowerMap (p m n : ℕ)
    (A : Matrix (Fin p) (Fin m) ℤ) :
    (⋀[ℤ]^n (Fin m → ℤ)) →ₗ[ℤ] (⋀[ℤ]^n (Fin p → ℤ))
  -- body: exteriorPower.map n A.mulVecLin

-- generalized `squareMap_toMatrix`/`cubeMap_toMatrix` (6854/6861):
public theorem exteriorPowerMap_toMatrix (p m n : ℕ)
    (A : Matrix (Fin p) (Fin m) ℤ) :
    LinearMap.toMatrix (standardExteriorBasisFin m n)
        (standardExteriorBasisFin p n) (exteriorPowerMap p m n A) =
      exteriorMinorMatrix p m n A
  -- recipe: `LinearMap.toMatrix_apply` + `exteriorPower.basis_apply` +
  --   `exteriorPower.map_comp_ιMulti_family` + `exteriorPower.basis_repr_apply` +
  --   `exteriorPower.ιMultiDual_apply_ιMulti` gives det of the coord submatrix
  --   = minor of `toMatrix (Pi.basisFun) (Pi.basisFun) A.mulVecLin` (= `A`,
  --   since `A.mulVecLin` is `Matrix.toLin' A` up to basis identification and
  --   `LinearMap.toMatrix'_toLin'`/`Pi.basisFun` lemmas apply); `Matrix.det`
  --   transpose-invariance kills the transpose in the submatrix orientation.

-- NEW — the Cauchy–Binet corollary promised by §7 (matrix form; the
-- powersetCard-sum entrywise form follows by `Matrix.mul_apply` + reindexing
-- the sum by `powersetCardFinEquiv`):
public theorem cauchyBinet_minors (p q m n : ℕ)
    (A : Matrix (Fin p) (Fin q) ℤ) (B : Matrix (Fin q) (Fin m) ℤ) :
    exteriorMinorMatrix p m n (A * B) =
      exteriorMinorMatrix p q n A * exteriorMinorMatrix q m n B
  -- recipe: `exteriorPowerMap_toMatrix` thrice + `Matrix.mulVecLin_mul`
  --   (ToLin.lean:334) + `exteriorPower.map_comp` + `toMatrix` of `comp`
  --   equals product.
```

Rank-4 compatibility declarations (Specialization 6662–6882) are **retained in Hopf**
until their replacements and coordinate-compatibility equations are proved and their
consumers rerouted. They are not public outputs of the Mathlib-only J-A packet.
In particular pairSubset/tripleSubset, their ordered/equivalence lemmas and the old
coordinate maps must not be deleted before the order-theoretic adapters exist.
The following is the migration inventory, not an instruction to delete at J-A landing:
`latticeExterior` (6662), `latticeBasis` (6665), `latticeExteriorBasis` (6668),
`pairIndices_strictMono` (6672), `tripleIndices_strictMono` (6675), `pairIndices_injective`
(6678), `tripleIndices_injective` (6681), `pairEmbedding` (6684), `tripleEmbedding` (6687),
`pairSubset` (6690), `tripleSubset` (6693), `pairSubset_ordered` (6697),
`tripleSubset_ordered` (6704), `pairSubset_injective` (6710), `tripleSubset_injective`
(6716), `pairSubset_bijective` (6723), `tripleSubset_bijective` (6729), `pairSubsetEquiv`
(6736), `tripleSubsetEquiv` (6739), `squareBasis` (6742), `cubeBasis` (6745),
`squareBasis_apply` (6748), `cubeBasis_apply` (6756), `squareCoordinates` (6764),
`cubeCoordinates` (6767), `squareCoordinates_apply` (6771), `cubeCoordinates_apply` (6776),
`latticeExterior_finrank` (6780), `exteriorMap` (6826, → `exteriorPowerMap`),
`squareMap_coefficient` (6830, → `standardExterior_map_coefficient` +
`powersetCardFinEquiv` via the compat equation), `cubeMap_coefficient` (6843),
`squareMap_toMatrix` (6854), `cubeMap_toMatrix` (6861), `squareCoordinates_map` (6868),
`cubeCoordinates_map` (6876).

Compat detail: `pairSubsetEquiv : Fin 6 ≃ Set.powersetCard (Fin 4) 2` runs the
*opposite* direction to `powersetCardFinEquiv`; the adapter proves
`powersetCardFinEquiv 4 2 ∘ pairSubsetEquiv = id` (equivalently
`squareBasis = standardExteriorBasisFin 4 2`) from
`powersetCardFinEquiv_lt_iff` as described above — same for
`tripleSubsetEquiv` at `n = 3`.

Owner-flagged (not moved by J without owner sign-off): `LocalSystemMatrices.{pairIndices,
exteriorSquare, tripleIndices, exteriorCube}` (`FiniteCore.lean:328–338`) — generic
minor-matrix API at rank 4; recommend moving into `MinorCoordinates.lean` as the
lexicographic instances of `exteriorPowerMap_toMatrix`, or replacing by
`exteriorMinorMatrix 4 4 n` outright.

## Boundary J-B — `Lib/AlgebraicTopology/SingularHomology/Torus.lean`

```text
commit_boundary   J-B1 (recursive torus core, candidate only; not certified);
                  J-B2a (circle/naturality and coordinate-basis closure, blocked);
                  J-B2b (public degree-one identification, blocked).
imports           J-B1: Mathlib; Lib.AlgebraicTopology.SingularHomology.{MayerVietoris,
                  CircleProduct, HomotopyInvariance}.
                  J-B2a: J-B1 plus the public M-C provider and circle seams S-path/S-nat/S-cross.
                  J-B2b: J-B2a plus Lib.AlgebraicTopology.Hurewicz.Degree1.
                  No Torus packet imports Pontryagin.
visibility        `module` file; outputs `public` inside `namespace Mathoverflow1973`
source            Theorems A (first half) and B (§§3–4)
destination       Lib/AlgebraicTopology/SingularHomology/Torus.lean
focused_check     `lake build Lib.AlgebraicTopology.SingularHomology.Torus`
return_seam       Axis 5 for any `coordinateTorus*` signature drift
```

**J-B1 public outputs** (existing recursive-core signatures; candidate, not a GO).
The source proofs close over Mathlib and the landed circle splitting, with no
positive-circle or Pontryagin product. The independently certifiable unit ends before
`coordinateTorusMap` below. Every source declaration listed here remains public.

Proof-closure census (all names in `PeriodTorusHigherHomology` unless qualified):

| Outputs | Exact earlier inputs / source proof closure |
|---|---|
| ProductTorus; zero/successor homeomorphisms | Pi topology on AddCircle; Fin.cons/Fin.elim0; CuspFilling 13103, 13147–13174 |
| binomialModule; binomialPascalIndexEquiv; binomialModuleSuccEquiv | Nat.choose_succ_succ', finCongr, finSumFinEquiv, LinearEquiv.piCongrLeft', LinearEquiv.sumArrowLequivProdArrow; CuspFilling 14916–14926 |
| integerBinomialZeroEquiv; binomialModule_finrank; subsingleton/zero results | LinearEquiv.funUnique, Nat.choose_zero_right, Module.finrank_fin_fun, Nat.choose_eq_zero_of_lt; CuspFilling 14940–14961 |
| productTorusHomologyEquiv; zero/succ/succ_apply | preceding Pascal API; SingularHomology.connectedHomologyZeroEquiv, totallyDisconnected_homology_subsingleton, homeomorphHomologyEquiv, circleProductHomologyEquiv, circleProductHomologyEquiv_apply; structural recursion, CuspFilling 14963–15014 |
| homology free/finite/finrank/torsionFree/subsingleton | preceding equivalence; Module.Free.of_equiv, Module.Finite.of_surjective, LinearEquiv.finrank_eq; CuspFilling 15016–15038 |
| productTorusTopClass; equiv_topClass; zero/succ_coordinates/succ_boundary | preceding core; SingularHomology.pointClass and connectedHomologyZeroEquiv_pointClass; binomialModuleSuccEquiv_top at Specialization 3394, itself from binomialModule_eq_zero_of_lt; Specialization 3400–3438 |

Core helpers are not silently private: binomialModuleSuccEquiv_apply_fst/snd
(CuspFilling 14929/14935), binomialCoordinateBasis/apply (Specialization 3349/3354),
binomialModuleSuccEquiv_single_inl/inr (3359/3372), integerBinomialZeroEquiv_one_single
(3384), and binomialModuleSuccEquiv_top (3394) are retained source helpers. Their
complete signature census and aggregate J-B1 consumer test remain required before GO.

```lean
abbrev PeriodTorusHigherHomology.ProductTorus (n : ℕ) := Fin n → AddCircle (1 : ℝ)
  -- (CuspFilling 13103; TopologicalSpace/AddCommGroup/IsTopologicalAddGroup via Pi)

def PeriodTorusHigherHomology.productTorusZeroHomeomorph : ProductTorus 0 ≃ₜ PUnit
  -- (CuspFilling 13167)
def PeriodTorusHigherHomology.productTorusSuccHomeomorph (n : ℕ) :
    ProductTorus (n + 1) ≃ₜ AddCircle (1 : ℝ) × ProductTorus n
  -- (CuspFilling 13147; note: `CircleTopology.Circle` is the abbrev `AddCircle (1 : ℝ)`
  --  at CircleProduct.lean:137, so the circleProductHomologyEquiv domain unifies)

abbrev PeriodTorusHigherHomology.binomialModule (r n : ℕ) := Fin (r.choose n) → ℤ
  -- (CuspFilling 14916)
def PeriodTorusHigherHomology.binomialPascalIndexEquiv (r n : ℕ) :
    Fin ((r + 1).choose (n + 1)) ≃ Fin (r.choose (n + 1)) ⊕ Fin (r.choose n) -- (14919)
def PeriodTorusHigherHomology.binomialModuleSuccEquiv (r n : ℕ) :
    binomialModule (r + 1) (n + 1) ≃ₗ[ℤ] binomialModule r (n + 1) × binomialModule r n
  -- (14923)
def PeriodTorusHigherHomology.integerBinomialZeroEquiv (r : ℕ) :
    ℤ ≃ₗ[ℤ] binomialModule r 0                                                  -- (14940)
theorem PeriodTorusHigherHomology.binomialModule_finrank (r n : ℕ) :
    Module.finrank ℤ (binomialModule r n) = r.choose n                          -- (14945)
theorem PeriodTorusHigherHomology.binomialModule_subsingleton_of_lt {r n : ℕ}
    (h : r < n) : Subsingleton (binomialModule r n)                             -- (14949)
instance PeriodTorusHigherHomology.binomialModule_zero_succ_subsingleton (n : ℕ) :
    Subsingleton (binomialModule 0 (n + 1))                                     -- (14955)
theorem PeriodTorusHigherHomology.binomialModule_eq_zero_of_lt {r n : ℕ}
    (h : r < n) (x : binomialModule r n) : x = 0                                -- (14959)

def PeriodTorusHigherHomology.productTorusHomologyEquiv : (r n : ℕ) →
    SingularMayerVietoris.SingularHomology (ProductTorus r) n ≃ₗ[ℤ] binomialModule r n
  -- (CuspFilling 14963; the codomain stays `binomialModule` — it is an abbrev, so the
  --  "plain function space" spelling is defeq; no codomain change at landing)
theorem PeriodTorusHigherHomology.productTorusHomologyEquiv_zero (r : ℕ) :
    productTorusHomologyEquiv r 0 =
      (connectedHomologyZeroEquiv (ProductTorus r)).trans (integerBinomialZeroEquiv r)
  -- (14981)
theorem PeriodTorusHigherHomology.productTorusHomologyEquiv_succ (r n : ℕ) :
    productTorusHomologyEquiv (r + 1) (n + 1) =
      ((homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1)).toAddEquiv.trans
          ((circleProductHomologyEquiv (ProductTorus r) n).toAddEquiv.trans
            (((productTorusHomologyEquiv r (n + 1)).toAddEquiv.prodCongr
                  (productTorusHomologyEquiv r n).toAddEquiv).trans
              (binomialModuleSuccEquiv r n).symm.toAddEquiv))).toIntLinearEquiv
  -- (14986)
theorem PeriodTorusHigherHomology.productTorusHomologyEquiv_succ_apply (r n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (ProductTorus (r + 1)) (n + 1)) :
    binomialModuleSuccEquiv r n (productTorusHomologyEquiv (r + 1) (n + 1) a) =
      (productTorusHomologyEquiv r (n + 1)
          (circleProjectionHomology (ProductTorus r) (n + 1)
            (homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1) a)),
        productTorusHomologyEquiv r n
          (circleBoundary (ProductTorus r) n
            (homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1) a)))
  -- (14995; alias `productTorusHomologyEquiv_succ_pair` at Specialization 6439 is
  --  deleted, consumers re-pointed — dedup item)
def PeriodTorusHigherHomology.productTorusTopClass (n : ℕ) :
    SingularMayerVietoris.SingularHomology (ProductTorus n) n                   -- (3400)
theorem PeriodTorusHigherHomology.productTorusHomologyEquiv_topClass (n : ℕ) :
    productTorusHomologyEquiv n n (productTorusTopClass n) = fun _ => (1 : ℤ)
  -- (Specialization 3405)
theorem PeriodTorusHigherHomology.productTorusTopClass_zero :
    productTorusTopClass 0 = pointClass (0 : ProductTorus 0)                    -- (3410)
theorem PeriodTorusHigherHomology.productTorusTopClass_succ_coordinates (n : ℕ) :
    circleProductHomologyEquiv (ProductTorus n) n
        (homeomorphHomologyEquiv (productTorusSuccHomeomorph n) (n + 1)
          (productTorusTopClass (n + 1))) = (0, productTorusTopClass n)         -- (3417)
theorem PeriodTorusHigherHomology.productTorusTopClass_succ_boundary (n : ℕ) :
    circleBoundary (ProductTorus n) n
        (homeomorphHomologyEquiv (productTorusSuccHomeomorph n) (n + 1)
          (productTorusTopClass (n + 1))) = productTorusTopClass n              -- (3433)

theorem PeriodTorusHigherHomology.productTorus_homology_free (r n : ℕ) :
    Module.Free ℤ (SingularMayerVietoris.SingularHomology (ProductTorus r) n)
theorem PeriodTorusHigherHomology.productTorus_homology_finite (r n : ℕ) :
    Module.Finite ℤ (SingularMayerVietoris.SingularHomology (ProductTorus r) n)
theorem PeriodTorusHigherHomology.productTorus_homology_finrank (r n : ℕ) :
    Module.finrank ℤ (SingularMayerVietoris.SingularHomology (ProductTorus r) n) =
      r.choose n
theorem PeriodTorusHigherHomology.productTorus_homology_torsionFree (r n : ℕ) :
    Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology (ProductTorus r) n)
theorem PeriodTorusHigherHomology.productTorus_homology_subsingleton_of_lt {r n : ℕ}
    (h : r < n) :
    Subsingleton (SingularMayerVietoris.SingularHomology (ProductTorus r) n)
  -- CuspFilling declaration starts, in the order above:
  -- free 15016; finite 15020; finrank 15025; torsionFree 15030; subsingleton 15035.

```

**J-B2a coordinate outputs — blocked, not part of J-B1.** Their proof closure needs
S-nat, including `circleProductMap` (CuspFilling 14325) and
`circleProductHomologyEquiv_naturality` (14480). In particular:
`coordinateTorusBasis_apply` (Specialization 6498) →
`productTorusHomologyEquiv_coordinateTorusClass` (6459) →
`circleCoordinates_coordinateTorusClass_take` (6428) → S-nat.
The Along basis/span/range family inherits this dependency. Coordinate maps and
matrix helpers are grouped here conservatively rather than claimed as separate green units.

```lean
def PeriodTorusHigherHomology.coordinateTorusMap :
    (r n : ℕ) → Fin (r.choose n) → C(ProductTorus n, ProductTorus r)             -- (6237)
def PeriodTorusHigherHomology.coordinateTorusClass (r n : ℕ) (i : Fin (r.choose n)) :
    SingularMayerVietoris.SingularHomology (ProductTorus r) n                    -- (6361)
def PeriodTorusHigherHomology.coordinateTorusBasis (r n : ℕ) :
    Module.Basis (Fin (r.choose n)) ℤ
      (SingularMayerVietoris.SingularHomology (ProductTorus r) n)                -- (6492)
theorem PeriodTorusHigherHomology.coordinateTorusBasis_apply (r n : ℕ)
    (i : Fin (r.choose n)) : coordinateTorusBasis r n i = coordinateTorusClass r n i
  -- (6498)

def PeriodTorusHigherHomology.coordinateTorusMapAlong {X : Type} [TopologicalSpace X]
    {r : ℕ} (e : X ≃ₜ ProductTorus r) (n : ℕ) (i : Fin (r.choose n)) :
    C(ProductTorus n, X)                                                       -- (6555)
def PeriodTorusHigherHomology.coordinateTorusClassAlong {X : Type} [TopologicalSpace X]
    {r : ℕ} (e : X ≃ₜ ProductTorus r) (n : ℕ) (i : Fin (r.choose n)) :
    SingularMayerVietoris.SingularHomology X n                                   -- (6559)
def PeriodTorusHigherHomology.coordinateTorusBasisAlong {X : Type} [TopologicalSpace X]
    {r : ℕ} (e : X ≃ₜ ProductTorus r) (n : ℕ) :
    Module.Basis (Fin (r.choose n)) ℤ (SingularMayerVietoris.SingularHomology X n) -- (6565)
theorem PeriodTorusHigherHomology.coordinateTorusBasisAlong_apply {X : Type}
    [TopologicalSpace X] {r : ℕ} (e : X ≃ₜ ProductTorus r) (n : ℕ)
    (i : Fin (r.choose n)) :
    coordinateTorusBasisAlong e n i = coordinateTorusClassAlong e n i            -- (6571)
theorem PeriodTorusHigherHomology.coordinateTorusBasisAlong_coe {X : Type}
    [TopologicalSpace X] {r : ℕ} (e : X ≃ₜ ProductTorus r) (n : ℕ) :
    ⇑(coordinateTorusBasisAlong e n) = coordinateTorusClassAlong e n             -- (6586)
theorem PeriodTorusHigherHomology.coordinateTorusClassAlong_span {X : Type}
    [TopologicalSpace X] {r : ℕ} (e : X ≃ₜ ProductTorus r) (n : ℕ) :
    Submodule.span ℤ (Set.range (coordinateTorusClassAlong e n)) = ⊤             -- (6591)
theorem PeriodTorusHigherHomology.surjective_of_coordinateTorusClassAlong_mem_range
    {X : Type} [TopologicalSpace X] {r : ℕ} {M : Type*} [AddCommGroup M] [Module ℤ M]
    (e : X ≃ₜ ProductTorus r) (n : ℕ)
    (f : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology X n)
    (hf : ∀ i : Fin (r.choose n), coordinateTorusClassAlong e n i ∈
      LinearMap.range f) : Function.Surjective f                                -- (6596)

```

**J-B2b degree-one outputs — blocked identification seam.** The canonical Degree1
signatures below elaborate in the review-3 Lib-only provisional provider. The source
proofs use the old loop-class interface; they are not verbatim public-module moves.
`coordinateH1_basis_hit` and `coordinateH1_apply` below are missing mathematical
inputs, not proved APIs. They must be aligned and independently reviewed before
surjectivity, naturality or J-D can be handed to Axis 6.

```lean
def PeriodTorusHigherHomology.coordinateH1Add (n : ℕ) :
    (Fin n → ℤ) →+ AlgebraicTopology.SingularH1 (ProductTorus n)                     -- (6884)
def PeriodTorusHigherHomology.coordinateH1 (n : ℕ) :
    (Fin n → ℤ) →ₗ[ℤ] AlgebraicTopology.SingularH1 (ProductTorus n)                  -- (6891)
@[simp]
theorem PeriodTorusHigherHomology.coordinateH1_basis (n : ℕ) (i : Fin n) :
    coordinateH1 n (Pi.basisFun ℤ (Fin n) i) =
      AlgebraicTopology.Hurewicz.loopHomologyClass (coordinatePeriodLoop n (Pi.single i 1))   -- (6901)
@[simp]
theorem PeriodTorusHigherHomology.coordinateH1_single (n : ℕ) (i : Fin n) :
    coordinateH1 n (Pi.single i 1) =
      AlgebraicTopology.Hurewicz.loopHomologyClass (coordinatePeriodLoop n (Pi.single i 1))   -- (6907)
-- NB: `AlgebraicTopology.SingularH1 X` is the abbrev
-- `((TopCat.toSSet.obj X).chainComplex ℤ).homology 1` (Degree1.lean:106) — defeq to
-- `SingularMayerVietoris.SingularHomology X 1`; `SingularH1.map f` is defeq to
-- `singularHomologyMap f 1`. No bridging equiv is needed, only `change`/defeq use.

-- NEW — generalizes `coordinateH1_four_surjective` (7033, rank-4-only). Proof is NOT
-- the rank-4 detour through the marking: `coordinateTorusBasis r 1` exhibits the range
-- of `coordinateH1 r` hitting every `coordinateTorusClass r 1 i` (the two bases differ
-- by a permutation of `Fin (r.choose 1) ≃ Fin r`), then
-- `surjective_of_coordinateTorusClassAlong_mem_range (Homeomorph.refl _) 1`:
theorem PeriodTorusHigherHomology.coordinateH1_basis_hit (r : ℕ)
    (i : Fin (r.choose 1)) :
    ∃ v : Fin r → ℤ, coordinateH1 r v = coordinateTorusClass r 1 i

theorem PeriodTorusHigherHomology.coordinateH1_apply (r : ℕ) (v : Fin r → ℤ) :
    coordinateH1 r v =
      AlgebraicTopology.Hurewicz.loopHomologyClass (coordinatePeriodLoop r v)

theorem PeriodTorusHigherHomology.coordinateH1_surjective (r : ℕ) :
    Function.Surjective (coordinateH1 r)

-- NEW — generalizes `coordinateH1_matrix_natural` (6940), conditional on the
-- missing `coordinateH1_apply` above: rewrite both sides with that identity, then
-- use the public-API form of `torusMatrixMap_coordinatePeriodHomology` (3533).
-- Basis linearity alone does not establish the arbitrary-column loop identity.
-- This is J-B2b, not a green J-B1 result.
theorem PeriodTorusHigherHomology.coordinateH1_matrix_natural (r : ℕ)
    (A : Matrix (Fin r) (Fin r) ℤ) (v : Fin r → ℤ) :
    AlgebraicTopology.SingularH1.map (torusMatrixMap A) (coordinateH1 r v) =
      coordinateH1 r (A *ᵥ v)
  -- the rank-4 `coordinateH1_matrix_natural (p : PeriodDomain)` (6940) is then a
  -- corollary; it stays in Hopf only if its `PeriodDomain` formulation is what
  -- consumers cite — prefer re-pointing consumers at this general version.

-- NEW — generalizes `coordinateH1_four_bijective` (6929): `coordinateH1_surjective`
-- plus `OrzechProperty.bijective_of_surjective_of_finrank_le` with
-- `Module.finrank_fintype_fun_eq_card` on both sides:
theorem PeriodTorusHigherHomology.coordinateH1_bijective (r : ℕ) :
    Function.Bijective (coordinateH1 r)
def PeriodTorusHigherHomology.coordinateH1Equiv (r : ℕ) :
    (Fin r → ℤ) ≃ₗ[ℤ] AlgebraicTopology.SingularH1 (ProductTorus r)
  -- generalizes `coordinateH1FourEquiv` (6936): LinearEquiv.ofBijective _ (coordinateH1_bijective r)
```

**J-B2 proof-closure disposition (not J-B1).** The coordinate-matrix/map recursion
at Specialization 6200–6359, classes/coordinate equations at 6361–6502, and Along
family at 6555–6635 belong to J-B2a. Its dependency chain includes the previously
omitted torusMatrixLinearMap/continuous/torusMatrixMap at 2464/2481/2488, the map
identities through 2524, and coordinateProjection at CuspFilling 13106–13145.
The coordinateCircleMap/loop/torusTailMap family at Specialization 3454–3594 and
coordinatePeriodLoop at CuspFilling 13176 require the S-path/public-loop-class
alignment when used on homology. No rank-four PeriodDomain adapter moves with them.

`productTorusTopClass_succ_product` (Specialization 3646) and its product-dependent
proof helpers `productTorusSucc_inverse_eq_add` (3596), `torusSplit_positiveCircleCross`
(3609), `productTorusTopClass_two` (3673), and `productTorusTopClass_three` (3683) move
with **J-C3**, after Torus; Torus does not contain their Pontryagin-valued types.
`productTorusTopClass_succ_cross` (3631), `torusHeadCircleMap_positiveHomology` (3625)
and `productTorusTopClass_one` (3655) depend on circle/loop seams but not Pontryagin
and belong to J-B2a. This allocation breaks the type-level Torus↔Pontryagin cycle.

The following names are existing `SingularHomology` inputs, **not moves**:
pointClass, singularHomologyMap_pointClass (CircleProduct 964/988),
singularHomologyMap_comp and homeomorphHomologyEquiv_symm_apply
(HomotopyInvariance; all four checked with Lib imports alone).

Public helper signatures (J-B2a, except the matrix-on-loop statement which is J-B2b):

```lean
def PeriodTorusHigherHomology.torusMatrixMap {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) : C(ProductTorus n, ProductTorus m)

def PeriodTorusHigherHomology.coordinatePeriodLoop (r : ℕ) (v : Fin r → ℤ) :
    Path (0 : ProductTorus r) 0

def PeriodTorusHigherHomology.torusTailMap (n : ℕ) :
    C(ProductTorus n, ProductTorus (n + 1))

theorem PeriodTorusHigherHomology.torusTailMap_add (n : ℕ) (x y : ProductTorus n) :
    torusTailMap n (x + y) = torusTailMap n x + torusTailMap n y

theorem PeriodTorusHigherHomology.coordinateTorusMapAlong_add {G : Type}
    [TopologicalSpace G] [Add G] {r : ℕ} (e : G ≃ₜ ProductTorus r)
    (he : ∀ x y, e (x + y) = e x + e y) (n : ℕ) (i : Fin (r.choose n))
    (x y : ProductTorus n) :
    coordinateTorusMapAlong e n i (x + y) =
      coordinateTorusMapAlong e n i x + coordinateTorusMapAlong e n i y

theorem PeriodTorusHigherHomology.torusMatrixMap_coordinatePeriodHomology {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (v : Fin n → ℤ) :
    AlgebraicTopology.SingularH1.map (torusMatrixMap A)
        (AlgebraicTopology.Hurewicz.loopHomologyClass (coordinatePeriodLoop n v)) =
      AlgebraicTopology.Hurewicz.loopHomologyClass (coordinatePeriodLoop m (A *ᵥ v))

theorem PeriodTorusHigherHomology.productTorusTopClass_one :
    productTorusTopClass 1 =
      AlgebraicTopology.Hurewicz.loopHomologyClass (coordinatePeriodLoop 1 (Pi.single 0 1))
```

Source coordinates in order: Specialization 2488; CuspFilling 13176;
Specialization 3554, 3563, 6626, 3533, 3655. The two loop-class statements are target
signatures in the public Degree1 API, not claims that their original proofs already
import through that module. The new rank-general basis-hit/apply nodes have no existing
source declarations; their textbook source is §4's coordinate-basis identification.

**J-B2 — circle-section API, blocked seam.** Public outputs (exact signatures; the
proofs route through the unlanded circle-path cluster below):

```lean
def PeriodTorusHigherHomology.positiveCircleCross (X : Type) [TopologicalSpace X]
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology X n →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (CircleTopology.Circle × X) (n + 1)
  -- (CuspFilling 13700; body = crossProductHomology Circle X n
  --   (AlgebraicTopology.Hurewicz.loopHomologyClass CirclePaths.positiveLoop))
theorem PeriodTorusHigherHomology.positiveCircleCross_arcSum_cycleClass (X : Type)
    [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle
      (SingularChains.singularComplex X) n) :
    positiveCircleCross X n
        (SingularMayerVietoris.ModuleHomology.cycleClass
          (SingularChains.singularComplex X) n b) =
      SingularMayerVietoris.ModuleHomology.cycleClass
        (SingularChains.singularComplex (CircleTopology.Circle × X)) (n + 1)
        (crossProductCycles CircleTopology.Circle X n CirclePaths.arcSumCycle b)
                                                                          -- (13707)
theorem PeriodTorusHigherHomology.circleBoundaryCoordinates_positiveCircleCross
    (X : Type) [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.SingularHomology X n) :
    circleBoundaryCoordinates X n (positiveCircleCross X n b) = (-b, b)     -- (14310)
@[simp]
theorem PeriodTorusHigherHomology.circleBoundary_positiveCircleCross (X : Type)
    [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.SingularHomology X n) :
    circleBoundary X n (positiveCircleCross X n b) = b                      -- (14319)
theorem PeriodTorusHigherHomology.circleProjection_positiveCircleCross (X : Type)
    [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.SingularHomology X n) :
    circleProjectionHomology X (n + 1) (positiveCircleCross X n b) = 0      -- (14579)
@[simp]
theorem PeriodTorusHigherHomology.circleProductHomologyEquiv_positiveCircleCross
    (X : Type) [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.SingularHomology X n) :
    circleProductHomologyEquiv X n (positiveCircleCross X n b) = (0, b)     -- (14585)
theorem PeriodTorusHigherHomology.positiveCircleCross_eq_symm (X : Type)
    [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.SingularHomology X n) :
    positiveCircleCross X n b = (circleProductHomologyEquiv X n).symm (0, b)
                                                                          -- (14592)
theorem PeriodTorusHigherHomology.circleProductHomologyEquiv_symm_eq_section_add_cross
    (X : Type) [TopologicalSpace X] (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology X (n + 1) ×
      SingularMayerVietoris.SingularHomology X n) :
    (circleProductHomologyEquiv X n).symm a =
      circleSectionHomology X (n + 1) a.1 + positiveCircleCross X n a.2     -- (14598)
theorem PeriodTorusHigherHomology.positiveCircleCross_naturality {X : Type}
    [TopologicalSpace X] {Y : Type} [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ)
    (b : SingularMayerVietoris.SingularHomology X n) :
    SingularMayerVietoris.singularHomologyMap (circleProductMap f) (n + 1)
        (positiveCircleCross X n b) =
      positiveCircleCross Y n
        (SingularMayerVietoris.singularHomologyMap f n b)                   -- (14610)
```

Supporting decls moving with this boundary (verbatim signatures, same file or
`CrossProduct.lean` if the owner lands the cluster there):
`circleProductMap` (CuspFilling 14325 — `C(Circle × X, Circle × Y)` from `f : C(X, Y)`),
`circleConnecting_positiveCircleCross_cycleClass` (14271),
`circleBoundaryCoordinates_positiveCircleCross_cycleClass` (14291),
`twoChainSmallCycle` (14129), `twoChainSmallCycle_*` boundary/class lemmas,
`connectingHomomorphism_twoChain` (14194),
`crossProductEdge_path_boundary` (13856),
`intersectionDifferenceCycle` + `positiveCircleSmallCycle*` (the small-cycle helpers
used at 14278–14290).

**S-nat — unlanded splitting-naturality closure**, all in CuspFilling:
`circleProductMap` (14325), `intersectionProductMap` (14331),
`circleProductMap_projection` (14338), `intersectionProductMap_homotopyEquiv` (14344),
`circleProjectionHomology_naturality` (14362), `sumHomologyEquiv_naturality` (14369),
`productIntersectionHomologyEquiv_naturality` (14384), `circleProductMap_mapsToU` (14409),
`circleProductMap_mapsToV` (14414), `circleProductIntersectionRestriction_eq` (14419),
`circleMayerVietorisConnecting_naturality` (14427), `circleBoundaryCoordinates_naturality`
(14443), `circleBoundary_naturality` (14466), `circleProductHomologyEquiv_naturality`
(14480), and `circleProductHomologyEquiv_symm_naturality` (14493).
This gates the coordinate basis **and** the circle-section naturality result; it is
not supplied by the landed CircleProduct module. Owner/provider commit is outstanding.

**S-path — unlanded circle-path closure**, CuspFilling **13348–13698**. In addition
to the named outputs below, include CirclePaths.circleTranslation (13348),
circleTranslation_apply (13360), circleTranslationHomotopy (13365),
circleTranslation_singularHomologyMap (13380), circleTranslation_inducedHomology
(13386), loopHomologyClass_map_circleTranslation (13390), quarterPoint (13410),
quarterPoint_coe (13419), quarterIntersection_component (13424),
threeQuarterIntersection_component (13430), quarterU (13435), quarterV (13439),
uCirclePath_apply (13517), vCirclePath_apply (13523), quarterLoop_apply (13542),
quarterTranslation_zero (13572), quarterLoop_eq_translation (13576),
quarterIntersectionSection_comp (13665), threeQuarterIntersectionSection_component
(13675), and threeQuarterIntersectionSection_comp (13691). These earlier/later
helpers are part of the source proof closure, not optional omissions.

**S-cross — unlanded cross-product naturality**, CuspFilling 14509–14576;
its exact theorem names and declaration starts are listed below.

S-path/S-cross named interfaces (all currently legacy source, NOT GO):
`CirclePaths.{positiveLoop` (13558) + `positiveLoop_apply`, `quarterLoop`,
`arcSumCycle` (13609), `arcSumCycle_class` (13614),
`arcSumCycle_positiveLoop_class` (13628), `quarterIntersection` (13398),
`threeQuarterIntersection` (13404), `threeQuarterPoint` (13414), `threeQuarterU` (13443),
`threeQuarterV` (13447), `uPath` (13451), `vPath` (13480), `uCirclePath` (13510),
`vCirclePath` (13513), `uCirclePath_trans_vCirclePath`, `quarterLoop_homologyClass`,
`quarterIntersectionSection` (13633, `X : Type*`), `threeQuarterIntersectionSection`
(13641, `X : Type*`), `quarterIntersectionSection_component`, `boundaryOne_arcSum`};
`crossProductCycles_natural` (14509), `crossProductHomology_natural` (14526),
`crossProductHomology_snd` (14549).

Lane A's report (`Lib/reports/A.md` §Wang note) proposes that cluster for
`CrossProduct.lean`; its landing is **not J-owned** — owner confirmation needed
(GLM's cross-product work is the natural home). Only the restricted J-B1 recursive
core above is independent of this cluster. J-B2a waits for an owner-approved public
provider of S-path, S-nat and S-cross plus M-C; it does not acquire permission to
land another lane's cluster merely because its statements need it. NB: the `quarterIntersectionSection` family uses
`Type*` for the ambient space — harmless there (pure topology, no homology), keep as-is.

## Boundary J-C — `Lib/AlgebraicTopology/SingularHomology/Pontryagin.lean`

```text
commit_boundary   J-C1 (candidate; blocked by M-C public-module provider);
                  J-C2 (also needs S-cross); J-C3 (also needs GLM's G-J3,
                  J-B2a circle/top-class API and the public loop-class alignment).
                  All three remain NOT GO until aggregate module/consumer checks.
imports           Mathlib; Lib.AlgebraicTopology.SingularHomology.{MayerVietoris,
                  CrossProduct}; J-B's Torus.lean only for the top-class lemmas of J-C3
visibility        `module` file; outputs `public` inside `namespace Mathoverflow1973`
source            Theorem C (§5)
destination       Lib/AlgebraicTopology/SingularHomology/Pontryagin.lean
focused_check     `lake build Lib.AlgebraicTopology.SingularHomology.Pontryagin`
return_seam       Axis 5 if a lemma's coherence dependency was misread
```

**J-C1 public outputs** (mathematical inputs exist at head, but their CrossProduct
provider is legacy: NOT GO for a production module). Inputs: `crossProductHomology`,
`integerBilinearPostcompose`, `singularHomologyMap`, and the topology/linear algebra
APIs used in the source proofs; no torus import is needed by this sub-boundary.

```lean
def PeriodTorusHigherHomologyPontryagin.cyclicMap (X Y Z : Type) [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] : C(Y × (Z × X), X × (Y × Z))  -- (3143)
def PeriodTorusHigherHomologyPontryagin.additionMap (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G] : C(G × G, G)                 -- (3147)
def PeriodTorusHigherHomologyPontryagin.rightAdditionMap (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G] : C(G × (G × G), G)           -- (3151)
theorem PeriodTorusHigherHomologyPontryagin.rightAdditionMap_comp_cyclic (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G] :
    (rightAdditionMap G).comp (cyclicMap G G G) = rightAdditionMap G         -- (3156)
theorem PeriodTorusHigherHomologyPontryagin.rightAddition_homology_cyclic (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G] (n : ℕ) :
    (SingularMayerVietoris.singularHomologyMap (rightAdditionMap G) n).comp
        (SingularMayerVietoris.singularHomologyMap (cyclicMap G G G) n) =
      SingularMayerVietoris.singularHomologyMap (rightAdditionMap G) n       -- (3163;
  -- needs only `singularHomologyMap_comp` + `rightAdditionMap_comp_cyclic` — J-C1)
theorem PeriodTorusHigherHomologyPontryagin.additionMap_natural {G : Type}
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G] {H : Type}
    [TopologicalSpace H] [AddCommGroup H] [IsTopologicalAddGroup H] (f : C(G, H))
    (hf : ∀ x y, f (x + y) = f x + f y) :
    f.comp (additionMap G) = (additionMap H).comp (f.prodMap f)              -- (3170)
theorem PeriodTorusHigherHomologyPontryagin.addition_homology_natural {G : Type}
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G] {H : Type}
    [TopologicalSpace H] [AddCommGroup H] [IsTopologicalAddGroup H] (f : C(G, H))
    (hf : ∀ x y, f (x + y) = f x + f y) (n : ℕ) :
    (SingularMayerVietoris.singularHomologyMap f n).comp
        (SingularMayerVietoris.singularHomologyMap (additionMap G) n) =
      (SingularMayerVietoris.singularHomologyMap (additionMap H) n).comp
        (SingularMayerVietoris.singularHomologyMap (f.prodMap f) n)          -- (3177)
def PeriodTorusHigherHomologyPontryagin.product (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G] (n : ℕ) :
    SingularMayerVietoris.SingularHomology G 1 →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology G n →ₗ[ℤ]
        SingularMayerVietoris.SingularHomology G (n + 1)                     -- (3190)
theorem PeriodTorusHigherHomologyPontryagin.product_apply (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G] (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology G 1)
    (b : SingularMayerVietoris.SingularHomology G n) :
    product G n a b =
      SingularMayerVietoris.singularHomologyMap (additionMap G) (n + 1)
        (PeriodTorusHigherHomology.crossProductHomology G G n a b)           -- (3202)
abbrev PeriodTorusHigherHomologyPontryagin.product11 (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G] :
    SingularMayerVietoris.SingularHomology G 1 →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology G 1 →ₗ[ℤ]
        SingularMayerVietoris.SingularHomology G 2                           -- (3213)
abbrev PeriodTorusHigherHomologyPontryagin.product12 (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G] :
    SingularMayerVietoris.SingularHomology G 1 →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology G 2 →ₗ[ℤ]
        SingularMayerVietoris.SingularHomology G 3                           -- (3222)
def PeriodTorusHigherHomologyPontryagin.tripleProduct (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G] :
    SingularMayerVietoris.SingularHomology G 1 →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology G 1 →ₗ[ℤ]
        SingularMayerVietoris.SingularHomology G 1 →ₗ[ℤ]
          SingularMayerVietoris.SingularHomology G 3                         -- (3231)
theorem PeriodTorusHigherHomologyPontryagin.tripleProduct_apply (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (a b c : SingularMayerVietoris.SingularHomology G 1) :
    tripleProduct G a b c = product12 G a (product11 G b c)                  -- (3269)

-- generic multilinear/alternating plumbing (3698–3768), verbatim — pure linear
-- algebra, no coherence deps, so J-C1 even though its consumers are J-C3:
def PeriodTorusHigherHomologyPontryagin.multilinearOfBilinear {M N : Type*}
    [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    (β : M →ₗ[ℤ] M →ₗ[ℤ] N) : MultilinearMap ℤ (fun _ : Fin 2 => M) N        -- (3698)
def PeriodTorusHigherHomologyPontryagin.alternatingOfBilinear {M N : Type*}
    [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    (β : M →ₗ[ℤ] M →ₗ[ℤ] N) (hdiag : ∀ x : M, β x x = 0) :
    AlternatingMap ℤ M N (Fin 2)                                            -- (3715)
theorem PeriodTorusHigherHomologyPontryagin.skewBilinear_diagonal_zero {M N : Type*}
    [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    [Module.IsTorsionFree ℤ N] (β : M →ₗ[ℤ] M →ₗ[ℤ] N)
    (hskew : ∀ x y : M, β x y = -β y x) (x : M) : β x x = 0                 -- (3728)
def PeriodTorusHigherHomologyPontryagin.multilinearOfTrilinear {M N : Type*}
    [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    (g : M →ₗ[ℤ] M →ₗ[ℤ] M →ₗ[ℤ] N) : MultilinearMap ℤ (fun _ : Fin 3 => M) N
                                                                          -- (3736)
def PeriodTorusHigherHomologyPontryagin.alternatingOfTrilinear {M N : Type*}
    [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    (g : M →ₗ[ℤ] M →ₗ[ℤ] M →ₗ[ℤ] N) (h01 : ∀ x z : M, g x x z = 0)
    (h02 : ∀ x y : M, g x y x = 0) (h12 : ∀ x y : M, g x y y = 0) :
    AlternatingMap ℤ M N (Fin 3)                                            -- (3753)
```

**J-C2 — needs `crossProductHomology_natural`** (still `Hopf/`-only, CuspFilling 14526;
also `crossProductCycles_natural` 14509, `crossProductHomology_snd` 14549 — same
unlanded cluster as J-B2; record on that seam). Exact signatures:

```lean
theorem PeriodTorusHigherHomologyPontryagin.product_natural {G H : Type}
    [TopologicalSpace G] [TopologicalSpace H] [AddCommGroup G] [AddCommGroup H]
    [IsTopologicalAddGroup G] [IsTopologicalAddGroup H] (f : C(G, H))
    (hf : ∀ x y, f (x + y) = f x + f y) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology G 1)
    (b : SingularMayerVietoris.SingularHomology G n) :
    SingularMayerVietoris.singularHomologyMap f (n + 1) (product G n a b) =
      product H n (SingularMayerVietoris.singularHomologyMap f 1 a)
        (SingularMayerVietoris.singularHomologyMap f n b)                    -- (3277)
theorem PeriodTorusHigherHomologyPontryagin.tripleProduct_natural {G H : Type}
    [TopologicalSpace G] [TopologicalSpace H] [AddCommGroup G] [AddCommGroup H]
    [IsTopologicalAddGroup G] [IsTopologicalAddGroup H] (f : C(G, H))
    (hf : ∀ x y, f (x + y) = f x + f y)
    (a b c : SingularMayerVietoris.SingularHomology G 1) :
    SingularMayerVietoris.singularHomologyMap f 3 (tripleProduct G a b c) =
      tripleProduct H (SingularMayerVietoris.singularHomologyMap f 1 a)
        (SingularMayerVietoris.singularHomologyMap f 1 b)
        (SingularMayerVietoris.singularHomologyMap f 1 c)                    -- (3292)
theorem PeriodTorusHigherHomologyPontryagin.tripleProduct_eq_cross (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (a b c : SingularMayerVietoris.SingularHomology G 1) :
    tripleProduct G a b c =
      SingularMayerVietoris.singularHomologyMap (rightAdditionMap G) 3
        (PeriodTorusHigherHomology.crossProductHomology G (G × G) 2 a
          (PeriodTorusHigherHomology.crossProductHomology G G 1 b c))        -- (3309;
  -- direct call site of `crossProductHomology_natural` at 3317)
```

**J-C3 — needs GLM's G-J3 coherence suite** (the homology-level laws
`crossProductHomology_{swap,pushforward_anticommute,associative,cyclic}` and friends,
currently Specialization 3771–5987; exact exclusion manifest below). Exact signatures:

```lean
theorem PeriodTorusHigherHomologyPontryagin.product11_skew (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (a b : SingularMayerVietoris.SingularHomology G 1) :
    product11 G a b = -product11 G b a                                      -- (4199)
theorem PeriodTorusHigherHomologyPontryagin.product11_self (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (a : SingularMayerVietoris.SingularHomology G 1) : product11 G a a = 0  -- (4207)
def PeriodTorusHigherHomologyPontryagin.homologyAlternatingTwo (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] :
    AlternatingMap ℤ (SingularMayerVietoris.SingularHomology G 1)
      (SingularMayerVietoris.SingularHomology G 2) (Fin 2)                    -- (4215)
def PeriodTorusHigherHomologyPontryagin.homologyAlternatingThree (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] :
    AlternatingMap ℤ (SingularMayerVietoris.SingularHomology G 1)
      (SingularMayerVietoris.SingularHomology G 3) (Fin 3)                    -- (6055)
def PeriodTorusHigherHomologyPontryagin.homologyWedgeTwo (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] :
    (⋀[ℤ]^2 (SingularMayerVietoris.SingularHomology G 1)) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology G 2                            -- (4224)
theorem PeriodTorusHigherHomologyPontryagin.homologyWedgeTwo_apply_ιMulti (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (v : Fin 2 → SingularMayerVietoris.SingularHomology G 1) :
    homologyWedgeTwo G (exteriorPower.ιMulti ℤ 2 v) = product11 G (v 0) (v 1) -- (4234)
def PeriodTorusHigherHomologyPontryagin.homologyWedgeThree (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] :
    (⋀[ℤ]^3 (SingularMayerVietoris.SingularHomology G 1)) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology G 3                            -- (6065;
  -- NOTE the hypothesis is torsion-freeness of H₂, not H₃ — the wedge descends via
  --  alternatingOfTrilinear which needs the degree-2 diagonal vanishing)
theorem PeriodTorusHigherHomologyPontryagin.homologyWedgeThree_apply_ιMulti (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (v : Fin 3 → SingularMayerVietoris.SingularHomology G 1) :
    homologyWedgeThree G (exteriorPower.ιMulti ℤ 3 v) =
      tripleProduct G (v 0) (v 1) (v 2)                                     -- (6075)

-- the lattice wedge, de-pinned: `Lattice` → arbitrary `M`; `latticeWedgeTwo G c`
-- becomes `(homologyWedgeTwo G).comp (exteriorPower.map 2 c)` at general `M`:
def PeriodTorusHigherHomologyPontryagin.wedgeTwoAlong (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    {M : Type} [AddCommGroup M] [Module ℤ M]
    (c : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1) :
    (⋀[ℤ]^2 M) →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 2
  -- generalizes `latticeWedgeTwo` (4243); the rank-4 name is deleted, consumers
  -- re-pointed at `wedgeTwoAlong G c` with `M := Lattice`
def PeriodTorusHigherHomologyPontryagin.wedgeThreeAlong (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    {M : Type} [AddCommGroup M] [Module ℤ M]
    (c : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1) :
    (⋀[ℤ]^3 M) →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 3
  -- likewise for `latticeWedgeThree` (6084)
theorem PeriodTorusHigherHomologyPontryagin.wedgeTwoAlong_apply_ιMulti (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    {M : Type} [AddCommGroup M] [Module ℤ M]
    (c : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1) (v : Fin 2 → M) :
    wedgeTwoAlong G c (exteriorPower.ιMulti ℤ 2 v) = product11 G (c (v 0)) (c (v 1))
  -- generalizes `latticeWedgeTwo_apply_ιMulti` (4253, @[simp])
theorem PeriodTorusHigherHomologyPontryagin.wedgeThreeAlong_apply_ιMulti (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    {M : Type} [AddCommGroup M] [Module ℤ M]
    (c : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1) (v : Fin 3 → M) :
    wedgeThreeAlong G c (exteriorPower.ιMulti ℤ 3 v) =
      tripleProduct G (c (v 0)) (c (v 1)) (c (v 2))
  -- generalizes `latticeWedgeThree_apply_ιMulti` (6094, @[simp])

-- wedge naturality (needs J-C2's naturality seam AND the J-C3 wedge — dual deps;
-- lands with J-C3):
theorem PeriodTorusHigherHomologyPontryagin.wedgeTwoAlong_natural {G : Type}
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] {H : Type}
    [TopologicalSpace H] [AddCommGroup H] [IsTopologicalAddGroup H]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology H 2)] (f : C(G, H))
    (hf : ∀ x y, f (x + y) = f x + f y) {M N : Type} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N]
    (c : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1)
    (d : N →ₗ[ℤ] SingularMayerVietoris.SingularHomology H 1) (A : M →ₗ[ℤ] N)
    (hmark : ∀ v, SingularMayerVietoris.singularHomologyMap f 1 (c v) = d (A v)) :
    (SingularMayerVietoris.singularHomologyMap f 2).comp (wedgeTwoAlong G c) =
      (wedgeTwoAlong H d).comp (exteriorPower.map 2 A)
  -- de-pinned `latticeWedgeTwo_natural` (4264): source uses `Lattice` for all three
  -- of M N A; general M N with A : M →ₗ[ℤ] N is the same proof
theorem PeriodTorusHigherHomologyPontryagin.wedgeThreeAlong_natural {G : Type}
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] {H : Type}
    [TopologicalSpace H] [AddCommGroup H] [IsTopologicalAddGroup H]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology H 2)] (f : C(G, H))
    (hf : ∀ x y, f (x + y) = f x + f y) {M N : Type} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N]
    (c : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1)
    (d : N →ₗ[ℤ] SingularMayerVietoris.SingularHomology H 1) (A : M →ₗ[ℤ] N)
    (hmark : ∀ v, SingularMayerVietoris.singularHomologyMap f 1 (c v) = d (A v)) :
    (SingularMayerVietoris.singularHomologyMap f 3).comp (wedgeThreeAlong G c) =
      (wedgeThreeAlong H d).comp (exteriorPower.map 3 A)
  -- de-pins `latticeWedgeThree_natural` (Specialization 6106); provisional module
  -- signature elaborated in review 3; proof still waits on J-C2/J-C3.

theorem PeriodTorusHigherHomologyPontryagin.product11_mem_range_wedgeTwoAlong
    (G : Type) [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    {M : Type} [AddCommGroup M] [Module ℤ M]
    (c : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1)
    (hc : Function.Surjective c)
    (a b : SingularMayerVietoris.SingularHomology G 1) :
    product11 G a b ∈ LinearMap.range (wedgeTwoAlong G c)
  -- generalizes `product11_mem_range_latticeWedgeTwo` (6131)
theorem PeriodTorusHigherHomologyPontryagin.tripleProduct_mem_range_wedgeThreeAlong
    (G : Type) [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    {M : Type} [AddCommGroup M] [Module ℤ M]
    (c : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1)
    (hc : Function.Surjective c)
    (a b d : SingularMayerVietoris.SingularHomology G 1) :
    tripleProduct G a b d ∈ LinearMap.range (wedgeThreeAlong G c)
  -- generalizes `tripleProduct_mem_range_latticeWedgeThree` (6144)

theorem PeriodTorusHigherHomologyPontryagin.tripleProduct_cyclic (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (a b c : SingularMayerVietoris.SingularHomology G 1) :
    tripleProduct G a b c = tripleProduct G b c a                           -- (6013;
  -- needs `crossProductHomology_cyclic` (GLM) + `tripleProduct_eq_cross` (J-C2))
theorem PeriodTorusHigherHomologyPontryagin.tripleProduct_self12 (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (a b : SingularMayerVietoris.SingularHomology G 1) :
    tripleProduct G a b b = 0                                               -- (6031)
theorem PeriodTorusHigherHomologyPontryagin.tripleProduct_self02 (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (a b : SingularMayerVietoris.SingularHomology G 1) :
    tripleProduct G a b a = 0                                               -- (6039)
theorem PeriodTorusHigherHomologyPontryagin.tripleProduct_self01 (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (a b : SingularMayerVietoris.SingularHomology G 1) :
    tripleProduct G a a b = 0                                               -- (6047)

theorem PeriodTorusHigherHomology.productTorusTopClass_succ_product (n : ℕ) :
    productTorusTopClass (n + 1) =
      PeriodTorusHigherHomologyPontryagin.product (ProductTorus (n + 1)) n
        (AlgebraicTopology.Hurewicz.loopHomologyClass
          (coordinatePeriodLoop (n + 1) (Pi.single 0 1)))
        (SingularMayerVietoris.singularHomologyMap (torusTailMap n) n
          (productTorusTopClass n))
  -- Specialization 3646, public Degree1 target; J-C3 after J-B2a, never Torus core.

theorem PeriodTorusHigherHomology.productTorusTopClass_two_is_product :
    ∃ a b : SingularMayerVietoris.SingularHomology (ProductTorus 2) 1,
      productTorusTopClass 2 =
        PeriodTorusHigherHomologyPontryagin.product11 (ProductTorus 2) a b   -- (6156)
theorem PeriodTorusHigherHomology.productTorusTopClass_three_is_tripleProduct :
    ∃ a b c : SingularMayerVietoris.SingularHomology (ProductTorus 3) 1,
      productTorusTopClass 3 =
        PeriodTorusHigherHomologyPontryagin.tripleProduct (ProductTorus 3) a b c
                                                                          -- (6165)
theorem PeriodTorusHigherHomology.map_topClass_two_mem_range_wedgeTwoAlong {G : Type}
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    {M : Type} [AddCommGroup M] [Module ℤ M]
    (c : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1)
    (hc : Function.Surjective c) (f : C(ProductTorus 2, G))
    (hf : ∀ x y, f (x + y) = f x + f y) :
    SingularMayerVietoris.singularHomologyMap f 2 (productTorusTopClass 2) ∈
      LinearMap.range (PeriodTorusHigherHomologyPontryagin.wedgeTwoAlong G c)
  -- de-pins `map_topClass_two_mem_range_latticeWedgeTwo` (6178)
theorem PeriodTorusHigherHomology.map_topClass_three_mem_range_wedgeThreeAlong {G : Type}
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    {M : Type} [AddCommGroup M] [Module ℤ M]
    (c : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1)
    (hc : Function.Surjective c) (f : C(ProductTorus 3, G))
    (hf : ∀ x y, f (x + y) = f x + f y) :
    SingularMayerVietoris.singularHomologyMap f 3 (productTorusTopClass 3) ∈
      LinearMap.range (PeriodTorusHigherHomologyPontryagin.wedgeThreeAlong G c)
  -- de-pins `map_topClass_three_mem_range_latticeWedgeThree` (6189)

-- the surjectivity/descend-to-range family (6784–6824), de-pinned; all in J-C3:
theorem PeriodTorusHigherHomology.coordinateTorusClassAlong_mem_range_wedgeTwoAlong
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] {r : ℕ}
    (e : G ≃ₜ ProductTorus r) (he : ∀ x y, e (x + y) = e x + e y)
    {M : Type} [AddCommGroup M] [Module ℤ M]
    (c : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1)
    (hc : Function.Surjective c) (i : Fin (r.choose 2)) :
    coordinateTorusClassAlong e 2 i ∈
      LinearMap.range (PeriodTorusHigherHomologyPontryagin.wedgeTwoAlong G c)
  -- de-pins `coordinateTorusClassAlong_mem_range_latticeWedgeTwo` (6784); depends on
  -- `coordinateTorusMapAlong_add` (J-B2a public helper; exact signature above)
theorem PeriodTorusHigherHomology.coordinateTorusClassAlong_mem_range_wedgeThreeAlong
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] {r : ℕ}
    (e : G ≃ₜ ProductTorus r) (he : ∀ x y, e (x + y) = e x + e y)
    {M : Type} [AddCommGroup M] [Module ℤ M]
    (c : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1)
    (hc : Function.Surjective c) (i : Fin (r.choose 3)) :
    coordinateTorusClassAlong e 3 i ∈
      LinearMap.range (PeriodTorusHigherHomologyPontryagin.wedgeThreeAlong G c)
  -- de-pins `coordinateTorusClassAlong_mem_range_latticeWedgeThree` (6795)
theorem PeriodTorusHigherHomology.wedgeTwoAlong_surjective_of_torusHomeomorph {G : Type}
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] {r : ℕ}
    (e : G ≃ₜ ProductTorus r) (he : ∀ x y, e (x + y) = e x + e y)
    {M : Type} [AddCommGroup M] [Module ℤ M]
    (c : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1)
    (hc : Function.Surjective c) :
    Function.Surjective (PeriodTorusHigherHomologyPontryagin.wedgeTwoAlong G c)
  -- de-pins `latticeWedgeTwo_surjective_of_torusHomeomorph` (6806)
theorem PeriodTorusHigherHomology.wedgeThreeAlong_surjective_of_torusHomeomorph {G : Type}
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] {r : ℕ}
    (e : G ≃ₜ ProductTorus r) (he : ∀ x y, e (x + y) = e x + e y)
    {M : Type} [AddCommGroup M] [Module ℤ M]
    (c : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1)
    (hc : Function.Surjective c) :
    Function.Surjective (PeriodTorusHigherHomologyPontryagin.wedgeThreeAlong G c)
  -- de-pins `latticeWedgeThree_surjective_of_torusHomeomorph` (6816)
```

## Boundary J-D — `Lib/AlgebraicTopology/SingularHomology/TorusExterior.lean`

```text
commit_boundary   J-D — NOT GO; needs J-A + J-B2b + J-C3 (degrees 2, 3 at rank r).
                  New degree-three signatures elaborate with provisional inputs,
                  not with a landed Torus/Pontryagin production provider.
imports           Mathlib; Lib.AlgebraicTopology.SingularHomology.{Torus, Pontryagin};
                  Lib.LinearAlgebra.ExteriorPower.MinorCoordinates
visibility        `module` file; outputs `public` inside `namespace Mathoverflow1973`
source            Theorem A second half (§6)
destination       Lib/AlgebraicTopology/SingularHomology/TorusExterior.lean
focused_check     `lake build Lib.AlgebraicTopology.SingularHomology.TorusExterior`
return_seam       Axis 5 if the Orzech step or basis-hit argument drifts
```

Public outputs — the rank-4 decls generalized to `(r : ℕ)`:

```lean
def PeriodTorusHigherHomology.coordinateTorusWedgeTwo (r : ℕ) :
    (⋀[ℤ]^2 (Fin r → ℤ)) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (ProductTorus r) 2
  -- generalizes 6949; body `wedgeTwoAlong (ProductTorus r) (coordinateH1 r)`
  -- with `letI := productTorus_homology_torsionFree r 2`
@[simp]
theorem PeriodTorusHigherHomology.coordinateTorusWedgeTwo_apply_ιMulti (r : ℕ)
    (v : Fin 2 → Fin r → ℤ) :
    coordinateTorusWedgeTwo r (exteriorPower.ιMulti ℤ 2 v) =
      PeriodTorusHigherHomologyPontryagin.product11 (ProductTorus r)
        (coordinateH1 r (v 0)) (coordinateH1 r (v 1))              -- generalizes Specialization 6964
theorem PeriodTorusHigherHomology.coordinateTorusWedgeTwo_matrix (r : ℕ)
    (A : Matrix (Fin r) (Fin r) ℤ) :
    (SingularMayerVietoris.singularHomologyMap (torusMatrixMap A) 2).comp
        (coordinateTorusWedgeTwo r) =
      (coordinateTorusWedgeTwo r).comp (exteriorPower.map 2 A.mulVecLin)
  -- generalizes `coordinateTorusWedgeTwo_matrix` (7009) — via `wedgeTwoAlong_natural`
  -- (J-C3) with the NEW rank-general `coordinateH1_matrix_natural` (J-B2b, blocked identification seam) as `hmark`;
  -- no `PeriodDomain` input
theorem PeriodTorusHigherHomology.coordinateTorusWedgeTwo_surjective (r : ℕ) :
    Function.Surjective (coordinateTorusWedgeTwo r)
  -- generalizes 7037 — via `wedgeTwoAlong_surjective_of_torusHomeomorph`
  -- (Homeomorph.refl _) (fun _ _ => rfl) (coordinateH1 r) (coordinateH1_surjective r)
theorem PeriodTorusHigherHomology.coordinateTorusWedgeTwo_bijective (r : ℕ) :
    Function.Bijective (coordinateTorusWedgeTwo r)
  -- generalizes 7051 — Orzech + exteriorPower_finrank_choose (J-A) +
  -- productTorus_homology_finrank (J-B)
def PeriodTorusHigherHomology.coordinateTorusWedgeTwoEquiv (r : ℕ) :
    (⋀[ℤ]^2 (Fin r → ℤ)) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (ProductTorus r) 2    -- generalizes 7069
def PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv (r : ℕ) :
    SingularMayerVietoris.SingularHomology (ProductTorus r) 2 ≃ₗ[ℤ]
      (⋀[ℤ]^2 (Fin r → ℤ))                                        -- generalizes 7079
theorem PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv_wedge (r : ℕ)
    (v : ⋀[ℤ]^2 (Fin r → ℤ)) :
    coordinateTorusH2ExteriorEquiv r (coordinateTorusWedgeTwo r v) = v
                                                                   -- generalizes 7090
theorem PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv_matrix (r : ℕ)
    (A : Matrix (Fin r) (Fin r) ℤ)
    (a : SingularMayerVietoris.SingularHomology (ProductTorus r) 2) :
    coordinateTorusH2ExteriorEquiv r
        (SingularMayerVietoris.singularHomologyMap (torusMatrixMap A) 2 a) =
      exteriorPower.map 2 A.mulVecLin (coordinateTorusH2ExteriorEquiv r a)
  -- generalizes 7110 — the `Elliptic.examplePeriod .four` marking inside the current
  --  proof is project data; the general proof uses `coordinateTorusWedgeTwo_matrix r`
  --  (above) + surjectivity, no `PeriodDomain` input
def PeriodTorusHigherHomology.coordinateTorusH2Coordinates (r : ℕ) :
    SingularMayerVietoris.SingularHomology (ProductTorus r) 2 ≃ₗ[ℤ]
      (Fin (r.choose 2) → ℤ)
  -- generalizes 7136 — body `(coordinateTorusH2ExteriorEquiv r).trans
  --   (standardExteriorCoordinates r 2)` (J-A)
theorem PeriodTorusHigherHomology.coordinateTorusH2Coordinates_matrix (r : ℕ)
    (A : Matrix (Fin r) (Fin r) ℤ)
    (a : SingularMayerVietoris.SingularHomology (ProductTorus r) 2) :
    coordinateTorusH2Coordinates r
        (SingularMayerVietoris.singularHomologyMap (torusMatrixMap A) 2 a) =
      PeriodTorusHigherHomologyExterior.exteriorMinorMatrix r r 2 A *ᵥ coordinateTorusH2Coordinates r a
  -- generalizes 7144 — `LocalSystemMatrices.exteriorSquare A` is replaced by
  -- `PeriodTorusHigherHomologyExterior.exteriorMinorMatrix r r 2 A` (J-A).
  -- At r=4, agreement additionally requires the retained Hopf subset-enumeration
  -- compatibility equations from J-A's order pinning; the minor formula alone is insufficient.

def PeriodTorusHigherHomology.coordinateTorusWedgeThree (r : ℕ) :
    (⋀[ℤ]^3 (Fin r → ℤ)) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (ProductTorus r) 3
  -- Specialization 6956; wedgeThreeAlong with coordinateH1 and the H2 torsion-free instance.
@[simp]
theorem PeriodTorusHigherHomology.coordinateTorusWedgeThree_apply_ιMulti (r : ℕ)
    (v : Fin 3 → Fin r → ℤ) :
    coordinateTorusWedgeThree r (exteriorPower.ιMulti ℤ 3 v) =
      PeriodTorusHigherHomologyPontryagin.tripleProduct (ProductTorus r)
        (coordinateH1 r (v 0)) (coordinateH1 r (v 1)) (coordinateH1 r (v 2))
  -- Specialization 6976.
theorem PeriodTorusHigherHomology.coordinateTorusWedgeThree_matrix (r : ℕ)
    (A : Matrix (Fin r) (Fin r) ℤ) :
    (SingularMayerVietoris.singularHomologyMap (torusMatrixMap A) 3).comp
        (coordinateTorusWedgeThree r) =
      (coordinateTorusWedgeThree r).comp (exteriorPower.map 3 A.mulVecLin)
  -- Specialization 7022; consumes wedgeThreeAlong_natural and J-B2b matrix naturality.
theorem PeriodTorusHigherHomology.coordinateTorusWedgeThree_surjective (r : ℕ) :
    Function.Surjective (coordinateTorusWedgeThree r)
  -- Specialization 7044; consumes wedgeThreeAlong_surjective_of_torusHomeomorph.
theorem PeriodTorusHigherHomology.coordinateTorusWedgeThree_bijective (r : ℕ) :
    Function.Bijective (coordinateTorusWedgeThree r)
  -- Specialization 7060; Orzech with J-A/J-B rank and free/finite instances.
def PeriodTorusHigherHomology.coordinateTorusWedgeThreeEquiv (r : ℕ) :
    (⋀[ℤ]^3 (Fin r → ℤ)) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (ProductTorus r) 3
  -- Specialization 7074.
def PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv (r : ℕ) :
    SingularMayerVietoris.SingularHomology (ProductTorus r) 3 ≃ₗ[ℤ]
      (⋀[ℤ]^3 (Fin r → ℤ))
  -- Specialization 7084.
theorem PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv_wedge (r : ℕ)
    (v : ⋀[ℤ]^3 (Fin r → ℤ)) :
    coordinateTorusH3ExteriorEquiv r (coordinateTorusWedgeThree r v) = v
  -- Specialization 7096.
theorem PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv_matrix (r : ℕ)
    (A : Matrix (Fin r) (Fin r) ℤ)
    (a : SingularMayerVietoris.SingularHomology (ProductTorus r) 3) :
    coordinateTorusH3ExteriorEquiv r
        (SingularMayerVietoris.singularHomologyMap (torusMatrixMap A) 3 a) =
      exteriorPower.map 3 A.mulVecLin (coordinateTorusH3ExteriorEquiv r a)
  -- Specialization 7123; consumes the wedge matrix law and surjectivity.
def PeriodTorusHigherHomology.coordinateTorusH3Coordinates (r : ℕ) :
    SingularMayerVietoris.SingularHomology (ProductTorus r) 3 ≃ₗ[ℤ]
      (Fin (r.choose 3) → ℤ)
  -- Specialization 7140; exterior equivalence followed by J-A coordinates.
theorem PeriodTorusHigherHomology.coordinateTorusH3Coordinates_matrix (r : ℕ)
    (A : Matrix (Fin r) (Fin r) ℤ)
    (a : SingularMayerVietoris.SingularHomology (ProductTorus r) 3) :
    coordinateTorusH3Coordinates r
        (SingularMayerVietoris.singularHomologyMap (torusMatrixMap A) 3 a) =
      PeriodTorusHigherHomologyExterior.exteriorMinorMatrix r r 3 A *ᵥ
        coordinateTorusH3Coordinates r a
  -- Specialization 7158; rectangular J-A API instantiated at p = m = r.

-- the §6 headline, at degrees 2 and 3 (rank-r generalization; the general-degree-n
-- version is deferred to J-E):
def PeriodTorusHigherHomology.productTorusWedgeTwoEquiv (r : ℕ) :
    (⋀[ℤ]^2 (SingularMayerVietoris.SingularHomology (ProductTorus r) 1)) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (ProductTorus r) 2
  -- body: homologyWedgeTwo upgraded by LinearEquiv.ofBijective via
  -- wedgeTwoAlong_surjective_of_torusHomeomorph (refl) ∘ coordinateH1_bijective-iso
  -- transport: equivalently (wedgeTwoAlong (ProductTorus r) (coordinateH1 r))-conjugate
  -- of coordinateTorusWedgeTwoEquiv under the exterior map of coordinateH1Equiv
def PeriodTorusHigherHomology.productTorusWedgeThreeEquiv (r : ℕ) :
    (⋀[ℤ]^3 (SingularMayerVietoris.SingularHomology (ProductTorus r) 1)) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (ProductTorus r) 3
```

The rank-3 re-run in `Hopf/LCP/BoundaryTopology.lean` is deleted and re-routed to these
general statements.

## Deferred boundary J-E — general-`n` wedge (NOT GO; missing inputs enumerated)

```text
commit_boundary   J-E — deferred; no Axis-6 handoff authorized.
class             FREE
source            Theorems C/A, §§5–6; n-fold product and alternating descent.
destination       Pontryagin.lean (product/descent); TorusExterior.lean (torus equiv);
                  CrossProduct.lean (C/GLM-owned prerequisite statements).
visibility        Intended module/public declarations inside Mathoverflow1973.
imports           Intended Mathlib + public MayerVietoris/CrossProduct/Torus providers;
                  only the current Lib-only provisional context has been checked.
dependencies      M-C; general cross product, transported swap/associativity;
                  n-fold unit/recursion and torus basis-image/rank interfaces not landed.
consumer          exteriorMap then productTorusExteriorEquiv.
focused_check     After prerequisites: lake build Lib.AlgebraicTopology.SingularHomology.TorusExterior
return_seam       Axis 3 for the uncompleted n-fold decomposition; Axis 5 for provider alignment.
```

Review-3 check: the degree transports below are explicit linear maps, and the two
coherence statements elaborate in a module with signature-only prerequisite inputs.
`homologyDegreeCast` and its reflexive identity were checked with actual terms.
This is type alignment only; no general cross product or coherence proof was constructed.

The §5–§6 statements at general `n` —
`Pontryagin.exteriorMap (G : Type) [TopologicalSpace G] [AddCommGroup G]
[IsTopologicalAddGroup G] [Module.IsTorsionFree ℤ (SH G 2)] (n : ℕ) :
(⋀[ℤ]^n (SH G 1)) →ₗ[ℤ] SH G n` and
`productTorusExteriorEquiv (r n : ℕ) : (⋀[ℤ]^n (SH (ProductTorus r) 1)) ≃ₗ[ℤ]
SH (ProductTorus r) n` —
need an `n`-fold iterated product and its alternating descent. The landed inputs are
insufficient: `crossProductHomology_swap` exists only at `(1,1)` (Specialization 4172)
and `crossProductHomology_associative` only at `(1,1,1)` (5949). Exact missing inputs:

```lean
noncomputable def PeriodTorusHigherHomology.homologyDegreeCast (X : Type)
    [TopologicalSpace X] {m n : ℕ} (h : m = n) :
    SingularMayerVietoris.SingularHomology X m →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology X n := by
  subst n
  exact LinearMap.id

theorem PeriodTorusHigherHomology.homologyDegreeCast_refl (X : Type)
    [TopologicalSpace X] (n : ℕ) :
    homologyDegreeCast X (rfl : n = n) = LinearMap.id
  -- representation-only proof: rfl; checked in the review-3 module probe.

-- C-owned follow-up (with the general (p,q) cross product):
def PeriodTorusHigherHomology.crossProductHomology' (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (p q : ℕ) :
    SingularMayerVietoris.SingularHomology X p →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology Y q →ₗ[ℤ]
        SingularMayerVietoris.SingularHomology (X × Y) (p + q)

-- GLM-owned, inside the G-J3 coherence suite at general degrees:
theorem PeriodTorusHigherHomology.crossProductHomology_swap' {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (p q : ℕ)
    (a : SingularMayerVietoris.SingularHomology X p)
    (b : SingularMayerVietoris.SingularHomology Y q) :
    SingularMayerVietoris.singularHomologyMap
        (Homeomorph.prodComm X Y : C(X × Y, Y × X)) (p + q)
        (crossProductHomology' X Y p q a b) =
      homologyDegreeCast (Y × X) (Nat.add_comm q p)
        ((-1 : ℤ)^(p * q) • crossProductHomology' Y X q p b a)
theorem PeriodTorusHigherHomology.crossProductHomology_associative' {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (p q r : ℕ)
    (a : SingularMayerVietoris.SingularHomology X p)
    (b : SingularMayerVietoris.SingularHomology Y q)
    (c : SingularMayerVietoris.SingularHomology Z r) :
    SingularMayerVietoris.singularHomologyMap
        (Homeomorph.prodAssoc X Y Z : C((X × Y) × Z, X × (Y × Z))) (p + q + r)
        (crossProductHomology' (X × Y) Z (p + q) r
          (crossProductHomology' X Y p q a b) c) =
      homologyDegreeCast (X × (Y × Z)) (Nat.add_assoc p q r).symm
        (crossProductHomology' X (Y × Z) p (q + r) a
          (crossProductHomology' Y Z q r b c))
  -- equation form generalizes the (1,1,1) instance at Specialization 5949

-- J-owned, built on those:
def PeriodTorusHigherHomologyPontryagin.nfoldProduct (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G] (n : ℕ) :
    MultilinearMap ℤ (fun _ : Fin n => SingularMayerVietoris.SingularHomology G 1)
      (SingularMayerVietoris.SingularHomology G n)
theorem PeriodTorusHigherHomologyPontryagin.nfoldProduct_alternating (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] (n : ℕ) :
    -- nfoldProduct G n vanishes whenever two arguments coincide
    -- (its AlternatingMap upgrade then descends through
    --  exteriorPower.alternatingMapLinearEquiv to `exteriorMap`):
    ∀ v : Fin n → SingularMayerVietoris.SingularHomology G 1,
      (∃ i j, i ≠ j ∧ v i = v j) → nfoldProduct G n v = 0
def PeriodTorusHigherHomologyPontryagin.exteriorMap (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] (n : ℕ) :
    (⋀[ℤ]^n (SingularMayerVietoris.SingularHomology G 1)) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology G n
def PeriodTorusHigherHomology.productTorusExteriorEquiv (r n : ℕ) :
    (⋀[ℤ]^n (SingularMayerVietoris.SingularHomology (ProductTorus r) 1)) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (ProductTorus r) n
```

J-E is returned to the Axis-3/decomposition seam: it waits on the same general-`(p,q)`
cross-product follow-up that already defers the general Pontryagin product. Owner
confirmation: whether the `n`-fold descent is J's once the coherence inputs land, or
folds into GLM's cross-product boundary.

## GLM exclusion manifest (G-J3)

Review-3 census was generated from `git show 15bd5f7:Hopf/LCP/Specialization.lean`:
number source lines, restrict to 3771–5987 inclusive, match declaration starts with
`^(?:noncomputable )?(?:theorem|def|lemma|instance|abbrev) (PeriodTorusHigherHomology\.[^\s({:]+)`.
This yields **110** excluded declarations (not Pontryagin-namespace declarations
interleaved in the same range). Expanding the suffix groups below reproduces this
name/line census. `chainTrilinearMap_ext` is included; all line numbers are declaration
starts rather than attribute lines. The exact script command is in the review-3 receipt.

J claims **no** declaration in `Hopf/LCP/Specialization.lean` lines 3771–5987 belonging
to the cross-product coherence suite. Exact excluded names (all `PeriodTorusHigherHomology.*`,
all currently in that range, destination `CrossProduct.lean` under GLM):
`formalMap_comp` (3771), `formalMap_prod_swap` (3783),
`formalMap_swap_pointCrossProduct_one` (3792), `formalMap_swap_edgeCrossProduct_zero`
(3824), `formalEdgeSwapDefect` + `_apply` (3856/3863), `formalBoundary_edgeSwapDefect`
(3870), `formalMap_edgeSwapDefect` (3878), `formalEdgeSwapHomotopy` (3887) +
`_simplex` (3896) + `_boundary` (3905), `formalMap_edgeSwapHomotopy` (3919),
`prodSwap_productAffineSimplex` (3941), `inducedChain_swap_productAffineChainMap` (3952),
`inducedChain_prodMap_swap` (3979), `crossProductSwapHomotopy` (3994) + `_simplex` (4008)
+ `_natural` (4022) + `_affineChainMap` (4044) + `_boundary_affine` (4078) +
`_boundary` (4100), `crossProductCycleClasses_add_swap_eq_zero` (4128),
`crossProductHomology_add_swap_eq_zero` (4154), `crossProductHomology_swap` (4172),
`crossProductHomology_pushforward_anticommute` (4183), `formalMap_comp_apply` (4451),
`integerTrilinearPostcompose` + `_apply` (4288/4314), `integerTrilinearPrecompose` +
`_apply` (4323/4350), `integerTrilinearLeftAssociated` (4360),
`integerTrilinearRightAssociated` (4385), `chainTrilinearLift` (4408) +
`chainTrilinearLift_simplex` (4420), `chainTrilinearMap_ext` (4434; call sites
5094/5447/5478) — generic-looking but used **only** by the
associator-homotopy machinery (5028–5486); they move with the suite, not with J-C.
`formalMap_id_apply` (4463), `formalEdgeCrossProduct_point_left`/`_middle` (4473/4492),
`formalTriangleCrossProduct_point_right` (4513), `formalChains_trilinear_ext` (4532),
`formalTrilinearLift` + `_simplex` (4550/4558), `formalAssociatorDefect` (4565) +
`_apply` (4581) + `_zero` (4591), `formalBoundary_associatorDefect` (4596),
`formalMap_prodAssoc_naturality` (4607), `formalMap_associatorDefect` (4625),
`formalAssociatorHomotopy` (4667) + `_zero` (4685) + `_simplex_succ` (4691) +
`_boundary_zero` (4704) + `_boundary` (4711), `formalMap_associatorHomotopy` (4799),
`tripleAffineSimplex` + `_face` (4841/4850), `tripleAffineChainMap` (4868) +
`_simplex` (4877) + `_boundary` (4885), `affineProductLeft`/`Right` + `_comp`
(4922–4959), `inducedChain_affineProductLeft`/`Right` (4979/5000),
`crossProductAssociatorDefect` (5023) + `_apply` (5036) + `_natural` (5125),
`crossProductAssociatorHomotopy` (5047) + `_simplex` (5063) + `_natural` (5079) +
`_affineChainMap` (5329) + `_boundary_zero_affine` (5390) + `_boundary_affine` (5410) +
`_boundary_zero` (5437) + `_boundary` (5463) + `_boundary_of_cycle` (5495),
`inducedChain_prodAssoc_natural` (5108), `productAffineSimplex_stdVertices_image` (5139),
`prodMap_tripleAffineSimplex` (5147), `inducedChain_tripleAffineChainMap` (5178),
`crossProductTriangle_productAffineChainMap_left` (5218),
`crossProductEdge_productAffineChainMap_right` (5286),
`crossProductAssociatorDefect_affineChainMap` (5375),
`formalMap_swap_pointCrossProduct_two` (5510), `formalMixedSwapDefect` + `_apply`
(5543/5550), `formalBoundary_mixedSwapDefect` (5557), `formalMap_mixedSwapDefect` (5566),
`formalMixedSwapHomotopy` (5575) + `_simplex` (5587) + `_boundary` (5599),
`formalMap_mixedSwapHomotopy` (5632), `crossProductMixedSwapHomotopy` (5656) +
`_simplex` (5670) + `_natural` (5684) + `_affineChainMap` (5706) + `_boundary_affine`
(5740) + `_boundary` (5767) + `_boundary_of_cycle` (5800), `crossProductTwoOneCycles`
(5811) + `_val` (5862), `crossProductHomologyTwoOne` (5871) + `_apply` (5882) +
`_cycleClass` (5893), `crossProductCycleClasses_associative` (5923),
`crossProductHomology_associative` (5949), `crossProductCyclicMap` (5972) +
`_assoc_swap` (5978), `crossProductHomology_cyclic` (5987).
(The suite is 110 declarations; the earlier "42" figure was a first-pass count of the
named families only — the manifest above is the exclusion list.)

## J-charged (stays in `Hopf/`)

`Hopf/FiniteCore.lean:339–392` (`squareA₁`, `cubeM₀_eq`, and the `by decide`
instantiations) stays; after J-A lands, its proofs become one-line instantiations of
`standardExterior_map_coefficient`. The rank-4 `PeriodDomain`/`RealTorus₄`/`flatTorus*`
adapters (`realTorusHomologyEquiv` 6504, `periodTorusHomologyEquiv` 6508,
`realTorusH4Equiv` 6551, `realTorus_homology_*` 6522–6546, `flatTorusCircleHomeomorph_add`
3441, `periodTorusCircle_inducedHomology_periodLoop` 3446, `coordinateH1_four_*`
6912–6929) stay in `Hopf/` as thin adapters — they consume the generalized J-B/J-D API
at `r = 4`.

---

# Open items, seams, probes

1. **Seams — all landed at head `f034c13`.** Lane A's API is in
   `Lib/AlgebraicTopology/SingularHomology/`: the abbrev
   `SingularMayerVietoris.SingularHomology` (`MayerVietoris.lean:853`),
   `SingularMayerVietoris.singularHomologyMap` (`MayerVietoris.lean:856`),
   the $S^1 \times Y$ splitting `SingularHomology.circleProductHomologyEquiv`
   (`CircleProduct.lean:798`, formerly SphereTopology 2191) with
   `circleSectionHomology`/`circleProjectionHomology`/`circleBoundaryCoordinates`, and
   `SingularHomology.{connectedHomologyZeroEquiv, totallyDisconnected_homology_subsingleton,
   homeomorphHomologyEquiv}` (`HomotopyInvariance.lean:223, 233, 164`). Lane C: the cross
   product `PeriodTorusHigherHomology.crossProductHomology` at `(1, n)`
   (`CrossProduct.lean:1689`) plus boundary laws; the swap/associator coherence suite is
   still under `Hopf/LCP/Specialization.lean` pending GLM's G-J3 move. **Unlanded seam
   (recorded per the axis-5 review):** `crossProductHomology_natural`
   (`Hopf/LCP/CuspFilling.lean:14526`, together with `crossProductCycles_natural` 14509
   and `crossProductHomology_snd` 14549) is still Hopf-internal — it is part of the
   circle-path/cross-product-naturality cluster that gates J-B2 and J-C2 (see the
   Axis-5 boundaries above). Probe
   commands (first-pass receipt, runnable at head `f034c13`):
   `lake env lean Lib/AlgebraicTopology/SingularHomology/J_InterfaceCheck.lean`,
   likewise the consumer probe; receipt at `Lib/docs/J-INTERFACE_RECEIPT.md`. A
   aggregate probe against the final revised ledger — in the production `module`/`public`
   context and in destination namespaces, with a separate consumer — is required
   **before GO and before implementation**, not as landing work. Review-3 checks and
   limitations are recorded separately in the receipt.
2. **Pontryagin product shape — settled 2026-09-12.** The lane states `product` at `(1, n)`
   matching the landed cross product; general `(p, q)` is a named follow-up once C's general
   cross product lands (boundary J-C / deferred J-E).
3. **Q4 note** (minor formula exists outside the tree): moved as-is; de-duplication is the
   owner's call.
4. **`PeriodTorusHigherHomology.rightTranslation`** is defined in
   `Hopf/LCP/BoundaryTopology.lean:14298`, far from the torus API: at landing, check
   whether it belongs to `Torus.lean`; recorded here because it sits outside the lane's
   named ranges.
5. **Duplications to delete at landing**: `formalMap_comp` = `formalMap_comp_apply`
   (Specialization 3771 vs 4451, identical statements); `productTorusHomologyEquiv_succ_pair`
   (Specialization 6439) is an exact alias of CuspFilling's `productTorusHomologyEquiv_succ_apply`.
6. **Bib keys.** `hatcher02` exists in the pinned Mathlib bib. Hirsch/Milnor keys are not needed
   for this lane.
7. **Citation flag for the owner.** The task file names this lane "Hatcher Ex. 2.48,
   Cor. 3.28, §3.C". Corollary 3.28 of Hatcher is the manifold-torsion corollary (torsion in
   $H_{n-1}$ of a closed $n$-manifold), not the torus computation; the correct references for
   this lane's content are Example 3.16 (the exterior-algebra ring computation) and §3.C
   Exercise 11 ($H_*(T^n;\mathbb{Z}) \cong \Lambda_\mathbb{Z}[x_1,\dots,x_n]$, $|x_i| = 1$),
   plus §3.B for the Künneth ranks and Ex. 2.48 for the Wang sequence. This document uses the
   corrected citations; no content change.
8. **Review.** Two independent reviews now exist for this lane. (a) Stage-2 review of
   §§1–8: done; the report (six corrections, four remarks, all incorporated in the
   current text) is held off-tree (Kimi seat's `~/s6-notes/J-review.md`; durable copy at
   the Muse seat's `~/s6-notes/kimi-notes/J-review.md`) and is committed into the tree
   as `Lib/docs/J-review.md` with the reviewer named — pending the owner confirming the
   reviewer's identity. (b) Axis-5 review of the first-pass ledger + probes by seat
   `devin-axis5-j` (GPT-6 Astra): **NO-GO**, nine findings — universe-0 vs `Type*` in the
   two proposed signatures, missing namespace/elaboration context and ChallengeNode
   fields, a genuine typed gap behind the general-`n` wedge descent, literal `…`s in
   signatures, stale ownership wording ("J appends G-J3"), the J7/J8 dependency order,
   and off-by-one source coordinates. All findings verified against the sources and
   incorporated into the present second-pass ledger (revision note at the top of the
   Axis-5 section). The review text is held off-tree at
   `~/s6-notes/J-review-devin-axis5-j.md` and is committed as
   `Lib/docs/J-axis5-review.md` alongside (a). A re-review of this revised ledger is
   outstanding before J's Axis-6 work starts.
