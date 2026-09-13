# Lane C — textbook, decomposition, placement, and typed ledger

**The Hurewicz theorem in every degree** (Hatcher, *Algebraic Topology*, Theorem 4.32),
generalized from the five pinned proofs `SecondHurewicz` … `SixthHurewicz` to a single
theorem at every `n ≥ 2`.

This file contains, in order:

* **Axis 1** (§§1–16): the complete textbook proof of the general statement, in ordinary
  mathematical language. No Lean names occur in these sections.
* **Axes 2–3** (§17): the additive decomposition into named lemmas, in dependency order.
* **Axis 4** (§18): file placement under `Lib/` with the Mathlib twin of each file.
* **Axis 5** (§19): the current typed ledger, checked at `37fc1de8`, followed by the explicitly
  superseded pre-landing plan. The aggregate interface receipt is `C-INTERFACE_RECEIPT.md`.
* **Current limitations and provenance** appear after the live signatures. Historical open
  items are retained only as part of the superseded plan.

---

# Axis 1 — the textbook proof

## 1. The theorem

**Theorem (Hurewicz; Hatcher Thm. 4.32).**
Let $n \geq 2$ and let $(X, x)$ be a pointed topological space which is *$(n-1)$-connected*:
path connected, simply connected, and $\pi_k(X, x) = 0$ for $2 \leq k < n$.
Then the Hurewicz homomorphism

$$h_n \colon \pi_n(X, x) \longrightarrow H_n(X; \mathbb{Z}),$$

which sends the class of a based cube $p \colon (I^n, \partial I^n) \to (X, x)$ to the homology
class of its triangulated singular chain (§11), is an isomorphism of abelian groups; and
$H_k(X;\mathbb{Z}) = 0$ for $1 \leq k < n$.

Three remarks on the shape of the statement.

* For $n = 2$ the range $2 \leq k < n$ is empty: the hypothesis is simple connectivity alone.
  The proof below is uniform in $n \geq 2$; nothing is case-split on the degree.
* The group $\pi_n$ is abelian for $n \geq 2$ (Eckmann–Hilton), and $h_n$ is a homomorphism
  (§11.3); since every homomorphism between abelian groups is $\mathbb{Z}$-linear, the theorem
  is equivalently a $\mathbb{Z}$-linear equivalence
  $\mathrm{Additive}(\pi_n(X,x)) \simeq_{\mathbb{Z}} H_n(X;\mathbb{Z})$. This is the shape the
  Lean statement takes.
* The vanishing $H_k(X) = 0$ for $1 \leq k < n$ is proved by the same machine that proves
  surjectivity, run at degree $k$ (§14). For $k = 1$ it is the degree-one Hurewicz theorem
  (Hatcher Thm. 2A.1; already in the library as the reference example) applied to
  $\pi_1(X, x) = 0$.

The proof occupies §§2–16. Everything is developed at arbitrary degree $n$; the two places
where the existing formalization unrolls a construction degree by degree — the chain identity
of §3 and the normalization tower of §8 — are proved here once and for all by induction, and
those two proofs are exactly the new mathematics of this lane.

## 2. Conventions and standing inputs

**Singular chains.** $\Delta^m = \{s \in \mathbb{R}^{m+1} : s_i \geq 0,\ \sum_i s_i = 1\}$ is the
standard simplex, with vertices $e_0, \dots, e_m$ and face embeddings
$\delta^i \colon \Delta^{m-1} \to \Delta^m$ (the affine map omitting $e_i$), $0 \leq i \leq m$.
$C_m(Y)$ is the free abelian group on the singular $m$-simplices $\tau \colon \Delta^m \to Y$,
with $\partial \tau = \sum_{i=0}^m (-1)^i\, \tau \circ \delta^i$. A simplex is *degenerate* if
it factors through a face projection $\Delta^m \to \Delta^{m-1}$; degenerate simplices span a
subcomplex $D_*(Y)$ with $H_*(D_*(Y)) = 0$, and the *normalized* complex
$C^N_*(Y) = C_*(Y)/D_*(Y)$ computes $H_*(Y)$ (this is a standard acyclicity lemma; in the
library it is part of the singular-chains API, lane A). A singular simplex of positive
dimension that is constant is degenerate; this is the only consequence of the normalization
that we use, and we use it constantly: *any positive-dimensional constant simplex is zero in
$C^N_*(Y)$.*

**Cubes and homotopy groups.** $I = [0,1]$, $I^n$ the $n$-cube, $\partial I^n$ its boundary.
$\pi_n(X, x)$ is the set of homotopy classes rel $\partial I^n$ of maps
$p \colon (I^n, \partial I^n) \to (X, x)$, with composition by concatenation in the first
coordinate,
$$(p \cdot q)(t_1, \dots, t_n) = p(2t_1, t_2, \dots) \ \ (t_1 \leq \tfrac12), \qquad
  (p \cdot q)(t_1, \dots, t_n) = q(2t_1 - 1, t_2, \dots)\ \ (t_1 \geq \tfrac12),$$
the class of the constant map $x$ as zero, and reversal $t_1 \mapsto 1 - t_1$ as inverse. For
$n \geq 2$ this group is abelian (Eckmann–Hilton in the second coordinate).

**Fundamental classes.** $H_n(I^n, \partial I^n; \mathbb{Z}) \cong \mathbb{Z}$, and we fix the
generator $[I^n]$ (the *fundamental class*) once and for all by $[I^1] = $ the class of the
affine homeomorphism $\Delta^1 \to I$ together with the product rule of §3.4. Similarly
$H_n(\Delta^n, \partial\Delta^n) \cong \mathbb{Z}$ with generator $[\Delta^n]$ the class of the
identity simplex. For a map $g \colon (I^n, \partial I^n) \to (I^n, \partial I^n)$ the *degree*
$\deg g \in \mathbb{Z}$ is defined by $g_*[I^n] = (\deg g)\,[I^n]$; local-degree computations
(Hatcher Prop. 2.30; the local-degree API of lane A) are used in §7 only.

**Standard inputs already in the library (lane A).** Functoriality, homotopy invariance
(Hatcher Thm. 2.10), the long exact sequence of a pair, excision, Mayer–Vietoris, the homology
of the sphere $H_*(S^n)$, the reduced/unreduced identification $H_n(X) \cong H_n(X, \{x\})$ for
$n \geq 1$, and the local-degree machine. Every use of these is named at the point of use.

**Basepoints.** All homotopies of based maps are rel the basepoint locus; we write
"$p \simeq p'$ rel $\partial I^n$" for a homotopy $I \times I^n \to X$ that is constant equal to
$x$ on $I \times \partial I^n$.

## 3. The Freudenthal–Kuhn triangulation of the cube

This section is the first of the two places where the formalization previously unrolled the
argument degree by degree (the chain identity 3.3 was proved separately at $n = 4$ and
$n = 5$). The proof given here is a single argument valid for every $n$; it is the
generalization **G1** of the lane.

**3.1 The triangulation.** For a permutation $\sigma \in S_n$ set
$$\Delta_\sigma := \{t \in I^n : t_{\sigma(1)} \geq t_{\sigma(2)} \geq \dots \geq t_{\sigma(n)}\}.$$
With $v_k^\sigma := e_{\sigma(1)} + \dots + e_{\sigma(k)} \in \mathbb{R}^n$ for
$0 \leq k \leq n$ (so $v_0^\sigma = 0$ and $v_n^\sigma = (1, \dots, 1)$), $\Delta_\sigma$ is the
convex hull of $v_0^\sigma, \dots, v_n^\sigma$: the point $t = \sum_k s_k v_k^\sigma$ of the
convex hull has coordinates $t_{\sigma(j)} = s_j + s_{j+1} + \dots + s_n$, which satisfy
$1 \geq t_{\sigma(1)} \geq \dots \geq t_{\sigma(n)} \geq 0$, and conversely every such $t$ is
recovered by $s_j = t_{\sigma(j)} - t_{\sigma(j+1)}$. The $n!$ simplices $\Delta_\sigma$ are the
maximal cells of a simplicial complex $K_n$ triangulating $I^n$: every point of $I^n$ lies in
some $\Delta_\sigma$ (sort its coordinates), two simplices meet in a common face (a
codimension-one face of $\Delta_\sigma$ is either a coordinate face $t_{\sigma(1)} = 1$ or
$t_{\sigma(n)} = 0$ of the cube, or a *braid hyperplane* $t_{\sigma(i)} = t_{\sigma(i+1)}$, which
is shared with exactly one other simplex, see 3.2), and the vertices of every face are among
the $v_k^\sigma$.

Write $A_\sigma \colon \Delta^n \to \Delta_\sigma \subseteq I^n$ for the affine homeomorphism
sending $e_k \mapsto v_k^\sigma$. Its linear part sends $e_k - e_{k-1} \mapsto e_{\sigma(k)}$, so
it is the permutation matrix of $\sigma$ and
$$\det(dA_\sigma) = \operatorname{sign}(\sigma);$$
$A_\sigma$ is orientation-preserving exactly for even $\sigma$.

**3.2 The face-incidence lemma.** The $i$-th face $A_\sigma \circ \delta^i$,
$0 \leq i \leq n$, is:

* ($i = 0$) the facet $t_{\sigma(1)} = 1$, lying on the cube face $\{t_{\sigma(1)} = 1\}$;
* ($i = n$) the facet $t_{\sigma(n)} = 0$, lying on the cube face $\{t_{\sigma(n)} = 0\}$;
* ($0 < i < n$) the facet $t_{\sigma(i)} = t_{\sigma(i+1)}$, which equals
  $A_{\sigma'} \circ \delta^i$ — *the same* singular $(n-1)$-simplex, with the *same* face index
  $i$ — for $\sigma' = \sigma \circ s_i$, where $s_i = (i\ \ i{+}1)$ is the adjacent
  transposition. Indeed $\sigma \circ s_i$ swaps the values in positions $i, i+1$, so the two
  vertex lists differ only in position $i$ ($v_i^{\sigma'} = v_{i-1}^\sigma + e_{\sigma(i+1)}$
  replaces $v_i^\sigma = v_{i-1}^\sigma + e_{\sigma(i)}$), and dropping vertex $i$ from both
  lists gives identical ordered lists, hence identical face maps.

Since $\operatorname{sign}(\sigma \circ s_i) = -\operatorname{sign}(\sigma)$, the two
contributions of this shared facet to $\partial \kappa_n$ (below) carry opposite total signs
$\operatorname{sign}(\sigma)(-1)^i$ and cancel.

**3.3 The chain identity.** Define the *triangulation chain* of the cube
$$\kappa_n := \sum_{\sigma \in S_n} \operatorname{sign}(\sigma)\, A_\sigma \ \in\ C_n(I^n).$$
**Theorem (chain identity, all $n$).** *The interior facets cancel in pairs, and*
$$\partial \kappa_n = \sum_{j=1}^n (-1)^{j-1}\big(\kappa^{(j,1)}_{n-1} - \kappa^{(j,0)}_{n-1}\big),$$
*where $\kappa^{(j,\varepsilon)}_{n-1}$ is the triangulation chain of the cube face
$\{t_j = \varepsilon\} \cong I^{n-1}$ (coordinates $t_1, \dots, \widehat{t_j}, \dots, t_n$ in
increasing index order). In particular $\kappa_n$ is a relative cycle of
$(I^n, \partial I^n)$.*

*Proof.* By 3.2 the faces with $0 < i < n$ cancel in pairs
$(\sigma, \sigma \circ s_i)$. The $i = 0$ faces are the facets $t_{\sigma(1)} = 1$; grouping by
$j = \sigma(1)$ and writing $\sigma = (j, \tau)$ with $\tau$ a permutation of the remaining
$n - 1$ coordinates, one has $\operatorname{sign}(\sigma) = (-1)^{j-1}\operatorname{sign}(\tau)$
(moving $j$ to the front of $(1, \dots, n)$ takes $j - 1$ transpositions), and the face map is
exactly $A_\tau$ on the face cube $\{t_j = 1\}$; the total sign is
$\operatorname{sign}(\sigma)(-1)^0 = (-1)^{j-1}\operatorname{sign}(\tau)$, giving
$(-1)^{j-1}\kappa^{(j,1)}_{n-1}$. The $i = n$ faces are the facets $t_{\sigma(n)} = 0$;
grouping by $j = \sigma(n)$ and writing $\sigma = (\tau, j)$ gives
$\operatorname{sign}(\sigma) = (-1)^{n-j}\operatorname{sign}(\tau)$ with total sign
$(-1)^{n-j}(-1)^n = (-1)^j = -(-1)^{j-1}$, giving $-(-1)^{j-1}\kappa^{(j,0)}_{n-1}$. $\square$

**3.4 The fundamental class.** $\kappa_1$ is the identity $\Delta^1 \to I$, the chosen
generator. Inducting on $n$ with 3.3: under the long exact sequence of the pair
$(I^n, \partial I^n)$ the boundary map
$\partial_* \colon H_n(I^n, \partial I^n) \to H_{n-1}(\partial I^n)$ is an isomorphism (the cube
is contractible), and 3.3 says $\partial_*[\kappa_n]$ is the class of the triangulation chain
of $\partial I^n$, which — by the standard computation of the homology of a sphere as an
iterated suspension, or directly by Mayer–Vietoris over the two hemispheres — is the generator
of $H_{n-1}(\partial I^n) \cong \mathbb{Z}$ once this holds for $\kappa_{n-1}$ on each face.
Hence $[\kappa_n] = [I^n]$, the fundamental class. (This is the only homology computation the
triangulation needs; it is lane A material — the homology of the sphere and the Mayer–Vietoris
sequence.)

**3.5 Remark — the shuffle point of view.** $I^n$ is the $n$-fold product
$\Delta^1 \times \dots \times \Delta^1$, and $K_n$ is the iterated *shuffle triangulation*: for
ordered simplices $\Delta^p, \Delta^q$, the product $\Delta^p \times \Delta^q$ is triangulated by
the $\binom{p+q}{p}$ *shuffle simplices* indexed by $(p,q)$-shuffles $\mu$ (order-preserving
reorderings of the $p$ "horizontal" and $q$ "vertical" steps), with signs
$\operatorname{sign}(\mu)$. For $\Delta^1 \times \Delta^1$ this is the diagonal cut of the
square; iterating gives exactly $K_n$, since a shuffle of $n$ one-step paths is a permutation.
The boundary formula 3.3 is the Leibniz rule
$\partial(a \times b) = \partial a \times b + (-1)^{\dim a} a \times \partial b$ for the shuffle
product, which is the same combinatorial computation as 3.2 (adjacent-transposition
cancellation). We use the shuffle product itself in §10 (the cross product) and its degenerate
case $\Delta^m \times \Delta^1$ in §6 (the prism).

## 4. The simplex–cube dictionary

**4.1 Lemma (homeomorphism of pairs).** *For each $m \geq 0$ there is a homeomorphism of pairs
$\varphi_m \colon (\Delta^m, \partial\Delta^m) \to (I^m, \partial I^m)$, natural in the sense
that faces go to (unions of) faces.*

*Proof.* Flatten $\Delta^m$ onto the flat simplex $F_m := \{v \in \mathbb{R}^m_{\geq 0} :
\sum_i v_i \leq 1\}$ by dropping the zeroth coordinate, then map $F_m$ onto the cube by the
radial rescaling $v \mapsto (\|v\|_1 / \|v\|_\infty)\cdot v$ (extended by $0$ at $0$): both
bodies are compact convex neighborhoods of $0$ in their affine spans, the rescaling is a
radial bijection between them (each ray meets each boundary once), and it is a homeomorphism
by compactness; boundary points correspond to boundary points since $\|v\|_1 = 1$ iff the
rescaled vector has $\|\cdot\|_\infty = 1$. Face-compatibility is visible in this
construction: the coordinate facets $\{v_i = 0\}$ are preserved, and the slant facet
$\{\sum_i v_i = 1\}$ maps onto $\{\|w\|_\infty = 1\} = \bigcup_i \{w_i = 1\}$, a union of cube
faces. $\square$

We fix such a family $\varphi_m$ once and for all. (This is the formalization's construction:
flatten, then rescale.)

**4.2 Consequences.** (a) Based cubes and based simplices are interchangeable:
$p \mapsto p \circ \varphi_n$ is a bijection from maps $(I^n, \partial I^n) \to (X, x)$ to maps
$(\Delta^n, \partial\Delta^n) \to (X, x)$, and likewise for homotopies rel boundary; we write
$[p]$ for either picture. (b) The class of the identity simplex
$\iota_n \colon \Delta^n \hookrightarrow$ (as a relative cycle of
$(\Delta^n, \partial\Delta^n)$) corresponds to $[I^n]$: $\varphi_{n*}[\Delta^n] = [I^n]$ for the
standard (orientation-preserving) choice of $\varphi_n$, since a homeomorphism of pairs has
degree $\pm 1$ and we normalize $\varphi_n$ to have degree $+1$. (c) A map
$(\Delta^n, \partial\Delta^n) \to (X,x)$, read as a singular $n$-simplex, is a normalized
cycle: its boundary is a sum of constant $(n-1)$-simplices, which vanish in $C^N_{n-1}(X)$.

## 5. Homotopy extension and cell filling

**5.1 The homotopy extension property (Hatcher Prop. 0.16, polyhedral case).** Let $(K, L)$ be
a pair of finite simplicial complexes (or: $K$ a cube $I^m$ or simplex $\Delta^m$ and $L$ a
union of its faces). Then $(K, L)$ has the homotopy extension property: any map
$K \times \{0\} \cup L \times I \to Y$ extends to $K \times I \to Y$.

*Proof.* It suffices to retract $K \times I$ onto $K \times \{0\} \cup L \times I$. For
$(I^m, \partial I^m)$: project $I^m \times I$ radially from the point
$(\bar t, 2) \in \mathbb{R}^{m+1}$ onto the boundary of the cylinder minus the top — a concrete
piecewise-linear retraction. For a general pair, retract cell by cell, inductively over the
skeleta of $K \setminus L$, using the simplex case
$(\Delta^k, \partial\Delta^k)$ at each step; the retraction on the $k$-skeleton extends the one
on the $(k-1)$-skeleton because the attaching maps land in the previous stage. $\square$

**5.2 Cell filling (the connectivity hypothesis, restated geometrically).** The hypothesis
"$\pi_k(X, x) = 0$" means exactly: every map $(D^k, \partial D^k) \cong (I^k, \partial I^k) \to
(X, x)$ is homotopic rel boundary to the constant map, i.e. extends over the cone on $D^k$ rel
boundary — equivalently, after identifying $D^k$ with the lower hemisphere of $S^k$, every
map $S^k \to X$ extends over $D^{k+1}$. For $k = 0$ this is path connectedness. Via the
dictionary 4.1 the same holds with $(\Delta^k, \partial\Delta^k)$ in place of
$(I^k, \partial I^k)$. We call any of these a *filling* of the given sphere/disc map. In an
$(n-1)$-connected space, fillings exist for all $k \leq n - 1$.

**5.3 The compression consequence.** A map of pairs $f \colon (K, L) \to (X, x)$ with $K$ a
finite complex of dimension $\leq n - 1$ is homotopic rel $L$... this direction is not needed;
what is needed is exactly the tower of §8, which is 5.1 + 5.2 iterated over skeleta.

## 6. The prism operator, in family form

**6.1 The prism.** Let $H \colon I \times \Delta^m \to Y$ be a homotopy from $\tau$ to $\tau'$
(singular $m$-simplices of $Y$). Triangulate the prism $\Delta^m \times I$ by the $m+1$
simplices $[v_0 \dots v_i\, w_i \dots w_m]$, $0 \leq i \leq m$, where $v_j, w_j$ are the two
copies of the $j$-th vertex (this is the shuffle triangulation of $\Delta^m \times \Delta^1$ of
3.5). The *prism chain* is
$$P_H(\tau) := \sum_{i=0}^m (-1)^i\ H \circ [v_0 \dots v_i\, w_i \dots w_m]\ \in\ C_{m+1}(Y).$$

**Lemma (prism boundary; Hatcher Thm. 2.10).**
$\partial P_H(\tau) = \tau' - \tau - P_{H|\partial}(\partial\tau)$, where the last term is the
sum of the prisms over the face homotopies with their boundary signs,
$P_{H|\partial}(\partial\tau) = \sum_j (-1)^j P_{H \circ (\mathrm{id} \times \delta^j)}$.

*Proof.* Direct computation: the boundary of the $i$-th prism simplex contributes the top face
$[w_0 \dots w_m]$ (only from $i = 0$, sign $+$), the bottom face $-[v_0 \dots v_m]$ (only from
$i = m$, sign $(-1)^m(-1)^{m+1} \cdot \ldots$ — the signs work out to $-1$), the interior side
faces $[v_0 \dots v_i\, w_{i+1} \dots]$ and $[v_0 \dots v_{i-1}\, w_i \dots]$, which cancel in
adjacent pairs $i, i-1$ exactly as in 3.2, and the outer side faces, which assemble to
$-P_{H|\partial}(\partial\tau)$. $\square$

**6.2 Family form.** Let $\{H_\alpha\}$ be a family of homotopies
$H_\alpha \colon \tau_\alpha \simeq \tau'_\alpha$ of singular $m$-simplices, *face-compatible*
in the sense that whenever two simplices of the family agree on a face,
$\tau_\alpha \circ \delta^j = \tau_\beta \circ \delta^{j'}$, the restricted homotopies agree
too, $H_\alpha \circ (\mathrm{id} \times \delta^j) = H_\beta \circ (\mathrm{id} \times
\delta^{j'})$. Then for any coefficients $a_\alpha \in \mathbb{Z}$:
$$\partial \Big(\sum_\alpha a_\alpha P_{H_\alpha}\Big)
= \sum_\alpha a_\alpha \tau'_\alpha - \sum_\alpha a_\alpha \tau_\alpha
- \sum_\alpha a_\alpha P_{H_\alpha|\partial}(\partial \tau_\alpha),$$
and the last sum inherits every cancellation that $\sum_\alpha a_\alpha \partial\tau_\alpha$
has: if a face occurs twice with opposite signs and the homotopies agree on it, its prism terms
cancel. In particular, if the family is stationary on every face that does not cancel — for
instance if all boundary faces are constant at $x$ and every $H_\alpha$ is rel those faces —
then in normalized chains
$\partial \sum_\alpha a_\alpha P_{H_\alpha} = \sum_\alpha a_\alpha \tau'_\alpha -
\sum_\alpha a_\alpha \tau_\alpha$, whence
$$\Big[\sum_\alpha a_\alpha \tau'_\alpha\Big] = \Big[\sum_\alpha a_\alpha \tau_\alpha\Big]
\ \in\ H_m(Y),$$
the class of a chain is unchanged under a face-compatible family of homotopies that is
stationary or cancelling on the boundary. This is the form in which homotopy invariance enters
the main theorem: not one simplex at a time but a whole chain's worth at once.

## 7. Subdivision of the cube and reparametrization invariance

**7.1 Reparametrization invariance.** Let $a \colon (I^n, \partial I^n) \to (I^n, \partial
I^n)$ be a map of degree $1$. Then for every based map $p \colon (I^n, \partial I^n) \to (X,
x)$, the chains $p_*(a_*\kappa_n)$ and $p_*(\kappa_n)$ differ by a boundary: $a_*\kappa_n$ and
$\kappa_n$ are relative cycles of $(I^n, \partial I^n)$ (3.3, and $\partial(a_*\kappa_n) =
a_*\partial\kappa_n$ is carried by $\partial I^n$), and
$$[a_*\kappa_n] = a_*[\kappa_n] = a_*[I^n] = (\deg a)\,[I^n] = [I^n] = [\kappa_n],$$
so their difference is a relative boundary, and pushing forward by $p$ kills the relative part
(constant chains are degenerate) and preserves boundaries. Hence
$[p_*(a_*\kappa_n)] = [p_*\kappa_n] \in H_n(X)$: **the Hurewicz class is unchanged under
degree-one reparametrization of the cube.** The same holds with $\Delta^n$ in place of $I^n$
via 4.1, and in particular for the affine homeomorphisms from $\Delta^n$ or $I^n$ onto the
cells of any subdivision (those have degree $+1$ by construction).

**7.2 Binary subdivision.** Subdivide $I^n$ into $m^n$ subcubes of side $1/m$ and triangulate
each subcube by 3.1; the total chain $\kappa_n^{(m)}$ (sum over subcubes of their pushed-forward
triangulation chains, each with its own permutation signs) again satisfies the chain identity
and represents $[I^n]$: the interior subcube boundaries cancel in pairs (each interior
subcube face appears twice with opposite orientations), leaving the triangulated boundary, so
$[\kappa_n^{(m)}] = [I^n]$ by the same induction as 3.4. By 7.1 the class $[p_*\kappa_n^{(m)}]$
equals $[p_*\kappa_n]$.

**7.3 The pinch computation (additivity of the class).** Let
$\mathrm{pinch} \colon (I^n, \partial I^n) \to (I^n \vee I^n,\ \partial I^n \vee \partial I^n)$
collapse the slab $\{t_1 = \frac12\}$, and let $\iota_1, \iota_2$ be the two inclusions of
pairs. In $H_n(I^n \vee I^n, \partial I^n \vee \partial I^n) \cong H_n(I^n, \partial I^n)
\oplus H_n(I^n, \partial I^n) \cong \mathbb{Z} \oplus \mathbb{Z}$ (excision on the wedge of the
two cube *pairs*; lane A),
$$\mathrm{pinch}_*[\kappa_n] = \iota_{1*}[\kappa_n] + \iota_{2*}[\kappa_n],$$
because the three relative classes have local degree $1$ at the generic points of the left
summand, right summand respectively (local-degree computation, Hatcher Prop. 2.30 machinery;
lane A), and local degrees determine the class in a free abelian homology group. For the
concatenation $p \cdot q$ of §2, $p \cdot q = (p \vee q) \circ \mathrm{pinch}$ as maps of pairs
into $(X, x)$, and pushing forward to $H_n(X, x) \cong H_n(X)$ (the reduced/unreduced
identification of §2) gives
$$[(p \cdot q)_*\kappa_n] = (p \vee q)_*\,\mathrm{pinch}_*[\kappa_n]
= (p \vee q)_*(\iota_{1*}[\kappa_n] + \iota_{2*}[\kappa_n]) = [p_*\kappa_n] + [q_*\kappa_n].$$
(One checks the reparametrizations of the two halves are the affine degree-one maps of 7.1.)

## 8. Straightening: the normalization tower

This section is the second place where the formalization unrolled a construction degree by
degree (a separate homotopy tower was built at each of $n = 2, 3, 4, 5, 6$). The construction
is a single induction over skeleta, uniform in $n$; this is the generalization **G2** of the
lane.

**Standing hypotheses:** $n \geq 1$ and $(X, x)$ is $(n-1)$-connected (§1; for the tower itself
$n \geq 1$ suffices — the hypothesis $n \geq 2$ enters only in §11, where the constructed map
must be a homomorphism into the abelian group $H_n$).

**8.1 Tower Lemma.** *Let $K$ be a finite simplicial complex (or $\Delta$-complex — the proof
uses only the skeletal filtration, the HEP of subcomplex pairs, and finiteness) of arbitrary
dimension $m$, $L \subseteq K$
a subcomplex, and $f \colon K \to X$ a map with $f(L) = \{x\}$. Then $f$ is homotopic rel $L$
to a map $f'$ with $f'(\mathrm{sk}_{\min(m, n) - 1} K) = \{x\}$; in particular, if
$m \leq n - 1$, $f'$ is the constant map $x$, and for any $m$, $f'$ is constant on the
$(n-1)$-skeleton (the case used in 12.3 with $m = n + 1$).*

*Proof.* We build a sequence of homotopies
$F_k \colon f_k \simeq f_{k+1}$ rel $L$, $k = 0, 1, \dots$, where $f_0 = f$ and $f_k$ satisfies
$f_k(\mathrm{sk}_{k-1} K \cup L) = \{x\}$; then $f' := f_{n}$ (resp. the constant map, if the
last stage collapses the top dimension) is the answer.

*Stage $k$* (from $f_k$ to $f_{k+1}$, for $k \leq \min(m, n) - 1$, plus the final stage
$k = m \leq n - 1$ in the case $m \leq n-1$). Induction hypothesis: $f_k$ is $x$ on
$\mathrm{sk}_{k-1}K \cup L$. For each $k$-simplex $\Delta$ of $K$:

* if $\Delta \subseteq L$, let $h_\Delta$ be the stationary homotopy;
* otherwise $f_k|_\Delta \colon (\Delta, \partial\Delta) \to (X, x)$ is a based map, and since
  $k \leq n - 1$ the hypothesis $\pi_k(X, x) = 0$ (via 5.2) gives a homotopy $h_\Delta \colon
  \Delta \times I \to X$ rel $\partial\Delta$ from $f_k|_\Delta$ to the constant map $x$.

The family $\{h_\Delta\}$ is face-compatible (6.2): on a shared $(k-1)$-face every $h_\Delta$
is stationary at $x$. So the $h_\Delta$ glue to a homotopy
$\mathrm{sk}_k K \times I \to X$, stationary on $\mathrm{sk}_{k-1}K \cup L$, and together with
the stationary homotopy of $f_k$ on $L$ and the initial map $f_k$ on $K \times \{0\}$ this is a
map $K \times \{0\} \cup (\mathrm{sk}_k K \cup L) \times I \to X$. Extend it to
$F_k \colon K \times I \to X$ by homotopy extension (5.1, applied to the pair
$(K, \mathrm{sk}_k K \cup L)$), and set $f_{k+1} := F_k(1, -)$. Then $f_{k+1}$ is $x$ on
$\mathrm{sk}_k K \cup L$, completing the induction.

If $m \leq n - 1$ the stage $k = m$ exists (since $m \leq n-1$) and turns the top simplices
constant, so $f_{m+1} \equiv x$. If $m = n$, stages run for $k = 0, \dots, n - 1$ and stop with
$f' = f_n$ constant on $\mathrm{sk}_{n-1} K$. Concatenate the $F_k$ (a finite composition of
homotopies rel $L$). $\square$

**8.2 Corollary (normalization of chains).** *Let $z = \sum_j a_j \tau_j \in C_m^N(X)$ be any
finite chain, $m \leq n + 1$ (the case $m = n + 1$ is used in 12.3), whose unnormalized
boundary face types either cancel pairwise in $C_{m-1}(X)$ or are constant at $x$ (e.g. $z$ a
genuine cycle, or $z$ a chain whose boundary is a sum of based simplices). Then there is a
face-compatible family of homotopies $H_j \colon \tau_j \simeq \tau'_j$, stationary on every
face already constant at $x$, such that every $\tau'_j$ is based: $\tau'_j$ sends
$\partial\Delta^m$ to $x$; and if $m \leq n - 1$ every $\tau'_j$ is constant at $x$. Moreover
the class is preserved when the family prism is computed in normalized chains: the pairwise
cancelling face types share one homotopy and their prism terms cancel; the constant face types
have stationary prisms, hence degenerate prism chains (each prism simplex has a repeated vertex
image), hence vanish in $C^N_*$.*

*Proof.* Let $K$ be the finite $\Delta$-complex obtained from the disjoint union of the
$\Delta^m$'s (one per $j$, repeated with multiplicity $|a_j|$) by identifying faces that are
equal as singular simplices of $X$ as oriented simplices (all occurrences of a face type, of
either coefficient sign, are identified and will share one homotopy), and let $L$ be the union
of all faces already constant at $x$. The $\tau_j$ assemble to a map $f \colon K \to X$ with
$f(L) = \{x\}$. Apply 8.1 (the $\Delta$-complex form); the resulting homotopy, read back on the
disjoint copies, is a face-compatible family (face-compatibility holds because identified faces
received the same homotopy — the choice of $h_\Delta$ was made per simplex of $K$, i.e. per
*face type*, not per occurrence). $\square$

*Remark (normalized cycles).* A cycle in the normalized complex $C^N_*(X)$ need not satisfy
8.2's hypothesis: its unnormalized boundary is a general degenerate chain whose face types may
be neither constant nor pairwise cancelling. In that case first replace it by a homologous
genuine cycle: $\partial z \in Z_{m-1}(D_*(X))$ is a boundary in the degenerate subcomplex
since $H_*(D_*) = 0$ (§2), say $\partial z = \partial w$ with $w \in D_m$; then $z - w$ is a
genuine cycle representing the same class, and 8.2 applies to it. This replacement is used in
13.1 and 14.

**8.3 Remark (what the tower costs at each stage).** Stage $k$ invokes the hypothesis
$\pi_k(X, x) = 0$ once per $k$-simplex of $K$ (finitely often) and homotopy extension once.
The induction is over the finite skeleton dimension, so the number of homotopies composed is
$\min(m, n-1) + 1$; in the formalization this is a recursion on $k$ with the extended homotopy
as the recursive data — the recursive definition that replaces the unrolled towers.

---

## 9. The decomposition theorem (cube gluing)

This section proves that the class of a straightened cube in $\pi_n$ is the signed sum of the
classes of its triangulation pieces, and the companion zero-sum relation for the faces of a
based simplex. Everything here is elementary homotopy theory of the cube — no homology — and
uniform in $n$. In the formalization this is the `CubeGluing` / chamber machinery; the two
ingredients that make it work at arbitrary $n$ are the Alexander trick (9.1) and a shelling of
the braid arrangement (9.3).

**9.1 The Alexander trick, the permutation action, and reparametrization.**
*Alexander's trick:* any homeomorphism $w$ of $I^n$ that fixes $\partial I^n$ pointwise is
isotopic to the identity rel boundary, by
$H(t, u) = t \cdot w(u/t)$ for $\|u\| \leq t$ in the radial parametrization and $H(t, u) = u$
otherwise (cone the homeomorphism). Consequently, precomposition with a boundary-fixing
self-homeomorphism of the cube does not change a class in $\pi_n(X, x)$; and a
reparametrization by any *explicit* boundary-fixing homeomorphism is canonical up to
homotopy rel boundary.

*The inverse as a reflection.* For $n \geq 2$ the group $\pi_n(X,x)$ is abelian and the
inverse is realized by reflection in any single coordinate,
$[p \circ \rho_i] = -[p]$: for the first coordinate this is the definition of the inverse; the
concatenation in coordinate $i$ is homotopic to concatenation in coordinate $1$ (Eckmann–Hilton:
the two compositions are related by a rotation of the unit square in the $(t_1, t_i)$-plane —
a boundary-*preserving* isotopy of the disc model of the cube (the boundary is moved as a set,
so precomposition carries based maps to based maps and yields based homotopies rel boundary)),
so inversion in coordinate $i$ equals inversion in coordinate $1$.

*The permutation action.* For a permutation $\sigma \in S_n$, write $\hat\sigma \colon I^n \to
I^n$ for the coordinate permutation. Then
$$[p \circ \hat\sigma] = \operatorname{sign}(\sigma)\,[p].$$
Proof: adjacent transpositions generate; for the transposition of coordinates $i, i+1$,
rotate the $(t_i, t_{i+1})$-plane of the disc model through angle $\pi/2$: a
boundary-preserving isotopy from the identity to $\hat s_i \circ \rho_i$ (a transposition is a
quarter-turn composed with a reflection), so $[p \circ \hat s_i] = [p \circ \rho_i] = -[p]$.
$\square$

**9.2 The cut lemma.** *Let $I^n = A \cup B$ with $A, B$ closed $n$-balls and $F := A \cap B$
an $(n-1)$-ball contained in $\partial A \cap \partial B$, and let $p \colon (I^n, \partial
I^n) \to (X, x)$ be constant equal to $x$ on $F$. Then $[p] = [p_A] + [p_B]$ in $\pi_n(X, x)$,
where $p_A, p_B$ are the restrictions of $p$, transported to the cube by fixed
orientation-preserving homeomorphisms of pairs $(A, \partial A) \cong (I^n, \partial I^n) \cong
(B, \partial B)$ chosen once and for all for the cuts that arise.*

*Proof.* Since $p$ is constant on $F$, it factors through the pinch $c \colon I^n \to I^n/F
\cong (A/F) \vee (B/F)$ — a wedge of two balls-with-boundary-collapsed, i.e. of two based
$n$-spheres. It remains to compare $c$ with the standard concatenation pinch $c_0$ of §2
(collapsing the slab $\{t_1 = \tfrac12\}$): we produce an isotopy of $p$ itself, rel boundary,
from $p$ to a map that is constant on the slab. The cut $F$ and the slab are two embedded
$(n-1)$-balls in $I^n$, each splitting the cube into two balls, each with boundary an embedded
$(n-2)$-sphere in $\partial I^n$ splitting the boundary sphere into two balls. Two such spheres
in $\partial I^n \cong S^{n-1}$ are ambiently isotopic (two embedded balls in a sphere are
isotopic — coning reduces to the Schoenflies content that both sides are balls; all embeddings
here are locally flat, indeed piecewise linear), and the isotopy extends to the filling balls,
then to the two sides, giving an ambient isotopy $\varphi_s$ of the cube with
$\varphi_s(\partial I^n) = \partial I^n$ (boundary-preserving, not pointwise), moving $F$ to
the slab. Then $p \circ \varphi_s^{-1}$ is a homotopy of based maps rel boundary (the
basepoint locus $\partial I^n$ is preserved as a set, so all intermediate maps are based), and
at the end $p \circ \varphi_1^{-1}$ is constant on the slab, i.e. literally a concatenation of
its two halves: $[p] = [p \circ \varphi_1^{-1}] = [p_A] + [p_B]$ by the definition of addition
and the reparametrization invariance of the classes of the halves (9.1, applied to the fixed
transport homeomorphisms composed with the restriction of $\varphi_1$). $\square$

The braid-hyperplane cut $H_{ij} = \{t_i = t_j\}$ of the cube (with the two sides
$\cong \Delta^2 \times I^{n-2}$, balls) is the case used in the first peel of the shelling
below; the general two-ball form is what the induction of 9.4 needs, since after the first
pinch the geometry is no longer a cube.

**9.3 Shelling the braid arrangement.** Order $S_n$ by any linear extension of inversion
number (equivalently: by a reduced-word path from the identity to the longest element in the
weak order on $S_n$); write $\sigma_1, \dots, \sigma_{n!}$. Then each initial union
$B_m = \bigcup_{r \leq m} \Delta_{\sigma_r}$ is a closed ball, and
$\Delta_{\sigma_{m+1}} \cap B_m$ is the union of the *descent facets* of $\sigma_{m+1}$ — the
facets $t_{\sigma(i)} = t_{\sigma(i+1)}$ at the descents $i$ of $\sigma_{m+1}$ (those are
exactly the facets shared with earlier chambers, since passing to $\sigma \circ s_i$ lowers the
inversion number precisely at descents). A nonempty proper union of facets of a simplex is a
ball — it is a cone from any vertex $e_k$ lying in *all* facets of the union (equivalently:
whose opposite facet $\delta^k$ is omitted; such a vertex exists because the union is proper)
over a smaller such union or a sphere, hence a ball by induction on $n$ — so each step glues an
$n$-ball onto a ball along an $(n-1)$-ball in both boundaries: every $B_m$ is a ball by
induction, and the pinch of 9.2 is available at every step.

**9.4 The decomposition theorem.** *Let $n \geq 2$ and let $p \colon (I^n, \partial I^n) \to
(X, x)$ be internally based: constant equal to $x$ on the $(n-1)$-skeleton of the Kuhn
triangulation $K_n$ (equivalently: on every braid hyperplane and on $\partial I^n$). Then in
$\pi_n(X, x)$,*
$$[p] \ =\ \sum_{\sigma \in S_n} \operatorname{sign}(\sigma)\,\big[p \circ A_\sigma\big],$$
*where each piece $p \circ A_\sigma \colon (\Delta^n, \partial\Delta^n) \to (X, x)$ is based and
is read as a $\pi_n$ element via the dictionary 4.1.*

*Proof.* Induction on the shelling 9.3. At step $m+1$, the two-ball decomposition
$B_{m+1} = B_m \cup \Delta_{\sigma_{m+1}}$ meets the cut lemma 9.2 exactly: both sides are
balls (9.3), the interface $\Delta_{\sigma_{m+1}} \cap B_m$ — the union of the descent facets
of $\sigma_{m+1}$, itself a ball (9.3) lying in both boundaries — is where $p$ is constant
$x$, so the class splits as
$[p|_{B_m}] + [p|_{\Delta_{\sigma_{m+1}}}]$, with the second term transported to the cube by the
fixed homeomorphism of 9.2. It remains to identify the transported class with
$\operatorname{sign}(\sigma_{m+1})\,[p \circ A_{\sigma_{m+1}}]$: the composite of the
triangle-straightening homeomorphisms with $A_{\sigma}$ is a boundary-preserving
self-homeomorphism of the cube whose orientation sign relative to the standard orientation is
exactly $\det(dA_\sigma) = \operatorname{sign}(\sigma)$ (3.1); a boundary-fixing homeomorphism
of positive sign is isotopic rel boundary to the identity (Alexander, 9.1, applied after the
unique affine orientation normalization), and a negative sign contributes one reflection, i.e.
one factor of $-1$ by 9.1. $\square$

**9.4′ The zero-sum relation.** *Let $\tau \colon \Delta^{n+1} \to X$ be a singular
$(n+1)$-simplex all of whose faces $\tau \circ \delta^i$ are based
($(\Delta^n, \partial\Delta^n) \to (X, x)$). Then*
$$\sum_{i=0}^{n+1} (-1)^i\,\big[\tau \circ \delta^i\big] = 0 \ \in\ \pi_n(X, x).$$

*Proof.* The face maps assemble to a map $\partial\tau \colon \partial\Delta^{n+1} \to X$ of the
boundary sphere, constant $x$ on the $(n-1)$-skeleton of $\partial\Delta^{n+1}$ (every
$(n-1)$-face is a face of a face). The decomposition theorem 9.4 applies verbatim to the
triangulated sphere $\partial\Delta^{n+1}$ in place of the triangulated cube (its chambers are
the $n+2$ facets; the shelling is any ordering of the facets, and the cut lemma 9.2 applies at
each step — the map is constant on every shared facet ball, including the last, equatorial,
cut), giving
$[\partial\tau] = \sum_i \varepsilon_i [\tau \circ \delta^i]$ in $\pi_n(X, x)$, where
$\varepsilon_i = (-1)^i$ is the orientation sign of the $i$-th facet in the boundary of the
oriented simplex. But $\partial\tau$ extends over $\Delta^{n+1}$ (via $\tau$), so
$[\partial\tau] = 0$. $\square$

## 10. The cross product

**10.1 The shuffle product on chains.** For singular simplices $\sigma \colon \Delta^p \to X$,
$\tau \colon \Delta^q \to Y$, define
$$\sigma \times \tau \ :=\ \sum_{\mu} \operatorname{sign}(\mu)\,
(\sigma \times \tau) \circ \mu^\sharp \ \in\ C_{p+q}(X \times Y),$$
where $\mu$ runs over the $(p,q)$-shuffles and $\mu^\sharp \colon \Delta^{p+q} \to \Delta^p
\times \Delta^q$ is the corresponding affine shuffle simplex (3.5). Extend bilinearly to
$\times \colon C_p(X) \otimes C_q(Y) \to C_{p+q}(X \times Y)$.

**Lemma (Leibniz rule).**
$\partial(\sigma \times \tau) = \partial\sigma \times \tau + (-1)^p\, \sigma \times
\partial\tau.$
*Proof.* Same adjacent-transposition cancellation as 3.2: interior shuffle facets cancel in
pairs; the outer faces assemble to the two terms, the second with the sign $(-1)^p$ from moving
the $q$ vertical steps past the $p$ horizontal ones. $\square$

**10.2 Descent to homology.** By the Leibniz rule the product of two cycles is a cycle, the
product of a cycle with a boundary is a boundary, and the induced map
$$\times \colon H_p(X;\mathbb{Z}) \otimes_{\mathbb{Z}} H_q(Y;\mathbb{Z}) \longrightarrow
H_{p+q}(X \times Y;\mathbb{Z})$$
is well-defined, natural in $X$ and $Y$, unital ($[\mathrm{pt}] \times z = z$ under
$X \times \{\mathrm{pt}\} = X$), and associative. This lane needs $p = 1$:
$H_1(X) \otimes H_n(Y) \to H_{n+1}(X \times Y)$; the general construction is no harder and is
what the library file records. (The Künneth *isomorphism* for $S^1 \times Y$ —
$H_{n+1}(S^1 \times Y) \cong H_{n+1}(Y) \oplus (H_1(S^1) \otimes H_n(Y))$, with the cross
product as the second summand inclusion — is proved from Mayer–Vietoris over the two-arc cover
of $S^1$; that direction is the torus lane J, and the $S^1 \times Y$ homology computation is
lane A material. The cross product map itself is all this section claims.)

**10.3 The fundamental chain of the cube, recursively.** The interval chain $\kappa_1$ is the
fundamental class of $I$. Inductively, $\kappa_{n+1} = \kappa_1 \times \kappa_n$: the shuffle
triangulation of $I \times I^n$ along a single interval inserts the new step at each of the
$n+1$ positions of the ordered coordinate list, and the insertion of the new element at
position $k$ in a permutation of $n$ letters to give a permutation of $n+1$ letters carries the
shuffle sign to the permutation sign. This is exactly the identity of 3.3 read inductively, and
it identifies the recursively defined cross-product chain with the permutation sum $\kappa_n$
of §3 *as chains* (not merely up to homology). This identity — *the cube chain equals the
signed sum of its triangulation simplices*, at every $n$ — is the generalization **G1** in its
final form; the existing formalization proves it separately at $n = 2$ (two triangles),
$n = 3$ (six tetrahedra), and $n = 4, 5, 6$ (the permutation sum, by unrolled computation).
The proof here is the single induction: Leibniz rule 10.1 + insertion-sign bookkeeping + 3.2.

**10.4 The loop–cylinder recursion.** A based $n$-cube $p \colon (I^n, \partial I^n) \to (X,x)$
is the same as a based loop $\widetilde p$ in the space of based $(n-1)$-cubes (currying in the
first coordinate), and the evaluation map
$\mathrm{ev} \colon \Omega_{n-1}X \times I^{n-1} \to X$ satisfies
$$p_*\kappa_n \ =\ \mathrm{ev}_*\big(\widetilde p_* \kappa_1 \times \kappa_{n-1}\big)$$
as chains (10.3 plus the definition of the cross product). The right-hand side is the
*suspension recursion*: the class $[p_*\kappa_n]$ is the cross product of the $H_1$-class of
the loop $\widetilde p$ with the fundamental class of $I^{n-1}$, pushed forward by evaluation.
This is the form in which the formalization defines the forward map (the "fundamental cube
chain" by recursion on $n$); 10.3 is then the theorem identifying it with the permutation sum,
and that theorem is where the old per-degree unrolling lived.

## 11. The Hurewicz homomorphism

**11.1 Definition.** For $p \colon (I^n, \partial I^n) \to (X, x)$ set
$c(p) := p_*\kappa_n \in C_n(X)$. By the chain identity 3.3,
$\partial c(p) = p_*(\text{triangulation chain of } \partial I^n)$, and $p|_{\partial I^n}$ is
constant $x$, so every boundary term is a constant — hence degenerate — $(n-1)$-simplex:
$c(p)$ is a cycle in the normalized complex $C^N_*(X)$. Set
$$h_n[p] := [c(p)] \in H_n(X;\mathbb{Z}).$$

**11.2 Well-defined.** If $p \simeq q$ rel $\partial I^n$ via $H \colon I \times I^n \to X$,
triangulate the cylinder $I \times I^n$ by the prisms over the Kuhn simplices (the shuffle
triangulation of $I \times I^n$, §6) and apply the family prism identity 6.2 to the family
$\{H \circ (\mathrm{id} \times A_\sigma)\}$: the side terms are $q_*\kappa_n - p_*\kappa_n$ and
the face terms are the prisms over the boundary faces, all constant — hence degenerate. So
$[c(p)] = [c(q)]$ in normalized homology. (Equivalently: homotopy invariance of singular
homology applied to the relative cycle $\kappa_n$; the point of doing it through the prism is
that the prism over the triangulation is exactly the triangulation of the prism, 3.5.)

**11.3 Homomorphism.** $h_n[p \cdot q] = h_n[p] + h_n[q]$ by the pinch computation 7.3;
$h_n[0] = 0$ since the constant cube maps $\kappa_n$ to a degenerate chain; and
$h_n[-p] = -h_n[p]$ since the reflection $t_1 \mapsto 1 - t_1$ has degree $-1$
(reparametrization invariance 7.1 read at general degree:
$[p_*(a_*\kappa_n)] = (\deg a)\,[p_*\kappa_n]$ for any boundary-preserving $a$). Being a
homomorphism between abelian groups, $h_n$ is automatically $\mathbb{Z}$-linear.

## 12. The inverse: the simplex class operator

Assume now the hypotheses of the theorem: $n \geq 2$ and $X$ is $(n-1)$-connected.

**12.1 The class of a based simplex.** A based singular $n$-simplex
$\tau \colon (\Delta^n, \partial\Delta^n) \to (X, x)$ defines
$\langle\tau\rangle := [\tau \circ \psi_n] \in \pi_n(X, x)$, where $\psi_n = \varphi_n^{-1}$ is
the fixed dictionary homeomorphism of 4.1. Degenerate based simplices have zero class — and the
argument needs no input at all: if $\tau = \rho \circ s^l \colon (\Delta^n, \partial\Delta^n)
\to (X, x)$ is degenerate (factoring through the codegeneracy $s^l$) and based, then $s^l$ maps
$\partial\Delta^n$ *onto* $\Delta^{n-1}$ (the facet whose vertices are not merged by $s^l$ maps
homeomorphically onto $\Delta^{n-1}$), so
$\rho(\Delta^{n-1}) = \rho(s^l(\partial\Delta^n)) = \tau(\partial\Delta^n) = \{x\}$: the map
$\rho$ — hence $\tau$ — is the constant map, and $\langle\tau\rangle = 0$. So
$\langle\cdot\rangle$ descends to the free abelian group on normalized based simplices.

**12.2 The class operator.** For an arbitrary singular $n$-simplex $\tau$, the tower 8.1
(applied to $K = \Delta^n$, $L = \varnothing$) supplies a homotopy $\tau \simeq \tau'$ with
$\tau'$ based; define the *class operator* on chains by
$$\Psi\Big(\sum_j a_j \tau_j\Big) := \sum_j a_j\, \big\langle \tau'_j \big\rangle
\ \in\ \pi_n(X, x),$$
choosing the tower homotopies per face type as in 8.2 so that the assignment is
face-compatible. This is a well-defined *function of the chain* once the homotopy recipe is
fixed (equal chains have the same face types, hence the same chosen homotopies) — and that is
all that is ever used: choice-independence of the induced map on homology is never invoked, the
round-trips of §13 working with one fixed recipe throughout. (Per-simplex choice-independence
does hold on chains whose boundary face types cancel, the $\pi_n$ ambiguities of the two
nullhomotopies then cancelling in pairs — but no application needs it.) The operator factors
through normalized chains: for a degenerate $\tau$, the straightened $\tau'$ is homotopic to
$\tau$, and $\tau$ factors through the contractible $\Delta^{n-1}$, so $\tau'$ is freely
nullhomotopic; since $\pi_1(X, x) = 0$ the $\pi_1$-action on $\pi_n$ is trivial, so a freely
nullhomotopic based map is null in $\pi_n(X, x)$, i.e. $\langle \tau' \rangle = 0$.

**12.3 The operator kills boundaries.** Let $\omega \colon \Delta^{n+1} \to X$ be a singular
$(n+1)$-simplex. Apply the tower to $\omega$ (dimension $n+1$: normalize the $n$-skeleton —
this uses $\pi_k = 0$ for $k \leq n-1$, all available) to get $\omega'$ with all faces based;
face-compatibility (8.2) identifies the class of each normalized face with the operator value
on that face. By the zero-sum relation 9.4′,
$\sum_i (-1)^i \big\langle (\omega \circ \delta^i)' \big\rangle
= \sum_i (-1)^i [\omega' \circ \delta^i] = 0$,
i.e. $\Psi(\partial\omega) = 0$. Hence $\Psi$ descends to a homomorphism
$$\bar\Psi \colon H_n(X;\mathbb{Z}) \longrightarrow \pi_n(X, x).$$

## 13. The two round-trips

**13.1 $h_n \circ \bar\Psi = \mathrm{id}$ on $H_n(X)$.** Let $z = \sum_j a_j \tau_j$ be a
normalized $n$-cycle. First replace it by a homologous genuine cycle: its unnormalized boundary
is a cycle in the degenerate subcomplex, hence a boundary there ($H_*(D_*) = 0$, §2), so
$z - w$ is a genuine cycle representing $[z]$ for a degenerate $w$; rename it $z$. Straighten
it by the tower to $z' = \sum_j a_j \tau'_j$ with all $\tau'_j$
based (8.2; the straightening preserves the homology class by the family prism 6.2 — the
pairwise face cancellation makes 6.2 applicable, see 8.2's remark). Then
$h_n(\bar\Psi[z]) = \sum_j a_j\, [c(\tau'_j \circ \psi_n)]$, and for each based simplex
$c(\tau' \circ \psi_n) = \tau'_*(\psi_{n*}\kappa_n)$ is homologous to
$\tau'_*(\iota_n) = \tau'$: the relative cycles $\psi_{n*}\kappa_n$ and $\iota_n$ of
$(\Delta^n, \partial\Delta^n)$ both represent $[\Delta^n]$ (4.2(b), 3.4), so they differ by a
relative boundary, which pushes forward to a boundary plus degenerate chains. Hence
$h_n(\bar\Psi[z]) = [z'] = [z]$.

**13.2 $\bar\Psi \circ h_n = \mathrm{id}$ on $\pi_n(X, x)$.** Let $p \colon (I^n, \partial I^n)
\to (X, x)$. Straighten each triangulation piece $p \circ A_\sigma$ by the tower, chosen
face-compatibly across shared facets (8.2) and stationary on $\partial I^n$ (where $p$ is
already $x$); the piece homotopies glue — this is the one place where a family of homotopies on
the triangulated cube is assembled into a *single* homotopy of $p$, continuous because the
family agrees on shared facets and is stationary on the boundary — to a homotopy
$p \simeq p'$ rel $\partial I^n$ with $p'$ internally based (8.1 at $K = K_n$, $m = n$). Then
$$\bar\Psi(h_n[p]) = \Psi(c(p)) = \sum_\sigma \operatorname{sign}(\sigma)\,
\big\langle (p \circ A_\sigma)' \big\rangle
= \sum_\sigma \operatorname{sign}(\sigma)\, \big[p' \circ A_\sigma\big]
= [p'] = [p],$$
where the second equality is the chain identity 3.3 ($c(p) = p_*\kappa_n$ *is* the permutation
sum, 10.3) plus the definition of $\Psi$; the third is the compatibility of the piecewise
straightening with the glued straightening; the fourth is the decomposition theorem 9.4. Hence
$h_n$ and $\bar\Psi$ are mutually inverse isomorphisms. $\square$ **(Theorem proved.)**

## 14. Vanishing below degree $n$

*Corollary (the rest of Hatcher Thm. 4.32).* Under the same hypotheses, $H_k(X;\mathbb{Z}) = 0$
for $1 \leq k < n$.

*Proof.* For $k = 1$: the degree-one Hurewicz theorem (Hatcher Thm. 2A.1, already in the
library) gives $H_1(X) \cong \pi_1(X,x)^{\mathrm{ab}} = 0$. For $2 \leq k < n$: let $z$ be a
normalized $k$-cycle; as in 13.1, first replace it by a homologous genuine cycle (8.2's
remark). Straighten $z$ by the tower (8.2 at $m = k \leq n - 1$): every simplex
becomes *constant* $x$ (the tower's last stage collapses the top cells, since $\pi_k(X,x) =
0$), so $z' = 0$ — but the straightening preserves the class (family prism 6.2, applicable by
the pairwise cancellation), so
$[z] = [z'] = 0$. $\square$

(The formalization exposes the vanishing differently — the consumers obtain $\pi_k(X, x) = 0$
for $k < n$ *from* the isomorphism $\pi_k(X,x) \cong H_k(X)$ applied inductively to spheres and
threefolds whose homology is already computed. Both formulations are recorded in the ledger;
the corollary above is the textbook half of Hatcher's statement and costs one paragraph.)

## 15. The Hopf degree theorem

*Corollary (Hatcher Cor. 4.25).* Two maps $S^n \to S^n$ are homotopic if and only if they have
the same degree; $\deg \colon \pi_n(S^n) \to \mathbb{Z}$ is an isomorphism.

*Proof.* The sphere $S^n$ is $(n-1)$-connected: simply connected for $n \geq 2$ (it is the
suspension of $S^{n-1}$, or by van Kampen applied to the two-hemisphere cover — lane B), and
$\pi_k(S^n) = 0$ for $2 \leq k < n$ by the *bootstrap induction*: inductively on $k$, the
theorem just proved applies at degree $k$ (the hypotheses at degree $k$ are simple connectivity
and $\pi_j(S^n) = 0$ for $2 \leq j < k$, the induction hypothesis), so
$\pi_k(S^n) \cong H_k(S^n) = 0$ (lane A: homology of the sphere). Hence
$h_n \colon \pi_n(S^n) \xrightarrow{\;\sim\;} H_n(S^n) = \mathbb{Z}\cdot[S^n]$, and
$h_n[f] = f_*[S^n] = (\deg f)\,[S^n]$ by naturality (a based cube representing $[f]$ pushes
$\kappa_n$ forward to a representative of $f_*[S^n]$ — this is the definition of degree
transported along the quotient map of §16). So $[f] = h_n^{-1}(\deg f)$: the degree is a
complete based-homotopy invariant. For unbased maps: $S^n$ is homogeneous, so any map is freely
homotopic to a based one, and the $\pi_1$-action on $\pi_n$ is trivial, so the based
classification is the free one. $\square$

The formalized statement is the equivalent form used by the consumer: a self-map of the sphere
acting as the identity on $H_n$ is homotopic to the identity, and a right homology inverse of a
sphere map is a left inverse ("right inverse is left inverse").

## 16. Transport to the sphere; cell filling

**16.1 The cube–sphere quotient.** Collapsing the boundary gives homeomorphisms of pairs
$(I^n, \partial I^n) \to (D^n, \partial D^n) \to (S^n, \mathrm{pt})$; explicitly, the interior
of the cube is $\mathbb{R}^n$ and its one-point compactification is $S^n$. The quotient map
$q \colon (I^n, \partial I^n) \to (S^n, \mathrm{pt})$ is a based cube in $S^n$ — the *universal*
one: every based cube $p \colon (I^n, \partial I^n) \to (X, x)$ factors uniquely as
$p = \bar p \circ q$ with $\bar p \colon (S^n, \mathrm{pt}) \to (X, x)$ continuous (the quotient
property), and homotopies rel boundary correspond to based homotopies of sphere maps. Likewise
$q_*\kappa_n$ represents $[S^n]$, and the square relating $h_n$ on cube classes and on sphere
maps commutes. This transports the whole lane between the cube model (used in the proofs, where
addition is concatenation) and the sphere model (used by the consumers, where the manifold
structure lives).

**16.2 Cell filling.** The geometric restatement of the connectivity hypothesis (5.2) in the
form the consumers use:

* (sphere filling) if $X$ is $(d-1)$-connected, every map $S^{k-1} \to X$ with $k \leq d$
  extends over $D^k$ — this is exactly 5.2 (the vanishing of $\pi_{k-1}$ is the extension over
  the cone, and $D^k$ is the cone on $S^{k-1}$);
* (cylinder filling) under the same hypotheses, a homotopy $S^{k-1} \times I \to X$ between the
  boundary restrictions of two disc maps $f, g \colon D^k \to X$ extends to a homotopy
  $D^k \times I \to X$ between $f$ and $g$: the given data is a map on
  $D^k \times \{0,1\} \cup S^{k-1} \times I = \partial(D^k \times I)$, i.e. a map
  $S^k \to X$, which fills by the previous item at degree $k + 1 \leq d$.

These are stated for the sphere and disc of an arbitrary finite-dimensional real normed space
(the model the consumers need), with the rank hypothesis $\dim V \leq d$ replacing the abstract
dimension.

---

# Axes 2–3 — additive decomposition, in dependency order

The proof of the theorem decomposes additively as $P = L_1 + \dots + L_{14}$ below. Every row
states its inputs, its exact output, and its destination file (§18). All rows are FREE (no
project vocabulary). Dependency order is row order; every dependency points backward.

| # | Lemma (textbook §) | Inputs | Output | Current `Hopf/` home |
|---|---|---|---|---|
| L1 | Simplex–cube dictionary (§4) | convex-body geometry | homeomorphism of pairs $(\Delta^m, \partial\Delta^m) \cong (I^m, \partial I^m)$, face-compatible | `HigherHurewicz.*` 119–456 |
| L2 | Homotopy extension for polyhedral pairs (§5.1); cylinder retraction | simplicial-pair combinatorics | HEP extensions; `extendBoundaryHomotopy` | `Hurewicz.lean` 1479–2148 |
| L3 | Kuhn triangulation (§3.1–3.2) | permutation combinatorics | the complex $K_n$; face-incidence lemma | `HigherHurewicz.CubeTriangulation` 16057–16613 |
| L4 | Shuffle cross product (§10.1–10.2) | L3 (shuffle signs), singular chains (A) | $\times \colon C_p \otimes C_q \to C_{p+q}$; Leibniz; $H_1 \otimes H_n \to H_{n+1}$ | `PeriodTorusHigherHomology` cross block 2152–3818 |
| L5 | Chain identity (§3.3–3.4, §10.3) — **G1** | L3, L4 | $\kappa_n = \sum_\sigma \mathrm{sign}(\sigma) A_\sigma$; $\partial \kappa_n$ = boundary triangulation; $\kappa_{n+1} = \kappa_1 \times \kappa_n$; $[\kappa_n] = [I^n]$ | per-degree: 7166 ($n{=}2$), 10679 ($n{=}3$), 18235 ($n{=}4$), 23264 ($n{=}5$), Rec 1240 ($n{=}6$) |
| L6 | Prism operator, family form (§6) | L3 (shuffle case $q{=}1$), chains (A) | $\partial P = g - f - P\partial$; face-compatible family form | `prismOperator` 4414; `prismCubeRealization` 16769 |
| L7 | Straightening tower (§8) — **G2** | L1, L2, cell filling (L13) | normalization of simplices/chains, face-compatible, stationary on normalized locus | vertex/edge storeys 4639–5363 (general); storey $k$: `simplexStraighteningHomotopy` 15183; per-degree compositions 14121, 15318, 22252, Rec 186 |
| L8 | Cycle straightening preserves the class (§8.2 + §6) | L6, L7 | `straightenedCycle` homologous to the original cycle | 15602–15758 |
| L9 | Reparametrization invariance; pinch computation (§7) | L5, local degree (A) | $[p_*(a_*\kappa_n)] = (\deg a)[p_*\kappa_n]$; $c(p\cdot q) \sim c(p) + c(q)$ | `NativeSubdivision` 18489–18782; `pathCubeClass_trans` per degree |
| L10 | Decomposition theorem + zero-sum relation (§9) | L1, L3, L7 (internally based input) | $[p] = \sum_\sigma \mathrm{sign}(\sigma)[p \circ A_\sigma]$; $\sum_i (-1)^i[\partial_i \tau] = 0$ | `CubeGluing` 19948–20581; `CubicalBoundary` 18323–19947; `nativeCubeSubdivision_class` 22073 (general $n$ — already done) |
| L11 | The Hurewicz homomorphism (§11) | L5, L6, L9 | $h_n \colon \pi_n(X,x) \to H_n(X)$ well-defined, $\mathbb{Z}$-linear | per-degree `hurewiczMap`; recursive `cubeChain` def 17364/23152/Rec 1128 |
| L12 | The class operator and the two round-trips (§12–13) | L7, L8, L10, L11 | $\bar\Psi \colon H_n(X) \to \pi_n(X,x)$; $h_n \circ \bar\Psi = \mathrm{id}$; $\bar\Psi \circ h_n = \mathrm{id}$ — **the theorem** | per-degree `hurewiczInverse`, `hurewiczLinearEquiv` (8285, 14984, 22152, 23611, Rec 1492) |
| L13 | Cell filling; cube→sphere transport (§16) | L7's one-level lemma (already general), quotient topology | sphere/cylinder filling at rank $\leq d$; $I^n/\partial I^n \cong S^n$ factorization | `Degree.Sphere.exists_boundary_extension_of_pi` Rec 2510; `Degree.CylinderFilling.exists_filling` Rec 2542; `SixSphereCube` Rec 1737–1955 (pinned $n=6$) |
| L14 | Hopf degree theorem (§15) | L12 (applied to $S^n$), sphere connectivity bootstrap (A/B) | $\deg \colon \pi_n(S^n) \cong \mathbb{Z}$; right-inverse-is-left-inverse | `Degree.Sphere.homotopic_id_of_topClass` Rec 4025 (pinned $n = 6$) |

**What is deleted.** The per-degree copies become instantiations: each `hurewiczPiNEquiv` is
the general `hurewiczLinearEquiv` applied to the subsingleton instances accumulated by the
bootstrap; the bespoke $n = 2, 3$ triangulation and prism blocks (L5, L6 at low degree) are
replaced by the general proofs. Estimated deletion $\approx 14{,}000$ of $25{,}000$ lines, as
forecast in the task; the exact count is measured in the lane report at landing.

---

# Axis 4 — placement

All files under `Lib/`; no `Hopf/` imports; namespaces `AlgebraicTopology.Hurewicz`,
`AlgebraicTopology.SingularHomology`, `Topology.Homotopy` as shown. Twin files are the pinned
Mathlib's closest files in subject and shape; several targets have no true Mathlib analogue
(Mathlib has no cubical Hurewicz development) — the twin then governs *shape* only: header,
binder hoisting, `lemma`/`theorem` choice, attribute idioms.

| File | Content (rows) | Mathlib twin |
|---|---|---|
| `Lib/AlgebraicTopology/Hurewicz/SimplexCube.lean` | L1 | `Mathlib/Topology/UnitInterval.lean`, `Mathlib/AlgebraicTopology/TopologicalSimplex.lean` |
| `Lib/Topology/Homotopy/CellFilling.lean` | L13 (filling half) | `Mathlib/Topology/Homotopy/Contractible.lean` |
| `Lib/AlgebraicTopology/Hurewicz/HomotopyExtension.lean` | L2 | `Mathlib/Topology/Homotopy/Basic.lean` (shape) |
| `Lib/AlgebraicTopology/Hurewicz/CubeTriangulation.lean` | L3 | none existing; shape after `Mathlib/AlgebraicTopology/TopologicalSimplex.lean` |
| `Lib/AlgebraicTopology/SingularHomology/CrossProduct.lean` | L4 | none existing (Mathlib has no singular cross product); shape after `Mathlib/AlgebraicTopology/SingularHomology/Basic.lean` |
| `Lib/AlgebraicTopology/Hurewicz/CubeChainDecomposition.lean` | L5 | same as `CrossProduct` |
| `Lib/AlgebraicTopology/Hurewicz/PrismOperator.lean` | L6 | `Mathlib/AlgebraicTopology/SingularHomology/HomotopyInvariance.lean` (Mathlib's prism lives here) |
| `Lib/AlgebraicTopology/Hurewicz/Straightening.lean` | L7, L8 | shape after `Degree1.lean` (reference example) |
| `Lib/AlgebraicTopology/Hurewicz/Subdivision.lean` | L9's subdivision half | `Mathlib/AlgebraicTopology/SingularHomology/Basic.lean` (shape) |
| `Lib/AlgebraicTopology/Hurewicz/CubeGluing.lean` | L10 | none existing; shape after `SimplexPaths.lean` (reference example) |
| `Lib/AlgebraicTopology/Hurewicz/Degree.lean` | L11, L12, §14 | `Lib/AlgebraicTopology/Hurewicz/Degree1.lean` (the in-tree reference example is the twin) |
| `Lib/AlgebraicTopology/Hurewicz/HopfDegree.lean` | L14 | none existing; shape after `Degree1.lean` |
| `Lib/AlgebraicTopology/Hurewicz/CubeSphere.lean` | L13 (transport half) | `Mathlib/Topology/OnePoint.lean` (shape) |

Build order (dependency-respecting): `SimplexCube`, `CellFilling`, `HomotopyExtension`,
`CubeTriangulation`, `CrossProduct`, `CubeChainDecomposition`, `PrismOperator`,
`Straightening`, `Subdivision`, `CubeGluing`, `Degree`, `CubeSphere`, `HopfDegree`.

The consumers `Hopf/Recognition.lean` (the `pi*_subsingleton` instances,
`SpecialPeriods.Threefold.Homotopy*`, `threefoldHomotopyEquiv` — statement unchanged,
proof re-routed) and `Hopf/LCP/IntegralHomology.lean` recover the original degrees by
instantiation of the general `hurewiczLinearEquiv` at $n = 2, \dots, 6$.

---

# Axis 5 — current typed ledger (validated at `37fc1de8`)

This section supersedes the pre-landing plan preserved below. Lanes A and B are available in
`Lib/`; there are no project imports in the lane-C library. C10 and C13 now exist, including
both Hurewicz round trips and the general sphere-map classification. The names below are the
actual public declarations, not proposed renames. All are under `Mathoverflow1973`.

The aggregate provider imports `Lib.AlgebraicTopology.Hurewicz.HopfDegree` and
`Lib.Topology.Homotopy.CellFilling`. It aliases the thirteen outputs below; a separate consumer
checks all thirteen and constructs the degree-six equivalence. Both compiles exited 0.
See `C-INTERFACE_RECEIPT.md`. This is a current-head receipt, not a claim that the same
interface was present at the historical integration head `856e4762`.

## Common ChallengeNode fields

The following fields apply to every row; the row and exact signature complete the node.

```text
class: FREE
visibility: plain-import Lean files; noncomputable section; namespace Mathoverflow1973
imports: the production module in the table, available through the two aggregate imports above
signature: the exact declaration header in the corresponding code block below
destination: the namespace in the signature and the production module in the table
commit_boundary: the already-landed module boundary, with C10 assembly at 0a3b870 and C13 at c2059b6
focused_check: lake build <production module>
return_seam: Axis 5 for type/visibility discrepancies; Axis 1 for missing mathematical hypotheses
```

| id | source | production module | dependencies / representation | consumer |
|---|---|---|---|---|
| C1 | §§3,10 | `Lib.AlgebraicTopology.SingularHomology.CrossProduct` | `SingularChains`, `SingularHomology.homologyDesc`; local integer-module instances retained | C5, C6; torus consumers through shims |
| C2 | §3 | `Lib.AlgebraicTopology.Hurewicz.CubeTriangulation` | `cubeAffineSimplex`, `cubeVertex`; permutation-indexed cells | C6, C8, C9 |
| C3 | §4 | `Lib.AlgebraicTopology.Hurewicz.SimplexCube` | `simplexFlatHomeomorph`, `flatCubeHomeomorph`, `realCubeHomeomorph`; boundary iff | C7; C13 basepoint adjustment |
| C4 | §5 | `Lib.AlgebraicTopology.Hurewicz.HomotopyExtension` | `gluedBoundaryMap`, `cylinderRetraction`; bottom/side restrictions | C5, C7, C13 |
| C5 | §6 | `Lib.AlgebraicTopology.Hurewicz.PrismOperator` | `simplexPrism`, `SingularChains.chainLift`; family boundary identity | C7, C10 |
| C6 | §§3,10 | `Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition` | `fundamentalCubeChain`, `cubeChain_succ`, prism insertion identities | C10 |
| C7 | §8 | `Lib.AlgebraicTopology.Hurewicz.Straightening` | `edgeTower`, `normalizationStep`, `normalizationTower`; starts at simplex, based endpoint | C10 |
| C8 | §9 | `Lib.AlgebraicTopology.Hurewicz.Subdivision` | `nativeClass_eq_sum_simplices`; internal basedness required | C9, C10 |
| C9 | §§9,13 | `Lib.AlgebraicTopology.Hurewicz.CubeGluing` | `coherentCubeHomotopyMap`, boundary constancy; coherent endpoint | C7 boundary relation, C10 |
| C10 | §§11–13 | `Lib.AlgebraicTopology.Hurewicz.CubeSphere` | `hurewiczLinearEquiv`, `degreeTwoLinearEquiv`; `Nontrivial (Fin n)` supplied by `hn` | `Hopf.Hurewicz`, `Hopf.Recognition` |
| C11 | §16.1 | `Lib.AlgebraicTopology.Hurewicz.CubeSphere` | `OnePointCollapse.collapseLift`, `compactification`; `factorMap_comp_quotient` | C10 well-definedness, C13 |
| C12 | §§5.2,16.2 | `Lib.Topology.Homotopy.CellFilling` | `Sphere.exists_boundary_extension_of_pi`, `CylinderBall.boundaryHomeomorph` | `Hopf.Recognition` cell lifting |
| C13 | §§15–16 | `Lib.AlgebraicTopology.Hurewicz.HopfDegree` | `hurewiczMap_injective`, `basedSphereCube_homologyClass`, `factorMap_homotopyRel`; quotient sphere model | `sphere_homotopicRel_of_topClass_eq`, recognition |

The historical boundary numbers are not a dependency ordering: in particular C11's quotient
construction precedes C10's assembly inside `CubeSphere`. The import graph and declaration
order in the production files give the executable ordering. The more detailed C13 node ledgers
are in `C13-BOOTSTRAP.md` and `C13-CLASSIFICATION.md`; their historical `HigherHurewicz`
spellings were renamed to `Hurewicz` at `2d6cd4c`, with compatibility shims in `Hopf/LibShims.lean`.

### C1 — cross product on homology

```lean
def SingularHomology.crossProductHomology (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) :
    (SingularChains.singularComplex X).homology 1 →ₗ[ℤ]
      (SingularChains.singularComplex Y).homology n →ₗ[ℤ]
        (SingularChains.singularComplex (X × Y)).homology (n + 1)
```

### C2 — Kuhn simplex

```lean
def Hurewicz.CubeTriangulation.cubeSimplex {n : ℕ} (e : Equiv.Perm (Fin n)) :
    C(SingularChains.Simplex n, Hurewicz.CubeTriangulation.CubeN n)
```

### C3 — simplex–cube homeomorphism

```lean
def Hurewicz.simplexCubeHomeomorph (n : ℕ) :
    SingularChains.Simplex n ≃ₜ (Fin n → unitInterval)
```

### C4 — boundary homotopy extension

```lean
def SecondHurewicz.SimplyConnected.extendBoundaryHomotopy {n : ℕ} {X : Type*}
    [TopologicalSpace X] (f : C(SingularChains.Simplex n, X))
    (h : C(unitInterval × SecondHurewicz.SimplyConnected.SimplexBoundary n, X))
    (h0 : ∀ s, h (0, s) = f s.val) : C(unitInterval × SingularChains.Simplex n, X)
```

### C5 — simplexwise prism operator

```lean
def SecondHurewicz.SimplyConnected.simplexPrismOperator {X : Type} [TopologicalSpace X]
    (n : ℕ)
    (H : SingularChains.SingularSimplex X n → C(unitInterval × SingularChains.Simplex n, X)) :
    SingularChains.Chains X n →ₗ[ℤ] SingularChains.Chains X (n + 1)
```

### C6 — chain decomposition

```lean
theorem Hurewicz.cubeChain_eq_sum_simplices (n : ℕ) {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin n) X x) :
    Hurewicz.cubeChain p = ∑ e : Equiv.Perm (Fin n),
      Hurewicz.CubeTriangulation.cubeOrientation e •
        SingularChains.simplexChain X n
          (p.val.comp (Hurewicz.CubeTriangulation.cubeSimplex e))
```

### C7 — normalization family

```lean
def Hurewicz.normalizationHomotopy {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) (n : ℕ) (hpi : ∀ j, 2 ≤ j → j < n → Subsingleton (π_ j X x)) :
    SingularChains.SingularSimplex X n → C(unitInterval × SingularChains.Simplex n, X)
```

### C8 — subdivision class

```lean
theorem Hurewicz.NativeSubdivision.nativeCubeSubdivision_class {n : ℕ} [Nontrivial (Fin n)]
    {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x)
    (hp : Hurewicz.NativeSubdivision.NativeCubeInternalBased p) :
    Additive.ofMul (⟦p⟧ : π_ n X x) =
      ∑ e : Equiv.Perm (Fin n),
        Hurewicz.CubeTriangulation.cubeOrientation e •
          Hurewicz.SimplexGeometry.basedSimplexClass
            (Hurewicz.NativeSubdivision.nativeBasedCubeSimplex p hp e)
```

### C9 — coherent cube endpoint

```lean
def Hurewicz.CubeGluing.coherentCubeEndpoint {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (H₀ : C(SingularChains.Simplex n, X) → C(unitInterval × SingularChains.Simplex n, X))
    (H₁ : C(SingularChains.Simplex (n + 1), X) →
      C(unitInterval × SingularChains.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H₀ H₁)
    (hconst : H₀ (ContinuousMap.const (SingularChains.Simplex n) x) =
      ContinuousMap.const (unitInterval × SingularChains.Simplex n) x)
    (p : GenLoop (Fin (n + 1)) X x) : GenLoop (Fin (n + 1)) X x
```

### C10 — Hurewicz equivalence in every degree at least two

```lean
def Hurewicz.hurewiczLinearEquivOfTwoLE {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) (n : ℕ) (hn : 2 ≤ n)
    (hpi : ∀ j, 2 ≤ j → j < n → Subsingleton (π_ j X x)) :
    letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
    Additive (π_ n X x) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology X n
```

### C11 — factorization through the sphere quotient

```lean
def SphereCube.factorMap {n : ℕ} (hn : 0 < n) {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin n) X x) : C(SphereCube.Sphere n, X)
```

### C12 — cylinder filling

```lean
theorem CylinderFilling.exists_filling {V X : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [TopologicalSpace X] [PathConnectedSpace X] {d : ℕ}
    (hpi : ∀ n, 0 < n → n < d → ∀ x : X, Subsingleton (π_ n X x))
    (hd : Module.finrank ℝ V + 1 ≤ d) (f g : C(DiskCylinder.Disk (E := V), X))
    (H : C(unitInterval × DiskCylinder.Sphere (E := V), X))
    (h0 : ∀ s, H (0, s) = f (DiskCylinder.boundaryToDisk s))
    (h1 : ∀ s, H (1, s) = g (DiskCylinder.boundaryToDisk s)) (x : X) :
    ∃ G : C(unitInterval × DiskCylinder.Disk (E := V), X),
      (∀ z, G (0, z) = f z) ∧
        (∀ z, G (1, z) = g z) ∧ ∀ t s, G (t, DiskCylinder.boundaryToDisk s) = H (t, s)
```

### C13 — based sphere-map classification

```lean
theorem Hurewicz.sphere_homotopicRel_of_topClass_eq {m : ℕ} {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] {x : X}
    (hpi : ∀ j, 2 ≤ j → j < m + 2 → Subsingleton (π_ j X x))
    (f g : C(SphereCube.Sphere (m + 2), X))
    (hf : f (SphereCube.point (m + 2)) = x)
    (hg : g (SphereCube.point (m + 2)) = x)
    (h : SingularMayerVietoris.singularHomologyMap f (m + 2)
          (Hurewicz.cubeHomologyClass (SphereCube.quotientLoop (m + 2))) =
        SingularMayerVietoris.singularHomologyMap g (m + 2)
          (Hurewicz.cubeHomologyClass (SphereCube.quotientLoop (m + 2)))) :
    f.HomotopicRel g {SphereCube.point (m + 2)}
```

## Current limitations and provenance

* The local integer-module instances remain: the recorded removal experiment fails at four
  scalar-action elaboration sites. This is not a new axiom or a failed production build.
* Universe-zero spaces are required where the concrete integral singular-chain interface is
  used. Pure topology retains `Type*` where supported; the old blanket `Type*` promise below
  was inaccurate.
* `GenLoop` is the pinned Mathlib's root name. There is no outstanding naming question.
* The historical Stage-2 review is recovered in `C-STAGE2-REVIEW.md`; the source did not name
  its reviewer. Original attribution awaits the owner and is not fabricated here.
* Plain imports and the transitional `Mathoverflow1973`/`SecondHurewicz` namespaces remain.
  The requested `HigherHurewicz → Hurewicz` rename and the explicitly identified generic-name
  cleanups are landed. Complete Mathlib-root namespace/module-system conversion is not claimed.
* The historical prospectus mentioned a separately named general naturality theorem and a
  positive-degree homology-vanishing corollary. Those extra public wrappers are not part of the
  thirteen validated outputs; the degree-six naturality consumer remains proved in `Hopf`.
  They are not to be inferred from this receipt as separately exported declarations.

# Historical pre-landing Axis-5 plan (superseded)

The following is retained as provenance only. Its proposed names, blockers, and future-tense
claims are not the current interface; use the validated ledger above.

Ledger rows are given for the **headline nodes** of each commit boundary (one row per
boundary's public output cluster; the full per-declaration census is generated from the sources
at landing and appended to the lane report). Convention: *current name* is the green
declaration in `Hopf/` today (evidence, compiles at HEAD); *target signature* is the designed
`Lib/` interface. Because GLM's lane A (singular-homology core) has not landed, every row whose
signature mentions the chains/homology API has a **seam**: it is checked against the current
`Hopf/` names now and re-pointed at `Lib/AlgebraicTopology/SingularHomology/*` when A lands.
The aggregate `*_InterfaceCheck.lean` / `*_InterfaceConsumerCheck.lean` producer/consumer probe
and its receipt are therefore pending lane A; the probe plan and commands are in §20.

**Boundary C1 — `CrossProduct.lean`.**
Current: `PeriodTorusHigherHomology.crossProductEdge (X Y : Type) [TopologicalSpace X]
[TopologicalSpace Y] (n : ℕ) : FirstHurewicz.Chains X 1 →ₗ[ℤ] FirstHurewicz.Chains Y n →ₗ[ℤ]
FirstHurewicz.Chains (X × Y) (n + 1)` (Hurewicz.lean 2862) and
`PeriodTorusHigherHomology.crossProductHomology (X Y : Type) [TopologicalSpace X]
[TopologicalSpace Y] (n : ℕ) : (FirstHurewicz.singularComplex X).homology 1 →ₗ[ℤ]
(FirstHurewicz.singularComplex Y).homology n →ₗ[ℤ]
(FirstHurewicz.singularComplex (X × Y)).homology (n + 1)` (3740), with boundary laws
`crossProductEdge_boundary`, `crossProductTriangle_boundary` and naturality.
Target (Mathlib naming, twin-shaped):
`SingularHomology.crossProductChain₁ : Chains X 1 →ₗ[ℤ] Chains Y n →ₗ[ℤ] Chains (X × Y) (n+1)`
and `SingularHomology.crossProduct₁ : H₁(X) →ₗ[ℤ] Hₙ(Y) →ₗ[ℤ] H_{n+1}(X × Y)` with
`crossProduct₁_chainMap`, `…_boundary`, `…_natural`. Seam: `FirstHurewicz.Chains` /
`SingularMayerVietoris.SingularHomology` are lane A names.
**Hazard (recorded):** the two `@[instance_reducible]` defs
`PeriodTorusHigherHomology.integerLinearMapModule` / `integerTensorModule` (2152/2159) are
re-attached by `attribute [local instance] … in` at ≈200 + 39 sites. Disposition: *reproduce*
in the baseline commit (byte-faithful, both defs and their wrappers), then in a separate
`refactor` commit attempt to drop them in favor of Mathlib's instances for `Module ℤ (A →ₗ[ℤ]
B)` / `Module ℤ (A ⊗[ℤ] B)`; the attempt and its outcome (which diamond forces the local
instances, if any) are recorded in the lane report. The build at HEAD is the evidence the
reproduction suffices.

**Boundary C2 — `CubeTriangulation.lean`.**
Current: `HigherHurewicz.CubeTriangulation.{CubeN, cubeAffineSimplex, cubeVertex, cubeSimplex,
cubeOrientation, SortedCoordinates, …}` (16057–16613).
Target: `Hurewicz.CubeTriangulation.cubeSimplex (n : ℕ) (σ : Equiv.Perm (Fin n)) :
C(Simplex n, CubeN n)`, `cubeOrientation (σ) : ℤ`-valued sign, face-incidence lemmas
`cubeSimplex_face_zero / _last / _swap`. No seam (pure geometry over `Fin n → unitInterval`).

**Boundary C3 — `SimplexCube.lean`.**
Current: `HigherHurewicz.simplexCubeHomeomorph (n : ℕ) : FirstHurewicz.Simplex n ≃ₜ (Fin n →
unitInterval)` (436) + boundary-iff lemmas (440, 452) + the ambient version
`ambientSimplexCubeHomeomorph` (387).
Target: `Hurewicz.simplexCubeHomeomorph` with `…_boundary_iff`, `…_symm_boundary_iff`. Seam:
`FirstHurewicz.Simplex n` is lane A's standard-simplex type (moves to
`Lib/AlgebraicTopology/SingularHomology/*`).

**Boundary C4 — `HomotopyExtension.lean`.**
Current: `cylinderRetraction` (2018), `extendBoundaryHomotopy` (2116),
`SecondHurewicz.SimplyConnected.{isClosed_simplexBoundary, simplexFace_mem_boundary}` (85–117),
`glueFaceHomotopies` (1632).
Target: `Hurewicz.HomotopyExtension.{simplexPairHEP, cubePairHEP, extendBoundaryHomotopy,
glueFaceHomotopies}`. No lane-A seam (topology of simplices only).

**Boundary C5 — `PrismOperator.lean`.**
Current: `SecondHurewicz.prismOperator` (4414), `ThirdHurewicz.CubeSubdivision.prismSimplex` /
`prismRealization` (10280–10367), general `HigherHurewicz.prismCubeRealization` /
`orientedPrismRealization` (16769/16784).
Target: `Hurewicz.PrismOperator.prismChain`, `prismChain_boundary` (the Leibniz identity),
`prismChain_family` (face-compatible family form). Seam: chains API (A).

**Boundary C6 — `CubeChainDecomposition.lean` (G1).**
Current: the five pinned identities listed at L5 above, plus the recursion
`cubeChain_eq_curriedCrossProduct` (17471/23152/Rec 1128) and prism realization chain.
Target, one theorem at general `n`:
`Hurewicz.cubeChain_eq_sum_simplices {n : ℕ} {X : Type*} [TopologicalSpace X] {x : X}
(p : GenLoop (Fin n) X x) : cubeChain p = ∑ σ : Equiv.Perm (Fin n),
CubeTriangulation.cubeOrientation σ • simplexChain X n (p.val.comp
(CubeTriangulation.cubeSimplex σ))`
with `cubeChain` defined recursively by `crossProductChain₁` and the recursion lemma
`cubeChain_succ`. Seam: chains API (A); `GenLoop` is checked against the pinned Mathlib's
`HomotopyGroup.GenLoop` at the rename commit (the code uses the un-namespaced name).
**This boundary is new mathematics** (the general induction); it follows §10.3's proof.

**Boundary C7 — `Straightening.lean` (G2).**
Current: `HigherHurewicz.nativeCubeNullHomotopy {n} [Subsingleton (π_ n X x)]` (15093),
`simplexStraighteningHomotopy (n) (x) [Subsingleton (π_ n X x)]` (15183), vertex/edge storeys
(`vertexStraighteningHomotopy` 4916, `edgeStraighteningHomotopy` 4986, dimension-general),
`extendCoherentSimplexHomotopy` (5131), per-degree composed `normalizationKSimplexHomotopy`
(14121/15318/22252/Rec 186), `HigherHurewicz.straightenedCycle` + `_class` (15690–15758).
Target: `Hurewicz.Straightening.normalizationTower` — a recursive definition over `k ≤ n`
composing storey `k` (which needs `Subsingleton (π_ k X x)`) with the previous tower, returning
the face-compatible family; public outputs
`normalizationHomotopy (hpi : ∀ k, 2 ≤ k → k < n → Subsingleton (π_ k X x))`,
`straightenedCycle`, `straightenedCycle_class`. **New mathematics** (the recursion replaces the
unrolled compositions; §8's induction). Seam: chains API (A).

**Boundary C8 — `Subdivision.lean`.**
Current: `HigherHurewicz.NativeSubdivision.*` (18489–18782, 20616–22167: native cube pairs,
quarter turns, chamber charts, cut sequences, the Duffy machinery).
Target: same content under `Hurewicz.Subdivision.*`, docstringed. Pure move (already
general-`n`). Seam: none beyond A's chains.

**Boundary C9 — `CubeGluing.lean`.**
Current: `HigherHurewicz.CubeGluing.*` (19948–20581: `CubeCompatible`, `cubeFamilyMap`,
`glueCubeHomotopies`, `coherentCubeEndpoint`), `CubicalBoundary.*` (18323–19947, incl. the
universe-polymorphic `cubicalBoundaryValue_eq_zero`, 19893 — **keep `Type u`/`Type v` here; it
is the one declaration in the lane with forced universes**), `nativeClass_eq_sum_simplices`
(22057), `nativeCubeSubdivision_class` (22073), `basedSimplexBoundary_signed_relation` (19914).
Target: same, `Hurewicz.CubeGluing.*`; docstrings per the reference-example checklist. Pure
move (general-`n` already). Universe note: `cubicalBoundaryValue_eq_zero` keeps
`Type u`/`Type v` and says so in its docstring.

**Boundary C10 — `Degree.lean` (headline).**
Target headline signature (the generalized theorem):

```lean
theorem AlgebraicTopology.Hurewicz.hurewiczLinearEquiv {n : ℕ} (hn : 2 ≤ n)
    {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (hpi : ∀ k, 2 ≤ k → k < n → Subsingleton (π_ k X x)) :
    Additive (π_ n X x) ≃ₗ[ℤ] SingularHomology X n
```

built from `hurewiczMap` / `hurewiczInverse` (general-`n` forms of the current per-degree
defs), the round-trip lemmas `hurewiczMap_comp_hurewiczInverse`,
`hurewiczInverse_comp_hurewiczMap`, plus `hurewiczMap_apply` (the computation on a cube),
naturality `hurewiczLinearEquiv_natural` (current: Rec 1550), and the vanishing corollary from
section 14 (`subsingleton_singularHomology_of_lt` — new but one page). Module docstring per the
checklist: the theorem with its exact type, the textbook outline mapped to declaration names,
reference key `hatcher02`. Current evidence: the five pinned `hurewiczLinearEquiv` (8285,
14984, 22152, 23611, Rec 1492). Seam: `SingularMayerVietoris.SingularHomology` (A).
Consumers recover e.g. the degree-2 iso by `hurewiczLinearEquiv (n := 2) le_rfl x` with the
vacuous family `(fun k h2 hk => by interval_cases k)`, and the sphere bootstrap
`Degree.Sphere.piTwo..piFive_subsingleton` re-routes through the general theorem applied
inductively (section 15's bootstrap), statements unchanged.

**Boundary C11 — `CubeSphere.lean`.**
Current (pinned $n = 6$): `SixSphereCube.{cubeInteriorSphereHomeomorph, cubeSphereMap,
cubeSphereLoop, factorMap, factorMap_comp_cubeSphereMap, factor_cubeChain, factor_cubeCycle,
factor_cubeHomologyClass}` (Rec 1737–1955).
Target: general-`n` `Hurewicz.CubeSphere.{cubeSphereMap, cubeSphereLoop, factorMap, …}` with
`OnePoint (Fin n → unitInterval)`-side statements; the $n = 6$ instance recovers today's
declarations. Seam: none beyond A.

**Boundary C12 — `CellFilling.lean`.**
Current (already general): `Degree.Sphere.exists_boundary_extension_of_pi` (Rec 2510) and
`Degree.CylinderFilling.exists_filling` (Rec 2542), both with
`(hpi : ∀ n, 0 < n → n < d → ∀ x : X, Subsingleton (π_ n X x))` and
`Module.finrank ℝ V ≤ d` / `+1 ≤ d`.
Target: `Topology.Homotopy.CellFilling.{exists_boundary_extension_of_pi_subsingleton,
exists_cylinderFilling}` over a general finite-dimensional real normed space. Pure move.

**Boundary C13 — `HopfDegree.lean`.**
Current (pinned): `Degree.sphere_homotopicRel_of_topClass_eq` (Rec 3988, $n = 6$ hypotheses
spelled out), `Degree.Sphere.homotopic_id_of_topClass` (Rec 4025),
`Degree.right_inverse_is_left_inverse` (Rec 4044).
Target: general-`n` forms over `Hurewicz.CubeSphere.StandardSphere n`, the connectivity
hypotheses packaged as the subsingleton family; the $n = 6$ instance recovers today's
statements unchanged. The sphere connectivity bootstrap (section 15) is included here as
`sphere_pi_subsingleton_of_lt` (it needs lane A's $H_k(S^n) = 0$ for $k < n$ — seam — and lane
B's simply-connectedness of spheres, imported from `Hopf` until B lands, recorded as a
dependency).

---

# Historical open items, seams, probes (superseded)

This list records the pre-landing plan, not the current status. The live status and validated
signatures are in the current Axis-5 section above and `Lib/reports/C.md`.

1. **Lane-A seam (blocking).** Every signature mentioning
   `FirstHurewicz.Chains`/`FirstHurewicz.SingularSimplex`/`FirstHurewicz.singularComplex`/
   `SingularMayerVietoris.SingularHomology`/`ModuleHomology.Cycle` re-points to lane A's
   `Lib/AlgebraicTopology/SingularHomology/*` names when A lands. The aggregate Axis-5
   interface probes (`C_InterfaceCheck.lean`, `C_InterfaceConsumerCheck.lean`) and the receipt
   `Lib/docs/C-INTERFACE_RECEIPT.md` are scheduled then; commands:
   `lake env lean Lib/AlgebraicTopology/Hurewicz/C_InterfaceCheck.lean` and likewise for the
   consumer probe, at HEAD with the A commits named in the receipt.
2. **Lane-B seam (minor).** `SimplyConnectedSpace Sⁿ` is used from `Hopf/` until B lands;
   recorded dependency, no `Hopf/` import will remain after B. (The degenerate-simplex lemma
   of section 12.1 was found in review to need no input at all — the constancy argument — and
   the previously listed `π_{n-1}(S^{n-2}) = 0` input is deleted: that group is
   *not* zero — $\pi_3(S^2) = \mathbb{Z}$ — and the text never needed it.)
3. **The ℤ-module diamond** (hazard from the task): disposition per boundary C1 — reproduce
   first, then attempt removal; outcome recorded in the lane report.
4. **Universe choice.** `Type*` everywhere except
   `CubicalBoundary.cubicalBoundaryValue_eq_zero`, which keeps its `Type u`/`Type v`
   polymorphism (the evaluator is applied at different levels); stated in its docstring.
5. **Bib keys.** Only `hatcher02` exists in the pinned Mathlib `docs/references.bib`. The
   docstrings cite Hatcher Thm. 4.32 / Cor. 4.25 / Thm. 2.10 / Prop. 0.16 / Prop. 2.30 under
   that key; no new keys needed for this lane.
6. **Vanishing corollary (section 14)** is new surface not present as a standalone theorem in
   the code today (the code gets the equivalent through the equivalence + homology vanishing);
   it is included in C10 as `subsingleton_singularHomology_of_lt` — flagged here so the
   reviewer checks it is wanted at that generality.
7. **`GenLoop` naming.** The code uses un-namespaced `GenLoop (Fin n) X x`; confirm against
   pinned Mathlib (`HomotopyGroup.GenLoop`) at the rename commit.
8. **Review.** Stage-2 independent review of sections 1–16: done (`~/s6-notes/C-review.md`);
   one blocker (the false `π_{n-1}(S^{n-2}) = 0` citation — repaired by the constancy
   argument) and six corrections (the two-ball cut lemma at its natural generality with the
   boundary-preserving isotopy; the wedge-of-cubes homology slip repaired by the pair
   formulation; the genuine-cycle replacement for normalized cycles; the class operator's
   well-definedness restated as functionality in the chain; the cone criterion fixed; the
   $\Delta$-complex and boundary-preserving phrasings) incorporated. Verified as correct as
   written: the chain-identity sign computation (3.3), the tower (8.1), the non-circular
   bootstrap (15), and the cross-product insertion signs (10.3).
