# Lane F — textbook, decomposition, placement, and typed ledger

**The Whitney trick, signed intersection numbers, handle slides, and integer-matrix
reduction** (Milnor, *Lectures on the h-cobordism theorem*, §6–7: Thm. 6.6 and Thm. 7.6; Smale,
*Generalized Poincaré's conjecture in dimensions greater than four*, §4–5; Hatcher Prop. 2.30),
generalized from the six-dimensional, index-$(2,3)$ formalization to sheets of complementary
dimensions in arbitrary codimension.

Contents:

* **Axis 1** (§§1–10): the complete textbook proofs, ordinary mathematics, no Lean names.
* **Axes 2–3** (§11): additive decomposition in dependency order.
* **Axis 4** (§12): placement with Mathlib twins.
* **Axis 5** (§13): typed ledger with seams on lanes A, D1, D2, E1, E2.
* **Open items** (§14).

---

# Axis 1 — the textbook proofs

## 1. The theorems

**(F1) Signed intersection number (Hatcher Prop. 2.30 in disguise).** Let $A^p, B^q$ be
oriented embedded submanifolds of the oriented $(p+q)$-manifold $N$, meeting transversely. Then
$A \cap B$ is finite when both are compact (lane E2), each intersection point carries a sign
$\varepsilon(x) = \pm 1$ (the orientation of $T_x A \oplus T_x B$ against $T_x N$), and the
signed count
$\sum_x \varepsilon(x)$ equals the homological intersection pairing — concretely,
the degree of the collapse map that collapses the complement of a tubular neighborhood of $B$
onto the Thom space of its normal bundle, read homologically (the Thom class localized at the
intersection points; §3). For maps between equidimensional manifolds this specializes to
Hatcher's Prop. 2.30: *the degree of a map equals the sum of its local degrees at the preimages
of a regular value* — the form the code's cell-filtration collapse uses.

**(F2) The Whitney lemma (Milnor, h-cobordism Thm. 6.6).** Let $A^p, B^q \subseteq N^m$ be
connected, compact, oriented, embedded submanifolds of a boundaryless $m$-manifold, $p + q = m
\geq 5$, $p, q \geq 2$, meeting transversely, and let $x_0, x_1 \in A \cap B$ have opposite
signs. Assume the loop formed by arcs from $x_0$ to $x_1$ in $A$ and in $B$ is nullhomotopic in
the complement of (the relevant closed part of) $A \cup B$ — in the strong form used by the
handle calculus: every circle in the ambient level contracts in the complement. Then there is a
compactly supported ambient isotopy $A_t$ of $A$, fixed near every other intersection point,
with $A_1 \cap B = (A \cap B) \setminus \{x_0, x_1\}$; the remaining intersection signs are
unchanged.

**(F3) Handle slides and the intersection matrix (Milnor §7).** For a Morse function with
ordered critical points and a regular level $N$ separating the index-$k$ handles (below) from
the index-$(k+1)$ handles (above), the *middle matrix* $M$ — rows indexed by the index-$k$
handles, columns by the index-$(k+1)$ handles, entries the signed intersection numbers of belt
and attaching spheres in $N$ — is the boundary matrix of the handle chain complex; in
particular the homology of the pair (upper sublevel, lower sublevel) is computed by $M$.
Sliding the $i$-th handle over the $j$-th handle ($i \neq j$) with multiplicity $c \in
\mathbb{Z}$ is realizable geometrically (without changing the critical points' values or the
other handles) and right-multiplies $M$ by the transvection $I + c\, E_{ji}$; and every
sequence of elementary column operations is realized by a sequence of handle slides.

**(F4) Integer reduction (Milnor Thm. 7.6's algebra).** (a) A surjective $1 \times n$ integer
matrix (a *unimodular row*) can be reduced by elementary column operations to a row containing
$\pm 1$. (b) A presentation $\mathbb{Z}^c \to \mathbb{Z}^r \twoheadrightarrow G$ of the trivial
group $G = 0$ has a surjective presentation matrix. Hence: a handle system whose middle matrix
presents the zero group (a homology sphere's middle level) can be reduced by handle slides to a
system whose matrix contains a unit entry, which (F2) + (F1) turn into a geometrically
cancellable pair.

## 2. Conventions and standing inputs

Manifolds are smooth and boundaryless unless stated; the Morse infrastructure (Morse functions,
handles, attaching and belt spheres, regular levels, gradient flows) is lanes D1/E1 material,
cited by name; transversality, ambient isotopy, arcs, tubular neighborhoods, and the finite
intersection theorem are lanes E2/D2, cited by name; singular homology, the local-degree
machine, and the sphere computations are lane A. The lane's own algebra files (transvections,
integer presentations) depend on nothing beyond linear algebra over $\mathbb{Z}$ and land
first.

Orientations: all signs come from oriented determinants of explicit frames. The conventions
are fixed once: at an intersection point, $T_x N$ is oriented against (a normal frame of $B$,
then a frame of $B$) — equivalently, via the transversality identifications $\nu B \cong T_x A$
and $\nu A \cong T_x B$, against (a frame of $A$, then a frame of $B$) — and the normal bundle
$\nu B$ is oriented by the normal-first splitting $o(\nu B) \wedge o(TB) = o(TN)|_B$; the
bridge "opposite intersection sign $\iff$ opposite corner determinant" is proved once (§5) and
used everywhere. (The code's sphere-normal Jacobian is the (normal of $B$, normal of $A$)
reading; the two readings agree by the transversality isomorphism.)

## 3. The signed intersection number and the local-degree theorem

**Definition.** With $A^p, B^q \subseteq N^{p+q}$ transverse as in (F1), the intersection set
$A \cap B$ is finite (E2, T10). At $x \in A \cap B$, transversality makes
$T_x A \oplus T_x B \to T_x N$ an isomorphism; $\varepsilon(x)$ is its determinant sign against
the orientations. The *signed intersection number* is
$$\langle A, B \rangle := \sum_{x \in A \cap B} \varepsilon(x),$$
with $B$ connected in the handle application (a sphere), which is where the Thom-side degree
formulation below is used.
**Isotopy invariance.** A compactly supported isotopy of either sheet changes the intersection
set by the birth/death of opposite-sign pairs (a generic 1-parameter family has finitely many
birth-death times, each creating or annihilating one $+$ and one $-$ point; at the births
themselves the intersection is a tangency with sign $0$ in either orientation count), so
$\langle \cdot, \cdot \rangle$ is invariant. (The formalization proves invariance through the
homological identification below rather than through the 1-parameter argument; both are
correct, the homological one is cheaper in Lean.)

**The local-degree theorem.** *The signed count equals the degree of the collapse.* Let $\tau
\colon N \to \mathrm{Th}(\nu B)$ be the collapse onto the Thom space of the normal bundle of
$B$ (tubular neighborhood — lane D2), with $B$ connected so that
$H_p(\mathrm{Th}(\nu B)) \cong H_0(B) \cong \mathbb{Z}$ (Thom isomorphism); orient $\nu B$ by
the normal-first convention of §2, which fixes the generator. Then
$\langle A, B \rangle = \deg(\tau \circ \iota_A)$.
*Proof.* This is a homological localization, not the equidimensional local-degree formula:
with $u \in H^p(\mathrm{Th}(\nu B))$ the Thom class, $\deg(\tau \circ \iota_A) = \langle
\tau^* u, [A] \rangle$; the pullback $\tau^* u$ is the Poincaré dual of $[B]$ in $N$; the
evaluation $\langle \tau^* u, [A] \rangle$ localizes by excision to the finite set
$A \cap B$; and in the crossing charts of E2 §12 the fibre projection of $A$ at $x$ is an
oriented linear isomorphism of determinant sign $\varepsilon(x)$ (with the normal-first
convention — writing $o(TA) = \lambda\, o(\nu B)$ through the transversality isomorphism,
$o(TA) \wedge o(TB) = \lambda\, o(\nu B) \wedge o(TB) = \lambda\, o(TN)$, so the local
degree at $x$ is exactly $\varepsilon(x)$, with no hidden global sign). Hence the evaluation
is $\sum_x \varepsilon(x)$. $\square$
(The code proves the equidimensional instance of the same fact: the cell-filtration collapse
of the level onto a wedge of $k$-spheres, where the attaching map runs between
equal-dimensional manifolds and Hatcher's Prop. 2.30 applies verbatim — the
`collapse_homology_signed_count` statement. The Thom formulation above is the same identity
read through the tubular collapse.)

In the handle-calculus application $A$ is the attaching sphere $S^k$ of an index-$(k+1)$
handle, $B$ is the belt sphere $S^{m-k}$ of an index-$k$ handle, $N$ is the intermediate
level, and the collapse map is the handle collapse: *the boundary coefficient of the handle
chain complex equals the signed intersection count.* This is the content of the code's
`collapse_homology_signed_count` family, stated there for the cell-filtration collapse maps.

## 4. The Whitney bigon model

The model lives in $\mathbb{R}^2 \times \mathbb{R}^{p-1} \times \mathbb{R}^{q-1}$,
$m = p + q = 2 + (p - 1) + (q - 1)$. In the $\mathbb{R}^2$ factor with coordinates $(s, t)$ and
a fixed height $h > 0$, the two model curves are the line $L_0 = \{t = 0\}$ and the parabola
$L_1 = \{t = h(1 - s^2)\}$; they cross at $s = \pm 1$ (the *corners*) and bound the *bigon*
$$B_h := \{(s, t) : 0 \leq t \leq h(1 - s^2)\},$$
a compact 2-disc. The model sheets are the submanifolds
$$A_{\mathrm{mod}} := L_0 \times \mathbb{R}^{p-1} \times \{0\}, \qquad
B_{\mathrm{mod}} := L_1 \times \{0\} \times \mathbb{R}^{q-1},$$
of dimensions $p$ and $q$ in the model space of dimension $m$; they meet exactly at the two
corners $(\pm 1, 0, 0, 0)$. The corner determinant of the model frames is computed directly: with the sheet frames
$\partial_s$ (the line) and $\partial_s - 2hs\,\partial_t$ (the parabola), the planar
determinant is $-2hs$ at the corner $(s, 0)$ — that is $+2h$ at $s = -1$ and $-2h$ at
$s = +1$ (or the global negative, with the opposite sheet order): the two corners have
*opposite* intersection signs. This is the only property of the model that the rest of the proof uses, and it is the
reason for the hypothesis "opposite signs" in (F2).

## 5. The framing bridge

Suppose $A, B$ meet transversely at $x_0, x_1$ with opposite signs, and arcs $\alpha \subseteq
A$, $\beta \subseteq B$ join $x_0$ to $x_1$ (arcs exist because $p, q \geq 2$ — the sheets are
connected and a generic arc avoids the finitely many other intersection points, since
$\dim A, \dim B \geq 2$ implies an arc in general position misses a finite set). Along the
loop $\alpha \cup \beta$ the normal data must be compatible for a bigon to be framed:

**Lemma (the sign/determinant bridge).** *Opposite intersection signs at the two corners are
equivalent to: the two normal frames of $\alpha$ in $A$ and of $\beta$ in $B$ extend over the
loop to a trivialization of the normal bundle of a bigon field, with the corner transition a
reflection in the bigon plane.* In the code this is the chain
`opposite_beltIntersectionSigns_iff_Whitney_corners` — opposite signs iff the corner
$2 \times 2$ determinants (the `PlanarFrame` areas of the two sheet frames at each corner) have
opposite signs — proved by transporting both sign conventions to the same oriented reference
frame (the sphere-normal Jacobian on one side, the strip-normal determinant on the other) and
comparing. The content: the signed intersection data is exactly the obstruction data for the
bigon's normal framing, so "opposite signs" is precisely the hypothesis under which the model
chart of §4 can be fitted onto the loop.

## 6. The Whitney lemma (proof of F2)

With the arcs $\alpha, \beta$ and the framing lemma of §5 in hand:

*Step 1 (the loop and its filling).* The loop $\alpha \cup \beta$ lies in $A \cup B$; by the
hypothesis it bounds a map of a disc into the ambient manifold, and by the strengthened
hypothesis (every circle contracts in the complement of the sheets' remaining intersection
data) the disc can be taken disjoint from the other intersection points. This is the only place
where a global hypothesis enters; in the handle application it is the simply-connectedness of
the relevant level complement, recorded as the hypothesis `hnull`.

*Step 2 (the embedded bigon).* The disc map is made immersion-generic rel boundary, then
embedded — for $m = p + q \geq 5$ this is already general position: the generic double-point
set of a 2-disc has dimension $4 - m \leq -1$, i.e. is empty, so immersion-generic rel
boundary is embedding-generic. It remains to clear the interior intersections with the sheets.
General position puts the 2-dimensional disc interior disjoint from $A$ when $2 + p < m$ and
from $B$ when $2 + q < m$; when $q = 2$ (symmetrically $p = 2$) — the codimension-2 case,
which is exactly the code's case $(p, q) = (2, 3)$ in a $5$-manifold, where $2 + 3 = 5$ is
*not* $< 5$ — the residual interior intersections with the codimension-2 sheet are isolated
points, removed one at a time by *piping* (Milnor's Lemma 6.7): for each residual point choose
a simple arc **in the disc** from the point to the boundary arc $\beta$ (which lies in the
sheet), avoiding the other residual points — automatic, since the disc is 2-dimensional — and
isotope the sheet in a neighborhood of that arc, pushing the intersection point within the
disc until it leaves across $\beta$; the framing keeps the push embedded. The details are the
code's `exists_filled_bigon_of_complement_contractions` chain. Result: an embedded bigon
$\iota \colon B_h \hookrightarrow N$ with boundary arcs on $A$ and $B$, interior disjoint from
$A \cup B$, clean germs at the two corners.

*Step 3 (the tubular chart).* The bigon's normal bundle is trivialized by the framing of §5
(the opposite-sign hypothesis is used here and nowhere else: it is what makes the two sheet
framings join across the corners). Extend $\iota$ to a chart
$B_h \times D^{m-2} \hookrightarrow N$ — a *tubular bigon* — in which the sheets are exactly
the model sheets of §4 in their respective normal directions: $A \cap \text{chart} = A_{\mathrm{mod}}$,
$B \cap \text{chart} = B_{\mathrm{mod}}$, near the bigon. This uses the tubular neighborhood
theorem (lane D2) plus the strip/germ machinery that prescribes the 1-jets along the two
boundary arcs (the code's `StripNormalData` and the `RankThreeCompatibleChart` construction at
$(p, q) = (2, 3)$).

*Step 4 (the model cancellation).* In the model of §4 there is an explicit compactly supported
isotopy moving $A_{\mathrm{mod}}$ off $B_{\mathrm{mod}}$: choose a smooth height function
$\varphi \colon \mathbb{R} \to [0, \infty)$, compactly supported slightly beyond $[-1, 1]$,
with $\varphi(s) > h(1 - s^2)$ on the **closed** interval $[-1, 1]$ (the strict inequality at
the endpoints is what removes the corners), and push $L_0$ vertically to $t = \varphi(s)$ over
the bigon (the *graph motion*),
blended to the identity outside a compact neighborhood with a cutoff in the normal directions.
The two model intersections are exactly the two corners, and the pushed line is disjoint from
the parabola. The isotopy is elementary and explicit (this is the code's `GraphMotion`
structure and `exists_supported_native_bigon_cancellation`).

*Step 5 (transport and support).* Transport the model isotopy through the chart of step 3 and
extend by the identity (isotopy extension, lane E2). The result is a compactly supported ambient
isotopy of $N$, supported in the chart, moving $A$ to $A_1$ with
$A_1 \cap B = (A \cap B) \setminus \{x_0, x_1\}$; on the boundary germ of the chart the isotopy
is stationary, so every other intersection point and its sign is untouched. $\square$

## 7. Finite signed cancellation

Iterate (F2): while two intersection points of opposite signs exist, remove a pair. The
intersection set is finite (E2 T10) and shrinks by two at each step, so the process terminates
with an intersection set of one sign; the signed count is invariant (§3), so the terminal
number of points is $|\langle A, B \rangle|$. In particular:

**Corollary (the single-intersection criterion).** *If $\langle A, B \rangle = \pm 1$ then,
after a compactly supported isotopy, $A \cap B$ is a single point.* This is the geometric input
to the handle-cancellation theorem (lane G): a pair of handles whose attaching and belt spheres
meet once geometrically cancels (first cancellation theorem, lane E1).

## 8. The intersection matrix and handle slides

**The middle matrix.** Let $f$ be a Morse function with ordered critical points (lane E1:
rearrangement) and $N = f^{-1}(a)$ a regular level separating the index-$k$ handles (below)
from the index-$(k+1)$ handles (above). Fix a basis of the relative homology
$H_k(\text{lower sublevel})$ — geometrically, the cores of the index-$k$ handles. The attaching
sphere of the $j$-th index-$(k+1)$ handle meets the belt sphere of the $i$-th index-$k$ handle
in $N$ in finitely many signed points (§3), and
$$M_{ij} := \big\langle \text{belt}_i,\ \text{attaching}_j \big\rangle \in \mathbb{Z}.$$
By §3's local-degree theorem, $M_{ij}$ equals the coefficient of the $i$-th core class in the
attaching class of handle $j$ — i.e. $M$ is the matrix of the boundary map
$H_{k+1}(\text{upper}, N) \to H_k(N) \to H_k(\text{lower})$ of the handle filtration: the
middle matrix *is* the handle chain complex's boundary in the middle degree.

**The slide theorem.** *Sliding handle $j$ over handle $i$ with multiplicity $c \in
\mathbb{Z}$ is realizable by an isotopy of the attaching map (hence by a modification of $f$,
unchanged below the level and with the same critical points and indices) and right-multiplies
$M$ by the transvection $I + c\,E_{ij}$ (adding $c$ times column $i$ to column $j$); every
finite sequence of elementary column **additions** is realized by a sequence of slides, and a
column sign-change is realized by reorienting the attaching sphere/core.* The geometric step:
choose an arc from the $j$-th
attaching sphere to the $i$-th — it exists because the level is connected, which holds in the
handle-calculus setting after the outer indices are eliminated (a standing hypothesis of this
section, satisfied in the application); the arc
is made embedded and transverse by lane E2; tube it; deform the $j$-th attaching sphere along the
tube to add $c$ copies of the $i$-th belt-linked sphere (the *passage* construction — a
longitudinal motion in the tube realizing the connected sum at the level of homology classes),
which adds $c$ times the $i$-th column to the $j$-th column of $M$ by §3 applied to the new
intersections; all of it supported away from the other handles. (This is the code's
`exists_arbitrary_column_addition`/`exists_arbitrary_column_sequence`, built from
`LongitudinalTubeMotion` and the sheet-passage lemmas; its convention — class $i$ gains
$k$ times class $q$ is `M * Matrix.transvection q i k` — is the same one.)

*(Sign-order note: §3's sign is defined for the ordered pair (attaching, belt) while $M_{ij}$
here is belt-first; the two orders differ by the entry-independent global sign
$(-1)^{k(m-k)}$, invisible to surjectivity, unit entries, and the pivot chain.)*

## 9. The integer algebra

**(a) Transvections preserve surjectivity** of a matrix's row map, since $I + cE_{ji}$ is
invertible over $\mathbb{Z}$ (its inverse is $I - cE_{ji}$).

**(b) Unimodular-row reduction (the Euclidean algorithm by column operations).** Let
$v = (v_1, \dots, v_n) \in \mathbb{Z}^n$ with $\gcd(v_1, \dots, v_n) = 1$ (equivalently the
$1 \times n$ matrix is surjective). If two entries $v_i, v_j$ are nonzero, the column operation
$v_j \mapsto v_j - q v_i$ with $q = \lfloor v_j / v_i \rfloor$ replaces $v_j$ by a remainder
with $|v_j'| < |v_i| \leq |v_j|$ or $v_j' = 0$; iterating (the Euclidean algorithm on the pair)
reduces the pair to $(\gcd(v_i, v_j), 0)$; iterating over pairs reduces the row to
$(\pm 1, 0, \dots, 0)$ up to order. Termination is the well-founded descent on the measure
$\sum_k |v_k|$, which strictly decreases at every step; the operations are transvections, so
the reduction is a product of elementary column operations.

**(c) Trivial-group presentations are surjective.** If
$\mathbb{Z}^c \xrightarrow{M} \mathbb{Z}^r \to G \to 0$ is a presentation of the trivial group,
then $\mathbb{Z}^r \to G$ is zero and surjective, so $M$'s image is all of $\mathbb{Z}^r$: $M$
is surjective. (The structure of an *integer presentation* — a linear map with a distinguished
spanning set of its kernel — packages exactly this data for the handle application, where the
presentation is furnished by the handle filtration and the "trivial group" is the vanishing
middle homology of a homology sphere.)

**(d) The pivot corollary.** Combining: a middle matrix of a homology-sphere handle system is
surjective (c), its row functionals are unimodular rows, (b) reduces some row to contain
$\pm 1$, and by (F3) the reduction is realized by handle slides. The resulting unit entry is
the algebraic hypothesis for the single-intersection criterion (§7's corollary), which (F2)
converts to a geometric single intersection — here the standing hypothesis that the level's
circles contract in the complement (simple connectivity of the level, *not* merely the homology
vanishing) is load-bearing, and it is satisfied in the h-cobordism application — which lane
E1's first cancellation theorem then turns
into a pair cancellation. This chain is Milnor's proof of the basis theorem (Thm. 7.6)
specialized to the h-cobordism's middle levels.

## 10. What stays CHARGED

Everything mentioning the six-sphere homotopy type, the specific handle systems of the
project's manifold, and the $n = 6$ instantiations stays in `Hopf/` as thin adapters: the Lib
statements quantify over $p, q, m$ (Whitney side) and $k, n$ (handle side). The pinned model
data (`Plane`, `RankThreeWhitneyModel.Lower = ℝ¹`, `Upper = ℝ²`, normal rank 3, ambient
dimension 6, index 2/3, `Hemisphere.Sphere 2`) is recovered by instantiating $p = 2$, $q = 3$
(sheets in the 5-level), $m = 5$ / ambient $n = 6$, and $k = 2$ in this document's convention
(§8: the lower handle index); the code's row-F11 convention names the *upper* index, $k = 3$
there.

---

# Axes 2–3 — additive decomposition, in dependency order

| # | Lemma (§) | Inputs | Output | Current `Hopf/` home |
|---|---|---|---|---|
| F0a | Transvection algebra (§9a–b) | Mathlib `Matrix.transvection` | surjectivity preservation; unimodular-row reduction | Recognition 3357–3366, 4737–4760, 7412–7558 (pure) |
| F0b | Integer presentations (§9c–d) | Mathlib linear algebra | `IntegerPresentation` structure + triviality criterion | SphereTopology 14171–14257 + 14312–14360 (pure part; geometric gluers 14258–14311 stay for F10) |
| F1 | Signed intersection number (§3) | E2 (T10, crossing charts), A (local degree) | sign, count, invariance, local-degree identity | SingularHomology 11385–11615 (`SphereNormalCoordinates`, `beltIntersection*`) |
| F2 | Bigon model (§4) | analysis of one parabola | the model, corner sign computation | SingularHomology 17041–17244 (`WhitneyPairModel`) |
| F3 | Strip/normal data (§5) | E2 charts | `StripNormalData`, sheet transitions, germ prescription | SingularHomology 16318–17040, 19783–20680 |
| F4 | Framing bridge (§5) | F1, F3 | opposite signs ⇔ opposite corner determinants | SingularHomology 20780–22214 |
| F5 | Bigon filling (§6 steps 1–2) | circle contractions (`hnull`), E2 | embedded clean bigon from opposite-sign pair | SingularHomology 18365–18488 (DiskCone), 18489–18730 (AnnularExtension), 19302–19591, 22316–23000 |
| F6 | Graph motion (§6 step 4) | F2 | the explicit model isotopy | SingularHomology 25071–25818 (`GraphMotion*`, `RankThreeWhitneyModel`) |
| F7 | The Whitney step (§6; **G-F1**) | F2–F6 + E2 isotopy extension + D2 tubular | the relative cancellation isotopy | SingularHomology ~20490–23150 (headline 22999) |
| F8 | Finite cancellation and single intersection (§7) | F7, F1 | pair removal iteration; single-intersection criterion | SphereTopology 6364–6660 (`FiniteSignedCancellation`, belt cancellation chain); Recognition 8195–8479 |
| F9 | Arcs and tubes (§8 geometry) | E2 (arcs, isotopy) | sheet arc tubes; longitudinal tube motion | SurgeryWindows 15078–15800 (`exists_sheet_arc_tube`, `longitudinalBlend*`/tube motion); Recognition 4709 |
| F10 | Attaching classes and the middle matrix (§8) | A, E1, F1 | `middleSectionClass`, `classCoordinateMatrix` (F0a-landed), `canonicalMiddleMatrix`, `middleMatrix`; matrix = boundary | Recognition 2800, 3359; SphereTopology 14258–14500 (geometric part incl. `middlePresentation`/`middleMatrix`) |
| F11 | Handle slides (§8) | F9, F10 | slide = transvection; every column op realized | Recognition 6582–7283 (geometry part) |
| F12 | The pivot chain (§9d) | F0a, F0b, F11 | primitive unit from a surjective presentation | Recognition 7365–7645, 9182–9200 |

Dependency order is row order; F0a/F0b land first (no lane dependencies — pure algebra over
Mathlib's matrix library; they are the one part of lane F executable before the GLM lanes
land, and the task orders them first).

---

# Axis 4 — placement

| File | Rows | Mathlib twin |
|---|---|---|
| `Lib/LinearAlgebra/Matrix/TransvectionReduction.lean` | F0a | `Mathlib/LinearAlgebra/Matrix/Transvection.lean` (exists; this file is its reduction-theory companion) |
| `Lib/Algebra/Module/IntegerPresentation.lean` | F0b | `Mathlib/LinearAlgebra/FreeModule/PID.lean` / `Mathlib/LinearAlgebra/…/SmithNormalForm` (shape; the structure is the presentation form of f.g. ℤ-modules) |
| `Lib/Geometry/Manifold/Whitney/IntersectionNumber.lean` | F1 | none existing |
| `Lib/Geometry/Manifold/Whitney/StripNormalData.lean` | F3 | none existing |
| `Lib/Geometry/Manifold/Whitney/BigonModel.lean` | F2 | none existing |
| `Lib/Geometry/Manifold/Whitney/Framing.lean` | F4 | none existing |
| `Lib/Geometry/Manifold/Whitney/Filling.lean` | F5 | none existing |
| `Lib/Geometry/Manifold/Whitney/GraphMotion.lean` | F6 | none existing |
| `Lib/Geometry/Manifold/Whitney/Trick.lean` | F7 | none existing |
| `Lib/Geometry/Manifold/Whitney/BeltCancellation.lean` | F8 | none existing |
| `Lib/Geometry/Manifold/Whitney/ArcTube.lean` | F9 (arc half) | none existing |
| `Lib/Geometry/Manifold/Whitney/LongitudinalMotion.lean` | F9 (tube half) | none existing |
| `Lib/Geometry/Manifold/Morse/AttachingClass.lean` | F10 (classes) | none existing |
| `Lib/Geometry/Manifold/Morse/IntersectionMatrix.lean` | F10 (matrix) | none existing |
| `Lib/Geometry/Manifold/Morse/HandleSlide.lean` | F11 | none existing |
| `Lib/Geometry/Manifold/Morse/SingleIntersection.lean` | F12 + F8's corollary | none existing |

---

# Axis 5 — typed ledger

Seams: everything manifold-level depends on GLM's D1 (Morse data), D2 (tubular), E1
(rearrangement/cancellation) and my E2 (transversality, isotopy extension, arcs) — until those
land, the ledger rows are checked against the `Hopf/` names. F0a/F0b have no lane seams and can
be built against the pinned Mathlib today.

**Row F0a (LANDED).** Exact signatures (the scout map's Recognition coordinates
6367+/9042+ were stale; the decls moved out of Recognition 3357/4737+/7412+ pre-move
positions into `Lib/LinearAlgebra/Matrix/TransvectionReduction.lean`):

```lean
def MorseCancel.classCoordinateMatrix {A : Type} [AddCommGroup A] [Module ℤ A] {r n : ℕ}
    (B : (Fin r → ℤ) ≃ₗ[ℤ] A) (v : Fin n → A) : Matrix (Fin r) (Fin n) ℤ
  -- Recognition 3357; classCoordinateMatrix_mulVec at 3361 moves with it
theorem MorseCancel.mul_transvection_surjective {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℤ)
    (i j : Fin n) (hij : i ≠ j) (k : ℤ) (hA : Function.Surjective A.mulVec) :
    Function.Surjective (A * Matrix.transvection i j k).mulVec  -- Recognition 4737
theorem MorseCancel.eq_mul_transvection_of_columns {r n : ℕ} (A A' : Matrix (Fin r) (Fin n) ℤ)
    (i j : Fin n) (k : ℤ) (hchanged : ∀ u, A' u j = A u j + k * A u i)
    (hother : ∀ u v, v ≠ j → A' u v = A u v) : A' = A * Matrix.transvection i j k
  -- Recognition 4747
theorem MorseCancel.mul_transvection_list_surjective {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℤ)
    (hA : Function.Surjective A.mulVec) (ops : List (Fin n × Fin n × ℤ))
    (hvalid : ∀ op ∈ ops, op.1 ≠ op.2.1) :
    Function.Surjective
      (A * (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod).mulVec
  -- Recognition 7412
theorem MorseCancel.primitive_row_has_unit_after_column_additions {n : ℕ}
    (A : Matrix (Fin 1) (Fin n) ℤ) (hA : Function.Surjective A.mulVec) :
    ∃ ops : List (Fin n × Fin n × ℤ),
      (∀ op ∈ ops, op.1 ≠ op.2.1) ∧
        ∃ i : Fin n,
          (A * (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod) 0 i = 1 ∨
            (A * (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod) 0 i = -1
  -- Recognition 7429
theorem MorseCancel.functional_class_row_surjective {H : Type} [AddCommGroup H] [Module ℤ H]
    {r n : ℕ} (B : (Fin r → ℤ) ≃ₗ[ℤ] H) (v : Fin n → H)
    (hA : Function.Surjective (classCoordinateMatrix B v).mulVec) (L : H →ₗ[ℤ] ℤ)
    (hL : Function.Surjective L) :
    Function.Surjective (Matrix.of (fun (_ : Fin 1) (j : Fin n) => L (v j))).mulVec
  -- Recognition 7507
theorem MorseCancel.transported_classes_of_matrix_product {H K : Type} [AddCommGroup H]
    [Module ℤ H] [AddCommGroup K] [Module ℤ K] {r n : ℕ} (B : (Fin r → ℤ) ≃ₗ[ℤ] H)
    (e : H ≃ₗ[ℤ] K) (v : Fin n → H) (w : Fin n → K) (P : Matrix (Fin n) (Fin n) ℤ)
    (hmatrix : classCoordinateMatrix (B.trans e) w = classCoordinateMatrix B v * P)
    (j : Fin n) : e.symm (w j) = ∑ i, P i j • v i  -- Recognition 7530
theorem MorseCancel.functional_rows_of_matrix_product {H K : Type} [AddCommGroup H]
    [Module ℤ H] [AddCommGroup K] [Module ℤ K] {r n : ℕ} (B : (Fin r → ℤ) ≃ₗ[ℤ] H)
    (e : H ≃ₗ[ℤ] K) (v : Fin n → H) (w : Fin n → K) (P : Matrix (Fin n) (Fin n) ℤ)
    (hmatrix : classCoordinateMatrix (B.trans e) w = classCoordinateMatrix B v * P)
    (L : H →ₗ[ℤ] ℤ) :
    Matrix.of (fun (_ : Fin 1) (j : Fin n) => L (e.symm (w j))) =
      Matrix.of (fun (_ : Fin 1) (j : Fin n) => L (v j)) * P  -- Recognition 7544
```

Target: `Matrix.TransvectionReduction.*` — same statements under the Mathlib namespace shape
(`Matrix.mul_transvection_surjective`, `Matrix.primitive_row_has_unit_after_column_additions`
etc.). Pure move; axiom probe target: `primitive_row_has_unit_after_column_additions`.

**Row F0b (LANDED).** The scout coordinates 18429+/18540+ were stale — sources were
SphereTopology 14201+ pre-move; now in `Lib/Algebra/Module/IntegerPresentation.lean`: `Smale.IntegerPresentation` structure (14201) with fields `map`,
`columns`, `surjective`, `kernel_eq`, and API `ofEquiv` (14207), `transport` (14217),
`liftRelation` (14235), `map_liftRelation` (14239 — the ledger previously omitted it),
`adjoin` (14243), `matrix` (14312), `columns_sum_eq_mulVec` (14315), `mem_range_matrix_iff`
(14321), `matrix_image_eq_kernel` (14331), `matrix_relation` (14338),
`columns_span_of_subsingleton` (14345), `matrix_surjective_of_subsingleton` (14353).
**Closure dependency that must move with the packet** (or land in the same target file):
`Smale.HomologyTransport.ker_comp_span_singleton` (SphereTopology 14171, pure
`CommRing`-module algebra — used by `adjoin`). `HomologyTransport.exact_of_equivalences`
is already Lib-landed (`Lib/Geometry/Manifold/Morse/SublevelSets.lean:88`). The remaining
pure `HomologyTransport` decls (`exists_split_rank_one_extension` ST 13840,
`exists_add_split_rank_one_extension` ST 13881, `integerCoordinateSplit` ST 13967,
`integerEquiv_one_natAbs` Rec 7646, `matrix_sizes_eq_of_bijective` Rec 9182) are also
pure algebra; they are **candidates for the same file** — flag to owner whether they
belong in `IntegerPresentation.lean` or a separate `HomologyTransport` module.
Target: `Algebra.Module.IntegerPresentation.*`. Pure move **with a boundary
correction**: leave the two interleaved geometric gluers
`MorseSurgeryData.indexThreePresentation` (14258) and `SurgeryWindows.middlePresentation`
(14291) in place (they move with F10); the extraction takes 14171–14257 + 14312–14360.

**Row F7 (the headline generalization, G-F1).** Current (verbatim; scout's SH 28000 is stale —
source is now SingularHomology 22999):

```lean
theorem Smale.TubularBigon.exists_rankThree_relative_cancellation {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3)
    (d : Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3))
      (E := E) S k.map)
    (e : Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2))
      (E := E) T l.map)
    (hS : IsClosed S) (hT : IsClosed T)
    (hsign : tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) :
    ∃ K : Set M,
      IsCompact K ∧ K ⊆ tube.chart.target ∧
        Disjoint K ((S ∩ T) \ {a 0, a 1}) ∧
          ∃ A : ℝ × M → M,
            ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A ∧ (∀ y, A (0, y) = y) ∧
              (∀ t, ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∀ y, A (t, y) = D y) ∧
                (∀ t y, y ∉ K → A (t, y) = y) ∧
                  ((fun y => A (1, y)) '' S) ∩ T = (S ∩ T) \ {a 0, a 1}
```

Sheets via `TubularBigon … h 3` (normal rank 3; the structure's `n := 4` default at
SH 14432 is instantiated to 3) over
`Smale.RankThreeWhitneyModel.Space = (ℝ × ℝ) × (Lower × Upper)` with
`Lower = EuclideanSpace ℝ (Fin 1)`, `Upper = EuclideanSpace ℝ (Fin 2)` (SH 20594–20600).
Hypothesis `hsign` = opposite corner determinant signs; conclusion the compactly supported
isotopy removing the two corners. Target:
`Geometry.Manifold.Whitney.Trick.exists_relative_cancellation_of_opposite_signs`, parameterized
by `(p q : ℕ)` with model `WhitneyModel.Space p q := (ℝ × ℝ) × (EuclideanSpace ℝ (Fin (p - 1))
× EuclideanSpace ℝ (Fin (q - 1)))` (sheet dims $p, q$; level dim $p + q$), hypotheses
`2 ≤ p`, `2 ≤ q`, `5 ≤ p + q`, the framing/hypothesis bundle as today, and
`Tube.chart` with normal rank `p + q - 2` (the current `n := 4` default and `… h 3` uses
become computed values). **New mathematics**: the model and its cancellation are
dimension-free; the chart-existence chain (`RankThreeTangentAdaptedChart`,
`RankThreeSheetParametrizedChart`, `RankThreeCompatibleChart`) is re-run with symbolic normal
ranks — every determinant computation it contains is a block decomposition
(bigouin plane ⊕ normals) and goes through unchanged. The two structural points that actually
depend on the dimensions are (i) the filling step's general-position counts (§6 step 2), where
the hypothesis bundle gets the explicit form "sheets of dims $p, q$ in a level of dim $p + q
\geq 5$, with circle contractions in the complement", and (ii) the arc-avoidance counts, which
need $p, q \geq 2$.

**Row F1.** Current (full `Smale.ManifoldMorse.MorseSurgeryData.` prefixes — the short
`MorseSurgeryData.*` spellings in earlier drafts don't resolve at head):
`Smale.ManifoldMorse.MorseSurgeryData.beltIntersectionJacobian` (SH 11499),
`.beltIntersectionSign` (11509, returns `SignType.sign (d.beltIntersectionJacobian m j g x)`),
`.beltIntersectionPoints` (11516), `.beltIntersectionCount` (11532), plus
`.beltIntersectionJacobian_ne_zero` (11541), `.beltIntersectionSign_unit` (11570),
`.finite_beltIntersectionPoints` (11597); `SphereNormalCoordinates.*` supporting cluster
(SH 11385+); `collapse_homology_signed_count` (Recognition 8195, stale map ref 10020).
Target: `Geometry.Manifold.Whitney.IntersectionNumber.*` at general index: the
Jacobian/sign/count take the sphere dimension `m` already (they do: `(m : ℕ)`); the pin is
in the *consumers* (`… 2 …`). Move as-is; the generalization is only in how consumers
instantiate.

**Row F11 (handle slides, G-F2).** Current chain (scout coords 8259+ are stale — sources are
Recognition 6582+): `AdaptedWindows.exists_repeatable_column_slide` (6582) →
`exists_iterated_column_slide` (6645) → `exists_integer_column_slide` (6733) →
`MorseCancel.canonicalMiddleMatrix_single_class_addition` (6807, algebraic side) →
`exists_labelled_integer_slide` (6885) → `exists_arbitrary_column_addition` (7032) →
`exists_arbitrary_column_sequence` (7201). Headline signature (verbatim):

```lean
theorem AdaptedWindows.exists_arbitrary_column_sequence {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] [PathConnectedSpace M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder : ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → MorseCancel.nativeMorseIndex E f x ≤ MorseCancel.nativeMorseIndex E f y)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hcut : ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        MorseCancel.nativeMorseIndex E f z < 3 → f z < a)
    {r n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (hcomplete : ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        MorseCancel.nativeMorseIndex E f z = 3 → ∃ j, p j = z)
    (hlower : ∀ j, a < S.toSurgeryWindows.lower (p j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hγ : MorseCancel.IsNativeMiddleBasinFamily S hf ha p (fun j => γ j))
    (hsurj : Function.Surjective (MorseCancel.canonicalMiddleMatrix B γ).mulVec)
    (ops : List (Fin n × Fin n × ℤ)) (hvalid : ∀ op ∈ ops, op.1 ≠ op.2.1) :
    ∃ g : M → ℝ, ∃ hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g,
      Smale.ManifoldMorse.IsMorse E g ∧
        ∃ hcrit : Smale.ManifoldMorse.criticalPoints E g =
            Smale.ManifoldMorse.criticalPoints E f,
          (∀ x y : Smale.ManifoldMorse.criticalPoints E g,
              g x < g y →
                MorseCancel.nativeMorseIndex E g x ≤ MorseCancel.nativeMorseIndex E g y) ∧
            (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                MorseCancel.nativeMorseIndex E g z = MorseCancel.nativeMorseIndex E f z) ∧
              (∀ d, MorseCancel.nativeMorseCount E g d = MorseCancel.nativeMorseCount E f d) ∧
                (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                    (∀ j, z ≠ (p j).val) → g z = f z) ∧
                  (∀ z : Smale.ManifoldMorse.criticalPoints E g,
                      MorseCancel.nativeMorseIndex E g z < 3 → g z < a) ∧
                    ∃ hsub : ∀ y, g y ≤ a ↔ f y ≤ a,
                      ∃ hlevel : ∀ y, g y = a ↔ f y = a,
                        ∃ hga : ∀ y, g y = a → y ∉ Smale.ManifoldMorse.criticalPoints E g,
                          ∃ T : AdaptedWindows E g,
                            (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                                ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
                              (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) ∧
                                let p' : Fin n → Smale.ManifoldMorse.criticalPoints E g :=
                                  fun j => ⟨(p j).val, hcrit.symm ▸ (p j).property⟩
                                let B' := B.trans (MorseCancel.equalCutHomologyEquiv hsub)
                                (∀ j, MorseCancel.nativeMorseIndex E g (p' j) = 3) ∧
                                  (∀ z : Smale.ManifoldMorse.criticalPoints E g,
                                      MorseCancel.nativeMorseIndex E g z = 3 → ∃ j, p' j = z) ∧
                                    (∀ j, a < T.toSurgeryWindows.lower (p' j)) ∧
                                      ∃ Γ : Fin n →
                                            C((Smale.Hemisphere.Sphere 2), { y : M // g y = a }),
                                        MorseCancel.IsNativeMiddleBasinFamily T hg hga p'
                                            (fun j => Γ j) ∧
                                          (∀ j, (∀ op ∈ ops, op.2.1 ≠ j) →
                                              Γ j = MorseCancel.equalCutSection hlevel (γ j)) ∧
                                            MorseCancel.canonicalMiddleMatrix B' Γ =
                                              MorseCancel.canonicalMiddleMatrix B γ *
                                                (ops.map (fun op =>
                                                    Matrix.transvection op.1 op.2.1
                                                      op.2.2)).prod ∧
                                              Function.Surjective
                                                  (MorseCancel.canonicalMiddleMatrix B'
                                                      Γ).mulVec ∧
                                                ∀ z : M, f z ≤ a →
                                                  (∀ x, Filter.Tendsto (fun t => T.flow t x)
                                                        Filter.atBot (𝓝 z) ↔
                                                      Filter.Tendsto (fun t => S.flow t x)
                                                        Filter.atBot (𝓝 z)) ∧
                                                    (∀ x, Filter.Tendsto (fun t => S.flow t x)
                                                          Filter.atBot (𝓝 z) →
                                                        Set.range (fun t => T.flow t x) =
                                                          Set.range (fun t => S.flow t x)) ∧
                                                      ∀ v, Filter.Tendsto (fun t => T.flow t z)
                                                            Filter.atTop (𝓝 v) ↔
                                                          Filter.Tendsto (fun t => S.flow t z)
                                                            Filter.atTop (𝓝 v)
  -- Recognition 7201–7283 (signature ends at `:= by`); `exists_arbitrary_column_addition`
  -- (7032) is the single-op specialisation with the same binder prefix and `(k : ℤ)` for
  -- `transvection q i k`. The chain's first three links (6582/6645/6733) share this
  -- binder shape at a single point q / single index j.
```

All six links carry `(hdim : Module.finrank ℝ E = 6)`, index-3 upper handles,
`Hemisphere.Sphere 2` attaching spheres, degree-2 homology
(`SingularMayerVietoris.SingularHomology … 2`). Target: index-$k$ upper handles in an
$n$-dimensional ambient with `3 ≤ k ≤ n - 3`-style hypotheses replaced by the explicit
bundle the proofs use: the attaching spheres are `Hemisphere.Sphere (k - 1)`, homology in
degree `k - 1`, levels simply connected enough (`hnull`-family hypotheses as in the code),
and `hdim : Module.finrank ℝ E = n`. **New mathematics**: none beyond symbolic-index
bookkeeping — the proofs use the dimensions only through the E2 counts that the hypothesis
bundle packages. The 37 `finrank ℝ E = 6` sites in Recognition collapse to the parameter.

**Row F8/F12.** `exists_single_belt_intersection_of_unit_count` (SphereTopology 6598,
stale ref 9765), `MorseCancel.exists_single_intersection_of_unit_coordinate` (Recognition
8479, stale ref 10304), `AdaptedWindows.exists_primitive_functional_unit` (Recognition
7365, stale ref 9190): same generalization
pattern; the signed-cancellation algebra (`Smale.FiniteSignedCancellation.*`,
SphereTopology 6364–6400) is already fully general and is a pure move.

**Consumers.** `Hopf.SingularHomology` (the belt-cancellation chain), `Hopf.SphereTopology`
(the finite cancellation iteration, the homology-transport matrix lemmas),
`Hopf.Recognition` (the middle-matrix and pivot chain feeding lane G). All statements under
`Hopf/` unchanged; proofs re-route.

---

# Open items, seams, probes

1. **Seams (blocking).** Lanes A (homology, local degree), D1 (Morse data), D2 (tubular), E1
   (rearrangement, first cancellation), E2 (transversality, isotopy extension, arcs). Until
   they land the Lib files import `Hopf/*` as today and each import is recorded. Probe
   commands (after the seams land): `lake env lean
   Lib/Geometry/Manifold/Whitney/F_InterfaceCheck.lean` + consumer probe; receipt at
   `Lib/docs/F-INTERFACE_RECEIPT.md`.
2. **F0a/F0b LANDED** (`Lib/LinearAlgebra/Matrix/TransvectionReduction.lean` — 10 decls;
   `Lib/Algebra/Module/IntegerPresentation.lean` — `HomologyTransport.ker_comp_span_singleton`
   + `IntegerPresentation` + 14 API decls incl. the four Recognition-side `adjoin_*` lemmas).
   Verbatim moves under existing `MorseCancel.*`/`Smale.IntegerPresentation.*` FQNs — consumers
   (`Recognition`, `SphereTopology`) unchanged except added imports. Receipt:
   `Lib/docs/F-INTERFACE_RECEIPT.md`. The `Matrix.*`/root-namespace rename the Axis-5 targets
   describe is deferred to the lane's rename commit.
3. **Exact generality of the Whitney step.** The task's "sheets of dimensions $p + q = n$,
   $n \geq 5$, with $3 \leq k \leq n - 3$ or $\pi_1$-trivial levels" is matched by the
   code-shaped hypothesis bundle: sheets of dims $p, q \geq 2$ in a level of dimension
   $p + q \geq 5$, plus the explicit circle-contraction hypothesis (`hnull` in the code) that
   the codimension-2 case needs. The code's instance is $(p, q) = (2, 3)$ in a 5-level. The
   strongest classical statement (Milnor's 6.6 as printed) will be re-checked against the
   formalized hypothesis bundle at landing and the docstring will say exactly which form is
   proved. Flagged for the reviewer.
4. **Pragma cargo.** The moved blocks carry `attribute [local instance 100]
   Classical.propDecidable in` wrappers (≈70 sites) and `attribute [local irreducible]
   MorseCancel.canonicalMiddleMatrix in` (11 sites); the anonymous instances
   `EuclideanSphere.instLocal1/2/3` and `MorseSurgeryData.instLocal1` get real names in the
   rename commit.
5. **Bib keys.** Milnor's h-cobordism lectures and Smale 1961 are not in the pinned Mathlib
   bib; add `milnor65hcob`-style keys on upstreaming (open item, as in E2).
6. **Review.** Stage-2 independent review of §§1–10 committed in-tree as
   `Lib/docs/F-stage2-review.md` (verdict: statements true and correctly shaped;
   dependencies non-circular).
