# Lane C — Stage 2 review (textbook proof, §§1–16)

Reviewed: `~/s6-notes/review/C.md`, Axis 1 (§§1–16, everything before `# Axes 2–3`), read once
as mathematics. Overall: the architecture is sound and most of the flagged computations check
out — in particular the §3.3 chain-identity sign computation is *correct* (both groupings
verified below), the §8.1 tower induction is correct, the §15 bootstrap is *not* circular, and
the §9 decomposition uses no hidden degree theory once the repairs in Findings 2–4 are made.
One false input is cited (Finding 1, BLOCKER); its lemma's conclusion survives by a trivial
elementary argument. Six further local corrections and six remarks follow. No finding requires
changing any statement of any lemma, corollary, or the main theorem.

**Verified correct (no action needed):**
- §3.1–3.2 (Kuhn triangulation, face incidence): $\Delta_\sigma = \mathrm{conv}(v_0^\sigma,
  \dots, v_n^\sigma)$ via $t_{\sigma(j)} = s_j + \dots + s_n$, $s_j = t_{\sigma(j)} -
  t_{\sigma(j+1)}$; $\det(dA_\sigma) = \operatorname{sign}(\sigma)$; the $i$-th interior facet
  of $\Delta_\sigma$ equals $A_{\sigma\circ s_i}\circ\delta^i$ *with the same face index* $i$
  (dropping vertex $i$ from both vertex lists gives identical lists).
- §3.3 (chain identity). Interior faces cancel in pairs $(\sigma, \sigma\circ s_i)$ since
  $\operatorname{sign}(\sigma\circ s_i) = -\operatorname{sign}(\sigma)$ at the same index $i$.
  $i = 0$ faces: grouping by $j = \sigma(1)$, $\sigma = (j,\tau)$, the inversion count gives
  $\operatorname{sign}(\sigma) = (-1)^{j-1}\operatorname{sign}(\tau)$ (exactly the $j-1$
  elements smaller than $j$ precede it), and the face map is $A_\tau$ on $\{t_j = 1\}$ in the
  increasing-index coordinates; total sign $(-1)^{j-1}$. $i = n$ faces: grouping by
  $j = \sigma(n)$, $\sigma = (\tau,j)$, there are $n-j$ elements greater than $j$, so
  $\operatorname{sign}(\sigma) = (-1)^{n-j}\operatorname{sign}(\tau)$ and the total sign is
  $(-1)^{n-j}(-1)^n = (-1)^j = -(-1)^{j-1}$. Result:
  $\partial\kappa_n = \sum_j (-1)^{j-1}(\kappa^{(j,1)}_{n-1} - \kappa^{(j,0)}_{n-1})$. Correct
  at every $n$, signs included.
- §3.4 (fundamental class by induction; LES of the pair, the one sphere-homology computation
  flagged as lane A input — legitimate and sufficient).
- §5.1–5.2 (HEP, cell filling), §6.1–6.2 (prism, family form; note: a *stationary* prism term
  $\sigma\circ\mathrm{pr}\circ[v_0\dots v_i w_i\dots w_m]$ has the repeated vertex image
  $e_i, e_i$, hence factors through a codegeneracy — so stationary prisms are degenerate
  chains, which is what makes 6.2's "In particular" clause work, read with cancellation in
  the *unnormalized* chain group).
- §7.1 (reparametrization invariance; the relative-boundary pushforward argument),
  §7.2 (subdivision), §10 (cross product, Leibniz, $\kappa_{n+1} = \kappa_1 \times \kappa_n$
  with the insertion-sign bookkeeping matching 3.3's $(-1)^{j-1}$ factor), §10.4.
- §8.1 (tower): stage $k$ uses $\pi_k(X,x) = 0$ once per $k$-simplex, face-compatible gluing,
  HEP extension; stage count $\min(m, n-1) + 1$; conclusions correct for $m \le n-1$ and
  $m = n$.
- §11.1–11.3 (definition, well-definedness through the triangulated cylinder, homomorphism
  via 7.3, inverse via the degree-$-1$ reflection read of 7.1).
- §13.2 ($\bar\Psi \circ h_n = \mathrm{id}$): the equalities are in $\pi_n$; the chain identity
  in the form "$c(p)$ *is* the permutation sum" (10.3), the face-compatible piecewise
  straightening glued to a single homotopy rel $\partial I^n$ (8.1 at $K = K_n$), and the
  decomposition theorem (9.4) assemble correctly.
- §15 (Hopf degree corollary): the bootstrap is *not* circular — §§2–14 prove the main
  theorem uniformly at every degree before §15 is reached, so applying it at degree $k < n$
  to conclude $\pi_k(S^n) \cong H_k(S^n) = 0$ is legitimate; simple connectivity of $S^n$
  ($n \ge 2$) is van Kampen/suspension; the identification $h_n[f] = (\deg f)[S^n]$ is
  naturality along §16's quotient; the free/based step uses $\pi_1(S^n) = 0$. Allowed inputs
  only (homology of spheres, van Kampen). Correct.
- §16.1 (cube–sphere transport), §16.2 cylinder filling ($S^k$ fill at degree $k+1 \le d$).

---

## Findings

### 1. BLOCKER — §12.1 cites the false vanishing $\pi_{n-1}(S^{n-2}) = 0$; the lemma survives by a one-line constancy argument

§12.1, sentence: "…and any such map of pairs is homotopic rel boundary to constant — its
boundary map $S^{n-1} \to S^{n-2}$ is nullhomotopic since $\pi_{n-1}(S^{n-2}) = 0$ (cellular
approximation; lane A/B input)…". Two distinct errors. (a) The group vanishing is false:
cellular approximation gives $\pi_k(S^m) = 0$ for $k < m$, but here $k = n-1 > n-2 = m$; in
fact $\pi_{n-1}(S^{n-2}) = \pi_{m+1}(S^m)$ is $\mathbb{Z}$ for $m = 2$ (i.e. $\pi_3(S^2)$, the
Hopf class — the subject of this project) and $\mathbb{Z}/2$ for $m \ge 3$ by Freudenthal.
(b) Consequently the general claim "any map of pairs $(\Delta^n, \partial\Delta^n) \to
(\Delta^{n-1}, \partial\Delta^{n-1})$ is nullhomotopic rel boundary" is also false for
$n \ge 4$ (the cone on the Hopf map $\eta : S^3 \to S^2$ is a map of pairs $(D^4, S^3) \to
(D^3, S^2)$ whose boundary map $\eta$ is essential). Moreover the simplicial codegeneracy
$s^l : \Delta^n \to \Delta^{n-1}$ is not even a map of pairs: $s^l(\partial\Delta^n) =
\Delta^{n-1}$ (the facet opposite the merged vertex maps homeomorphically onto
$\Delta^{n-1}$), so it does not land in $\partial\Delta^{n-1}$.

The lemma's *conclusion* ("degenerate based simplices have zero class") is true and needs no
input at all: if $\tau = \rho \circ s^l : (\Delta^n, \partial\Delta^n) \to (X, x)$ is
degenerate and based, then $\rho(\Delta^{n-1}) = \rho(s^l(\partial\Delta^n)) =
\tau(\partial\Delta^n) = \{x\}$ (surjectivity of $s^l|_{\partial\Delta^n}$ onto
$\Delta^{n-1}$, valid for all $n \ge 1$), so $\rho$ — hence $\tau$ — is the constant map, and
$\langle\tau\rangle = 0$.

**Exact fix:** replace the two sentences "…a degenerate based $n$-simplex factors through a
face collapse $(\Delta^n, \partial\Delta^n) \to (\Delta^{n-1}, \partial\Delta^{n-1})$, and any
such map of pairs is homotopic rel boundary to constant — its boundary map $S^{n-1} \to
S^{n-2}$ is nullhomotopic since $\pi_{n-1}(S^{n-2}) = 0$ (cellular approximation; lane A/B
input), after which the disc map is a $\pi_n(\Delta^{n-1}) = 0$ element (contractible
target)." by: "a degenerate based $n$-simplex $\tau = \rho \circ s^l$ is constant: the
codegeneracy $s^l$ maps $\partial\Delta^n$ onto $\Delta^{n-1}$ (the facet whose vertices are
not merged by $s^l$ maps homeomorphically onto $\Delta^{n-1}$), so
$\rho(\Delta^{n-1}) = \tau(\partial\Delta^n) = \{x\}$, and $\tau \equiv x$." Delete the
"lane A/B input" attribution (no input is needed).

### 2. CORRECTION — §9.2: the "cut warp" cannot be boundary-fixing; the Alexander trick as invoked does not apply

§9.2, sentence: "…there is a boundary-fixing homeomorphism $w$ of $I^n$ (the *cut warp*, an
explicit piecewise-affine straightening of the diagonal cut to the coordinate cut
$\{t_1 = \tfrac12\}$, …) such that $c$ is the standard concatenation pinch composed with $w$,
and $w \simeq \mathrm{id}$ rel boundary by the Alexander trick." No such boundary-fixing $w$
exists: the diagonal cut $H_{ij}$ and the coordinate cut $\{t_1 = \tfrac12\}$ meet
$\partial I^n$ in different sets (for $n = 2$: the two opposite corners vs. the two midpoints
of the top/bottom edges), and a homeomorphism fixing $\partial I^n$ pointwise cannot move one
cut to the other. So the Alexander trick (which requires a boundary-fixing homeomorphism)
cannot be applied to $w$ as stated.

**Exact fix:** take $w$ to be a *boundary-preserving* homeomorphism of $I^n$ mapping
$\{t_1 = \tfrac12\}$ to $H_{ij}$ (it exists: both cuts split the cube into two balls; match
the boundaries of the cuts by an orientation-preserving homeomorphism of
$\partial I^n \cong S^{n-1}$, extend over the cut ball, then cone over the two sides), of
degree $+1$ after the orientation choices of the two sides. Then $w$ is isotopic to the
identity *through boundary-preserving homeomorphisms*: its boundary restriction is an
orientation-preserving homeomorphism of $S^{n-1}$, isotopic to the identity by coning and the
Alexander trick rel boundary on the cone; extend that isotopy over a collar, reducing to a
boundary-fixing homeomorphism, and apply 9.1. Precomposition with such a $w$ preserves based
classes because the isotopy keeps $\partial I^n$ in $\partial I^n$, so all intermediate maps
remain based. This is elementary (homeomorphisms only — no "degree-one maps are homotopic to
the identity", which would be circular). Also fix the phrase "$[c] = \iota_1 + \iota_2$ in the
wedge of two cubes": the wedge of two cubes is contractible; either say "in the wedge of the
two quotient spheres $I^n/\partial I^n \vee I^n/\partial I^n$" or, better for this
homology-free section, phrase the conclusion directly as the based homotopy
$(p_{\le} \vee p_{\ge}) \circ c \simeq p_{\le} \cdot p_{\ge}$ rel boundary, which the repaired
comparison gives.

### 3. CORRECTION — §9.4 (with 9.2): the induction pinches a descent-facet *union* between two non-cube balls, which the stated single-cut lemma does not cover

§9.4, sentence: "At step $m+1$, pinch the descent-facet ball $\Delta_{\sigma_{m+1}} \cap B_m$
(on which $p$ is constant $x$): by 9.2 the class splits as $[p|_{B_m}] +
[p|_{\Delta_{\sigma_{m+1}}}]$…". But 9.2 as stated pinches a *single braid hyperplane
section* of the *cube*. The locus pinched at step $m+1$ is the union of the descent facets of
$\sigma_{m+1}$ — for a permutation with several descents (e.g. the longest element $w_0$,
which has $n-1$ descents) this is a union of several facets meeting in codimension 2 — and
the two sides are the balls $B_m$ and $\Delta_{\sigma_{m+1}}$, not the two halves of a cube
cut by one hyperplane. Iterating single hyperplane cuts does not reach this situation either
(after the first pinch the geometry is no longer a cube). Also, §9.4′'s parenthetical "the
single-cut lemma is not even needed: the facets share the basepoint locus directly" is
inaccurate — decomposing the sphere's class as the sum of its facet classes uses the same
pinch mechanism (the pinches are *available* because the map is constant on the shared
locus).

**Exact fix:** restate 9.2 in its natural generality: "*Let $I^n = A \cup B$ with $A, B$
$n$-balls and $A \cap B$ an $(n-1)$-ball contained in $\partial A \cap \partial B$, and let
$p : (I^n, \partial I^n) \to (X, x)$ be constant equal to $x$ on $A \cap B$. Then
$[p] = [p_A] + [p_B]$, the two terms transported to the cube by fixed homeomorphisms.*" The
proof is the same as 9.2's with the repaired cut warp of Finding 2 (the cut ball $A \cap B$
plays the role of $H_{ij}$). The braid-hyperplane case used at the first peel and the
single-cut picture are then special cases, and every step of the 9.3 shelling, as well as
9.4′'s sphere decomposition (including the last facet, whose cut is the equatorial
$S^{n-1} \subset \partial\Delta^{n+1}$), is covered.

### 4. CORRECTION — §9.3: the cone criterion in the parenthetical is backwards

§9.3, sentence: "A nonempty proper union of facets of a simplex is a ball (it is a cone from
any vertex lying in all omitted facets)". The claim is correct but the criterion is reversed:
a vertex lying in all *omitted* facets need not lie in the union at all (e.g. $n = 2$, union
= the single edge $\delta^0$: the vertex $e_0$ lies in both omitted facets $\delta^1,
\delta^2$ but is not in the union, so the union is certainly not a cone from it).

**Exact fix:** replace the parenthetical by: "(it is a cone from any vertex $e_k$ lying in
all facets of the union — equivalently, any vertex whose opposite facet $\delta^k$ is
omitted; such a vertex exists because the union is proper — over a smaller such union or a
sphere, hence a ball by induction on $n$)".

### 5. CORRECTION — §7.3: $H_n(I^n \vee I^n, \mathrm{pt}) \cong \mathbb{Z} \oplus \mathbb{Z}$ is false; the wedge of two cubes is contractible

§7.3, sentence: "In $H_n(I^n \vee I^n, \mathrm{pt}) \cong \mathbb{Z} \oplus \mathbb{Z}$
(Mayer–Vietoris for the wedge of two cubes along a point; lane A), …". The wedge of two
cubes at a point is contractible, so the displayed group is $0$ for $n \ge 1$ and the
equation $\mathrm{pinch}_*[I^n] = \iota_{1*}[I^n] + \iota_{2*}[I^n]$ is vacuous as written.

**Exact fix:** use the pair $(I^n \vee I^n, \partial I^n \vee \partial I^n)$ throughout:
excision gives $H_n(I^n \vee I^n, \partial I^n \vee \partial I^n) \cong H_n(I^n, \partial
I^n) \oplus H_n(I^n, \partial I^n) \cong \mathbb{Z} \oplus \mathbb{Z}$, the pinch and the
$\iota_k$ are maps of pairs into it, the local-degree justification (generic points of the
two summands) applies verbatim, and $p \vee q$ sends $\partial I^n \vee \partial I^n$ to $x$,
so the final pushforward lands in $H_n(X, x) \cong H_n(X)$ (the reduced/unreduced
identification cited in §2). Equivalently, work with the wedge of the two quotient spheres
$S^n \vee S^n$ via §16.1. The rest of 7.3 (the affine degree-one reparametrizations of the
halves, by 7.1) is correct as written.

### 6. CORRECTION — §8.2 (used in §§13.1 and 14): class-preservation $[z'] = [z]$ is unproved for normalized cycles with non-constant degenerate boundary faces

§8.2, hypothesis: "…whose boundary faces that remain in $\partial z$ are already constant at
$x$ (e.g. $z$ a cycle, …)", and its use in §13.1 ("Let $z = \sum_j a_j \tau_j$ be a
normalized $n$-cycle; straighten it … the straightening preserves the homology class by the
family prism 6.2") and §14 (same at degree $k$). For a cycle $z$ in the *normalized* complex,
$\partial z$ computed in $C_*(X)$ is a general degenerate chain: its non-cancelling face
types are degenerate but not necessarily constant at $x$. Such faces are not in $L$, so the
tower gives them non-stationary homotopies, and the prism over a degenerate simplex with a
non-stationary homotopy is **not** a degenerate chain in general (degeneracy of prism terms
requires the homotopy to factor through the codegeneracy — as it does for stationary
homotopies, where each prism simplex acquires the repeated vertex $e_i, e_i$). Hence 6.2's
"In particular" clause, whose hypothesis is stationarity-or-literal-cancellation on *every*
face, does not apply, and the identity $\partial\sum a_j P_{H_j} = z' - z$ in $C^N_*(X)$ is
not justified. (For a normalized *based* degenerate simplex there is no problem — it is
constant by Finding 1 — but the faces of an arbitrary normalized cycle are not based.)

**Exact fix (two options; the first is one sentence using an input already cited in §2):**
(a) In §13.1 and §14, first replace the normalized cycle $z$ by a homologous *genuine* cycle:
$\partial z \in Z_{n-1}(D_*(X))$ is a boundary in $D_*$ since $H_*(D_*) = 0$ (§2), say
$\partial z = \partial w$ with $w \in D_n$; then $z - w$ is a genuine cycle representing the
same class. For a genuine cycle every boundary face type occurs with net coefficient zero in
$C_{n-1}(X)$, its occurrences pair off with opposite signs, the face-compatible recipe gives
all occurrences of a type the same homotopy, and the prism terms cancel in pairs in $C_*$ —
no stationarity hypothesis is needed at all. State 8.2's class-preservation for chains whose
unnormalized boundary faces cancel pairwise or are constant at $x$ (with the constant ones
stationary). (b) Alternatively, build $K$ in 8.2 as the quotient of the displayed complex by
collapsing each degenerate face type onto its base simplex; the tower on the quotient
produces homotopies that factor through the codegeneracies, whence every prism term over a
degenerate face has a repeated vertex image and is degenerate. Option (a) is cheaper.

### 7. CORRECTION — §12.2: "two normalizations differ by a homotopy of based maps" is false for a single simplex; replace by functionality in the chain

§12.2, sentence: "This is well-defined: two normalizations differ by a homotopy of based maps
(built by the same tower applied one dimension up, to the square interpolating between the
two normalizations), and based homotopic simplices have the same class." For a single
$n$-simplex this is not true in general: the tower's last-stage nullhomotopies of the
$(n-1)$-faces are ambiguous by elements of $\pi_n(X)$ (two nullhomotopies rel boundary of a
based map $\Delta^{n-1} \to X$ differ by a $\pi_n$ element, which need not vanish — it is the
group the theorem is computing), and no "tower one dimension up" can kill that ambiguity.
Two normalizations of one simplex can therefore be non-homotopic rel boundary.

**Exact fix:** the only well-definedness ever used is: with the face-type recipe fixed (8.2),
$\Psi$ is a well-defined *function of the chain* (equal chains have the same face types,
hence the same chosen homotopies), it is linear, and it kills boundaries (12.3). Replace the
sentence by: "This is a well-defined function of the chain once the tower homotopies are
fixed per face type as in 8.2; it then descends to homology by 12.3." Note that
choice-independence of the induced $\bar\Psi$ is never needed: the round-trips of §13 use one
fixed recipe throughout, and §13.2's third equality uses only that the piecewise and glued
straightenings come from the *same* face-compatible recipe. (Per-simplex
choice-independence *does* hold in chains whose boundary face types cancel, because the
$\pi_n$ ambiguities then cancel in pairs — which is another way to see why all applications
are safe.)

### 8. REMARK — §12.2, last sentence: "By 12.1 the operator factors through normalized chains" needs one more step

12.1 gives zero class for degenerate *based* simplices, but $\Psi$ evaluates a degenerate
simplex $\tau$ via its *straightening* $\tau'$, which is based but a priori arbitrary. The
missing step: $\tau' \simeq \tau$ and $\tau$ factors through the contractible $\Delta^{n-1}$,
so $\tau'$ is freely nullhomotopic; since $\pi_1(X, x) = 0$ the $\pi_1$-action on $\pi_n$ is
trivial, so a freely nullhomotopic based map is null in $\pi_n(X, x)$, i.e.
$\langle\tau'\rangle = 0$. Add this sentence. (The factorization is in any case only a
convenience: $\bar\Psi$ is constructed on $H_n$ directly from $\Psi$ on unnormalized cycles
plus 12.3.)

### 9. REMARK — §8.1: the case $m > n$ is used (§12.3) but not stated

§12.3 applies the tower to $\omega : \Delta^{n+1} \to X$ ("dimension $n+1$: normalize the
$n$-skeleton"), while 8.1's statement lists only $m \le n-1$ and $m = n$. The proof's stage
range $k \le \min(m, n) - 1$ already covers $m > n$ with the conclusion "$f'$ constant on
$\mathrm{sk}_{n-1}K$". Add this case to the statement (uniformly: for any $m$, $f$ is
homotopic rel $L$ to $f'$ constant on $\mathrm{sk}_{\min(m,n)-1}K$, and constant outright if
$m \le n-1$).

### 10. REMARK — §8.2: the complex $K$ is a $\Delta$-complex, not necessarily a simplicial complex

"Identifying faces that are equal as singular simplices of $X$" of a disjoint union of
simplices produces a $\Delta$-complex (semi-simplicial complex) in general, while 8.1 is
stated for simplicial complexes. The tower proof is verbatim for $\Delta$-complexes (HEP for
subcomplexes, skeletal induction, finiteness are unaffected); either say so in 8.1 or pass to
a subdivision.

### 11. REMARK — §9.1: the rotation isotopies are not "rel boundary"

§9.1 twice says the rotation of the $(t_1, t_i)$-plane is "an isotopy of the disc model of
the cube rel boundary" (and the permutation-action proof uses the same picture). A rotation
of the disc moves its boundary. The argument is nonetheless correct: the rotations are
boundary-*preserving* isotopies, so precomposition carries based maps to based maps and gives
a based homotopy rel boundary after composition with $p$. Rephrase to "an isotopy of the
disc model preserving the boundary as a set; precomposition with it therefore preserves
classes in $\pi_n(X, x)$". This is also the point used in the repair of Finding 2.

### 12. REMARK — §4.1: the displayed radial construction does not establish the stated face-compatibility

The lemma claims $\varphi_m$ takes "faces to (unions of) faces", but the ray-rescaling
(Minkowski functional) construction given in the proof maps a simplex facet to a region of
$\partial I^m$ cut out by a cone of directions, which is generally not a union of cube faces
(e.g. $m = 2$: the image of an edge is an arc whose endpoints are not corners of the square).
The property does hold for the flattening construction mentioned in the parenthetical
(flatten to $\{v \in \mathbb{R}^m_{\ge 0} : \sum v_i \le 1\}$, then $v \mapsto
v\,\|v\|_1/\|v\|_\infty$, which sends the facet $\{\sum v_i = 1\}$ to
$\bigcup_i \{w_i = 1\}$). Since no downstream argument uses face-compatibility of
$\varphi_m$ (§§4.2, 12.1, 13.1 use only the homeomorphism of pairs and the degree
normalization), either present the flattening construction as the proof or delete the
naturality clause.

### 13. REMARK — §16.2: "sphere filling … directly from the tower 8.1" misattributes the argument

The tower 8.1 applies to a map defined on all of $K$; the sphere-filling data is only a map
$S^{k-1} \to X$. The filling is exactly 5.2 ($\pi_{k-1}(X, x) = 0$ for $k \le d$); cite 5.2
here (or note the tower is applied after a preliminary constant coning, which is unnecessary).
The cylinder-filling item that follows is correct as written (it reduces to sphere filling at
degree $k+1$).

### 14. REMARK — minor wording

§8's standing-hypotheses paragraph: "the hypothesis $n \geq 2$ enters only in §11, where
$\pi_n$ must be a group homomorphism land" is garbled (presumably "where $h_n$ must land in
the abelian group $H_n$ / be a homomorphism"). §8.2's "identifying faces … with the same
sign" should be read as "identified as oriented simplices (not up to orientation reversal)";
as written it is ambiguous, and the reading matters because all occurrences of a face type —
of either sign — must share one homotopy for the prism cancellation of 6.2.

---

## Verdict

Not correct as written: Finding 1 cites a false theorem (a non-existent group vanishing), and
Findings 2–6 are genuine gaps in proofs (each with the conclusion intact and a local,
elementary fix supplied above). Findings 7–14 are smaller corrections and remarks. With the
fixes applied — all of which stay inside the permitted toolkit (no Hopf degree theorem, no
$\pi_n(S^n) \cong \mathbb{Z}$ anywhere in §§2–16; §9 remains homology-free) — the proof of
Hatcher 4.32 in every degree is complete and correct, and the two advertised generalizations
G1 (chain identity, §§3/10.3) and G2 (straightening tower, §8) are proved once and for all by
induction.
