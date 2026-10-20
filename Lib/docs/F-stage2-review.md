# Lane F — Stage-2 independent review (§§1–10)

Reviewed: `/home/kimi/s6-notes/review/F.md` (stable copy), Axis 1 only, once, as mathematics.

## Verdict

The four headline statements (F1)–(F4) are true and correctly shaped for their consumers, and
the dependencies are non-circular (only lane-A local degree, D2 tubular neighbourhoods, and E2
transversality/isotopy extension are used). The assigned checkpoints that verify exactly as
written: §3's sign definition and isotopy invariance; §3's handle-application dimensions (belt
sphere $S^{m-k}$ of an index-$k$ handle in the $m$-dimensional level of an $(m+1)$-dimensional
ambient — correct); §4's dimension count $m = 2 + (p-1) + (q-1)$, sheet dimensions $p$ and $q$,
exactly two corners, and opposite corner signs (recomputed in Finding 4); §5's arc existence
from $p, q \geq 2$ and the normal-frame rank count $(p-1) + (q-1) = m-2$; §6's general-position
counts $2 + p < m$ / $2 + q < m$ and the codimension-2 residual isolated points; §7's
termination (a finite set shrinking by two at each step) and the single-intersection corollary;
§9(a), §9(c), and the logic of §9(d). However, the document is not correct as written: nine
corrections and five remarks follow. The most serious is Finding 1: the proof of the
local-degree identity in §3 invokes Hatcher Prop. 2.30 for a map between manifolds of different
dimensions, and two of its three sentences are false as written (the identity itself is true).

## Findings

### 1. CORRECTION — §3, proof of the local-degree theorem: Hatcher 2.30 does not apply to the Thom collapse as written

Sentence (§3, lines 97–100): "By transversality and the crossing charts of E2 §12,
$\tau \circ \iota_A$ near each intersection point is a local homeomorphism of oriented
$p$-balls with local degree $\varepsilon(x)$; the degree equals the sum of the local degrees at
the preimages of a regular value (Hatcher Prop. 2.30; lane A's local-degree machine)."

$\nu B$ has rank $p$, so $\mathrm{Th}(\nu B)$ is a $(p+q)$-dimensional space (a manifold away
from the basepoint), while $A$ is $p$-dimensional. Hence, for $q \geq 1$: (i) $\tau \circ
\iota_A$ near an intersection point is a local *embedding* of a $p$-ball, not a local
homeomorphism — source and target dimensions differ; (ii) the preimages of a generic value are
*empty* ($p - (p+q) = -q < 0$), so "the degree equals the sum of the local degrees at the
preimages of a regular value" cannot be invoked: Hatcher Prop. 2.30 is stated for maps between
closed oriented manifolds of the *same* dimension. The identity
$\langle A, B \rangle = \deg(\tau \circ \iota_A)$ itself is true and standard; only its
justification is broken. Fix (either):

(a) argue homologically: the generator of $H_p(\mathrm{Th}(\nu B))$ is the oriented fibre
sphere; $\deg(\tau \circ \iota_A) = \langle \tau^* u, [A] \rangle$ for the Thom class $u$;
$\tau^* u$ is Poincaré dual to $[B]$; the evaluation localizes by excision at the finite set
$A \cap B$; and in the crossing charts the fibre projection of $A$ at $x$ is an oriented linear
isomorphism of determinant sign $\varepsilon(x)$, so the evaluation is
$\sum_x \varepsilon(x)$; or

(b) restate with the equidimensional collapse actually used by the code: the cell-filtration
collapse $N \to \bigvee_i S^k$ (one sphere per index-$k$ handle); the attaching sphere then
maps between $k$-manifolds and Hatcher 2.30 applies verbatim, the degree on the $i$-th summand
being $\langle \mathrm{belt}_i, \mathrm{attaching} \rangle$ — this is exactly the setup of
`collapse_homology_signed_count`.

The same repair is needed for the parenthetical in (F1), §1 lines 29–30 ("the degree of a map
equals the sum of its local degrees at the preimages of a regular value"), which presupposes
the equidimensional reading.

### 2. CORRECTION — §3: the Thom generator needs $B$ connected, and the orientation convention for $\nu B$ must be declared

Sentence (§3, line 96): "the generator of $H_p(\mathrm{Th}(\nu B)) \cong \mathbb{Z}$ given by
the orientation of $\nu B$". Two gaps. (i) The Thom isomorphism gives
$H_p(\mathrm{Th}(\nu B)) \cong H_0(B)$; this is $\mathbb{Z}$ only for $B$ connected. (F1) as
stated allows disconnected $B$; add "$B$ connected" (automatic in the handle application, where
$B$ is a sphere). (ii) The orientation of $\nu B$ must be fixed from the given orientations of
$B$ and $N$ by a splitting convention, and the identity is sensitive to the choice: with the
normal-first convention $o(TN) = o(\nu B) \wedge o(TB)$, the local degree of the fibre
projection at $x$ equals $\varepsilon(x)$ exactly (writing $o(TA) = \lambda\, o(\nu B)$ via the
transversality isomorphism, $o(TA) \wedge o(TB) = \lambda\, o(\nu B) \wedge o(TB) =
\lambda\, o(TN)$); with the tangent-first convention it equals $(-1)^{pq}\varepsilon(x)$, i.e.
the identity would be off by the global sign $(-1)^{pq}$. Fix: state in §2 that $\nu B$ is
oriented by $o(\nu B) \wedge o(TB) = o(TN)|_B$.

### 3. CORRECTION — §2: the sign-convention parenthetical is dimensionally inconsistent as written

Sentence (§2, lines 71–73): "the sign conventions are fixed once (the belt sphere's normal
frame, then the attaching sphere's frame, against the level's orientation)". Read literally,
the belt sphere's normal frame has rank $p$ and the attaching sphere's (tangent) frame has rank
$p$, together $2p$ vectors against a $(p+q)$-dimensional orientation — a frame only when
$p = q$. The two consistent readings are "(normal frame of the belt, then frame of the belt)"
or "(normal frame of the belt, then normal frame of the attaching)"; the latter matches the
code's sphere-normal Jacobian and, via the transversality identifications $\nu B \cong T_xA$
and $\nu A \cong T_xB$ at an intersection point, reproduces §3's order $o(TA) \wedge o(TB)$.
Fix: write the convention as an explicit ordered decomposition, e.g. "at an intersection point,
$T_xN$ is oriented against (a normal frame of $B$, then a frame of $B$), equivalently against
(a frame of $A$, then a frame of $B$), the two compared by the transversality isomorphism",
kept consistent with the convention chosen in Finding 2.

### 4. CORRECTION — §4: the displayed corner-sign formula cannot be the corner determinant

Sentence (§4, lines 119–120): "The corner determinant sign of the model frames is
$\operatorname{sign}(8h(2t - 1))$-style". At the corners $t = 0$, so $8h(2t-1) = -8h < 0$ at
*both* corners: the expression does not change sign and so cannot be the corner determinant.
The direct computation that follows in the text is the correct one: with sheet frames
$\partial_s$ (the line) and $\partial_s - 2hs\,\partial_t$ (the parabola), the planar
determinant is $-2hs$, i.e. $+2h$ at $s = -1$ and $-2h$ at $s = +1$ (or its global negative,
with the opposite sheet order): opposite signs, as claimed. Fix: replace the formula by "the
corner determinant is $-2hs$ at the corner $(s, 0)$: $+2h$ at $s = -1$, $-2h$ at $s = +1$".
(The model's dimension count $m = 2 + (p-1) + (q-1) = p+q$, the sheet dimensions, and "meet
exactly at the two corners" all verify; this finding concerns only the displayed formula.)

### 5. CORRECTION — §6 step 4: the graph-motion inequality must hold on the closed interval $[-1, 1]$

Sentence (§6, lines 183–184): "choose a smooth height function
$\varphi \colon \mathbb{R} \to [0, \infty)$, compactly supported, with
$\varphi(s) > h(1 - s^2)$ on $(-1, 1)$". As stated, $\varphi$ may vanish at the endpoints:
there exist smooth compactly supported $\varphi \geq 0$ with $\varphi(s) > h(1-s^2)$ for all
$s \in (-1, 1)$ but $\varphi(\pm 1) = 0$ (e.g. $\varphi$ of slope $\mp 4h$ at $s = \pm 1$,
vanishing there, interpolated above the parabola in between: near $s = 1$,
$4h(1-s) > h(1-s)(1+s) = h(1-s^2)$). Then the pushed line still contains the corners
$(\pm 1, 0) \in L_1$, and "the pushed line is disjoint from the parabola" (line 186) fails —
the two intersections are not removed. Fix: require $\varphi(s) > h(1 - s^2)$ on the *closed*
interval $[-1, 1]$ (equivalently, add $\varphi(\pm 1) > 0$); such $\varphi$ exist with compact
support slightly larger than $[-1, 1]$.

### 6. CORRECTION — §6 step 2: unfilled placeholder "$p = q = \ldots$"

Sentence (§6, line 161): "this is exactly the case $p = q = \ldots$ of the code: sheets $2$ and
$3$ in a $5$-manifold". "$p = q = \ldots$" is a template placeholder, and as written it also
asserts $p = q$, contradicting the values given in the same sentence. Fix: "this is exactly the
case $(p, q) = (2, 3)$ of the code". (The count that follows — "$2 + 3 = 5$ is not $< 5$", the
disc against the $3$-dimensional, codimension-2 sheet — is correct.)

### 7. CORRECTION — §6 step 2: the piping guide arc lies in the disc, not in the sheet; the opposite-sign pairing is unjustified and unneeded

Sentence (§6, lines 163–166): "the residual intersections of the disc interior with the
codimension-2 sheet come in opposite-sign pairs and are piped off: push each such point along
an arc in the sheet to the boundary arc (which lies in the sheet) and absorb it into the
boundary germ". (i) A transverse intersection of the disc with the sheet is stable under small
motions of the sheet; what removes it is an isotopy of the sheet making the intersection travel
*within the disc* to the disc's boundary. The standard piping construction (Milnor, Lemma 6.7)
chooses a simple arc **in the disc** from the interior point to the boundary arc $\beta$ (which
lies in the same sheet), avoiding the other residual points, and isotopes the sheet in a
neighbourhood of that arc. As written, "an arc in the sheet ... this uses the sheet's dimension
$\geq 2$ for the arc to exist" describes the wrong guide and the wrong dimension count (the
avoidance count for an arc in the 2-dimensional disc is automatic). Fix: "push each such point
along an arc in the *disc* to the boundary arc $\beta$ (which lies in the sheet)". (ii) "come
in opposite-sign pairs" is asserted without argument and is never used: piping removes each
point individually. If the pairing is wanted, justify it: push $\beta$ off itself into a collar
of the disc; the pushed boundary loop meets the codimension-2 sheet only at $x_0, x_1$, which
have opposite signs, so the signed total of the interior intersections is zero. Otherwise
delete "come in opposite-sign pairs and".

### 8. CORRECTION — §8: the slide = transvection formula has the matrix-unit indices flipped

Sentence (§8, lines 222–225): "Sliding handle $j$ over handle $i$ with multiplicity $c$ ...
right-multiplies $M$ by the transvection $I + c\,E_{ji}$". With $E_{ji}$ the matrix unit ($1$
in row $j$, column $i$), right-multiplication $M \mapsto M(I + cE_{ji})$ adds $c$ times column
$j$ to column $i$; e.g. in the $2 \times 2$ case, $M(I + cE_{21})$ replaces column 1 by
column 1 $+\,c\cdot$ column 2. So the displayed formula is the matrix of sliding handle $i$
over handle $j$ — which is exactly (F3)'s consistent statement (§1, lines 48–50: "Sliding the
$i$-th handle over the $j$-th handle ... right-multiplies $M$ by the transvection
$I + c\,E_{ji}$"). §8 also contradicts itself: its geometric elaboration (line 231) says the
slide "adds $c$ times the $i$-th column to the $j$-th column of $M$", which is
right-multiplication by $I + cE_{ij}$. Fix: in §8 write "Sliding handle $j$ over handle $i$
... right-multiplies $M$ by $I + c\,E_{ij}$", or swap the roles of $i$ and $j$ to match (F3)
verbatim.

### 9. CORRECTION — §9(b): the Euclidean termination measure is not strictly decreasing as stated

Sentences (§9, lines 244–248): "...strictly reduces $\max(|v_i|, |v_j|)$ when
$|v_j| \geq |v_i|$ ... Termination is the well-founded descent on the maximum absolute value".
The strict-reduction claim fails when $|v_i| = |v_j|$: e.g. $v_i = v_j = 5$ gives $q = 1$ and
$(5, 5) \mapsto (5, 0)$, so the maximum is unchanged (a zero entry is created, but "descent on
the maximum absolute value" alone does not terminate a step that leaves the maximum fixed).
The remainder estimate itself is fine: $q = \lfloor v_j / v_i \rfloor$ gives $|v_j'| < |v_i|$
or $v_j' = 0$, for either sign of $v_i$. Fix: measure the row by $\sum_k |v_k|$, which strictly
decreases at every step (since $|v_j'| < |v_i| \leq |v_j|$ or $v_j' = 0$), or by the
lexicographic pair (maximum absolute value, number of entries attaining it). The rest of (b) —
pair reduction to $(\gcd, 0)$, row reduction to $(\pm 1, 0, \dots, 0)$ up to order using
$\gcd = 1$, and all operations being transvections — is correct.

### 10. CORRECTION — §10: "$k = 3$" uses the code's upper-index convention, conflicting with §8

Sentence (§10, lines 273–274): "recovered by instantiating $p = 2$, $q = 3$ (sheets in the
5-level), $m = 5$ / ambient $n = 6$, $k = 3$." In §8 (line 216) and in §3's handle application,
the rows of $M$ are indexed by the index-$k$ handles (below) and the columns by the
index-$(k+1)$ handles (above); for the pinned system — index 2 below, index 3 above (the
"index 2/3" of the same sentence), attaching `Hemisphere.Sphere 2` $= S^2 = S^k$ (so $k = 2$),
belt $S^{m-k} = S^3$ — §8's parameter is $k = 2$. The value $k = 3$ is correct only in the
code/row-F11 convention where $k$ denotes the *upper* handle index (attaching
`Hemisphere.Sphere (k-1)`). Fix: write $k = 2$ in §10, or state explicitly that the handle-side
parameter is the upper index as in row F11.

### 11. REMARK — §6 step 2: the double-point clause is vacuous for $m \geq 5$

Sentence (§6, lines 157–159): "The disc map is made immersion-generic rel boundary, then
embedded: its double points are interior arcs/points removable by the Whitney finger
construction's inverse". For a map of a 2-disc into an $m$-manifold with $m \geq 5$, the
generic double-point set has dimension $4 - m \leq -1$: it is empty. Double-point arcs/points
are $m = 3, 4$ phenomena. Under (F2)'s standing hypothesis $m = p + q \geq 5$, general position
already embeds the disc rel boundary; the only residual problem is intersections with the
sheets, which the displayed counts handle correctly. Suggest deleting the clause.

### 12. REMARK — §8: the belt-first order in $M_{ij}$ differs from §3's attaching-first order by a global sign

§3 defines the sign for the ordered pair $(A, B) = (\text{attaching}, \text{belt})$ via
$o(TA) \wedge o(TB)$ against $o(TN)$; §8 (line 216) sets
$M_{ij} = \langle \text{belt}_i, \text{attaching}_j \rangle$ (belt first), which differs by the
entry-independent sign $(-1)^{k(m-k)}$. This is harmless for surjectivity, unit entries, and
the pivot chain, but §2 promises the conventions are "fixed once"; state the comparison once
(or adopt one order everywhere).

### 13. REMARK — §8: level connectedness and "every elementary column operation"

(i) The slide arc exists "since the level is connected" (line 227): regular levels are not
connected in general; this is a standing hypothesis of the handle-calculus setting (no
index-$0$/$n$ handles) and should be named. (ii) "Every finite sequence of elementary column
operations is realized by a sequence of slides" (lines 225–226): column sign-changes are
reorientations of the attaching sphere/core rather than slides. Since §9's reduction uses only
additions, (F4) is unaffected, but the sentence should read "additions (transvections), with
sign changes realized by reorientation".

### 14. REMARK — §9(d)/(F4): the geometric step needs simple connectivity, not just vanishing homology

Sentences (§9(d), lines 259–263; echoed in (F4), §1 lines 56–59): the chain "homology-sphere
middle level $\Rightarrow$ surjective middle matrix $\Rightarrow$ unit entry $\Rightarrow$ (F2)
cancellable pair" is algebraically correct, but the last step applies (F2), whose hypothesis is
the nullhomotopy/`hnull` condition; vanishing middle homology alone does not provide it (a
homology sphere need not be simply connected). Name the hypothesis where the chain is asserted
(it is satisfied in the h-cobordism application).
