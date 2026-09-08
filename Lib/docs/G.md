# Lane G — textbook, decomposition, placement, and typed ledger

**Smale's recognition theorem** (Smale, *Generalized Poincaré's conjecture in dimensions
greater than four*, Ann. Math. 74 (1961), Theorem A; Milnor, *Lectures on the h-cobordism
theorem*, Thm. 9.1 for the handle-elimination pattern): *a compact smooth manifold homotopy
equivalent to the 6-sphere is homeomorphic to the 6-sphere.*

Per decision Q1 (DEFAULT): the lane keeps $n = 6$ and generalizes only the model space — the
theorem already takes an arbitrary finite-dimensional real normed space $E$ with
$\mathrm{finrank}\, E = 6$; the five spellings of $S^6$ consolidate on
`Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1`; the vestigial `[SecondCountableTopology M]`
on the current headline wrapper is dropped in the `Lib/` statement (it is implied by
compactness, and the proof never uses it — the inner chain does not take it). The
generalization to $n \geq 5$ is the follow-up lane G′ and is **not** started here.

Contents:

* **Axis 1** (§§1–7): the complete textbook proof, ordinary mathematics, no Lean names.
* **Axes 2–3** (§8): additive decomposition in dependency order.
* **Axis 4** (§9): placement with twins.
* **Axis 5** (§10): typed ledger with seams.
* **Open items** (§11).

---

# Axis 1 — the textbook proof

## 1. The theorem

**Theorem (Smale 1961, Theorem A at $n = 6$).** *Let $E$ be a 6-dimensional finite-dimensional
real normed space and $M$ a compact, Hausdorff, smooth ($C^\infty$) manifold modeled on $E$.
If $M$ is homotopy equivalent to the 6-sphere $S^6$, then $M$ is homeomorphic to $S^6$.*

Remarks. (a) The hypothesis "homotopy equivalent" is used through three corollaries: $M$ is
path connected; $M$ is simply connected ($\pi_1 M = 0$); and $M$ has the homology of $S^6$:
$\widetilde H_k(M) = 0$ for $k \neq 6$ and $H_6(M) \cong \mathbb{Z}$. (b) The conclusion is
*homeomorphism*, not diffeomorphism: the argument produces a two-disc decomposition and
invokes Reeb's theorem; the smooth structure is used only to run Morse theory. (c) In the
library the target sphere is the unit sphere of $\mathbb{R}^7$,
`Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1`, and the file's docstring records the precise
relation to Mathlib's
`proof_wanted ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere` (topological, every $n$,
Euclidean model, no compactness): our theorem is the smooth compact case at $n = 6$, strictly
stronger per unit of generality dropped and strictly weaker in $n$.

## 2. The strategy

Reeb's theorem (lane D1): a compact smooth $n$-manifold admitting a smooth function with
exactly two critical points is homeomorphic to $S^n$ (the sublevel set below a middle regular
value is a disc, by the flow and the regular-interval theorem; the complementary superlevel is
a disc by the same applied to $-f$; a manifold glued from two discs along their common boundary
sphere is homeomorphic to the sphere).

So the task is: *produce a smooth function on $M$ with exactly two critical points.* This is
done by handle elimination from an arbitrary Morse function, using the hypotheses of simple
connectivity and the homology of a sphere. The elimination has three campaigns:

1. **Indices 0 and 6** — connectedness leaves one index-0 critical point (a minimum) and one
   index-6 point (a maximum): a minimal system has one of each (§3).
2. **Indices 1 and 5** — the handle trade: on a simply connected manifold of dimension
   $n \geq 6$ an index-1 handle can be traded for an index-3 handle (birth a cancelling
   $(2,3)$-pair, then cancel the $(1,2)$-pair); dually for index 5. Minimality forbids the
   trade's net effect, so no index-1 or index-5 handles exist in a minimal system (§4).
3. **Indices 2, 3, 4** — the middle matrix campaign: the index-2/index-3 handles contribute a
   boundary matrix which, because $M$ is a homology sphere, presents the trivial group; integer
   reduction (lane F) turns it into a matrix with a unit entry; the Whitney trick (lane F)
   turns the unit into a single geometric intersection point; the first cancellation theorem
   (lane E1) removes the pair — contradicting minimality unless no middle handles exist.
   Index 4 is index 2 of $-f$, so indices 2, 3, 4 all vanish (§5).

Then $f$ has only the minimum and the maximum, and Reeb concludes (§6).

## 3. Minimal ordered systems

A Morse function $f \colon M \to \mathbb{R}$ with distinct critical values, ordered so that
values increase with the index (*ordered*), exists by lanes D1 (existence of Morse functions)
and E1 (rearrangement: the indices can be sorted without changing the critical set; an
*excellent* system additionally separates all critical values). Choose $f$ *minimal*: fewest
critical points among excellent ordered systems; and subject to that, *outer-index-minimal*:
fewest index-(1) plus index-($n-1$) points. (Existence of the minimum: the critical set is
finite, so both minima are attained.)

Since $M$ is connected, a minimal $f$ has exactly one local minimum (two minima would give two
index-0 handles; their basins are open and disjoint... more directly: connectedness plus the
handle picture forces a 0-handle per component at minimum; two minima would be cancelable or
connectable, contradicting minimality — the code's
`minimal_excellent_morse_extreme_counts_one`), and dually exactly one local maximum
(index 6).

## 4. Trading away index 1 (Milnor Thm. 8.1 at $n = 6$)

**The birth.** In a level band free of critical points, the birth theorem (lane E1) creates an
*excellent* cancelling pair of indices $(2, 3)$: a local cubic model with a single
intersection between the new attaching and belt spheres, embedded by the E2 machinery.

**The trade.** Suppose an index-1 critical point $q$ exists. Its attaching sphere is $S^0$; its
influence is local. The geometric content (the code's
`exists_one_to_three_handle_trade`): place the born 2-handle so that its attaching circle meets
the belt of the 1-handle in a single point (possible by the arc/tube machinery of E2/F in a
simply connected level; the level's simple connectivity is inherited from $M$ by the van
Kampen/Hurewicz bookkeeping of lanes A–B — the level of an ordered system below the index-2
handles is simply connected because the higher handles do not change $\pi_1$), then cancel the
$(1, 2)$-pair (first cancellation, E1). Net effect: one fewer index-1 point, one more index-3
point, total critical count unchanged.

**Minimality closes.** In an outer-index-minimal system the trade lowers the (index-1 +
index-5) count while keeping the total count fixed — a contradiction. Hence no index-1 points;
applying the same to $-f$ (whose indices are $6 - \lambda$, and whose minimality properties
transport by the duality lemmas), no index-5 points. $\square$

## 5. The middle campaign (indices 2, 3, 4)

Now $f$ has indices $0, 2, 3, 4, 6$ only. Choose the regular level $N$ separating index 2 from
index 3. The relevant homology: the sublevel $M_{\leq a}$ up through the index-2 handles has
$H_2$ free on the 2-handle cores (handle homology, lane D2/E1), and the attaching classes of
the index-3 handles give the *middle matrix* $M_3$: an $r \times c$ integer matrix ($r$ the
number of 2-handles, $c$ the number of 3-handles), equal — by lane F's intersection-number
theorem — to the matrix of signed intersection numbers of belt spheres $S^{3}$ (of the
2-handles) with attaching spheres $S^{2}$ (of the 3-handles) in the 5-dimensional level $N$.

**Vanishing.** Since $M$ is a homology sphere, $H_*(M_{\leq a})$ in degree 2 must be killed by
the index-3 handles: the middle matrix presents $H_2(\text{upper sublevel})$, which vanishes —
a presentation of the trivial group. By lane F's algebra (F4c), $M_3$ is surjective; hence
(F4a–b) a sequence of elementary column operations produces a unit entry; by F3 every such
operation is realized by handle slides; by F2 + §7 of lane F the unit entry is converted to a
single geometric intersection point of the corresponding belt/attaching spheres (the level $N$
is 5-dimensional, the spheres have dimensions 3 and 2 — the Whitney case $(p, q) = (3, 2)$,
$m = 5$, with the level's circles contracting by simple connectivity; this is exactly the
code's pinned instance, now generalized in lane F to the model form); and by the first
cancellation theorem (E1) the corresponding $(2, 3)$ pair cancels, *lowering the critical
count* — contradicting minimality unless there was nothing to cancel. Hence no index-2 and no
index-3 handles. (The contradiction argument is the code's
`minimal_ordered_index_two_count_zero`; the count bookkeeping
`ordered_no_middle_indices_count_two` then forces the total count to 2.)

**Index 4** is index 2 of $-f$: the same campaign on $-f$ (all hypotheses are
sign-symmetric) kills index 4. $\square$

## 6. The Reeb conclusion

The surviving minimal system has exactly two critical points: the unique minimum (index 0) and
the unique maximum (index 6). By Reeb's theorem (lane D1:
`Smale.ManifoldMorse.nonempty_homeomorphSphere_of_two_critical_points`, via the two-disc
decomposition: sublevel discs from the signed Morse charts, glued along the boundary sphere),
$M$ is homeomorphic to the sphere of dimension $\mathrm{finrank}\, E = 6$ — the unit sphere of
$\mathbb{R}^7$ in the consolidated spelling. $\square$

## 7. What is generalized and what is not

Generalized (per Q1): the model space — the whole chain takes an arbitrary
finite-dimensional real normed space $E$ with $\mathrm{finrank}\, E = 6$ already (the code's
signatures are `(E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]`;
no inner product is used anywhere in the chain), and the `Lib/` statement drops the vestigial
`[SecondCountableTopology M]` of the current wrapper (Recognition.lean:11314 — the inner chain
never uses it; a compact smooth Hausdorff manifold is second countable anyway, so the wrapper
loses no content). The five spellings of $S^6$
(`SphereHomology.UnitSphere 6`, `Smale.Hemisphere.Sphere 6`, `Smale.SixSphere`, `SixSphere`,
`SixSphereCube.StandardSphere`), all definitionally `Metric.sphere (0 : EuclideanSpace ℝ
(Fin 7)) 1`, consolidate on that spelling in the `Lib/` file; the `Hopf/` consumer keeps its
statement verbatim (the re-routing is definitional).

Not generalized: $n = 6$ stays. The $n \geq 5$ form (lane G′) needs lane F at full generality
*and* the middle-index range $2 \leq k \leq n - 2$ replacing the $n = 6$ coincidence "middle
indices $= \{2, 3, 4\}$ and index 4 is index 2 of $-f$". Do not start it.

---

# Axes 2–3 — additive decomposition, in dependency order

| # | Lemma (§) | Inputs | Output | Current `Hopf/` home (names; lines on 721fc82) |
|---|---|---|---|---|
| G1 | Homotopy-sphere data (§1) | homotopy invariance (A), spheres (A/B) | path/simply connected, homology vanishing of $M$ | `Smale.simplyConnectedSpace_of_homotopySixSphere`, `pathConnectedSpace_of_homotopySixSphere` (SingularHomology 19048–19056); `homotopySixSphere_homology_subsingleton` (SphereTopology 18589) |
| G2 | Minimal ordered systems (§3) | D1 (Morse existence), E1 (rearrangement) | minimal excellent ordered system, one min, one max | `exists_minimal_excellent_morse_system`, `exists_index_ordered_morse_system_preserving_critical_points`, `minimal_excellent_morse_extreme_counts_one` (SphereTopology 9456/10109/10180); `exists_outer_index_minimal_ordered_morse_system` (13171) |
| G3 | Handle trade (§4) | E1 (birth, cancellation), E2 (arcs), B ($\pi_1$) | index-1 → index-3 trade; outer counts vanish | `exists_excellent_indexed_morse_birth` (11803), `cancel_one_two_pair_at_unchanged_cut_of_unique_minimum` (12767), `exists_one_to_three_handle_trade*` (12962/13050/13143), `outer_index_minimal_index_one_count_zero` (13231), `outer_index_minimality_neg` (13279), `outer_index_minimal_outer_counts_zero` (13312) |
| G4 | Middle blocks and the matrix (§5) | F10, F1 | the middle family; the middle matrix surjective | `exists_middle_index_blocks` (18749), `exists_ordered_middle_family` (18831), `exists_canonical_middle_family` (Rec 4316), `canonical_middle_matrix_surjective` (Rec 5023), `middleMatrix_surjective_of_homotopySphere/_of_complete_blocks` (18701/18723) |
| G5 | The pivot and the cancellation (§5) | F (slides, integer reduction, Whitney, single intersection) | a cancelled pair; middle counts zero; count two | `exists_primitive_functional_unit` (Rec 9190), `exists_first_middle_pivot` (Rec 5505), `exists_native_belt_cut_family` (Rec 10165), `cancel_from_preserved_unit_belt_cut` (Rec 10514), `cancel_from_complete_middle_family` (Rec 10668), `minimal_ordered_index_two/four_count_zero` (Rec 10791/10851), `ordered_no_middle_indices_count_two` (Rec 11128) |
| G6 | Two critical points; Reeb (§6) | G2–G5, D1 (Reeb) | `Nonempty (M ≃ₜ S⁶)` | `critical_pair_of_surgery_count_two` (Rec 11255), `exists_two_critical_point_morse_of_homotopySixSphere` (Rec 11283), `nonempty_homeomorph_of_homotopySixSphere` (Rec 11301), headline (Rec 11312) |

Dependency order is row order; G1–G3 live in `Morse/MinimalSystem.lean` + `Morse/HandleTrade.lean`,
G4–G5 in `Morse/MiddleBlocks.lean`, G6 in `PoincareConjecture/Smale.lean`.

---

# Axis 4 — placement

| File | Rows | Mathlib twin |
|---|---|---|
| `Lib/Geometry/Manifold/Morse/MiddleBlocks.lean` | G4 (block structure, middle matrix surjectivity) | none existing; shape after the reference example |
| `Lib/Geometry/Manifold/Morse/HandleTrade.lean` | G3 | none existing |
| `Lib/Geometry/Manifold/Morse/MinimalSystem.lean` | G2, G5's count theorems | none existing |
| `Lib/Geometry/Manifold/PoincareConjecture/Smale.lean` | G1, G6 (the headline) | `Mathlib/Geometry/Manifold/PoincareConjecture.lean` (the `proof_wanted` file — our file is its smooth compact n=6 realization; the docstring records the relation) |

---

# Axis 5 — typed ledger

Seams: lanes D1 (Morse data, Reeb), E1 (rearrangement/birth/cancellation), E2 (transversality
inputs to F's Whitney step), F (the whole Whitney/slide/integer engine), A/B (homology and
simply-connected inputs). The consumers `Hopf/Final.lean` (through `Degree.
threefoldHomotopyEquiv`, which lane C re-routes) keep their statements.

**Row G-headline (the axiom probe).** Current (Recognition 11312, verbatim in the G map):
`Smale.homeomorphic_sixSphere_of_homotopySixSphere (E : Type) [NormedAddCommGroup E]
[NormedSpace ℝ E] [FiniteDimensional ℝ E] (M : Type) [TopologicalSpace M] [T2Space M]
[SecondCountableTopology M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
(hdim : Module.finrank ℝ E = 6) (hM : M ≃ₕ Smale.SixSphere) : Nonempty (M ≃ₜ Smale.SixSphere)`.
Target: same statement in `Lib/Geometry/Manifold/PoincareConjecture/Smale.lean` as
`Geometry.Manifold.PoincareConjecture.homeomorphic_sphere_of_homotopyEquiv_sphere_six` (name
fixed at the rename commit) **minus** the vestigial `[SecondCountableTopology M]`, with
`Smale.SixSphere` replaced by the consolidated `Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1`.
The `Hopf/` theorem keeps its current statement (instance included) and re-proves through the
Lib theorem (a `letI`/infer-step adapter — the statement seen from `Hopf/` is unchanged, per
the comparator gate).

**Rows G1–G6.** The full chain with verbatim signatures is in `~/s6-notes/G-map.md` §1
((1)–(15)); each row moves its block at unchanged statement except for the sphere-spelling
consolidation (defeq, no consumer-visible change). The `Type` vs `Type*` note: the chain mixes
`(E : Type)` (Recognition chain) and `{E M : Type*}` (Reeb, handle trade) — normalize to
`Type*` per the checklist; the one universe-relevant declaration is again
`CubicalBoundary.cubicalBoundaryValue_eq_zero`-style polymorphism, which lane C already owns.

---

# Open items, seams, probes

1. **Seams (blocking).** Lane G starts after C and F land (per the DAG). The ledger rows are
   then exact; probes: `lake env lean
   Lib/Geometry/Manifold/PoincareConjecture/G_InterfaceCheck.lean` + consumer probe; receipt at
   `Lib/docs/G-INTERFACE_RECEIPT.md`.
2. **The vestigial instance.** Dropping `[SecondCountableTopology M]` in the Lib statement is
   authorized by the task; the Hopf wrapper keeps it (statement unchanged); record both in the
   lane report.
3. **Sphere consolidation.** The five spellings collapse to the `Metric.sphere (0 :
   EuclideanSpace ℝ (Fin 7)) 1` spelling; the consumer-side abbrevs stay as local notation in
   `Hopf/` until the final cleanup; `Hopf/Final.lean`'s own `unitSphere` abbrev is a consumer
   detail, unchanged.
4. **The Mathlib `proof_wanted` relation** goes into the `Smale.lean` module docstring verbatim
   as in §1 remark (c).
5. **Review.** Stage-2 independent review of §§1–7: scheduled; report in `~/s6-notes/`.
6. **GLM-lane overlap discovered after landing A–D2/H/I:** lane E2's source ranges were largely
   swept into GLM's `Lib/Geometry/Manifold/Morse/SurgeryWindows.lean` (17,556 lines; the D2
   baseline blob contains e.g. `exists_compact_embedding_of_immersion` at its line 12352 and
   `exists_ambient_transverse_diffeomorph` at 17495). Lane E2's Lean work is therefore a
   Lib-internal *split* of that file (plus the generalization G-E2), not a Hopf→Lib move;
   lane F's sources remain in `Hopf/` (verified: `TubularBigon`, `primitive_row_*` unmoved).
   This affects E2/F placement timing, not this lane's content.
