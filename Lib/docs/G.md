# Lane G — textbook, decomposition, placement, and typed ledger

**Independent Stage-2 review at `699d1a4` (astra): NO-GO — repairs applied, pending
re-review.** Astra's numbered findings are in `Lib/docs/G-stage2-astra-review.md`
(in-tree copy of `~/s6-notes/G-stage2-astra-review.md`). Repairs landed: the trade cut,
elimination order, and Whitney codimension-two input in §§4–5 are rewritten with the
source's actual mechanisms; the unique-minimum argument in §3 is expanded with the
(0,1)-cancellation mechanism; every ledger signature is now verbatim at live coordinates
(no compression); G2 is split G2a/G2b with the file placement resolved. Muse's earlier
`G-stage2-review.md` is **self-review, superseded** — the astra review governs; a
successful re-review is required before Axis-6.

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
real normed space and $M$ a compact, Hausdorff, smooth ($C^\infty$) manifold without boundary modeled on $E$.
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
Euclidean model, no explicit compactness): our theorem establishes the smooth compact
$n = 6$ case, after transport along a linear equivalence of model spaces. It does not
strengthen the general topological statement.

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
*excellent* system additionally separates all critical values — the code's
`exists_index_ordered_morse_system_preserving_critical_points`, which preserves the critical
set, all indices, and all index counts).

**Existence of the minima.** Choose $f$ *minimal*: the set of critical-point counts of
excellent Morse functions on $M$ is a nonempty subset of $\mathbb{N}$, so it has a least
element attained by some $f$ (the code's `exists_minimal_excellent_morse_system` performs
this `Nat.find`; the comparison class is *every* smooth Morse $g$ with distinct critical
values, ordered or not). Then order $f$ by the rearrangement above — ordering preserves the
count, so minimality is retained — and subject to the minimal count choose $f$
*outer-index-minimal*: the index-$1$ + index-$(n-1)$ count is least among minimal ordered
systems (a second well-ordering; the code's
`exists_outer_index_minimal_ordered_morse_system`).

**Unique minimum.** Suppose a minimal excellent system has at least two index-0 points.
The descending basin of each minimum is open, and the flow from a generic point ends at a
critical point; because $M$ is connected, the basin boundaries must be joined by 1-handles —
concretely, there is an index-1 point $q$ whose two attaching ends (the two points of its
$S^0$ attaching sphere) descend to minima in *different* basins (the code's
`exists_native_one_handle_joining_components`). Realizing the two descending branches
geometrically (`realize_one_handle_minimum_branches`) produces a gradient-like field along
which $q$ is joined to two minima $p, r$; the higher of the two then forms a cancelling
$(0,1)$-pair with $q$, and the first cancellation theorem removes both
(`cancel_realized_higher_minimum`). The result is an excellent Morse function with exactly
two fewer critical points (`exists_excellent_morse_reduction_of_multiple_minima`),
contradicting minimality (`minimal_excellent_morse_forbids_pair_removal`). Hence
`nativeMorseCount E f 0 = 1` (`minimal_excellent_morse_minimum_count_one`); applied to $-f$,
whose indices are $n - \lambda$, `nativeMorseCount E f n = 1` — together
`minimal_excellent_morse_extreme_counts_one`, and at $n = 6$ this is one minimum and one
maximum.

## 4. Trading away index 1 (Milnor Thm. 8.1 at $n = 6$)

**The birth.** In a level band free of critical points, the birth theorem (lane E1) creates an
*excellent* cancelling pair of indices $(2, 3)$: a local cubic model with a single
intersection between the new attaching and belt spheres, embedded by the E2 machinery.

**The trade.** Suppose an index-1 critical point $q$ exists. Its attaching sphere is $S^0$.
The relevant regular cut $a$ is **after the original index-2 point region used by the
argument and before the index-3 points**, not below the index-2 handles: 2-handles can kill
fundamental-group generators, so a level below them need not be simply connected. The
source's cut has index at most $2$ below and at least $3$ above (`hlow`/`hhigh`), with $q$
below the cut and a critical-free band above it (the `Ioo a u` hypothesis) containing a
basepoint `x`. The trade proceeds in two steps:

* **Birth above the cut** (`exists_excellent_indexed_morse_birth` at $k = 2$): inside the
  band, birth an excellent cancelling $(2,3)$-pair $b_2, b_3$. The birth changes nothing at
  or below the cut: the level $f = a$ is preserved verbatim (`heq`, `hsub`, `hlevel` in the
  code), the cut stays regular for the new function (`hgr`), the unique minimum survives
  (`birth_preserves_unique_index_zero`), and there is a value gap below $b_2$ (`hgap`).
* **Cancellation at the unchanged cut**
  (`cancel_one_two_pair_at_unchanged_cut_of_unique_minimum`): the born 2-handle's attaching
  circle is placed, in the preserved level $f^{-1}(a)$, to meet the belt sphere of the
  1-handle $q$ transversely in a single point, and the first cancellation theorem removes
  the $(1,2)$-pair $(q, b_2)$ *without disturbing the cut*. The placement is the
  substantive geometric content: the source realizes the two branches of the unique
  minimum's 1-handle (`realize_unique_minimum_one_handle_branches`), produces flow windows
  avoiding the level (`exists_same_flow_windows_avoiding_level`), identifies the attaching
  branches along the common flow (`attaching_branches_of_same_flow`), uses the two distinct
  unit-sphere points of the 1-handle's one-dimensional negative-coordinate space
  (`exists_distinct_unitSphere_points_of_finrank_one`) to hit the belt once, and feeds the
  transverse level data to
  `cancel_one_two_pair_at_preserved_middle_cut`
  (`exists_handle_trade_transverse_level_data` +
  `cancel_transverse_pair_after_flow_preserving_descent`).

Net effect (`exists_one_to_three_handle_trade`): an excellent Morse function $h$ with the
same total count, `count 1` decreased by one, `count 3` increased by one, all other index
counts unchanged — the born $b_3$ survives as the new index-3 point.

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

**Vanishing.** Handles of index at least 4 do not change $H_2$, so the sublevel just
after all index-3 handles has the same $H_2$ as $M$, namely zero. The handle chain complex
therefore gives a surjection $M_3 : \mathbb Z^c \to \mathbb Z^r$. If $r>0$, select a
primitive coordinate functional on $\mathbb Z^r$; its composite with $M_3$ is a primitive
integer row. Elementary column operations produce a unit in that row and are realized
geometrically by slides of the 3-handles.

The belt sphere of a 2-handle is $S^3$, and the attaching sphere of a 3-handle is $S^2$,
in the 5-dimensional regular level $N$. **The Whitney step needs more than ambient simple
connectivity.** Milnor's Theorem 6.6, with the moving sheet of dimension $2$ and the fixed
sheet of dimension $3$, requires injectivity of
$\pi_1(N \smallsetminus \text{fixed sheet}) \to \pi_1(N)$ in addition to the contractible
Whitney loop and orientation hypotheses. The required input is supplied by the handle
structure as follows — this is the mechanism the code implements, replacing ambient
simple connectivity with a *lower-level* one.

* **The lower level of an index-2 point is simply connected for circles.**
  `lower_circle_nullhomotopies_of_ordered_native_indices` (SphereTopology:5821): in an
  ordered system with one minimum and no index-1 points, every circle in the lower level
  of an index-$2$ point is nullhomotopic. The proof is an induction up the ordered window
  sequence (`lower_circle_nullhomotopies_of_middle_indices`, SphereTopology:5716): the
  first sublevel is a disk (its level is a $5$-sphere, circles contract), and each
  subsequent handle before the index-$2$ block has index $2$ or $3$ — attaching such a
  handle preserves "all circles in the level contract," because a circle in the new level
  can be isotoped off the belt sphere $S^{5-k}$ (for $k \in \{2,3\}$ the sum
  $1 + (5-k) < 5$ puts the circle disjoint from the belt generically) and then contracts
  in the previous level.
* **Transport to the belt complement.** The belt $S^3$ of the chosen index-$2$ handle is
  the boundary of its descending disk; flowing the level minus a tubular neighbourhood of
  the belt downwards lands in the lower level of that handle, so a circle in the
  complement is homotopic into the lower level, where it contracts. The code's
  `exists_native_belt_cut_family` (Recognition:8331) performs this transport: it returns
  the lower-level circle nullhomotopies (from `last_index_two_collapse_is_primitive`,
  Recognition:8295) *together with* the transported attaching family at the new belt cut,
  the preserved matrix equality, and surjectivity — i.e. it moves the whole middle-block
  data to the cut where the cancellation is performed.
* **The cancellation input.** `cancel_from_preserved_unit_belt_cut` (Recognition:8680)
  and `cancel_from_complete_middle_family` (Recognition:8834) consume the nullhomotopy as
  the hypothesis `hnull : ∀ δ : C(S¹, LowerLevel p), ∃ z, δ ~ const z`, alongside the unit
  coordinate `natAbs (indexTwoCollapseCoordinate … (middleSectionClass γ)) = 1` — the
  single transverse intersection needed for first cancellation. In the textbook
  presentation the `hnull` hypothesis is exactly the codimension-two complement
  condition transported to the level where the Whitney disk must be embedded.

Once this input is in place, the unit gives one transverse geometric intersection and
the first cancellation theorem removes the $(2,3)$ pair. This lowers the total critical
count, contradicting minimality when $r>0$. Thus there are no index-2 handles; surjectivity
alone does **not** eliminate the remaining index-3 handles.

**Index 4** is index 2 of $-f$: the same campaign on $-f$ kills index 4.
Only then does $H_3(M)=0$ force the index-3 count to vanish: the handle chain groups in
degrees 2 and 4 are zero, so $H_3(M)$ is the free group on the remaining 3-handles.
The source's complete-block matrix/count argument implements this final step. There are
then exactly two critical points. $\square$

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
`[SecondCountableTopology M]` of the current wrapper (Recognition.lean:9429 — the inner chain
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

| # | Lemma (§) | Inputs | Output | Current `Hopf/` home (names; lines on `1cc1784`) |
|---|---|---|---|---|
| G1 | Homotopy-sphere data (§1) | homotopy invariance (A), spheres (A/B) | path/simply connected, homology vanishing of $M$ | `Smale.simplyConnectedSpace_of_homotopySixSphere` (SingularHomology 14047), `Smale.pathConnectedSpace_of_homotopySixSphere` (SingularHomology 14052); `Smale.homotopySixSphere_homology_subsingleton` (SphereTopology 14226) |
| G2 | Minimal ordered systems (§3) | D1 (Morse existence), E1 (rearrangement) | minimal excellent ordered system, one min, one max | `MorseCancel.exists_minimal_excellent_morse_system` (SphereTopology 6289), `MorseCancel.exists_index_ordered_morse_system_preserving_critical_points` (6942), `MorseCancel.minimal_excellent_morse_extreme_counts_one` (7013), `MorseCancel.exists_outer_index_minimal_ordered_morse_system` (10004), `MorseCancel.exists_minimal_ordered_morse_system_without_outer_indices` (10194) |
| G3 | Handle trade (§4) | E1 (birth, cancellation), E2 (arcs), B ($\pi_1$) | index-1 → index-3 trade; outer counts vanish | `MorseCancel.exists_excellent_indexed_morse_birth` (8636), `MorseCancel.cancel_one_two_pair_at_unchanged_cut_of_unique_minimum` (9600), `MorseCancel.exists_one_to_three_handle_trade` (9795), `MorseCancel.exists_one_to_three_handle_trade_at_cut` (9883), `MorseCancel.exists_one_to_three_handle_trade_of_ordered_indices` (9976), `MorseCancel.outer_index_minimal_index_one_count_zero` (10064), `MorseCancel.outer_index_minimality_neg` (10112), `MorseCancel.outer_index_minimal_outer_counts_zero` (10145) |
| G4 | Middle blocks and the matrix (§5) | F10, F1 | the middle family; the middle matrix surjective | `MorseCancel.exists_middle_index_blocks` (SphereTopology 14386), `AdaptedWindows.exists_ordered_middle_family` (14468), `AdaptedWindows.exists_canonical_middle_family` (Rec 2688), `MorseCancel.canonical_middle_matrix_surjective` (Rec 3365), `Smale.ManifoldMorse.SurgeryWindows.middleMatrix_surjective_of_homotopySphere` / `..._of_complete_blocks` (SphereTopology 14338/14360) |
| G5 | The pivot and the cancellation (§5) | F (slides, integer reduction, Whitney, single intersection) | a cancelled pair; middle counts zero; count two | `AdaptedWindows.exists_primitive_functional_unit` (Rec 7365), `AdaptedWindows.exists_first_middle_pivot` (Rec 3847), `MorseCancel.exists_native_belt_cut_family` (Rec 8340), `MorseCancel.cancel_from_preserved_unit_belt_cut` (Rec 8689), `MorseCancel.cancel_from_complete_middle_family` (Rec 8843), `MorseCancel.minimal_ordered_index_two_count_zero` / `..._four_count_zero` (Rec 8966/9026), `MorseCancel.ordered_no_middle_indices_count_two` (Rec 9258) |
| G6 | Two critical points; Reeb (§6) | G2–G5, D1 (Reeb) | `Nonempty (M ≃ₜ S⁶)` | `MorseCancel.critical_pair_of_surgery_count_two` (Rec 9385), `MorseCancel.exists_two_critical_point_morse_of_homotopySixSphere` (Rec 9413), `MorseCancel.nonempty_homeomorph_of_homotopySixSphere` (Rec 9431), `Smale.ManifoldMorse.nonempty_homeomorphSphere_of_two_critical_points` (Rec 9344), headline `Smale.homeomorphic_sixSphere_of_homotopySixSphere` (Rec 9442) |

These rows were originally thematic groups; the true dependency order requires splitting
G2: `exists_minimal_ordered_morse_system_without_outer_indices` (G2b) consumes G3's
`outer_index_minimal_outer_counts_zero`. The ledger below orders G2a → G3 → G2b → G4 →
G5 → G6, and the file split follows it (see Axis 4): `MinimalSystem.lean` = G1 + G2a;
`HandleTrade.lean` = G3 + G2b (post-trade assembly belongs with the trade);
`MiddleBlocks.lean` = G4 + G5; `PoincareConjecture/Smale.lean` = G6 + the headline.

---

# Axis 4 — placement

| File | Rows | Mathlib twin |
|---|---|---|
| `Lib/Geometry/Manifold/Morse/MinimalSystem.lean` | G1 (homotopy-sphere data), G2a (minimal excellent/ordered/outer-minimal systems) | none existing |
| `Lib/Geometry/Manifold/Morse/HandleTrade.lean` | G3 (birth, trade, outer-count kills), G2b (`without_outer_indices` assembly) | none existing |
| `Lib/Geometry/Manifold/Morse/MiddleBlocks.lean` | G4 (block structure, middle matrix surjectivity), G5 (pivot, cancellation, count conclusions) | none existing; shape after the reference example |
| `Lib/Geometry/Manifold/PoincareConjecture/Smale.lean` | G6 (Reeb assembly, the headline) | `Mathlib/Geometry/Manifold/PoincareConjecture.lean` (the `proof_wanted` file — our file is its smooth compact n=6 realization; the docstring records the relation) |

Import order is `MinimalSystem → HandleTrade → MiddleBlocks → Smale`, matching the
G2a → G3 → G2b → G4 → G5 → G6 dependency chain.

---

# Axis 5 — typed ledger

Seams: lanes D1 (Morse data, Reeb), E1 (rearrangement/birth/cancellation), E2 (transversality
inputs to F's Whitney step), F (the whole Whitney/slide/integer engine), A/B (homology and
simply-connected inputs). The consumers `Hopf/Final.lean` (through `Degree.
threefoldHomotopyEquiv`, which lane C re-routes) keep their statements.

**Row G-headline (the axiom probe).** Current (Recognition 9427 at `699d1a4`, verbatim in the G map):
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

**Rows G1–G6 — the typed ledger.** All signatures below are **verbatim from the current
sources** (coordinates re-verified at `699d1a4` against the astra census); nothing is
reconstructed or compressed. The row order G1 → G2a → G3 → G2b → G4 → G5 → G6 is the true
dependency order — G2 splits because `exists_minimal_ordered_morse_system_without_
outer_indices` (G2b) consumes G3's `outer_index_minimal_outer_counts_zero`.

**Row G1 (homotopy-sphere data).** Verbatim:

```lean
theorem Smale.simplyConnectedSpace_of_homotopySixSphere {M : Type*} [TopologicalSpace M]
    (e : M ≃ₕ Smale.SixSphere) : SimplyConnectedSpace M          -- SingularHomology.lean:14047

theorem Smale.pathConnectedSpace_of_homotopySixSphere {M : Type*} [TopologicalSpace M]
    (e : M ≃ₕ Smale.SixSphere) : PathConnectedSpace M            -- SingularHomology.lean:14052

theorem Smale.homotopySixSphere_homology_subsingleton {M : Type} [TopologicalSpace M]
    (h : M ≃ₕ Smale.SixSphere) (k : ℕ) (hk : k ≠ 0) (hktop : k ≠ 6) :
    Subsingleton (SingularMayerVietoris.SingularHomology M k)    -- SphereTopology.lean:14166
```

Pure lemmas (no manifold content) — these are the hypothesis-generation half of the headline's
`(e : M ≃ₕ S⁶)` input; they move verbatim to `Morse/MinimalSystem.lean` or a small
`PoincareConjecture/HomotopyData` section. The `≃ₕ Smale.SixSphere` spelling consolidates to
`≃ₕ Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1` (defeq — `Smale.SixSphere` is that sphere).

**Row G2a (preliminary minimal ordered systems).** Pure existence/minimality tower —
no surgical content; complete verbatim signatures:

```lean
theorem MorseCancel.exists_minimal_excellent_morse_system (E : Type*) (M : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] :
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        Smale.ManifoldMorse.IsMorse E f ∧
          ∃ _ : AdaptedWindows E f,
            ∀ g : M → ℝ,
              ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
                Smale.ManifoldMorse.IsMorse E g →
                  Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) →
                    (Smale.ManifoldMorse.criticalPoints E f).ncard ≤
                      (Smale.ManifoldMorse.criticalPoints E g).ncard := by  -- SphereTopology.lean:6290

theorem MorseCancel.exists_index_ordered_morse_system_preserving_critical_points {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]
    {f₀ : M → ℝ} (S₀ : AdaptedWindows E f₀) (hf₀ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f₀)
    (hm₀ : Smale.ManifoldMorse.IsMorse E f₀) :
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        Smale.ManifoldMorse.IsMorse E f ∧
          Smale.ManifoldMorse.criticalPoints E f = Smale.ManifoldMorse.criticalPoints E f₀ ∧
            (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f₀,
                nativeMorseIndex E f x = nativeMorseIndex E f₀ x) ∧
              ∃ _ : AdaptedWindows E f,
                (∀ p q : Smale.ManifoldMorse.criticalPoints E f,
                    f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q) ∧
                  ∀ k, nativeMorseCount E f k = nativeMorseCount E f₀ k := by  -- SphereTopology.lean:6943

theorem MorseCancel.minimal_excellent_morse_extreme_counts_one {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f)
    (hminimal :
      ∀ g : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
          Smale.ManifoldMorse.IsMorse E g →
            Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) →
              (Smale.ManifoldMorse.criticalPoints E f).ncard ≤
                (Smale.ManifoldMorse.criticalPoints E g).ncard) :
    nativeMorseCount E f 0 = 1 ∧ nativeMorseCount E f (Module.finrank ℝ E) = 1 := by  -- SphereTopology.lean:7014

theorem MorseCancel.exists_outer_index_minimal_ordered_morse_system (E : Type) (M : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] :
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        Smale.ManifoldMorse.IsMorse E f ∧
          ∃ _ : AdaptedWindows E f,
            (∀ p q : Smale.ManifoldMorse.criticalPoints E f,
                f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q) ∧
              nativeMorseCount E f 0 = 1 ∧
                nativeMorseCount E f (Module.finrank ℝ E) = 1 ∧
                  (∀ g : M → ℝ,
                      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
                        Smale.ManifoldMorse.IsMorse E g →
                          Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) →
                            (Smale.ManifoldMorse.criticalPoints E f).ncard ≤
                              (Smale.ManifoldMorse.criticalPoints E g).ncard) ∧
                    ∀ g : M → ℝ,
                      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
                        Smale.ManifoldMorse.IsMorse E g →
                          Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) →
                            (Smale.ManifoldMorse.criticalPoints E g).ncard =
                                (Smale.ManifoldMorse.criticalPoints E f).ncard →
                              nativeMorseCount E f 1 + nativeMorseCount E f 5 ≤
                                nativeMorseCount E g 1 + nativeMorseCount E g 5 := by  -- SphereTopology.lean:10005
```

`exists_minimal_excellent_morse_system` is the textbook "minimal Morse function" input
(Faudree: an *excellent* Morse function minimising critical-point count); the other three
refine it — index ordering, `count 0 = count dim = 1` (single min/max, §3 below), and
outer-index minimality among equal critical-cardinality competitors.

**Row G3 (handle trade, Milnor Thm. 8.1 at n=6).** Birth → trade → count contradiction.
Complete verbatim signatures:

```lean
theorem MorseCancel.exists_excellent_indexed_morse_birth {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f)) {l u : ℝ}
    (hband : ∀ y, f y ∈ Set.Ioo l u → y ∉ Smale.ManifoldMorse.criticalPoints E f) {x : M}
    (hx : f x ∈ Set.Ioo l u) {k : ℕ} (hk : k < Module.finrank ℝ E) {U : Set M} (hU : IsOpen U)
    (hxU : x ∈ U) :
    ∃ (g : M → ℝ) (p q : M),
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        Smale.ManifoldMorse.IsMorse E g ∧
          Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) ∧
            p ∈ U ∧
              q ∈ U ∧
                nativeMorseIndex E g p = k ∧
                  nativeMorseIndex E g q = k + 1 ∧
                    g p < g q ∧
                      g p ∈ Set.Ioo l u ∧
                        g q ∈ Set.Ioo l u ∧
                          (Smale.ManifoldMorse.criticalPoints E g).ncard =
                              (Smale.ManifoldMorse.criticalPoints E f).ncard + 2 ∧
                            (∀ y,
                                y ∈ Smale.ManifoldMorse.criticalPoints E g ↔
                                  y ∈ Smale.ManifoldMorse.criticalPoints E f ∨ y = p ∨ y = q) ∧
                              (∀ y, y ∉ U → g =ᶠ[𝓝 y] f) ∧
                                (∀ y ∈ Smale.ManifoldMorse.criticalPoints E f, g =ᶠ[𝓝 y] f) ∧
                                  nativeMorseCount E g k = nativeMorseCount E f k + 1 ∧
                                    nativeMorseCount E g (k + 1) =
                                        nativeMorseCount E f (k + 1) + 1 ∧
                                      ∀ j,
                                        j ≠ k →
                                          j ≠ k + 1 →
                                            nativeMorseCount E g j = nativeMorseCount E f j := by  -- SphereTopology.lean:8637

theorem MorseCancel.cancel_one_two_pair_at_unchanged_cut_of_unique_minimum {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] {f g : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (hmg : Smale.ManifoldMorse.IsMorse E g)
    (hinjg : Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g)) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6) {a : ℝ}
    (hfr : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hgr : ∀ y, g y = a → y ∉ Smale.ManifoldMorse.criticalPoints E g)
    (heq : ∀ y, g y = a ↔ f y = a)
    (hhigh : ∀ z : Smale.ManifoldMorse.criticalPoints E f, a ≤ f z → 3 ≤ nativeMorseIndex E f z)
    (hlow : ∀ z : Smale.ManifoldMorse.criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ 3)
    (m q r : Smale.ManifoldMorse.criticalPoints E g) (hm : nativeMorseIndex E g m = 0)
    (hq : nativeMorseIndex E g q = 1) (hr : nativeMorseIndex E g r = 2)
    (hminimum : ∀ z : Smale.ManifoldMorse.criticalPoints E g, nativeMorseIndex E g z = 0 → z = m)
    (hqa : g q < a) (har : a < g r)
    (hgap : ∀ z : Smale.ManifoldMorse.criticalPoints E g, g z < g r → g z < a)
    (hnewlow :
      ∀ z : Smale.ManifoldMorse.criticalPoints E g, g z ≤ a → nativeMorseIndex E g z ≤ 2) :
    ∃ h : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h ∧
        Smale.ManifoldMorse.IsMorse E h ∧
          Set.InjOn h (Smale.ManifoldMorse.criticalPoints E h) ∧
            (Smale.ManifoldMorse.criticalPoints E h).ncard + 2 =
                (Smale.ManifoldMorse.criticalPoints E g).ncard ∧
              (∀ w,
                  w ∈ Smale.ManifoldMorse.criticalPoints E h ↔
                    w ∈ Smale.ManifoldMorse.criticalPoints E g ∧ w ≠ q.val ∧ w ≠ r.val) ∧
                ∀ w ∈ Smale.ManifoldMorse.criticalPoints E h,
                  nativeMorseIndex E h w = nativeMorseIndex E g w := by  -- SphereTopology.lean:9601

theorem MorseCancel.exists_one_to_three_handle_trade_at_cut {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6) (m q : Smale.ManifoldMorse.criticalPoints E f)
    (hm0 : nativeMorseIndex E f m = 0) (hq1 : nativeMorseIndex E f q = 1)
    (hminimum : ∀ z : Smale.ManifoldMorse.criticalPoints E f, nativeMorseIndex E f z = 0 → z = m)
    {a : ℝ} (hreg : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hhigh : ∀ z : Smale.ManifoldMorse.criticalPoints E f, a ≤ f z → 3 ≤ nativeMorseIndex E f z)
    (hlow : ∀ z : Smale.ManifoldMorse.criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ 2)
    (hqa : f q < a) :
    ∃ h : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h ∧
        Smale.ManifoldMorse.IsMorse E h ∧
          Set.InjOn h (Smale.ManifoldMorse.criticalPoints E h) ∧
            (Smale.ManifoldMorse.criticalPoints E h).ncard =
                (Smale.ManifoldMorse.criticalPoints E f).ncard ∧
              nativeMorseCount E h 1 + 1 = nativeMorseCount E f 1 ∧
                nativeMorseCount E h 3 = nativeMorseCount E f 3 + 1 ∧
                  ∀ j, j ≠ 1 → j ≠ 3 → nativeMorseCount E h j = nativeMorseCount E f j := by  -- SphereTopology.lean:9884

theorem MorseCancel.exists_one_to_three_handle_trade_of_ordered_indices {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    [PathConnectedSpace M] (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (m q : Smale.ManifoldMorse.criticalPoints E f) (hm0 : nativeMorseIndex E f m = 0)
    (hq1 : nativeMorseIndex E f q = 1)
    (hminimum :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f, nativeMorseIndex E f z = 0 → z = m) :
    ∃ h : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h ∧
        Smale.ManifoldMorse.IsMorse E h ∧
          Set.InjOn h (Smale.ManifoldMorse.criticalPoints E h) ∧
            (Smale.ManifoldMorse.criticalPoints E h).ncard =
                (Smale.ManifoldMorse.criticalPoints E f).ncard ∧
              nativeMorseCount E h 1 + 1 = nativeMorseCount E f 1 ∧
                nativeMorseCount E h 3 = nativeMorseCount E f 3 + 1 ∧
                  ∀ j, j ≠ 1 → j ≠ 3 → nativeMorseCount E h j = nativeMorseCount E f j := by  -- SphereTopology.lean:9977

theorem MorseCancel.outer_index_minimal_index_one_count_zero {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1)
    (hsecondary :
      ∀ g : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
          Smale.ManifoldMorse.IsMorse E g →
            Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) →
              (Smale.ManifoldMorse.criticalPoints E g).ncard =
                  (Smale.ManifoldMorse.criticalPoints E f).ncard →
                nativeMorseCount E f 1 + nativeMorseCount E f 5 ≤
                  nativeMorseCount E g 1 + nativeMorseCount E g 5) :
    nativeMorseCount E f 1 = 0 := by  -- SphereTopology.lean:10065

theorem MorseCancel.outer_index_minimality_neg {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (hdim : Module.finrank ℝ E = 6)
    (hsecondary :
      ∀ g : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
          Smale.ManifoldMorse.IsMorse E g →
            Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) →
              (Smale.ManifoldMorse.criticalPoints E g).ncard =
                  (Smale.ManifoldMorse.criticalPoints E f).ncard →
                nativeMorseCount E f 1 + nativeMorseCount E f 5 ≤
                  nativeMorseCount E g 1 + nativeMorseCount E g 5) :
    ∀ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
        Smale.ManifoldMorse.IsMorse E g →
          Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) →
            (Smale.ManifoldMorse.criticalPoints E g).ncard =
                (Smale.ManifoldMorse.criticalPoints E (fun x => -f x)).ncard →
              nativeMorseCount E (fun x => -f x) 1 + nativeMorseCount E (fun x => -f x) 5 ≤
                nativeMorseCount E g 1 + nativeMorseCount E g 5 := by  -- SphereTopology.lean:10113

theorem MorseCancel.outer_index_minimal_outer_counts_zero {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1) (hsix : nativeMorseCount E f 6 = 1)
    (hsecondary :
      ∀ g : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
          Smale.ManifoldMorse.IsMorse E g →
            Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) →
              (Smale.ManifoldMorse.criticalPoints E g).ncard =
                  (Smale.ManifoldMorse.criticalPoints E f).ncard →
                nativeMorseCount E f 1 + nativeMorseCount E f 5 ≤
                  nativeMorseCount E g 1 + nativeMorseCount E g 5) :
    nativeMorseCount E f 1 = 0 ∧ nativeMorseCount E f 5 = 0 := by  -- SphereTopology.lean:10146
```

**Row G2b (post-trade assembly — consumes G3).** `exists_minimal_ordered_morse_system_
without_outer_indices` packages G2a + G3 (its proof calls
`outer_index_minimal_outer_counts_zero`); complete verbatim signature:

```lean
theorem MorseCancel.exists_minimal_ordered_morse_system_without_outer_indices (E : Type)
    (M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] (e : M ≃ₕ Smale.SixSphere) (hdim : Module.finrank ℝ E = 6) :
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        Smale.ManifoldMorse.IsMorse E f ∧
          ∃ _ : AdaptedWindows E f,
            (∀ p q : Smale.ManifoldMorse.criticalPoints E f,
                f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q) ∧
              nativeMorseCount E f 0 = 1 ∧
                nativeMorseCount E f 6 = 1 ∧
                  nativeMorseCount E f 1 = 0 ∧
                    nativeMorseCount E f 5 = 0 ∧
                      ∀ g : M → ℝ,
                        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
                          Smale.ManifoldMorse.IsMorse E g →
                            Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) →
                              (Smale.ManifoldMorse.criticalPoints E f).ncard ≤
                                (Smale.ManifoldMorse.criticalPoints E g).ncard := by  -- SphereTopology.lean:10195
```

**Row G4 (middle blocks and the matrix).** Verbatim:

```lean
theorem Smale.ManifoldMorse.SurgeryWindows.middleMatrix_surjective_of_homotopySphere {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hM : M ≃ₕ Smale.SixSphere) (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + c < S.count) (hthree : S.HasIndexThreeBlock r c)
    (hj : r + c + 1 < S.count)
    (hafter :
      ∀ i : Fin S.count,
        r + c < i.val →
          i.val + 1 < S.count →
            2 ≤ Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates ∧
              Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates ≠ 3) :
    Function.Surjective (S.middleMatrix hf r c htwo hc hthree).mulVec := by  -- SphereTopology.lean:14278

theorem Smale.ManifoldMorse.SurgeryWindows.middleMatrix_surjective_of_complete_blocks {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hM : M ≃ₕ Smale.SixSphere) (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + c < S.count) (hthree : S.HasIndexThreeBlock r c)
    (hcount : r + c + 2 = S.count) :
    Function.Surjective (S.middleMatrix hf r c htwo hc hthree).mulVec := by  -- SphereTopology.lean:14300

theorem MorseCancel.exists_middle_index_blocks {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0) :
    ∃ r c : ℕ,
      S.HasIndexTwoPrefix r ∧
        ∃ _ : r + c < S.count,
          S.HasIndexThreeBlock r c ∧
            r + c + 1 < S.count ∧
              ∀ i : Fin S.count,
                r + c < i.val →
                  4 ≤ Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates := by  -- SphereTopology.lean:14326

theorem AdaptedWindows.exists_ordered_middle_family {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (hdim : Module.finrank ℝ E = 6) (r n : ℕ) (hn : r + n < S.toSurgeryWindows.count)
    (hthree : S.toSurgeryWindows.HasIndexThreeBlock r n)
    (ε : Smale.ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ q, 0 < ε q) :
    let q := S.toSurgeryWindows.point ⟨r, by omega⟩
    ∃ T : AdaptedWindows E f,
      (∀ p, (T.data p).chart = (S.data p).chart) ∧
        (∀ p, (T.data p).radius < ε p) ∧
          (∀ p ∈ Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 p, T.field y = S.field y) ∧
            ∃ α : Fin n → (Smale.Hemisphere.Sphere 2) → (S.data q).UpperLevel,
              MorseCancel.IsNativeMiddleBasinFamily T hf (S.data q).upper_regular
                (MorseCancel.nativeMiddleBlockPoint S r n hn) α := by  -- SphereTopology.lean:14408

theorem AdaptedWindows.exists_canonical_middle_family {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) {n : ℕ}
    (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (α : Fin n → (Smale.Hemisphere.Sphere 2) → { y : M // f y = a })
    (hα : MorseCancel.IsNativeMiddleBasinFamily S hf ha p α) :
    ∃ γ : Fin n → (Smale.Hemisphere.Sphere 2) → { y : M // f y = a },
      MorseCancel.IsNativeMiddleBasinFamily S hf ha p γ ∧
        (∀ j, Set.range (γ j) = Set.range (α j)) ∧
          ∀ j x,
            ∃ t : ℝ,
              S.flow t (MorseCancel.nativeIndexThreeAttachingSphere S (p j) (hp j) x).val =
                (γ j x).val := by  -- Recognition.lean:2688

theorem MorseCancel.canonical_middle_matrix_surjective {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S T : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0) (r n : ℕ)
    (hr : nativeMorseCount E f 2 = r) (hn : nativeMorseCount E f 3 = n)
    (hrc : r + n < S.toSurgeryWindows.count)
    (hp : ∀ j, nativeMorseIndex E f (nativeMiddleBlockPoint S r n hrc j) = 3)
    (hbefore :
      ∀ j,
        nativeMiddleBaseCut S r n hrc <
          T.toSurgeryWindows.lower (nativeMiddleBlockPoint S r n hrc j))
    (B :
      (Fin r → ℤ) ≃ₗ[ℤ]
        SingularMayerVietoris.SingularHomology { y : M // f y ≤ nativeMiddleBaseCut S r n hrc } 2)
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = nativeMiddleBaseCut S r n hrc }))
    (horbit :
      ∀ j x,
        ∃ t : ℝ,
          T.flow t
              (nativeIndexThreeAttachingSphere T (nativeMiddleBlockPoint S r n hrc j) (hp j)
                  x).val =
            (γ j x).val) :
    Function.Surjective (canonicalMiddleMatrix B γ).mulVec :=
  classCoordinateMatrix_surjective B _
    (middle_section_classes_span S T hf hdim e horder hzero hone r n hr hn hrc hp hbefore γ
      horbit)

theorem AdaptedWindows.no_connection_above_canonical_cut {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p q : Smale.ManifoldMorse.criticalPoints E f)
    (hpq : f p < f q) (hq : MorseCancel.nativeMorseIndex E f q = 3) {a : ℝ} (hap : a < f p)
    (γ : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (horbit :
      ∀ x,
        ∃ t : ℝ,
          S.flow t (MorseCancel.nativeIndexThreeAttachingSphere S q hq x).val = (γ x).val) :
    ∀ x,
      ¬(Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 q.val) ∧
          Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)) := by  -- Recognition.lean:3365
```

`exists_canonical_middle_family` is G4's working interface (universal at-belt-cuts
unit-column property, holding for every γ on the ordered family) and
`canonical_middle_matrix_surjective` the matrix-level consequence
(`indexThreePresentation_matrix_surjective` is a local `let`-bound presentation used
inside the proof, not an extraction target — the lane's G6′ list).

**Row G5 (pivot and cancellation).** Verbatim:

```lean
theorem AdaptedWindows.exists_primitive_functional_unit {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] [PathConnectedSpace M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → MorseCancel.nativeMorseIndex E f x ≤ MorseCancel.nativeMorseIndex E f y)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hcut :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        MorseCancel.nativeMorseIndex E f z < 3 → f z < a)
    {r n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (hcomplete :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        MorseCancel.nativeMorseIndex E f z = 3 → ∃ j, p j = z)
    (hlower : ∀ j, a < S.toSurgeryWindows.lower (p j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hγ : MorseCancel.IsNativeMiddleBasinFamily S hf ha p (fun j => γ j))
    (hsurj : Function.Surjective (MorseCancel.canonicalMiddleMatrix B γ).mulVec)
    (L : SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2 →ₗ[ℤ] ℤ)
    (hL : Function.Surjective L) :
    ∃ ops : List (Fin n × Fin n × ℤ),
      (∀ op ∈ ops, op.1 ≠ op.2.1) ∧
        ∃ g : M → ℝ,
          ∃ hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g,
            Smale.ManifoldMorse.IsMorse E g ∧
              ∃ hcrit :
                Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f,
                (∀ x y : Smale.ManifoldMorse.criticalPoints E g,
                    g x < g y →
                      MorseCancel.nativeMorseIndex E g x ≤ MorseCancel.nativeMorseIndex E g y) ∧
                  (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                      MorseCancel.nativeMorseIndex E g z = MorseCancel.nativeMorseIndex E f z) ∧
                    (∀ d,
                        MorseCancel.nativeMorseCount E g d = MorseCancel.nativeMorseCount E f d) ∧
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
                                            MorseCancel.nativeMorseIndex E g z = 3 →
                                              ∃ j, p' j = z) ∧
                                          (∀ j, a < T.toSurgeryWindows.lower (p' j)) ∧
                                            ∃ Γ :
                                              Fin n →
                                                C((Smale.Hemisphere.Sphere 2),
                                                  { y : M // g y = a }),
                                              MorseCancel.IsNativeMiddleBasinFamily T hg hga p'
                                                  (fun j => Γ j) ∧
                                                (∀ j,
                                                    (∀ op ∈ ops, op.2.1 ≠ j) →
                                                      Γ j =
                                                        MorseCancel.equalCutSection hlevel
                                                          (γ j)) ∧
                                                  MorseCancel.canonicalMiddleMatrix (M := M) (f :=
                                                        g) (a := a) (r := r) (n := n) B' Γ =
                                                      MorseCancel.canonicalMiddleMatrix (M := M)
                                                          (f := f) (a := a) (r := r) (n := n) B
                                                          γ *
                                                        (ops.map
                                                            (fun op =>
                                                              Matrix.transvection op.1 op.2.1
                                                                op.2.2)).prod ∧
                                                    Function.Surjective
                                                        (MorseCancel.canonicalMiddleMatrix B'
                                                            Γ).mulVec ∧
                                                      (∃ i : Fin n,
                                                          L
                                                                ((MorseCancel.equalCutHomologyEquiv
                                                                      hsub).symm
                                                                  (MorseCancel.middleSectionClass
                                                                    (Γ i))) =
                                                              1 ∨
                                                            L
                                                                ((MorseCancel.equalCutHomologyEquiv
                                                                      hsub).symm
                                                                  (MorseCancel.middleSectionClass
                                                                    (Γ i))) =
                                                              -1) ∧
                                                        ∀ z : M,
                                                          f z ≤ a →
                                                            (∀ x,
                                                                Filter.Tendsto
                                                                    (fun t => T.flow t x)
                                                                    Filter.atBot (𝓝 z) ↔
                                                                  Filter.Tendsto
                                                                    (fun t => S.flow t x)
                                                                    Filter.atBot (𝓝 z)) ∧
                                                              (∀ x,
                                                                  Filter.Tendsto
                                                                      (fun t => S.flow t x)
                                                                      Filter.atBot (𝓝 z) →
                                                                    Set.range
                                                                        (fun t => T.flow t x) =
                                                                      Set.range
                                                                        (fun t => S.flow t x)) ∧
                                                                ∀ v,
                                                                  Filter.Tendsto
                                                                      (fun t => T.flow t z)
                                                                      Filter.atTop (𝓝 v) ↔
                                                                    Filter.Tendsto
                                                                      (fun t => S.flow t z)
                                                                      Filter.atTop (𝓝 v) := by  -- Recognition.lean:7365

theorem AdaptedWindows.exists_first_middle_pivot {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} [PreconnectedSpace M]
    [Nonempty M] (S₀ : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → MorseCancel.nativeMorseIndex E f x ≤ MorseCancel.nativeMorseIndex E f y)
    {r n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (hcomplete :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        MorseCancel.nativeMorseIndex E f z = 3 → ∃ j, p j = z)
    (hlower : ∀ j, a < S₀.toSurgeryWindows.lower (p j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hγ : MorseCancel.IsNativeMiddleBasinFamily S₀ hf ha p (fun j => γ j))
    (hsurj : Function.Surjective (MorseCancel.canonicalMiddleMatrix B γ).mulVec) (q : Fin n) :
    ∃ g : M → ℝ,
      ∃ hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g,
        Smale.ManifoldMorse.IsMorse E g ∧
          ∃ hcrit :
            Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f,
            (∀ x y : Smale.ManifoldMorse.criticalPoints E g,
                g x < g y →
                  MorseCancel.nativeMorseIndex E g x ≤ MorseCancel.nativeMorseIndex E g y) ∧
              (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                  MorseCancel.nativeMorseIndex E g z = MorseCancel.nativeMorseIndex E f z) ∧
                (∀ k, MorseCancel.nativeMorseCount E g k = MorseCancel.nativeMorseCount E f k) ∧
                  (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                      (∀ j, z ≠ (p j).val) → g z = f z) ∧
                    (∀ j, j ≠ q → g (p q) < g (p j)) ∧
                      ∃ hsub : ∀ y, g y ≤ a ↔ f y ≤ a,
                        ∃ hlevel : ∀ y, g y = a ↔ f y = a,
                          ∃ hga : ∀ y, g y = a → y ∉ Smale.ManifoldMorse.criticalPoints E g,
                            ∃ T : AdaptedWindows E g,
                              T.field = S₀.field ∧
                                T.flow = S₀.flow ∧
                                  (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) ∧
                                    let p' : Fin n → Smale.ManifoldMorse.criticalPoints E g :=
                                      fun j => ⟨(p j).val, hcrit.symm ▸ (p j).property⟩
                                    let B' := B.trans (MorseCancel.equalCutHomologyEquiv hsub)
                                    let γ' := fun j => MorseCancel.equalCutSection hlevel (γ j)
                                    (∀ j, MorseCancel.nativeMorseIndex E g (p' j) = 3) ∧
                                      (∀ j, a < T.toSurgeryWindows.lower (p' j)) ∧
                                        MorseCancel.IsNativeMiddleBasinFamily T hg hga p'
                                            (fun j => γ' j) ∧
                                          (∀ j x, (γ' j x).val = (γ j x).val) ∧
                                            MorseCancel.canonicalMiddleMatrix B' γ' =
                                                MorseCancel.canonicalMiddleMatrix B γ ∧
                                              Function.Surjective
                                                (MorseCancel.canonicalMiddleMatrix B'
                                                    γ').mulVec := by  -- Recognition.lean:3847

theorem MorseCancel.exists_native_belt_cut_family {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S T : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0) (r n : ℕ)
    (hr : nativeMorseCount E f 2 = r) (hn : nativeMorseCount E f 3 = n) (hrpos : 0 < r)
    (hrc : r + n < S.toSurgeryWindows.count)
    (hradii : ∀ z, (T.data z).radius < (S.data z).radius) :
    let q := S.toSurgeryWindows.point ⟨r, by omega⟩
    let a := nativeMiddleBaseCut S r n hrc
    let p := nativeMiddleBlockPoint S r n hrc
    ∀ (_ : ∀ j, a < T.toSurgeryWindows.lower (p j))
      (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
      (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a })),
      IsNativeMiddleBasinFamily T hf (S.data q).upper_regular p (fun j => γ j) →
        Function.Surjective (canonicalMiddleMatrix B γ).mulVec →
          ∃ hindex : Module.finrank ℝ (T.data q).chart.NegativeCoordinates = 2,
            Function.Surjective ((T.data q).indexTwoCollapseCoordinate hf.continuous hindex) ∧
              (∀ δ : C(Smale.Hemisphere.Sphere 1, (T.data q).LowerLevel),
                  ∃ z, δ.Homotopic (ContinuousMap.const _ z)) ∧
                (∀ z : Smale.ManifoldMorse.criticalPoints E f,
                    nativeMorseIndex E f z < 3 → f z < T.toSurgeryWindows.upper q) ∧
                  (∀ z : Smale.ManifoldMorse.criticalPoints E f,
                      nativeMorseIndex E f z = 3 → ∃ j, p j = z) ∧
                    (∀ j, T.toSurgeryWindows.upper q < T.toSurgeryWindows.lower (p j)) ∧
                      ∃ β : Fin n → C((Smale.Hemisphere.Sphere 2), (T.data q).UpperLevel),
                        IsNativeMiddleBasinFamily T hf (T.data q).upper_regular p (fun j => β j) ∧
                          (∀ j x, ∃ t : ℝ, T.flow t (γ j x).val = (β j x).val) ∧
                            ∃ B' :
                              (Fin r → ℤ) ≃ₗ[ℤ]
                                SingularMayerVietoris.SingularHomology
                                  { y : M // f y ≤ T.toSurgeryWindows.upper q } 2,
                              canonicalMiddleMatrix B' β = canonicalMiddleMatrix B γ ∧
                                Function.Surjective (canonicalMiddleMatrix B' β).mulVec := by  -- Recognition.lean:8331

theorem MorseCancel.cancel_from_preserved_unit_belt_cut {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f g : M → ℝ} (S : AdaptedWindows E f)
    (T : AdaptedWindows E g) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) (hmg : Smale.ManifoldMorse.IsMorse E g)
    (hdim : Module.finrank ℝ E = 6) (p : Smale.ManifoldMorse.criticalPoints E f)
    (hindex : Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2)
    (hnull :
      ∀ δ : C(Smale.Hemisphere.Sphere 1, (S.data p).LowerLevel),
        ∃ z, δ.Homotopic (ContinuousMap.const _ z))
    (hpcg : p.val ∈ Smale.ManifoldMorse.criticalPoints E g) (hpg : nativeMorseIndex E g p = 2)
    (q : Smale.ManifoldMorse.criticalPoints E g) (hq : nativeMorseIndex E g q = 3)
    (hconsecutive : ∀ z : Smale.ManifoldMorse.criticalPoints E g, ¬(g p < g z ∧ g z < g q))
    (hpc : g p < (f p + (S.data p).radius ^ 2)) (hcq : (f p + (S.data p).radius ^ 2) < g q)
    (hsub : ∀ y, g y ≤ (f p + (S.data p).radius ^ 2) ↔ f y ≤ (f p + (S.data p).radius ^ 2))
    (hlevel : ∀ y, g y = (f p + (S.data p).radius ^ 2) ↔ f y = (f p + (S.data p).radius ^ 2))
    (hga : ∀ y, g y = (f p + (S.data p).radius ^ 2) → y ∉ Smale.ManifoldMorse.criticalPoints E g)
    (hforward :
      ∀ y : (S.data p).UpperLevel,
        Filter.Tendsto (fun t => T.flow t y.val) Filter.atTop (𝓝 p.val) ↔
          Filter.Tendsto (fun t => S.flow t y.val) Filter.atTop (𝓝 p.val))
    (γ : C((Smale.Hemisphere.Sphere 2), { y : M // g y = (f p + (S.data p).radius ^ 2) })) :
    letI := Smale.RegularLevel.chartedSpace hg hga
    ∀ (_ : ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ γ) (_ : Function.Injective γ)
      (_ : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) γ x)),
      (∀ y, y ∈ Set.range γ ↔ Filter.Tendsto (fun t => T.flow t y.val) Filter.atBot (𝓝 q.val)) →
        ((S.data p).indexTwoCollapseCoordinate hf.continuous hindex
                ((equalCutHomologyEquiv hsub).symm (middleSectionClass γ))).natAbs =
            1 →
          ∃ v : M → ℝ,
            ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v ∧
              Smale.ManifoldMorse.IsMorse E v ∧
                (Smale.ManifoldMorse.criticalPoints E v).ncard + 2 =
                    (Smale.ManifoldMorse.criticalPoints E g).ncard ∧
                  (∀ z,
                      z ∈ Smale.ManifoldMorse.criticalPoints E v ↔
                        z ∈ Smale.ManifoldMorse.criticalPoints E g ∧ z ≠ p.val ∧ z ≠ q.val) ∧
                    ∀ z,
                      g z ∉
                          Set.Ioo (T.toSurgeryWindows.lower ⟨p.val, hpcg⟩)
                            (T.toSurgeryWindows.upper q) →
                        v =ᶠ[𝓝 z] g := by  -- Recognition.lean:8680

theorem MorseCancel.cancel_from_complete_middle_family {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] [PathConnectedSpace M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (p : Smale.ManifoldMorse.criticalPoints E f)
    (hindex : Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2)
    (hnull :
      ∀ δ : C(Smale.Hemisphere.Sphere 1, (S.data p).LowerLevel),
        ∃ z, δ.Homotopic (ContinuousMap.const _ z))
    (hprimitive :
      Function.Surjective ((S.data p).indexTwoCollapseCoordinate hf.continuous hindex))
    (hcut :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E f z < 3 → f z < f p + (S.data p).radius ^ 2)
    {r n : ℕ} (labels : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hlabels : ∀ j, nativeMorseIndex E f (labels j) = 3)
    (hcomplete :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E f z = 3 → ∃ j, labels j = z)
    (hlower : ∀ j, f p + (S.data p).radius ^ 2 < S.toSurgeryWindows.lower (labels j))
    (B :
      (Fin r → ℤ) ≃ₗ[ℤ]
        SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + (S.data p).radius ^ 2 } 2)
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), (S.data p).UpperLevel))
    (hγ : IsNativeMiddleBasinFamily S hf (S.data p).upper_regular labels (fun j => γ j))
    (hsurj : Function.Surjective (canonicalMiddleMatrix B γ).mulVec) :
    ∃ v : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v ∧
        Smale.ManifoldMorse.IsMorse E v ∧
          Set.InjOn v (Smale.ManifoldMorse.criticalPoints E v) ∧
            (Smale.ManifoldMorse.criticalPoints E v).ncard + 2 =
              (Smale.ManifoldMorse.criticalPoints E f).ncard := by  -- Recognition.lean:8834

theorem MorseCancel.minimal_ordered_index_two_count_zero {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] [PathConnectedSpace M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0)
    (hminimal :
      ∀ v : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v →
          Smale.ManifoldMorse.IsMorse E v →
            Set.InjOn v (Smale.ManifoldMorse.criticalPoints E v) →
              (Smale.ManifoldMorse.criticalPoints E f).ncard ≤
                (Smale.ManifoldMorse.criticalPoints E v).ncard) :
    nativeMorseCount E f 2 = 0 := by  -- Recognition.lean:8957

theorem MorseCancel.minimal_ordered_index_four_count_zero {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] [PathConnectedSpace M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (hsix : nativeMorseCount E f 6 = 1) (hfive : nativeMorseCount E f 5 = 0)
    (hminimal :
      ∀ v : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v →
          Smale.ManifoldMorse.IsMorse E v →
            Set.InjOn v (Smale.ManifoldMorse.criticalPoints E v) →
              (Smale.ManifoldMorse.criticalPoints E f).ncard ≤
                (Smale.ManifoldMorse.criticalPoints E v).ncard) :
    nativeMorseCount E f 4 = 0 := by  -- Recognition.lean:9017

theorem MorseCancel.ordered_no_middle_indices_count_two {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (hzero : nativeMorseCount E f 0 = 1) (hsix : nativeMorseCount E f 6 = 1)
    (hone : nativeMorseCount E f 1 = 0) (htwo : nativeMorseCount E f 2 = 0)
    (hfour : nativeMorseCount E f 4 = 0) (hfive : nativeMorseCount E f 5 = 0) :
    nativeMorseCount E f 3 = 0 ∧ S.count = 2 := by  -- Recognition.lean:9243
```

`exists_primitive_functional_unit` is the surjectivity→integral-primitive step (F11's
slide machinery consumed), `exists_first_middle_pivot` the position-zero pivot, the
`exists_native_belt_cut_family`/`cancel_from_preserved_unit_belt_cut` pair the
transport-to-lower-level cancellation engine (§5), and
`cancel_from_complete_middle_family` the complete-block blocker. The three count
theorems are the elimination conclusions in source order: index 2, index 4 (dual
function −f), then index 3 via H₃ = 0 with the middle chain groups already zeroed —
ordered_no_middle_indices_count_two's `3 < k` hypothesis excludes index 3 on purpose.


**Row G6 (two critical points; Reeb).** Verbatim:

```lean
theorem MorseCancel.critical_pair_of_surgery_count_two {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hcount : S.count = 2) :
    ∃ p q : M, f p < f q ∧ Smale.ManifoldMorse.criticalPoints E f = { p, q }
                                                -- Recognition.lean:9370 (map §1(15d))

theorem Smale.ManifoldMorse.nonempty_homeomorphSphere_of_two_critical_points {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f) {p q : M} (hpq : f p < f q)
    (hcrit : criticalPoints E f = { p, q }) :
    Nonempty (M ≃ₜ Smale.Hemisphere.Sphere (Module.finrank ℝ E))
                                                -- Recognition.lean:9329 (map §1(4); Reeb —
                                                -- lane D1 consumer surface, included here as
                                                -- the G6 endpoint's direct dependency)

theorem MorseCancel.exists_two_critical_point_morse_of_homotopySixSphere (E : Type) (M : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere) :
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        Smale.ManifoldMorse.IsMorse E f ∧
          ∃ p q : M, f p < f q ∧ Smale.ManifoldMorse.criticalPoints E f = { p, q }
                                                -- Recognition.lean:9398 (map §1(3))

theorem MorseCancel.nonempty_homeomorph_of_homotopySixSphere (E : Type) (M : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere) : Nonempty (M ≃ₜ SixSphere)
                                                -- Recognition.lean:9416 (map §1(2))
                                                -- NOTE: no [SecondCountableTopology M] —
                                                -- the inner chain never carries it.

theorem Smale.homeomorphic_sixSphere_of_homotopySixSphere (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (M : Type) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    (hdim : Module.finrank ℝ E = 6) (hM : M ≃ₕ Smale.SixSphere) :
    Nonempty (M ≃ₜ Smale.SixSphere)             -- Recognition.lean:9427 (map §1(1));
                                                -- body: nonempty_homeomorph_of_homotopySixSphere
```

Two-Disk decomposition deps for Reeb (lane D1 structures, outside this lane): `Smale.
twoDiskDecompositionOfSublevels` (Rec 9274), `Smale.homeomorphSphereOfSublevelDisks`
(Rec 9324), `Smale.TwoDiskDecomposition` (SphereTopology 5199), `Smale.SublevelDisk`
(SphereTopology 5283).

**Ledger notes.**

* *Namespaces.* All decls sit in `namespace Mathoverflow1973`; the dotted prefixes
  (`MorseCancel.`, `AdaptedWindows.`, `Smale.`, `Smale.ManifoldMorse.SurgeryWindows.`)
  are the actual namespaces — no bare name in this table resolves without one.
* *`Type` vs `Type*`.* Preserve the elaborated universes during extraction. The chain mixes
  `(E : Type) (M : Type)` (the Recognition-side homotopy-sphere chain) with polymorphic
  declarations such as `exists_minimal_excellent_morse_system` and Reeb. The current
  `SingularMayerVietoris.SingularHomology` takes spaces in `Type`; changing all binders to
  `Type*` is not a representation-only rename and requires a separate typed design/probe.
* *Sphere spellings.* Every `M ≃ₕ Smale.SixSphere` / `M ≃ₜ SixSphere` /
  `Smale.Hemisphere.Sphere n` occurrence consolidates to the `Metric.sphere` spelling where
  defeq permits; `Hemisphere.Sphere 2`-typed attaching maps (the `γ` binders) are part of the
  native family interface and stay as-is — the consolidation applies to the *theorem*
  statements' sphere, not to internal attaching-sphere types.
* *Instances.* `[SecondCountableTopology M]` appears only on the headline wrapper; the Lib
  theorem drops it (see §7 and open item 2). All other instance sets move verbatim.
* *Universe/instance gotcha recorded by the map:* `(4)`'s `Nonempty (M ≃ₜ Hemisphere.Sphere
  (finrank ℝ E))` is what the `change … ; rw [hdim]` in `(2)` resolves — the Lib file must
  keep that definitional chain intact when consolidating spellings.

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
5. **Review.** Stage-2 independent review of §§1–7: astra's NO-GO review is in-tree at
   `Lib/docs/G-stage2-astra-review.md` (Muse's earlier pass at `G-stage2-review.md` is
   self-review and does not satisfy the independence condition). Remaining obligations
   per that review: expand the unique-minimum reduction, the relative handle-trade
   placement, and the codimension-two Whitney complement argument; then re-review.
6. **GLM-lane overlap discovered after landing A–D2/H/I:** lane E2's source ranges were largely
   swept into GLM's `Lib/Geometry/Manifold/Morse/SurgeryWindows.lean` (17,556 lines; the D2
   baseline blob contains e.g. `exists_compact_embedding_of_immersion` at its line 12352 and
   `exists_ambient_transverse_diffeomorph` at 17495). Lane E2's Lean work is therefore a
   Lib-internal *split* of that file (plus the generalization G-E2), not a Hopf→Lib move;
   lane F's sources remain in `Hopf/` (verified: `TubularBigon`, `primitive_row_*` unmoved).
   This affects E2/F placement timing, not this lane's content.
