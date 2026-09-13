# Lane G — textbook, decomposition, placement, and typed ledger

**Independent Stage-2 review at `699d1a4` (astra): NO-GO as submitted.**
The uncommitted narrative corrections below are proposed repairs, not a frozen proof.
The historical coordinates and compressed signatures in the tables below are not a
certified Axis-5 packet; use the complete live-coordinate census and numbered findings
in `~/s6-notes/G-stage2-astra-review.md`. In particular, G2 has inaccurate signatures,
G2/G3 are not in strict dependency order, and the codimension-two Whitney input still
needs an explicit textbook justification. Muse's self-review and legacy receipt do not
constitute an independent Stage-2 GO or production-module certification.

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

**The trade.** Suppose an index-1 critical point $q$ exists. Its attaching sphere is $S^0$.
The relevant regular cut is **after all original index-2 points and before index-3 points**,
not below the index-2 handles: 2-handles can kill fundamental-group generators, so a level
below them need not be simply connected. Place the auxiliary cancelling $(2,3)$-pair above
this cut. The handle-trading argument transports a circle meeting the chosen 1-handle belt
once to the cut, identifies it there with the born 2-handle's attaching circle by isotopy,
and transports the placement back to perform the $(1,2)$ cancellation. In the source the
cut has indices at most 2 below and at least 3 above; the embedded-disk, level-basin and
isotopy arguments, together with the unique minimum, are substantive inputs, not a local
consequence of the $S^0$ attaching sphere. Net effect: one fewer index-1 point, one more
index-3 point, total critical count unchanged. The full relative placement and preservation
argument remains to be expanded before this text is frozen.

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
in the 5-dimensional regular level. **The Whitney step needs more than ambient simple
connectivity.** In Milnor's Theorem 6.6, taking the moving sheet to have dimension 2 and
the fixed sheet dimension 3 requires injectivity of the complement map on fundamental
groups, in addition to the contractible Whitney loop and orientation hypotheses. The
handle-specific proof must supply this condition (or the precise stronger relative
nullhomotopy input of lane F), preserving the other attaching data. The source supplies
lower-level circle nullhomotopies through its native belt-cut construction; the textbook
transport from that lower level to the required belt complement remains to be written
explicitly. This is an open Stage-2 obligation, not a consequence of dimensions alone.
Once this input is justified, the unit gives one transverse geometric intersection and
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

These rows are thematic groups, not a strict dependency order: G2's
`exists_minimal_ordered_morse_system_without_outer_indices` consumes G3's
`outer_index_minimal_outer_counts_zero`. Split G2 into the preliminary minimal-system
construction and the post-trade conclusion, with G3 between them. The placement table
also puts preliminary G2 and downstream G5 counts in the same `MinimalSystem.lean`;
the file-level dependency graph must be resolved before that grouping becomes a commit
boundary. G4–G5 use `Morse/MiddleBlocks.lean`; G6 uses `PoincareConjecture/Smale.lean`.

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

**Rows G1–G6 — the typed ledger.** Imported from `~/s6-notes/kimi-notes/G-map.md` §1 items
(1)–(15), re-grounded to the current source layout (all coordinates re-verified on `1cc1784`;
the map's Recognition 11214–11317 block and SphereTopology 11803–13393 block are pre-move
coordinates — the current positions are below). Signatures are verbatim unless marked
"compressed" — compressed signatures elide repeated binder blocks with `…`; the verbatim
form is at the cited source coordinate.

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

**Row G2 (minimal ordered systems).** The chain is a pure existence/minimality tower —
no handle geometry, no `e : M ≃ₕ S⁶` except where marked:

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
                      (Smale.ManifoldMorse.criticalPoints E g).ncard
                          -- SphereTopology.lean:6290 (VERBATIM, astra-corrected: NO
                          -- [PathConnectedSpace]/[Nonempty] instances; the comparison
                          -- class is every smooth Morse InjOn g, not ordered systems)

theorem MorseCancel.exists_index_ordered_morse_system_preserving_critical_points {E M : Type*}
    … : ∃ g : M → ℝ, … (same critical points, index-ordered values)
                          -- SphereTopology.lean:6943 (compressed)

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
    nativeMorseCount E f 0 = 1 ∧ nativeMorseCount E f (Module.finrank ℝ E) = 1
                          -- SphereTopology.lean:7014 (VERBATIM, astra-corrected: NO hdim,
                          -- NO homotopy equiv; conclusion is general-dimension)

theorem MorseCancel.exists_outer_index_minimal_ordered_morse_system (E : Type) (M : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] :
    ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ Smale.ManifoldMorse.IsMorse E f ∧
          ∃ _ : AdaptedWindows E f,
            (∀ p q : Smale.ManifoldMorse.criticalPoints E f,
                f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q) ∧
              nativeMorseCount E f 0 = 1 ∧
                nativeMorseCount E f (Module.finrank ℝ E) = 1 ∧
                  (∀ g …, (criticalPoints E f).ncard ≤ (criticalPoints E g).ncard) ∧
                    ∀ g …, (criticalPoints E g).ncard = (criticalPoints E f).ncard →
                              nativeMorseCount E f 1 + nativeMorseCount E f 5 ≤
                                nativeMorseCount E g 1 + nativeMorseCount E g 5
                          -- SphereTopology.lean:10005; binder elisions as in map §1(6).
                          -- NOTE: no hdim/e hypothesis — the 1+5 cost is stated at general
                          -- finrank; the literal `1`/`5` indices pin it to n=6 anyway.

theorem MorseCancel.exists_minimal_ordered_morse_system_without_outer_indices (E : Type)
    (M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    [CompactSpace M] [PathConnectedSpace M] (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6) :
    ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ Smale.ManifoldMorse.IsMorse E f ∧
          ∃ _ : AdaptedWindows E f,
            (∀ p q …, f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q) ∧
              nativeMorseCount E f 0 = 1 ∧ nativeMorseCount E f 6 = 1 ∧
                nativeMorseCount E f 1 = 0 ∧ nativeMorseCount E f 5 = 0 ∧
                  ∀ g : M → ℝ, … (minimality)
                          -- SphereTopology.lean:10195 (map §1(5))
```

**Row G3 (handle trade, Milnor Thm. 8.1 at n=6).** Birth → trade → count contradiction:

```lean
theorem MorseCancel.exists_excellent_indexed_morse_birth {E M : Type*} … (k : ℕ)
    (hband : ∀ y, f y ∈ Set.Ioo a u → y ∉ criticalPoints E f) … :
    ∃ g : M → ℝ, … (excellent cancelling (k, k+1)-pair born in the band)
                          -- SphereTopology.lean:8637 (compressed)

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
    (hhigh : ∀ z …, a ≤ f z → 3 ≤ nativeMorseIndex E f z)
    (hlow : ∀ z …, f z ≤ a → nativeMorseIndex E f z ≤ 3)
    (m q r : Smale.ManifoldMorse.criticalPoints E g) (hm : nativeMorseIndex E g m = 0)
    (hq : nativeMorseIndex E g q = 1) (hr : nativeMorseIndex E g r = 2)
    (hminimum : ∀ z …, nativeMorseIndex E g z = 0 → z = m)
    (hqa : g q < a) (har : a < g r)
    (hgap : ∀ z …, g z < g r → g z < a)
    (hnewlow : ∀ z …, g z ≤ a → nativeMorseIndex E g z ≤ 2) :
    ∃ h : M → ℝ, ContMDiff … ∞ h ∧ IsMorse E h ∧ Set.InjOn h … ∧
            (criticalPoints E h).ncard + 2 = (criticalPoints E g).ncard ∧
              (∀ w, w ∈ criticalPoints E h ↔ w ∈ criticalPoints E g ∧ w ≠ q.val ∧ w ≠ r.val) ∧
                ∀ w ∈ criticalPoints E h, nativeMorseIndex E h w = nativeMorseIndex E g w
                          -- SphereTopology.lean:9601 (map §1(12), verbatim modulo binder …)

theorem MorseCancel.exists_one_to_three_handle_trade {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6) (m q : Smale.ManifoldMorse.criticalPoints E f)
    (hm0 : nativeMorseIndex E f m = 0) (hq1 : nativeMorseIndex E f q = 1)
    (hminimum : ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E f z = 0 → z = m)
    {a l u : ℝ} (hreg : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hhigh : ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        a ≤ f z → 3 ≤ nativeMorseIndex E f z)
    (hlow : ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        f z ≤ a → nativeMorseIndex E f z ≤ 2)
    (hqa : f q < a) (hal : a < l)
    (hband : ∀ y, f y ∈ Set.Ioo a u → y ∉ Smale.ManifoldMorse.criticalPoints E f) {x : M}
    (hx : f x ∈ Set.Ioo l u) :
    ∃ h : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h ∧
        Smale.ManifoldMorse.IsMorse E h ∧
          Set.InjOn h (Smale.ManifoldMorse.criticalPoints E h) ∧
            (Smale.ManifoldMorse.criticalPoints E h).ncard =
                (Smale.ManifoldMorse.criticalPoints E f).ncard ∧
              nativeMorseCount E h 1 + 1 = nativeMorseCount E f 1 ∧
                nativeMorseCount E h 3 = nativeMorseCount E f 3 + 1 ∧
                  ∀ j, j ≠ 1 → j ≠ 3 → nativeMorseCount E h j = nativeMorseCount E f j
                          -- SphereTopology.lean:9796 (VERBATIM, astra-corrected: hminimum
                          -- and the cut hypotheses are material; output is excellent but
                          -- NOT promised ordered)

theorem MorseCancel.exists_one_to_three_handle_trade_at_cut {E M : Type*} …
                          -- SphereTopology.lean:9884 (compressed; cut-fixed variant)

theorem MorseCancel.exists_one_to_three_handle_trade_of_ordered_indices {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    [PathConnectedSpace M] (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6)
    (horder : ∀ p q …, f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (m q : Smale.ManifoldMorse.criticalPoints E f) (hm0 : nativeMorseIndex E f m = 0)
    (hq1 : nativeMorseIndex E f q = 1)
    (hminimum : ∀ z …, nativeMorseIndex E f z = 0 → z = m) :
    ∃ h : M → ℝ, ContMDiff … ∞ h ∧ Smale.ManifoldMorse.IsMorse E h ∧
            Set.InjOn h (Smale.ManifoldMorse.criticalPoints E h) ∧
            (Smale.ManifoldMorse.criticalPoints E h).ncard =
              (Smale.ManifoldMorse.criticalPoints E f).ncard ∧
              nativeMorseCount E h 1 + 1 = nativeMorseCount E f 1 ∧
                nativeMorseCount E h 3 = nativeMorseCount E f 3 + 1 ∧
                  ∀ j, j ≠ 1 → j ≠ 3 → nativeMorseCount E h j = nativeMorseCount E f j
                          -- SphereTopology.lean:9977 (map §1(10))

theorem MorseCancel.outer_index_minimal_index_one_count_zero {E M : Type} …
    (S : AdaptedWindows E f) (hf …) (hm : IsMorse E f) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6) (horder …) (hzero : nativeMorseCount E f 0 = 1)
    (hsecondary : ∀ g …, … nativeMorseCount E f 1 + nativeMorseCount E f 5 ≤ …) :
    nativeMorseCount E f 1 = 0                     -- SphereTopology.lean:10065 (map §1(8))

theorem MorseCancel.outer_index_minimality_neg {E M : Type} … (hf …) (hm : IsMorse E f)
    (hdim : Module.finrank ℝ E = 6) (hsecondary …) :
    ∀ g : M → ℝ, … →
      nativeMorseCount E (fun x => -f x) 1 + nativeMorseCount E (fun x => -f x) 5 ≤
        nativeMorseCount E g 1 + nativeMorseCount E g 5
                          -- SphereTopology.lean:10113 (map §1(9))

theorem MorseCancel.outer_index_minimal_outer_counts_zero {E M : Type} …
    (S : AdaptedWindows E f) (hf …) (hm : IsMorse E f) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6) (horder …) (hzero : nativeMorseCount E f 0 = 1)
    (hsix : nativeMorseCount E f 6 = 1) (hsecondary …) :
    nativeMorseCount E f 1 = 0 ∧ nativeMorseCount E f 5 = 0
                          -- SphereTopology.lean:10146 (map §1(7))
```

**Row G4 (middle blocks and the matrix).**

```lean
theorem Smale.ManifoldMorse.SurgeryWindows.middleMatrix_surjective_of_homotopySphere
    {E M : Type} … (hdim : Module.finrank ℝ E = 6) (hM : M ≃ₕ Smale.SixSphere) (r c : ℕ)
    (htwo : …) (hc : …) (hthree : …) :
    Function.Surjective (S.middleMatrix …).mulVec   -- SphereTopology.lean:14278 (compressed)

theorem Smale.ManifoldMorse.SurgeryWindows.middleMatrix_surjective_of_complete_blocks
    {E M : Type} …                                  -- SphereTopology.lean:14300 (compressed)

theorem MorseCancel.exists_middle_index_blocks {E M : Type} …
                          -- SphereTopology.lean:14326 (compressed)

theorem AdaptedWindows.exists_ordered_middle_family {E M : Type} …
                          -- SphereTopology.lean:14408 (compressed)

theorem AdaptedWindows.exists_canonical_middle_family {E M : Type} [NormedAddCommGroup E]
    …                                                 -- Recognition.lean:2688 (compressed)

theorem MorseCancel.canonical_middle_matrix_surjective {E M : Type} [NormedAddCommGroup E]
    …                                                 -- Recognition.lean:3365 (compressed)
```

`canonicalMiddleMatrix` itself (`def`, Recognition.lean:3359) is pure algebra over
`IsNativeMiddleBasinFamily`/`middleSectionClass` — it is an F10-adjacent input, already
in-scope for the lane-F boundary, and G4 consumes it.

**Row G5 (pivot and cancellation).**

```lean
theorem AdaptedWindows.exists_primitive_functional_unit {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] [PathConnectedSpace M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder : ∀ x y …, f x < f y → MorseCancel.nativeMorseIndex E f x ≤ … y)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hcut : ∀ z …, MorseCancel.nativeMorseIndex E f z < 3 → f z < a)
    {r n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (hcomplete : ∀ z …, nativeMorseIndex E f z = 3 → ∃ j, p j = z)
    (hlower : ∀ j, a < S.toSurgeryWindows.lower (p j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hγ : MorseCancel.IsNativeMiddleBasinFamily S hf ha p (fun j => γ j))
    (hsurj : Function.Surjective (MorseCancel.canonicalMiddleMatrix B γ).mulVec)
    (L : SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2 →ₗ[ℤ] ℤ)
    (hL : Function.Surjective L) :
    ∃ ops : List (Fin n × Fin n × ℤ), (∀ op ∈ ops, op.1 ≠ op.2.1) ∧ ∃ g : M → ℝ, …
                          -- Recognition.lean:7365 (map §1(14); conclusion: handle slides
                          -- produce g, windows T, family Γ, and a pivot
                          -- ∃ i, L ((equalCutHomologyEquiv hsub).symm
                          --   (MorseCancel.middleSectionClass (Γ i))) = 1 ∨ … = -1)

theorem AdaptedWindows.exists_first_middle_pivot {E M : Type} …  -- Recognition.lean:3847
theorem MorseCancel.exists_native_belt_cut_family {E M : Type} …  -- Recognition.lean:8331
theorem MorseCancel.cancel_from_preserved_unit_belt_cut {E M : Type} …  -- Recognition.lean:8680

theorem MorseCancel.cancel_from_complete_middle_family {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] [PathConnectedSpace M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder : ∀ x y …, f x < f y → nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (p : Smale.ManifoldMorse.criticalPoints E f)
    (hindex : Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2)
    (hnull : ∀ δ : C(Smale.Hemisphere.Sphere 1, (S.data p).LowerLevel),
        ∃ z, δ.Homotopic (ContinuousMap.const _ z))
    (hprimitive : Function.Surjective ((S.data p).indexTwoCollapseCoordinate hf.continuous
        hindex))
    (hcut : ∀ z …, nativeMorseIndex E f z < 3 → f z < f p + (S.data p).radius ^ 2)
    {r n : ℕ} (labels : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hlabels : ∀ j, nativeMorseIndex E f (labels j) = 3)
    (hcomplete : ∀ z …, nativeMorseIndex E f z = 3 → ∃ j, labels j = z)
    (hlower : ∀ j, f p + (S.data p).radius ^ 2 < S.toSurgeryWindows.lower (labels j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ]
        SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + (S.data p).radius ^ 2 } 2)
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), (S.data p).UpperLevel))
    (hγ : IsNativeMiddleBasinFamily S hf (S.data p).upper_regular labels (fun j => γ j))
    (hsurj : Function.Surjective (canonicalMiddleMatrix B γ).mulVec) :
    ∃ v : M → ℝ, ContMDiff … ∞ v ∧ IsMorse E v ∧ Set.InjOn v (criticalPoints E v) ∧
            (Smale.ManifoldMorse.criticalPoints E v).ncard + 2 =
              (Smale.ManifoldMorse.criticalPoints E f).ncard
                          -- Recognition.lean:8834 (map §1(13); body: primitive unit →
                          -- first_middle_pivot → cancels the (2,3) pair)

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
    nativeMorseCount E f 2 = 0            -- Recognition.lean:8957 (VERBATIM,
                                          -- astra-corrected: [Nonempty M],
                                          -- [PathConnectedSpace M], S/hf and the exact
                                          -- comparison class are material inputs)

theorem MorseCancel.minimal_ordered_index_four_count_zero …
    (hsix : nativeMorseCount E f 6 = 1) (hfive : nativeMorseCount E f 5 = 0) (hminimal …) :
    nativeMorseCount E f 4 = 0            -- Recognition.lean:9017 (map §1(15b); −f duality)

theorem MorseCancel.ordered_no_middle_indices_count_two {E M : Type} …
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere) (horder …)
    (hzero : nativeMorseCount E f 0 = 1) (hsix : nativeMorseCount E f 6 = 1)
    (hone : nativeMorseCount E f 1 = 0) (htwo : nativeMorseCount E f 2 = 0)
    (hfour : nativeMorseCount E f 4 = 0) (hfive : nativeMorseCount E f 5 = 0) :
    nativeMorseCount E f 3 = 0 ∧ S.count = 2
                          -- Recognition.lean:9243 (map §1(15c); via
                          -- middle_blocks_complete_of_no_four_five + S.middle_counts_equal)
```

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
