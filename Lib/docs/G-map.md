# Lane G — Smale recognition theorem (Smale 1961 Thm A; h-cobordism Thm 9.1 realized as handle trade + pair cancellation)

**Status: historical scout map.** Recorded before the post-integration renames —
namespaces/coordinates below reflect the old tree (`MorseCancel.*`, `Smale.*`,
old file lines). For current names see `Lib/reports/RENAMES.md`; for live
signatures and coordinates see the `G.md` typed ledger.

All declarations live in `namespace Mathoverflow1973` (no sections); dotted prefixes (`MorseCancel.*`, `AdaptedWindows.*`, `Smale.*`, `Smale.ManifoldMorse.*`) act as namespaces. `≃ₕ` = `HomotopyEquiv`, `≃ₜ` = `Homeomorph`.

## 0. File spine (observed import lines)
- `Hopf/SingularHomology.lean:64` — `import Hopf.DifferentialTopology`
- `Hopf/SphereTopology.lean:64` — `import Hopf.SingularHomology`
- `Hopf/Recognition.lean:64` — `import Hopf.LCP.IntegralHomology` (transitively pulls SphereTopology)
- `Hopf/Final.lean` — `import Hopf.Recognition`
- Identical header pragmas in all five files: `set_option maxSynthPendingDepth 3`; `open Set Function Filter Manifold Topology`; `open scoped BigOperators … UpperHalfPlane`; `universe u v`; `noncomputable section`; SphereTopology/SingularHomology also `local infixr:80 " ≫ₚ " => Path.trans` (line 81).

## 1. Dependency chain (verbatim signatures, file:line)

### (1) Headline — Hopf/Recognition.lean:11312-11317
```lean
theorem Smale.homeomorphic_sixSphere_of_homotopySixSphere (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (M : Type) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    (hdim : Module.finrank ℝ E = 6) (hM : M ≃ₕ Smale.SixSphere) :
    Nonempty (M ≃ₜ Smale.SixSphere) :=
  MorseCancel.nonempty_homeomorph_of_homotopySixSphere E M hdim hM
```
Note: `NormedSpace`/`FiniteDimensional` only — **no** `InnerProductSpace ℝ E`.

### (2) Hopf/Recognition.lean:11301-11310
```lean
theorem MorseCancel.nonempty_homeomorph_of_homotopySixSphere (E : Type) (M : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere) : Nonempty (M ≃ₜ SixSphere) := by
  obtain ⟨f, hf, hm, p, q, hpq, hcrit⟩ :=
    exists_two_critical_point_morse_of_homotopySixSphere E M hdim e
  have hh := Smale.ManifoldMorse.nonempty_homeomorphSphere_of_two_critical_points hf hm hpq hcrit
  change Nonempty (M ≃ₜ Smale.Hemisphere.Sphere (Module.finrank ℝ E)) at hh
  rw [hdim] at hh
```

### (3) Hopf/Recognition.lean:11283-11298
```lean
theorem MorseCancel.exists_two_critical_point_morse_of_homotopySixSphere (E : Type) (M : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere) :
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        Smale.ManifoldMorse.IsMorse E f ∧
          ∃ p q : M, f p < f q ∧ Smale.ManifoldMorse.criticalPoints E f = { p, q } := by
  let _ := Smale.pathConnectedSpace_of_homotopySixSphere e
  obtain ⟨f, hf, hm, S, horder, hzero, hsix, hone, hfive, hminimal⟩ :=
    exists_minimal_ordered_morse_system_without_outer_indices E M e hdim
  have htwo := minimal_ordered_index_two_count_zero S hf hm hdim e horder hzero hone hminimal
  have hfour := minimal_ordered_index_four_count_zero S hf hm hdim e horder hsix hfive hminimal
  obtain ⟨-, hcount⟩ :=
    ordered_no_middle_indices_count_two S.toSurgeryWindows hf hdim e horder hzero hsix hone htwo
      hfour hfive
  exact ⟨f, hf, hm, critical_pair_of_surgery_count_two S.toSurgeryWindows hcount⟩
```

### (4) Reeb theorem — Hopf/Recognition.lean:11214-11219
```lean
theorem Smale.ManifoldMorse.nonempty_homeomorphSphere_of_two_critical_points {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f) {p q : M} (hpq : f p < f q)
    (hcrit : criticalPoints E f = { p, q }) :
    Nonempty (M ≃ₜ Smale.Hemisphere.Sphere (Module.finrank ℝ E))
```
Proved via `unique_extrema_of_two_critical_values`, `nonempty_signedMorseChart`, `*.nonempty_sublevelDisk_before_next_critical` (p below / q for `-f` above the mid-level), and:
- Recognition.lean:11209-11212 `def Smale.homeomorphSphereOfSublevelDisks {M : Type*} [TopologicalSpace M] [T2Space M] {n : ℕ} {f : M → ℝ} {a : ℝ} (L : SublevelDisk n f a) (R : SublevelDisk n (fun x => -f x) (-a)) : M ≃ₜ Hemisphere.Sphere n := (twoDiskDecompositionOfSublevels L R).homeomorphSphere`
- Recognition.lean:11159-11161 `def Smale.twoDiskDecompositionOfSublevels … : TwoDiskDecomposition n M`
- (`Smale.TwoDiskDecomposition` structure: SphereTopology.lean:8073; `Smale.SublevelDisk` structure: SphereTopology.lean:8157 — both outside assigned ranges.)

### (5) Minimal ordered system — Hopf/SphereTopology.lean:13361-13383
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
                      ∀ g : M → ℝ, … (minimality: (criticalPoints E f).ncard ≤ (criticalPoints E g).ncard)
```
Body (13385-13393): `exists_outer_index_minimal_ordered_morse_system E M` → `outer_index_minimal_outer_counts_zero S hf hm e hdim horder hzero hsix hsecondary`.

### (6) Outer-index-minimal system — SphereTopology.lean:13171-13197
```lean
theorem MorseCancel.exists_outer_index_minimal_ordered_morse_system (E : Type) (M : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] :
    ∃ f : M → ℝ, ContMDiff … ∞ f ∧ Smale.ManifoldMorse.IsMorse E f ∧
          ∃ _ : AdaptedWindows E f,
            (∀ p q …, f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q) ∧
              nativeMorseCount E f 0 = 1 ∧
                nativeMorseCount E f (Module.finrank ℝ E) = 1 ∧
                  (∀ g …, (criticalPoints E f).ncard ≤ (criticalPoints E g).ncard) ∧
                    ∀ g …, (criticalPoints E g).ncard = (criticalPoints E f).ncard →
                              nativeMorseCount E f 1 + nativeMorseCount E f 5 ≤
                                nativeMorseCount E g 1 + nativeMorseCount E g 5
```
(No `hdim`/`e` hypothesis here — the 1+5 cost is stated for general finrank.) Body: `exists_minimal_excellent_morse_system` (SphereTopology 9456, out of range) → `Nat.find` on the 1+5 cost → `nonempty_adaptedSurgeryWindows` → `exists_index_ordered_morse_system_preserving_critical_points` (SphereTopology 10109, out of range) → `minimal_excellent_morse_extreme_counts_one` (SphereTopology 10180, out of range).

### (7) Outer counts vanish — SphereTopology.lean:13312-13329
```lean
theorem MorseCancel.outer_index_minimal_outer_counts_zero {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6)
    (horder : ∀ p q …, f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1) (hsix : nativeMorseCount E f 6 = 1)
    (hsecondary : ∀ g …, (criticalPoints E g).ncard = (criticalPoints E f).ncard →
                nativeMorseCount E f 1 + nativeMorseCount E f 5 ≤ nativeMorseCount E g 1 + nativeMorseCount E g 5) :
    nativeMorseCount E f 1 = 0 ∧ nativeMorseCount E f 5 = 0
```
Body: `outer_index_minimal_index_one_count_zero` + negation duality (`nonempty_adaptedSurgeryWindows hf.neg (isMorse_neg hm) (distinct_critical_values_neg S.distinct)`, `nativeMorseIndex_neg_add`, `nativeMorseCount_neg`, `outer_index_minimality_neg`).

### (8) Index-1 kill — SphereTopology.lean:13231-13250 (sig)
```lean
theorem MorseCancel.outer_index_minimal_index_one_count_zero {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6)
    (horder : ∀ p q …, f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1)
    (hsecondary : ∀ g …, … nativeMorseCount E f 1 + nativeMorseCount E f 5 ≤ …) :
    nativeMorseCount E f 1 = 0
```
Body (13272-13274): contradiction via `exists_one_to_three_handle_trade_of_ordered_indices S hf hm e hdim horder mc ⟨q, hqcrit⟩ hmem.2 hq1 hminimum`, then `hsecondary` + `hother 5` force the cost down.

### (9) Duality transfer — SphereTopology.lean:13279-13298
```lean
theorem MorseCancel.outer_index_minimality_neg {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (hdim : Module.finrank ℝ E = 6)
    (hsecondary : ∀ g …, … nativeMorseCount E f 1 + nativeMorseCount E f 5 ≤ …) :
    ∀ g : M → ℝ, … →
              nativeMorseCount E (fun x => -f x) 1 + nativeMorseCount E (fun x => -f x) 5 ≤
                nativeMorseCount E g 1 + nativeMorseCount E g 5
```

### (10) Handle trade (1→3) — SphereTopology.lean:13143-13162
```lean
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
            (Smale.ManifoldMorse.criticalPoints E h).ncard = (Smale.ManifoldMorse.criticalPoints E f).ncard ∧
              nativeMorseCount E h 1 + 1 = nativeMorseCount E f 1 ∧
                nativeMorseCount E h 3 = nativeMorseCount E f 3 + 1 ∧
                  ∀ j, j ≠ 1 → j ≠ 3 → nativeMorseCount E h j = nativeMorseCount E f j
```
Body: `S.exists_ordered_index_cut horder q (… ≤ 2)` → `exists_one_to_three_handle_trade_at_cut` (13050) → `exists_one_to_three_handle_trade` (12962).

### (11) Trade at fixed band — SphereTopology.lean:12962-12982 (sig)
`theorem MorseCancel.exists_one_to_three_handle_trade {E M : Type*} … (hm0 : nativeMorseIndex E f m = 0) (hq1 : nativeMorseIndex E f q = 1) … {a l u : ℝ} (hreg …) (hhigh : ∀ z …, a ≤ f z → 3 ≤ nativeMorseIndex E f z) (hlow : ∀ z …, f z ≤ a → nativeMorseIndex E f z ≤ 2) (hqa : f q < a) (hal : a < l) (hband : ∀ y, f y ∈ Set.Ioo a u → y ∉ criticalPoints E f) {x : M} (hx : f x ∈ Set.Ioo l u) : ∃ h …, same conclusion as (10)`.
Body: birth of an excellent cancelling (2,3)-pair via `exists_excellent_indexed_morse_birth hf hm S.distinct hbirthband hx (k := 2) …` (11803), then `cancel_one_two_pair_at_unchanged_cut_of_unique_minimum` (12767), bookkeeping via `nativeMorseCount_adjacent_removed_of_index_eq` (12938), `birth_preserves_*` (11898/12810/12828/12848).

### (12) Index-(1,2) pair cancellation — SphereTopology.lean:12767-12794 (sig)
```lean
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
```
Body: `nonempty_adaptedSurgeryWindows`, `T₀.realize_unique_minimum_one_handle_branches` (12662), `U.exists_same_flow_windows_avoiding_level` (4062), `attaching_branches_of_same_flow` (3991), `exists_distinct_unitSphere_points_of_finrank_one` (12607; index-1 ⇒ NegativeCoordinates finrank = 1 ⇒ two distinct attaching points), then `cancel_one_two_pair_at_preserved_middle_cut` (12531) → which calls `exists_handle_trade_transverse_level_data` (12152, at line 12572) and `cancel_transverse_pair_after_flow_preserving_descent` (12440).

### (13) Index-2/3 middle cancellation — Hopf/Recognition.lean:10668-10703
```lean
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
    (hprimitive : Function.Surjective ((S.data p).indexTwoCollapseCoordinate hf.continuous hindex))
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
```
Body (10710-10711): `S.exists_primitive_functional_unit hf hm hdim horder … hcut labels hlabels hcomplete hlower B γ hγ hsurj L hprimitive`, then `T.exists_first_middle_pivot` (Recognition 5505, out of range) — pivot index-3 label whose middle section class maps to ±1, then cancels the (2,3) pair.

### (14) Primitive functional unit — Hopf/Recognition.lean:9190-~9330 (header verbatim; OUTSIDE assigned ranges but a named chain link)
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
```
Conclusion (through ~9330): a list of integer handle slides (`Matrix.transvection`) transforming the middle matrix by elementary column operations, new Morse function `g` with identical critical points/indices, new windows `T`, new family `Γ`, surjectivity preserved, and a pivot `∃ i : Fin n, L ((equalCutHomologyEquiv hsub).symm (MorseCancel.middleSectionClass (Γ i))) = 1 ∨ … = -1`.

### (15) Middle count theorems — Recognition.lean
- 10791-10807 `theorem MorseCancel.minimal_ordered_index_two_count_zero {E M : Type} … (hm : … IsMorse E f) (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere) (horder : …) (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0) (hminimal : ∀ v …, (criticalPoints E f).ncard ≤ (criticalPoints E v).ncard) : nativeMorseCount E f 2 = 0` — body: `exists_middle_index_blocks` + `native_middle_block_counts` (Recognition 4114, out of range) + `S.exists_ordered_middle_family` (SphereTopology 18831) + `T.exists_canonical_middle_family` (Recognition 4316, out of range) + `canonical_middle_matrix_surjective` (Recognition 5023, out of range) + `exists_native_belt_cut_family` (Recognition 10165, out of range) + `cancel_from_complete_middle_family` (10668); contradiction with minimality.
- 10851-10867 `theorem MorseCancel.minimal_ordered_index_four_count_zero … (hsix : nativeMorseCount E f 6 = 1) (hfive : nativeMorseCount E f 5 = 0) (hminimal : …) : nativeMorseCount E f 4 = 0` — pure f ↦ −f duality reducing to (15a) via `nativeMorseCount_neg`, `minimal_excellent_morse_neg`.
- 11128-11139 `theorem MorseCancel.ordered_no_middle_indices_count_two {E M : Type} … (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere) (horder : …) (hzero : nativeMorseCount E f 0 = 1) (hsix : nativeMorseCount E f 6 = 1) (hone : nativeMorseCount E f 1 = 0) (htwo : nativeMorseCount E f 2 = 0) (hfour : nativeMorseCount E f 4 = 0) (hfive : nativeMorseCount E f 5 = 0) : nativeMorseCount E f 3 = 0 ∧ S.count = 2` — via `middle_blocks_complete_of_no_four_five` (11086: `… (hsix : nativeMorseCount E f 6 = 1) (hfour : nativeMorseCount E f 4 = 0) (hfive : nativeMorseCount E f 5 = 0) : r + n + 2 = S.count`) and `S.middle_counts_equal hf hdim e r n …` (11058: bijectivity of the middle matrix forces `r = c`, i.e. equal index-2/index-3 counts; then all zero).
- 11255-11258 `theorem MorseCancel.critical_pair_of_surgery_count_two {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : Smale.ManifoldMorse.SurgeryWindows E f) (hcount : S.count = 2) : ∃ p q : M, f p < f q ∧ Smale.ManifoldMorse.criticalPoints E f = { p, q }`

### Dependency skeleton (arrow = "proved using")
```
Smale.homeomorphic_sixSphere_of_homotopySixSphere        Recognition:11312
  └─ MorseCancel.nonempty_homeomorph_of_homotopySixSphere  Recognition:11301
       ├─ exists_two_critical_point_morse_of_homotopySixSphere  Recognition:11283
       │    ├─ Smale.pathConnectedSpace_of_homotopySixSphere     SingularHomology:19053
       │    ├─ exists_minimal_ordered_morse_system_without_outer_indices  SphereTopology:13361
       │    │    ├─ exists_outer_index_minimal_ordered_morse_system       SphereTopology:13171
       │    │    │    ├─ exists_minimal_excellent_morse_system            SphereTopology:9456 *
       │    │    │    ├─ exists_index_ordered_morse_system_preserving_critical_points  SphereTopology:10109 *
       │    │    │    └─ minimal_excellent_morse_extreme_counts_one       SphereTopology:10180 *
       │    │    └─ outer_index_minimal_outer_counts_zero                 SphereTopology:13312
       │    │         ├─ outer_index_minimal_index_one_count_zero         SphereTopology:13231
       │    │         │    └─ exists_one_to_three_handle_trade_of_ordered_indices  :13143
       │    │         │         └─ exists_one_to_three_handle_trade_at_cut :13050
       │    │         │              └─ exists_one_to_three_handle_trade   :12962
       │    │         │                   ├─ exists_excellent_indexed_morse_birth  :11803 (cubic birth :11056, charts :11284/:11332/:11426/:11555/:11643/:11687)
       │    │         │                   └─ cancel_one_two_pair_at_unchanged_cut_of_unique_minimum :12767
       │    │         │                        └─ cancel_one_two_pair_at_preserved_middle_cut :12531
       │    │         │                             ├─ exists_handle_trade_transverse_level_data :12152
       │    │         │                             │    └─ exists_equal_level_circle_isotopy :12000, exists_new_attaching_circle_placement :12060
       │    │         │                             └─ cancel_transverse_pair_after_flow_preserving_descent :12440
       │    │         └─ outer_index_minimality_neg + nativeMorseCount_neg (f ↦ −f)  :13279
       │    ├─ minimal_ordered_index_two_count_zero   Recognition:10791
       │    │    ├─ exists_middle_index_blocks        SphereTopology:18749
       │    │    ├─ native_middle_block_counts        Recognition:4114 *
       │    │    ├─ exists_ordered_middle_family      SphereTopology:18831
       │    │    ├─ exists_canonical_middle_family    Recognition:4316 *
       │    │    ├─ canonical_middle_matrix_surjective Recognition:5023 *
       │    │    ├─ exists_native_belt_cut_family     Recognition:10165 *
       │    │    └─ cancel_from_complete_middle_family Recognition:10668
       │    │         ├─ AdaptedWindows.exists_primitive_functional_unit  Recognition:9190 *
       │    │         └─ AdaptedWindows.exists_first_middle_pivot         Recognition:5505 *
       │    ├─ minimal_ordered_index_four_count_zero  Recognition:10851 (duality → 10791)
       │    ├─ ordered_no_middle_indices_count_two    Recognition:11128
       │    │    ├─ middle_blocks_complete_of_no_four_five  Recognition:11086
       │    │    └─ SurgeryWindows.middle_counts_equal      Recognition:11058
       │    │         └─ middleMatrix_bijective_of_complete_blocks Recognition:11041
       │    │              └─ middleMatrix_surjective_of_complete_blocks SphereTopology:18723
       │    │                   └─ middleMatrix_surjective_of_homotopySphere SphereTopology:18701
       │    └─ critical_pair_of_surgery_count_two     Recognition:11255
       └─ Smale.ManifoldMorse.nonempty_homeomorphSphere_of_two_critical_points  Recognition:11214 (Reeb)
            └─ homeomorphSphereOfSublevelDisks :11209 ← twoDiskDecompositionOfSublevels :11159
```\n(* = outside assigned ranges.)

## 2. The five spellings of S⁶ (all defeq: `Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1`)

| Spelling | File:line | Verbatim definition | Where used |
|---|---|---|---|
| `SphereHomology.UnitSphere n` | SphereTopology.lean:85-86 | `abbrev SphereHomology.UnitSphere (n : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1` | SphereTopology homology lane (unitSphere_norm :89, basePoint :92…); `UnitSphere 6` = S⁶; basis of `SixSphereCube.StandardSphere` |
| `Smale.Hemisphere.Sphere n` | DifferentialTopology.lean:9547-9548 | `abbrev Smale.Hemisphere.Sphere (n : ℕ) := Metric.sphere (0 : Ambient (n + 1)) 1` (with `abbrev Smale.Hemisphere.Ambient (n : ℕ) := EuclideanSpace ℝ (Fin n)` at :9541-9542) | The Reeb conclusion `M ≃ₜ Smale.Hemisphere.Sphere (Module.finrank ℝ E)` (Recognition:11218), rewritten by `hdim` at :11309; also `Sphere 1`/`Sphere 2` for attaching circles/spheres throughout |
| `Smale.SixSphere` | SingularHomology.lean:18731-18732 | `abbrev Smale.SixSphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1` | **The headline theorem** (Recognition:11315-11316, both hypothesis and conclusion); SphereTopology chain (:12966, :13147, :13235, :13316, :13364, :18705…); Recognition matrix lemmas (:11028, :11045, :11062) |
| `SixSphere` (bare) | Recognition.lean:1641-1642 | `abbrev SixSphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1` | The `MorseCancel.*_homotopySixSphere` chain in Recognition (:10795, :10855, :11132, :11286, :11304); also SixSphereHomology :1644-1650 |
| `SixSphereCube.StandardSphere` | Hurewicz.lean:23627-23628 | `abbrev SixSphereCube.StandardSphere := SphereHomology.UnitSphere 6` | Hurewicz lane only (`euclideanOnePointSphereHomeomorph` :23630, `sphereBasePoint` :23634, `Degree.Sphere.piTwo/Five_subsingleton` :23637-23655) |
| (bonus, local) `unitSphere n` | Final.lean:85-86 | `abbrev unitSphere (n : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1` | Final.lean consumer only: `threefoldHomeomorph : … ≃ₜ unitSphere 6` (:92) |

`Smale.SixSphere` and bare `SixSphere` are two abbrevs with identical RHS; the wrapper at Recognition:11317 passes `hM : M ≃ₕ Smale.SixSphere` where `e : M ≃ₕ SixSphere` is expected (defeq). The headline theorem's spelling is `Smale.SixSphere`.

## 3. Model-space generality / vestigial instances
- Headline signature: `(E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] (hdim : Module.finrank ℝ E = 6) (hM : M ≃ₕ Smale.SixSphere)`. **No `InnerProductSpace ℝ E`** anywhere in the chain; the whole chain is `NormedSpace` + `FiniteDimensional` + `finrank ℝ E = 6`.
- `[SecondCountableTopology M]` sites in the lane ranges: **Recognition.lean:11314 only**, on the headline wrapper. The body (11317) passes only `E M hdim hM`; the inner theorems (`nonempty_homeomorph_of_homotopySixSphere` :11301, `exists_two_critical_point_morse_of_homotopySixSphere` :11283) do not take it → vestigial. (Other `SecondCountableTopology` occurrences in Recognition are outside the assigned ranges: :6533-6535, :7262-7263, :7448, :7566 — Whitney/embedded-avoidance material with `hdim = 6` at :7450/:7567.)
- `[PathConnectedSpace M]` IS load-bearing: required by `exists_minimal_ordered_morse_system_without_outer_indices` (SphereTopology:13363) and the whole MorseCancel chain; it is synthesized from the homotopy equivalence by `Smale.pathConnectedSpace_of_homotopySixSphere` inside (3) at Recognition:11292.
- Consumer discharges the vestigial instance via `attribute [local instance] … SpecialPeriods.Threefold.space_secondCountable in` (Final.lean:88-91, :98-101).

## 4. Middle blocks / handle trade / minimal system (SphereTopology 10489–13361)
Namespace inventory (file order; all inside `Mathoverflow1973`):
- 10489-10556 `Smale.SphereBoundary.*`, `Smale.exists_embedded_disk_extension_of_smooth_extension` — 2-disk extension/Whitney embedding over `Hemisphere.Ambient 2`; needs `5 ≤ finrank ℝ G` (:10525), realized at `= 6` (:10727).
- 10558-10690 `Smale.RadialFilling.*` — direction/radialTime/filling; smooth radial filling of a nullhomotopy.
- 10691-10738 `Smale.exists_smooth_nullhomotopy_of_homotopySixSphere`, `exists_smooth_disk_extension_of_homotopySixSphere` (`(hn : n < 6)` :10709), `exists_embedded_disk_of_homotopySixSphere` (`hdim : finrank ℝ G = 6` :10727) — embedded-disk Whitney trick in dim 6.
- 10740-11024 `MorseCancel.exists_disk_in_level_basin_of_index_cut`, `exists_actual_regular_level_disk_of_index_cut`, `circle_nullhomotopy_of_disk`, `exists_smooth_embedded_disk_of_continuous_filling`, `exists_embedded_regular_level_disk_of_index_cut`, `exists_native_middle_level_circle_disk`, `exists_native_middle_level_circle_isotopy` — embedded level disks bounding attaching circles at a middle cut (`hdim = 6` at :10744/:10791/:10884/:10927/:10972; index bands `3 ≤ index` above, `≤ 3`/`≤ 2` below).
- 11026-11877 `MorseCancel` birth-model block: `cancelled` cubic family (:11026), `exists_exact_cubic_birth` (:11056), scalar/height diffeomorphs (:11115/:11160), Hessian/Morse transfer across linear equivs (:11182-11264), native charts (:11284 `exists_centered_native_height_chart`, :11332 `insert_morse_chart_pair`), birth theorems `exists_native_morse_birth` (:11426), `exists_excellent_native_morse_birth` (:11555), signed-chart constructions (:11643/:11687), index computations (:11741/:11749/:11767), `exists_transverse_signs_of_count` (:11787), **`exists_excellent_indexed_morse_birth` (:11803)** — birth of an excellent cancelling (k,k+1) pair (instantiated k=2 at :12994).
- 11879-12404 level bookkeeping + isotopy: `superlevel_bound_of_critical_bound`, `birth_preserves_lower_levels`, `equalLevelDiffeomorph` (:11933), `regular_level_of_retained_critical_germs`, `isotopicToIdentity_conj`, `exists_equal_level_circle_isotopy` (:12000, hdim=6 :12005), `exists_new_attaching_circle_placement` (:12060, hdim=6 :12065), `unit_level_count_of_circle_placement` (:12121), **`exists_handle_trade_transverse_level_data` (:12152, hdim=6 :12157)** — the "handle trade" geometric core (transverse level data for trading a 1-handle for a 3-handle), `AdaptedWindows.realize_unit_level_isotopy` (:12227), `realize_unit_transverse_level_isotopy` (:12294).
- 12405-12605 cancellation: `no_other_connections_of_two_level_endpoints`, `cancel_transverse_pair_after_flow_preserving_descent` (:12440), **`cancel_one_two_pair_at_preserved_middle_cut` (:12531, hdim=6 :12537)** — index-1/index-2 pair cancellation preserving a middle cut.
- 12607-12765 uniqueness-of-minimum tools: `exists_distinct_unitSphere_points_of_finrank_one` (:12607), `AdaptedWindows.place_one_handle_in_unique_minimum_basin` (:12623), `realize_unique_minimum_one_handle_branches` (:12662).
- 12767-13361 top of the chain: `cancel_one_two_pair_at_unchanged_cut_of_unique_minimum` (:12767), birth bookkeeping (:12810-12959), `exists_one_to_three_handle_trade` (:12962) / `_at_cut` (:13050) / `AdaptedWindows.exists_ordered_index_cut` (:13102) / `_of_ordered_indices` (:13143), `exists_outer_index_minimal_ordered_morse_system` (:13171), `outer_index_minimal_index_one_count_zero` (:13231), `outer_index_minimality_neg` (:13279), `outer_index_minimal_outer_counts_zero` (:13312), **`exists_minimal_ordered_morse_system_without_outer_indices` (:13361)**.

Dimension/index hypotheses: `hdim : Module.finrank ℝ E = 6` on every theorem from :10744 onward (and :4427, :4880 earlier); middle indices are exactly 2 and 3 — index-2 critical point ⇔ `finrank ℝ chart.NegativeCoordinates = 2` (Recognition:10677), its attaching/belt data uses `C(Smale.Hemisphere.Sphere 1, LowerLevel)` (Recognition:10679) and `indexTwoCollapseCoordinate` (SphereTopology:18124, out of range); index-3 ⇔ `NegativeCoordinates = 2 + 1` Fact (SphereTopology:4469-4471, :4620), attaching map `C(Smale.Hemisphere.Sphere 2, LowerLevel)` (`MorseCancel.nativeIndexThreeAttachingSphere` :4616-4623; `hp : nativeMorseIndex E f p = 3`); middle H₂ basis `B : (Fin r → ℤ) ≃ₗ[ℤ] SingularHomology {y // f y ≤ a} 2` (Recognition:10693-10694). `HasIndexTwoPrefix` (def :18232: indices 1..n have NegativeCoordinates finrank = 2), `HasIndexThreeBlock` (def :18499: indices r+1..r+c have finrank = 3). `exists_middle_index_blocks` (:18749-18762, verbatim sig): `(hdim : Module.finrank ℝ E = 6) (horder : …) (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0) : ∃ r c : ℕ, S.HasIndexTwoPrefix r ∧ ∃ _ : r + c < S.count, S.HasIndexThreeBlock r c ∧ r + c + 1 < S.count ∧ ∀ i : Fin S.count, r + c < i.val → 4 ≤ Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates`.

Earlier ranges feeding this: 3778-4876 (circle parametrization `standardCircleParametrization` :3778, index-1 branch realization `realize_one_handle_minimum_branches` :4118 with `hone : nativeMorseIndex E f q = 1` :4122, `exists_middle_family_descent` :4423, `nativeIndexThreeAttachingSphere` :4616, `IsNativeMiddleBasinFamily` def :4810-4813, `exists_middle_block_realization` :4876-4891 with `(hdim : Module.finrank ℝ E = 6)`, `(hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)`, conclusion `∃ α : Fin n → (Smale.Hemisphere.Sphere 2) → { y : M // f y = c }, MorseCancel.IsNativeMiddleBasinFamily T hf hc p α`); 8709-8882 (`ordered_upper_pathConnected_of_later_transfers` :8709, `cell_old_empty_of_empty_boundary` :8758, `native_zero_handle_lower_isEmpty` :8780 with `hindex : finrank ℝ NegativeCoordinates = 0`, `Smale.SublevelDisk.circle_nullhomotopies` :8800 — S¹ nullhomotopies on boundary levels from `NoExotic.sphere_sphere_nullhomotopic`, `Smale.FlowConstruction.regularLevelHomeomorphOfFlow` :8817, `nonempty_regularLevelHomeomorph` :8849, `circle_nullhomotopies_regular_level` :8858); 18589-18831 (`Smale.homotopySixSphere_homology_subsingleton` :18589 `(h : M ≃ₕ Smale.SixSphere) (k : ℕ) (hk : k ≠ 0) (hktop : k ≠ 6) : Subsingleton (SingularHomology M k)`, `lastUpperHomeomorph` :18596, `lastLower_homology_subsingleton` :18604 (hdim=6, `0 < k`, `k < 5`), `upper_homology_subsingleton_of_later_indices` :18635, `SurgeryWindows.middleMatrix` def :18693, `middleMatrix_surjective_of_homotopySphere` :18701 / `_of_complete_blocks` :18723 (hdim=6 at :18705/:18727), `MorseCancel.native_indices_monotone` :18735, `exists_middle_index_blocks` :18749, `nativeMiddleBlockPoint` :18825, `AdaptedWindows.exists_ordered_middle_family` :18831).

## 5. SingularHomology.lean small pieces (verbatim)
19048-19056:
```lean
theorem Smale.simplyConnectedSpace_of_homotopySixSphere {M : Type*} [TopologicalSpace M]
    (e : M ≃ₕ Smale.SixSphere) : SimplyConnectedSpace M := by
  let : SimplyConnectedSpace Smale.SixSphere := EuclideanSphere.simplyConnectedSpace 4
  exact e.simplyConnectedSpace

theorem Smale.pathConnectedSpace_of_homotopySixSphere {M : Type*} [TopologicalSpace M]
    (e : M ≃ₕ Smale.SixSphere) : PathConnectedSpace M := by
  let : SimplyConnectedSpace M := simplyConnectedSpace_of_homotopySixSphere e
  infer_instance
```
19057-19058 (also in range): `abbrev NoExotic.UnitSphere (E : Type*) [NormedAddCommGroup E] := Metric.sphere (0 : E) 1`.
19220-19239:
```lean
theorem Smale.nullhomotopic_of_homotopySixSphere_comp {X M : Type*} [TopologicalSpace X]
    [TopologicalSpace M] (e : M ≃ₕ Smale.SixSphere) (g : C(X, M))
    (h : ∃ c, (e.toFun.comp g).Homotopic (ContinuousMap.const X c)) :
    ∃ c, g.Homotopic (ContinuousMap.const X c)

theorem Smale.manifoldMap_nullhomotopic_of_homotopySixSphere {X M : Type*} [TopologicalSpace X]
    [TopologicalSpace M] {B H : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [FiniteDimensional ℝ B] [TopologicalSpace H] (I : ModelWithCorners ℝ B H) [I.Boundaryless]
    [ChartedSpace H X] [IsManifold I ∞ X] [CompactSpace X] [T2Space X] (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ B < 6) (g : C(X, M)) : ∃ c, g.Homotopic (ContinuousMap.const _ c)
```
(body: `NoExotic.sphereMap_nullhomotopic_of_dim_lt (I := I) 6 (e.toFun.comp g) hdim`).
19241-~19301: `Smale.exists_circle_neighborhood_extension_of_circle_nullhomotopies` — from `(hnull : ∀ f : C(Hemisphere.Sphere 1, M), ∃ c, f.Homotopic (ContinuousMap.const _ c))`, extends a map defined near `Metric.sphere (0 : Hemisphere.Ambient 2) 1` to a compactly-constant `G : C(Hemisphere.Ambient 2, M)` (annular two-disk extension; `DiskCone.extension`, `AnnularExtension.*`). Range 19220-19302 ends as `Smale.WhitneyPairModel.convex_bigon` begins at :19302 (next block).

## 6. Consumers
- Recognition.lean 10477-11148 is not a consumer but the lane's cancellation/homology machinery: `conjugate_level_isotopy` (:10477), `intersection_count_under_injective_map` (:10500), `cancel_from_preserved_unit_belt_cut` (:10514, index-2/3 belt cancellation at a preserved cut; `hdim=6` :10519, `hindex : finrank ℝ NegativeCoordinates = 2` :10520, `hnull` over `Hemisphere.Sphere 1` :10522), `consecutive_last_two_first_three` (:10625), `cancel_from_complete_middle_family` (:10668), `minimal_ordered_index_two/four_count_zero` (:10791/:10851), `MorseSurgeryData.coreBoundary_two_injective_of_upper` (:10896), `indexThreeAttaching_zsmul_eq_zero` (:10910), `Smale.IntegerPresentation.*` (:10926-10949), `indexThreePresentation_matrix_injective` (:10971), `SurgeryWindows.middleMatrix_injective_of_upper_third` (:10985) / `_of_complete_blocks` (:11024) / `middleMatrix_bijective_of_complete_blocks` (:11041), `Smale.HomologyTransport.matrix_sizes_eq_of_bijective` (:11052), `middle_counts_equal` (:11058), `native_index_excluded_of_count_zero` (:11068), `middle_blocks_complete_of_no_four_five` (:11086), `ordered_no_middle_indices_count_two` (:11128).
- Recognition.lean 11255-11317: the chain tail itself (:11255 count-two → critical pair; :11283; :11301; :11312 headline; file ends :11320 `end Mathoverflow1973`).
- Hopf/Final.lean: does **not** restate the theorem. Sole use at :92-96: `def SixSphereComplexAtlas.threefoldHomeomorph : SpecialPeriods.Threefold.Space ≃ₜ unitSphere 6 := Classical.choice (Smale.homeomorphic_sixSphere_of_homotopySixSphere (ℂ × ComplexPlane₂) SpecialPeriods.Threefold.Space SpecialPeriods.Threefold.real_dimension Degree.threefoldHomotopyEquiv)` — model `E = ℂ × ComplexPlane₂` (real finrank 6 via `real_dimension`), `M = SpecialPeriods.Threefold.Space`, homotopy equivalence `Degree.threefoldHomotopyEquiv`; the `[SecondCountableTopology M]` instance comes from the `attribute [local instance] … space_secondCountable in` block (:88-91). Then `modelEquiv` (:102), `exists_complex_analytic_atlas` (:108, IsManifold 𝓘(ℂ,…) ω), `exists_complex_atlas` (:121), and the final `theorem mathoverflow_1973` (:134-138) is the complex-atlas existence statement over `unitSphere 6`, derived from `exists_complex_atlas` — not a restatement of recognition.

## 7. Pragmas/instances the moved code needs
- File-top (each of the 5 files): `set_option maxSynthPendingDepth 3`, `open Set Function Filter Manifold Topology`, `open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity UpperHalfPlane`, `universe u v`, `noncomputable section`, `namespace Mathoverflow1973`, `local infixr:80 " ≫ₚ " => Path.trans`.
- In-range `attribute [local instance 100] Classical.propDecidable in` prefixes: SphereTopology :3852, :4011, :4061, :4117, :11740, :11748, :11766, :12059, :12151, :12530, :12622, :12661, :12766, :12890, :12961, :13101, :18603, :18748 (preceding the named theorems).
- `attribute [local irreducible] MorseCancel.canonicalMiddleMatrix in`: Recognition :9189 (before `exists_primitive_functional_unit`), :10164 (before `exists_native_belt_cut_family`), :10667 (before `cancel_from_complete_middle_family`). `canonicalMiddleMatrix` def itself: Recognition:5017-5020 (out of range).
- Core type definitions the lane depends on (out of range): `AdaptedWindows` structure DifferentialTopology:14114 (extends `Smale.ManifoldMorse.SurgeryWindows`, adds `field`); `MorseCancel.nativeMorseIndex` DifferentialTopology:20088; `MorseCancel.nativeMorseCount` SingularHomology:28261; `Smale.TwoDiskDecomposition` SphereTopology:8073; `Smale.SublevelDisk` SphereTopology:8157; `MorseCancel.IsNativeMiddleBasinFamily` SphereTopology:4810 (in range).
- No `universe`/`set_option`/`open`/`@[instance_reducible]` declarations occur inside the assigned ranges themselves.
- No declaration named *cobord* exists anywhere in the repo: the h-cobordism Thm 9.1 content is realized as the handle-trade/cancellation chain `exists_handle_trade_transverse_level_data` (SphereTopology:12152) → `cancel_one_two_pair_at_preserved_middle_cut` (:12531) → `cancel_one_two_pair_at_unchanged_cut_of_unique_minimum` (:12767) → `exists_one_to_three_handle_trade*` (:12962/:13050/:13143), plus the index-2/3 cancellation `cancel_from_preserved_unit_belt_cut` (Recognition:10514) → `cancel_from_complete_middle_family` (:10668).