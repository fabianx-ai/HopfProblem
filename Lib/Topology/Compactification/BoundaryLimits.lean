module
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.DenseEmbedding

/-!+# Homeomorphisms from paired boundary limits

The graph-closure argument for compact Hausdorff spaces: forward limits identify
the closure of the interior graph, and paired inverse limits give injectivity.
Source: CENTER_LCP_FREE_COMPACTIFICATION_F1_TEXTBOOK.md, complete proof.
This is general topology, with no analytic realization assumption.
-/

public section
open Set Filter Topology
universe u v

/-- A homeomorphism between open dense subsets of compact Hausdorff spaces
extends when each source boundary point has one complementary value carrying
both the forward and inverse restricted limits. Empty spaces are allowed. -/
theorem Compactification.exists_homeomorph_of_paired_limits
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    [CompactSpace A] [T2Space A] [CompactSpace B] [T2Space B]
    {U : Set A} {V : Set B}
    (hUo : IsOpen U) (hVo : IsOpen V) (hU : Dense U) (hV : Dense V)
    (g : U ≃ₜ V)
    (hb : ∀ x ∉ U, ∃ y : B, y ∉ V ∧
      Tendsto (fun z : U => (g z : B)) (comap Subtype.val (𝓝 x)) (𝓝 y) ∧
      Tendsto (fun z : V => (g.symm z : A)) (comap Subtype.val (𝓝 y)) (𝓝 x)) :
    ∃ G : A ≃ₜ B, ∀ z : U, G z = (g z : B) := by
  classical
  -- Empty source forces empty target by bijectivity on the dense subsets (E).
  by_cases hA : IsEmpty A
  · letI : IsEmpty A := hA
    have hVe : V = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro b hbV
      exact isEmptyElim (g.symm ⟨b, hbV⟩).val
    have hBe : IsEmpty B := ⟨fun b => by
      have hm := hV b
      rw [hVe, closure_empty] at hm
      exact hm⟩
    letI : IsEmpty B := hBe
    exact ⟨Homeomorph.empty, fun z => isEmptyElim z.val⟩
  · -- Select one map, retaining both halves of the same boundary witness (I,G,R).
    let G : A → B := fun x => if hx : x ∈ U then (g ⟨x, hx⟩ : B) else (hb x hx).choose
    have he : ∀ z : U, G z = (g z : B) := by
      intro z
      simp only [G, dif_pos z.property]
    have ho : ∀ x ∉ U, G x ∉ V := by
      intro x hx
      simpa only [G, dif_neg hx] using (hb x hx).choose_spec.1
    have ht : ∀ x, Tendsto (fun z : U => (g z : B))
        (comap Subtype.val (𝓝 x)) (𝓝 (G x)) := by
      intro x
      by_cases hx : x ∈ U
      · have hc := (continuous_subtype_val.comp g.continuous).continuousAt (x := ⟨x, hx⟩)
        change Tendsto (fun z : U => (g z : B)) (𝓝 (⟨x, hx⟩ : U)) (𝓝 (g ⟨x, hx⟩ : B)) at hc
        rw [nhds_subtype_eq_comap] at hc
        simpa only [G, dif_pos hx] using hc
      · simpa only [G, dif_neg hx] using (hb x hx).choose_spec.2.1
    have hi : ∀ x ∉ U, Tendsto (fun z : V => (g.symm z : A))
        (comap Subtype.val (𝓝 (G x))) (𝓝 x) := by
      intro x hx
      simpa only [G, dif_neg hx] using (hb x hx).choose_spec.2.2
    -- Density makes both restricted filters nonvacuous; Hausdorff limits are unique (N,L).
    have hNU (x : A) : NeBot (comap (Subtype.val : U → A) (𝓝 x)) :=
      hU.isDenseInducing_val.comap_nhds_neBot x
    have hNV (y : B) : NeBot (comap (Subtype.val : V → B) (𝓝 y)) :=
      hV.isDenseInducing_val.comap_nhds_neBot y
    have hUnique (x : A) (y : B)
        (hy : Tendsto (fun z : U => (g z : B)) (comap Subtype.val (𝓝 x)) (𝓝 y)) :
        G x = y := tendsto_nhds_unique' (hNU x) (ht x) hy
    have hInverseUnique (y : B) (x x' : A)
        (hx : Tendsto (fun z : V => (g.symm z : A)) (comap Subtype.val (𝓝 y)) (𝓝 x))
        (hx' : Tendsto (fun z : V => (g.symm z : A)) (comap Subtype.val (𝓝 y)) (𝓝 x')) :
        x = x' := tendsto_nhds_unique' (hNV y) hx hx'
    let Γ : Set (A × B) := closure (Set.range (fun z : U => ((z : A), (g z : B))))
    -- Every rectangle at (x,G x) meets the interior graph: intersect its source
    -- neighborhood with the forward-limit neighborhood and use density (J).
    have hJ : ∀ x, (x, G x) ∈ Γ := by
      intro x
      apply mem_closure_iff.mpr
      intro o hoo hxo
      obtain ⟨n, hn, w, hw, hsub⟩ := mem_nhds_prod_iff.mp (hoo.mem_nhds hxo)
      letI := hNU x
      have hn' : ∀ᶠ z : U in comap Subtype.val (𝓝 x), (z : A) ∈ n :=
        preimage_mem_comap hn
      have hw' : ∀ᶠ z : U in comap Subtype.val (𝓝 x), (g z : B) ∈ w := ht x hw
      obtain ⟨z, hzn, hzw⟩ := (hn'.and hw').exists
      exact ⟨((z : A), (g z : B)), hsub ⟨hzn, hzw⟩, ⟨z, rfl⟩⟩
    -- A different second coordinate has a separated target neighborhood.
    -- Its rectangle with a forward-limit neighborhood misses the graph (K).
    have hK : ∀ p ∈ Γ, p.2 = G p.1 := by
      intro p hp
      by_contra hne
      obtain ⟨w, v, hwo, hvo, hpw, hGv, hd⟩ := t2_separation hne
      obtain ⟨n, hn, hnv⟩ := mem_comap.mp (ht p.1 (hvo.mem_nhds hGv))
      obtain ⟨n', hnn, hno, hpn⟩ := mem_nhds_iff.mp hn
      obtain ⟨q, hq, z, hz⟩ := mem_closure_iff.mp hp (n' ×ˢ w)
        (hno.prod hwo) ⟨hpn, hpw⟩
      subst q
      exact Set.disjoint_left.mp hd hq.2 (hnv (hnn hq.1))
    have hGraph : Γ = {p : A × B | p.2 = G p.1} := by
      ext p
      constructor
      · exact hK p
      · intro hp
        change p.2 = G p.1 at hp
        have hj := hJ p.1
        simpa only [← hp, Prod.mk.eta] using hj
    -- The compact graph projects continuously and bijectively onto A (Q).
    have hΓ : IsCompact Γ := isClosed_closure.isCompact
    letI : CompactSpace Γ := isCompact_iff_compactSpace.mp hΓ
    let p : Γ → A := fun z => z.val.1
    have hp : Continuous p := continuous_fst.comp continuous_subtype_val
    have hpb : Function.Bijective p := by
      constructor
      · intro z w hzw
        apply Subtype.ext
        apply Prod.ext hzw
        exact (hK z.val z.property).trans ((congrArg G hzw).trans (hK w.val w.property).symm)
      · intro x
        exact ⟨⟨(x, G x), hJ x⟩, rfl⟩
    -- Closed subsets have compact, hence closed, images in Hausdorff A.
    -- The inverse projection is continuous, and its second coordinate is G (C).
    let pe : Γ ≃ A := Equiv.ofBijective p hpb
    have hpclosed : IsClosedMap p := hp.isClosedMap
    let ph : Γ ≃ₜ A := hp.homeoOfEquivCompactToT2 (f := pe)
    have hrec : (fun x => (ph.symm x).val.2) = G := by
      funext x
      have hx : (ph.symm x).val.1 = x := ph.apply_symm_apply x
      exact (hK _ (ph.symm x).property).trans (congrArg G hx)
    have hGc : Continuous G := by
      rw [← hrec]
      exact continuous_snd.comp (continuous_subtype_val.comp ph.symm.continuous)
    -- Exhaust all four membership cases. Two boundary points with a common
    -- image have equal limits of the SAME inverse on the dense target subset (M).
    have hGi : Function.Injective G := by
      intro x x' hxx
      by_cases hx : x ∈ U <;> by_cases hx' : x' ∈ U
      · have hg : g ⟨x, hx⟩ = g ⟨x', hx'⟩ := Subtype.ext
          ((he ⟨x, hx⟩).symm.trans (hxx.trans (he ⟨x', hx'⟩)))
        exact congrArg Subtype.val (g.injective hg)
      · have hv : G x ∈ V := (he ⟨x, hx⟩) ▸ (g ⟨x, hx⟩).property
        exact False.elim (ho x' hx' (hxx ▸ hv))
      · have hv : G x' ∈ V := (he ⟨x', hx'⟩) ▸ (g ⟨x', hx'⟩).property
        exact False.elim (ho x hx (hxx.symm ▸ hv))
      · exact hInverseUnique (G x) x x' (hi x hx) (hxx.symm ▸ hi x' hx')
    -- The continuous image is compact and closed, and contains dense V (S).
    have hRangeClosed : IsClosed (Set.range G) := (isCompact_range hGc).isClosed
    have hVRange : V ⊆ Set.range G := by
      intro y hy
      refine ⟨(g.symm ⟨y, hy⟩ : A), ?_⟩
      exact (he (g.symm ⟨y, hy⟩)).trans (congrArg Subtype.val (g.apply_symm_apply ⟨y, hy⟩))
    have hGs : Function.Surjective G := by
      intro y
      exact (closure_minimal hVRange hRangeClosed) (hV y)
    -- The same compact-to-Hausdorff closed-map argument gives inverse
    -- continuity for this same G, with its original agreement unchanged (H,T).
    let ge : A ≃ B := Equiv.ofBijective G ⟨hGi, hGs⟩
    let gh : A ≃ₜ B := hGc.homeoOfEquivCompactToT2 (f := ge)
    exact ⟨gh, he⟩
