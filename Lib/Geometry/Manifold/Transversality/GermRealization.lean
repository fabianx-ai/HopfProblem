/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.Existence
public import Lib.Geometry.Manifold.RegularLevel
public import Lib.Geometry.Manifold.WhitneyEmbedding
public import Lib.Geometry.Manifold.Collar
public import Lib.Geometry.Manifold.Morse.SurgeryWindows
public import Lib.Geometry.Manifold.Morse.CubicFlow
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Lib.Geometry.Manifold.Transversality.SupportedIsotopy
public import Lib.Geometry.Manifold.Transversality.LinearFramePaths
public import Lib.Geometry.Manifold.Transversality.GermLinearization
/-!
# Germs realised by compactly supported diffeomorphisms

`SupportedGerms.Realizes U f`: the germ of `f` at the origin is the germ of a diffeomorphism isotopic
to the identity through diffeomorphisms supported in a compact subset of `U` and fixing the origin.
Realised germs are closed under composition and linear conjugation; shears, transvections, hence all
of `SL(n, ℝ)` and every determinant-one germ with bijective derivative (in dimension at least two)
are realised. As an application, two charts with the same centre can be aligned along the first
factor by such a diffeomorphism.

## Main results

* `SupportedGerms.realizes_det_one`, `SupportedGerms.realizes_local_germ`
* `SupportedGerms.exists_native_disk_germ_alignment`

## References

* cf. [M. Hirsch, *Differential Topology*][hirsch76], Ch. 8 §3 (proof of the disc theorem).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff Matrix NNReal

@[expose] public noncomputable section


/-- The germ at the origin of a map `f` is realised by a diffeomorphism supported in `U`: there is a
diffeomorphism agreeing with `f` near the origin which is isotopic to the identity through
diffeomorphisms supported in a compact subset of `U` and fixing the origin.
-/
def SupportedGerms.Realizes {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (f : E → E) : Prop :=
  ∃ (d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (K : Set E),
    IsCompact K ∧
      K ⊆ U ∧
        Nonempty (SupportedDiffeomorph.SupportedRelativeIsotopy d K {0}) ∧
          (d : E → E) =ᶠ[𝓝 (0 : E)] f

/-- Germs realised by supported diffeomorphisms are closed under composition. -/
theorem SupportedGerms.Realizes.comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} {f g : E → E} (hf : SupportedGerms.Realizes U f)
    (hg : SupportedGerms.Realizes U g) : SupportedGerms.Realizes U (f ∘ g) := by
  obtain ⟨d, K, hK, hKU, ⟨A⟩, hd⟩ := hf
  obtain ⟨e, L, hL, hLU, ⟨B⟩, he⟩ := hg
  have he0 : e (0 : E) = 0 := B.endpoint_fixed_on 0 rfl
  have het : Filter.Tendsto e (𝓝 (0 : E)) (𝓝 0) := by
    simpa only [he0] using e.continuous.tendsto (0 : E)
  have C : SupportedDiffeomorph.SupportedRelativeIsotopy (e.trans d) (K ∪ L) {0} := by
    refine
      ⟨(fun p => A.family (p.1, B.family p)), A.smooth.comp (contMDiff_fst.prodMk B.smooth), ?_,
        ?_, ?_, ?_, ?_⟩
    · intro x
      rw [B.zero, A.zero]
    · intro x
      change A.family (1, B.family (1, x)) = d (e x)
      rw [B.one, A.one]
    · intro t
      obtain ⟨dₜ, hdₜ⟩ := A.slices t
      obtain ⟨eₜ, heₜ⟩ := B.slices t
      refine ⟨eₜ.trans dₜ, ?_⟩
      intro x
      change dₜ (eₜ x) = A.family (t, B.family (t, x))
      rw [heₜ, hdₜ]
    · intro t x hx
      rw [B.fixedOutside t x (fun h => hx (Or.inr h)),
        A.fixedOutside t x (fun h => hx (Or.inl h))]
    · intro t x hx
      rw [B.fixedOn t x hx, A.fixedOn t x hx]
  refine ⟨e.trans d, K ∪ L, hK.union hL, Set.union_subset hKU hLU, ⟨C⟩, ?_⟩
  filter_upwards [hd.comp_tendsto het, he] with x hx hy
  change d (e x) = f (g x)
  exact hx.trans (congrArg f hy)

/-- Realisability is invariant under conjugation by a linear isomorphism, the neighbourhood being
transported along.
-/
theorem SupportedGerms.Realizes.conj {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (c : E ≃L[ℝ] F) {U : Set E} {f : E → E}
    (hf : SupportedGerms.Realizes U f) :
    SupportedGerms.Realizes (c '' U) (fun y => c (f (c.symm y))) := by
  obtain ⟨d, K, hK, hKU, ⟨A⟩, hd⟩ := hf
  let D := (c.symm.toDiffeomorph.trans d).trans c.toDiffeomorph
  have B : SupportedDiffeomorph.SupportedRelativeIsotopy D (c '' K) {0} := by
    refine
      ⟨(fun p => c (A.family (p.1, c.symm p.2))),
        c.toDiffeomorph.contMDiff.comp
          (A.smooth.comp
            (contMDiff_fst.prodMk (c.symm.toDiffeomorph.contMDiff.comp contMDiff_snd))),
        ?_, ?_, ?_, ?_, ?_⟩
    · intro y
      rw [A.zero, c.apply_symm_apply]
    · intro y
      change c (A.family (1, c.symm y)) = c (d (c.symm y))
      rw [A.one]
    · intro t
      obtain ⟨e, he⟩ := A.slices t
      refine ⟨(c.symm.toDiffeomorph.trans e).trans c.toDiffeomorph, ?_⟩
      intro y
      change c (e (c.symm y)) = c (A.family (t, c.symm y))
      rw [he]
    · intro t y hy
      have hnot : c.symm y ∉ K := fun h => hy ⟨c.symm y, h, c.apply_symm_apply y⟩
      rw [A.fixedOutside t (c.symm y) hnot, c.apply_symm_apply]
    · intro t y hy
      have hy0 : y = 0 := Set.mem_singleton_iff.mp hy
      subst y
      rw [map_zero, A.fixedOn t 0 rfl, map_zero]
  refine ⟨D, c '' K, hK.image c.continuous, Set.image_mono hKU, ⟨B⟩, ?_⟩
  have ht : Filter.Tendsto c.symm (𝓝 (0 : F)) (𝓝 0) := by
    simpa only [map_zero] using c.symm.continuous.tendsto (0 : F)
  filter_upwards [hd.comp_tendsto ht] with y hy
  exact congrArg c hy

/-- The germ of a linear shear is realised by a supported diffeomorphism. -/
theorem SupportedGerms.realizes_shear {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (L : F →L[ℝ] E) {U : Set (E × F)} (hU : IsOpen U)
    (h0 : (0 : E × F) ∈ U) : Realizes U (fun p => (p.1 + L p.2, p.2)) := by
  obtain ⟨A, K, hK, hKU, hA, hA0, hdiff, hfix, -, hcore, hgerm⟩ :=
    SupportedDiffeomorph.exists_supported_shear_isotopy L hU h0
  obtain ⟨d, hd⟩ := hdiff 1
  have H : SupportedDiffeomorph.SupportedRelativeIsotopy d K {0} := by
    refine ⟨A, hA, hA0, fun x => (hd x).symm, hdiff, hfix, ?_⟩
    intro t x hx
    have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
    subst x
    exact hcore t 0
  refine ⟨d, K, hK, hKU, ⟨H⟩, ?_⟩
  filter_upwards [hgerm] with x hx
  exact (hd x).trans hx


/-- The linear isomorphism splitting `ι → ℝ` into the `i`-th coordinate and the remaining ones. -/
def SupportedGerms.coordinateSplit {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    (ι → ℝ) ≃L[ℝ] ℝ × ({ j : ι // j ≠ i } → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => (x i, fun j => x j)
      invFun := fun p j => if h : j = i then p.1 else p.2 ⟨j, h⟩
      left_inv := by
        intro x
        funext j
        by_cases h : j = i <;> simp [h]
      right_inv := by
        rintro ⟨a, x⟩
        apply Prod.ext
        · simp
        · funext j
          simp [j.property]
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- The germ of a transvection is realised by a supported diffeomorphism, a transvection being a
shear in suitable coordinates.
-/
theorem SupportedGerms.realizes_transvection {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U : Set (ι → ℝ)} (hU : IsOpen U) (h0 : (0 : ι → ℝ) ∈ U) {i j : ι} (hij : i ≠ j) (a : ℝ) :
    Realizes U
      (Matrix.SpecialLinearGroup.toLin' (Matrix.SpecialLinearGroup.transvection hij a)) := by
  let c := coordinateSplit i
  let L : ({ k : ι // k ≠ i } → ℝ) →L[ℝ] ℝ := a • ContinuousLinearMap.proj ⟨j, Ne.symm hij⟩
  have h :=
    (realizes_shear L (c.toHomeomorph.isOpenMap _ hU)
          (show (0 : ℝ × ({ k : ι // k ≠ i } → ℝ)) ∈ c '' U from ⟨0, h0, map_zero c⟩)).conj
      c.symm
  have hset : c.symm '' (c '' U) = U := by
    rw [← Set.image_comp]
    simp only [ContinuousLinearEquiv.symm_comp_self, Set.image_id]
  change Realizes (c.symm '' (c '' U)) (fun y => c.symm ((c y).1 + L (c y).2, (c y).2)) at h
  rw [hset] at h
  convert h using 1
  funext x k
  change
    ((Matrix.SpecialLinearGroup.transvection hij a : Matrix ι ι ℝ) *ᵥ x) k =
      (c.symm ((c x).1 + L (c x).2, (c x).2)) k
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec_eq]
  by_cases hk : k = i
  · subst k
    simp [c, coordinateSplit, L]
  · simp [c, coordinateSplit, L, hk]

/-- The germ of any matrix of determinant one is realised by a supported diffeomorphism. -/
theorem SupportedGerms.realizes_specialLinear {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nontrivial ι] {U : Set (ι → ℝ)} (hU : IsOpen U) (h0 : (0 : ι → ℝ) ∈ U)
    (A : Matrix.SpecialLinearGroup ι ℝ) : Realizes U (Matrix.SpecialLinearGroup.toLin' A) := by
  have hmul (A B : Matrix.SpecialLinearGroup ι ℝ)
    (hA : Realizes U (Matrix.SpecialLinearGroup.toLin' A))
    (hB : Realizes U (Matrix.SpecialLinearGroup.toLin' B)) :
    Realizes U (Matrix.SpecialLinearGroup.toLin' (A * B)) := by
    convert hA.comp hB using 1
    funext x
    rw [map_mul]
    rfl
  apply
    Matrix.SpecialLinearGroup.diagonal_transvection_induction'
      (fun A => Realizes U (Matrix.SpecialLinearGroup.toLin' A)) A
  · intro i j hij a ha
    rw [LinearFramePaths.diag2n_decompose hij a ha]
    exact
      hmul _ _
        (hmul _ _
          (hmul _ _
            (hmul _ _
              (hmul _ _ (realizes_transvection hU h0 hij a)
                (realizes_transvection hU h0 hij.symm (-a⁻¹)))
              (realizes_transvection hU h0 hij a))
            (realizes_transvection hU h0 hij (-1)))
          (realizes_transvection hU h0 hij.symm 1))
        (realizes_transvection hU h0 hij (-1))
  · exact fun i j hij a => realizes_transvection hU h0 hij a
  · exact hmul

/-- The germ of a linear automorphism of determinant one of a finite-dimensional space of dimension
at least two (the basis `b` is indexed by a `Finite`, `Nontrivial` type) is realised by a
supported diffeomorphism.
-/
theorem SupportedGerms.realizes_det_one {ι : Type*} [Finite ι] [Nontrivial ι] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (b : Module.Basis ι ℝ E)
    (C : E ≃L[ℝ] E) (hdet : C.toLinearMap.det = 1) {U : Set E} (hU : IsOpen U)
    (h0 : (0 : E) ∈ U) : Realizes U C := by
  classical
  let := Fintype.ofFinite ι
  let A : Matrix.SpecialLinearGroup ι ℝ :=
    ⟨LinearMap.toMatrix b b C.toLinearMap, (LinearMap.det_toMatrix b C.toLinearMap).trans hdet⟩
  let c : (ι → ℝ) ≃L[ℝ] E := b.equivFun.symm.toContinuousLinearEquiv
  have h :=
    (realizes_specialLinear (c.symm.toHomeomorph.isOpenMap _ hU)
          (show (0 : ι → ℝ) ∈ c.symm '' U from ⟨0, h0, map_zero c.symm⟩) A).conj
      c
  change Realizes (c '' (c.symm '' U)) (fun y => c (A.toLin' (c.symm y))) at h
  have hset : c '' (c.symm '' U) = U := by
    rw [← Set.image_comp]
    simp only [ContinuousLinearEquiv.self_comp_symm, Set.image_id]
  rw [hset] at h
  convert h using 1
  funext x
  apply c.symm.injective
  rw [c.symm_apply_apply]
  exact (LinearMap.toMatrix_mulVec_repr b b C.toLinearMap x).symm


/-- A germ at the origin of a smooth map fixing the origin whose derivative is bijective of
determinant one is realised by a diffeomorphism supported in any prescribed neighbourhood. The
space is assumed of dimension at least two (the basis `b` is indexed by a `Finite`, `Nontrivial`
type).
-/
theorem SupportedGerms.realizes_local_germ {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Finite ι] [Nontrivial ι] (b : Module.Basis ι ℝ E)
    {f : E → E} {U : Set E} (hU : IsOpen U) (h0 : (0 : E) ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (hf0 : f 0 = 0) (hbij : Function.Bijective (fderiv ℝ f 0))
    (hdet : (fderiv ℝ f 0).toLinearMap.det = 1) : Realizes U f := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨C, A, K, hC, -, -, hK, hKU, hA, hA0, hdiff, hfix, -, hfixed, hgerm⟩ :=
    SmallPerturbation.exists_relative_germ_linearization_isotopy hU h0 hf hf0 hbij
      (0 : E →L[ℝ] ℝ) (fun _ _ => rfl) (⊥ : Submodule ℝ E)
      (by
        intro x hx
        have hx0 : x = 0 := hx.2
        subst x
        exact hf0)
  have hCdet : C.toLinearMap.det = 1 := by
    change C.toContinuousLinearMap.toLinearMap.det = 1
    rw [hC]
    exact hdet
  obtain ⟨d, hd⟩ := hdiff 1
  have H : SupportedDiffeomorph.SupportedRelativeIsotopy d K {0} := by
    refine ⟨A, hA, hA0, fun x => (hd x).symm, hdiff, hfix, ?_⟩
    intro t x hx
    exact hfixed t x (Set.mem_singleton_iff.mp hx)
  have hdreal : Realizes U (fun x => A (1, x)) :=
    ⟨d, K, hK, hKU, ⟨H⟩, Filter.Eventually.of_forall hd⟩
  obtain ⟨D, L, hL, hLU, hH, hDgerm⟩ := (realizes_det_one b C hCdet hU h0).comp hdreal
  exact ⟨D, L, hL, hLU, hH, hDgerm.trans hgerm.symm⟩


/-- Every nonzero real number is the determinant of a linear automorphism of a finite-dimensional
space.
-/
theorem SupportedGerms.exists_linearEquiv_with_det {B ι : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [Finite ι] (b : Module.Basis ι ℝ B) (i : ι) {r : ℝ}
    (hr : r ≠ 0) : ∃ R : B ≃L[ℝ] B, R.toLinearMap.det = r := by
  classical
  let := Fintype.ofFinite ι
  let L : B →ₗ[ℝ] B := Matrix.toLin b b (LinearFramePaths.scalarDiagonal i r)
  have hdet : L.det = r := by
    rw [← LinearMap.det_toMatrix b L]
    change
      Matrix.det
          (LinearMap.toMatrix b b
            (Matrix.toLin b b (LinearFramePaths.scalarDiagonal i r))) =
        r
    rw [LinearMap.toMatrix_toLin]
    exact LinearFramePaths.det_scalarDiagonal i r
  have hker : L.ker = ⊥ := by
    by_contra hk
    exact hr (hdet.symm.trans (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk))
  have hi : Function.Injective L := LinearMap.ker_eq_bot.mp hker
  have hbij : Function.Bijective L :=
    ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi⟩
  exact ⟨(LinearEquiv.ofBijective L hbij).toContinuousLinearEquiv, hdet⟩

/-- An automorphism of `A × B` can be corrected to determinant one by an automorphism of the second
factor alone.
-/
theorem SupportedGerms.exists_normal_det_correction {A B ι : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [FiniteDimensional ℝ B] [Finite ι] (b : Module.Basis ι ℝ B) (i : ι)
    (C : (A × B) ≃L[ℝ] (A × B)) :
    ∃ R : B ≃L[ℝ] B,
      (((ContinuousLinearEquiv.refl ℝ A).prodCongr R).toContinuousLinearMap.comp
            C.toContinuousLinearMap).toLinearMap.det =
        1 := by
  classical
  let := Fintype.ofFinite ι
  have hne : C.toLinearMap.det ≠ 0 := C.toLinearEquiv.isUnit_det'.ne_zero
  obtain ⟨R, hR⟩ := exists_linearEquiv_with_det b i (inv_ne_zero hne)
  refine ⟨R, ?_⟩
  change LinearMap.det ((LinearMap.id.prodMap R.toLinearMap).comp C.toLinearMap) = 1
  rw [LinearMap.det_comp, LinearMap.det_prodMap, LinearMap.det_id, one_mul, hR,
    inv_mul_cancel₀ hne]

/-- A chart of `A × B` fixing the origin can be straightened along the first factor: there is a
diffeomorphism supported near the origin and isotopic to the identity carrying the germ of
`x ↦ Φ (x, 0)` to the germ of the inclusion `x ↦ (x, 0)`.
-/
theorem SupportedGerms.exists_supported_disk_germ_alignment {A B ι κ : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [Finite ι] [Finite κ] [Nontrivial κ]
    (b : Module.Basis ι ℝ B) (i : ι) (basis : Module.Basis κ ℝ (A × B))
    (Φ : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
    (h0 : (0 : A × B) ∈ Φ.source) (hΦ0 : Φ 0 = 0) {U : Set (A × B)} (hU : IsOpen U)
    (h0U : (0 : A × B) ∈ U) :
    ∃ (d : Diffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞) (K : Set (A × B)),
      IsCompact K ∧
        K ⊆ U ∧
          Nonempty (SupportedDiffeomorph.SupportedRelativeIsotopy d K {0}) ∧
            (fun x : A => d (Φ (x, 0))) =ᶠ[𝓝 (0 : A)] (fun x => (x, (0 : B))) := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  have ht0 : (0 : A × B) ∈ Φ.target := hΦ0 ▸ Φ.map_source' h0
  have hi0 : Φ.symm 0 = 0 := by
    have hh := Φ.left_inv' h0
    rwa [hΦ0] at hh
  have hi : ContDiffOn ℝ ∞ (Φ.symm : (A × B) → A × B) Φ.target := Φ.contMDiffOn_invFun.contDiffOn
  have hib : Function.Bijective (fderiv ℝ Φ.symm 0) := by
    have hh := PartialChart.bijective_mfderiv Φ.symm ht0
    change
      Function.Bijective (mfderiv 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) Φ.symm 0 : (A × B) →L[ℝ] (A × B)) at hh
    rwa [mfderiv_eq_fderiv] at hh
  let C := (LinearEquiv.ofBijective (fderiv ℝ Φ.symm 0).toLinearMap hib).toContinuousLinearEquiv
  obtain ⟨R, hR⟩ := exists_normal_det_correction b i C
  let T := (ContinuousLinearEquiv.refl ℝ A).prodCongr R
  let f : (A × B) → A × B := T ∘ Φ.symm
  have hf : ContDiffOn ℝ ∞ f (U ∩ Φ.target) :=
    T.contDiff.comp_contDiffOn (hi.mono Set.inter_subset_right)
  have hf0 : f 0 = 0 := by simp only [f, Function.comp_apply, hi0, map_zero]
  have hfi :=
    ((hi.contDiffAt (Φ.open_target.mem_nhds ht0)).differentiableAt (by simp)).hasFDerivAt
  have hdf : fderiv ℝ f 0 = T.toContinuousLinearMap.comp C.toContinuousLinearMap :=
    (T.toContinuousLinearMap.hasFDerivAt.comp 0 hfi).fderiv
  have hfb : Function.Bijective (fderiv ℝ f 0) := by
    rw [hdf]
    exact T.bijective.comp C.bijective
  have hdet : (fderiv ℝ f 0).toLinearMap.det = 1 := by
    rw [hdf]
    exact hR
  obtain ⟨d, K, hK, hKU, hH, hgerm⟩ :=
    realizes_local_germ basis (hU.inter Φ.open_target) ⟨h0U, ht0⟩ hf hf0 hfb hdet
  refine ⟨d, K, hK, hKU.trans Set.inter_subset_left, hH, ?_⟩
  have hΦt : Filter.Tendsto Φ (𝓝 (0 : A × B)) (𝓝 0) := by
    have hh := Φ.toOpenPartialHomeomorph.continuousAt h0
    change Filter.Tendsto Φ (𝓝 (0 : A × B)) (𝓝 (Φ 0)) at hh
    rwa [hΦ0] at hh
  have hcore : Filter.Tendsto (fun x : A => (x, (0 : B))) (𝓝 0) (𝓝 (0 : A × B)) :=
    (continuous_id.prodMk continuous_const).tendsto 0
  filter_upwards [(hgerm.comp_tendsto hΦt).comp_tendsto hcore,
    hcore (Φ.open_source.mem_nhds h0)] with x hx hxsource
  change d (Φ (x, 0)) = f (Φ (x, 0)) at hx
  rw [hx]
  change T (Φ.symm (Φ (x, 0))) = (x, 0)
  have hinv : Φ.symm (Φ (x, 0)) = (x, 0) := Φ.left_inv' hxsource
  rw [hinv]
  simp [T]

/-- Two charts of a manifold with the same centre agree along the first factor after a supported
diffeomorphism: there is a diffeomorphism of `M`, isotopic to the identity through
diffeomorphisms supported in a compact subset of the target of `Ψ`, carrying the germ of
`x ↦ Φ (x, 0)` to the germ of `x ↦ Ψ (x, 0)`.
-/
theorem SupportedGerms.exists_native_disk_germ_alignment {A B E H M ι κ : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [Finite ι] [Finite κ] [Nontrivial κ] (b : Module.Basis ι ℝ B) (i : ι)
    (basis : Module.Basis κ ℝ (A × B)) (Φ Ψ : PartialDiffeomorph 𝓘(ℝ, A × B) J (A × B) M ∞)
    (hΦ0 : (0 : A × B) ∈ Φ.source) (hΨ0 : (0 : A × B) ∈ Ψ.source) (hcenter : Φ 0 = Ψ 0) :
    ∃ (D : Diffeomorph J J M M ∞) (K : Set M),
      IsCompact K ∧
        K ⊆ Ψ.target ∧
          Nonempty (SupportedDiffeomorph.SupportedRelativeIsotopy D K {Ψ 0}) ∧
            (fun x : A => D (Φ (x, 0))) =ᶠ[𝓝 (0 : A)] (fun x => Ψ (x, (0 : B))) := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  let Θ := Φ.trans Ψ.symm
  have hΘ0 : (0 : A × B) ∈ Θ.source := by
    refine ⟨hΦ0, ?_⟩
    change Φ 0 ∈ Ψ.target
    rw [hcenter]
    exact Ψ.map_source' hΨ0
  have hΘzero : Θ 0 = 0 := by
    change Ψ.symm (Φ 0) = 0
    rw [hcenter]
    exact Ψ.left_inv' hΨ0
  obtain ⟨d, L, hL, hLsource, ⟨Hiso⟩, hgerm⟩ :=
    exists_supported_disk_germ_alignment b i basis Θ hΘ0 hΘzero Ψ.open_source hΨ0
  let D := SupportedDiffeomorph.extension Ψ d hL hLsource Hiso.endpoint_fixed_outside
  have hfixed : ∀ x ∈ Ψ.source, Ψ x ∈ ({Ψ 0} : Set M) → x ∈ ({0} : Set (A × B)) := by
    intro x hx hh
    exact
      Set.mem_singleton_iff.mpr
        (Ψ.toOpenPartialHomeomorph.injOn hx hΨ0 (Set.mem_singleton_iff.mp hh))
  have HD := Hiso.extension Ψ hL hLsource hfixed
  refine
    ⟨D, Ψ '' L, hL.image_of_continuousOn (Ψ.contMDiffOn_toFun.continuousOn.mono hLsource), ?_,
      ⟨HD⟩, ?_⟩
  · rintro y ⟨x, hx, rfl⟩
    exact Ψ.map_source' (hLsource hx)
  · have hcore : Filter.Tendsto (fun x : A => (x, (0 : B))) (𝓝 0) (𝓝 (0 : A × B)) :=
      (continuous_id.prodMk continuous_const).tendsto 0
    filter_upwards [hgerm, hcore (Θ.open_source.mem_nhds hΘ0)] with x hx hxsource
    have ht : Φ (x, 0) ∈ Ψ.target := hxsource.2
    have hback : Ψ (Θ (x, 0)) = Φ (x, 0) := Ψ.right_inv' ht
    calc
      D (Φ (x, 0)) = D (Ψ (Θ (x, 0))) := congrArg D hback.symm
      _ = Ψ (d (Θ (x, 0))) :=
        (SupportedDiffeomorph.extension_chart Ψ d hL hLsource Hiso.endpoint_fixed_outside
          (Ψ.map_target' ht))
      _ = Ψ (x, 0) := congrArg Ψ hx
