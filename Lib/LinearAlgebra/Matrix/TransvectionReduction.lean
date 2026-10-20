module

public import Mathlib

/-!
# Transvection reduction of integer matrices

Elementary column operations on integer matrices, realized as right multiplication by
`Matrix.transvection`, and the Euclidean reduction of a unimodular row: a `1 × n` integer row
whose associated map `ℤⁿ → ℤ` is surjective can be brought by column additions to a row having an
entry `±1`.  Alongside this we record the coordinate-matrix API transporting a `ℤ`-basis through
such operations: the matrix of a family of vectors in a chosen basis, its behaviour under
`Matrix.mulVec`, and the transport of these rows along a linear isomorphism.  That coordinate
matrix is Mathlib's `Module.Basis.toMatrix` for the basis `Module.Basis.ofEquivFun B.symm`
(`LinearEquiv.coordMatrix_eq_toMatrix`).

## Main results

* `Matrix.primitive_row_has_unit_after_column_additions`: a unimodular row becomes a
  row containing `1` or `-1` after finitely many column additions.
* `Matrix.surjective_mulVec_mul_transvection_list`: column additions preserve surjectivity.

## References

* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65], §7 (the algebra of Theorem 7.6:
  elementary column operations on a unimodular row).
-/

@[expose] public noncomputable section

/-- The matrix of a family `v : Fin n → A` in a chosen basis `B : (Fin r → ℤ) ≃ₗ[ℤ] A`: its
`j`-th column is the coordinate vector of `v j`.

This is Mathlib's `Module.Basis.toMatrix` for the basis `Module.Basis.ofEquivFun B.symm`
attached to `B`; see `LinearEquiv.coordMatrix_eq_toMatrix`.  It is kept as a separate definition
because the downstream files phrase everything in terms of the linear equivalence `B` rather
than a `Module.Basis`. -/
def LinearEquiv.coordMatrix {A : Type*} [AddCommGroup A] [Module ℤ A] {r n : ℕ}
    (B : (Fin r → ℤ) ≃ₗ[ℤ] A) (v : Fin n → A) : Matrix (Fin r) (Fin n) ℤ := fun i j =>
  B.symm (v j) i

/-- Hypotheses: a `ℤ`-module `A`, a linear equivalence `B : (Fin r → ℤ) ≃ₗ[ℤ] A` and a family
`v : Fin n → A`.  Conclusion: `LinearEquiv.coordMatrix B v` is the Mathlib matrix
`Module.Basis.toMatrix` of `v` in the basis `Module.Basis.ofEquivFun B.symm` determined by
`B`. -/
theorem LinearEquiv.coordMatrix_eq_toMatrix {A : Type*} [AddCommGroup A] [Module ℤ A] {r n : ℕ}
    (B : (Fin r → ℤ) ≃ₗ[ℤ] A) (v : Fin n → A) :
    coordMatrix B v = (Module.Basis.ofEquivFun B.symm).toMatrix v := by
  ext i j
  simp [coordMatrix, Module.Basis.toMatrix, Module.Basis.ofEquivFun_repr_apply]

/-- Multiplying the coordinate matrix of `v` by a vector of scalars gives, in the basis `B`, the
corresponding linear combination `∑ j, z j • v j`. -/
theorem LinearEquiv.coordMatrix_mulVec {A : Type*} [AddCommGroup A] [Module ℤ A]
    {r n : ℕ} (B : (Fin r → ℤ) ≃ₗ[ℤ] A) (v : Fin n → A) (z : Fin n → ℤ) :
    B ((coordMatrix B v).mulVec z) = ∑ j, z j • v j := by
  have hvec : (coordMatrix B v).mulVec z = ∑ j, z j • B.symm (v j) := by
    funext i
    simp [coordMatrix, Matrix.mulVec, dotProduct, mul_comm]
  rw [hvec, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_zsmul, LinearEquiv.apply_symm_apply]

/-- If a family `v` spans `A`, then multiplication by its coordinate matrix is surjective. -/
theorem LinearEquiv.surjective_coordMatrix_mulVec {A : Type*} [AddCommGroup A] [hA : Module ℤ A]
    {r n : ℕ} (B : (Fin r → ℤ) ≃ₗ[ℤ] A) (v : Fin n → A)
    (hspan : Submodule.span ℤ (Set.range v) = ⊤) :
    Function.Surjective (coordMatrix B v).mulVec := by
  intro w
  have hw : B w ∈ Submodule.span ℤ (Set.range v) := by rw [hspan]; trivial
  obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hw
  refine ⟨z, B.injective ?_⟩
  rw [coordMatrix_mulVec]
  have hsum : (∑ j, z j • v j) = ∑ j, hA.smul (z j) (v j) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact (int_smul_eq_zsmul hA (z j) (v j)).symm
  exact hsum.trans hz
/-- An elementary column operation preserves surjectivity of `Matrix.mulVec`, because the
transvection is invertible with inverse the opposite transvection. -/
theorem Matrix.surjective_mulVec_mul_transvection {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℤ)
    (i j : Fin n) (hij : i ≠ j) (k : ℤ) (hA : Function.Surjective A.mulVec) :
    Function.Surjective (A * Matrix.transvection i j k).mulVec := by
  intro y
  obtain ⟨z, hz⟩ := hA y
  refine ⟨(Matrix.transvection i j (-k)).mulVec z, ?_⟩
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.transvection_mul_transvection_same i j hij,
    add_neg_cancel, Matrix.transvection_zero, Matrix.mul_one]
  exact hz

/-- A matrix obtained from `A` by adding `k` times the `i`-th column to the `j`-th column, and
leaving the other columns unchanged, is `A * Matrix.transvection i j k`. -/
theorem Matrix.eq_mul_transvection_of_columns {r n : ℕ} (A A' : Matrix (Fin r) (Fin n) ℤ)
    (i j : Fin n) (k : ℤ) (hchanged : ∀ u, A' u j = A u j + k * A u i)
    (hother : ∀ u v, v ≠ j → A' u v = A u v) : A' = A * Matrix.transvection i j k := by
  funext u v
  by_cases hv : v = j
  · subst v
    exact (hchanged u).trans (Matrix.mul_transvection_apply_same i j u k A).symm
  · exact (hother u v hv).trans (Matrix.mul_transvection_apply_of_ne i j u v hv k A).symm

/-- Any finite sequence of elementary column operations preserves surjectivity of
`Matrix.mulVec`. -/
theorem Matrix.surjective_mulVec_mul_transvection_list {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℤ)
    (hA : Function.Surjective A.mulVec) (ops : List (Fin n × Fin n × ℤ))
    (hvalid : ∀ op ∈ ops, op.1 ≠ op.2.1) :
    Function.Surjective
      (A * (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod).mulVec := by
  revert hvalid
  induction ops using List.reverseRecOn with
  | nil =>
    intro hvalid
    simpa only [List.map_nil, List.prod_nil, Matrix.mul_one] using hA
  | append_singleton ops op ih =>
    intro hvalid
    have hprev : ∀ e ∈ ops, e.1 ≠ e.2.1 := fun e he => hvalid e (List.mem_append.mpr (Or.inl he))
    have hop := hvalid op (List.mem_append.mpr (Or.inr (List.mem_singleton_self op)))
    simpa only [List.map_append, List.map_singleton, List.prod_append, List.prod_singleton,
      ← Matrix.mul_assoc] using surjective_mulVec_mul_transvection _ op.1 op.2.1 hop op.2.2 (ih hprev)

/-- Euclidean reduction of a unimodular row (Milnor, *Lectures on the h-cobordism theorem*, §7,
the algebra of Theorem 7.6): if the `1 × n` integer row `A` has surjective `Matrix.mulVec`, then
finitely many column additions turn it into a row having an entry `1` or `-1`. -/
theorem Matrix.primitive_row_has_unit_after_column_additions {n : ℕ}
    (A : Matrix (Fin 1) (Fin n) ℤ) (hA : Function.Surjective A.mulVec) :
    ∃ ops : List (Fin n × Fin n × ℤ),
      (∀ op ∈ ops, op.1 ≠ op.2.1) ∧
        ∃ i : Fin n,
          (A * (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod) 0 i = 1 ∨
            (A * (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod) 0 i = -1 := by
  classical
  have hnonzero : ∃ j, A 0 j ≠ 0 := by
    by_contra hnot
    push Not at hnot
    obtain ⟨x, hx⟩ := hA 1
    have hh := congrFun hx 0
    change ∑ j, A 0 j * x j = 1 at hh
    simp only [hnot, MulZeroClass.zero_mul, Finset.sum_const_zero] at hh
    exact zero_ne_one hh
  let P : ℕ → Prop := fun m =>
    ∃ ops : List (Fin n × Fin n × ℤ),
      (∀ op ∈ ops, op.1 ≠ op.2.1) ∧
        ∃ i : Fin n,
          (A * (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod) 0 i ≠ 0 ∧
            ((A * (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod) 0 i).natAbs =
              m
  obtain ⟨j₀, hj₀⟩ := hnonzero
  have hex : ∃ m, P m := by
    refine ⟨(A 0 j₀).natAbs, [], ?_, j₀, ?_, ?_⟩
    · intro op hop
      simp only [List.not_mem_nil] at hop
    · simpa only [List.map_nil, List.prod_nil, Matrix.mul_one] using hj₀
    · simp only [List.map_nil, List.prod_nil, Matrix.mul_one]
  obtain ⟨ops, hvalid, i, hi, hrank⟩ := Nat.find_spec hex
  let C := A * (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod
  have hC : Function.Surjective C.mulVec := surjective_mulVec_mul_transvection_list A hA ops hvalid
  have hdiv (j : Fin n) : C 0 i ∣ C 0 j := by
    by_cases hij : i = j
    · subst j
      exact dvd_refl _
    apply Int.dvd_of_emod_eq_zero
    by_contra hrem
    let op : Fin n × Fin n × ℤ := (i, j, -(C 0 j / C 0 i))
    let ops' := ops ++ [op]
    have hvalid' : ∀ e ∈ ops', e.1 ≠ e.2.1 := by
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact hvalid e he
      · have heq : e = op := List.mem_singleton.mp he
        subst e
        exact hij
    have hnew :
      A * (ops'.map (fun e => Matrix.transvection e.1 e.2.1 e.2.2)).prod =
        C * Matrix.transvection i j (-(C 0 j / C 0 i)) := by
      simp only [ops', List.map_append, List.map_singleton, List.prod_append, List.prod_singleton,
        ← Matrix.mul_assoc]
      rfl
    have hentry :
      (A * (ops'.map (fun e => Matrix.transvection e.1 e.2.1 e.2.2)).prod) 0 j = C 0 j % C 0 i := by
      rw [hnew, Matrix.mul_transvection_apply_same, Int.emod_def]
      ring
    have hsmall : (C 0 j % C 0 i).natAbs < (C 0 i).natAbs := by
      have hh :=
        Int.natAbs_lt_natAbs_of_nonneg_of_lt (Int.emod_nonneg (C 0 j) hi)
          (Int.emod_lt_abs (C 0 j) hi)
      simpa only [Int.natAbs_abs] using hh
    have hminimal :=
      Nat.find_min' hex
        (show P (C 0 j % C 0 i).natAbs from
          ⟨ops', hvalid', j, (by rw [hentry]; exact hrem), congrArg Int.natAbs hentry⟩)
    rw [← hrank] at hminimal
    exact (not_le_of_gt hsmall) hminimal
  obtain ⟨x, hx⟩ := hC 1
  have hsum := congrFun hx 0
  change ∑ j, C 0 j * x j = 1 at hsum
  have hdvd : C 0 i ∣ 1 := by
    rw [← hsum]
    exact Finset.dvd_sum (fun j _ => dvd_mul_of_dvd_left (hdiv j) (x j))
  obtain ⟨v, hv⟩ := hdvd
  exact ⟨ops, hvalid, i, Int.eq_one_or_neg_one_of_mul_eq_one hv.symm⟩
/-- If the coordinate matrix of a family `v` has surjective `Matrix.mulVec` and `L : H →ₗ[ℤ] ℤ`
is surjective, then the row `(L (v j))_j` has surjective `Matrix.mulVec`, i.e. it is
unimodular. -/
theorem LinearEquiv.surjective_functional_row_mulVec {H : Type*} [AddCommGroup H] [Module ℤ H]
    {r n : ℕ} (B : (Fin r → ℤ) ≃ₗ[ℤ] H) (v : Fin n → H)
    (hA : Function.Surjective (coordMatrix B v).mulVec) (L : H →ₗ[ℤ] ℤ)
    (hL : Function.Surjective L) :
    Function.Surjective (Matrix.of (fun (_ : Fin 1) (j : Fin n) => L (v j))).mulVec := by
  intro y
  obtain ⟨h, hh⟩ := hL (y 0)
  obtain ⟨x, hx⟩ := hA (B.symm h)
  have hsum : (∑ j, x j • v j) = h := by
    rw [← coordMatrix_mulVec B v x, hx, LinearEquiv.apply_symm_apply]
  refine ⟨x, ?_⟩
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have heq := congrArg L hsum
  rw [map_sum] at heq
  simp only [map_zsmul, smul_eq_mul] at heq
  change ∑ j, L (v j) * x j = y 0
  rw [← hh, ← heq]
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

/-- If the coordinate matrix of a family `w`, taken in the basis transported along `e`, is the
coordinate matrix of `v` times `P`, then each `e⁻¹ (w j)` is the combination `∑ i, P i j • v i`
of the family `v`. -/
theorem LinearEquiv.symm_apply_eq_sum_of_coordMatrix_eq_mul {H K : Type*} [AddCommGroup H]
    [Module ℤ H] [AddCommGroup K] [Module ℤ K] {r n : ℕ} (B : (Fin r → ℤ) ≃ₗ[ℤ] H) (e : H ≃ₗ[ℤ] K)
    (v : Fin n → H) (w : Fin n → K) (P : Matrix (Fin n) (Fin n) ℤ)
    (hmatrix : coordMatrix (B.trans e) w = coordMatrix B v * P) (j : Fin n) :
    e.symm (w j) = ∑ i, P i j • v i := by
  have hvec : (coordMatrix B v).mulVec (fun i => P i j) = (B.trans e).symm (w j) := by
    funext i
    exact (congrFun (congrFun hmatrix i) j).symm
  calc
    e.symm (w j) = B ((coordMatrix B v).mulVec (fun i => P i j)) := by
      rw [hvec]
      exact (B.apply_symm_apply (e.symm (w j))).symm
    _ = _ := coordMatrix_mulVec B v _

/-- In the situation above, the row of values of a functional `L` on `e⁻¹ ∘ w` is the row of its
values on `v` times `P`: column operations on coordinate matrices act on functional rows. -/
theorem LinearEquiv.functional_row_eq_mul_of_coordMatrix_eq_mul {H K : Type*} [AddCommGroup H] [Module ℤ H]
    [AddCommGroup K] [Module ℤ K] {r n : ℕ} (B : (Fin r → ℤ) ≃ₗ[ℤ] H) (e : H ≃ₗ[ℤ] K)
    (v : Fin n → H) (w : Fin n → K) (P : Matrix (Fin n) (Fin n) ℤ)
    (hmatrix : coordMatrix (B.trans e) w = coordMatrix B v * P)
    (L : H →ₗ[ℤ] ℤ) :
    Matrix.of (fun (_ : Fin 1) (j : Fin n) => L (e.symm (w j))) =
      Matrix.of (fun (_ : Fin 1) (j : Fin n) => L (v j)) * P := by
  funext u j
  change L (e.symm (w j)) = ∑ i, L (v i) * P i j
  rw [symm_apply_eq_sum_of_coordMatrix_eq_mul B e v w P hmatrix j, map_sum]
  simp only [map_zsmul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _


