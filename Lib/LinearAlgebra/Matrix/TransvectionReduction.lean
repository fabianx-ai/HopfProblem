module

public import Mathlib

/-!
# Transvection reduction of integer matrices

Elementary column operations on integer matrices realized as right multiplication by
`Matrix.transvection`, and the reduction of a unimodular row to a row containing `±1`
(Milnor, *Lectures on the h-cobordism theorem*, §7, Thm. 7.6's algebra), together with
the coordinate-matrix API that transports `ℤ`-bases through these operations.

## Provenance

Moved verbatim from `Hopf/Recognition.lean` (lane F0a). The declarations keep their
`Mathoverflow1973.MorseCancel.*` names so existing consumers re-point through unchanged
fully qualified names; the upstream-shaped rename to `Matrix.*` is a separate commit.
-/

@[expose] public noncomputable section

namespace Mathoverflow1973

def MorseCancel.classCoordinateMatrix {A : Type} [AddCommGroup A] [Module ℤ A] {r n : ℕ}
    (B : (Fin r → ℤ) ≃ₗ[ℤ] A) (v : Fin n → A) : Matrix (Fin r) (Fin n) ℤ := fun i j =>
  B.symm (v j) i

theorem MorseCancel.classCoordinateMatrix_mulVec {A : Type} [AddCommGroup A] [Module ℤ A]
    {r n : ℕ} (B : (Fin r → ℤ) ≃ₗ[ℤ] A) (v : Fin n → A) (z : Fin n → ℤ) :
    B ((classCoordinateMatrix B v).mulVec z) = ∑ j, z j • v j := by
  have hvec : (classCoordinateMatrix B v).mulVec z = ∑ j, z j • B.symm (v j) := by
    funext i
    simp [classCoordinateMatrix, Matrix.mulVec, dotProduct, mul_comm]
  rw [hvec, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_zsmul, LinearEquiv.apply_symm_apply]

theorem MorseCancel.classCoordinateMatrix_surjective {A : Type} [AddCommGroup A] [hA : Module ℤ A]
    {r n : ℕ} (B : (Fin r → ℤ) ≃ₗ[ℤ] A) (v : Fin n → A)
    (hspan : Submodule.span ℤ (Set.range v) = ⊤) :
    Function.Surjective (classCoordinateMatrix B v).mulVec := by
  intro w
  have hw : B w ∈ Submodule.span ℤ (Set.range v) := by rw [hspan]; trivial
  obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hw
  refine ⟨z, B.injective ?_⟩
  rw [classCoordinateMatrix_mulVec]
  have hsum : (∑ j, z j • v j) = ∑ j, hA.smul (z j) (v j) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact (int_smul_eq_zsmul hA (z j) (v j)).symm
  exact hsum.trans hz
theorem MorseCancel.mul_transvection_surjective {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℤ)
    (i j : Fin n) (hij : i ≠ j) (k : ℤ) (hA : Function.Surjective A.mulVec) :
    Function.Surjective (A * Matrix.transvection i j k).mulVec := by
  intro y
  obtain ⟨z, hz⟩ := hA y
  refine ⟨(Matrix.transvection i j (-k)).mulVec z, ?_⟩
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.transvection_mul_transvection_same i j hij,
    add_neg_cancel, Matrix.transvection_zero, Matrix.mul_one]
  exact hz

theorem MorseCancel.eq_mul_transvection_of_columns {r n : ℕ} (A A' : Matrix (Fin r) (Fin n) ℤ)
    (i j : Fin n) (k : ℤ) (hchanged : ∀ u, A' u j = A u j + k * A u i)
    (hother : ∀ u v, v ≠ j → A' u v = A u v) : A' = A * Matrix.transvection i j k := by
  funext u v
  by_cases hv : v = j
  · subst v
    exact (hchanged u).trans (Matrix.mul_transvection_apply_same i j u k A).symm
  · exact (hother u v hv).trans (Matrix.mul_transvection_apply_of_ne i j u v hv k A).symm

theorem MorseCancel.mul_transvection_list_surjective {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℤ)
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
      ← Matrix.mul_assoc] using mul_transvection_surjective _ op.1 op.2.1 hop op.2.2 (ih hprev)

theorem MorseCancel.primitive_row_has_unit_after_column_additions {n : ℕ}
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
  have hC : Function.Surjective C.mulVec := mul_transvection_list_surjective A hA ops hvalid
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
theorem MorseCancel.functional_class_row_surjective {H : Type} [AddCommGroup H] [Module ℤ H]
    {r n : ℕ} (B : (Fin r → ℤ) ≃ₗ[ℤ] H) (v : Fin n → H)
    (hA : Function.Surjective (classCoordinateMatrix B v).mulVec) (L : H →ₗ[ℤ] ℤ)
    (hL : Function.Surjective L) :
    Function.Surjective (Matrix.of (fun (_ : Fin 1) (j : Fin n) => L (v j))).mulVec := by
  intro y
  obtain ⟨h, hh⟩ := hL (y 0)
  obtain ⟨x, hx⟩ := hA (B.symm h)
  have hsum : (∑ j, x j • v j) = h := by
    rw [← classCoordinateMatrix_mulVec B v x, hx, LinearEquiv.apply_symm_apply]
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

theorem MorseCancel.transported_classes_of_matrix_product {H K : Type} [AddCommGroup H]
    [Module ℤ H] [AddCommGroup K] [Module ℤ K] {r n : ℕ} (B : (Fin r → ℤ) ≃ₗ[ℤ] H) (e : H ≃ₗ[ℤ] K)
    (v : Fin n → H) (w : Fin n → K) (P : Matrix (Fin n) (Fin n) ℤ)
    (hmatrix : classCoordinateMatrix (B.trans e) w = classCoordinateMatrix B v * P) (j : Fin n) :
    e.symm (w j) = ∑ i, P i j • v i := by
  have hvec : (classCoordinateMatrix B v).mulVec (fun i => P i j) = (B.trans e).symm (w j) := by
    funext i
    exact (congrFun (congrFun hmatrix i) j).symm
  calc
    e.symm (w j) = B ((classCoordinateMatrix B v).mulVec (fun i => P i j)) := by
      rw [hvec]
      exact (B.apply_symm_apply (e.symm (w j))).symm
    _ = _ := classCoordinateMatrix_mulVec B v _

theorem MorseCancel.functional_rows_of_matrix_product {H K : Type} [AddCommGroup H] [Module ℤ H]
    [AddCommGroup K] [Module ℤ K] {r n : ℕ} (B : (Fin r → ℤ) ≃ₗ[ℤ] H) (e : H ≃ₗ[ℤ] K)
    (v : Fin n → H) (w : Fin n → K) (P : Matrix (Fin n) (Fin n) ℤ)
    (hmatrix : classCoordinateMatrix (B.trans e) w = classCoordinateMatrix B v * P)
    (L : H →ₗ[ℤ] ℤ) :
    Matrix.of (fun (_ : Fin 1) (j : Fin n) => L (e.symm (w j))) =
      Matrix.of (fun (_ : Fin 1) (j : Fin n) => L (v j)) * P := by
  funext u j
  change L (e.symm (w j)) = ∑ i, L (v i) * P i j
  rw [transported_classes_of_matrix_product B e v w P hmatrix j, map_sum]
  simp only [map_zsmul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _


end Mathoverflow1973
