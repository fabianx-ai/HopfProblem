module

public import Mathlib

/-!
# Integer presentations

Presentations of `ℤ`-modules by generators and explicit relation columns: a
`IntegerPresentation B r c` is a surjective linear map `Fin r → ℤ →ₗ B` whose kernel
is the span of `c` explicit column vectors. Includes the presentation matrix and the
triviality criterion (a presentation of the zero module has surjective presentation
matrix) — Milnor, *Lectures on the h-cobordism theorem*, §7, Thm. 7.6's algebra.

## Provenance

Moved verbatim from `Hopf/SphereTopology.lean` (lane F0b). The declarations keep their
`*` names so existing consumers re-point through unchanged fully
qualified names; the upstream-shaped rename is a separate commit. The interleaved
geometric gluers `MorseSurgeryData.indexThreePresentation` and
`SurgeryWindows.middlePresentation` stay in `Hopf/SphereTopology.lean` and move with
lane F10.
-/

@[expose] public noncomputable section

theorem HomologyTransport.ker_comp_span_singleton {R A B C : Type*} [CommRing R]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [Module R A] [Module R B] [Module R C]
    (p : A →ₗ[R] B) (q : B →ₗ[R] C) (v : A) (hq : LinearMap.ker q = Submodule.span R {p v}) :
    LinearMap.ker (q.comp p) = LinearMap.ker p ⊔ Submodule.span R { v } := by
  apply le_antisymm
  · intro a ha
    have hpa : p a ∈ Submodule.span R {p v} := by
      rw [← hq]
      exact ha
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hpa
    have hk : a - r • v ∈ LinearMap.ker p := by
      change p (a - r • v) = 0
      rw [map_sub, map_smul, hr, sub_self]
    exact
      Submodule.mem_sup.mpr
        ⟨a - r • v, hk, r • v, Submodule.smul_mem _ _ (Submodule.subset_span (by simp)),
          sub_add_cancel _ _⟩
  · apply sup_le
    · intro a ha
      change q (p a) = 0
      change p a = 0 at ha
      rw [ha, map_zero]
    · apply Submodule.span_le.mpr
      intro a ha
      have ha' : a = v := Set.mem_singleton_iff.mp ha
      subst a
      change p v ∈ LinearMap.ker q
      rw [hq]
      exact Submodule.subset_span (by simp)

structure IntegerPresentation (B : Type*) [AddCommGroup B] [Module ℤ B] (r c : ℕ) where
  map : (Fin r → ℤ) →ₗ[ℤ] B
  columns : Fin c → (Fin r → ℤ)
  surjective : Function.Surjective map
  kernel_eq : LinearMap.ker map = Submodule.span ℤ (Set.range columns)

def IntegerPresentation.ofEquiv {B : Type*} [AddCommGroup B] [Module ℤ B] {r : ℕ}
    (e : (Fin r → ℤ) ≃ₗ[ℤ] B) : IntegerPresentation B r 0
    where
  map := e.toLinearMap
  columns := Fin.elim0
  surjective := e.surjective
  kernel_eq := by
    rw [LinearMap.ker_eq_bot.mpr e.injective]
    simp

def IntegerPresentation.transport {B C : Type*} [AddCommGroup B] [AddCommGroup C]
    [Module ℤ B] [Module ℤ C] {r c : ℕ} (P : IntegerPresentation B r c) (e : B ≃ₗ[ℤ] C) :
    IntegerPresentation C r c
    where
  map := e.toLinearMap.comp P.map
  columns := P.columns
  surjective := e.surjective.comp P.surjective
  kernel_eq := by
    have h : LinearMap.ker (e.toLinearMap.comp P.map) = LinearMap.ker P.map := by
      ext v
      change e (P.map v) = 0 ↔ P.map v = 0
      constructor
      · intro hv
        exact e.injective (hv.trans (map_zero e).symm)
      · intro hv
        rw [hv, map_zero]
    exact h.trans P.kernel_eq

def IntegerPresentation.liftRelation {B : Type*} [AddCommGroup B] [Module ℤ B] {r c : ℕ}
    (P : IntegerPresentation B r c) (b : B) : Fin r → ℤ :=
  Classical.choose (P.surjective b)

theorem IntegerPresentation.map_liftRelation {B : Type*} [AddCommGroup B] [Module ℤ B]
    {r c : ℕ} (P : IntegerPresentation B r c) (b : B) : P.map (P.liftRelation b) = b :=
  Classical.choose_spec (P.surjective b)

def IntegerPresentation.adjoin {B C : Type*} [AddCommGroup B] [AddCommGroup C] [Module ℤ B]
    [Module ℤ C] {r c : ℕ} (P : IntegerPresentation B r c) (q : B →ₗ[ℤ] C)
    (hq : Function.Surjective q) (b : B) (hker : LinearMap.ker q = Submodule.span ℤ { b }) :
    IntegerPresentation C r (c + 1)
    where
  map := q.comp P.map
  columns := Fin.cons (P.liftRelation b) P.columns
  surjective := hq.comp P.surjective
  kernel_eq := by
    have hk : LinearMap.ker q = Submodule.span ℤ {P.map (P.liftRelation b)} := by
      rw [P.map_liftRelation]
      exact hker
    rw [HomologyTransport.ker_comp_span_singleton P.map q (P.liftRelation b) hk,
      P.kernel_eq, Fin.range_cons, Submodule.span_insert, sup_comm]

def IntegerPresentation.matrix {B : Type*} [AddCommGroup B] [Module ℤ B] {r c : ℕ}
    (P : IntegerPresentation B r c) : Matrix (Fin r) (Fin c) ℤ := fun i j => P.columns j i

theorem IntegerPresentation.columns_sum_eq_mulVec {B : Type*} [AddCommGroup B] [Module ℤ B]
    {r c : ℕ} (P : IntegerPresentation B r c) (z : Fin c → ℤ) :
    (∑ j, z j • P.columns j) = P.matrix.mulVec z := by
  funext i
  simp [IntegerPresentation.matrix, Matrix.mulVec, dotProduct, mul_comm]

theorem IntegerPresentation.mem_range_matrix_iff {B : Type*} [AddCommGroup B] [Module ℤ B]
    {r c : ℕ} (P : IntegerPresentation B r c) (v : Fin r → ℤ) :
    v ∈ Set.range P.matrix.mulVec ↔ v ∈ Submodule.span ℤ (Set.range P.columns) := by
  rw [Submodule.mem_span_range_iff_exists_fun ℤ]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, (P.columns_sum_eq_mulVec z).trans hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, (P.columns_sum_eq_mulVec z).symm.trans hz⟩

theorem IntegerPresentation.matrix_image_eq_kernel {B : Type*} [AddCommGroup B] [Module ℤ B]
    {r c : ℕ} (P : IntegerPresentation B r c) :
    Set.range P.matrix.mulVec = (LinearMap.ker P.map : Set (Fin r → ℤ)) := by
  ext v
  rw [P.mem_range_matrix_iff, P.kernel_eq]
  rfl

theorem IntegerPresentation.matrix_relation {B : Type*} [AddCommGroup B] [Module ℤ B]
    {r c : ℕ} (P : IntegerPresentation B r c) (z : Fin c → ℤ) :
    P.map (P.matrix.mulVec z) = 0 := by
  have h : P.matrix.mulVec z ∈ Set.range P.matrix.mulVec := ⟨z, rfl⟩
  rw [P.matrix_image_eq_kernel] at h
  exact h

theorem IntegerPresentation.columns_span_of_subsingleton {B : Type*} [AddCommGroup B]
    [Module ℤ B] {r c : ℕ} (P : IntegerPresentation B r c) [Subsingleton B] :
    Submodule.span ℤ (Set.range P.columns) = ⊤ := by
  apply top_unique
  intro v _
  rw [← P.kernel_eq]
  exact Subsingleton.elim _ _

theorem IntegerPresentation.matrix_surjective_of_subsingleton {B : Type*} [AddCommGroup B]
    [Module ℤ B] {r c : ℕ} (P : IntegerPresentation B r c) [Subsingleton B] :
    Function.Surjective P.matrix.mulVec := by
  intro v
  apply (P.mem_range_matrix_iff v).mpr
  rw [P.columns_span_of_subsingleton]
  trivial



theorem IntegerPresentation.ofEquiv_matrix_injective {B : Type*} [AddCommGroup B]
    [Module ℤ B] {r : ℕ} (e : (Fin r → ℤ) ≃ₗ[ℤ] B) :
    Function.Injective (ofEquiv e).matrix.mulVec := fun _ _ _ => Subsingleton.elim _ _

theorem IntegerPresentation.adjoin_mulVec {B C : Type*} [AddCommGroup B] [AddCommGroup C]
    [Module ℤ B] [Module ℤ C] {r c : ℕ} (P : IntegerPresentation B r c) (q : B →ₗ[ℤ] C)
    (hq : Function.Surjective q) (b : B) (hker : LinearMap.ker q = Submodule.span ℤ { b })
    (z : Fin (c + 1) → ℤ) :
    (P.adjoin q hq b hker).matrix.mulVec z =
      z 0 • P.liftRelation b + P.matrix.mulVec (Fin.tail z) := by
  rw [← (P.adjoin q hq b hker).columns_sum_eq_mulVec, Fin.sum_univ_succ]
  change z 0 • P.liftRelation b + (∑ i, z i.succ • P.columns i) = _
  rw [P.columns_sum_eq_mulVec]
  rfl

theorem IntegerPresentation.adjoin_coefficient {B C : Type*} [AddCommGroup B]
    [AddCommGroup C] [Module ℤ B] [Module ℤ C] {r c : ℕ} (P : IntegerPresentation B r c)
    (q : B →ₗ[ℤ] C) (hq : Function.Surjective q) (b : B)
    (hker : LinearMap.ker q = Submodule.span ℤ { b }) (z : Fin (c + 1) → ℤ) :
    P.map ((P.adjoin q hq b hker).matrix.mulVec z) = z 0 • b := by
  rw [P.adjoin_mulVec q hq b hker, map_add, map_zsmul, P.map_liftRelation, P.matrix_relation,
    add_zero]

theorem IntegerPresentation.adjoin_matrix_injective {B C : Type*} [AddCommGroup B]
    [AddCommGroup C] [Module ℤ B] [Module ℤ C] {r c : ℕ} (P : IntegerPresentation B r c)
    (q : B →ₗ[ℤ] C) (hq : Function.Surjective q) (b : B)
    (hker : LinearMap.ker q = Submodule.span ℤ { b }) (hP : Function.Injective P.matrix.mulVec)
    (hb : ∀ z : ℤ, z • b = 0 → z = 0) : Function.Injective (P.adjoin q hq b hker).matrix.mulVec :=
  by
  have hzero (z : Fin (c + 1) → ℤ) (hz : (P.adjoin q hq b hker).matrix.mulVec z = 0) : z = 0 := by
    have hcoeff : z 0 • b = 0 :=
      (P.adjoin_coefficient q hq b hker z).symm.trans ((congrArg P.map hz).trans (map_zero P.map))
    have hz0 := hb (z 0) hcoeff
    have htail : P.matrix.mulVec (Fin.tail z) = 0 := by
      rw [P.adjoin_mulVec q hq b hker, hz0, zero_smul, zero_add] at hz
      exact hz
    have hzero' : P.matrix.mulVec (0 : Fin c → ℤ) = 0 := by simp
    have ht : Fin.tail z = 0 := hP (htail.trans hzero'.symm)
    funext i
    exact Fin.cases hz0 (fun j => congrFun ht j) i
  intro x y hxy
  apply sub_eq_zero.mp
  apply hzero (x - y)
  rw [Matrix.mulVec_sub, hxy, sub_self]

theorem HomologyTransport.exists_split_rank_one_extension {R : Type*} [CommRing R]
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B] (i : A →ₗ[R] B)
    (p : B →ₗ[R] R) (hi : Function.Injective i) (hp : Function.Surjective p)
    (hk : LinearMap.ker p = LinearMap.range i) :
    ∃ e : (A × R) ≃ₗ[R] B, (∀ a, e (a, 0) = i a) ∧ ∀ z, p (e z) = z.2 := by
  obtain ⟨b, hb⟩ := hp 1
  let s : R →ₗ[R] B := LinearMap.toSpanSingleton R B b
  have hs (z : R) : p (s z) = z := by
    change p (z • b) = z
    rw [map_smul, hb, smul_eq_mul, mul_one]
  have hz (a : A) : p (i a) = 0 := by
    have h : i a ∈ LinearMap.range i := ⟨a, rfl⟩
    rw [← hk] at h
    exact h
  let F : (A × R) →ₗ[R] B := i.coprod s
  have hF (z : A × R) : p (F z) = z.2 := by
    change p (i z.1 + s z.2) = z.2
    rw [map_add, hz, hs, zero_add]
  have hinj : Function.Injective F := by
    intro x y h
    have h₂ : x.2 = y.2 := (hF x).symm.trans ((congrArg p h).trans (hF y))
    apply Prod.ext _ h₂
    apply hi
    change i x.1 + s x.2 = i y.1 + s y.2 at h
    rw [h₂] at h
    exact add_right_cancel h
  have hsurj : Function.Surjective F := by
    intro v
    have hv : v - s (p v) ∈ LinearMap.ker p := by
      change p (v - s (p v)) = 0
      rw [map_sub, hs, sub_self]
    rw [hk] at hv
    obtain ⟨a, ha⟩ := hv
    refine ⟨(a, p v), ?_⟩
    change i a + s (p v) = v
    rw [ha, sub_add_cancel]
  refine ⟨LinearEquiv.ofBijective F ⟨hinj, hsurj⟩, ?_, hF⟩
  intro a
  change i a + s 0 = i a
  rw [map_zero, add_zero]

theorem HomologyTransport.exists_add_split_rank_one_extension {R : Type*} [CommRing R]
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B] (i : A →ₗ[R] B)
    (p : B →ₗ[R] R) (hi : Function.Injective i) (hp : Function.Surjective p)
    (hk : LinearMap.ker p = LinearMap.range i) :
    ∃ e : (A × R) ≃+ B, (∀ a, e (a, 0) = i a) ∧ ∀ z, p (e z) = z.2 := by
  obtain ⟨e, he, hp⟩ := exists_split_rank_one_extension i p hi hp hk
  exact ⟨e.toAddEquiv, he, hp⟩
def HomologyTransport.integerCoordinateSplit (n : ℕ) :
    (Fin (n + 1) → ℤ) ≃+ ((Fin n → ℤ) × ℤ)
    where
  toFun v := (fun i => v i.succ, v 0)
  invFun v := Fin.cons v.2 v.1
  left_inv
    v := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  right_inv v := rfl
  map_add' _ _ := rfl
theorem HomologyTransport.integerEquiv_one_natAbs (e : ℤ ≃ₗ[ℤ] ℤ) : (e 1).natAbs = 1 := by
  have h : e.symm 1 * e 1 = 1 := by
    calc
      e.symm 1 * e 1 = e (e.symm 1 • (1 : ℤ)) := by
        rw [map_zsmul, zsmul_eq_mul]
        simp
      _ = 1 := by simp
  exact Int.isUnit_iff_natAbs_eq.mp (IsUnit.of_mul_eq_one_right _ h)
theorem HomologyTransport.matrix_sizes_eq_of_bijective {R : Type*} [CommRing R]
    [Nontrivial R] [StrongRankCondition R] {r c : ℕ} (A : Matrix (Fin r) (Fin c) R)
    (hA : Function.Bijective A.mulVec) : c = r := by
  let e := LinearEquiv.ofBijective A.mulVecLin hA
  simpa using e.finrank_eq

