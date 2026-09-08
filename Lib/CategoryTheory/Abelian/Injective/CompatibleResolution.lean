/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.CategoryTheory.Abelian.Injective.ShortExact
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Recursive compatible injective presentations

Iterate the specified-endpoint embedding and cokernel successor on one shared
short exact row. The three columns retain these same quotient maps and give
injective resolutions with consecutive differential given by quotient followed
by the next embedding. This is the construction of PD-L07, PD7–PD8.
-/

@[expose] public section
noncomputable section
universe v u

namespace CategoryTheory.InjectiveResolution
open CategoryTheory CategoryTheory.Limits
variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]

/-- The private tuple retains one complete embedding and its actual cokernel successor. -/
private structure Step (S : ShortComplex C) where
  x : S.X₂ ⟶ Injective.under S.X₁
  β : S.X₂ ⟶ Injective.under S.X₁ ⊞ Injective.under S.X₃
  hx : S.f ≫ x = Injective.ι S.X₁
  hβ : β = biprod.lift x (S.g ≫ Injective.ι S.X₃)
  hl : S.f ≫ β = Injective.ι S.X₁ ≫ biprod.inl
  hr : β ≫ biprod.snd = S.g ≫ Injective.ι S.X₃
  monoβ : Mono β
  inj : Injective (Injective.under S.X₁ ⊞ Injective.under S.X₃)
  splitExact : (ShortComplex.mk
    (biprod.inl : Injective.under S.X₁ ⟶ Injective.under S.X₁ ⊞ Injective.under S.X₃)
    biprod.snd biprod.inl_snd).ShortExact
  a : cokernel (Injective.ι S.X₁) ⟶ cokernel β
  b : cokernel β ⟶ cokernel (Injective.ι S.X₃)
  ha : a = cokernel.map (Injective.ι S.X₁) β S.f biprod.inl hl.symm
  hb : b = cokernel.map β (Injective.ι S.X₃) S.g biprod.snd hr
  hqa : cokernel.π (Injective.ι S.X₁) ≫ a = biprod.inl ≫ cokernel.π β
  hqb : cokernel.π β ≫ b = biprod.snd ≫ cokernel.π (Injective.ι S.X₃)
  hab : a ≫ b = 0
  exactNext : (ShortComplex.mk a b hab).ShortExact

private abbrev State (C : Type u) [Category.{v} C] [Abelian C] :=
  {S : ShortComplex C // S.ShortExact}

-- Merely collect the complete outputs of the two already-green theorems.
private theorem stepNonempty (s : State C) : Nonempty (Step s.val) := by
  obtain ⟨x, β, hx, hβ, hl, hr, hm⟩ :=
    s.property.exists_injective_biprod_embedding (Injective.ι s.val.X₁)
      (Injective.ι s.val.X₃)
  let : Mono β := hm
  obtain ⟨hi, hs, a, b, ha, hb, hqa, hqb, hab, he⟩ :=
    s.property.injective_biprod_cokernel_successor (Injective.ι s.val.X₁)
      (Injective.ι s.val.X₃) β hl hr
  exact ⟨⟨x, β, hx, hβ, hl, hr, hm, hi, hs, a, b, ha, hb, hqa, hqb, hab, he⟩⟩

private def step (s : State C) : Step s.val := Classical.choice (stepNonempty s)
private def next (s : State C) : State C :=
  ⟨ShortComplex.mk (step s).a (step s).b (step s).hab, (step s).exactNext⟩
private def tower (s : State C) : ℕ → State C
  | 0 => s
  | n + 1 => next (tower s n)

private abbrev row (s : State C) (n : ℕ) := (tower s n).val
private abbrev leftTerm (s : State C) (n : ℕ) := Injective.under (row s n).X₁
private abbrev rightTerm (s : State C) (n : ℕ) := Injective.under (row s n).X₃
private abbrev eA (s : State C) (n : ℕ) := Injective.ι (row s n).X₁
private abbrev eB (s : State C) (n : ℕ) := (step (tower s n)).β
private abbrev eC (s : State C) (n : ℕ) := Injective.ι (row s n).X₃

private def rA (s : State C) (n : ℕ) : leftTerm s n ⟶ (row s (n + 1)).X₁ :=
  cokernel.π (eA s n)
private def rB (s : State C) (n : ℕ) : leftTerm s n ⊞ rightTerm s n ⟶ (row s (n + 1)).X₂ :=
  cokernel.π (eB s n)
private def rC (s : State C) (n : ℕ) : rightTerm s n ⟶ (row s (n + 1)).X₃ :=
  cokernel.π (eC s n)

omit [EnoughInjectives C]

private theorem exactPost (S : ShortComplex C) (he : S.Exact) {Y : C} (q : S.X₃ ⟶ Y) [Mono q]
    (w : S.f ≫ (S.g ≫ q) = 0) : (ShortComplex.mk S.f (S.g ≫ q) w).Exact := by
  let φ : S ⟶ ShortComplex.mk S.f (S.g ≫ q) w :=
    ShortComplex.homMk (𝟙 _) (𝟙 _) q (by simp) (by simp)
  let : Epi φ.τ₁ := by change Epi (𝟙 S.X₁); infer_instance
  let : IsIso φ.τ₂ := by change IsIso (𝟙 S.X₂); infer_instance
  let : Mono φ.τ₃ := by change Mono q; infer_instance
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 he

private theorem exactPre (S : ShortComplex C) (he : S.Exact) {Y : C} (p : Y ⟶ S.X₁) [Epi p]
    (w : (p ≫ S.f) ≫ S.g = 0) : (ShortComplex.mk (p ≫ S.f) S.g w).Exact := by
  let φ : ShortComplex.mk (p ≫ S.f) S.g w ⟶ S :=
    ShortComplex.homMk p (𝟙 _) (𝟙 _) (by simp) (by simp)
  let : Epi φ.τ₁ := by change Epi p; infer_instance
  let : IsIso φ.τ₂ := by change IsIso (𝟙 S.X₂); infer_instance
  let : Mono φ.τ₃ := by change Mono (𝟙 S.X₃); infer_instance
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 he

private theorem columnShortExact {X J Y : C} (e : X ⟶ J) (r : J ⟶ Y) (w : e ≫ r = 0)
    [Mono e] (hc : IsColimit (CokernelCofork.ofπ r w)) :
    (ShortComplex.mk e r w).ShortExact :=
  { exact := ShortComplex.exact_of_g_is_cokernel _ hc
    mono_f := inferInstance
    epi_g := epi_of_isColimit_cofork hc }

private theorem augmentationQuasiIso (X : C) (K : CochainComplex C ℕ) (e : X ⟶ K.X 0)
    (w : e ≫ K.d 0 1 = 0) [Mono e]
    (he : (ShortComplex.mk e (K.d 0 1) w).Exact) :
    QuasiIsoAt ((CochainComplex.fromSingle₀Equiv K X).symm ⟨e, w⟩) 0 := by
  rw [CochainComplex.quasiIsoAt₀_iff]
  apply (ShortComplex.quasiIso_iff_of_zeros _ (by rfl) (by rfl)
    (by change K.d 0 0 = 0; exact K.shape 0 0 (by simp))).2
  refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2 ⟨he, inferInstance⟩
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      change 𝟙 X ≫ e = ((CochainComplex.fromSingle₀Equiv K X).symm ⟨e, w⟩).f 0 ≫ 𝟙 (K.X 0)
      rw [CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
      simp)
    (by change 𝟙 (K.X 0) ≫ K.d 0 1 = K.d 0 1 ≫ 𝟙 (K.X 1); simp)

/-- PD8: the intervening embedding followed by its quotient is zero. -/
private theorem consecutiveSquare
    (X J : ℕ → C) (e : ∀ n, X n ⟶ J n)
    (r : ∀ n, J n ⟶ X (n + 1)) (w : ∀ n, e n ≫ r n = 0) :
    ∀ n, (r n ≫ e (n + 1)) ≫ (r (n + 1) ≫ e (n + 2)) = 0 := by
  intro n
  rw [Category.assoc, ← Category.assoc (e (n + 1)), w (n + 1), zero_comp, comp_zero]

/-- The initial quotient also kills the augmentation. -/
private theorem augmentationZero
    (X J : ℕ → C) (e : ∀ n, X n ⟶ J n)
    (r : ∀ n, J n ⟶ X (n + 1)) (w : ∀ n, e n ≫ r n = 0) :
    e 0 ≫ (r 0 ≫ e 1) = 0 := by
  rw [← Category.assoc, w 0, zero_comp]

/-- At degree zero, postcomposing the quotient by the next monic embedding
does not change its kernel, so the augmentation remains exact. -/
private theorem augmentationExact
    (X J : ℕ → C) (e : ∀ n, X n ⟶ J n)
    (r : ∀ n, J n ⟶ X (n + 1)) (w : ∀ n, e n ≫ r n = 0)
    (he : ∀ n, (ShortComplex.mk (e n) (r n) (w n)).ShortExact)
    (wa : e 0 ≫ (r 0 ≫ e 1) = 0) :
    (ShortComplex.mk (e 0) (r 0 ≫ e 1) wa).Exact := by
  let : Mono (e 1) := (he 1).mono_f
  exact exactPost (ShortComplex.mk (e 0) (r 0) (w 0)) (he 0).exact (e 1) wa

/-- At positive degrees, postcomposition by the next embedding preserves
the kernel, and precomposition by the preceding epic quotient preserves
the image. The same PD7 row therefore gives consecutive exactness. -/
private theorem consecutiveExact
    (X J : ℕ → C) (e : ∀ n, X n ⟶ J n)
    (r : ∀ n, J n ⟶ X (n + 1)) (w : ∀ n, e n ≫ r n = 0)
    (he : ∀ n, (ShortComplex.mk (e n) (r n) (w n)).ShortExact)
    (sq : ∀ n, (r n ≫ e (n + 1)) ≫ (r (n + 1) ≫ e (n + 2)) = 0) :
    ∀ n, (ShortComplex.mk (r n ≫ e (n + 1))
      (r (n + 1) ≫ e (n + 2)) (sq n)).Exact := by
  intro n
  let : Mono (e (n + 2)) := (he (n + 2)).mono_f
  let : Epi (r n) := (he n).epi_g
  have wz : e (n + 1) ≫ (r (n + 1) ≫ e (n + 2)) = 0 := by
    rw [← Category.assoc, w (n + 1), zero_comp]
  have hz := exactPost (ShortComplex.mk (e (n + 1)) (r (n + 1)) (w (n + 1)))
    (he (n + 1)).exact (e (n + 2)) wz
  exact exactPre (ShortComplex.mk (e (n + 1)) (r (n + 1) ≫ e (n + 2)) wz)
    hz (r n) (sq n)

/-- Form the supplied consecutive complex, not an independently chosen
resolution. The preceding exactness calculations give the quasi-isomorphism
from its degree-zero augmentation. -/
private def columnResolution
    (X J : ℕ → C) (e : ∀ n, X n ⟶ J n)
    (r : ∀ n, J n ⟶ X (n + 1)) (w : ∀ n, e n ≫ r n = 0)
    (he : ∀ n, (ShortComplex.mk (e n) (r n) (w n)).ShortExact)
    (inj : ∀ n, Injective (J n)) : InjectiveResolution (X 0) := by
  let d := fun n => r n ≫ e (n + 1)
  let sq := consecutiveSquare X J e r w
  let K := CochainComplex.of J d sq
  have wa : e 0 ≫ K.d 0 1 = 0 := by
    change e 0 ≫ CochainComplex.of.d J d 0 (0 + 1) = 0
    rw [CochainComplex.of_d J d 0]
    exact augmentationZero X J e r w
  let ι := (CochainComplex.fromSingle₀Equiv K (X 0)).symm ⟨e 0, wa⟩
  let : Mono (e 0) := (he 0).mono_f
  have ha : (ShortComplex.mk (e 0) (K.d 0 1) wa).Exact := by
    change (ShortComplex.mk (e 0) (CochainComplex.of.d J d 0 (0 + 1)) _).Exact
    simpa only [CochainComplex.of_d] using
      augmentationExact X J e r w he (augmentationZero X J e r w)
  have h0 : QuasiIsoAt ι 0 := augmentationQuasiIso (X 0) K (e 0) wa ha
  have hp : ∀ n, K.ExactAt (n + 1) := by
    intro n
    rw [K.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)]
    change (ShortComplex.mk (CochainComplex.of.d J d n (n + 1))
      (CochainComplex.of.d J d (n + 1) ((n + 1) + 1)) _).Exact
    simpa only [CochainComplex.of_d] using consecutiveExact X J e r w he sq n
  exact
    { cocomplex := K
      injective := inj
      ι := ι
      quasiIso := ⟨fun n => by
        cases n with
        | zero => exact h0
        | succ n => exact (quasiIsoAt_iff_exactAt ι (n + 1)
            (CochainComplex.exactAt_succ_single_obj (X 0) n)).2 (hp n)⟩ }


/-- The augmentation of the supplied column resolution is its original first embedding. -/
private theorem columnResolution_ι_zero
    (X J : ℕ → C) (e : ∀ n, X n ⟶ J n)
    (r : ∀ n, J n ⟶ X (n + 1)) (w : ∀ n, e n ≫ r n = 0)
    (he : ∀ n, (ShortComplex.mk (e n) (r n) (w n)).ShortExact)
    (inj : ∀ n, Injective (J n)) :
    (columnResolution X J e r w he inj).ι.f 0 = e 0 :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

/-- Repeatedly embed one shared short exact row into its injective biproduct
row and take its three actual cokernels. The resulting short exact column
presentations give consecutive differentials by quotient followed by the
next embedding. Their zero composites, positive exactness and augmentation
exactness yield three injective resolutions on these very terms and maps.
All four stage squares and all quotient universal properties are retained.
This is PD-L07, equations PD7 and PD8; no strict cochain maps are asserted. -/
theorem exists_recursive_injective_presentations
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    (S : ShortComplex C) (hS : S.ShortExact) :
    ∃ (T : ℕ → ShortComplex C) (h0 : T 0 = S)
      (L R : ℕ → C)
      (eA : ∀ n, (T n).X₁ ⟶ L n)
      (eB : ∀ n, (T n).X₂ ⟶ L n ⊞ R n)
      (eC : ∀ n, (T n).X₃ ⟶ R n)
      (rA : ∀ n, L n ⟶ (T (n + 1)).X₁)
      (rB : ∀ n, L n ⊞ R n ⟶ (T (n + 1)).X₂)
      (rC : ∀ n, R n ⟶ (T (n + 1)).X₃),
      (∀ n, (T n).ShortExact) ∧
      (∀ n, Injective (L n)) ∧ (∀ n, Injective (R n)) ∧
      (∀ n, Injective (L n ⊞ R n)) ∧
      (∀ n, (T n).f ≫ eB n = eA n ≫ biprod.inl) ∧
      (∀ n, eB n ≫ biprod.snd = (T n).g ≫ eC n) ∧
      (∀ n, biprod.inl ≫ rB n = rA n ≫ (T (n + 1)).f) ∧
      (∀ n, rB n ≫ (T (n + 1)).g = biprod.snd ≫ rC n) ∧
      (∀ n, ∃ (w : eA n ≫ rA n = 0),
        (ShortComplex.mk (eA n) (rA n) w).ShortExact ∧
        Nonempty (IsColimit (CokernelCofork.ofπ (rA n) w))) ∧
      (∀ n, ∃ (w : eB n ≫ rB n = 0),
        (ShortComplex.mk (eB n) (rB n) w).ShortExact ∧
        Nonempty (IsColimit (CokernelCofork.ofπ (rB n) w))) ∧
      (∀ n, ∃ (w : eC n ≫ rC n = 0),
        (ShortComplex.mk (eC n) (rC n) w).ShortExact ∧
        Nonempty (IsColimit (CokernelCofork.ofπ (rC n) w))) ∧
      ∃ (sqA : ∀ n, (rA n ≫ eA (n + 1)) ≫ (rA (n + 1) ≫ eA (n + 2)) = 0)
        (sqB : ∀ n, (rB n ≫ eB (n + 1)) ≫ (rB (n + 1) ≫ eB (n + 2)) = 0)
        (sqC : ∀ n, (rC n ≫ eC (n + 1)) ≫ (rC (n + 1) ≫ eC (n + 2)) = 0)
        (IA : InjectiveResolution S.X₁)
        (IB : InjectiveResolution S.X₂)
        (IC : InjectiveResolution S.X₃)
        (hA : IA.cocomplex = CochainComplex.of L (fun n => rA n ≫ eA (n + 1)) sqA)
        (hB : IB.cocomplex = CochainComplex.of (fun n => L n ⊞ R n)
          (fun n => rB n ≫ eB (n + 1)) sqB)
        (hC : IC.cocomplex = CochainComplex.of R (fun n => rC n ≫ eC (n + 1)) sqC),
        IA.ι.f 0 ≫ eqToHom (congrArg (fun K : CochainComplex C ℕ => K.X 0) hA) =
          eqToHom (congrArg (fun U : ShortComplex C => U.X₁) h0.symm) ≫ eA 0 ∧
        IB.ι.f 0 ≫ eqToHom (congrArg (fun K : CochainComplex C ℕ => K.X 0) hB) =
          eqToHom (congrArg (fun U : ShortComplex C => U.X₂) h0.symm) ≫ eB 0 ∧
        IC.ι.f 0 ≫ eqToHom (congrArg (fun K : CochainComplex C ℕ => K.X 0) hC) =
          eqToHom (congrArg (fun U : ShortComplex C => U.X₃) h0.symm) ≫ eC 0 := by
  let s : State C := ⟨S, hS⟩
  let XA := fun n => (row s n).X₁
  let XB := fun n => (row s n).X₂
  let XC := fun n => (row s n).X₃
  let JA := leftTerm s
  let JB := fun n => leftTerm s n ⊞ rightTerm s n
  let JC := rightTerm s
  have wA : ∀ n, eA s n ≫ rA s n = 0 := fun n => cokernel.condition (eA s n)
  have wB : ∀ n, eB s n ≫ rB s n = 0 := fun n => cokernel.condition (eB s n)
  have wC : ∀ n, eC s n ≫ rC s n = 0 := fun n => cokernel.condition (eC s n)
  have hA : ∀ n, (ShortComplex.mk (eA s n) (rA s n) (wA n)).ShortExact := by
    intro n
    exact columnShortExact _ _ _ (cokernelIsCokernel (eA s n))
  have hB : ∀ n, (ShortComplex.mk (eB s n) (rB s n) (wB n)).ShortExact := by
    intro n
    let : Mono (eB s n) := (step (tower s n)).monoβ
    exact columnShortExact _ _ _ (cokernelIsCokernel (eB s n))
  have hC : ∀ n, (ShortComplex.mk (eC s n) (rC s n) (wC n)).ShortExact := by
    intro n
    exact columnShortExact _ _ _ (cokernelIsCokernel (eC s n))
  have injA : ∀ n, Injective (JA n) := fun n => Injective.injective_under _
  have injB : ∀ n, Injective (JB n) := fun n => (step (tower s n)).inj
  have injC : ∀ n, Injective (JC n) := fun n => Injective.injective_under _
  let IA := columnResolution XA JA (eA s) (rA s) wA hA injA
  let IB := columnResolution XB JB (eB s) (rB s) wB hB injB
  let IC := columnResolution XC JC (eC s) (rC s) wC hC injC
  refine ⟨row s, rfl, JA, JC, eA s, eB s, eC s, rA s, rB s, rC s,
    (fun n => (tower s n).property), injA, injC, injB,
    (fun n => (step (tower s n)).hl), (fun n => (step (tower s n)).hr),
    (fun n => (step (tower s n)).hqa.symm), (fun n => (step (tower s n)).hqb),
    (fun n => ⟨wA n, hA n, ⟨cokernelIsCokernel (eA s n)⟩⟩),
    (fun n => ⟨wB n, hB n, ⟨cokernelIsCokernel (eB s n)⟩⟩),
    (fun n => ⟨wC n, hC n, ⟨cokernelIsCokernel (eC s n)⟩⟩),
    consecutiveSquare XA JA (eA s) (rA s) wA,
    consecutiveSquare XB JB (eB s) (rB s) wB,
    consecutiveSquare XC JC (eC s) (rC s) wC,
    IA, IB, IC, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · change IA.ι.f 0 ≫ 𝟙 _ = 𝟙 _ ≫ eA s 0
    rw [Category.comp_id, Category.id_comp]
    exact columnResolution_ι_zero XA JA (eA s) (rA s) wA hA injA
  · change IB.ι.f 0 ≫ 𝟙 _ = 𝟙 _ ≫ eB s 0
    rw [Category.comp_id, Category.id_comp]
    exact columnResolution_ι_zero XB JB (eB s) (rB s) wB hB injB
  · change IC.ι.f 0 ≫ 𝟙 _ = 𝟙 _ ≫ eC s 0
    rw [Category.comp_id, Category.id_comp]
    exact columnResolution_ι_zero XC JC (eC s) (rC s) wC hC injC

end CategoryTheory.InjectiveResolution

namespace CategoryTheory.InjectiveResolution

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

/- PD-L08 (PD9): the four stage squares make inclusion and projection commute
with the consecutive differentials r followed by e. -/
private theorem inclusion_comm
    (T : ℕ → ShortComplex C) (L R : ℕ → C)
    (eA : ∀ n, (T n).X₁ ⟶ L n) (eB : ∀ n, (T n).X₂ ⟶ L n ⊞ R n)
    (rA : ∀ n, L n ⟶ (T (n + 1)).X₁)
    (rB : ∀ n, L n ⊞ R n ⟶ (T (n + 1)).X₂)
    (he : ∀ n, (T n).f ≫ eB n = eA n ≫ biprod.inl)
    (hr : ∀ n, biprod.inl ≫ rB n = rA n ≫ (T (n + 1)).f) :
    ∀ n, biprod.inl ≫ (rB n ≫ eB (n + 1)) =
      (rA n ≫ eA (n + 1)) ≫ biprod.inl := by
  intro n
  rw [← Category.assoc, hr n, Category.assoc, he (n + 1), ← Category.assoc]

private theorem projection_comm
    (T : ℕ → ShortComplex C) (L R : ℕ → C)
    (eB : ∀ n, (T n).X₂ ⟶ L n ⊞ R n) (eC : ∀ n, (T n).X₃ ⟶ R n)
    (rB : ∀ n, L n ⊞ R n ⟶ (T (n + 1)).X₂)
    (rC : ∀ n, R n ⟶ (T (n + 1)).X₃)
    (he : ∀ n, eB n ≫ biprod.snd = (T n).g ≫ eC n)
    (hr : ∀ n, rB n ≫ (T (n + 1)).g = biprod.snd ≫ rC n) :
    ∀ n, biprod.snd ≫ (rC n ≫ eC (n + 1)) =
      (rB n ≫ eB (n + 1)) ≫ biprod.snd := by
  intro n
  rw [← Category.assoc, ← hr n, Category.assoc, ← he (n + 1), ← Category.assoc]

private def mapOfConsecutive (A B : ℕ → C)
    (dA : ∀ n, A n ⟶ A (n + 1)) (dB : ∀ n, B n ⟶ B (n + 1))
    (sqA : ∀ n, dA n ≫ dA (n + 1) = 0)
    (sqB : ∀ n, dB n ≫ dB (n + 1) = 0)
    (f : ∀ n, A n ⟶ B n) (hf : ∀ n, f n ≫ dB n = dA n ≫ f (n + 1)) :
    CochainComplex.of A dA sqA ⟶ CochainComplex.of B dB sqB :=
  { f := f
    comm' := by
      intro i j h
      obtain rfl : i + 1 = j := h
      change f i ≫ CochainComplex.of.d B dB i (i + 1) =
        CochainComplex.of.d A dA i (i + 1) ≫ f (i + 1)
      simpa only [CochainComplex.of_d] using hf i }

private theorem mapTransport_f (K K' L L' : CochainComplex C ℕ) (hK : K = K') (hL : L = L')
    (f : K' ⟶ L') (n : ℕ) :
    (eqToHom hK ≫ f ≫ eqToHom hL.symm).f n =
      eqToHom (congrArg (fun M : CochainComplex C ℕ => M.X n) hK) ≫ f.f n ≫
        eqToHom (congrArg (fun M : CochainComplex C ℕ => M.X n) hL.symm) := by
  subst K'
  subst L'
  simp

private theorem augmentationFromZero (X Y : C) (K L : CochainComplex C ℕ)
    (a : (CochainComplex.single₀ C).obj X ⟶ K)
    (b : (CochainComplex.single₀ C).obj Y ⟶ L) (j : K ⟶ L) (f : X ⟶ Y)
    (h : a.f 0 ≫ j.f 0 = f ≫ b.f 0) :
    a ≫ j = (CochainComplex.single₀ C).map f ≫ b := by
  apply (CochainComplex.fromSingle₀Equiv L X).injective
  apply Subtype.ext
  change (a ≫ j).f 0 = ((CochainComplex.single₀ C).map f ≫ b).f 0
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero]
  exact h

/- The initial-row equality and the specified degree-zero augmentations give
the two augmentation squares; equality out of the single complex is detected in degree zero. -/
set_option linter.unusedVariables false in
private theorem augmentation_squares
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    (S : ShortComplex C) (hS : S.ShortExact)
    (T : ℕ → ShortComplex C) (h0 : T 0 = S) (L R : ℕ → C)
    (eA : ∀ n, (T n).X₁ ⟶ L n)
    (eB : ∀ n, (T n).X₂ ⟶ L n ⊞ R n)
    (eC : ∀ n, (T n).X₃ ⟶ R n)
    (rA : ∀ n, L n ⟶ (T (n + 1)).X₁)
    (rB : ∀ n, L n ⊞ R n ⟶ (T (n + 1)).X₂)
    (rC : ∀ n, R n ⟶ (T (n + 1)).X₃)
    (hel : ∀ n, (T n).f ≫ eB n = eA n ≫ biprod.inl)
    (her : ∀ n, eB n ≫ biprod.snd = (T n).g ≫ eC n)
    (hrl : ∀ n, biprod.inl ≫ rB n = rA n ≫ (T (n + 1)).f)
    (hrr : ∀ n, rB n ≫ (T (n + 1)).g = biprod.snd ≫ rC n)
    (sqA : ∀ n, (rA n ≫ eA (n + 1)) ≫ (rA (n + 1) ≫ eA (n + 2)) = 0)
    (sqB : ∀ n, (rB n ≫ eB (n + 1)) ≫ (rB (n + 1) ≫ eB (n + 2)) = 0)
    (sqC : ∀ n, (rC n ≫ eC (n + 1)) ≫ (rC (n + 1) ≫ eC (n + 2)) = 0)
    (IA : InjectiveResolution S.X₁) (IB : InjectiveResolution S.X₂)
    (IC : InjectiveResolution S.X₃)
    (hA : IA.cocomplex = CochainComplex.of L (fun n => rA n ≫ eA (n + 1)) sqA)
    (hB : IB.cocomplex = CochainComplex.of (fun n => L n ⊞ R n)
      (fun n => rB n ≫ eB (n + 1)) sqB)
    (hC : IC.cocomplex = CochainComplex.of R (fun n => rC n ≫ eC (n + 1)) sqC)
    (haA : IA.ι.f 0 ≫ eqToHom (congrArg (fun K : CochainComplex C ℕ => K.X 0) hA) =
      eqToHom (congrArg (fun U : ShortComplex C => U.X₁) h0.symm) ≫ eA 0)
    (haB : IB.ι.f 0 ≫ eqToHom (congrArg (fun K : CochainComplex C ℕ => K.X 0) hB) =
      eqToHom (congrArg (fun U : ShortComplex C => U.X₂) h0.symm) ≫ eB 0)
    (haC : IC.ι.f 0 ≫ eqToHom (congrArg (fun K : CochainComplex C ℕ => K.X 0) hC) =
      eqToHom (congrArg (fun U : ShortComplex C => U.X₃) h0.symm) ≫ eC 0)
    (j : IA.cocomplex ⟶ IB.cocomplex) (q : IB.cocomplex ⟶ IC.cocomplex)
    (hj : ∀ n, j.f n =
      eqToHom (congrArg (fun K : CochainComplex C ℕ => K.X n) hA) ≫ biprod.inl ≫
        eqToHom (congrArg (fun K : CochainComplex C ℕ => K.X n) hB.symm))
    (hq : ∀ n, q.f n =
      eqToHom (congrArg (fun K : CochainComplex C ℕ => K.X n) hB) ≫ biprod.snd ≫
        eqToHom (congrArg (fun K : CochainComplex C ℕ => K.X n) hC.symm)) :
    IA.ι ≫ j = (CochainComplex.single₀ C).map S.f ≫ IB.ι ∧
    IB.ι ≫ q = (CochainComplex.single₀ C).map S.g ≫ IC.ι := by
  subst S
  have haA' : IA.ι.f 0 ≫ eqToHom (congrArg (fun K : CochainComplex C ℕ => K.X 0) hA) = eA 0 := by
    simpa using haA
  have haB' : IB.ι.f 0 ≫ eqToHom (congrArg (fun K : CochainComplex C ℕ => K.X 0) hB) = eB 0 := by
    simpa using haB
  have haC' : IC.ι.f 0 ≫ eqToHom (congrArg (fun K : CochainComplex C ℕ => K.X 0) hC) = eC 0 := by
    simpa using haC
  constructor
  · apply augmentationFromZero _ _ _ _ IA.ι IB.ι j (T 0).f
    apply (cancel_mono (eqToHom (congrArg (fun K : CochainComplex C ℕ => K.X 0) hB))).1
    rw [hj 0]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    rw [← Category.assoc, haA']
    change eA 0 ≫ biprod.inl = ((T 0).f ≫ IB.ι.f 0) ≫
      eqToHom (congrArg (fun K : CochainComplex C ℕ => K.X 0) hB)
    exact (hel 0).symm.trans ((Category.assoc _ _ _).trans
      (congrArg (fun z => (T 0).f ≫ z) haB')).symm
  · apply augmentationFromZero _ _ _ _ IB.ι IC.ι q (T 0).g
    apply (cancel_mono (eqToHom (congrArg (fun K : CochainComplex C ℕ => K.X 0) hC))).1
    rw [hq 0]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    rw [← Category.assoc, haB']
    change eB 0 ≫ biprod.snd = ((T 0).g ≫ IC.ι.f 0) ≫
      eqToHom (congrArg (fun K : CochainComplex C ℕ => K.X 0) hC)
    exact (her 0).trans ((Category.assoc _ _ _).trans
      (congrArg (fun z => (T 0).g ≫ z) haC')).symm

/- The inverse middle transports cancel, leaving the biproduct zero composite. -/
private theorem strict_zero
    (K L M : CochainComplex C ℕ) (A B : ℕ → C)
    (hK : ∀ n, K.X n = A n) (hL : ∀ n, L.X n = (A n ⊞ B n))
    (hM : ∀ n, M.X n = B n) (j : K ⟶ L) (q : L ⟶ M)
    (hj : ∀ n, j.f n = eqToHom (hK n) ≫ biprod.inl ≫ eqToHom (hL n).symm)
    (hq : ∀ n, q.f n = eqToHom (hL n) ≫ biprod.snd ≫ eqToHom (hM n).symm) :
    j ≫ q = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  simp [hj, hq, Category.assoc]

private def splittingOfComponents (X Y Z A B : C) (h₁ : X = A) (h₂ : Y = (A ⊞ B)) (h₃ : Z = B)
    (j : X ⟶ Y) (q : Y ⟶ Z)
    (hj : j = eqToHom h₁ ≫ biprod.inl ≫ eqToHom h₂.symm)
    (hq : q = eqToHom h₂ ≫ biprod.snd ≫ eqToHom h₃.symm)
    (w : j ≫ q = 0) : (ShortComplex.mk j q w).Splitting := by
  subst X
  subst Y
  subst Z
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hj hq
  subst j
  subst q
  exact ShortComplex.Splitting.ofHasBinaryBiproduct A B

/-- PD-L08, textbook PD9: the recursive presentations give a strict short exact
sequence on the very three supplied injective resolutions. Each degree is the
transported split biproduct row; its splitting need not commute with differentials. -/
theorem strict_sequence_of_recursive_presentations
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    (S : ShortComplex C) (hS : S.ShortExact)
    (T : ℕ → ShortComplex C) (h0 : T 0 = S) (L R : ℕ → C)
    (eA : ∀ n, (T n).X₁ ⟶ L n)
    (eB : ∀ n, (T n).X₂ ⟶ L n ⊞ R n)
    (eC : ∀ n, (T n).X₃ ⟶ R n)
    (rA : ∀ n, L n ⟶ (T (n + 1)).X₁)
    (rB : ∀ n, L n ⊞ R n ⟶ (T (n + 1)).X₂)
    (rC : ∀ n, R n ⟶ (T (n + 1)).X₃)
    (hel : ∀ n, (T n).f ≫ eB n = eA n ≫ biprod.inl)
    (her : ∀ n, eB n ≫ biprod.snd = (T n).g ≫ eC n)
    (hrl : ∀ n, biprod.inl ≫ rB n = rA n ≫ (T (n + 1)).f)
    (hrr : ∀ n, rB n ≫ (T (n + 1)).g = biprod.snd ≫ rC n)
    (sqA : ∀ n, (rA n ≫ eA (n + 1)) ≫ (rA (n + 1) ≫ eA (n + 2)) = 0)
    (sqB : ∀ n, (rB n ≫ eB (n + 1)) ≫ (rB (n + 1) ≫ eB (n + 2)) = 0)
    (sqC : ∀ n, (rC n ≫ eC (n + 1)) ≫ (rC (n + 1) ≫ eC (n + 2)) = 0)
    (IA : InjectiveResolution S.X₁) (IB : InjectiveResolution S.X₂)
    (IC : InjectiveResolution S.X₃)
    (hA : IA.cocomplex = CochainComplex.of L (fun n => rA n ≫ eA (n + 1)) sqA)
    (hB : IB.cocomplex = CochainComplex.of (fun n => L n ⊞ R n)
      (fun n => rB n ≫ eB (n + 1)) sqB)
    (hC : IC.cocomplex = CochainComplex.of R (fun n => rC n ≫ eC (n + 1)) sqC)
    (haA : IA.ι.f 0 ≫ eqToHom (congrArg (fun K : CochainComplex C ℕ => K.X 0) hA) =
      eqToHom (congrArg (fun U : ShortComplex C => U.X₁) h0.symm) ≫ eA 0)
    (haB : IB.ι.f 0 ≫ eqToHom (congrArg (fun K : CochainComplex C ℕ => K.X 0) hB) =
      eqToHom (congrArg (fun U : ShortComplex C => U.X₂) h0.symm) ≫ eB 0)
    (haC : IC.ι.f 0 ≫ eqToHom (congrArg (fun K : CochainComplex C ℕ => K.X 0) hC) =
      eqToHom (congrArg (fun U : ShortComplex C => U.X₃) h0.symm) ≫ eC 0) :
    ∃ (j : IA.cocomplex ⟶ IB.cocomplex) (q : IB.cocomplex ⟶ IC.cocomplex)
      (w : j ≫ q = 0),
      IA.ι ≫ j = (CochainComplex.single₀ C).map S.f ≫ IB.ι ∧
      IB.ι ≫ q = (CochainComplex.single₀ C).map S.g ≫ IC.ι ∧
      (∀ n, j.f n =
        eqToHom (congrArg (fun K : CochainComplex C ℕ => K.X n) hA) ≫ biprod.inl ≫
          eqToHom (congrArg (fun K : CochainComplex C ℕ => K.X n) hB.symm)) ∧
      (∀ n, q.f n =
        eqToHom (congrArg (fun K : CochainComplex C ℕ => K.X n) hB) ≫ biprod.snd ≫
          eqToHom (congrArg (fun K : CochainComplex C ℕ => K.X n) hC.symm)) ∧
      (ShortComplex.mk j q w).ShortExact ∧
      (∀ n, ((ShortComplex.mk j q w).map
        (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).ShortExact ∧
        Nonempty (((ShortComplex.mk j q w).map
          (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).Splitting)) := by
  let jm := mapOfConsecutive L (fun n => L n ⊞ R n)
    (fun n => rA n ≫ eA (n + 1)) (fun n => rB n ≫ eB (n + 1)) sqA sqB
    (fun _ => biprod.inl) (inclusion_comm T L R eA eB rA rB hel hrl)
  let qm := mapOfConsecutive (fun n => L n ⊞ R n) R
    (fun n => rB n ≫ eB (n + 1)) (fun n => rC n ≫ eC (n + 1)) sqB sqC
    (fun _ => biprod.snd) (projection_comm T L R eB eC rB rC her hrr)
  let j := eqToHom hA ≫ jm ≫ eqToHom hB.symm
  let q := eqToHom hB ≫ qm ≫ eqToHom hC.symm
  have hj := fun n => mapTransport_f _ _ _ _ hA hB jm n
  have hq := fun n => mapTransport_f _ _ _ _ hB hC qm n
  have w : j ≫ q = 0 := strict_zero _ _ _ L R
    (fun n => congrArg (fun K : CochainComplex C ℕ => K.X n) hA)
    (fun n => congrArg (fun K : CochainComplex C ℕ => K.X n) hB)
    (fun n => congrArg (fun K : CochainComplex C ℕ => K.X n) hC) j q hj hq
  have ha := augmentation_squares S hS T h0 L R eA eB eC rA rB rC
    hel her hrl hrr sqA sqB sqC IA IB IC hA hB hC haA haB haC j q hj hq
  let row := ShortComplex.mk j q w
  have sp (n : ℕ) :
      (row.map (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).Splitting :=
    splittingOfComponents _ _ _ (L n) (R n)
      (congrArg (fun K : CochainComplex C ℕ => K.X n) hA)
      (congrArg (fun K : CochainComplex C ℕ => K.X n) hB)
      (congrArg (fun K : CochainComplex C ℕ => K.X n) hC)
      (j.f n) (q.f n) (hj n) (hq n)
      (row.map (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).zero
  exact ⟨j, q, w, ha.1, ha.2, hj, hq,
    HomologicalComplex.shortExact_of_degreewise_shortExact row (fun n => (sp n).shortExact),
    fun n => ⟨(sp n).shortExact, ⟨sp n⟩⟩⟩

end CategoryTheory.InjectiveResolution

namespace CategoryTheory.InjectiveResolution

open CategoryTheory CategoryTheory.Limits
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Exactness makes the differential induced out of the cokernel monic. Its next
composite is zero by cancellation of the epic quotient, and the quotient comparison
transports the next exact pair. This is the single-column induction in PD-L10. -/
private theorem column_successor
    {X J K L : C} (e : X ⟶ J) [Mono e] (d : J ⟶ K) (d' : K ⟶ L)
    (w : e ≫ d = 0) (h : (ShortComplex.mk e d w).Exact)
    (wd : d ≫ d' = 0) (hd : (ShortComplex.mk d d' wd).Exact) :
    ∃ w' : cokernel.desc e d w ≫ d' = 0,
      Mono (cokernel.desc e d w) ∧
      (ShortComplex.mk (cokernel.desc e d w) d' w').Exact := by
  have w' : cokernel.desc e d w ≫ d' = 0 := by
    apply (cancel_epi (cokernel.π e)).1
    rw [← Category.assoc, cokernel.π_desc, wd, comp_zero]
  refine ⟨w', h.mono_cokernelDesc, ?_⟩
  let φ : ShortComplex.mk d d' wd ⟶
      ShortComplex.mk (cokernel.desc e d w) d' w' :=
    ShortComplex.homMk (cokernel.π e) (𝟙 K) (𝟙 L) (by simp) (by simp)
  let : Epi φ.τ₁ := (inferInstance : Epi (cokernel.π e))
  let : IsIso φ.τ₂ := (inferInstance : IsIso (𝟙 K))
  let : Mono φ.τ₃ := (inferInstance : Mono (𝟙 L))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hd

/-- Evaluate the supplied strict sequence in its original degree; no complex is replaced. -/
private abbrev evaluatedRow {A B D : CochainComplex C ℕ}
    (j : A ⟶ B) (q : B ⟶ D) (w : j ≫ q = 0) (n : ℕ) :=
  (ShortComplex.mk j q w).map (HomologicalComplex.eval C (ComplexShape.up ℕ) n)

/-- The original cochain commutation laws make the three differentials a map of rows. -/
private def rowDifferential {A B D : CochainComplex C ℕ}
    (j : A ⟶ B) (q : B ⟶ D) (w : j ≫ q = 0) (n : ℕ) :
    evaluatedRow j q w n ⟶ evaluatedRow j q w (n + 1) :=
  ShortComplex.homMk (A.d n (n + 1)) (B.d n (n + 1)) (D.d n (n + 1))
    (j.comm n (n + 1)).symm (q.comm n (n + 1)).symm

/-- The given augmentation squares, evaluated in degree zero, form the initial row map. -/
private def initialEmbedding
    (S : ShortComplex C) (IA : InjectiveResolution S.X₁)
    (IB : InjectiveResolution S.X₂) (IC : InjectiveResolution S.X₃)
    (j : IA.cocomplex ⟶ IB.cocomplex) (q : IB.cocomplex ⟶ IC.cocomplex)
    (w : j ≫ q = 0)
    (ha : IA.ι ≫ j = (CochainComplex.single₀ C).map S.f ≫ IB.ι)
    (hb : IB.ι ≫ q = (CochainComplex.single₀ C).map S.g ≫ IC.ι) :
    S ⟶ evaluatedRow j q w 0 :=
  ShortComplex.homMk (IA.ι.f 0) (IB.ι.f 0) (IC.ι.f 0)
    (by
      change IA.ι.f 0 ≫ j.f 0 = S.f ≫ IB.ι.f 0
      simpa using HomologicalComplex.congr_hom ha 0)
    (by
      change IB.ι.f 0 ≫ q.f 0 = S.g ≫ IC.ι.f 0
      simpa using HomologicalComplex.congr_hom hb 0)

/-- After precomposition with the first epic quotient, the induced row composite
is the original zero row composite followed by the last quotient. Cancel that epic map. -/
private theorem quotientRow_zero {T E : ShortComplex C} (e : T ⟶ E) :
    cokernel.map e.τ₁ e.τ₂ T.f E.f e.comm₁₂ ≫
      cokernel.map e.τ₂ e.τ₃ T.g E.g e.comm₂₃ = 0 := by
  have ha : cokernel.π e.τ₁ ≫ cokernel.map e.τ₁ e.τ₂ T.f E.f e.comm₁₂ =
      E.f ≫ cokernel.π e.τ₂ := cokernel.π_desc _ _ _
  have hb : cokernel.π e.τ₂ ≫ cokernel.map e.τ₂ e.τ₃ T.g E.g e.comm₂₃ =
      E.g ≫ cokernel.π e.τ₃ := cokernel.π_desc _ _ _
  apply (cancel_epi (cokernel.π e.τ₁)).1
  rw [← Category.assoc, ha, Category.assoc, hb, ← Category.assoc,
    E.zero, zero_comp, comp_zero]

/-- The successor row uses the three actual component cokernels and their induced arrows. -/
private def quotientRow {T E : ShortComplex C} (e : T ⟶ E) : ShortComplex C :=
  ShortComplex.mk (cokernel.map e.τ₁ e.τ₂ T.f E.f e.comm₁₂)
    (cokernel.map e.τ₂ e.τ₃ T.g E.g e.comm₂₃) (quotientRow_zero e)

/-- The three canonical quotient maps form a row map by their universal properties. -/
private def quotientMap {T E : ShortComplex C} (e : T ⟶ E) : E ⟶ quotientRow e :=
  ShortComplex.homMk (cokernel.π e.τ₁) (cokernel.π e.τ₂) (cokernel.π e.τ₃)
    (cokernel.π_desc _ _ _) (cokernel.π_desc _ _ _)

/-- Apply the snake lemma to the two short exact rows and their componentwise
monic map. It gives middle exactness; the zero kernel of the right monomorphism
gives the initial zero arrow and hence the successor monomorphism. The original
last epimorphism and quotient square give the successor epimorphism. -/
private theorem quotientRow_shortExact {T E : ShortComplex C}
    (hT : T.ShortExact) (hE : E.ShortExact)
    (e : T ⟶ E) [Mono e.τ₁] [Mono e.τ₂] [Mono e.τ₃] :
    (quotientRow e).ShortExact := by
  let r := quotientMap e
  have w : e ≫ r = 0 := by
    apply ShortComplex.hom_ext
    · exact cokernel.condition e.τ₁
    · exact cokernel.condition e.τ₂
    · exact cokernel.condition e.τ₃
  have hc : IsColimit (CokernelCofork.ofπ r w) := by
    apply ShortComplex.isColimitOfIsColimitπ
    · exact (isColimitMapCoconeCoforkEquiv' ShortComplex.π₁ w).symm
        (cokernelIsCokernel e.τ₁)
    · exact (isColimitMapCoconeCoforkEquiv' ShortComplex.π₂ w).symm
        (cokernelIsCokernel e.τ₂)
    · exact (isColimitMapCoconeCoforkEquiv' ShortComplex.π₃ w).symm
        (cokernelIsCokernel e.τ₃)
  let D : ShortComplex.SnakeInput C :=
    { L₀ := kernel e, L₁ := T, L₂ := E, L₃ := quotientRow e
      v₀₁ := kernel.ι e, v₁₂ := e, v₂₃ := r
      w₀₂ := kernel.condition e, w₁₃ := w
      h₀ := kernelIsKernel e, h₃ := hc
      L₁_exact := hT.exact, epi_L₁_g := hT.epi_g
      L₂_exact := hE.exact, mono_L₂_f := hE.mono_f }
  let : Mono D.v₁₂.τ₃ := (inferInstance : Mono e.τ₃)
  have hz : IsZero D.L₀.X₃ := KernelFork.IsLimit.isZero_of_mono D.h₀τ₃
  have hzero : D.L₂'.f = 0 := hz.eq_of_src _ _
  have hm : Mono (quotientRow e).f := D.L₂'_exact.mono_g hzero
  let : Epi E.g := hE.epi_g
  let : Epi (E.g ≫ (quotientMap e).τ₃) :=
    (inferInstance : Epi (E.g ≫ cokernel.π e.τ₃))
  have hep : Epi (quotientRow e).g := epi_of_epi_fac (quotientMap e).comm₂₃
  exact { exact := D.L₃_exact, mono_f := hm, epi_g := hep }

/-- Precompose each desired descended square with its epic cokernel quotient.
The quotient restrictions reduce it to the original differential square; epic
cancellation gives both strict row squares. -/
private theorem descended_squares {T E F : ShortComplex C}
    (e : T ⟶ E) (d : E ⟶ F) (w : e ≫ d = 0) :
    (cokernel.desc e.τ₁ d.τ₁ (congrArg (fun f : T ⟶ F => f.τ₁) w)) ≫ F.f =
      (quotientRow e).f ≫
        (cokernel.desc e.τ₂ d.τ₂ (congrArg (fun f : T ⟶ F => f.τ₂) w)) ∧
    (cokernel.desc e.τ₂ d.τ₂ (congrArg (fun f : T ⟶ F => f.τ₂) w)) ≫ F.g =
      (quotientRow e).g ≫
        (cokernel.desc e.τ₃ d.τ₃ (congrArg (fun f : T ⟶ F => f.τ₃) w)) := by
  constructor
  · have hq : cokernel.π e.τ₁ ≫ cokernel.map e.τ₁ e.τ₂ T.f E.f e.comm₁₂ =
        E.f ≫ cokernel.π e.τ₂ := cokernel.π_desc _ _ _
    apply (cancel_epi (cokernel.π e.τ₁)).1
    change cokernel.π e.τ₁ ≫
      (cokernel.desc e.τ₁ d.τ₁ (congrArg (fun f : T ⟶ F => f.τ₁) w) ≫ F.f) =
      cokernel.π e.τ₁ ≫ (cokernel.map e.τ₁ e.τ₂ T.f E.f e.comm₁₂ ≫
        cokernel.desc e.τ₂ d.τ₂ (congrArg (fun f : T ⟶ F => f.τ₂) w))
    rw [← Category.assoc,
      cokernel.π_desc e.τ₁ d.τ₁ (congrArg (fun f : T ⟶ F => f.τ₁) w),
      ← Category.assoc, hq, Category.assoc,
      cokernel.π_desc e.τ₂ d.τ₂ (congrArg (fun f : T ⟶ F => f.τ₂) w)]
    exact d.comm₁₂
  · have hq : cokernel.π e.τ₂ ≫ cokernel.map e.τ₂ e.τ₃ T.g E.g e.comm₂₃ =
        E.g ≫ cokernel.π e.τ₃ := cokernel.π_desc _ _ _
    apply (cancel_epi (cokernel.π e.τ₂)).1
    change cokernel.π e.τ₂ ≫
      (cokernel.desc e.τ₂ d.τ₂ (congrArg (fun f : T ⟶ F => f.τ₂) w) ≫ F.g) =
      cokernel.π e.τ₂ ≫ (cokernel.map e.τ₂ e.τ₃ T.g E.g e.comm₂₃ ≫
        cokernel.desc e.τ₃ d.τ₃ (congrArg (fun f : T ⟶ F => f.τ₃) w))
    rw [← Category.assoc,
      cokernel.π_desc e.τ₂ d.τ₂ (congrArg (fun f : T ⟶ F => f.τ₂) w),
      ← Category.assoc, hq, Category.assoc,
      cokernel.π_desc e.τ₃ d.τ₃ (congrArg (fun f : T ⟶ F => f.τ₃) w)]
    exact d.comm₂₃

/-- Bundle the three induced differentials using the two descended strict squares. -/
private def descendedEmbedding {T E F : ShortComplex C}
    (e : T ⟶ E) (d : E ⟶ F) (w : e ≫ d = 0) : quotientRow e ⟶ F :=
  ShortComplex.homMk
    (cokernel.desc e.τ₁ d.τ₁ (congrArg (fun f : T ⟶ F => f.τ₁) w))
    (cokernel.desc e.τ₂ d.τ₂ (congrArg (fun f : T ⟶ F => f.τ₂) w))
    (cokernel.desc e.τ₃ d.τ₃ (congrArg (fun f : T ⟶ F => f.τ₃) w))
    (descended_squares e d w).1 (descended_squares e d w).2

/-- At each fixed original degree retain the short exact row, monic embedding
and the three exact pairs needed to take the next cokernels. -/
private structure PresentationState (E : ℕ → ShortComplex C)
    (d : ∀ n, E n ⟶ E (n + 1)) (n : ℕ) where
  T : ShortComplex C
  exactRow : T.ShortExact
  e : T ⟶ E n
  monoA : Mono e.τ₁
  monoB : Mono e.τ₂
  monoC : Mono e.τ₃
  zero : e ≫ d n = 0
  exactA : (ShortComplex.mk e.τ₁ (d n).τ₁
    (congrArg (fun f : T ⟶ E (n + 1) => f.τ₁) zero)).Exact
  exactB : (ShortComplex.mk e.τ₂ (d n).τ₂
    (congrArg (fun f : T ⟶ E (n + 1) => f.τ₂) zero)).Exact
  exactC : (ShortComplex.mk e.τ₃ (d n).τ₃
    (congrArg (fun f : T ⟶ E (n + 1) => f.τ₃) zero)).Exact


/-- The original augmentations kill the first differentials. Each supplied
resolution identifies its augmented object with the kernel of that differential,
so the three initial column pairs are exact. -/
private theorem initial_exact
    (S : ShortComplex C) (IA : InjectiveResolution S.X₁)
    (IB : InjectiveResolution S.X₂) (IC : InjectiveResolution S.X₃)
    (j : IA.cocomplex ⟶ IB.cocomplex) (q : IB.cocomplex ⟶ IC.cocomplex)
    (w : j ≫ q = 0)
    (ha : IA.ι ≫ j = (CochainComplex.single₀ C).map S.f ≫ IB.ι)
    (hb : IB.ι ≫ q = (CochainComplex.single₀ C).map S.g ≫ IC.ι) :
    let a := initialEmbedding S IA IB IC j q w ha hb
    let d := rowDifferential j q w 0
    ∃ wz : a ≫ d = 0,
      (ShortComplex.mk a.τ₁ d.τ₁
        (congrArg (fun f : S ⟶ evaluatedRow j q w 1 => f.τ₁) wz)).Exact ∧
      (ShortComplex.mk a.τ₂ d.τ₂
        (congrArg (fun f : S ⟶ evaluatedRow j q w 1 => f.τ₂) wz)).Exact ∧
      (ShortComplex.mk a.τ₃ d.τ₃
        (congrArg (fun f : S ⟶ evaluatedRow j q w 1 => f.τ₃) wz)).Exact := by
  have wz : initialEmbedding S IA IB IC j q w ha hb ≫ rowDifferential j q w 0 = 0 := by
    apply ShortComplex.hom_ext
    · exact IA.ι_f_zero_comp_complex_d
    · exact IB.ι_f_zero_comp_complex_d
    · exact IC.ι_f_zero_comp_complex_d
  exact ⟨wz, ShortComplex.exact_of_f_is_kernel _ IA.isLimitKernelFork,
    ShortComplex.exact_of_f_is_kernel _ IB.isLimitKernelFork,
    ShortComplex.exact_of_f_is_kernel _ IC.isLimitKernelFork⟩

/-- The original short exact row and augmentations give the initial presentation state. -/
private def initialState
    (S : ShortComplex C) (hS : S.ShortExact)
    (IA : InjectiveResolution S.X₁) (IB : InjectiveResolution S.X₂)
    (IC : InjectiveResolution S.X₃)
    (j : IA.cocomplex ⟶ IB.cocomplex) (q : IB.cocomplex ⟶ IC.cocomplex)
    (w : j ≫ q = 0)
    (ha : IA.ι ≫ j = (CochainComplex.single₀ C).map S.f ≫ IB.ι)
    (hb : IB.ι ≫ q = (CochainComplex.single₀ C).map S.g ≫ IC.ι) :
    PresentationState (evaluatedRow j q w) (rowDifferential j q w) 0 := by
  let wz := Classical.choose (initial_exact S IA IB IC j q w ha hb)
  have hA := (Classical.choose_spec (initial_exact S IA IB IC j q w ha hb)).1
  have hB := (Classical.choose_spec (initial_exact S IA IB IC j q w ha hb)).2.1
  have hC := (Classical.choose_spec (initial_exact S IA IB IC j q w ha hb)).2.2
  exact { T := S, exactRow := hS, e := initialEmbedding S IA IB IC j q w ha hb
          monoA := (inferInstance : Mono (IA.ι.f 0))
          monoB := (inferInstance : Mono (IB.ι.f 0))
          monoC := (inferInstance : Mono (IC.ι.f 0))
          zero := wz, exactA := hA, exactB := hB, exactC := hC }

/-- Take the canonical cokernel row and descend the original differential.
The three column successor receipts supply monicity and exactness, while the
snake receipt supplies the successor short exact row. -/
private def nextState
    (E : ℕ → ShortComplex C) (d : ∀ n, E n ⟶ E (n + 1))
    (n : ℕ) (s : PresentationState E d n) (hE : (E n).ShortExact)
    (wd : d n ≫ d (n + 1) = 0)
    (hdA : (ShortComplex.mk (d n).τ₁ (d (n + 1)).τ₁
      (congrArg (fun f : E n ⟶ E (n + 2) => f.τ₁) wd)).Exact)
    (hdB : (ShortComplex.mk (d n).τ₂ (d (n + 1)).τ₂
      (congrArg (fun f : E n ⟶ E (n + 2) => f.τ₂) wd)).Exact)
    (hdC : (ShortComplex.mk (d n).τ₃ (d (n + 1)).τ₃
      (congrArg (fun f : E n ⟶ E (n + 2) => f.τ₃) wd)).Exact) :
    PresentationState E d (n + 1) := by
  let : Mono s.e.τ₁ := s.monoA
  let : Mono s.e.τ₂ := s.monoB
  let : Mono s.e.τ₃ := s.monoC
  let hAall := column_successor s.e.τ₁ (d n).τ₁ (d (n + 1)).τ₁
    _ s.exactA _ hdA
  let wA := Classical.choose hAall
  have mA := (Classical.choose_spec hAall).1
  have hA := (Classical.choose_spec hAall).2
  let hBall := column_successor s.e.τ₂ (d n).τ₂ (d (n + 1)).τ₂
    _ s.exactB _ hdB
  let wB := Classical.choose hBall
  have mB := (Classical.choose_spec hBall).1
  have hB := (Classical.choose_spec hBall).2
  let hCall := column_successor s.e.τ₃ (d n).τ₃ (d (n + 1)).τ₃
    _ s.exactC _ hdC
  let wC := Classical.choose hCall
  have mC := (Classical.choose_spec hCall).1
  have hC := (Classical.choose_spec hCall).2
  have wz : descendedEmbedding s.e (d n) s.zero ≫ d (n + 1) = 0 := by
    apply ShortComplex.hom_ext
    · exact wA
    · exact wB
    · exact wC
  exact { T := quotientRow s.e, exactRow := quotientRow_shortExact s.exactRow hE s.e
          e := descendedEmbedding s.e (d n) s.zero
          monoA := mA, monoB := mB, monoC := mC
          zero := wz, exactA := hA, exactB := hB, exactC := hC }

/-- The original three differential-square identities form a zero row composite. -/
private theorem originalDZero {A B D : CochainComplex C ℕ}
    (j : A ⟶ B) (q : B ⟶ D) (w : j ≫ q = 0) (n : ℕ) :
    rowDifferential j q w n ≫ rowDifferential j q w (n + 1) = 0 := by
  apply ShortComplex.hom_ext
  · exact A.d_comp_d n (n + 1) (n + 2)
  · exact B.d_comp_d n (n + 1) (n + 2)
  · exact D.d_comp_d n (n + 1) (n + 2)


/-- Iterate the presentation successor over natural-number degrees while keeping
the original degree rows and differentials fixed. -/
private def presentationTower
    (E : ℕ → ShortComplex C) (d : ∀ n, E n ⟶ E (n + 1))
    (initial : PresentationState E d 0)
    (next : ∀ n, PresentationState E d n → PresentationState E d (n + 1)) :
    ∀ n, PresentationState E d n
  | 0 => initial
  | n + 1 => next n (presentationTower E d initial next n)


/-- Every supplied compatible triple of nonnegative injective resolutions has
recursive short exact presentations. Start with its given augmentations, take
actual cokernels, and descend the original differentials. Degreewise injectivity
splits each original row; these splittings need not commute with differentials.
The same witnesses retain all quotient universal properties, strict row squares
and differential factorizations (PD-L10, PD7–PD8). -/
public theorem exists_presentations_of_compatible_resolutions
    (S : ShortComplex C) (hS : S.ShortExact)
    (IA : InjectiveResolution S.X₁) (IB : InjectiveResolution S.X₂)
    (IC : InjectiveResolution S.X₃)
    (j : IA.cocomplex ⟶ IB.cocomplex) (q : IB.cocomplex ⟶ IC.cocomplex)
    (w : j ≫ q = 0)
    (ha : IA.ι ≫ j = (CochainComplex.single₀ C).map S.f ≫ IB.ι)
    (hb : IB.ι ≫ q = (CochainComplex.single₀ C).map S.g ≫ IC.ι)
    (he : ∀ n, ((ShortComplex.mk j q w).map
      (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).ShortExact) :
    let E := fun n => (ShortComplex.mk j q w).map
      (HomologicalComplex.eval C (ComplexShape.up ℕ) n)
    (∀ n, Nonempty (E n).Splitting) ∧
    ∃ (T : ℕ → ShortComplex C) (h0 : T 0 = S)
      (e : ∀ n, T n ⟶ E n) (r : ∀ n, E n ⟶ T (n + 1)),
      (∀ n, (T n).ShortExact) ∧
      (e 0).τ₁ = eqToHom (congrArg (fun U : ShortComplex C => U.X₁) h0) ≫ IA.ι.f 0 ∧
      (e 0).τ₂ = eqToHom (congrArg (fun U : ShortComplex C => U.X₂) h0) ≫ IB.ι.f 0 ∧
      (e 0).τ₃ = eqToHom (congrArg (fun U : ShortComplex C => U.X₃) h0) ≫ IC.ι.f 0 ∧
      (∀ n, ∃ wA : (e n).τ₁ ≫ (r n).τ₁ = 0,
        (ShortComplex.mk (e n).τ₁ (r n).τ₁ wA).ShortExact ∧
        Nonempty (IsColimit (CokernelCofork.ofπ (r n).τ₁ wA))) ∧
      (∀ n, ∃ wB : (e n).τ₂ ≫ (r n).τ₂ = 0,
        (ShortComplex.mk (e n).τ₂ (r n).τ₂ wB).ShortExact ∧
        Nonempty (IsColimit (CokernelCofork.ofπ (r n).τ₂ wB))) ∧
      (∀ n, ∃ wC : (e n).τ₃ ≫ (r n).τ₃ = 0,
        (ShortComplex.mk (e n).τ₃ (r n).τ₃ wC).ShortExact ∧
        Nonempty (IsColimit (CokernelCofork.ofπ (r n).τ₃ wC))) ∧
      (∀ n, (r n).τ₁ ≫ (e (n + 1)).τ₁ = IA.cocomplex.d n (n + 1)) ∧
      (∀ n, (r n).τ₂ ≫ (e (n + 1)).τ₂ = IB.cocomplex.d n (n + 1)) ∧
      (∀ n, (r n).τ₃ ≫ (e (n + 1)).τ₃ = IC.cocomplex.d n (n + 1))
 := by
  let E := evaluatedRow j q w
  let d := rowDifferential j q w
  let next (n : ℕ) (s : PresentationState E d n) :=
    nextState E d n s (he n) (originalDZero j q w n)
      (IA.exact_succ n) (IB.exact_succ n) (IC.exact_succ n)
  let t := presentationTower E d (initialState S hS IA IB IC j q w ha hb) next
  refine ⟨?_, (fun n => (t n).T), rfl, (fun n => (t n).e),
    (fun n => quotientMap (t n).e), (fun n => (t n).exactRow), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    let : Injective (E n).X₁ := IA.injective n
    exact ⟨(he n).splittingOfInjective⟩
  · change IA.ι.f 0 = (𝟙 _) ≫ IA.ι.f 0
    exact (Category.id_comp _).symm
  · change IB.ι.f 0 = (𝟙 _) ≫ IB.ι.f 0
    exact (Category.id_comp _).symm
  · change IC.ι.f 0 = (𝟙 _) ≫ IC.ι.f 0
    exact (Category.id_comp _).symm
  · intro n
    let : Mono (t n).e.τ₁ := (t n).monoA
    exact ⟨cokernel.condition _,
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
        mono_f := inferInstance, epi_g := (inferInstance : Epi (cokernel.π (t n).e.τ₁)) }, ⟨cokernelIsCokernel _⟩⟩
  · intro n
    let : Mono (t n).e.τ₂ := (t n).monoB
    exact ⟨cokernel.condition _,
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
        mono_f := inferInstance, epi_g := (inferInstance : Epi (cokernel.π (t n).e.τ₂)) }, ⟨cokernelIsCokernel _⟩⟩
  · intro n
    let : Mono (t n).e.τ₃ := (t n).monoC
    exact ⟨cokernel.condition _,
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
        mono_f := inferInstance, epi_g := (inferInstance : Epi (cokernel.π (t n).e.τ₃)) }, ⟨cokernelIsCokernel _⟩⟩
  · intro n
    exact cokernel.π_desc _ _ _
  · intro n
    exact cokernel.π_desc _ _ _
  · intro n
    exact cokernel.π_desc _ _ _

end CategoryTheory.InjectiveResolution

namespace CategoryTheory.InjectiveResolution
open CategoryTheory CategoryTheory.Limits
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Extend the current whole-row map along the monic embedding into the specified
split injective target. This preserves both sequence squares at once (PD-L12, PD12). -/
private theorem stage_extension {T E T' E' : ShortComplex C}
    (hT : T.ShortExact) (hE : E.ShortExact) (e : T ⟶ E)
    [Mono e.τ₁] [Mono e.τ₂] [Mono e.τ₃]
    (e' : T' ⟶ E') (s : E'.Splitting)
    [Injective E'.X₁] [Injective E'.X₃] (f : T ⟶ T') :
    ∃ u : E ⟶ E', e ≫ u = f ≫ e' :=
  ShortComplex.ShortExact.exists_extension_to_split_injective hT hE e s (f ≫ e')

/-- Project the extension equation to each component and follow by the target
quotient. Its composite with the target embedding is zero, so all three maps
annihilate the source embedding and can descend to its cokernel. -/
private theorem stage_kills {T E T' E' Q' : ShortComplex C}
    (e : T ⟶ E) (e' : T' ⟶ E') (r' : E' ⟶ Q')
    (z' : e' ≫ r' = 0) (f : T ⟶ T') (u : E ⟶ E')
    (hu : e ≫ u = f ≫ e') :
    e.τ₁ ≫ (u.τ₁ ≫ r'.τ₁) = 0 ∧
    e.τ₂ ≫ (u.τ₂ ≫ r'.τ₂) = 0 ∧
    e.τ₃ ≫ (u.τ₃ ≫ r'.τ₃) = 0 := by
  have h₁ : e.τ₁ ≫ u.τ₁ = f.τ₁ ≫ e'.τ₁ :=
    congrArg (fun t : T ⟶ E' => t.τ₁) hu
  have z₁ : e'.τ₁ ≫ r'.τ₁ = 0 :=
    congrArg (fun t : T' ⟶ Q' => t.τ₁) z'
  have h₂ : e.τ₂ ≫ u.τ₂ = f.τ₂ ≫ e'.τ₂ :=
    congrArg (fun t : T ⟶ E' => t.τ₂) hu
  have z₂ : e'.τ₂ ≫ r'.τ₂ = 0 :=
    congrArg (fun t : T' ⟶ Q' => t.τ₂) z'
  have h₃ : e.τ₃ ≫ u.τ₃ = f.τ₃ ≫ e'.τ₃ :=
    congrArg (fun t : T ⟶ E' => t.τ₃) hu
  have z₃ : e'.τ₃ ≫ r'.τ₃ = 0 :=
    congrArg (fun t : T' ⟶ Q' => t.τ₃) z'
  refine ⟨?_, ?_, ?_⟩
  · rw [← Category.assoc, h₁, Category.assoc, z₁, comp_zero]
  · rw [← Category.assoc, h₂, Category.assoc, z₂, comp_zero]
  · rw [← Category.assoc, h₃, Category.assoc, z₃, comp_zero]

/-- Descend a map through the supplied actual cokernel universal property. -/
private def actualDesc {A B Q Z : C} (e : A ⟶ B) (r : B ⟶ Q)
    (z : e ≫ r = 0) (hr : IsColimit (CokernelCofork.ofπ r z))
    (k : B ⟶ Z) (hk : e ≫ k = 0) : Q ⟶ Z :=
  hr.desc (CokernelCofork.ofπ k hk)

/-- The descended map retains its defining quotient equation (PD13 component). -/
private theorem actualDesc_fac {A B Q Z : C} (e : A ⟶ B) (r : B ⟶ Q)
    (z : e ≫ r = 0) (hr : IsColimit (CokernelCofork.ofπ r z))
    (k : B ⟶ Z) (hk : e ≫ k = 0) :
    r ≫ actualDesc e r z hr k hk = k := Cofork.IsColimit.π_desc hr

/-- Precompose each proposed successor square with its epic quotient map.
The restrictions and the three original row morphisms give equality there;
epic cancellation proves both strict successor squares. -/
private theorem comparisonDescendedSquares {E Q E' Q' : ShortComplex C}
    (r : E ⟶ Q) (r' : E' ⟶ Q') (u : E ⟶ E')
    [Epi r.τ₁] [Epi r.τ₂]
    (a : Q.X₁ ⟶ Q'.X₁) (b : Q.X₂ ⟶ Q'.X₂) (c : Q.X₃ ⟶ Q'.X₃)
    (ha : r.τ₁ ≫ a = u.τ₁ ≫ r'.τ₁)
    (hb : r.τ₂ ≫ b = u.τ₂ ≫ r'.τ₂)
    (hc : r.τ₃ ≫ c = u.τ₃ ≫ r'.τ₃) :
    a ≫ Q'.f = Q.f ≫ b ∧ b ≫ Q'.g = Q.g ≫ c := by
  constructor
  · apply (cancel_epi r.τ₁).1
    calc
      r.τ₁ ≫ (a ≫ Q'.f) = (u.τ₁ ≫ r'.τ₁) ≫ Q'.f := by rw [← Category.assoc, ha]
      _ = u.τ₁ ≫ (E'.f ≫ r'.τ₂) := by rw [Category.assoc, r'.comm₁₂]
      _ = E.f ≫ (u.τ₂ ≫ r'.τ₂) := by rw [← Category.assoc, u.comm₁₂, Category.assoc]
      _ = E.f ≫ (r.τ₂ ≫ b) := by rw [hb]
      _ = r.τ₁ ≫ (Q.f ≫ b) := by rw [← Category.assoc, ← r.comm₁₂, Category.assoc]
  · apply (cancel_epi r.τ₂).1
    calc
      r.τ₂ ≫ (b ≫ Q'.g) = (u.τ₂ ≫ r'.τ₂) ≫ Q'.g := by rw [← Category.assoc, hb]
      _ = u.τ₂ ≫ (E'.g ≫ r'.τ₃) := by rw [Category.assoc, r'.comm₂₃]
      _ = E.g ≫ (u.τ₃ ≫ r'.τ₃) := by rw [← Category.assoc, u.comm₂₃, Category.assoc]
      _ = E.g ≫ (r.τ₃ ≫ c) := by rw [hc]
      _ = r.τ₂ ≫ (Q.g ≫ c) := by rw [← Category.assoc, ← r.comm₂₃, Category.assoc]

/-- The three descended components and their two squares form one row morphism. -/
private def descendedRow {E Q E' Q' : ShortComplex C}
    (r : E ⟶ Q) (r' : E' ⟶ Q') (u : E ⟶ E')
    [Epi r.τ₁] [Epi r.τ₂]
    (a : Q.X₁ ⟶ Q'.X₁) (b : Q.X₂ ⟶ Q'.X₂) (c : Q.X₃ ⟶ Q'.X₃)
    (ha : r.τ₁ ≫ a = u.τ₁ ≫ r'.τ₁)
    (hb : r.τ₂ ≫ b = u.τ₂ ≫ r'.τ₂)
    (hc : r.τ₃ ≫ c = u.τ₃ ≫ r'.τ₃) : Q ⟶ Q' :=
  ShortComplex.homMk a b c (comparisonDescendedSquares r r' u a b c ha hb hc).1
    (comparisonDescendedSquares r r' u a b c ha hb hc).2

/-- Bundle the three quotient restrictions into the whole-row equation PD13. -/
private theorem descendedRow_fac {E Q E' Q' : ShortComplex C}
    (r : E ⟶ Q) (r' : E' ⟶ Q') (u : E ⟶ E')
    [Epi r.τ₁] [Epi r.τ₂]
    (a : Q.X₁ ⟶ Q'.X₁) (b : Q.X₂ ⟶ Q'.X₂) (c : Q.X₃ ⟶ Q'.X₃)
    (ha : r.τ₁ ≫ a = u.τ₁ ≫ r'.τ₁)
    (hb : r.τ₂ ≫ b = u.τ₂ ≫ r'.τ₂)
    (hc : r.τ₃ ≫ c = u.τ₃ ≫ r'.τ₃) :
    r ≫ descendedRow r r' u a b c ha hb hc = u ≫ r' :=
  ShortComplex.hom_ext _ _ ha hb hc

/-- One recursive comparison stage retains the whole extension and its
simultaneous successor, together with PD12 and PD13. -/
private structure ComparisonStep {T E Q T' E' Q' : ShortComplex C}
    (e : T ⟶ E) (r : E ⟶ Q) (e' : T' ⟶ E') (r' : E' ⟶ Q')
    (f : T ⟶ T') where
  u : E ⟶ E'
  next : Q ⟶ Q'
  extension : e ≫ u = f ≫ e'
  descent : r ≫ next = u ≫ r'

/-- Choose one whole-row extension, then descend its three components through
the same supplied cokernels. Epic cancellation keeps the successor a row map. -/
private def comparisonStep {T E Q T' E' Q' : ShortComplex C}
    (hT : T.ShortExact) (hE : E.ShortExact)
    (e : T ⟶ E) (r : E ⟶ Q) (e' : T' ⟶ E') (r' : E' ⟶ Q')
    (hA : ∃ z : e.τ₁ ≫ r.τ₁ = 0,
      (ShortComplex.mk e.τ₁ r.τ₁ z).ShortExact ∧ Nonempty (IsColimit (CokernelCofork.ofπ r.τ₁ z)))
    (hB : ∃ z : e.τ₂ ≫ r.τ₂ = 0,
      (ShortComplex.mk e.τ₂ r.τ₂ z).ShortExact ∧ Nonempty (IsColimit (CokernelCofork.ofπ r.τ₂ z)))
    (hC : ∃ z : e.τ₃ ≫ r.τ₃ = 0,
      (ShortComplex.mk e.τ₃ r.τ₃ z).ShortExact ∧ Nonempty (IsColimit (CokernelCofork.ofπ r.τ₃ z)))
    (z' : e' ≫ r' = 0) (s : E'.Splitting)
    [Injective E'.X₁] [Injective E'.X₃] (f : T ⟶ T') :
    ComparisonStep e r e' r' f := by
  let zA := hA.choose
  let zB := hB.choose
  let zC := hC.choose
  let ca := hA.choose_spec.2.some
  let cb := hB.choose_spec.2.some
  let cc := hC.choose_spec.2.some
  let : Mono e.τ₁ := hA.choose_spec.1.mono_f
  let : Mono e.τ₂ := hB.choose_spec.1.mono_f
  let : Mono e.τ₃ := hC.choose_spec.1.mono_f
  let : Epi r.τ₁ := epi_of_isColimit_cofork ca
  let : Epi r.τ₂ := epi_of_isColimit_cofork cb
  let ex := stage_extension hT hE e e' s f
  let u := ex.choose
  have hu : e ≫ u = f ≫ e' := ex.choose_spec
  have hz := stage_kills e e' r' z' f u hu
  let a := actualDesc e.τ₁ r.τ₁ zA ca (u.τ₁ ≫ r'.τ₁) hz.1
  let b := actualDesc e.τ₂ r.τ₂ zB cb (u.τ₂ ≫ r'.τ₂) hz.2.1
  let c := actualDesc e.τ₃ r.τ₃ zC cc (u.τ₃ ≫ r'.τ₃) hz.2.2
  have ha : r.τ₁ ≫ a = u.τ₁ ≫ r'.τ₁ := actualDesc_fac _ _ _ _ _ _
  have hb : r.τ₂ ≫ b = u.τ₂ ≫ r'.τ₂ := actualDesc_fac _ _ _ _ _ _
  have hc : r.τ₃ ≫ c = u.τ₃ ≫ r'.τ₃ := actualDesc_fac _ _ _ _ _ _
  exact ⟨u, descendedRow r r' u a b c ha hb hc, hu,
    descendedRow_fac r r' u a b c ha hb hc⟩

/-- Iterate the successor operation on the unchanged supplied rows, starting
with the given original morphism. -/
private def comparisonTower (T T' : ℕ → ShortComplex C) (f0 : T 0 ⟶ T' 0)
    (next : ∀ n, (T n ⟶ T' n) → (T (n + 1) ⟶ T' (n + 1))) :
    ∀ n, T n ⟶ T' n
  | 0 => f0
  | n + 1 => next n (comparisonTower T T' f0 next n)

/-- Any original sequence morphism admits recursive whole-row comparisons on
the supplied compatible presentations. At each degree extend along the monic
embedding into the split injective target and descend through the actual three
cokernels. The same comparisons satisfy PD12 and PD13, with the given map in
degree zero; no monicity or epicity is required of that map (PD-L12). -/
public theorem exists_recursive_comparison
    {S S' : ShortComplex C} (f : S ⟶ S')
    (T E T' E' : ℕ → ShortComplex C) (h0 : T 0 = S) (h0' : T' 0 = S')
    (e : ∀ n, T n ⟶ E n) (r : ∀ n, E n ⟶ T (n + 1))
    (e' : ∀ n, T' n ⟶ E' n) (r' : ∀ n, E' n ⟶ T' (n + 1))
    (hT : ∀ n, (T n).ShortExact) (hE : ∀ n, (E n).ShortExact)
    (hA : ∀ n, ∃ z : (e n).τ₁ ≫ (r n).τ₁ = 0,
      (ShortComplex.mk (e n).τ₁ (r n).τ₁ z).ShortExact ∧
      Nonempty (IsColimit (CokernelCofork.ofπ (r n).τ₁ z)))
    (hB : ∀ n, ∃ z : (e n).τ₂ ≫ (r n).τ₂ = 0,
      (ShortComplex.mk (e n).τ₂ (r n).τ₂ z).ShortExact ∧
      Nonempty (IsColimit (CokernelCofork.ofπ (r n).τ₂ z)))
    (hC : ∀ n, ∃ z : (e n).τ₃ ≫ (r n).τ₃ = 0,
      (ShortComplex.mk (e n).τ₃ (r n).τ₃ z).ShortExact ∧
      Nonempty (IsColimit (CokernelCofork.ofπ (r n).τ₃ z)))
    (z' : ∀ n, e' n ≫ r' n = 0) (s' : ∀ n, Nonempty (E' n).Splitting)
    (hI : ∀ n, Injective (E' n).X₁) (hK : ∀ n, Injective (E' n).X₃) :
    ∃ (fn : ∀ n, T n ⟶ T' n) (un : ∀ n, E n ⟶ E' n),
      fn 0 = eqToHom h0 ≫ f ≫ eqToHom h0'.symm ∧
      (∀ n, e n ≫ un n = fn n ≫ e' n) ∧
      (∀ n, r n ≫ fn (n + 1) = un n ≫ r' n) := by
  let step (n : ℕ) (f : T n ⟶ T' n) :
      ComparisonStep (e n) (r n) (e' n) (r' n) f := by
    let : Injective (E' n).X₁ := hI n
    let : Injective (E' n).X₃ := hK n
    exact comparisonStep (hT n) (hE n) (e n) (r n) (e' n) (r' n)
      (hA n) (hB n) (hC n) (z' n) (s' n).some f
  let next (n : ℕ) (f : T n ⟶ T' n) := (step n f).next
  let fn := comparisonTower T T' (eqToHom h0 ≫ f ≫ eqToHom h0'.symm) next
  exact ⟨fn, (fun n => (step n (fn n)).u), rfl,
    (fun n => (step n (fn n)).extension), (fun n => (step n (fn n)).descent)⟩

end CategoryTheory.InjectiveResolution

namespace CategoryTheory.InjectiveResolution
open CategoryTheory CategoryTheory.Limits
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The quotient-embedding differential factorization and the two recursive
comparison equations give the five-term differential identity, in each position
of the original compatible triple (PD-L13, PD14). -/
private theorem comparisonDifferential (K K' : CochainComplex C ℕ)
    (X X' : ℕ → C)
    (e : ∀ n, X n ⟶ K.X n) (r : ∀ n, K.X n ⟶ X (n + 1))
    (e' : ∀ n, X' n ⟶ K'.X n) (r' : ∀ n, K'.X n ⟶ X' (n + 1))
    (fn : ∀ n, X n ⟶ X' n) (un : ∀ n, K.X n ⟶ K'.X n)
    (d : ∀ n, r n ≫ e (n + 1) = K.d n (n + 1))
    (d' : ∀ n, r' n ≫ e' (n + 1) = K'.d n (n + 1))
    (ext : ∀ n, e n ≫ un n = fn n ≫ e' n)
    (desc : ∀ n, r n ≫ fn (n + 1) = un n ≫ r' n) :
    ∀ n, un n ≫ K'.d n (n + 1) = K.d n (n + 1) ≫ un (n + 1) := by
  intro n
  symm
  calc
    K.d n (n + 1) ≫ un (n + 1) = (r n ≫ e (n + 1)) ≫ un (n + 1) := by rw [d n]
    _ = r n ≫ (fn (n + 1) ≫ e' (n + 1)) := by rw [Category.assoc, ext (n + 1)]
    _ = (un n ≫ r' n) ≫ e' (n + 1) := by rw [← Category.assoc, desc n]
    _ = un n ≫ K'.d n (n + 1) := by rw [Category.assoc, d' n]

/-- Package the same degreewise comparisons as a cochain map of the original
complexes, using their consecutive differential equations. -/
private def comparisonCochainMap (K K' : CochainComplex C ℕ)
    (un : ∀ n, K.X n ⟶ K'.X n)
    (h : ∀ n, un n ≫ K'.d n (n + 1) = K.d n (n + 1) ≫ un (n + 1)) : K ⟶ K' :=
  { f := un
    comm' := by
      intro i j hij
      obtain rfl : i + 1 = j := hij
      exact h i }

/-- Identify the initial rows with the original sequences. Projecting the
initial whole-row comparison equation and substituting the six original
augmentations proves the three augmentation equations. -/
private theorem comparisonInitialAugmentation {S S' T T' E E' : ShortComplex C}
    (f : S ⟶ S') (h0 : T = S) (h0' : T' = S')
    (e : T ⟶ E) (e' : T' ⟶ E') (u : E ⟶ E')
    (a : S.X₁ ⟶ E.X₁) (b : S.X₂ ⟶ E.X₂) (c : S.X₃ ⟶ E.X₃)
    (a' : S'.X₁ ⟶ E'.X₁) (b' : S'.X₂ ⟶ E'.X₂) (c' : S'.X₃ ⟶ E'.X₃)
    (ha : e.τ₁ = eqToHom (congrArg (fun U : ShortComplex C => U.X₁) h0) ≫ a)
    (hb : e.τ₂ = eqToHom (congrArg (fun U : ShortComplex C => U.X₂) h0) ≫ b)
    (hc : e.τ₃ = eqToHom (congrArg (fun U : ShortComplex C => U.X₃) h0) ≫ c)
    (ha' : e'.τ₁ = eqToHom (congrArg (fun U : ShortComplex C => U.X₁) h0') ≫ a')
    (hb' : e'.τ₂ = eqToHom (congrArg (fun U : ShortComplex C => U.X₂) h0') ≫ b')
    (hc' : e'.τ₃ = eqToHom (congrArg (fun U : ShortComplex C => U.X₃) h0') ≫ c')
    (h : e ≫ u = (eqToHom h0 ≫ f ≫ eqToHom h0'.symm) ≫ e') :
    a ≫ u.τ₁ = f.τ₁ ≫ a' ∧ b ≫ u.τ₂ = f.τ₂ ≫ b' ∧ c ≫ u.τ₃ = f.τ₃ ≫ c' := by
  cases h0
  cases h0'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at ha hb hc ha' hb' hc' h
  have h₁ : e.τ₁ ≫ u.τ₁ = f.τ₁ ≫ e'.τ₁ := congrArg (fun g => g.τ₁) h
  have h₂ : e.τ₂ ≫ u.τ₂ = f.τ₂ ≫ e'.τ₂ := congrArg (fun g => g.τ₂) h
  have h₃ : e.τ₃ ≫ u.τ₃ = f.τ₃ ≫ e'.τ₃ := congrArg (fun g => g.τ₃) h
  exact ⟨by simpa only [ha, ha'] using h₁,
    by simpa only [hb, hb'] using h₂, by simpa only [hc, hc'] using h₃⟩

/-- Equality out of the degree-zero single complex is detected in degree zero;
apply this to the original augmentation equation. -/
private theorem comparisonAugmentationFromZero (X Y : C) (K L : CochainComplex C ℕ)
    (a : (CochainComplex.single₀ C).obj X ⟶ K)
    (b : (CochainComplex.single₀ C).obj Y ⟶ L) (j : K ⟶ L) (f : X ⟶ Y)
    (h : a.f 0 ≫ j.f 0 = f ≫ b.f 0) :
    a ≫ j = (CochainComplex.single₀ C).map f ≫ b := by
  apply (CochainComplex.fromSingle₀Equiv L X).injective
  apply Subtype.ext
  change (a ≫ j).f 0 = ((CochainComplex.single₀ C).map f ≫ b).f 0
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero]
  exact h

/-- The two degreewise sequence squares give a strict map between the original
cochain sequences, by extensionality of cochain maps. -/
private def comparisonStrictMap (S S' : ShortComplex (CochainComplex C ℕ))
    (a : S.X₁ ⟶ S'.X₁) (b : S.X₂ ⟶ S'.X₂) (c : S.X₃ ⟶ S'.X₃)
    (ha : ∀ n, a.f n ≫ S'.f.f n = S.f.f n ≫ b.f n)
    (hb : ∀ n, b.f n ≫ S'.g.f n = S.g.f n ≫ c.f n) : S ⟶ S' :=
  ShortComplex.homMk a b c (HomologicalComplex.hom_ext _ _ ha)
    (HomologicalComplex.hom_ext _ _ hb)

/-- Every morphism of short exact sequences admits a strict simultaneous
comparison on any two supplied compatible injective resolution triples.
Use their recursive presentations and whole-row comparisons; PD14 supplies
the cochain equations, the row maps supply both strict sequence squares, and
PD12 at zero gives all three original augmentations. No monicity or epicity
of the given morphism is required (PD-L13). -/
public theorem exists_strict_comparison_of_compatible_resolutions (S S' : ShortComplex C) (hS : S.ShortExact) (hS' : S'.ShortExact)
    (f : S ⟶ S')
    (IA : InjectiveResolution S.X₁) (IB : InjectiveResolution S.X₂)
    (IC : InjectiveResolution S.X₃)
    (j : IA.cocomplex ⟶ IB.cocomplex) (q : IB.cocomplex ⟶ IC.cocomplex)
    (w : j ≫ q = 0)
    (ha : IA.ι ≫ j = (CochainComplex.single₀ C).map S.f ≫ IB.ι)
    (hb : IB.ι ≫ q = (CochainComplex.single₀ C).map S.g ≫ IC.ι)
    (he : ∀ n, ((ShortComplex.mk j q w).map
      (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).ShortExact)
    (IA' : InjectiveResolution S'.X₁) (IB' : InjectiveResolution S'.X₂)
    (IC' : InjectiveResolution S'.X₃)
    (j' : IA'.cocomplex ⟶ IB'.cocomplex) (q' : IB'.cocomplex ⟶ IC'.cocomplex)
    (w' : j' ≫ q' = 0)
    (ha' : IA'.ι ≫ j' = (CochainComplex.single₀ C).map S'.f ≫ IB'.ι)
    (hb' : IB'.ι ≫ q' = (CochainComplex.single₀ C).map S'.g ≫ IC'.ι)
    (he' : ∀ n, ((ShortComplex.mk j' q' w').map
      (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).ShortExact)
    : ∃ φ : ShortComplex.mk j q w ⟶ ShortComplex.mk j' q' w',
      IA.ι ≫ φ.τ₁ = (CochainComplex.single₀ C).map f.τ₁ ≫ IA'.ι ∧
      IB.ι ≫ φ.τ₂ = (CochainComplex.single₀ C).map f.τ₂ ≫ IB'.ι ∧
      IC.ι ≫ φ.τ₃ = (CochainComplex.single₀ C).map f.τ₃ ≫ IC'.ι := by
  obtain ⟨spl, T, h0, e, r, hT, a, b, c, A, B, D, da, db, dc⟩ :=
    exists_presentations_of_compatible_resolutions S hS IA IB IC j q w ha hb he
  obtain ⟨spl', T', h0', e', r', hT', a', b', c', A', B', D', da', db', dc'⟩ :=
    exists_presentations_of_compatible_resolutions S' hS' IA' IB' IC' j' q' w' ha' hb' he'
  have z' (n : ℕ) : e' n ≫ r' n = 0 :=
    ShortComplex.hom_ext _ _ (A' n).choose (B' n).choose (D' n).choose
  obtain ⟨fn, un, fzero, ext, desc⟩ :=
    exists_recursive_comparison f T _ T' _ h0 h0' e r e' r' hT he
      A B D z' spl' (fun n => IA'.injective n) (fun n => IC'.injective n)
  let ua := comparisonCochainMap IA.cocomplex IA'.cocomplex (fun n => (un n).τ₁)
    (comparisonDifferential IA.cocomplex IA'.cocomplex
      (fun n => (T n).X₁) (fun n => (T' n).X₁)
      (fun n => (e n).τ₁) (fun n => (r n).τ₁)
      (fun n => (e' n).τ₁) (fun n => (r' n).τ₁)
      (fun n => (fn n).τ₁) (fun n => (un n).τ₁) da da'
      (fun n => congrArg (fun t => t.τ₁) (ext n))
      (fun n => congrArg (fun t => t.τ₁) (desc n)))
  let ub := comparisonCochainMap IB.cocomplex IB'.cocomplex (fun n => (un n).τ₂)
    (comparisonDifferential IB.cocomplex IB'.cocomplex
      (fun n => (T n).X₂) (fun n => (T' n).X₂)
      (fun n => (e n).τ₂) (fun n => (r n).τ₂)
      (fun n => (e' n).τ₂) (fun n => (r' n).τ₂)
      (fun n => (fn n).τ₂) (fun n => (un n).τ₂) db db'
      (fun n => congrArg (fun t => t.τ₂) (ext n))
      (fun n => congrArg (fun t => t.τ₂) (desc n)))
  let uc := comparisonCochainMap IC.cocomplex IC'.cocomplex (fun n => (un n).τ₃)
    (comparisonDifferential IC.cocomplex IC'.cocomplex
      (fun n => (T n).X₃) (fun n => (T' n).X₃)
      (fun n => (e n).τ₃) (fun n => (r n).τ₃)
      (fun n => (e' n).τ₃) (fun n => (r' n).τ₃)
      (fun n => (fn n).τ₃) (fun n => (un n).τ₃) dc dc'
      (fun n => congrArg (fun t => t.τ₃) (ext n))
      (fun n => congrArg (fun t => t.τ₃) (desc n)))
  have initial : e 0 ≫ un 0 = (eqToHom h0 ≫ f ≫ eqToHom h0'.symm) ≫ e' 0 :=
    (ext 0).trans (congrArg (fun g => g ≫ e' 0) fzero)
  have aug := comparisonInitialAugmentation f h0 h0' (e 0) (e' 0) (un 0)
    (IA.ι.f 0) (IB.ι.f 0) (IC.ι.f 0) (IA'.ι.f 0) (IB'.ι.f 0) (IC'.ι.f 0)
    a b c a' b' c' initial
  let φ := comparisonStrictMap (ShortComplex.mk j q w) (ShortComplex.mk j' q' w')
    ua ub uc (fun n => (un n).comm₁₂) (fun n => (un n).comm₂₃)
  exact ⟨φ,
    comparisonAugmentationFromZero _ _ _ _ IA.ι IA'.ι ua f.τ₁ aug.1,
    comparisonAugmentationFromZero _ _ _ _ IB.ι IB'.ι ub f.τ₂ aug.2.1,
    comparisonAugmentationFromZero _ _ _ _ IC.ι IC'.ι uc f.τ₃ aug.2.2⟩

end CategoryTheory.InjectiveResolution
