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
