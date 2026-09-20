/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma

/-!
# Embedding short exact sequences into injective biproduct rows

Specified embeddings of the endpoints into injectives extend to a compatible
embedding of the middle object into their biproduct.

This is the first step of the Horseshoe lemma in its dual (injective) form:
Weibel, *An Introduction to Homological Algebra*, Proposition 2.2.8 (dualised);
Cartan–Eilenberg V.2.
-/

@[expose] public section

noncomputable section

universe v u

namespace CategoryTheory.ShortComplex.ShortExact

open CategoryTheory CategoryTheory.Limits

/-- Given monomorphisms `α : X₁ ⟶ I` and `γ : X₃ ⟶ K` into injectives for a short exact
sequence `0 → X₁ → X₂ → X₃ → 0`, there is a monomorphism `β : X₂ ⟶ I ⊞ K` making both
squares commute, namely `β = ⟨x, g ≫ γ⟩` for an extension `x` of `α` along `f`.
This is the horseshoe step of Weibel 2.2.8, dualised to injectives. -/
theorem exists_injective_biprod_embedding
    {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex C} (hS : S.ShortExact)
    {I K : C} [Injective I] [Injective K]
    (α : S.X₁ ⟶ I) [Mono α] (γ : S.X₃ ⟶ K) [Mono γ] :
    ∃ (x : S.X₂ ⟶ I) (β : S.X₂ ⟶ I ⊞ K),
      S.f ≫ x = α ∧
      β = biprod.lift x (S.g ≫ γ) ∧
      S.f ≫ β = α ≫ biprod.inl ∧
      β ≫ biprod.snd = S.g ≫ γ ∧
      Mono β := by
  let : Mono S.f := hS.mono_f
  let x : S.X₂ ⟶ I := Injective.factorThru α S.f
  have hx : S.f ≫ x = α := Injective.comp_factorThru α S.f
  let β : S.X₂ ⟶ I ⊞ K := biprod.lift x (S.g ≫ γ)
  have hfst : β ≫ biprod.fst = x := biprod.lift_fst x (S.g ≫ γ)
  have hsnd : β ≫ biprod.snd = S.g ≫ γ := biprod.lift_snd x (S.g ≫ γ)
  have hleft : S.f ≫ β = α ≫ biprod.inl := by
    apply biprod.hom_ext
    · simp only [Category.assoc, hfst, biprod.inl_fst, Category.comp_id, hx]
    · simp only [Category.assoc, hsnd, biprod.inl_snd, comp_zero]
      rw [← Category.assoc, S.zero, zero_comp]
  have hmono : Mono β := by
    apply Preadditive.mono_of_cancel_zero
    intro T t ht
    have htγ : (t ≫ S.g) ≫ γ = 0 := by
      calc
        (t ≫ S.g) ≫ γ = (t ≫ β) ≫ biprod.snd := by
          rw [Category.assoc, Category.assoc, hsnd]
        _ = 0 := by rw [ht, zero_comp]
    have htg : t ≫ S.g = 0 := zero_of_comp_mono γ htγ
    let s : T ⟶ S.X₁ := hS.exact.lift t htg
    have hs : s ≫ S.f = t := hS.exact.lift_f t htg
    have htx : t ≫ x = 0 := by
      calc
        t ≫ x = (t ≫ β) ≫ biprod.fst := by rw [Category.assoc, hfst]
        _ = 0 := by rw [ht, zero_comp]
    have hsα : s ≫ α = 0 := by
      rw [← hx, ← Category.assoc, hs, htx]
    have hs0 : s = 0 := zero_of_comp_mono α hsα
    rw [← hs, hs0, zero_comp]
  exact ⟨x, β, hx, rfl, hleft, hsnd, hmono⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The split target row of a specified componentwise monic embedding has injective
middle term. Its three component cokernels, with the arrows induced by the standard
biproduct inclusion and projection, form a short exact successor sequence.

The biproduct `I ⊞ K` is injective, the biproduct row `0 → I → I ⊞ K → K → 0` is short
exact, and the induced sequence of cokernels
`0 → coker α → coker β → coker γ → 0` is again short exact.  This is the inductive step
of the Horseshoe lemma, Weibel 2.2.8 dualised. -/
theorem injective_biprod_cokernel_successor
    {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex C} (hS : S.ShortExact)
    {I K : C} [Injective I] [Injective K]
    (α : S.X₁ ⟶ I) [Mono α] (γ : S.X₃ ⟶ K) [Mono γ]
    (β : S.X₂ ⟶ I ⊞ K) [Mono β]
    (hl : S.f ≫ β = α ≫ biprod.inl)
    (hr : β ≫ biprod.snd = S.g ≫ γ) :
    Injective (I ⊞ K) ∧
    (ShortComplex.mk (biprod.inl : I ⟶ I ⊞ K)
      (biprod.snd : I ⊞ K ⟶ K) biprod.inl_snd).ShortExact ∧
    ∃ (a : cokernel α ⟶ cokernel β) (b : cokernel β ⟶ cokernel γ),
      a = cokernel.map α β S.f biprod.inl hl.symm ∧
      b = cokernel.map β γ S.g biprod.snd hr ∧
      cokernel.π α ≫ a = biprod.inl ≫ cokernel.π β ∧
      cokernel.π β ≫ b = biprod.snd ≫ cokernel.π γ ∧
      ∃ (hab : a ≫ b = 0), (ShortComplex.mk a b hab).ShortExact := by
  let a : cokernel α ⟶ cokernel β := cokernel.map α β S.f biprod.inl hl.symm
  let b : cokernel β ⟶ cokernel γ := cokernel.map β γ S.g biprod.snd hr
  have ha : cokernel.π α ≫ a = biprod.inl ≫ cokernel.π β := cokernel.π_desc _ _ _
  have hb : cokernel.π β ≫ b = biprod.snd ≫ cokernel.π γ := cokernel.π_desc _ _ _
  have hab : a ≫ b = 0 := by
    apply (cancel_epi (cokernel.π α)).1
    rw [← Category.assoc, ha, Category.assoc, hb, ← Category.assoc,
      biprod.inl_snd, zero_comp, comp_zero]
  let Q : ShortComplex C := ShortComplex.mk a b hab
  let E : ShortComplex C := ShortComplex.mk (biprod.inl : I ⟶ I ⊞ K)
    (biprod.snd : I ⊞ K ⟶ K) biprod.inl_snd
  let φ : S ⟶ E := ShortComplex.homMk α β γ hl.symm hr
  let q : E ⟶ Q :=
    ShortComplex.homMk (cokernel.π α) (cokernel.π β) (cokernel.π γ) ha hb
  have w : φ ≫ q = 0 := by
    ext
    · exact cokernel.condition α
    · exact cokernel.condition β
    · exact cokernel.condition γ
  have hq : IsColimit (CokernelCofork.ofπ q w) := by
    apply ShortComplex.isColimitOfIsColimitπ
    · exact (isColimitMapCoconeCoforkEquiv' ShortComplex.π₁ w).symm
        (cokernelIsCokernel α)
    · exact (isColimitMapCoconeCoforkEquiv' ShortComplex.π₂ w).symm
        (cokernelIsCokernel β)
    · exact (isColimitMapCoconeCoforkEquiv' ShortComplex.π₃ w).symm
        (cokernelIsCokernel γ)
  let D : ShortComplex.SnakeInput C :=
    { L₀ := kernel φ
      L₁ := S
      L₂ := E
      L₃ := Q
      v₀₁ := kernel.ι φ
      v₁₂ := φ
      v₂₃ := q
      w₀₂ := kernel.condition φ
      w₁₃ := w
      h₀ := kernelIsKernel φ
      h₃ := hq
      L₁_exact := hS.exact
      epi_L₁_g := hS.epi_g
      L₂_exact := (ShortComplex.Splitting.ofHasBinaryBiproduct I K).shortExact.exact
      mono_L₂_f := (inferInstance : Mono (biprod.inl : I ⟶ I ⊞ K)) }
  have hExact : Q.Exact := D.L₃_exact
  have hEpi : Epi Q.g := by
    let : Epi D.L₂.g := (inferInstance : Epi (biprod.snd : I ⊞ K ⟶ K))
    change Epi D.L₃.g
    infer_instance
  have hMono : Mono Q.f := by
    let : Mono D.v₁₂.τ₃ := (inferInstance : Mono γ)
    have hz : IsZero D.L₀.X₃ := KernelFork.IsLimit.isZero_of_mono D.h₀τ₃
    exact D.L₂'_exact.mono_g (hz.eq_of_src _ _)
  have hQ : Q.ShortExact := { exact := hExact, mono_f := hMono, epi_g := hEpi }
  exact ⟨inferInstance, (ShortComplex.Splitting.ofHasBinaryBiproduct I K).shortExact,
    a, b, rfl, rfl, ha, hb, hab, hQ⟩

section

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The standard split target has inclusion and projection as its row arrows. -/
private abbrev row (I K : C) : ShortComplex C :=
  ShortComplex.mk (biprod.inl : I ⟶ I ⊞ K) (biprod.snd : I ⊞ K ⟶ K) biprod.inl_snd

/-- Project the two strict squares: the right coordinate of the middle map is
forced by the right endpoint, and the left endpoint is forced by its first coordinate. -/
private theorem coordinates {T : ShortComplex C} {I K : C} (v : T ⟶ row I K) :
  v.τ₂ = biprod.lift (v.τ₂ ≫ biprod.fst) (T.g ≫ v.τ₃) ∧
  v.τ₁ = T.f ≫ (v.τ₂ ≫ biprod.fst) := by
  constructor
  · apply biprod.hom_ext
    · simp
    · simpa using v.comm₂₃
  · have h := congrArg (fun f => f ≫ biprod.fst) v.comm₁₂
    simpa [row, Category.assoc] using h

/-- A map `v : T ⟶ row I K` from a short exact sequence into a biproduct row with
injective endpoints extends along any componentwise monic map `m : T ⟶ U` of short exact
sequences, as a single map of rows: there is `w : U ⟶ row I K` with `m ≫ w = v`. -/
private theorem coordinate_extension {T U : ShortComplex C}
    (hT : T.ShortExact) (hU : U.ShortExact)
    (m : T ⟶ U) [Mono m.τ₁] [Mono m.τ₂] [Mono m.τ₃]
    {I K : C} [Injective I] [Injective K] (v : T ⟶ row I K) :
    ∃ (w : U ⟶ row I K),
      w.τ₁ = U.f ≫ Injective.factorThru (v.τ₂ ≫ biprod.fst) m.τ₂ ∧
      w.τ₂ = biprod.lift (Injective.factorThru (v.τ₂ ≫ biprod.fst) m.τ₂)
        (U.g ≫ Injective.factorThru v.τ₃ m.τ₃) ∧
      w.τ₃ = Injective.factorThru v.τ₃ m.τ₃ ∧ m ≫ w = v := by
  have _ := hT
  have _ := hU
  let x := Injective.factorThru (v.τ₂ ≫ biprod.fst) m.τ₂
  let z := Injective.factorThru v.τ₃ m.τ₃
  have hx : m.τ₂ ≫ x = v.τ₂ ≫ biprod.fst := Injective.comp_factorThru _ _
  have hz : m.τ₃ ≫ z = v.τ₃ := Injective.comp_factorThru _ _
  have hl : (U.f ≫ x) ≫ biprod.inl = U.f ≫ biprod.lift x (U.g ≫ z) := by
    apply biprod.hom_ext
    · simp
    · simp only [Category.assoc, biprod.inl_snd, comp_zero, biprod.lift_snd]
      rw [← Category.assoc, U.zero, zero_comp]
  have hr : biprod.lift x (U.g ≫ z) ≫ biprod.snd = U.g ≫ z := biprod.lift_snd _ _
  let w : U ⟶ row I K :=
    ShortComplex.homMk (U.f ≫ x) (biprod.lift x (U.g ≫ z)) z hl hr
  refine ⟨w, rfl, rfl, rfl, ?_⟩
  apply ShortComplex.hom_ext
  · change m.τ₁ ≫ (U.f ≫ x) = v.τ₁
    rw [← Category.assoc, m.comm₁₂, Category.assoc, hx, ← (coordinates v).2]
  · change m.τ₂ ≫ biprod.lift x (U.g ≫ z) = v.τ₂
    apply biprod.hom_ext
    · simpa only [Category.assoc, biprod.lift_fst] using hx
    · simp only [Category.assoc, biprod.lift_snd]
      rw [← Category.assoc, m.comm₂₃, Category.assoc, hz]
      exact v.comm₂₃.symm
  · exact hz

/-- A specified splitting identifies the target with its endpoint biproduct row,
using identity maps at both endpoints and the standard splitting isomorphism in the middle. -/
private def splitIso (E : ShortComplex C) (s : E.Splitting) : E ≅ row E.X₁ E.X₃ :=
  ShortComplex.isoMk (Iso.refl _) s.isoBinaryBiproduct (Iso.refl _)
    (by
      dsimp [row, ShortComplex.Splitting.isoBinaryBiproduct]
      ext <;> simp [s.f_r, E.zero])
    (by simp [row, ShortComplex.Splitting.isoBinaryBiproduct])

end

/-- A map of short exact sequences `v : T ⟶ E` into a split short exact sequence `E`
with injective endpoints extends along any componentwise monic map `m : T ⟶ U`: there is
`w : U ⟶ E` with `m ≫ w = v`.  Equivalently, a split short exact sequence with injective
endpoints is an injective object of the category of short exact sequences
(Weibel 2.2.8, dualised). -/
public theorem exists_extension_to_split_injective
    {C : Type u} [Category.{v} C] [Abelian C]
    {T U E : ShortComplex C} (hT : T.ShortExact) (hU : U.ShortExact)
    (m : T ⟶ U) [Mono m.τ₁] [Mono m.τ₂] [Mono m.τ₃]
    (s : E.Splitting) [Injective E.X₁] [Injective E.X₃] (v : T ⟶ E) :
    ∃ w : U ⟶ E, m ≫ w = v := by
  let q := splitIso E s
  obtain ⟨w, _, _, _, hw⟩ := coordinate_extension hT hU m (v ≫ q.hom)
  refine ⟨w ≫ q.inv, ?_⟩
  rw [← Category.assoc, hw, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end CategoryTheory.ShortComplex.ShortExact
