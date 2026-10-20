/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib

/-!
# Subcomplexes and quotient complexes of a chain complex of `ℤ`-modules

A *chain submodule* of a chain complex `K` of `ℤ`-modules (indexed by `ℕ`, descending shape) is a
family of submodules `S n ≤ K.X n` closed under the differential.  It determines the subcomplex
`S.subComplex` with terms `S n`, the quotient complex `S.quotientComplex` with terms `K.X n ⧸ S n`,
and, for two chain submodules `T`, `S`, the relative complex `relativeComplex T S` with terms
`T n ⧸ (S n ∩ T n)`, which is the chain-level model of a relative homology group `H_*(U, A)` when
`T` and `S` are the chains supported in `U` and in `A`.  The short exact sequences
`0 → S.subComplex → K → S.quotientComplex → 0` and, for `S ≤ T`,
`0 → S.subComplex → T.subComplex → relativeComplex T S → 0` are recorded as
`CategoryTheory.ShortComplex.ShortExact`, so that the long exact homology sequence of
`Lib/AlgebraicTopology/SingularHomology/MayerVietoris/HomologyLongExact.lean` applies to them.
The second isomorphism theorem `relativeSupIso T S : relativeComplex T S ≅ relativeComplex (S ⊔ T) S`
is the chain-level form of the excision argument (Hatcher, *Algebraic Topology*, proof of Theorem
2.20: `C_n(B)/C_n(A ∩ B) ≅ (C_n(A) + C_n(B))/C_n(A)`).

## Main definitions and results

* `ChainSubmodule K` : a family of submodules closed under the differential, with the lattice
  operations `⊤`, `⊥`, `⊔`, `⊓` and the order `≤`.
* `ChainSubmodule.subComplex`, `ChainSubmodule.ι` : the subcomplex and its inclusion.
* `ChainSubmodule.quotientComplex`, `ChainSubmodule.π` : the quotient complex and its projection;
  `ChainSubmodule.quotientSequence_shortExact`.
* `ChainSubmodule.relativeComplex T S`, `ChainSubmodule.relativeMap`,
  `ChainSubmodule.relativeSequence_shortExact`.
* `ChainSubmodule.relativeSupIso` : the second isomorphism theorem for relative complexes.
* `ChainSubmodule.relativeTopIso` : `relativeComplex ⊤ S ≅ S.quotientComplex`.
* `ChainSubmodule.quotientMapOfChainMap`, `ChainSubmodule.mapOfChainMap` : a chain map `K ⟶ L`
  carrying the submodules into each other induces maps of quotient and of relative complexes.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §2.1 (relative homology groups) and the proof
  of Theorem 2.20 (excision)
* `Mathlib/LinearAlgebra/Isomorphisms.lean` (`LinearMap.quotientInfEquivSupQuotient`)

## Tags

subcomplex, quotient complex, relative homology, second isomorphism theorem
-/

open CategoryTheory

@[expose] public noncomputable section

universe u

/-- A family of submodules of the terms of a chain complex of `ℤ`-modules, closed under the
differential (Hatcher, Algebraic Topology, §2.1: a subcomplex). -/
structure ChainSubmodule (K : ChainComplex (ModuleCat.{u} ℤ) ℕ) where
  /-- The submodule in degree `n`. -/
  carrier : ∀ n : ℕ, Submodule ℤ (K.X n)
  /-- The submodules are closed under every differential. -/
  d_mem : ∀ (i j : ℕ) ⦃c : K.X i⦄, c ∈ carrier i → (K.d i j).hom c ∈ carrier j

namespace ChainSubmodule

variable {K : ChainComplex (ModuleCat.{u} ℤ) ℕ}

/-- The `ℤ`-module structure of a term of a chain submodule is the submodule one (this pins the
diamond with `AddCommGroup.toIntModule`, as in `SingularMayerVietoris.smallChainModule`). -/
instance carrierModule (S : ChainSubmodule K) (n : ℕ) : Module ℤ (S.carrier n) :=
  (S.carrier n).module

/-- The `ℤ`-module structure of a quotient by a term of a chain submodule is the quotient one. -/
instance quotientModule (S : ChainSubmodule K) (n : ℕ) : Module ℤ (K.X n ⧸ S.carrier n) :=
  Submodule.Quotient.module _

/-- The `ℤ`-module structure of a quotient of a term by a submodule is the quotient one. -/
instance quotientCarrierModule (T : ChainSubmodule K) (n : ℕ) (p : Submodule ℤ (T.carrier n)) :
    Module ℤ (T.carrier n ⧸ p) :=
  Submodule.Quotient.module _

/-- A family of submodules closed under the differentials `d (n+1) n` is a chain submodule. -/
def mk' (carrier : ∀ n : ℕ, Submodule ℤ (K.X n))
    (d_mem : ∀ (n : ℕ) ⦃c : K.X (n + 1)⦄, c ∈ carrier (n + 1) → (K.d (n + 1) n).hom c ∈ carrier n) :
    ChainSubmodule K where
  carrier := carrier
  d_mem i j c hc := by
    by_cases hij : (ComplexShape.down ℕ).Rel i j
    · have he : j + 1 = i := hij
      subst he
      exact d_mem j hc
    · rw [K.shape i j hij]
      exact Submodule.zero_mem _

@[simp]
theorem mk'_carrier (carrier : ∀ n : ℕ, Submodule ℤ (K.X n)) (d_mem) :
    (mk' carrier d_mem).carrier = carrier := rfl

/-- The differentials `K.d i j` and `K.d j k` compose to zero, elementwise. -/
theorem d_d_apply (i j k : ℕ) (c : K.X i) : (K.d j k).hom ((K.d i j).hom c) = 0 :=
  congrArg (fun f : K.X i ⟶ K.X k => f.hom c) (K.d_comp_d i j k)

/-! ### The lattice of chain submodules -/

instance : LE (ChainSubmodule K) := ⟨fun S T => ∀ n, S.carrier n ≤ T.carrier n⟩

theorem le_def {S T : ChainSubmodule K} : S ≤ T ↔ ∀ n, S.carrier n ≤ T.carrier n := Iff.rfl

instance : Top (ChainSubmodule K) :=
  ⟨{ carrier := fun _ => ⊤, d_mem := fun _ _ _ _ => Submodule.mem_top }⟩

instance : Bot (ChainSubmodule K) :=
  ⟨{ carrier := fun _ => ⊥
     d_mem := fun i j c hc => by
       rw [Submodule.mem_bot] at hc ⊢
       rw [hc, map_zero] }⟩

/-- The sum of two chain submodules. -/
instance : Max (ChainSubmodule K) :=
  ⟨fun S T =>
    { carrier := fun n => S.carrier n ⊔ T.carrier n
      d_mem := fun i j c hc => by
        rcases Submodule.mem_sup.mp hc with ⟨a, ha, b, hb, rfl⟩
        rw [map_add]
        exact Submodule.mem_sup.mpr ⟨_, S.d_mem i j ha, _, T.d_mem i j hb, rfl⟩ }⟩

/-- The intersection of two chain submodules. -/
instance : Min (ChainSubmodule K) :=
  ⟨fun S T =>
    { carrier := fun n => S.carrier n ⊓ T.carrier n
      d_mem := fun i j _ hc => ⟨S.d_mem i j hc.1, T.d_mem i j hc.2⟩ }⟩

@[simp] theorem top_carrier (n : ℕ) : (⊤ : ChainSubmodule K).carrier n = ⊤ := rfl
@[simp] theorem bot_carrier (n : ℕ) : (⊥ : ChainSubmodule K).carrier n = ⊥ := rfl
@[simp] theorem sup_carrier (S T : ChainSubmodule K) (n : ℕ) :
    (S ⊔ T).carrier n = S.carrier n ⊔ T.carrier n := rfl
@[simp] theorem inf_carrier (S T : ChainSubmodule K) (n : ℕ) :
    (S ⊓ T).carrier n = S.carrier n ⊓ T.carrier n := rfl

theorem le_top (S : ChainSubmodule K) : S ≤ ⊤ := fun _ => _root_.le_top
theorem bot_le (S : ChainSubmodule K) : ⊥ ≤ S := fun _ => _root_.bot_le
theorem le_sup_left (S T : ChainSubmodule K) : S ≤ S ⊔ T := fun _ => _root_.le_sup_left
theorem le_sup_right (S T : ChainSubmodule K) : T ≤ S ⊔ T := fun _ => _root_.le_sup_right
theorem inf_le_left (S T : ChainSubmodule K) : S ⊓ T ≤ S := fun _ => _root_.inf_le_left
theorem inf_le_right (S T : ChainSubmodule K) : S ⊓ T ≤ T := fun _ => _root_.inf_le_right
theorem le_refl (S : ChainSubmodule K) : S ≤ S := fun _ => _root_.le_rfl
theorem le_trans {S T U : ChainSubmodule K} (h₁ : S ≤ T) (h₂ : T ≤ U) : S ≤ U :=
  fun n => (h₁ n).trans (h₂ n)
theorem sup_le {S T U : ChainSubmodule K} (h₁ : S ≤ U) (h₂ : T ≤ U) : S ⊔ T ≤ U :=
  fun n => _root_.sup_le (h₁ n) (h₂ n)
theorem le_inf {S T U : ChainSubmodule K} (h₁ : U ≤ S) (h₂ : U ≤ T) : U ≤ S ⊓ T :=
  fun n => _root_.le_inf (h₁ n) (h₂ n)

/-! ### The subcomplex -/

/-- The differential restricted to a chain submodule. -/
def subDifferential (S : ChainSubmodule K) (i j : ℕ) : S.carrier i →ₗ[ℤ] S.carrier j :=
  (K.d i j).hom.restrict (fun _ hc => S.d_mem i j hc)

@[simp]
theorem subDifferential_apply_coe (S : ChainSubmodule K) (i j : ℕ) (c : S.carrier i) :
    (S.subDifferential i j c : K.X j) = (K.d i j).hom c := rfl

/-- The subcomplex with terms the submodules of a chain submodule. -/
abbrev subComplex (S : ChainSubmodule K) : ChainComplex (ModuleCat.{u} ℤ) ℕ where
  X n := ModuleCat.of ℤ (S.carrier n)
  d i j := ModuleCat.ofHom (S.subDifferential i j)
  shape i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    change (K.d i j).hom c.1 = 0
    rw [K.shape i j hij]
    rfl
  d_comp_d' i j k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact d_d_apply i j k c.1

/-- Extensionality for morphisms out of a term of a subcomplex. -/
theorem sub_hom_ext {S : ChainSubmodule K} {n : ℕ} {Y : ModuleCat.{u} ℤ}
    {f g : S.subComplex.X n ⟶ Y} (h : ∀ c : S.carrier n, f.hom c = g.hom c) : f = g :=
  ModuleCat.hom_ext (LinearMap.ext h)

/-- The inclusion of a subcomplex. -/
def ι (S : ChainSubmodule K) : S.subComplex ⟶ K where
  f n := ModuleCat.ofHom (S.carrier n).subtype
  comm' _ _ _ := sub_hom_ext fun _ => rfl

@[simp]
theorem ι_f_apply (S : ChainSubmodule K) (n : ℕ) (c : S.carrier n) : (S.ι.f n).hom c = c := rfl

theorem ι_f_injective (S : ChainSubmodule K) (n : ℕ) : Function.Injective (S.ι.f n).hom :=
  Subtype.val_injective

/-- The inclusion of subcomplexes along `S ≤ T`. -/
def subMap {S T : ChainSubmodule K} (h : S ≤ T) : S.subComplex ⟶ T.subComplex where
  f n := ModuleCat.ofHom (Submodule.inclusion (h n))
  comm' _ _ _ := sub_hom_ext fun _ => rfl

@[simp]
theorem subMap_f_apply {S T : ChainSubmodule K} (h : S ≤ T) (n : ℕ) (c : S.carrier n) :
    ((subMap h).f n).hom c = Submodule.inclusion (h n) c := rfl

@[simp]
theorem subMap_ι {S T : ChainSubmodule K} (h : S ≤ T) : subMap h ≫ T.ι = S.ι := by
  apply HomologicalComplex.hom_ext
  intro n
  exact sub_hom_ext fun _ => rfl

/-! ### The quotient complex -/

/-- The differential on the quotient by a chain submodule. -/
def quotientDifferential (S : ChainSubmodule K) (i j : ℕ) :
    (K.X i ⧸ S.carrier i) →ₗ[ℤ] K.X j ⧸ S.carrier j :=
  Submodule.mapQ _ _ (K.d i j).hom (fun _ hc => S.d_mem i j hc)

@[simp]
theorem quotientDifferential_mk (S : ChainSubmodule K) (i j : ℕ) (c : K.X i) :
    S.quotientDifferential i j (Submodule.Quotient.mk c) = Submodule.Quotient.mk ((K.d i j).hom c) :=
  rfl

/-- The quotient complex `K / S`. -/
abbrev quotientComplex (S : ChainSubmodule K) : ChainComplex (ModuleCat.{u} ℤ) ℕ where
  X n := ModuleCat.of ℤ (K.X n ⧸ S.carrier n)
  d i j := ModuleCat.ofHom (S.quotientDifferential i j)
  shape i j hij := by
    apply ModuleCat.hom_ext
    apply Submodule.linearMap_qext
    ext c
    change Submodule.Quotient.mk ((K.d i j).hom c) = 0
    rw [K.shape i j hij]
    rfl
  d_comp_d' i j k _ _ := by
    apply ModuleCat.hom_ext
    apply Submodule.linearMap_qext
    ext c
    change Submodule.Quotient.mk ((K.d j k).hom ((K.d i j).hom c)) = 0
    rw [d_d_apply]
    rfl

/-- Extensionality for morphisms out of a term of a quotient complex. -/
theorem quotient_hom_ext {S : ChainSubmodule K} {n : ℕ} {Y : ModuleCat.{u} ℤ}
    {f g : S.quotientComplex.X n ⟶ Y}
    (h : ∀ c : K.X n, f.hom (Submodule.Quotient.mk c) = g.hom (Submodule.Quotient.mk c)) : f = g :=
  ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext h))

/-- Extensionality for chain maps out of a quotient complex. -/
theorem quotientComplex_hom_ext {S : ChainSubmodule K} {L : ChainComplex (ModuleCat.{u} ℤ) ℕ}
    {f g : S.quotientComplex ⟶ L}
    (h : ∀ (n : ℕ) (c : K.X n),
      (f.f n).hom (Submodule.Quotient.mk c) = (g.f n).hom (Submodule.Quotient.mk c)) : f = g :=
  HomologicalComplex.hom_ext _ _ fun n => quotient_hom_ext (h n)

theorem quotientComplex_d_mk (S : ChainSubmodule K) (i j : ℕ) (c : K.X i) :
    (S.quotientComplex.d i j).hom (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk ((K.d i j).hom c) :=
  rfl

/-- The projection onto a quotient complex. -/
def π (S : ChainSubmodule K) : K ⟶ S.quotientComplex where
  f n := ModuleCat.ofHom (S.carrier n).mkQ
  comm' _ _ _ := ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

@[simp]
theorem π_f_apply (S : ChainSubmodule K) (n : ℕ) (c : K.X n) :
    (S.π.f n).hom c = Submodule.Quotient.mk c := rfl

theorem π_f_surjective (S : ChainSubmodule K) (n : ℕ) : Function.Surjective (S.π.f n).hom :=
  Submodule.Quotient.mk_surjective _

/-- The projection of quotient complexes along `S ≤ T`. -/
def quotientMap {S T : ChainSubmodule K} (h : S ≤ T) : S.quotientComplex ⟶ T.quotientComplex where
  f n := ModuleCat.ofHom (Submodule.mapQ _ _ LinearMap.id (fun _ hc => h n hc))
  comm' _ _ _ := quotient_hom_ext fun _ => rfl

@[simp]
theorem quotientMap_f_mk {S T : ChainSubmodule K} (h : S ≤ T) (n : ℕ) (c : K.X n) :
    ((quotientMap h).f n).hom (Submodule.Quotient.mk c) = Submodule.Quotient.mk c :=
  rfl

@[simp]
theorem π_quotientMap {S T : ChainSubmodule K} (h : S ≤ T) : S.π ≫ quotientMap h = T.π :=
  HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

theorem quotientMap_comp {S T U : ChainSubmodule K} (h : S ≤ T) (h' : T ≤ U) :
    quotientMap h ≫ quotientMap h' = quotientMap (le_trans h h') :=
  quotientComplex_hom_ext fun _ _ => rfl

theorem quotientMap_id (S : ChainSubmodule K) : quotientMap (le_refl S) = 𝟙 S.quotientComplex :=
  quotientComplex_hom_ext fun _ _ => rfl

/-- The short complex `S.subComplex → K → S.quotientComplex`. -/
def quotientSequence (S : ChainSubmodule K) : ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
  ShortComplex.mk S.ι S.π (HomologicalComplex.hom_ext _ _ fun _ => sub_hom_ext fun c =>
    (Submodule.Quotient.mk_eq_zero _).mpr c.2)

@[simp] theorem quotientSequence_X₁ (S : ChainSubmodule K) : S.quotientSequence.X₁ = S.subComplex := rfl
@[simp] theorem quotientSequence_X₂ (S : ChainSubmodule K) : S.quotientSequence.X₂ = K := rfl
@[simp] theorem quotientSequence_X₃ (S : ChainSubmodule K) :
    S.quotientSequence.X₃ = S.quotientComplex := rfl
@[simp] theorem quotientSequence_f (S : ChainSubmodule K) : S.quotientSequence.f = S.ι := rfl
@[simp] theorem quotientSequence_g (S : ChainSubmodule K) : S.quotientSequence.g = S.π := rfl

/-- `0 → S → K → K/S → 0` is short exact. -/
theorem quotientSequence_shortExact (S : ChainSubmodule K) : S.quotientSequence.ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  apply ModuleCat.shortComplex_shortExact
  · intro c
    constructor
    · intro hc
      exact ⟨⟨c, (Submodule.Quotient.mk_eq_zero _).mp hc⟩, rfl⟩
    · rintro ⟨d, rfl⟩
      exact (Submodule.Quotient.mk_eq_zero _).mpr d.2
  · exact S.ι_f_injective n
  · exact S.π_f_surjective n

/-! ### The relative complex `T / (S ⊓ T)` -/

/-- The submodule of `T n` cut out by `S n`. -/
abbrev relativeSubmodule (T S : ChainSubmodule K) (n : ℕ) : Submodule ℤ (T.carrier n) :=
  (S.carrier n).comap (T.carrier n).subtype

theorem mem_relativeSubmodule (T S : ChainSubmodule K) (n : ℕ) (c : T.carrier n) :
    c ∈ relativeSubmodule T S n ↔ (c : K.X n) ∈ S.carrier n := Iff.rfl

/-- The differential of the relative complex. -/
def relativeDifferential (T S : ChainSubmodule K) (i j : ℕ) :
    (T.carrier i ⧸ relativeSubmodule T S i) →ₗ[ℤ] T.carrier j ⧸ relativeSubmodule T S j :=
  Submodule.mapQ _ _ (T.subDifferential i j) (fun _ hc => S.d_mem i j hc)

@[simp]
theorem relativeDifferential_mk (T S : ChainSubmodule K) (i j : ℕ) (c : T.carrier i) :
    relativeDifferential T S i j (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (T.subDifferential i j c) :=
  rfl

/-- The relative complex `T / (S ⊓ T)`: in degree `n` the quotient of `T n` by the chains of `T n`
lying in `S n` (Hatcher, Algebraic Topology, §2.1, the relative chain groups `C_n(X, A) = C_n(X)/C_n(A)`). -/
abbrev relativeComplex (T S : ChainSubmodule K) : ChainComplex (ModuleCat.{u} ℤ) ℕ where
  X n := ModuleCat.of ℤ (T.carrier n ⧸ relativeSubmodule T S n)
  d i j := ModuleCat.ofHom (relativeDifferential T S i j)
  shape i j hij := by
    apply ModuleCat.hom_ext
    apply Submodule.linearMap_qext
    ext c
    change Submodule.Quotient.mk (T.subDifferential i j c) = 0
    have : T.subDifferential i j c = 0 := by
      apply Subtype.ext
      change (K.d i j).hom c = 0
      rw [K.shape i j hij]
      rfl
    rw [this, Submodule.Quotient.mk_zero]
  d_comp_d' i j k _ _ := by
    apply ModuleCat.hom_ext
    apply Submodule.linearMap_qext
    ext c
    change Submodule.Quotient.mk (T.subDifferential j k (T.subDifferential i j c)) = 0
    have : T.subDifferential j k (T.subDifferential i j c) = 0 := by
      apply Subtype.ext
      exact d_d_apply i j k c.1
    rw [this, Submodule.Quotient.mk_zero]

/-- Extensionality for morphisms out of a term of a relative complex. -/
theorem relative_hom_ext {T S : ChainSubmodule K} {n : ℕ} {Y : ModuleCat.{u} ℤ}
    {f g : (relativeComplex T S).X n ⟶ Y}
    (h : ∀ c : T.carrier n, f.hom (Submodule.Quotient.mk c) = g.hom (Submodule.Quotient.mk c)) :
    f = g :=
  ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext h))

/-- Extensionality for chain maps out of a relative complex. -/
theorem relativeComplex_hom_ext {T S : ChainSubmodule K} {L : ChainComplex (ModuleCat.{u} ℤ) ℕ}
    {f g : relativeComplex T S ⟶ L}
    (h : ∀ (n : ℕ) (c : T.carrier n),
      (f.f n).hom (Submodule.Quotient.mk c) = (g.f n).hom (Submodule.Quotient.mk c)) : f = g :=
  HomologicalComplex.hom_ext _ _ fun n => relative_hom_ext (h n)

theorem relativeComplex_d_mk (T S : ChainSubmodule K) (i j : ℕ) (c : T.carrier i) :
    ((relativeComplex T S).d i j).hom (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (T.subDifferential i j c) :=
  rfl

/-- The projection from the subcomplex of `T` to the relative complex. -/
def relativeProjection (T S : ChainSubmodule K) : T.subComplex ⟶ relativeComplex T S where
  f n := ModuleCat.ofHom (relativeSubmodule T S n).mkQ
  comm' _ _ _ := sub_hom_ext fun _ => rfl

@[simp]
theorem relativeProjection_f_apply (T S : ChainSubmodule K) (n : ℕ) (c : T.carrier n) :
    ((relativeProjection T S).f n).hom c = Submodule.Quotient.mk c := rfl

theorem relativeProjection_f_surjective (T S : ChainSubmodule K) (n : ℕ) :
    Function.Surjective ((relativeProjection T S).f n).hom :=
  Submodule.Quotient.mk_surjective _

/-- The short complex `S → T → T/S` for `S ≤ T`. -/
def relativeSequence {T S : ChainSubmodule K} (h : S ≤ T) :
    ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
  ShortComplex.mk (subMap h) (relativeProjection T S)
    (HomologicalComplex.hom_ext _ _ fun n => sub_hom_ext fun c =>
      (Submodule.Quotient.mk_eq_zero (relativeSubmodule T S n)).mpr c.2)

@[simp] theorem relativeSequence_X₁ {T S : ChainSubmodule K} (h : S ≤ T) :
    (relativeSequence h).X₁ = S.subComplex := rfl
@[simp] theorem relativeSequence_X₂ {T S : ChainSubmodule K} (h : S ≤ T) :
    (relativeSequence h).X₂ = T.subComplex := rfl
@[simp] theorem relativeSequence_X₃ {T S : ChainSubmodule K} (h : S ≤ T) :
    (relativeSequence h).X₃ = relativeComplex T S := rfl
@[simp] theorem relativeSequence_f {T S : ChainSubmodule K} (h : S ≤ T) :
    (relativeSequence h).f = subMap h := rfl
@[simp] theorem relativeSequence_g {T S : ChainSubmodule K} (h : S ≤ T) :
    (relativeSequence h).g = relativeProjection T S := rfl

/-- `0 → S → T → T/S → 0` is short exact for `S ≤ T`. -/
theorem relativeSequence_shortExact {T S : ChainSubmodule K} (h : S ≤ T) :
    (relativeSequence h).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  apply ModuleCat.shortComplex_shortExact
  · intro c
    constructor
    · intro hc
      exact ⟨⟨c.1, (Submodule.Quotient.mk_eq_zero (relativeSubmodule T S n)).mp hc⟩,
        Subtype.ext rfl⟩
    · rintro ⟨d, rfl⟩
      exact (Submodule.Quotient.mk_eq_zero (relativeSubmodule T S n)).mpr d.2
  · intro a b hab
    have hab' : Submodule.inclusion (h n) a = Submodule.inclusion (h n) b := hab
    exact Subtype.ext (congrArg Subtype.val hab' :)
  · exact relativeProjection_f_surjective T S n

/-- The map of relative complexes along `T ≤ T'`, `S ≤ S'`. -/
def relativeMap {T T' S S' : ChainSubmodule K} (hT : T ≤ T') (hS : S ≤ S') :
    relativeComplex T S ⟶ relativeComplex T' S' where
  f n := ModuleCat.ofHom (Submodule.mapQ _ _ (Submodule.inclusion (hT n)) (fun _ hc => hS n hc))
  comm' _ _ _ := relative_hom_ext fun _ => rfl

@[simp]
theorem relativeMap_f_mk {T T' S S' : ChainSubmodule K} (hT : T ≤ T') (hS : S ≤ S') (n : ℕ)
    (c : T.carrier n) :
    ((relativeMap hT hS).f n).hom (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (Submodule.inclusion (hT n) c) :=
  rfl

theorem relativeMap_id (T S : ChainSubmodule K) :
    relativeMap (le_refl T) (le_refl S) = 𝟙 (relativeComplex T S) :=
  relativeComplex_hom_ext fun _ _ => rfl

theorem relativeMap_comp {T T' T'' S S' S'' : ChainSubmodule K} (hT : T ≤ T') (hT' : T' ≤ T'')
    (hS : S ≤ S') (hS' : S' ≤ S'') :
    relativeMap hT hS ≫ relativeMap hT' hS' = relativeMap (le_trans hT hT') (le_trans hS hS') :=
  relativeComplex_hom_ext fun _ _ => rfl

@[simp]
theorem subMap_relativeProjection {T T' S S' : ChainSubmodule K} (hT : T ≤ T') (hS : S ≤ S') :
    subMap hT ≫ relativeProjection T' S' = relativeProjection T S ≫ relativeMap hT hS :=
  HomologicalComplex.hom_ext _ _ fun _ => sub_hom_ext fun _ => rfl

/-- The relative complex of `T` and `S` and that of `T` and `S ⊓ T` have the same submodules. -/
theorem relativeSubmodule_inf (T S : ChainSubmodule K) (n : ℕ) :
    relativeSubmodule T (S ⊓ T) n = relativeSubmodule T S n := by
  ext c
  exact ⟨fun h => h.1, fun h => ⟨h, c.2⟩⟩

/-- For `S ≤ T`, the inclusion `S.subComplex → T.subComplex` and the projection
`K/S → K/T` form a morphism of quotient sequences (with `𝟙 K` in the middle). -/
def quotientSequenceMap {S T : ChainSubmodule K} (h : S ≤ T) :
    S.quotientSequence ⟶ T.quotientSequence where
  τ₁ := subMap h
  τ₂ := 𝟙 K
  τ₃ := quotientMap h
  comm₁₂ := by
    change subMap h ≫ T.ι = S.ι ≫ 𝟙 K
    rw [subMap_ι, Category.comp_id]
  comm₂₃ := by
    change 𝟙 K ≫ T.π = S.π ≫ quotientMap h
    rw [Category.id_comp, π_quotientMap]

/-- If the inclusion of subcomplexes `S ≤ T` is a quasi-isomorphism, so is `K/S → K/T` (the five
lemma on the two long exact sequences). -/
theorem quotientMap_quasiIso {S T : ChainSubmodule K} (h : S ≤ T) [QuasiIso (subMap h)] :
    QuasiIso (quotientMap h) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃ (quotientSequenceMap h)
    S.quotientSequence_shortExact T.quotientSequence_shortExact
    (show QuasiIso (subMap h) from inferInstance) (show QuasiIso (𝟙 K) from inferInstance)

/-! ### From the relative complex to the quotient complex -/

/-- The map `T/(S ⊓ T) ⟶ K/S` induced by the inclusion of `T`. -/
def relativeToQuotient (T S : ChainSubmodule K) : relativeComplex T S ⟶ S.quotientComplex where
  f n := ModuleCat.ofHom (Submodule.mapQ _ _ (T.carrier n).subtype (fun _ hc => hc))
  comm' _ _ _ := relative_hom_ext fun _ => rfl

@[simp]
theorem relativeToQuotient_f_mk (T S : ChainSubmodule K) (n : ℕ) (c : T.carrier n) :
    ((relativeToQuotient T S).f n).hom (Submodule.Quotient.mk c) = Submodule.Quotient.mk (c : K.X n) :=
  rfl

@[simp]
theorem relativeProjection_relativeToQuotient (T S : ChainSubmodule K) :
    relativeProjection T S ≫ relativeToQuotient T S = T.ι ≫ S.π :=
  HomologicalComplex.hom_ext _ _ fun _ => sub_hom_ext fun _ => rfl

/-- The inclusion of `T` as a morphism from the relative sequence of `S ≤ T` to the quotient
sequence of `S`. -/
def relativeSequenceToQuotientSequence {T S : ChainSubmodule K} (h : S ≤ T) :
    relativeSequence h ⟶ S.quotientSequence where
  τ₁ := 𝟙 _
  τ₂ := T.ι
  τ₃ := relativeToQuotient T S
  comm₁₂ := by
    change 𝟙 _ ≫ S.ι = subMap h ≫ T.ι
    rw [Category.id_comp, subMap_ι]
  comm₂₃ := (relativeProjection_relativeToQuotient T S).symm

/-- If the inclusion of `T` is a quasi-isomorphism, so is `T/(S ⊓ T) ⟶ K/S` for `S ≤ T` (the five
lemma on the two long exact sequences). -/
theorem relativeToQuotient_quasiIso {T S : ChainSubmodule K} (h : S ≤ T) [QuasiIso T.ι] :
    QuasiIso (relativeToQuotient T S) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃ (relativeSequenceToQuotientSequence h)
    (relativeSequence_shortExact h) S.quotientSequence_shortExact
    (show QuasiIso (𝟙 S.subComplex) from inferInstance) (show QuasiIso T.ι from inferInstance)

/-! ### The second isomorphism theorem -/

/-- The natural map `T/(S ⊓ T) → (S ⊔ T)/S` in degree `n`. -/
def relativeSupMap (T S : ChainSubmodule K) (n : ℕ) :
    (T.carrier n ⧸ relativeSubmodule T S n) →ₗ[ℤ] (S ⊔ T).carrier n ⧸ relativeSubmodule (S ⊔ T) S n :=
  Submodule.mapQ _ _ (Submodule.inclusion (le_sup_right S T n)) (fun _ hc => hc)

theorem relativeSupMap_bijective (T S : ChainSubmodule K) (n : ℕ) :
    Function.Bijective (relativeSupMap T S n) := by
  constructor
  · intro a b hab
    induction a using Submodule.Quotient.induction_on with
    | H a =>
    induction b using Submodule.Quotient.induction_on with
    | H b =>
    have hab' : (Submodule.Quotient.mk (Submodule.inclusion (le_sup_right S T n) a) :
        (S ⊔ T).carrier n ⧸ relativeSubmodule (S ⊔ T) S n) =
        Submodule.Quotient.mk (Submodule.inclusion (le_sup_right S T n) b) := hab
    rw [Submodule.Quotient.eq] at hab' ⊢
    exact hab'
  · intro c
    induction c using Submodule.Quotient.induction_on with
    | H c =>
    rcases Submodule.mem_sup.mp c.2 with ⟨s, hs, t, ht, hst⟩
    refine ⟨Submodule.Quotient.mk ⟨t, ht⟩, ?_⟩
    change Submodule.Quotient.mk (Submodule.inclusion (le_sup_right S T n) ⟨t, ht⟩) =
      Submodule.Quotient.mk c
    rw [Submodule.Quotient.eq]
    change (t : K.X n) - c ∈ S.carrier n
    rw [← hst, sub_add_cancel_right]
    exact (S.carrier n).neg_mem hs

/-- The second isomorphism theorem in degree `n`: `T/(S ⊓ T) ≃ (S ⊔ T)/S`. -/
def relativeSupEquiv (T S : ChainSubmodule K) (n : ℕ) :
    (T.carrier n ⧸ relativeSubmodule T S n) ≃ₗ[ℤ] (S ⊔ T).carrier n ⧸ relativeSubmodule (S ⊔ T) S n :=
  LinearEquiv.ofBijective (relativeSupMap T S n) (relativeSupMap_bijective T S n)

theorem relativeSupEquiv_mk (T S : ChainSubmodule K) (n : ℕ) (c : T.carrier n) :
    relativeSupEquiv T S n (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (Submodule.inclusion (le_sup_right S T n) c) :=
  rfl

/-- The second isomorphism theorem as an isomorphism of chain complexes:
`T/(S ⊓ T) ≅ (S ⊔ T)/S`. -/
def relativeSupIso (T S : ChainSubmodule K) :
    relativeComplex T S ≅ relativeComplex (S ⊔ T) S :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (relativeSupEquiv T S n).toModuleIso)
    (fun _ _ _ => relative_hom_ext fun _ => rfl)

@[simp]
theorem relativeSupIso_hom_f_mk (T S : ChainSubmodule K) (n : ℕ) (c : T.carrier n) :
    ((relativeSupIso T S).hom.f n).hom (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (Submodule.inclusion (le_sup_right S T n) c) := rfl

/-- The second isomorphism theorem is the map of relative complexes along `T ≤ S ⊔ T`. -/
theorem relativeSupIso_hom_eq (T S : ChainSubmodule K) :
    (relativeSupIso T S).hom = relativeMap (le_sup_right S T) (le_refl S) :=
  relativeComplex_hom_ext fun _ _ => rfl

/-! ### The relative complex of `⊤` is the quotient complex -/

/-- The natural map `⊤ / S → K / S` in degree `n`. -/
def relativeTopMap (S : ChainSubmodule K) (n : ℕ) :
    ((⊤ : ChainSubmodule K).carrier n ⧸ relativeSubmodule ⊤ S n) →ₗ[ℤ] K.X n ⧸ S.carrier n :=
  Submodule.mapQ _ _ ((⊤ : ChainSubmodule K).carrier n).subtype (fun _ hc => hc)

theorem relativeTopMap_bijective (S : ChainSubmodule K) (n : ℕ) :
    Function.Bijective (relativeTopMap S n) := by
  constructor
  · intro a b hab
    induction a using Submodule.Quotient.induction_on with
    | H a =>
    induction b using Submodule.Quotient.induction_on with
    | H b =>
    have hab' : (Submodule.Quotient.mk (a : K.X n) : K.X n ⧸ S.carrier n) =
        Submodule.Quotient.mk (b : K.X n) := hab
    rw [Submodule.Quotient.eq] at hab' ⊢
    exact hab'
  · intro c
    induction c using Submodule.Quotient.induction_on with
    | H c => exact ⟨Submodule.Quotient.mk ⟨c, Submodule.mem_top⟩, rfl⟩

/-- `⊤ / S ≅ K / S` in degree `n`. -/
def relativeTopEquiv (S : ChainSubmodule K) (n : ℕ) :
    ((⊤ : ChainSubmodule K).carrier n ⧸ relativeSubmodule ⊤ S n) ≃ₗ[ℤ] K.X n ⧸ S.carrier n :=
  LinearEquiv.ofBijective (relativeTopMap S n) (relativeTopMap_bijective S n)

theorem relativeTopEquiv_mk (S : ChainSubmodule K) (n : ℕ) (c : (⊤ : ChainSubmodule K).carrier n) :
    relativeTopEquiv S n (Submodule.Quotient.mk c) = Submodule.Quotient.mk (c : K.X n) := rfl

/-- `⊤ / S ≅ K / S` as chain complexes. -/
def relativeTopIso (S : ChainSubmodule K) : relativeComplex ⊤ S ≅ S.quotientComplex :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (relativeTopEquiv S n).toModuleIso)
    (fun _ _ _ => relative_hom_ext fun _ => rfl)

@[simp]
theorem relativeTopIso_hom_f_mk (S : ChainSubmodule K) (n : ℕ) (c : (⊤ : ChainSubmodule K).carrier n) :
    ((relativeTopIso S).hom.f n).hom (Submodule.Quotient.mk c) = Submodule.Quotient.mk (c : K.X n) :=
  rfl

/-! ### Functoriality along chain maps -/

section ChainMap

variable {L : ChainComplex (ModuleCat.{u} ℤ) ℕ}

/-- The image of a chain submodule under a chain map. -/
def map (f : K ⟶ L) (S : ChainSubmodule K) : ChainSubmodule L where
  carrier n := (S.carrier n).map (f.f n).hom
  d_mem i j c hc := by
    rcases hc with ⟨d, hd, rfl⟩
    refine ⟨(K.d i j).hom d, S.d_mem i j hd, ?_⟩
    exact (congrArg (fun g : K.X i ⟶ L.X j => g.hom d) (f.comm i j)).symm

@[simp]
theorem map_carrier (f : K ⟶ L) (S : ChainSubmodule K) (n : ℕ) :
    (map f S).carrier n = (S.carrier n).map (f.f n).hom := rfl

/-- The preimage of a chain submodule under a chain map. -/
def comap (f : K ⟶ L) (S : ChainSubmodule L) : ChainSubmodule K where
  carrier n := (S.carrier n).comap (f.f n).hom
  d_mem i j c hc := by
    change (f.f j).hom ((K.d i j).hom c) ∈ S.carrier j
    have hcomm : (L.d i j).hom ((f.f i).hom c) = (f.f j).hom ((K.d i j).hom c) :=
      congrArg (fun g : K.X i ⟶ L.X j => g.hom c) (f.comm i j)
    rw [← hcomm]
    exact S.d_mem i j hc

@[simp]
theorem comap_carrier (f : K ⟶ L) (S : ChainSubmodule L) (n : ℕ) :
    (comap f S).carrier n = (S.carrier n).comap (f.f n).hom := rfl

/-- A chain map carrying `S` into `S'` induces a map of quotient complexes `K/S ⟶ L/S'`. -/
def quotientMapOfChainMap (f : K ⟶ L) {S : ChainSubmodule K} {S' : ChainSubmodule L}
    (hS : ∀ n, ∀ c ∈ S.carrier n, (f.f n).hom c ∈ S'.carrier n) :
    S.quotientComplex ⟶ S'.quotientComplex where
  f n := ModuleCat.ofHom (Submodule.mapQ _ _ (f.f n).hom (fun c hc => hS n c hc))
  comm' i j _ := quotient_hom_ext fun c => by
    change Submodule.Quotient.mk ((L.d i j).hom ((f.f i).hom c)) =
      Submodule.Quotient.mk ((f.f j).hom ((K.d i j).hom c))
    have hcomm : (L.d i j).hom ((f.f i).hom c) = (f.f j).hom ((K.d i j).hom c) :=
      congrArg (fun g : K.X i ⟶ L.X j => g.hom c) (f.comm i j)
    rw [hcomm]

@[simp]
theorem quotientMapOfChainMap_f_mk (f : K ⟶ L) {S : ChainSubmodule K} {S' : ChainSubmodule L}
    (hS : ∀ n, ∀ c ∈ S.carrier n, (f.f n).hom c ∈ S'.carrier n) (n : ℕ) (c : K.X n) :
    ((quotientMapOfChainMap f hS).f n).hom (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk ((f.f n).hom c) :=
  rfl

/-- Quotient complexes are functorial for composable chain maps. -/
theorem quotientMapOfChainMap_comp {M : ChainComplex (ModuleCat.{u} ℤ) ℕ} (f : K ⟶ L) (g : L ⟶ M)
    {S : ChainSubmodule K} {S' : ChainSubmodule L} {S'' : ChainSubmodule M}
    (hS : ∀ n, ∀ c ∈ S.carrier n, (f.f n).hom c ∈ S'.carrier n)
    (hS' : ∀ n, ∀ c ∈ S'.carrier n, (g.f n).hom c ∈ S''.carrier n) :
    quotientMapOfChainMap f hS ≫ quotientMapOfChainMap g hS' =
      quotientMapOfChainMap (f ≫ g) (fun n c hc => hS' n _ (hS n c hc)) :=
  quotientComplex_hom_ext fun _ _ => rfl

/-- The identity chain map induces the identity on quotient complexes. -/
theorem quotientMapOfChainMap_id {S : ChainSubmodule K}
    (hS : ∀ n, ∀ c ∈ S.carrier n, ((𝟙 K : K ⟶ K).f n).hom c ∈ S.carrier n) :
    quotientMapOfChainMap (𝟙 K) hS = 𝟙 S.quotientComplex :=
  quotientComplex_hom_ext fun _ _ => rfl

/-- The projections commute with the maps induced by a chain map. -/
@[simp]
theorem π_quotientMapOfChainMap (f : K ⟶ L) {S : ChainSubmodule K} {S' : ChainSubmodule L}
    (hS : ∀ n, ∀ c ∈ S.carrier n, (f.f n).hom c ∈ S'.carrier n) :
    S.π ≫ quotientMapOfChainMap f hS = f ≫ S'.π :=
  HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

/-- A chain map carrying `T` into `T'` and `S` into `S'` induces a map of relative complexes. -/
def mapOfChainMap (f : K ⟶ L) {T S : ChainSubmodule K} {T' S' : ChainSubmodule L}
    (hT : ∀ n, ∀ c ∈ T.carrier n, (f.f n).hom c ∈ T'.carrier n)
    (hS : ∀ n, ∀ c ∈ S.carrier n, (f.f n).hom c ∈ S'.carrier n) :
    relativeComplex T S ⟶ relativeComplex T' S' where
  f n := ModuleCat.ofHom (Submodule.mapQ _ _ ((f.f n).hom.restrict (hT n))
    (fun c hc => hS n c hc))
  comm' i j _ := relative_hom_ext fun c => by
    change Submodule.Quotient.mk (T'.subDifferential i j ((f.f i).hom.restrict (hT i) c)) =
      Submodule.Quotient.mk ((f.f j).hom.restrict (hT j) (T.subDifferential i j c))
    congr 1
    apply Subtype.ext
    exact congrArg (fun g : K.X i ⟶ L.X j => g.hom c.1) (f.comm i j)

@[simp]
theorem mapOfChainMap_f_mk (f : K ⟶ L) {T S : ChainSubmodule K} {T' S' : ChainSubmodule L}
    (hT : ∀ n, ∀ c ∈ T.carrier n, (f.f n).hom c ∈ T'.carrier n)
    (hS : ∀ n, ∀ c ∈ S.carrier n, (f.f n).hom c ∈ S'.carrier n) (n : ℕ) (c : T.carrier n) :
    ((mapOfChainMap f hT hS).f n).hom (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk ((f.f n).hom.restrict (hT n) c) :=
  rfl

/-- Relative complexes are functorial for composable chain maps. -/
theorem mapOfChainMap_comp {M : ChainComplex (ModuleCat.{u} ℤ) ℕ} (f : K ⟶ L) (g : L ⟶ M)
    {T S : ChainSubmodule K} {T' S' : ChainSubmodule L} {T'' S'' : ChainSubmodule M}
    (hT : ∀ n, ∀ c ∈ T.carrier n, (f.f n).hom c ∈ T'.carrier n)
    (hS : ∀ n, ∀ c ∈ S.carrier n, (f.f n).hom c ∈ S'.carrier n)
    (hT' : ∀ n, ∀ c ∈ T'.carrier n, (g.f n).hom c ∈ T''.carrier n)
    (hS' : ∀ n, ∀ c ∈ S'.carrier n, (g.f n).hom c ∈ S''.carrier n) :
    mapOfChainMap f hT hS ≫ mapOfChainMap g hT' hS' =
      mapOfChainMap (f ≫ g) (fun n c hc => hT' n _ (hT n c hc)) (fun n c hc => hS' n _ (hS n c hc)) :=
  relativeComplex_hom_ext fun _ _ => rfl

/-- The identity chain map induces the identity on relative complexes. -/
theorem mapOfChainMap_id {T S : ChainSubmodule K}
    (hT : ∀ n, ∀ c ∈ T.carrier n, ((𝟙 K : K ⟶ K).f n).hom c ∈ T.carrier n)
    (hS : ∀ n, ∀ c ∈ S.carrier n, ((𝟙 K : K ⟶ K).f n).hom c ∈ S.carrier n) :
    mapOfChainMap (𝟙 K) hT hS = 𝟙 (relativeComplex T S) :=
  relativeComplex_hom_ext fun _ _ => rfl

end ChainMap

end ChainSubmodule
