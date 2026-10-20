/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Homology.DerivedCategory.Ext.AcyclicResolutionH1Naturality

/-!
# Indexed acyclic resolutions and dimension shifting in every positive degree

An `AcyclicResolution` is an indexed tower of short exact sequences

`0 ⟶ Z n ⟶ X n ⟶ Z (n+1) ⟶ 0`.

Its associated cochain complex has differential `X n ⟶ Z (n+1) ⟶ X (n+1)`.
This presentation records the recursively chosen cycle objects as data.  Consequently, tails are
definitionally coherent and dimension shifting can be iterated without making new kernel choices.

For a fixed object `P`, the only hypothesis is positive `Ext`-acyclicity of every `X n`.  The main
comparison identifies `Ext^(n+1)(P,Z 0)` with degree-`n+1` homology of the cochain complex obtained
by applying `Ext⁰(P,-)` (equivalently `Hom(P,-)`) to the resolution.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.Ext

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! ## Connecting isomorphisms -/

section

variable [HasExt.{w} C]

/-- If the middle term vanishes in the relevant Ext degree, the connecting map is injective. -/
theorem connecting_injective (P : C) {S : ShortComplex C}
    (hS : S.ShortExact) (n : ℕ) [Subsingleton (Ext P S.X₂ n)] :
    Function.Injective (connecting P hS n) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, hy⟩ := (connecting_exact P hS n x).mp hx
  rw [← hy, Subsingleton.elim y 0]
  exact map_zero _

/-- If the middle term vanishes in two consecutive Ext degrees, the connecting map is bijective. -/
theorem connecting_bijective (P : C) {S : ShortComplex C}
    (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (Ext P S.X₂ n)] [Subsingleton (Ext P S.X₂ (n + 1))] :
    Function.Bijective (connecting P hS n) :=
  ⟨connecting_injective P hS n, connecting_surjective P hS n⟩

/-- Dimension shifting across a short exact sequence with acyclic middle term. -/
def connectingIso (P : C) {S : ShortComplex C}
    (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (Ext P S.X₂ n)] [Subsingleton (Ext P S.X₂ (n + 1))] :
    AddCommGrpCat.of (Ext P S.X₃ n) ≅ AddCommGrpCat.of (Ext P S.X₁ (n + 1)) :=
  (AddEquiv.ofBijective (connecting P hS n) (connecting_bijective P hS n)).toAddCommGrpIso

/-- Naturality of the connecting isomorphism. -/
@[reassoc]
theorem connectingIso_hom_naturality (P : C) {S T : ShortComplex C}
    (hS : S.ShortExact) (hT : T.ShortExact) (f : S ⟶ T) (n : ℕ)
    [Subsingleton (Ext P S.X₂ n)] [Subsingleton (Ext P S.X₂ (n + 1))]
    [Subsingleton (Ext P T.X₂ n)] [Subsingleton (Ext P T.X₂ (n + 1))] :
    (extFunctorObj P n).map f.τ₃ ≫ (connectingIso P hT n).hom =
      (connectingIso P hS n).hom ≫ (extFunctorObj P (n + 1)).map f.τ₁ := by
  ext x
  exact connecting_naturality P hS hT f n x

/-- Naturality in the direction used by dimension shifting. -/
@[reassoc]
theorem connectingIso_inv_naturality (P : C) {S T : ShortComplex C}
    (hS : S.ShortExact) (hT : T.ShortExact) (f : S ⟶ T) (n : ℕ)
    [Subsingleton (Ext P S.X₂ n)] [Subsingleton (Ext P S.X₂ (n + 1))]
    [Subsingleton (Ext P T.X₂ n)] [Subsingleton (Ext P T.X₂ (n + 1))] :
    (extFunctorObj P (n + 1)).map f.τ₁ ≫ (connectingIso P hT n).inv =
      (connectingIso P hS n).inv ≫ (extFunctorObj P n).map f.τ₃ := by
  let a : AddCommGrpCat.of (Ext P S.X₁ (n + 1)) ⟶
      AddCommGrpCat.of (Ext P T.X₁ (n + 1)) := (extFunctorObj P (n + 1)).map f.τ₁
  let b : AddCommGrpCat.of (Ext P S.X₃ n) ⟶
      AddCommGrpCat.of (Ext P T.X₃ n) := (extFunctorObj P n).map f.τ₃
  change a ≫ (connectingIso P hT n).inv = (connectingIso P hS n).inv ≫ b
  have hn : b ≫ (connectingIso P hT n).hom =
      (connectingIso P hS n).hom ≫ a :=
    connectingIso_hom_naturality P hS hT f n
  apply (cancel_mono (connectingIso P hT n).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Category.assoc, hn, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end

/-! ## Indexed resolutions -/

set_option genSizeOf false in
/-- An augmented acyclic resolution with explicit, coherently indexed cycle objects.

The intended interpretation is `Z 0 = F`; the `n`th short exact sequence is
`0 ⟶ Z n ⟶ X n ⟶ Z (n+1) ⟶ 0`.
-/
structure AcyclicResolution where
  Z : ℕ → C
  X : ℕ → C
  i : ∀ n, Z n ⟶ X n
  p : ∀ n, X n ⟶ Z (n + 1)
  zero : ∀ n, i n ≫ p n = 0
  shortExact : ∀ n, (ShortComplex.mk (i n) (p n) (zero n)).ShortExact

namespace AcyclicResolution

variable (R : AcyclicResolution (C := C))

/-- The `n`th short exact sequence in an indexed resolution. -/
abbrev step (n : ℕ) : ShortComplex C :=
  ShortComplex.mk (R.i n) (R.p n) (R.zero n)

/-- The differential `X n ⟶ X (n+1)` factors through the chosen cycle object `Z (n+1)`. -/
def d (n : ℕ) : R.X n ⟶ R.X (n + 1) :=
  R.p n ≫ R.i (n + 1)

@[reassoc (attr := simp)]
theorem i_d (n : ℕ) : R.i n ≫ R.d n = 0 := by
  rw [d, ← Category.assoc, R.zero, Limits.zero_comp]

@[reassoc (attr := simp)]
theorem d_p (n : ℕ) : R.d n ≫ R.p (n + 1) = 0 := by
  rw [d, Category.assoc, R.zero, Limits.comp_zero]

@[reassoc (attr := simp)]
theorem d_comp_d (n : ℕ) : R.d n ≫ R.d (n + 1) = 0 := by
  change R.d n ≫ (R.p (n + 1) ≫ R.i ((n + 1) + 1)) = 0
  rw [← Category.assoc, R.d_p, Limits.zero_comp]

/-- The literal cochain complex underlying the indexed resolution. -/
def complex : CochainComplex C ℕ :=
  CochainComplex.of R.X R.d R.d_comp_d

@[simp]
theorem complex_X (n : ℕ) : R.complex.X n = R.X n := rfl

@[simp]
theorem complex_d (n : ℕ) : R.complex.d n (n + 1) = R.d n :=
  by simp [complex]

/-- Discard the first short exact sequence. -/
def tail : AcyclicResolution (C := C) where
  Z n := R.Z (n + 1)
  X n := R.X (n + 1)
  i n := R.i (n + 1)
  p n := R.p (n + 1)
  zero n := R.zero (n + 1)
  shortExact n := R.shortExact (n + 1)

@[simp] theorem tail_Z (n : ℕ) : R.tail.Z n = R.Z (n + 1) := rfl
@[simp] theorem tail_X (n : ℕ) : R.tail.X n = R.X (n + 1) := rfl
@[simp] theorem tail_i (n : ℕ) : R.tail.i n = R.i (n + 1) := rfl
@[simp] theorem tail_p (n : ℕ) : R.tail.p n = R.p (n + 1) := rfl

/-- The short complex `Z n ⟶ X n ⟶ X (n+1)`. -/
abbrev augmentedStep (n : ℕ) : ShortComplex C :=
  ShortComplex.mk (R.i n) (R.d n) (R.i_d n)

/-- Exactness at the augmentation of every tail. -/
theorem augmentedStep_exact (n : ℕ) : (R.augmentedStep n).Exact := by
  let φ : R.step n ⟶ R.augmentedStep n :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := R.i (n + 1)
      comm₁₂ := by simp
      comm₂₃ := by simp [d] }
  have : Epi φ.τ₁ := inferInstanceAs (Epi (𝟙 (R.Z n)))
  have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 (R.X n)))
  have : Mono φ.τ₃ := (R.shortExact (n + 1)).mono_f
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp
    (R.shortExact n).exact

/-- The three consecutive terms around cohomological degree `n+1`. -/
abbrev localComplex (n : ℕ) : ShortComplex C :=
  ShortComplex.mk (R.d n) (R.d (n + 1)) (R.d_comp_d n)

/-- Exactness of the underlying complex at every positive degree. -/
theorem localComplex_exact (n : ℕ) : (R.localComplex n).Exact := by
  let T : ShortComplex C :=
    ShortComplex.mk (R.d n) (R.p (n + 1)) (R.d_p n)
  let φ : T ⟶ R.step (n + 1) :=
    { τ₁ := R.p n
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [T, d]
      comm₂₃ := by simp [T] }
  have hφ₁ : Epi φ.τ₁ := (R.shortExact n).epi_g
  have hφ₂ : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 (R.X (n + 1))))
  have hφ₃ : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 (R.Z (n + 2))))
  have hT : T.Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr
      (R.shortExact (n + 1)).exact
  let ψ : T ⟶ R.localComplex n :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := R.i (n + 2)
      comm₁₂ := by simp [T]
      comm₂₃ := by simp [T, d] }
  have hψ₁ : Epi ψ.τ₁ := inferInstanceAs (Epi (𝟙 (R.X n)))
  have hψ₂ : IsIso ψ.τ₂ := inferInstanceAs (IsIso (𝟙 (R.X (n + 1))))
  have hψ₃ : Mono ψ.τ₃ := (R.shortExact (n + 2)).mono_f
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).mp hT

/-- The degree-one truncation beginning at the `n`th chosen cycle object. -/
def trunc (n : ℕ) : AcyclicResolutionH1 (C := C) where
  F := R.Z n
  complex := R.localComplex n
  ι := R.i n
  zero := R.i_d n
  initial_exact := R.augmentedStep_exact n
  exact := R.localComplex_exact n
  mono_ι := (R.shortExact n).mono_f

@[simp] theorem trunc_F (n : ℕ) : (R.trunc n).F = R.Z n := rfl
@[simp] theorem trunc_X₁ (n : ℕ) : (R.trunc n).complex.X₁ = R.X n := rfl
@[simp] theorem trunc_X₂ (n : ℕ) : (R.trunc n).complex.X₂ = R.X (n + 1) := rfl
@[simp] theorem trunc_X₃ (n : ℕ) : (R.trunc n).complex.X₃ = R.X (n + 2) := rfl

/-! ## Maps of indexed resolutions -/

set_option genSizeOf false in
/-- A map of indexed acyclic resolutions, including the chosen cycle objects. -/
structure Hom (R S : AcyclicResolution (C := C)) where
  z : ∀ n, R.Z n ⟶ S.Z n
  x : ∀ n, R.X n ⟶ S.X n
  comm_i : ∀ n, z n ≫ S.i n = R.i n ≫ x n
  comm_p : ∀ n, x n ≫ S.p n = R.p n ≫ z (n + 1)

namespace Hom

variable {R S T : AcyclicResolution (C := C)}

/-- Identity map of an indexed resolution. -/
def id (R : AcyclicResolution (C := C)) : Hom R R where
  z _ := 𝟙 _
  x _ := 𝟙 _
  comm_i _ := by simp
  comm_p _ := by simp

/-- Composition of maps of indexed resolutions. -/
def comp (f : Hom R S) (g : Hom S T) : Hom R T where
  z n := f.z n ≫ g.z n
  x n := f.x n ≫ g.x n
  comm_i n := by
    calc
      (f.z n ≫ g.z n) ≫ T.i n = f.z n ≫ (g.z n ≫ T.i n) :=
        Category.assoc _ _ _
      _ = f.z n ≫ (S.i n ≫ g.x n) := congrArg (fun k ↦ f.z n ≫ k) (g.comm_i n)
      _ = (f.z n ≫ S.i n) ≫ g.x n := (Category.assoc _ _ _).symm
      _ = (R.i n ≫ f.x n) ≫ g.x n := congrArg (fun k ↦ k ≫ g.x n) (f.comm_i n)
      _ = R.i n ≫ (f.x n ≫ g.x n) := Category.assoc _ _ _
  comm_p n := by
    calc
      (f.x n ≫ g.x n) ≫ T.p n = f.x n ≫ (g.x n ≫ T.p n) :=
        Category.assoc _ _ _
      _ = f.x n ≫ (S.p n ≫ g.z (n + 1)) :=
        congrArg (fun k ↦ f.x n ≫ k) (g.comm_p n)
      _ = (f.x n ≫ S.p n) ≫ g.z (n + 1) := (Category.assoc _ _ _).symm
      _ = (R.p n ≫ f.z (n + 1)) ≫ g.z (n + 1) :=
        congrArg (fun k ↦ k ≫ g.z (n + 1)) (f.comm_p n)
      _ = R.p n ≫ (f.z (n + 1) ≫ g.z (n + 1)) := Category.assoc _ _ _

@[simp] theorem id_z (R : AcyclicResolution (C := C)) (n : ℕ) : (id R).z n = 𝟙 _ := rfl
@[simp] theorem id_x (R : AcyclicResolution (C := C)) (n : ℕ) : (id R).x n = 𝟙 _ := rfl
@[simp] theorem comp_z (f : Hom R S) (g : Hom S T) (n : ℕ) :
    (comp f g).z n = f.z n ≫ g.z n := rfl
@[simp] theorem comp_x (f : Hom R S) (g : Hom S T) (n : ℕ) :
    (comp f g).x n = f.x n ≫ g.x n := rfl

variable (f : Hom R S)

@[reassoc (attr := simp)]
theorem comm_i_assoc (n : ℕ) {Y : C} (k : S.X n ⟶ Y) :
    f.z n ≫ S.i n ≫ k = R.i n ≫ f.x n ≫ k := by
  rw [← Category.assoc, f.comm_i, Category.assoc]

@[reassoc (attr := simp)]
theorem comm_p_assoc (n : ℕ) {Y : C} (k : S.Z (n + 1) ⟶ Y) :
    f.x n ≫ S.p n ≫ k = R.p n ≫ f.z (n + 1) ≫ k := by
  rw [← Category.assoc, f.comm_p, Category.assoc]

/-- The induced map of the `n`th short exact sequences. -/
def stepMap (n : ℕ) : R.step n ⟶ S.step n where
  τ₁ := f.z n
  τ₂ := f.x n
  τ₃ := f.z (n + 1)
  comm₁₂ := f.comm_i n
  comm₂₃ := f.comm_p n

/-- The induced map after discarding the first step. -/
def tail : Hom R.tail S.tail where
  z n := f.z (n + 1)
  x n := f.x (n + 1)
  comm_i n := f.comm_i (n + 1)
  comm_p n := f.comm_p (n + 1)

@[reassoc]
theorem d_naturality (n : ℕ) :
    f.x n ≫ S.d n = R.d n ≫ f.x (n + 1) := by
  calc
    f.x n ≫ S.d n = (f.x n ≫ S.p n) ≫ S.i (n + 1) := by
      rw [d, Category.assoc]
    _ = (R.p n ≫ f.z (n + 1)) ≫ S.i (n + 1) := by rw [f.comm_p]
    _ = R.p n ≫ (f.z (n + 1) ≫ S.i (n + 1)) := by rw [Category.assoc]
    _ = R.p n ≫ (R.i (n + 1) ≫ f.x (n + 1)) := by rw [f.comm_i]
    _ = R.d n ≫ f.x (n + 1) := by rw [d, Category.assoc]

/-- The induced map of literal cochain complexes. -/
def complexMap : R.complex ⟶ S.complex :=
  CochainComplex.ofHom f.x (fun n ↦ by
    rw [R.complex_d, S.complex_d]
    exact f.d_naturality n)

@[simp]
theorem complexMap_id (R : AcyclicResolution (C := C)) :
    (id R).complexMap = 𝟙 R.complex := by
  ext n
  rfl

@[simp]
theorem complexMap_comp (f : Hom R S) (g : Hom S T) :
    (comp f g).complexMap = f.complexMap ≫ g.complexMap := by
  ext n
  rfl

/-- The induced map of degree-one truncations. -/
def truncMap (n : ℕ) : AcyclicResolutionH1.Hom (R.trunc n) (S.trunc n) where
  augmentation := f.z n
  complex :=
    { τ₁ := f.x n
      τ₂ := f.x (n + 1)
      τ₃ := f.x (n + 2)
      comm₁₂ := f.d_naturality n
      comm₂₃ := by
        change f.x (n + 1) ≫ S.d (n + 1) = R.d (n + 1) ≫ f.x (n + 2)
        simpa only [Nat.add_assoc, Nat.reduceAdd] using f.d_naturality (n + 1) }
  comm := f.comm_i n

end Hom

/-! ## Ext acyclicity and iteration -/

variable [HasExt.{w} C]

/-- Every resolution term is `Ext`-acyclic for `P` in every strictly positive degree. -/
def IsAcyclicFor (P : C) : Prop :=
  ∀ (i q : ℕ), 0 < q → Subsingleton (Ext P (R.X i) q)

theorem isAcyclicFor_tail (P : C) (h : R.IsAcyclicFor P) : R.tail.IsAcyclicFor P := by
  intro i q hq
  exact h (i + 1) q hq

/-- The coherent iteration of the positive-degree connecting isomorphisms.

After `n` shifts, `Ext^(n+1)(P,Z 0)` becomes `Ext¹(P,Z n)`.  The final degree-one
step is intentionally not included: it is a quotient comparison rather than a connecting
isomorphism unless `Hom(P,X n)` also vanishes.
-/
def shiftIso (P : C) :
    ∀ (R : AcyclicResolution (C := C)) (_h : R.IsAcyclicFor P) (n : ℕ),
      AddCommGrpCat.of (Ext P (R.Z 0) (n + 1)) ≅
        AddCommGrpCat.of (Ext P (R.Z n) 1)
  | R, _, 0 => Iso.refl _
  | R, _h, n + 1 => by
      letI : Subsingleton (Ext P (R.X 0) (n + 1)) := _h 0 (n + 1) (Nat.succ_pos n)
      letI : Subsingleton (Ext P (R.X 0) ((n + 1) + 1)) :=
        _h 0 ((n + 1) + 1) (Nat.succ_pos (n + 1))
      exact (connectingIso P (R.shortExact 0) (n + 1)).symm ≪≫
        shiftIso P R.tail (R.isAcyclicFor_tail P _h) n

@[simp]
theorem shiftIso_zero (P : C) (_h : R.IsAcyclicFor P) :
    R.shiftIso P _h 0 = Iso.refl _ := rfl

theorem shiftIso_succ (P : C) (h : R.IsAcyclicFor P) (n : ℕ) :
    R.shiftIso P h (n + 1) = by
      letI : Subsingleton (Ext P (R.X 0) (n + 1)) := h 0 (n + 1) (Nat.succ_pos n)
      letI : Subsingleton (Ext P (R.X 0) ((n + 1) + 1)) :=
        h 0 ((n + 1) + 1) (Nat.succ_pos (n + 1))
      exact (connectingIso P (R.shortExact 0) (n + 1)).symm ≪≫
        R.tail.shiftIso P (R.isAcyclicFor_tail P h) n := rfl

/-- Naturality of every iterated dimension shift under maps of indexed resolutions. -/
@[reassoc]
theorem Hom.shiftIso_naturality {R S : AcyclicResolution (C := C)}
    (f : Hom R S) (P : C) (hR : R.IsAcyclicFor P) (hS : S.IsAcyclicFor P) (n : ℕ) :
    (extFunctorObj P (n + 1)).map (f.z 0) ≫ (S.shiftIso P hS n).hom =
      (R.shiftIso P hR n).hom ≫ (extFunctorObj P 1).map (f.z n) := by
  induction n generalizing R S with
  | zero =>
      rw [R.shiftIso_zero, S.shiftIso_zero]
      change (extFunctorObj P 1).map (f.z 0) ≫ 𝟙 _ =
        𝟙 _ ≫ (extFunctorObj P 1).map (f.z 0)
      rw [Category.comp_id, Category.id_comp]
  | succ n ih =>
      let _ : Subsingleton (Ext P (R.X 0) (n + 1)) :=
        hR 0 (n + 1) (Nat.succ_pos n)
      let _ : Subsingleton (Ext P (R.X 0) ((n + 1) + 1)) :=
        hR 0 ((n + 1) + 1) (Nat.succ_pos (n + 1))
      let _ : Subsingleton (Ext P (S.X 0) (n + 1)) :=
        hS 0 (n + 1) (Nat.succ_pos n)
      let _ : Subsingleton (Ext P (S.X 0) ((n + 1) + 1)) :=
        hS 0 ((n + 1) + 1) (Nat.succ_pos (n + 1))
      let a : AddCommGrpCat.of (Ext P (R.Z 0) ((n + 1) + 1)) ⟶
          AddCommGrpCat.of (Ext P (S.Z 0) ((n + 1) + 1)) :=
        (extFunctorObj P ((n + 1) + 1)).map (f.z 0)
      let b : AddCommGrpCat.of (Ext P (R.tail.Z 0) (n + 1)) ⟶
          AddCommGrpCat.of (Ext P (S.tail.Z 0) (n + 1)) :=
        (extFunctorObj P (n + 1)).map (f.tail.z 0)
      let c : AddCommGrpCat.of (Ext P (R.tail.Z n) 1) ⟶
          AddCommGrpCat.of (Ext P (S.tail.Z n) 1) :=
        (extFunctorObj P 1).map (f.tail.z n)
      let δR : AddCommGrpCat.of (Ext P (R.Z 0) ((n + 1) + 1)) ⟶
          AddCommGrpCat.of (Ext P (R.tail.Z 0) (n + 1)) :=
        (connectingIso P (R.shortExact 0) (n + 1)).inv
      let δS : AddCommGrpCat.of (Ext P (S.Z 0) ((n + 1) + 1)) ⟶
          AddCommGrpCat.of (Ext P (S.tail.Z 0) (n + 1)) :=
        (connectingIso P (S.shortExact 0) (n + 1)).inv
      let rTail : AddCommGrpCat.of (Ext P (R.tail.Z 0) (n + 1)) ⟶
          AddCommGrpCat.of (Ext P (R.tail.Z n) 1) :=
        (R.tail.shiftIso P (R.isAcyclicFor_tail P hR) n).hom
      let sTail : AddCommGrpCat.of (Ext P (S.tail.Z 0) (n + 1)) ⟶
          AddCommGrpCat.of (Ext P (S.tail.Z n) 1) :=
        (S.tail.shiftIso P (S.isAcyclicFor_tail P hS) n).hom
      change a ≫ (δS ≫ sTail) = (δR ≫ rTail) ≫ c
      have hδ : a ≫ δS = δR ≫ b :=
        connectingIso_inv_naturality P (R.shortExact 0) (S.shortExact 0)
          (f.stepMap 0) (n + 1)
      have hTail : b ≫ sTail = rTail ≫ c :=
        ih f.tail (R.isAcyclicFor_tail P hR) (S.isAcyclicFor_tail P hS)
      calc
        a ≫ (δS ≫ sTail) = (a ≫ δS) ≫ sTail :=
          (Category.assoc _ _ _).symm
        _ = (δR ≫ b) ≫ sTail := by rw [hδ]
        _ = δR ≫ (b ≫ sTail) := Category.assoc _ _ _
        _ = δR ≫ (rTail ≫ c) := by rw [hTail]
        _ = (δR ≫ rTail) ≫ c := (Category.assoc _ _ _).symm

/-! ## Comparison with the evaluated complex -/

/-- Applying `Ext⁰(P,-)`, hence `Hom(P,-)`, to the literal resolution complex. -/
abbrev evaluatedComplex (P : C) : CochainComplex AddCommGrpCat.{w} ℕ :=
  CochainComplex.of (fun n ↦ (extFunctorObj P 0).obj (R.X n))
    (fun n ↦ (extFunctorObj P 0).map (R.d n)) (fun n ↦ by
      rw [← Functor.map_comp, R.d_comp_d, Functor.map_zero])

@[simp]
theorem evaluatedComplex_d (P : C) (n : ℕ) :
    (R.evaluatedComplex P).d n (n + 1) = (extFunctorObj P 0).map (R.d n) :=
  CochainComplex.of_d
    (fun k ↦ (extFunctorObj P 0).obj (R.X k))
    (fun k ↦ (extFunctorObj P 0).map (R.d k)) n

namespace Hom

variable {R S T : AcyclicResolution (C := C)} (f : Hom R S)

/-- Applying `Ext⁰(P,-)` to a map of indexed resolutions. -/
def evaluatedComplexMap (P : C) : R.evaluatedComplex P ⟶ S.evaluatedComplex P :=
  CochainComplex.ofHom (fun n ↦ (extFunctorObj P 0).map (f.x n)) (fun n ↦ by
    rw [R.evaluatedComplex_d, S.evaluatedComplex_d, ← Functor.map_comp,
      ← Functor.map_comp, f.d_naturality])

@[simp]
theorem evaluatedComplexMap_id (R : AcyclicResolution (C := C)) (P : C) :
    (id R).evaluatedComplexMap P = 𝟙 (R.evaluatedComplex P) := by
  apply HomologicalComplex.hom_ext
  intro n
  change (extFunctorObj P 0).map (𝟙 (R.X n)) = 𝟙 _
  exact (extFunctorObj P 0).map_id (R.X n)

@[simp]
theorem evaluatedComplexMap_comp (f : Hom R S) (g : Hom S T) (P : C) :
    (comp f g).evaluatedComplexMap P =
      f.evaluatedComplexMap P ≫ g.evaluatedComplexMap P := by
  apply HomologicalComplex.hom_ext
  intro n
  change (extFunctorObj P 0).map (f.x n ≫ g.x n) =
    (extFunctorObj P 0).map (f.x n) ≫ (extFunctorObj P 0).map (g.x n)
  exact (extFunctorObj P 0).map_comp (f.x n) (g.x n)

end Hom

/-- The short complex used by the degree-one truncation is the corresponding three-term
window in the evaluated cochain complex. -/
def evaluatedLocalIso (P : C) (n : ℕ) :
    (R.trunc n).extZeroComplex P ≅
      (R.evaluatedComplex P).sc' n (n + 1) ((n + 1) + 1) := by
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · change 𝟙 _ ≫ (R.evaluatedComplex P).d n (n + 1) =
      (extFunctorObj P 0).map (R.d n) ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
    exact CochainComplex.of_d
      (fun k ↦ (extFunctorObj P 0).obj (R.X k))
      (fun k ↦ (extFunctorObj P 0).map (R.d k)) n
  · change 𝟙 _ ≫ (R.evaluatedComplex P).d (n + 1) ((n + 1) + 1) =
      (extFunctorObj P 0).map (R.d (n + 1)) ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
    exact CochainComplex.of_d
      (fun k ↦ (extFunctorObj P 0).obj (R.X k))
      (fun k ↦ (extFunctorObj P 0).map (R.d k)) (n + 1)

namespace Hom

variable {R S : AcyclicResolution (C := C)} (f : Hom R S)

/-- The truncation comparison and the literal evaluated-complex window form a natural square. -/
@[reassoc]
theorem evaluatedLocalIso_naturality (P : C) (n : ℕ) :
    (f.truncMap n).extZeroMap P ≫ (S.evaluatedLocalIso P n).hom =
      (R.evaluatedLocalIso P n).hom ≫
        (HomologicalComplex.shortComplexFunctor' AddCommGrpCat (ComplexShape.up ℕ)
          n (n + 1) ((n + 1) + 1)).map (f.evaluatedComplexMap P) := by
  ext <;> rfl

/-- Naturality of the induced local homology identification. -/
@[reassoc]
theorem evaluatedLocalHomology_naturality (P : C) (n : ℕ) :
    ShortComplex.homologyMap ((f.truncMap n).extZeroMap P) ≫
        (ShortComplex.homologyMapIso (S.evaluatedLocalIso P n)).hom =
      (ShortComplex.homologyMapIso (R.evaluatedLocalIso P n)).hom ≫
        ShortComplex.homologyMap
          ((HomologicalComplex.shortComplexFunctor' AddCommGrpCat (ComplexShape.up ℕ)
            n (n + 1) ((n + 1) + 1)).map (f.evaluatedComplexMap P)) := by
  let H := ShortComplex.homologyFunctor AddCommGrpCat
  change H.map ((f.truncMap n).extZeroMap P) ≫
      H.map (S.evaluatedLocalIso P n).hom =
    H.map (R.evaluatedLocalIso P n).hom ≫
      H.map ((HomologicalComplex.shortComplexFunctor' AddCommGrpCat (ComplexShape.up ℕ)
        n (n + 1) ((n + 1) + 1)).map (f.evaluatedComplexMap P))
  simpa only [Functor.map_comp] using
    congrArg H.map (f.evaluatedLocalIso_naturality P n)

/-- Naturality of the inverse local-window identification used by `extIsoHomology`. -/
@[reassoc]
theorem evaluatedWindowIso_inv_naturality (P : C) (n : ℕ) :
    ShortComplex.homologyMap
          ((HomologicalComplex.shortComplexFunctor' AddCommGrpCat (ComplexShape.up ℕ)
            n (n + 1) ((n + 1) + 1)).map (f.evaluatedComplexMap P)) ≫
        ((S.evaluatedComplex P).homologyIsoSc'
          n (n + 1) ((n + 1) + 1) (by simp) (by simp)).inv =
      ((R.evaluatedComplex P).homologyIsoSc'
          n (n + 1) ((n + 1) + 1) (by simp) (by simp)).inv ≫
        HomologicalComplex.homologyMap (f.evaluatedComplexMap P) (n + 1) := by
  have hhom :
      HomologicalComplex.homologyMap (f.evaluatedComplexMap P) (n + 1) ≫
          ((S.evaluatedComplex P).homologyIsoSc'
            n (n + 1) ((n + 1) + 1) (by simp) (by simp)).hom =
        ((R.evaluatedComplex P).homologyIsoSc'
            n (n + 1) ((n + 1) + 1) (by simp) (by simp)).hom ≫
          ShortComplex.homologyMap
            ((HomologicalComplex.shortComplexFunctor' AddCommGrpCat (ComplexShape.up ℕ)
              n (n + 1) ((n + 1) + 1)).map (f.evaluatedComplexMap P)) := by
    let H := ShortComplex.homologyFunctor AddCommGrpCat
    change H.map
          ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (ComplexShape.up ℕ)
            (n + 1)).map (f.evaluatedComplexMap P)) ≫
        H.map ((HomologicalComplex.natIsoSc' AddCommGrpCat (ComplexShape.up ℕ)
          n (n + 1) ((n + 1) + 1) (by simp) (by simp)).hom.app (S.evaluatedComplex P)) =
      H.map ((HomologicalComplex.natIsoSc' AddCommGrpCat (ComplexShape.up ℕ)
          n (n + 1) ((n + 1) + 1) (by simp) (by simp)).hom.app (R.evaluatedComplex P)) ≫
        H.map ((HomologicalComplex.shortComplexFunctor' AddCommGrpCat (ComplexShape.up ℕ)
          n (n + 1) ((n + 1) + 1)).map (f.evaluatedComplexMap P))
    simpa only [Functor.map_comp] using congrArg H.map
      ((HomologicalComplex.natIsoSc' AddCommGrpCat (ComplexShape.up ℕ)
        n (n + 1) ((n + 1) + 1) (by simp) (by simp)).hom.naturality
          (f.evaluatedComplexMap P))
  let q := ShortComplex.homologyMap
    ((HomologicalComplex.shortComplexFunctor' AddCommGrpCat (ComplexShape.up ℕ)
      n (n + 1) ((n + 1) + 1)).map (f.evaluatedComplexMap P))
  let g := HomologicalComplex.homologyMap (f.evaluatedComplexMap P) (n + 1)
  let jR := (R.evaluatedComplex P).homologyIsoSc'
    n (n + 1) ((n + 1) + 1) (by simp) (by simp)
  let jS := (S.evaluatedComplex P).homologyIsoSc'
    n (n + 1) ((n + 1) + 1) (by simp) (by simp)
  change q ≫ jS.inv = jR.inv ≫ g
  have hhom' : g ≫ jS.hom = jR.hom ≫ q := hhom
  apply (cancel_mono jS.hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Category.assoc, hhom', ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end Hom

/-- The local three-term comparison in degree `n+1`. -/
def localExtIso (P : C) (h : R.IsAcyclicFor P) (n : ℕ) :
    AddCommGrpCat.of (Ext P (R.Z 0) (n + 1)) ≅
      ((R.trunc n).extZeroComplex P).homology := by
  letI : Subsingleton (Ext P (R.trunc n).complex.X₁ 1) := h n 1 Nat.zero_lt_one
  exact R.shiftIso P h n ≪≫ (R.trunc n).extOneIso P

/-- The finite degree-one staircase, with its acyclicity instance supplied by the tower. -/
def finiteStaircaseHomZero (P : C) (h : R.IsAcyclicFor P) :
    AddCommGrpCat.of (Ext P (R.Z 0) 1) ⟶ ((R.trunc 0).extZeroComplex P).homology := by
  let _ : Subsingleton (Ext P (R.trunc 0).complex.X₁ 1) := h 0 1 Nat.zero_lt_one
  exact ((R.trunc 0).extOneIso P).hom

/-- The finite degree-two staircase, with its acyclicity instances supplied by the tower. -/
def finiteStaircaseHomOne (P : C) (h : R.IsAcyclicFor P) :
    AddCommGrpCat.of (Ext P (R.Z 0) 2) ⟶ ((R.trunc 1).extZeroComplex P).homology := by
  let _ : Subsingleton (Ext P (R.X 0) 1) := h 0 1 Nat.zero_lt_one
  let _ : Subsingleton (Ext P (R.X 0) 2) := h 0 2 (by omega)
  let _ : Subsingleton (Ext P (R.trunc 1).complex.X₁ 1) := h 1 1 Nat.zero_lt_one
  exact (connectingIso P (R.shortExact 0) 1).inv ≫ ((R.trunc 1).extOneIso P).hom

/-- The finite degree-three staircase, with its acyclicity instances supplied by the tower. -/
def finiteStaircaseHomTwo (P : C) (h : R.IsAcyclicFor P) :
    AddCommGrpCat.of (Ext P (R.Z 0) 3) ⟶ ((R.trunc 2).extZeroComplex P).homology := by
  let _ : Subsingleton (Ext P (R.X 0) 2) := h 0 2 (by omega)
  let _ : Subsingleton (Ext P (R.X 0) 3) := h 0 3 (by omega)
  let _ : Subsingleton (Ext P (R.X 1) 1) := h 1 1 Nat.zero_lt_one
  let _ : Subsingleton (Ext P (R.X 1) 2) := h 1 2 (by omega)
  let _ : Subsingleton (Ext P (R.trunc 2).complex.X₁ 1) := h 2 1 Nat.zero_lt_one
  exact ((connectingIso P (R.shortExact 0) 2).inv ≫
    (connectingIso P (R.shortExact 1) 1).inv) ≫ ((R.trunc 2).extOneIso P).hom

/-- The indexed comparison in degree one is the original degree-one comparison. -/
theorem localExtIso_hom_zero (P : C) (h : R.IsAcyclicFor P) :
    (R.localExtIso P h 0).hom = R.finiteStaircaseHomZero P h := by
  unfold finiteStaircaseHomZero
  let _ : Subsingleton (Ext P (R.trunc 0).complex.X₁ 1) := h 0 1 Nat.zero_lt_one
  change 𝟙 _ ≫ ((R.trunc 0).extOneIso P).hom = ((R.trunc 0).extOneIso P).hom
  exact Category.id_comp _

/-- The indexed comparison in degree two is the original one-step finite staircase. -/
theorem localExtIso_hom_one (P : C) (h : R.IsAcyclicFor P) :
    (R.localExtIso P h 1).hom = R.finiteStaircaseHomOne P h := by
  unfold finiteStaircaseHomOne
  let _ : Subsingleton (Ext P (R.X 0) 1) := h 0 1 Nat.zero_lt_one
  let _ : Subsingleton (Ext P (R.X 0) 2) := h 0 2 (by omega)
  let _ : Subsingleton (Ext P (R.trunc 1).complex.X₁ 1) := h 1 1 Nat.zero_lt_one
  change ((connectingIso P (R.shortExact 0) 1).inv ≫ 𝟙 _) ≫
      ((R.trunc 1).extOneIso P).hom =
    (connectingIso P (R.shortExact 0) 1).inv ≫ ((R.trunc 1).extOneIso P).hom
  rw [Category.comp_id]

/-- The indexed comparison in degree three is the original two-step finite staircase. -/
theorem localExtIso_hom_two (P : C) (h : R.IsAcyclicFor P) :
    (R.localExtIso P h 2).hom = R.finiteStaircaseHomTwo P h := by
  unfold finiteStaircaseHomTwo
  let _ : Subsingleton (Ext P (R.X 0) 2) := h 0 2 (by omega)
  let _ : Subsingleton (Ext P (R.X 0) 3) := h 0 3 (by omega)
  let _ : Subsingleton (Ext P (R.X 1) 1) := h 1 1 Nat.zero_lt_one
  let _ : Subsingleton (Ext P (R.X 1) 2) := h 1 2 (by omega)
  let _ : Subsingleton (Ext P (R.trunc 2).complex.X₁ 1) := h 2 1 Nat.zero_lt_one
  change ((connectingIso P (R.shortExact 0) 2).inv ≫
      ((connectingIso P (R.shortExact 1) 1).inv ≫ 𝟙 _)) ≫
        ((R.trunc 2).extOneIso P).hom =
    ((connectingIso P (R.shortExact 0) 2).inv ≫
      (connectingIso P (R.shortExact 1) 1).inv) ≫
        ((R.trunc 2).extOneIso P).hom
  rw [Category.comp_id]

/-- Naturality of the local all-degree comparison. -/
@[reassoc]
theorem Hom.localExtIso_naturality {R S : AcyclicResolution (C := C)}
    (f : Hom R S) (P : C) (hR : R.IsAcyclicFor P) (hS : S.IsAcyclicFor P) (n : ℕ) :
    (extFunctorObj P (n + 1)).map (f.z 0) ≫ (S.localExtIso P hS n).hom =
      (R.localExtIso P hR n).hom ≫
        ShortComplex.homologyMap ((f.truncMap n).extZeroMap P) := by
  let _ : Subsingleton (Ext P (R.trunc n).complex.X₁ 1) :=
    hR n 1 Nat.zero_lt_one
  let _ : Subsingleton (Ext P (S.trunc n).complex.X₁ 1) :=
    hS n 1 Nat.zero_lt_one
  let a : AddCommGrpCat.of (Ext P (R.Z 0) (n + 1)) ⟶
      AddCommGrpCat.of (Ext P (S.Z 0) (n + 1)) :=
    (extFunctorObj P (n + 1)).map (f.z 0)
  let b : AddCommGrpCat.of (Ext P (R.Z n) 1) ⟶
      AddCommGrpCat.of (Ext P (S.Z n) 1) :=
    (extFunctorObj P 1).map (f.z n)
  let rShift := (R.shiftIso P hR n).hom
  let sShift := (S.shiftIso P hS n).hom
  let rOne := ((R.trunc n).extOneIso P).hom
  let sOne := ((S.trunc n).extOneIso P).hom
  let m := ShortComplex.homologyMap ((f.truncMap n).extZeroMap P)
  change a ≫ (sShift ≫ sOne) = (rShift ≫ rOne) ≫ m
  have hShift : a ≫ sShift = rShift ≫ b :=
    f.shiftIso_naturality P hR hS n
  have hOne : b ≫ sOne = rOne ≫ m :=
    (f.truncMap n).extOneIso_naturality P
  calc
    a ≫ (sShift ≫ sOne) = (a ≫ sShift) ≫ sOne :=
      (Category.assoc _ _ _).symm
    _ = (rShift ≫ b) ≫ sOne := by rw [hShift]
    _ = rShift ≫ (b ≫ sOne) := Category.assoc _ _ _
    _ = rShift ≫ (rOne ≫ m) :=
      congrArg (fun k ↦ rShift ≫ k) hOne
    _ = (rShift ≫ rOne) ≫ m := by rfl

/-- The all-positive-degree acyclic-resolution comparison with the homology of
the literal `Ext⁰(P,-)` complex. -/
def extIsoHomology (P : C) (h : R.IsAcyclicFor P) (n : ℕ) :
    AddCommGrpCat.of (Ext P (R.Z 0) (n + 1)) ≅
      (R.evaluatedComplex P).homology (n + 1) := by
  exact R.localExtIso P h n ≪≫
    ShortComplex.homologyMapIso (R.evaluatedLocalIso P n) ≪≫
      ((R.evaluatedComplex P).homologyIsoSc' n (n + 1) ((n + 1) + 1)
        (by simp) (by simp)).symm

private theorem compThreeNaturality {D : Type*} [Category* D]
    {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : D}
    (a : A₀ ⟶ B₀) (s₁ : B₀ ⟶ B₁) (s₂ : B₁ ⟶ B₂) (s₃ : B₂ ⟶ B₃)
    (r₁ : A₀ ⟶ A₁) (b : A₁ ⟶ B₁) (r₂ : A₁ ⟶ A₂) (c : A₂ ⟶ B₂)
    (r₃ : A₂ ⟶ A₃) (d : A₃ ⟶ B₃)
    (h₁ : a ≫ s₁ = r₁ ≫ b) (h₂ : b ≫ s₂ = r₂ ≫ c)
    (h₃ : c ≫ s₃ = r₃ ≫ d) :
    a ≫ ((s₁ ≫ s₂) ≫ s₃) = ((r₁ ≫ r₂) ≫ r₃) ≫ d := by
  calc
    a ≫ ((s₁ ≫ s₂) ≫ s₃) = (((a ≫ s₁) ≫ s₂) ≫ s₃) := by
      simp only [Category.assoc]
    _ = (((r₁ ≫ b) ≫ s₂) ≫ s₃) := by rw [h₁]
    _ = ((r₁ ≫ (b ≫ s₂)) ≫ s₃) :=
      congrArg (fun k ↦ k ≫ s₃) (Category.assoc _ _ _)
    _ = ((r₁ ≫ (r₂ ≫ c)) ≫ s₃) := by rw [h₂]
    _ = (((r₁ ≫ r₂) ≫ c) ≫ s₃) :=
      congrArg (fun k ↦ k ≫ s₃) (Category.assoc _ _ _).symm
    _ = ((r₁ ≫ r₂) ≫ (c ≫ s₃)) := Category.assoc _ _ _
    _ = ((r₁ ≫ r₂) ≫ (r₃ ≫ d)) := by rw [h₃]
    _ = (((r₁ ≫ r₂) ≫ r₃) ≫ d) :=
      (Category.assoc _ _ _).symm

/-- Naturality of the all-positive-degree comparison with literal complex homology. -/
@[reassoc]
theorem Hom.extIsoHomology_naturality {R S : AcyclicResolution (C := C)}
    (f : Hom R S) (P : C) (hR : R.IsAcyclicFor P) (hS : S.IsAcyclicFor P) (n : ℕ) :
    (extFunctorObj P (n + 1)).map (f.z 0) ≫ (S.extIsoHomology P hS n).hom =
      (R.extIsoHomology P hR n).hom ≫
        HomologicalComplex.homologyMap (f.evaluatedComplexMap P) (n + 1) := by
  let _ : Subsingleton (Ext P (R.trunc n).complex.X₁ 1) :=
    hR n 1 Nat.zero_lt_one
  let _ : Subsingleton (Ext P (S.trunc n).complex.X₁ 1) :=
    hS n 1 Nat.zero_lt_one
  let a := (extFunctorObj P (n + 1)).map (f.z 0)
  let lR := (R.localExtIso P hR n).hom
  let lS := (S.localExtIso P hS n).hom
  let m := ShortComplex.homologyMap ((f.truncMap n).extZeroMap P)
  let eR := (ShortComplex.homologyMapIso (R.evaluatedLocalIso P n)).hom
  let eS := (ShortComplex.homologyMapIso (S.evaluatedLocalIso P n)).hom
  let q := ShortComplex.homologyMap
    ((HomologicalComplex.shortComplexFunctor' AddCommGrpCat (ComplexShape.up ℕ)
      n (n + 1) ((n + 1) + 1)).map (f.evaluatedComplexMap P))
  let jR := ((R.evaluatedComplex P).homologyIsoSc'
    n (n + 1) ((n + 1) + 1) (by simp) (by simp)).inv
  let jS := ((S.evaluatedComplex P).homologyIsoSc'
    n (n + 1) ((n + 1) + 1) (by simp) (by simp)).inv
  let g := HomologicalComplex.homologyMap (f.evaluatedComplexMap P) (n + 1)
  change a ≫ ((lS ≫ eS) ≫ jS) = ((lR ≫ eR) ≫ jR) ≫ g
  have hLocal : a ≫ lS = lR ≫ m :=
    f.localExtIso_naturality P hR hS n
  have hEval : m ≫ eS = eR ≫ q :=
    f.evaluatedLocalHomology_naturality P n
  have hWindow : q ≫ jS = jR ≫ g :=
    f.evaluatedWindowIso_inv_naturality P n
  exact compThreeNaturality a lS eS jS lR m eR q jR g hLocal hEval hWindow

end AcyclicResolution

end CategoryTheory.Abelian.Ext
