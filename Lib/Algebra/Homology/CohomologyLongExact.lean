/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib

/-!
# The long exact cohomology sequence of a short exact sequence of cochain complexes of abelian
groups

The cochain-complex, abelian-group counterpart of
`Lib/AlgebraicTopology/SingularHomology/MayerVietoris/HomologyLongExact.lean`: for a short exact
sequence `S` of cochain complexes in `AddCommGrpCat` (indexed by `ℕ`, ascending shape), the
connecting homomorphism `connectingHom hS n : H^n(S.X₃) →+ H^{n+1}(S.X₁)` and the three exactness
statements of the long exact sequence, as equalities `AddMonoidHom.range = AddMonoidHom.ker`.

## Main definitions and results

* `CohomologyLongExact.cohomologyHom`, `CohomologyLongExact.connectingHom`.
* `CohomologyLongExact.exact_at_first`, `exact_at_second`, `exact_at_third`,
  `CohomologyLongExact.cohomologyHom_f_zero_injective`.

## Tags

cochain complex, long exact sequence, connecting homomorphism
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace CohomologyLongExact

/-- The map on cohomology induced by a map of cochain complexes of abelian groups. -/
abbrev cohomologyHom {K L : CochainComplex AddCommGrpCat.{0} ℕ} (f : K ⟶ L) (n : ℕ) :
    K.homology n →+ L.homology n :=
  (HomologicalComplex.homologyMap f n).hom

theorem cohomologyHom_comp {K L M : CochainComplex AddCommGrpCat.{0} ℕ} (f : K ⟶ L) (g : L ⟶ M)
    (n : ℕ) : cohomologyHom (f ≫ g) n = (cohomologyHom g n).comp (cohomologyHom f n) :=
  congrArg AddCommGrpCat.Hom.hom (HomologicalComplex.homologyMap_comp f g n)

/-- The connecting homomorphism `H^n(X₃) → H^{n+1}(X₁)` of a short exact sequence of cochain
complexes. -/
def connectingHom {S : ShortComplex (CochainComplex AddCommGrpCat.{0} ℕ)} (hS : S.ShortExact)
    (n : ℕ) : S.X₃.homology n →+ S.X₁.homology (n + 1) :=
  (hS.δ n (n + 1) (by simp)).hom

/-- Exactness at `H^{n+1}(X₁)`: the image of the connecting homomorphism is the kernel of
`H^{n+1}(X₁) → H^{n+1}(X₂)`. -/
theorem exact_at_first {S : ShortComplex (CochainComplex AddCommGrpCat.{0} ℕ)} (hS : S.ShortExact)
    (n : ℕ) :
    AddMonoidHom.range (connectingHom hS n) = AddMonoidHom.ker (cohomologyHom S.f (n + 1)) :=
  ShortComplex.ab_exact_iff_range_eq_ker.mp (hS.homology_exact₁ n (n + 1) (by simp))

/-- Exactness at `H^n(X₂)`. -/
theorem exact_at_second {S : ShortComplex (CochainComplex AddCommGrpCat.{0} ℕ)} (hS : S.ShortExact)
    (n : ℕ) :
    AddMonoidHom.range (cohomologyHom S.f n) = AddMonoidHom.ker (cohomologyHom S.g n) :=
  ShortComplex.ab_exact_iff_range_eq_ker.mp (hS.homology_exact₂ n)

/-- Exactness at `H^n(X₃)`. -/
theorem exact_at_third {S : ShortComplex (CochainComplex AddCommGrpCat.{0} ℕ)} (hS : S.ShortExact)
    (n : ℕ) :
    AddMonoidHom.range (cohomologyHom S.g n) = AddMonoidHom.ker (connectingHom hS n) :=
  ShortComplex.ab_exact_iff_range_eq_ker.mp (hS.homology_exact₃ n (n + 1) (by simp))

/-- `H^0(X₁) → H^0(X₂)` is injective. -/
theorem cohomologyHom_f_zero_injective {S : ShortComplex (CochainComplex AddCommGrpCat.{0} ℕ)}
    (hS : S.ShortExact) : Function.Injective (cohomologyHom S.f 0) := by
  have := hS.mono_f
  have := HomologicalComplex.mono_homologyMap_of_mono_of_not_rel S.f 0 (by intro i; simp)
  exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance

/-- The connecting homomorphism is natural in the short exact sequence. -/
theorem connectingHom_naturality {S T : ShortComplex (CochainComplex AddCommGrpCat.{0} ℕ)}
    (hS : S.ShortExact) (φ : S ⟶ T) (hT : T.ShortExact) (n : ℕ) :
    (cohomologyHom φ.τ₁ (n + 1)).comp (connectingHom hS n) =
      (connectingHom hT n).comp (cohomologyHom φ.τ₃ n) :=
  congrArg AddCommGrpCat.Hom.hom
    (HomologicalComplex.HomologySequence.δ_naturality φ hS hT n (n + 1) (by simp))

end CohomologyLongExact
