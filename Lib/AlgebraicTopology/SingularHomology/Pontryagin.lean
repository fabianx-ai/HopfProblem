/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
public import Lib.AlgebraicTopology.SingularHomology.CrossProduct

/-!
# The Pontryagin product on `H₁` of a topological abelian group

For a topological abelian group `G`, the Pontryagin product on degree-1 singular homology
is the cross product followed by the addition map on `G`:

```
product G n : H₁(G) → H_n(G) → H_{n+1}(G)
a ⋆ b = (additionMap G)_* (a × b)
```

The file contains the continuous addition maps (`additionMap`, `rightAdditionMap`,
`cyclicMap`) and their naturality and cyclicity lemmas, the bilinear `product`, its
`product11`/`product12` slices and the `tripleProduct`, the graded-commutativity laws
`product11_skew`, `product11_self` and the `tripleProduct_self*` family, and the generic
multilinear/alternating plumbing (`multilinearOfBilinear`, `alternatingOfBilinear`,
`skewBilinear_diagonal_zero`, `multilinearOfTrilinear`, `alternatingOfTrilinear`) used to
present the products as maps out of exterior powers of `H₁(G)`.

## References

Hatcher, *Algebraic Topology*, §3.C (Pontryagin products).
-/

@[expose] public noncomputable section

open SingularHomology

/-- The cyclic shuffle `Y × (Z × X) → X × (Y × Z)`, `(y, z, x) ↦ (x, y, z)`, as a continuous
map. -/
def PeriodTorusHigherHomologyPontryagin.cyclicMap (X Y Z : Type) [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] : C(Y × (Z × X), X × (Y × Z)) :=
  ⟨fun p => (p.2.2, (p.1, p.2.1)), by fun_prop⟩

/-- Addition `G × G → G` of a topological abelian group, as a continuous map. -/
def PeriodTorusHigherHomologyPontryagin.additionMap (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G] : C(G × G, G) :=
  ⟨fun p => p.1 + p.2, continuous_fst.add continuous_snd⟩

/-- The right-bracketed triple sum `G × (G × G) → G`, `(x, y, z) ↦ x + (y + z)`. -/
def PeriodTorusHigherHomologyPontryagin.rightAdditionMap (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G] : C(G × (G × G), G) :=
  (additionMap G).comp ((ContinuousMap.id G).prodMap (additionMap G))

/-- The triple sum is invariant under the cyclic shuffle of its three arguments. -/
@[simp]
theorem PeriodTorusHigherHomologyPontryagin.rightAdditionMap_comp_cyclic (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G] :
    (rightAdditionMap G).comp (cyclicMap G G G) = rightAdditionMap G := by
  ext p
  change p.2.2 + (p.1 + p.2.1) = p.1 + (p.2.1 + p.2.2)
  abel

/-- On singular homology, the triple sum is invariant under the cyclic shuffle. -/
theorem PeriodTorusHigherHomologyPontryagin.rightAddition_homology_cyclic (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G] (n : ℕ) :
    (SingularMayerVietoris.singularHomologyMap (rightAdditionMap G) n).comp
        (SingularMayerVietoris.singularHomologyMap (cyclicMap G G G) n) =
      SingularMayerVietoris.singularHomologyMap (rightAdditionMap G) n := by
  rw [← singularHomologyMap_comp, rightAdditionMap_comp_cyclic]

/-- An additive continuous map `f : G → H` commutes with addition: `f ∘ (+) = (+) ∘ (f × f)`. -/
theorem PeriodTorusHigherHomologyPontryagin.additionMap_natural {G : Type} [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G] {H : Type} [TopologicalSpace H] [AddCommGroup H]
    [IsTopologicalAddGroup H] (f : C(G, H)) (hf : ∀ x y, f (x + y) = f x + f y) :
    f.comp (additionMap G) = (additionMap H).comp (f.prodMap f) := by
  ext p
  exact hf p.1 p.2

/-- An additive continuous map `f : G → H` commutes with addition on singular homology. -/
theorem PeriodTorusHigherHomologyPontryagin.addition_homology_natural {G : Type}
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G] {H : Type}
    [TopologicalSpace H] [AddCommGroup H] [IsTopologicalAddGroup H] (f : C(G, H))
    (hf : ∀ x y, f (x + y) = f x + f y) (n : ℕ) :
    (SingularMayerVietoris.singularHomologyMap f n).comp
        (SingularMayerVietoris.singularHomologyMap (additionMap G) n) =
      (SingularMayerVietoris.singularHomologyMap (additionMap H) n).comp
        (SingularMayerVietoris.singularHomologyMap (f.prodMap f) n) := by
  rw [← singularHomologyMap_comp, additionMap_natural f hf,
    singularHomologyMap_comp]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The Pontryagin product `H₁(G) ⊗ Hₙ(G) → H_{n+1}(G)` of a topological abelian group: the
cross product followed by the map induced by addition (Hatcher, *Algebraic Topology*, §3.C). -/
def PeriodTorusHigherHomologyPontryagin.product (G : Type) [TopologicalSpace G] [AddCommGroup G]
    [IsTopologicalAddGroup G] (n : ℕ) :
    SingularMayerVietoris.SingularHomology G 1 →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology G n →ₗ[ℤ]
        SingularMayerVietoris.SingularHomology G (n + 1) :=
  SingularHomology.integerBilinearPostcompose
    (SingularHomology.crossProductHomology G G n)
    (SingularMayerVietoris.singularHomologyMap (additionMap G) (n + 1))

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The Pontryagin product of `a` and `b` is the pushforward along addition of `a × b`. -/
@[simp]
theorem PeriodTorusHigherHomologyPontryagin.product_apply (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G] (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology G 1)
    (b : SingularMayerVietoris.SingularHomology G n) :
    product G n a b =
      SingularMayerVietoris.singularHomologyMap (additionMap G) (n + 1)
        (SingularHomology.crossProductHomology G G n a b) :=
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The Pontryagin product `H₁(G) ⊗ H₁(G) → H₂(G)`. -/
abbrev PeriodTorusHigherHomologyPontryagin.product11 (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G] :
    SingularMayerVietoris.SingularHomology G 1 →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology G 1 →ₗ[ℤ]
        SingularMayerVietoris.SingularHomology G 2 :=
  product G 1

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The Pontryagin product `H₁(G) ⊗ H₂(G) → H₃(G)`. -/
abbrev PeriodTorusHigherHomologyPontryagin.product12 (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G] :
    SingularMayerVietoris.SingularHomology G 1 →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology G 2 →ₗ[ℤ]
        SingularMayerVietoris.SingularHomology G 3 :=
  product G 2

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The triple Pontryagin product `H₁(G)^{⊗3} → H₃(G)`, `(a, b, c) ↦ a ⋆ (b ⋆ c)`, as a
trilinear map. -/
def PeriodTorusHigherHomologyPontryagin.tripleProduct (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G] :
    SingularMayerVietoris.SingularHomology G 1 →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology G 1 →ₗ[ℤ]
        SingularMayerVietoris.SingularHomology G 1 →ₗ[ℤ]
          SingularMayerVietoris.SingularHomology G 3
    where
  toFun a := SingularHomology.integerBilinearPostcompose (product11 G) (product12 G a)
  map_add' a
    b := by
    apply LinearMap.ext
    intro c
    apply LinearMap.ext
    intro d
    exact
      congrArg
        (fun f :
            SingularMayerVietoris.SingularHomology G 2 →ₗ[ℤ]
              SingularMayerVietoris.SingularHomology G 3 =>
          f (product11 G c d))
        ((product12 G).map_add a b)
  map_smul' r
    a := by
    apply LinearMap.ext
    intro c
    apply LinearMap.ext
    intro d
    exact
      congrArg
        (fun f :
            SingularMayerVietoris.SingularHomology G 2 →ₗ[ℤ]
              SingularMayerVietoris.SingularHomology G 3 =>
          f (product11 G c d))
        ((product12 G).map_smul r a)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The triple Pontryagin product is `a ⋆ (b ⋆ c)`. -/
@[simp]
theorem PeriodTorusHigherHomologyPontryagin.tripleProduct_apply (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    (a b c : SingularMayerVietoris.SingularHomology G 1) :
    tripleProduct G a b c = product12 G a (product11 G b c) :=
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule in
/-- A bilinear map `M → M → N` read as a multilinear map on `Fin 2`-indexed families. -/
def PeriodTorusHigherHomologyPontryagin.multilinearOfBilinear {M N : Type*} [AddCommGroup M]
    [Module ℤ M] [AddCommGroup N] [Module ℤ N] (β : M →ₗ[ℤ] M →ₗ[ℤ] N) :
    MultilinearMap ℤ (fun _ : Fin 2 => M) N
    where
  toFun v := β (v 0) (v 1)
  map_update_add' {hDecEq} v i x
    y := by
    have heq : hDecEq = instDecidableEqFin 2 := Subsingleton.elim _ _
    subst hDecEq
    fin_cases i <;> simp
  map_update_smul' {hDecEq} v i r
    x := by
    have heq : hDecEq = instDecidableEqFin 2 := Subsingleton.elim _ _
    subst hDecEq
    fin_cases i <;> simp

attribute [local instance] SingularHomology.integerLinearMapModule in
/-- A bilinear map vanishing on the diagonal is an alternating map on `Fin 2`. -/
def PeriodTorusHigherHomologyPontryagin.alternatingOfBilinear {M N : Type*} [AddCommGroup M]
    [Module ℤ M] [AddCommGroup N] [Module ℤ N] (β : M →ₗ[ℤ] M →ₗ[ℤ] N)
    (hdiag : ∀ x : M, β x x = 0) : AlternatingMap ℤ M N (Fin 2)
    where
  toMultilinearMap := multilinearOfBilinear β
  map_eq_zero_of_eq' v i j hij
    hne := by
    have h : v 0 = v 1 := by fin_cases i <;> fin_cases j <;> simp_all
    change β (v 0) (v 1) = 0
    rw [h]
    exact hdiag _

attribute [local instance] SingularHomology.integerLinearMapModule in
/-- A skew-symmetric bilinear map into a torsion-free abelian group vanishes on the
diagonal. -/
theorem PeriodTorusHigherHomologyPontryagin.skewBilinear_diagonal_zero {M N : Type*}
    [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N] [Module.IsTorsionFree ℤ N]
    (β : M →ₗ[ℤ] M →ₗ[ℤ] N) (hskew : ∀ x y : M, β x y = -β y x) (x : M) : β x x = 0 := by
  apply (smul_eq_zero_iff_right (show (2 : ℤ) ≠ 0 by decide)).mp
  rw [two_smul ℤ]
  exact add_eq_zero_iff_eq_neg.mpr (hskew x x)

attribute [local instance] SingularHomology.integerLinearMapModule in
/-- A trilinear map `M → M → M → N` read as a multilinear map on `Fin 3`-indexed families. -/
def PeriodTorusHigherHomologyPontryagin.multilinearOfTrilinear {M N : Type*} [AddCommGroup M]
    [Module ℤ M] [AddCommGroup N] [Module ℤ N] (g : M →ₗ[ℤ] M →ₗ[ℤ] M →ₗ[ℤ] N) :
    MultilinearMap ℤ (fun _ : Fin 3 => M) N
    where
  toFun v := g (v 0) (v 1) (v 2)
  map_update_add' {hDecEq} v i x
    y := by
    have heq : hDecEq = instDecidableEqFin 3 := Subsingleton.elim _ _
    subst hDecEq
    fin_cases i <;> simp
  map_update_smul' {hDecEq} v i r
    x := by
    have heq : hDecEq = instDecidableEqFin 3 := Subsingleton.elim _ _
    subst hDecEq
    fin_cases i <;> simp

attribute [local instance] SingularHomology.integerLinearMapModule in
/-- A trilinear map vanishing whenever two of its three arguments agree is an alternating map
on `Fin 3`. -/
def PeriodTorusHigherHomologyPontryagin.alternatingOfTrilinear {M N : Type*} [AddCommGroup M]
    [Module ℤ M] [AddCommGroup N] [Module ℤ N] (g : M →ₗ[ℤ] M →ₗ[ℤ] M →ₗ[ℤ] N)
    (h01 : ∀ x z : M, g x x z = 0) (h02 : ∀ x y : M, g x y x = 0) (h12 : ∀ x y : M, g x y y = 0) :
    AlternatingMap ℤ M N (Fin 3)
    where
  toMultilinearMap := multilinearOfTrilinear g
  map_eq_zero_of_eq' v i j hij
    hne := by
    have h : v 0 = v 1 ∨ v 0 = v 2 ∨ v 1 = v 2 := by fin_cases i <;> fin_cases j <;> simp_all
    change g (v 0) (v 1) (v 2) = 0
    rcases h with h | h | h
    · rw [h]
      exact h01 _ _
    · rw [h]
      exact h02 _ _
    · rw [h]
      exact h12 _ _

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The Pontryagin product is natural for continuous additive maps:
`f_*(a ⋆ b) = f_* a ⋆ f_* b`. -/
theorem PeriodTorusHigherHomologyPontryagin.product_natural {G H : Type} [TopologicalSpace G]
    [TopologicalSpace H] [AddCommGroup G] [AddCommGroup H] [IsTopologicalAddGroup G]
    [IsTopologicalAddGroup H] (f : C(G, H)) (hf : ∀ x y, f (x + y) = f x + f y) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology G 1)
    (b : SingularMayerVietoris.SingularHomology G n) :
    SingularMayerVietoris.singularHomologyMap f (n + 1) (product G n a b) =
      product H n (SingularMayerVietoris.singularHomologyMap f 1 a)
        (SingularMayerVietoris.singularHomologyMap f n b) :=
  (LinearMap.congr_fun (addition_homology_natural f hf (n + 1))
        (SingularHomology.crossProductHomology G G n a b)).trans
    (congrArg (SingularMayerVietoris.singularHomologyMap (additionMap H) (n + 1))
      (PeriodTorusHigherHomology.crossProductHomology_natural f f n a b))

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The triple Pontryagin product is natural for continuous additive maps. -/
theorem PeriodTorusHigherHomologyPontryagin.tripleProduct_natural {G H : Type}
    [TopologicalSpace G] [TopologicalSpace H] [AddCommGroup G] [AddCommGroup H]
    [IsTopologicalAddGroup G] [IsTopologicalAddGroup H] (f : C(G, H))
    (hf : ∀ x y, f (x + y) = f x + f y) (a b c : SingularMayerVietoris.SingularHomology G 1) :
    SingularMayerVietoris.singularHomologyMap f 3 (tripleProduct G a b c) =
      tripleProduct H (SingularMayerVietoris.singularHomologyMap f 1 a)
        (SingularMayerVietoris.singularHomologyMap f 1 b)
        (SingularMayerVietoris.singularHomologyMap f 1 c) := by
  change
    SingularMayerVietoris.singularHomologyMap f 3 (product G 2 a (product G 1 b c)) =
      product H 2 (SingularMayerVietoris.singularHomologyMap f 1 a)
        (product H 1 (SingularMayerVietoris.singularHomologyMap f 1 b)
          (SingularMayerVietoris.singularHomologyMap f 1 c))
  rw [product_natural f hf 2, product_natural f hf 1]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The triple Pontryagin product is the triple cross product pushed forward along the
triple sum `G × (G × G) → G`. -/
theorem PeriodTorusHigherHomologyPontryagin.tripleProduct_eq_cross (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    (a b c : SingularMayerVietoris.SingularHomology G 1) :
    tripleProduct G a b c =
      SingularMayerVietoris.singularHomologyMap (rightAdditionMap G) 3
        (SingularHomology.crossProductHomology G (G × G) 2 a
          (SingularHomology.crossProductHomology G G 1 b c)) := by
  have h :=
    PeriodTorusHigherHomology.crossProductHomology_natural (ContinuousMap.id G) (additionMap G) 2
      a (SingularHomology.crossProductHomology G G 1 b c)
  change
    SingularMayerVietoris.singularHomologyMap ((ContinuousMap.id G).prodMap (additionMap G)) 3
        (SingularHomology.crossProductHomology G (G × G) 2 a
          (SingularHomology.crossProductHomology G G 1 b c)) =
      SingularHomology.crossProductHomology G G 2
        (SingularMayerVietoris.singularHomologyMap (ContinuousMap.id G) 1 a)
        (SingularMayerVietoris.singularHomologyMap (additionMap G) 2
          (SingularHomology.crossProductHomology G G 1 b c)) at h
  rw [SingularHomology.singularHomologyMap_id, LinearMap.id_apply] at h
  calc
    tripleProduct G a b c =
        SingularMayerVietoris.singularHomologyMap (additionMap G) 3
          (SingularHomology.crossProductHomology G G 2 a
            (SingularMayerVietoris.singularHomologyMap (additionMap G) 2
              (SingularHomology.crossProductHomology G G 1 b c))) :=
      rfl
    _ =
        SingularMayerVietoris.singularHomologyMap (additionMap G) 3
          (SingularMayerVietoris.singularHomologyMap
            ((ContinuousMap.id G).prodMap (additionMap G)) 3
            (SingularHomology.crossProductHomology G (G × G) 2 a
              (SingularHomology.crossProductHomology G G 1 b c))) :=
      (congrArg (SingularMayerVietoris.singularHomologyMap (additionMap G) 3) h.symm)
    _ = _ :=
      (LinearMap.congr_fun
          (SingularHomology.singularHomologyMap_comp
            ((ContinuousMap.id G).prodMap (additionMap G)) (additionMap G) 3)
          (SingularHomology.crossProductHomology G (G × G) 2 a
            (SingularHomology.crossProductHomology G G 1 b c))).symm

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The Pontryagin product on `H₁` is skew-symmetric: `a ⋆ b = -(b ⋆ a)`
(Hatcher §3.C, graded commutativity in degree `1 · 1`). -/
theorem PeriodTorusHigherHomologyPontryagin.product11_skew (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    (a b : SingularMayerVietoris.SingularHomology G 1) : product11 G a b = -product11 G b a :=
  PeriodTorusHigherHomology.crossProductHomology_pushforward_anticommute (additionMap G)
    (by ext p; exact add_comm p.2 p.1) a b

/-- When `H₂(G)` is torsion free, `a ⋆ a = 0` for every `a ∈ H₁(G)`. -/
theorem PeriodTorusHigherHomologyPontryagin.product11_self (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (a : SingularMayerVietoris.SingularHomology G 1) : product11 G a a = 0 :=
  skewBilinear_diagonal_zero (product11 G) (product11_skew G) a

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The Pontryagin product `H₁(G) × H₁(G) → H₂(G)` as an alternating map. -/
def PeriodTorusHigherHomologyPontryagin.homologyAlternatingTwo (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] :
    AlternatingMap ℤ (SingularMayerVietoris.SingularHomology G 1)
      (SingularMayerVietoris.SingularHomology G 2) (Fin 2) :=
  alternatingOfBilinear (product11 G) (product11_self G)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The induced linear map `⋀²H₁(G) → H₂(G)` from the Pontryagin product. -/
def PeriodTorusHigherHomologyPontryagin.homologyWedgeTwo (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] :
    (⋀[ℤ]^2 (SingularMayerVietoris.SingularHomology G 1)) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology G 2 :=
  exteriorPower.alternatingMapLinearEquiv (homologyAlternatingTwo G)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- On a decomposable wedge `v₀ ∧ v₁`, the map `⋀²H₁(G) → H₂(G)` is the Pontryagin product. -/
@[simp]
theorem PeriodTorusHigherHomologyPontryagin.homologyWedgeTwo_apply_ιMulti (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (v : Fin 2 → SingularMayerVietoris.SingularHomology G 1) :
    homologyWedgeTwo G (exteriorPower.ιMulti ℤ 2 v) = product11 G (v 0) (v 1) :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The triple Pontryagin product is invariant under a cyclic permutation of its arguments. -/
theorem PeriodTorusHigherHomologyPontryagin.tripleProduct_cyclic (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    (a b c : SingularMayerVietoris.SingularHomology G 1) :
    tripleProduct G a b c = tripleProduct G b c a := by
  rw [tripleProduct_eq_cross G a b c, tripleProduct_eq_cross G b c a,
    PeriodTorusHigherHomology.crossProductHomology_cyclic]
  have he : PeriodTorusHigherHomology.crossProductCyclicMap G G G = cyclicMap G G G := by
    apply ContinuousMap.ext
    intro p
    rfl
  rw [he]
  exact
    LinearMap.congr_fun (rightAddition_homology_cyclic G 3)
      (SingularHomology.crossProductHomology G (G × G) 2 b
        (SingularHomology.crossProductHomology G G 1 c a))

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The triple Pontryagin product vanishes when its last two arguments agree. -/
theorem PeriodTorusHigherHomologyPontryagin.tripleProduct_self12 (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (a b : SingularMayerVietoris.SingularHomology G 1) : tripleProduct G a b b = 0 := by
  rw [tripleProduct_apply, product11_self, map_zero]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The triple Pontryagin product vanishes when its first and last arguments agree. -/
theorem PeriodTorusHigherHomologyPontryagin.tripleProduct_self02 (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (a b : SingularMayerVietoris.SingularHomology G 1) : tripleProduct G a b a = 0 :=
  (tripleProduct_cyclic G a b a).trans (tripleProduct_self12 G b a)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The triple Pontryagin product vanishes when its first two arguments agree. -/
theorem PeriodTorusHigherHomologyPontryagin.tripleProduct_self01 (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (a b : SingularMayerVietoris.SingularHomology G 1) : tripleProduct G a a b = 0 :=
  (tripleProduct_cyclic G a a b).trans (tripleProduct_self02 G a b)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The triple Pontryagin product `H₁(G)³ → H₃(G)` as an alternating map. -/
def PeriodTorusHigherHomologyPontryagin.homologyAlternatingThree (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] :
    AlternatingMap ℤ (SingularMayerVietoris.SingularHomology G 1)
      (SingularMayerVietoris.SingularHomology G 3) (Fin 3) :=
  alternatingOfTrilinear (tripleProduct G) (tripleProduct_self01 G) (tripleProduct_self02 G)
    (tripleProduct_self12 G)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The induced linear map `⋀³H₁(G) → H₃(G)` from the triple Pontryagin product. -/
def PeriodTorusHigherHomologyPontryagin.homologyWedgeThree (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] :
    (⋀[ℤ]^3 (SingularMayerVietoris.SingularHomology G 1)) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology G 3 :=
  exteriorPower.alternatingMapLinearEquiv (homologyAlternatingThree G)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- On a decomposable wedge `v₀ ∧ v₁ ∧ v₂`, the map `⋀³H₁(G) → H₃(G)` is the triple
Pontryagin product. -/
@[simp]
theorem PeriodTorusHigherHomologyPontryagin.homologyWedgeThree_apply_ιMulti (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (v : Fin 3 → SingularMayerVietoris.SingularHomology G 1) :
    homologyWedgeThree G (exteriorPower.ιMulti ℤ 3 v) = tripleProduct G (v 0) (v 1) (v 2) :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _
