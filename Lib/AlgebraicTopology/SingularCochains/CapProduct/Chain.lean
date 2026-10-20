/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.Chains

/-!
# The cap and cup products on singular chains

For a topological space `X`, a `k`-cochain `φ : Cochain X k = (Chains X k →ₗ[ℤ] ℤ)` and a singular
`m`-simplex `σ` with `m = k + l`, the cap product is
`σ ⌢ φ = φ(σ|[v_0, …, v_k]) · σ|[v_k, …, v_m]` (Hatcher §3.3), extended linearly to chains
(`capChain k l m h φ : Chains X m →ₗ[ℤ] Chains X l`), and the cup product of `φ` with an
`l`-cochain `ψ` is `(φ ∪ ψ)(σ) = φ(σ|[v_0, …, v_k]) · ψ(σ|[v_k, …, v_m])` (Hatcher §3.2), that is
`ψ(σ ⌢ φ)` (`cupChain`).  The two Leibniz formulas are

* `boundary_capChain` : `∂(c ⌢ φ) = (-1)^k (∂c ⌢ φ - c ⌢ δφ)`;
* `coboundary_cupChain` : `δ(φ ∪ ψ) = δφ ∪ ψ + (-1)^k φ ∪ δψ`,

and both products are natural in continuous maps (`inducedChain_capChain`,
`pullback_cupChain`).  In top degree the cap product is evaluation times the last vertex
(`capSimplex_top`).

## Outline of the proof

1. *Front and back faces.*  `frontFun`, `backFun` (the vertex maps `i ↦ i`, `i ↦ k + i`),
   `frontFace`, `backFace` as `simplexMap`s of the standard simplex; `simplexMap_comp` and
   `simplexFace_eq_simplexMap` reduce every composite of faces to a `Fin`-function.
2. *Face identities.*  For the `i`-th face `δ_i` of an `(k + l + 1)`-simplex:
   if `i ≤ k`, the front `k`-face of `σ ∘ δ_i` is the `i`-th face of the front `(k + 1)`-face
   of `σ` and its back `l`-face is the back `l`-face of `σ` from `v_{k+1}`
   (`comp_simplexFace_comp_frontFace_of_le`, `comp_simplexFace_comp_backFace_of_le`);
   if `i = k + 1 + j`, the front `k`-face of `σ ∘ δ_i` is the front `k`-face of `σ` and its
   back `l`-face is the `(j + 1)`-st face of the back `(l + 1)`-face of `σ`
   (`comp_simplexFace_comp_frontFace_of_gt`, `comp_simplexFace_comp_backFace_of_gt`).
   The last face of the front `(k + 1)`-face is the front `k`-face, and the zeroth face of the
   back `(l + 1)`-face is the back `l`-face from `v_{k+1}`.
3. *The Leibniz formula for the cap product.*  Split `∂σ ⌢ φ` into the faces `i ≤ k` and
   `i ≥ k + 1` (`sum_fin_split`); the first part is `δφ(front σ) · back σ` up to the missing
   last face of the front, the second part is `(-1)^k φ(front σ) · ∂(back σ)` up to the
   missing zeroth face of the back; the two corrections are the same chain
   (`boundary_capSimplex`, `boundary_capChain`).
4. *The cup product.*  Evaluating `ψ` on the cap formula gives the coboundary formula
   (`coboundary_cupChain`).
5. *Naturality.*  `inducedChain_capChain`, `pullback_cupChain`.

## Main definitions and results

* `SingularCapProduct.Cochain`, `SingularCapProduct.coboundary`, `SingularCapProduct.pullback` :
  integral singular cochains, their coboundary and their pullback.
* `SingularCapProduct.frontFace`, `SingularCapProduct.backFace` : front and back faces.
* `SingularCapProduct.capSimplex`, `SingularCapProduct.capChain`,
  `SingularCapProduct.cupChain` : the cap and cup products.
* `SingularCapProduct.boundary_capChain`, `SingularCapProduct.coboundary_cupChain` : the
  Leibniz formulas.
* `SingularCapProduct.inducedChain_capChain`, `SingularCapProduct.pullback_cupChain` :
  naturality.
* `SingularCapProduct.capSimplex_top` : the cap product in top degree.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], §3.2 (cup product, Lemma 3.6) and §3.3
  (cap product, the formula before Proposition 3.25 and its naturality)

## Tags

cap product, cup product, singular cochains, Leibniz formula, front face, back face
-/

open Set Function
open scoped CategoryTheory

@[expose] public noncomputable section

namespace SingularCapProduct

open SingularChains

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-! ### Cochains -/

/-- `k`-cochains of `X` with integer coefficients, as linear functionals on `k`-chains. -/
abbrev Cochain (X : Type) [TopologicalSpace X] (k : ℕ) :=
  Chains X k →ₗ[ℤ] ℤ

/-- The coboundary `δφ = φ ∘ ∂` of a singular cochain. -/
def coboundary (k : ℕ) (φ : Cochain X k) : Cochain X (k + 1) :=
  φ.comp ((singularComplex X).d (k + 1) k).hom

/-- The pullback `f^* ψ = ψ ∘ f_*` of a cochain along a continuous map `f`. -/
def pullback (f : C(X, Y)) (k : ℕ) (ψ : Cochain Y k) : Cochain X k :=
  ψ.comp (inducedChain f k)

/-- The coboundary evaluates the cochain on the boundary. -/
theorem coboundary_apply (k : ℕ) (φ : Cochain X k) (c : Chains X (k + 1)) :
    coboundary k φ c = φ (((singularComplex X).d (k + 1) k).hom c) :=
  rfl

/-- The pullback evaluates the cochain on the pushed-forward chain. -/
theorem pullback_apply (f : C(X, Y)) (k : ℕ) (ψ : Cochain Y k) (c : Chains X k) :
    pullback f k ψ c = ψ (inducedChain f k c) :=
  rfl

/-! ### Maps of standard simplices

A map of vertex sets `Fin (a + 1) → Fin (b + 1)` induces the affine map of standard simplices;
composites of faces are reduced to composites of vertex maps. -/

/-- The affine map `Δ^a → Δ^b` induced by a map of vertices `Fin (a + 1) → Fin (b + 1)`. -/
def simplexMap {a b : ℕ} (f : Fin (a + 1) → Fin (b + 1)) : C(Simplex a, Simplex b) :=
  ⟨stdSimplex.map f, stdSimplex.continuous_map f⟩

/-- `simplexMap` evaluates as `stdSimplex.map`. -/
@[simp]
theorem simplexMap_apply {a b : ℕ} (f : Fin (a + 1) → Fin (b + 1)) (s : Simplex a) :
    simplexMap f s = stdSimplex.map f s :=
  rfl

/-- `simplexMap` is functorial: the composite of induced maps is induced by the composite. -/
theorem simplexMap_comp {a b c : ℕ} (g : Fin (b + 1) → Fin (c + 1)) (f : Fin (a + 1) → Fin (b + 1)) :
    (simplexMap g).comp (simplexMap f) = simplexMap (g ∘ f) :=
  ContinuousMap.ext fun s => stdSimplex.map_comp_apply f g s

/-- `simplexMap` of the identity is the identity. -/
theorem simplexMap_id (a : ℕ) : simplexMap (id : Fin (a + 1) → Fin (a + 1)) = ContinuousMap.id _ :=
  ContinuousMap.ext fun s => stdSimplex.map_id_apply s

/-- The `i`-th face inclusion is induced by the vertex map `Fin.succAbove i`. -/
theorem simplexFace_eq_simplexMap (n : ℕ) (i : Fin (n + 2)) :
    simplexFace n i = simplexMap i.succAbove :=
  ContinuousMap.ext fun _ => rfl

/-- Composing a singular simplex with two induced maps is composing with the composite. -/
theorem comp_simplexMap_comp_simplexMap {a b c : ℕ} (σ : C(Simplex c, X))
    (g : Fin (b + 1) → Fin (c + 1)) (f : Fin (a + 1) → Fin (b + 1)) :
    (σ.comp (simplexMap g)).comp (simplexMap f) = σ.comp (simplexMap (g ∘ f)) := by
  rw [ContinuousMap.comp_assoc, simplexMap_comp]

/-- `Fin.succAbove i` fixes the values below `i`. -/
theorem val_succAbove_of_lt {n : ℕ} (i : Fin (n + 1)) (j : Fin n) (h : j.val < i.val) :
    (i.succAbove j).val = j.val := by
  rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simpa using h)]
  simp

/-- `Fin.succAbove i` shifts the values from `i` on by one. -/
theorem val_succAbove_of_ge {n : ℕ} (i : Fin (n + 1)) (j : Fin n) (h : i.val ≤ j.val) :
    (i.succAbove j).val = j.val + 1 := by
  rw [Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simpa using h)]
  simp

/-! ### Front and back faces -/

/-- The vertex map of the front face `[v_0, …, v_k] ⊆ [v_0, …, v_m]` for `k + l = m`. -/
def frontFun (k l m : ℕ) (h : k + l = m) : Fin (k + 1) → Fin (m + 1) :=
  fun i => ⟨i, by omega⟩

/-- The vertex map of the back face `[v_k, …, v_m] ⊆ [v_0, …, v_m]` for `k + l = m`. -/
def backFun (k l m : ℕ) (h : k + l = m) : Fin (l + 1) → Fin (m + 1) :=
  fun i => ⟨k + i, by omega⟩

/-- The front face `Δ^k → Δ^m`, `k + l = m`, onto the first `k + 1` vertices. -/
def frontFace (k l m : ℕ) (h : k + l = m) : C(Simplex k, Simplex m) :=
  simplexMap (frontFun k l m h)

/-- The back face `Δ^l → Δ^m`, `k + l = m`, onto the last `l + 1` vertices. -/
def backFace (k l m : ℕ) (h : k + l = m) : C(Simplex l, Simplex m) :=
  simplexMap (backFun k l m h)

/-- The value of the front vertex map. -/
@[simp]
theorem val_frontFun (k l m : ℕ) (h : k + l = m) (i : Fin (k + 1)) :
    (frontFun k l m h i).val = i.val :=
  rfl

/-- The value of the back vertex map. -/
@[simp]
theorem val_backFun (k l m : ℕ) (h : k + l = m) (i : Fin (l + 1)) :
    (backFun k l m h i).val = k + i.val :=
  rfl

/-- The front face in top degree is the identity vertex map. -/
theorem frontFun_top (k : ℕ) (h : k + 0 = k) : frontFun k 0 k h = id :=
  funext fun _ => Fin.ext rfl

/-- The front face in top degree is the identity of the simplex. -/
theorem frontFace_top (k : ℕ) (h : k + 0 = k) : frontFace k 0 k h = ContinuousMap.id _ := by
  rw [frontFace, frontFun_top, simplexMap_id]

/-! ### Face identities

The faces of an `(k + l + 1)`-simplex `σ` split into those that delete a front vertex
(`i ≤ k`) and those that delete a back vertex (`i = k + 1 + j`).  Each identity is an equality
of vertex maps, checked on values. -/

section FaceIdentities

variable (k l : ℕ)

/-- Deleting the front vertex `a ≤ k`, then taking the front `k`-face, is the front
`(k + 1)`-face followed by the `a`-th face. -/
theorem succAbove_comp_frontFun_of_le (a : Fin (k + 1)) (h : k + 1 + l = k + l + 1) :
    (⟨a, by omega⟩ : Fin (k + l + 2)).succAbove ∘ frontFun k l (k + l) rfl =
      frontFun (k + 1) l (k + l + 1) h ∘ a.castSucc.succAbove := by
  funext x
  apply Fin.ext
  rw [Function.comp_apply, Function.comp_apply, val_frontFun (k + 1)]
  rcases Nat.lt_or_ge x.val a.val with hx | hx
  · rw [val_succAbove_of_lt (⟨a, by omega⟩ : Fin (k + l + 2)) (frontFun k l (k + l) rfl x) hx,
      val_succAbove_of_lt a.castSucc x hx, val_frontFun]
  · rw [val_succAbove_of_ge (⟨a, by omega⟩ : Fin (k + l + 2)) (frontFun k l (k + l) rfl x) hx,
      val_succAbove_of_ge a.castSucc x hx, val_frontFun]

/-- Deleting the front vertex `a ≤ k`, then taking the back `l`-face, is the back `l`-face
from `v_{k+1}`. -/
theorem succAbove_comp_backFun_of_le (a : Fin (k + 1)) (h : k + 1 + l = k + l + 1) :
    (⟨a, by omega⟩ : Fin (k + l + 2)).succAbove ∘ backFun k l (k + l) rfl =
      backFun (k + 1) l (k + l + 1) h := by
  funext x
  apply Fin.ext
  have ha := a.isLt
  rw [Function.comp_apply, val_succAbove_of_ge (⟨a, by omega⟩ : Fin (k + l + 2))
    (backFun k l (k + l) rfl x) (by simp only [val_backFun]; omega), val_backFun, val_backFun]
  omega

/-- Deleting the back vertex `k + 1 + j`, then taking the front `k`-face, is the front
`k`-face. -/
theorem succAbove_comp_frontFun_of_gt (j : Fin (l + 1)) :
    (⟨k + 1 + j, by omega⟩ : Fin (k + l + 2)).succAbove ∘ frontFun k l (k + l) rfl =
      frontFun k (l + 1) (k + l + 1) rfl := by
  funext x
  apply Fin.ext
  have hx := x.isLt
  rw [Function.comp_apply, val_succAbove_of_lt (⟨k + 1 + j, by omega⟩ : Fin (k + l + 2))
    (frontFun k l (k + l) rfl x) (by simp only [val_frontFun]; omega), val_frontFun, val_frontFun]

/-- Deleting the back vertex `k + 1 + j`, then taking the back `l`-face, is the back
`(l + 1)`-face followed by its `(j + 1)`-st face. -/
theorem succAbove_comp_backFun_of_gt (j : Fin (l + 1)) :
    (⟨k + 1 + j, by omega⟩ : Fin (k + l + 2)).succAbove ∘ backFun k l (k + l) rfl =
      backFun k (l + 1) (k + l + 1) rfl ∘ j.succ.succAbove := by
  funext x
  apply Fin.ext
  rw [Function.comp_apply, Function.comp_apply, val_backFun k (l + 1)]
  rcases Nat.lt_or_ge x.val (j.val + 1) with hx | hx
  · rw [val_succAbove_of_lt (⟨k + 1 + j, by omega⟩ : Fin (k + l + 2)) (backFun k l (k + l) rfl x)
      (by simp only [val_backFun]; omega), val_succAbove_of_lt j.succ x (by simpa using hx),
      val_backFun]
  · rw [val_succAbove_of_ge (⟨k + 1 + j, by omega⟩ : Fin (k + l + 2)) (backFun k l (k + l) rfl x)
      (by simp only [val_backFun]; omega), val_succAbove_of_ge j.succ x (by simpa using hx),
      val_backFun]
    omega

/-- The last face of the front `(k + 1)`-face is the front `k`-face. -/
theorem frontFun_comp_succAbove_last (h : k + 1 + l = k + l + 1) :
    frontFun (k + 1) l (k + l + 1) h ∘ (Fin.last (k + 1)).succAbove =
      frontFun k (l + 1) (k + l + 1) rfl := by
  funext x
  apply Fin.ext
  have hx := x.isLt
  rw [Function.comp_apply, val_frontFun, val_frontFun,
    val_succAbove_of_lt (Fin.last (k + 1)) x (by simp only [Fin.val_last]; omega)]

/-- The zeroth face of the back `(l + 1)`-face is the back `l`-face from `v_{k+1}`. -/
theorem backFun_comp_succAbove_zero (h : k + 1 + l = k + l + 1) :
    backFun k (l + 1) (k + l + 1) rfl ∘ (0 : Fin (l + 2)).succAbove =
      backFun (k + 1) l (k + l + 1) h := by
  funext x
  apply Fin.ext
  rw [Function.comp_apply, val_backFun, val_backFun,
    val_succAbove_of_ge (0 : Fin (l + 2)) x (by simp only [Fin.val_zero]; omega)]
  omega

variable {k l}

/-- Front face of the `a`-th face, `a ≤ k`, of a singular `(k + l + 1)`-simplex. -/
theorem comp_simplexFace_comp_frontFace_of_le (σ : SingularSimplex X (k + l + 1))
    (a : Fin (k + 1)) (h : k + 1 + l = k + l + 1) :
    (σ.comp (simplexFace (k + l) ⟨a, by omega⟩)).comp (frontFace k l (k + l) rfl) =
      (σ.comp (frontFace (k + 1) l (k + l + 1) h)).comp (simplexFace k a.castSucc) := by
  rw [simplexFace_eq_simplexMap, simplexFace_eq_simplexMap, frontFace, frontFace,
    comp_simplexMap_comp_simplexMap, comp_simplexMap_comp_simplexMap,
    succAbove_comp_frontFun_of_le k l a h]

/-- Back face of the `a`-th face, `a ≤ k`, of a singular `(k + l + 1)`-simplex. -/
theorem comp_simplexFace_comp_backFace_of_le (σ : SingularSimplex X (k + l + 1))
    (a : Fin (k + 1)) (h : k + 1 + l = k + l + 1) :
    (σ.comp (simplexFace (k + l) ⟨a, by omega⟩)).comp (backFace k l (k + l) rfl) =
      σ.comp (backFace (k + 1) l (k + l + 1) h) := by
  rw [simplexFace_eq_simplexMap, backFace, backFace, comp_simplexMap_comp_simplexMap,
    succAbove_comp_backFun_of_le k l a h]

/-- Front face of the `(k + 1 + j)`-th face of a singular `(k + l + 1)`-simplex. -/
theorem comp_simplexFace_comp_frontFace_of_gt (σ : SingularSimplex X (k + l + 1))
    (j : Fin (l + 1)) :
    (σ.comp (simplexFace (k + l) ⟨k + 1 + j, by omega⟩)).comp (frontFace k l (k + l) rfl) =
      σ.comp (frontFace k (l + 1) (k + l + 1) rfl) := by
  rw [simplexFace_eq_simplexMap, frontFace, frontFace, comp_simplexMap_comp_simplexMap,
    succAbove_comp_frontFun_of_gt k l j]

/-- Back face of the `(k + 1 + j)`-th face of a singular `(k + l + 1)`-simplex. -/
theorem comp_simplexFace_comp_backFace_of_gt (σ : SingularSimplex X (k + l + 1))
    (j : Fin (l + 1)) :
    (σ.comp (simplexFace (k + l) ⟨k + 1 + j, by omega⟩)).comp (backFace k l (k + l) rfl) =
      (σ.comp (backFace k (l + 1) (k + l + 1) rfl)).comp (simplexFace l j.succ) := by
  rw [simplexFace_eq_simplexMap, simplexFace_eq_simplexMap, backFace, backFace,
    comp_simplexMap_comp_simplexMap, comp_simplexMap_comp_simplexMap,
    succAbove_comp_backFun_of_gt k l j]

/-- The last face of the front `(k + 1)`-face of a singular simplex is its front `k`-face. -/
theorem comp_frontFace_comp_simplexFace_last (σ : SingularSimplex X (k + l + 1))
    (h : k + 1 + l = k + l + 1) :
    (σ.comp (frontFace (k + 1) l (k + l + 1) h)).comp (simplexFace k (Fin.last (k + 1))) =
      σ.comp (frontFace k (l + 1) (k + l + 1) rfl) := by
  rw [simplexFace_eq_simplexMap, frontFace, frontFace, comp_simplexMap_comp_simplexMap,
    frontFun_comp_succAbove_last k l h]

/-- The zeroth face of the back `(l + 1)`-face of a singular simplex is its back `l`-face from
`v_{k+1}`. -/
theorem comp_backFace_comp_simplexFace_zero (σ : SingularSimplex X (k + l + 1))
    (h : k + 1 + l = k + l + 1) :
    (σ.comp (backFace k (l + 1) (k + l + 1) rfl)).comp (simplexFace l 0) =
      σ.comp (backFace (k + 1) l (k + l + 1) h) := by
  rw [simplexFace_eq_simplexMap, backFace, backFace, comp_simplexMap_comp_simplexMap,
    backFun_comp_succAbove_zero k l h]

end FaceIdentities

/-! ### The cap and cup products -/

/-- The cap product of a singular `m`-simplex with a `k`-cochain, `k + l = m`:
`σ ⌢ φ = φ(σ|[v_0, …, v_k]) · σ|[v_k, …, v_m]` (Hatcher §3.3). -/
def capSimplex (k l m : ℕ) (h : k + l = m) (φ : Cochain X k) (σ : SingularSimplex X m) :
    Chains X l :=
  φ (simplexChain X k (σ.comp (frontFace k l m h))) • simplexChain X l (σ.comp (backFace k l m h))

/-- The cap product with a `k`-cochain as a linear map `C_m(X) → C_l(X)`, `k + l = m`. -/
def capChain (k l m : ℕ) (h : k + l = m) (φ : Cochain X k) : Chains X m →ₗ[ℤ] Chains X l :=
  chainLift X m (capSimplex k l m h φ)

/-- The cap product on a simplex is `capSimplex`. -/
@[simp]
theorem capChain_simplexChain (k l m : ℕ) (h : k + l = m) (φ : Cochain X k)
    (σ : SingularSimplex X m) :
    capChain k l m h φ (simplexChain X m σ) = capSimplex k l m h φ σ :=
  chainLift_simplex X m _ σ

/-- The cup product of a `k`-cochain and an `l`-cochain, `k + l = m`:
`(φ ∪ ψ)(σ) = φ(σ|front) · ψ(σ|back)`, i.e. `ψ(σ ⌢ φ)` (Hatcher §3.2). -/
def cupChain (k l m : ℕ) (h : k + l = m) (φ : Cochain X k) (ψ : Cochain X l) : Cochain X m :=
  ψ.comp (capChain k l m h φ)

/-- The cup product on a simplex is the product of the values on the front and back faces. -/
@[simp]
theorem cupChain_simplexChain (k l m : ℕ) (h : k + l = m) (φ : Cochain X k) (ψ : Cochain X l)
    (σ : SingularSimplex X m) :
    cupChain k l m h φ ψ (simplexChain X m σ) =
      φ (simplexChain X k (σ.comp (frontFace k l m h))) *
        ψ (simplexChain X l (σ.comp (backFace k l m h))) := by
  rw [cupChain, LinearMap.comp_apply, capChain_simplexChain, capSimplex, map_zsmul, smul_eq_mul]

/-- In top degree the cap product is evaluation times the last vertex: for a `k`-simplex `σ`,
`σ ⌢ φ = φ(σ) · [σ(v_k)]`. -/
theorem capSimplex_top (k : ℕ) (φ : Cochain X k) (σ : SingularSimplex X k) :
    capSimplex k 0 k (by omega) φ σ =
      φ (simplexChain X k σ) • simplexChain X 0 (σ.comp (backFace k 0 k (by omega))) := by
  rw [capSimplex, frontFace_top, ContinuousMap.comp_id]

/-! ### The Leibniz formula for the cap product

For a singular `(k + l + 1)`-simplex `σ`, the faces `δ_i σ` with `i ≤ k` contribute
`φ(δ_i front_{k+1} σ) · back_l σ`, which sum to `δφ(front_{k+1} σ) · back_l σ` except for the
last face `i = k + 1` of the front; the faces with `i = k + 1 + j` contribute
`(-1)^k φ(front_k σ) · (-1)^{j+1} δ_{j+1} back_{l+1} σ`, which sum to
`(-1)^k φ(front_k σ) · ∂ back_{l+1} σ` except for the zeroth face of the back.  The two
missing terms are both `± φ(front_k σ) · back_l σ` and cancel against each other. -/

/-- The boundary of a simplex, with the boundary map as a linear map. -/
private theorem boundary_simplex_hom (n : ℕ) (σ : SingularSimplex X (n + 1)) :
    ((singularComplex X).d (n + 1) n).hom (simplexChain X (n + 1) σ) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • simplexChain X n (σ.comp (simplexFace n i)) :=
  boundary_simplex X n σ

/-- A sum over `Fin (k + l + 2)` splits into the first `k + 1` and the last `l + 1` indices. -/
theorem sum_fin_split {M : Type*} [AddCommMonoid M] (k l : ℕ) (f : Fin (k + l + 2) → M) :
    ∑ i, f i = ∑ a : Fin (k + 1), f ⟨a, by omega⟩ + ∑ j : Fin (l + 1), f ⟨k + 1 + j, by omega⟩ := by
  rw [← (finCongr (by omega : k + 1 + (l + 1) = k + l + 2)).sum_comp, Fin.sum_univ_add]
  rfl

/-- The boundary of the cap product of a simplex: `φ(front_k σ) · ∂ back_{l+1} σ`, with the
zeroth face of the back split off. -/
theorem boundary_capSimplex_eq (k l : ℕ) (φ : Cochain X k) (σ : SingularSimplex X (k + l + 1))
    (h : k + 1 + l = k + l + 1) :
    ((singularComplex X).d (l + 1) l).hom (capSimplex k (l + 1) (k + l + 1) rfl φ σ) =
      φ (simplexChain X k (σ.comp (frontFace k (l + 1) (k + l + 1) rfl))) •
        (simplexChain X l (σ.comp (backFace (k + 1) l (k + l + 1) h)) +
          ∑ j : Fin (l + 1), (-1 : ℤ) ^ (j.val + 1) •
            simplexChain X l ((σ.comp (backFace k (l + 1) (k + l + 1) rfl)).comp
              (simplexFace l j.succ))) := by
  rw [capSimplex, map_zsmul, boundary_simplex_hom, Fin.sum_univ_succ,
    comp_backFace_comp_simplexFace_zero σ h]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ]

/-- The cap product of the boundary of a simplex, sorted by front and back faces. -/
theorem capChain_boundary_simplex_eq (k l : ℕ) (φ : Cochain X k)
    (σ : SingularSimplex X (k + l + 1)) (h : k + 1 + l = k + l + 1) :
    capChain k l (k + l) rfl φ
        (((singularComplex X).d (k + l + 1) (k + l)).hom (simplexChain X (k + l + 1) σ)) =
      (∑ a : Fin (k + 1), (-1 : ℤ) ^ a.val *
          φ (simplexChain X k ((σ.comp (frontFace (k + 1) l (k + l + 1) h)).comp
            (simplexFace k a.castSucc)))) •
          simplexChain X l (σ.comp (backFace (k + 1) l (k + l + 1) h)) +
        ((-1 : ℤ) ^ k * φ (simplexChain X k (σ.comp (frontFace k (l + 1) (k + l + 1) rfl)))) •
          ∑ j : Fin (l + 1), (-1 : ℤ) ^ (j.val + 1) •
            simplexChain X l ((σ.comp (backFace k (l + 1) (k + l + 1) rfl)).comp
              (simplexFace l j.succ)) := by
  -- the `ℤ`-action on chains is `zsmul`; use the matching module structure
  let : Module ℤ (Chains X l) := AddCommGroup.toIntModule _
  rw [boundary_simplex_hom, sum_fin_split, map_add, map_sum, map_sum, Finset.sum_smul,
    Finset.smul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_zsmul, capChain_simplexChain, capSimplex, comp_simplexFace_comp_frontFace_of_le σ a h,
      comp_simplexFace_comp_backFace_of_le σ a h, smul_smul]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, capChain_simplexChain, capSimplex, comp_simplexFace_comp_frontFace_of_gt σ j,
      comp_simplexFace_comp_backFace_of_gt σ j, smul_smul, smul_smul]
    congr 1
    ring

/-- The cap product of a simplex with a coboundary: `δφ(front_{k+1} σ) · back_l σ`, with the
last face of the front split off. -/
theorem capSimplex_coboundary_eq (k l : ℕ) (φ : Cochain X k) (σ : SingularSimplex X (k + l + 1))
    (h : k + 1 + l = k + l + 1) :
    capSimplex (k + 1) l (k + l + 1) h (coboundary k φ) σ =
      (∑ a : Fin (k + 1), (-1 : ℤ) ^ a.val *
          φ (simplexChain X k ((σ.comp (frontFace (k + 1) l (k + l + 1) h)).comp
            (simplexFace k a.castSucc))) +
        (-1 : ℤ) ^ (k + 1) * φ (simplexChain X k (σ.comp (frontFace k (l + 1) (k + l + 1) rfl)))) •
          simplexChain X l (σ.comp (backFace (k + 1) l (k + l + 1) h)) := by
  rw [capSimplex, coboundary_apply, boundary_simplex_hom, map_sum, Fin.sum_univ_castSucc,
    comp_frontFace_comp_simplexFace_last σ h]
  simp only [map_zsmul, smul_eq_mul, Fin.val_castSucc, Fin.val_last]

/-- **Leibniz formula for the cap product** on a simplex:
`∂(σ ⌢ φ) = (-1)^k (∂σ ⌢ φ - σ ⌢ δφ)`. -/
theorem boundary_capSimplex (k l : ℕ) (φ : Cochain X k) (σ : SingularSimplex X (k + l + 1)) :
    ((singularComplex X).d (l + 1) l).hom (capSimplex k (l + 1) (k + l + 1) rfl φ σ) =
      (-1 : ℤ) ^ k • (capChain k l (k + l) rfl φ
          (((singularComplex X).d (k + l + 1) (k + l)).hom (simplexChain X (k + l + 1) σ)) -
        capSimplex (k + 1) l (k + l + 1) (by omega) (coboundary k φ) σ) := by
  have h : k + 1 + l = k + l + 1 := by omega
  rw [boundary_capSimplex_eq k l φ σ h, capChain_boundary_simplex_eq k l φ σ h,
    capSimplex_coboundary_eq k l φ σ h, pow_succ]
  have he : (-1 : ℤ) ^ k * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
  generalize (-1 : ℤ) ^ k = e at he ⊢
  generalize φ (simplexChain X k (σ.comp (frontFace k (l + 1) (k + l + 1) rfl))) = F
  -- the `ℤ`-action on chains is `zsmul`; use the matching module structure
  let : Module ℤ (Chains X l) := AddCommGroup.toIntModule _
  match_scalars <;> linear_combination (-F) * he

/-- Evaluation of an integer multiple of a linear map of chains (the `ℤ`-action being `zsmul`). -/
private theorem zsmul_linearMap_apply {m l : ℕ} (n : ℤ) (g : Chains X m →ₗ[ℤ] Chains X l)
    (x : Chains X m) : (n • g) x = n • g x :=
  map_zsmul (LinearMap.applyₗ (R := ℤ) x) n g

/-- **Leibniz formula for the cap product** (Hatcher §3.3): `∂(c ⌢ φ) = (-1)^k (∂c ⌢ φ - c ⌢ δφ)`. -/
theorem boundary_capChain (k l : ℕ) (φ : Cochain X k) (c : Chains X (k + l + 1)) :
    ((singularComplex X).d (l + 1) l).hom (capChain k (l + 1) (k + l + 1) rfl φ c) =
      (-1 : ℤ) ^ k • (capChain k l (k + l) rfl φ (((singularComplex X).d (k + l + 1) (k + l)).hom c)
        - capChain (k + 1) l (k + l + 1) (by omega) (coboundary k φ) c) := by
  have key : ((singularComplex X).d (l + 1) l).hom.comp (capChain k (l + 1) (k + l + 1) rfl φ) =
      (-1 : ℤ) ^ k • ((capChain k l (k + l) rfl φ).comp
          ((singularComplex X).d (k + l + 1) (k + l)).hom -
        capChain (k + 1) l (k + l + 1) (by omega) (coboundary k φ)) := by
    apply chainMap_ext X (k + l + 1)
    intro σ
    rw [LinearMap.comp_apply, capChain_simplexChain, boundary_capSimplex, zsmul_linearMap_apply,
      LinearMap.sub_apply, LinearMap.comp_apply, capChain_simplexChain]
  rw [← LinearMap.comp_apply, key, zsmul_linearMap_apply, LinearMap.sub_apply, LinearMap.comp_apply]

/-! ### The Leibniz formula for the cup product -/

/-- **Leibniz formula for the cup product** (Hatcher §3.2, Lemma 3.6):
`δ(φ ∪ ψ) = δφ ∪ ψ + (-1)^k φ ∪ δψ`. -/
theorem coboundary_cupChain (k l : ℕ) (φ : Cochain X k) (ψ : Cochain X l) :
    coboundary (k + l) (cupChain k l (k + l) rfl φ ψ) =
      cupChain (k + 1) l (k + l + 1) (by omega) (coboundary k φ) ψ
        + (-1 : ℤ) ^ k • cupChain k (l + 1) (k + l + 1) rfl φ (coboundary l ψ) := by
  ext c
  have he : (-1 : ℤ) ^ k * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
  simp only [LinearMap.add_apply, LinearMap.smul_apply, coboundary_apply, cupChain,
    LinearMap.comp_apply]
  rw [boundary_capChain, map_zsmul, map_sub, smul_eq_mul, smul_eq_mul]
  linear_combination (ψ (capChain (k + 1) l (k + l + 1) (by omega) (coboundary k φ) c) -
    ψ (capChain k l (k + l) rfl φ (((singularComplex X).d (k + l + 1) (k + l)).hom c))) * he

/-! ### Naturality -/

/-- Naturality of the cap product: `f_*(c ⌢ f^*φ) = f_* c ⌢ φ`. -/
theorem inducedChain_capChain (f : C(X, Y)) (k l m : ℕ) (h : k + l = m) (φ : Cochain Y k)
    (c : Chains X m) :
    inducedChain f l (capChain k l m h (pullback f k φ) c) =
      capChain k l m h φ (inducedChain f m c) := by
  have key : (inducedChain f l).comp (capChain k l m h (pullback f k φ)) =
      (capChain k l m h φ).comp (inducedChain f m) := by
    apply chainMap_ext X m
    intro σ
    rw [LinearMap.comp_apply, LinearMap.comp_apply, capChain_simplexChain, inducedChain_simplex,
      capChain_simplexChain, capSimplex, capSimplex, map_zsmul, pullback_apply,
      inducedChain_simplex, inducedChain_simplex, ContinuousMap.comp_assoc,
      ContinuousMap.comp_assoc]
  exact LinearMap.congr_fun key c

/-- Naturality of the cup product: `f^*(φ ∪ ψ) = f^*φ ∪ f^*ψ`. -/
theorem pullback_cupChain (f : C(X, Y)) (k l m : ℕ) (h : k + l = m) (φ : Cochain Y k)
    (ψ : Cochain Y l) :
    pullback f m (cupChain k l m h φ ψ) = cupChain k l m h (pullback f k φ) (pullback f l ψ) := by
  ext c
  simp only [pullback_apply, cupChain, LinearMap.comp_apply]
  rw [inducedChain_capChain]

end SingularCapProduct
