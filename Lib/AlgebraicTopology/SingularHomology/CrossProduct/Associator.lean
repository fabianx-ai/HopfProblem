/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Lib.AlgebraicTopology.SingularHomology.CrossProduct.Swap

open Set Function Filter Manifold Topology

open scoped BigOperators TensorProduct

/-!
# Associativity of the cross product

The cross product is associative: under the re-association `(X × Y) × Z ≃ X × (Y × Z)`,
`(a × b) × c = a × (b × c)` on homology (Hatcher, *Algebraic Topology*, §3.B).  This file proves
it for three `1`-classes, `H₁(X) ⊗ H₁(Y) ⊗ H₁(Z) → H₃(X × (Y × Z))`, with `(a × b) × c` formed by
the left-degree-two product `SingularHomology.crossProductHomologyTwoOne`.

* On formal chains: the re-association lemmas for the point, edge and triangle products
  (`SingularHomology.formalEdgeCrossProduct_point_left`, `_point_middle`,
  `.formalTriangleCrossProduct_point_right`), the associator defect
  `SingularHomology.formalAssociatorDefect` (the difference of the two bracketings after
  re-association), its Leibniz rule `.formalBoundary_associatorDefect`, and the homotopy
  `SingularHomology.formalAssociatorHomotopy` with `∂H = defect`
  (`.formalAssociatorHomotopy_boundary`), both natural in the three vertex sets.
* On singular chains: `SingularHomology.crossProductAssociatorDefect`,
  `.crossProductAssociatorHomotopy` (natural, computed on affine chains of a triple product of
  standard simplices by the formal data, `.crossProductAssociatorHomotopy_affineChainMap`), and the
  boundary identity `.crossProductAssociatorHomotopy_boundary`, `_boundary_of_cycle`.
* On homology: `SingularHomology.crossProductCycleClasses_associative`,
  `.crossProductHomology_associative`, and the cyclic consequence
  `SingularHomology.crossProductHomology_cyclic` along the cyclic re-association
  `.crossProductCyclicMap : Y × (Z × X) → X × (Y × Z)`.
-/


@[expose] public noncomputable section


/-! ### The associator defect and its homotopy on formal chains -/

/-- Under the triple re-association `(V × W) × Z → V × (W × Z)`, the left-nested edge/point cross product becomes the right-nested one. -/
theorem SingularHomology.formalEdgeCrossProduct_point_left {V W Z : Type*} (q : ℕ)
    (a : SingularMayerVietoris.FormalChains V 1) (b : SingularMayerVietoris.FormalChains W 2)
    (c : SingularMayerVietoris.FormalChains Z (q + 1)) :
    SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) (q + 2)
        (SingularHomology.formalEdgeCrossProduct q (SingularHomology.formalPointCrossProduct 1 a b) c) =
      SingularHomology.formalPointCrossProduct (q + 1) a (SingularHomology.formalEdgeCrossProduct q b c) := by
  have h :
    (SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) (q + 2)).comp
        (((SingularHomology.formalEdgeCrossProduct q).flip c).comp ((SingularHomology.formalPointCrossProduct 1).flip b)) =
      (SingularHomology.formalPointCrossProduct (q + 1)).flip (SingularHomology.formalEdgeCrossProduct q b c) := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, SingularHomology.formalPointCrossProduct_simplex_left]
    have hn := SingularHomology.formalMap_edgeCrossProduct (fun w : W => (v 0, w)) (id : Z → Z) q b c
    rw [SingularHomology.formalMap_id_apply] at hn
    rw [← hn, SingularHomology.formalMap_comp_apply]
    rfl
  exact LinearMap.congr_fun h a
/-- Under the triple re-association, the middle-nested cross product transfers to the right-nested form. -/
theorem SingularHomology.formalEdgeCrossProduct_point_middle {V W Z : Type*} (q : ℕ)
    (a : SingularMayerVietoris.FormalChains V 2) (b : SingularMayerVietoris.FormalChains W 1)
    (c : SingularMayerVietoris.FormalChains Z (q + 1)) :
    SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) (q + 2)
        (SingularHomology.formalEdgeCrossProduct q (SingularHomology.formalEdgeCrossProduct 0 a b) c) =
      SingularHomology.formalEdgeCrossProduct q a (SingularHomology.formalPointCrossProduct q b c) := by
  have h :
    (SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) (q + 2)).comp
        (((SingularHomology.formalEdgeCrossProduct q).flip c).comp (SingularHomology.formalEdgeCrossProduct 0 a)) =
      (SingularHomology.formalEdgeCrossProduct q a).comp ((SingularHomology.formalPointCrossProduct q).flip c) := by
    apply SingularMayerVietoris.formalChains_ext
    intro w
    simp only [LinearMap.comp_apply, LinearMap.flip_apply]
    rw [SingularHomology.formalEdgeCrossProduct_zero_simplex_right, SingularHomology.formalPointCrossProduct_simplex_left]
    have hl := SingularHomology.formalMap_edgeCrossProduct (fun v : V => (v, w 0)) (id : Z → Z) q a c
    have hr := SingularHomology.formalMap_edgeCrossProduct (id : V → V) (fun z : Z => (w 0, z)) q a c
    rw [SingularHomology.formalMap_id_apply] at hl hr
    rw [← hl, SingularHomology.formalMap_comp_apply, ← hr]
    rfl
  exact LinearMap.congr_fun h b
/-- Under the triple re-association, the triangle/point cross product transfers to the right-nested form. -/
theorem SingularHomology.formalTriangleCrossProduct_point_right {V W Z : Type*}
    (a : SingularMayerVietoris.FormalChains V 2) (b : SingularMayerVietoris.FormalChains W 2)
    (c : SingularMayerVietoris.FormalChains Z 1) :
    SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) 3
        (SingularHomology.formalTriangleCrossProduct 0 (SingularHomology.formalEdgeCrossProduct 1 a b) c) =
      SingularHomology.formalEdgeCrossProduct 1 a (SingularHomology.formalEdgeCrossProduct 0 b c) := by
  have h :
    (SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) 3).comp
        (SingularHomology.formalTriangleCrossProduct 0 (SingularHomology.formalEdgeCrossProduct 1 a b)) =
      (SingularHomology.formalEdgeCrossProduct 1 a).comp (SingularHomology.formalEdgeCrossProduct 0 b) := by
    apply SingularMayerVietoris.formalChains_ext
    intro z
    simp only [LinearMap.comp_apply, SingularHomology.formalTriangleCrossProduct_zero_simplex_right,
      SingularHomology.formalEdgeCrossProduct_zero_simplex_right, SingularHomology.formalMap_comp_apply]
    have hn := SingularHomology.formalMap_edgeCrossProduct (id : V → V) (fun w : W => (w, z 0)) 1 a b
    rw [SingularHomology.formalMap_id_apply] at hn
    exact hn
  exact LinearMap.congr_fun h c
/-- The associativity defect of the cross product: the failure of `(a × b) × c` and `a × (b × c)` to agree after the product re-association. -/
def SingularHomology.formalAssociatorDefect {V W Z : Type*} (q : ℕ) :
    SingularMayerVietoris.FormalChains V 2 →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W 2 →ₗ[ℤ]
        SingularMayerVietoris.FormalChains Z (q + 1) →ₗ[ℤ]
          SingularMayerVietoris.FormalChains (V × (W × Z)) (q + 3) :=
  (SingularHomology.formalEdgeCrossProduct 1).compr₂
      ((SingularHomology.formalTriangleCrossProduct q).compr₂
        (SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2)))
          (q + 3))) -
    ((LinearMap.llcomp ℤ (SingularMayerVietoris.FormalChains Z (q + 1))
              (SingularMayerVietoris.FormalChains (W × Z) (q + 2))
              (SingularMayerVietoris.FormalChains (V × (W × Z)) (q + 3))).compl₂
          (SingularHomology.formalEdgeCrossProduct q)).comp
      (SingularHomology.formalEdgeCrossProduct (q + 1))
/-- Explicit form of the associator defect as the difference of the two bracketings pushed through the re-association. -/
@[simp]
theorem SingularHomology.formalAssociatorDefect_apply {V W Z : Type*} (q : ℕ)
    (a : SingularMayerVietoris.FormalChains V 2) (b : SingularMayerVietoris.FormalChains W 2)
    (c : SingularMayerVietoris.FormalChains Z (q + 1)) :
    SingularHomology.formalAssociatorDefect q a b c =
      SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) (q + 3)
          (SingularHomology.formalTriangleCrossProduct q (SingularHomology.formalEdgeCrossProduct 1 a b) c) -
        SingularHomology.formalEdgeCrossProduct (q + 1) a (SingularHomology.formalEdgeCrossProduct q b c) :=
  rfl
/-- In the lowest degrees the associator defect vanishes. -/
@[simp]
theorem SingularHomology.formalAssociatorDefect_zero {V W Z : Type*}
    (a : SingularMayerVietoris.FormalChains V 2) (b : SingularMayerVietoris.FormalChains W 2)
    (c : SingularMayerVietoris.FormalChains Z 1) : SingularHomology.formalAssociatorDefect 0 a b c = 0 := by
  rw [SingularHomology.formalAssociatorDefect_apply, SingularHomology.formalTriangleCrossProduct_point_right, sub_self]
/-- The Leibniz rule for the associator defect. -/
theorem SingularHomology.formalBoundary_associatorDefect {V W Z : Type*} (q : ℕ)
    (a : SingularMayerVietoris.FormalChains V 2) (b : SingularMayerVietoris.FormalChains W 2)
    (c : SingularMayerVietoris.FormalChains Z (q + 2)) :
    SingularMayerVietoris.formalBoundary (q + 3) (SingularHomology.formalAssociatorDefect (q + 1) a b c) =
      SingularHomology.formalAssociatorDefect q a b (SingularMayerVietoris.formalBoundary (q + 1) c) := by
  simp only [SingularHomology.formalAssociatorDefect_apply, map_sub, ← SingularMayerVietoris.formalMap_boundary,
    SingularHomology.formalBoundary_triangleCrossProduct, SingularHomology.formalBoundary_edgeCrossProduct, map_add,
    LinearMap.sub_apply, SingularHomology.formalEdgeCrossProduct_point_middle]
  rw [SingularHomology.formalEdgeCrossProduct_point_left (q + 1) (SingularMayerVietoris.formalBoundary 1 a) b c]
  abel
/-- The product re-association is natural: pushforward along a product of maps commutes with it. -/
theorem SingularHomology.formalMap_prodAssoc_naturality {V W Z V' W' Z' : Type*}
    (f : V → V') (g : W → W') (h : Z → Z') (n : ℕ)
    (c : SingularMayerVietoris.FormalChains ((V × W) × Z) n) :
    SingularMayerVietoris.formalMap (Prod.map f (Prod.map g h)) n
        (SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) n c) =
      SingularMayerVietoris.formalMap (fun p : (V' × W') × Z' => (p.1.1, (p.1.2, p.2))) n
        (SingularMayerVietoris.formalMap (Prod.map (Prod.map f g) h) n c) := by
  have heq :
    (SingularMayerVietoris.formalMap (Prod.map f (Prod.map g h)) n).comp
        (SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) n) =
      (SingularMayerVietoris.formalMap (fun p : (V' × W') × Z' => (p.1.1, (p.1.2, p.2))) n).comp
        (SingularMayerVietoris.formalMap (Prod.map (Prod.map f g) h) n) := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, SingularMayerVietoris.formalMap_simplex]
    rfl
  exact LinearMap.congr_fun heq c
/-- The associator defect is natural under maps of the three factors. -/
theorem SingularHomology.formalMap_associatorDefect {V W Z V' W' Z' : Type*} (f : V → V')
    (g : W → W') (h : Z → Z') (q : ℕ) (a : SingularMayerVietoris.FormalChains V 2)
    (b : SingularMayerVietoris.FormalChains W 2)
    (c : SingularMayerVietoris.FormalChains Z (q + 1)) :
    SingularMayerVietoris.formalMap (Prod.map f (Prod.map g h)) (q + 3)
        (SingularHomology.formalAssociatorDefect q a b c) =
      SingularHomology.formalAssociatorDefect q (SingularMayerVietoris.formalMap f 2 a)
        (SingularMayerVietoris.formalMap g 2 b) (SingularMayerVietoris.formalMap h (q + 1) c) := by
  rw [SingularHomology.formalAssociatorDefect_apply, map_sub, SingularHomology.formalMap_prodAssoc_naturality,
    SingularHomology.formalMap_triangleCrossProduct, SingularHomology.formalMap_edgeCrossProduct, SingularHomology.formalMap_edgeCrossProduct,
    SingularHomology.formalMap_edgeCrossProduct]
  rfl
/-- Private plumbing: postcompose the output of a trilinear map on formal chain groups. -/
private def SingularHomology.triplePostcomp {V W Z U U' : Type*}
    {n m l r s : ℕ}
    (F :
      SingularMayerVietoris.FormalChains V n →ₗ[ℤ]
        SingularMayerVietoris.FormalChains W m →ₗ[ℤ]
          SingularMayerVietoris.FormalChains Z l →ₗ[ℤ] SingularMayerVietoris.FormalChains U r)
    (f : SingularMayerVietoris.FormalChains U r →ₗ[ℤ] SingularMayerVietoris.FormalChains U' s) :
    SingularMayerVietoris.FormalChains V n →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W m →ₗ[ℤ]
        SingularMayerVietoris.FormalChains Z l →ₗ[ℤ] SingularMayerVietoris.FormalChains U' s :=
  F.compr₂
    (LinearMap.llcomp ℤ (SingularMayerVietoris.FormalChains Z l)
      (SingularMayerVietoris.FormalChains U r) (SingularMayerVietoris.FormalChains U' s) f)

/-- Private plumbing: precompose the last argument of a trilinear map on formal chain groups. -/
private def SingularHomology.triplePrecompLast {V W Z Z' U : Type*}
    {n m l l' r : ℕ}
    (F :
      SingularMayerVietoris.FormalChains V n →ₗ[ℤ]
        SingularMayerVietoris.FormalChains W m →ₗ[ℤ]
          SingularMayerVietoris.FormalChains Z l →ₗ[ℤ] SingularMayerVietoris.FormalChains U r)
    (f : SingularMayerVietoris.FormalChains Z' l' →ₗ[ℤ] SingularMayerVietoris.FormalChains Z l) :
    SingularMayerVietoris.FormalChains V n →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W m →ₗ[ℤ]
        SingularMayerVietoris.FormalChains Z' l' →ₗ[ℤ] SingularMayerVietoris.FormalChains U r :=
  F.compr₂
    ((LinearMap.llcomp ℤ (SingularMayerVietoris.FormalChains Z' l')
          (SingularMayerVietoris.FormalChains Z l) (SingularMayerVietoris.FormalChains U r)).flip
      f)
/-- The chain homotopy witnessing that the associator defect is a boundary, degree by degree; zero in the lowest degree. -/
def SingularHomology.formalAssociatorHomotopy {V W Z : Type*} :
    (q : ℕ) →
      SingularMayerVietoris.FormalChains V 2 →ₗ[ℤ]
        SingularMayerVietoris.FormalChains W 2 →ₗ[ℤ]
          SingularMayerVietoris.FormalChains Z (q + 1) →ₗ[ℤ]
            SingularMayerVietoris.FormalChains (V × (W × Z)) (q + 4)
  | 0 => 0
  | q + 1 =>
    SingularHomology.formalTrilinearLift fun v w z =>
      SingularMayerVietoris.formalCone (v 0, (w 0, z 0)) (q + 4)
        (SingularHomology.formalAssociatorDefect (q + 1) (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z) -
          SingularHomology.formalAssociatorHomotopy q (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w)
            (SingularMayerVietoris.formalBoundary (q + 1)
              (SingularMayerVietoris.formalSimplex z)))
/-- The associator homotopy vanishes in the lowest degree. -/
@[simp]
theorem SingularHomology.formalAssociatorHomotopy_zero {V W Z : Type*}
    (a : SingularMayerVietoris.FormalChains V 2) (b : SingularMayerVietoris.FormalChains W 2)
    (c : SingularMayerVietoris.FormalChains Z 1) : SingularHomology.formalAssociatorHomotopy 0 a b c = 0 :=
  rfl
/-- On simplices the successor step of the associator homotopy is the cone of the lower-degree data. -/
@[simp]
theorem SingularHomology.formalAssociatorHomotopy_simplex_succ {V W Z : Type*} (q : ℕ)
    (v : Fin 2 → V) (w : Fin 2 → W) (z : Fin (q + 2) → Z) :
    SingularHomology.formalAssociatorHomotopy (q + 1) (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z) =
      SingularMayerVietoris.formalCone (v 0, (w 0, z 0)) (q + 4)
        (SingularHomology.formalAssociatorDefect (q + 1) (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z) -
          SingularHomology.formalAssociatorHomotopy q (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w)
            (SingularMayerVietoris.formalBoundary (q + 1)
              (SingularMayerVietoris.formalSimplex z))) :=
  SingularHomology.formalTrilinearLift_simplex _ _ _ _
/-- Degree-zero boundary identity of the associator homotopy. -/
theorem SingularHomology.formalAssociatorHomotopy_boundary_zero {V W Z : Type*}
    (a : SingularMayerVietoris.FormalChains V 2) (b : SingularMayerVietoris.FormalChains W 2)
    (c : SingularMayerVietoris.FormalChains Z 1) :
    SingularMayerVietoris.formalBoundary 3 (SingularHomology.formalAssociatorHomotopy 0 a b c) =
      SingularHomology.formalAssociatorDefect 0 a b c := by
  rw [SingularHomology.formalAssociatorHomotopy_zero, map_zero, SingularHomology.formalAssociatorDefect_zero]
/-- The defining identity: `∂H + (swapped bracketing defect) = 0` — the homotopy carries one bracketing of the cross product to the other. -/
theorem SingularHomology.formalAssociatorHomotopy_boundary {V W Z : Type*} :
    ∀ (q : ℕ) (a : SingularMayerVietoris.FormalChains V 2)
      (b : SingularMayerVietoris.FormalChains W 2)
      (c : SingularMayerVietoris.FormalChains Z (q + 2)),
      SingularMayerVietoris.formalBoundary (q + 4) (SingularHomology.formalAssociatorHomotopy (q + 1) a b c) +
          SingularHomology.formalAssociatorHomotopy q a b (SingularMayerVietoris.formalBoundary (q + 1) c) =
        SingularHomology.formalAssociatorDefect (q + 1) a b c := by
  intro q
  induction q with
  | zero =>
    intro a b c
    have heq :
      SingularHomology.triplePostcomp (SingularHomology.formalAssociatorHomotopy (V := V) (W := W) (Z := Z) 1)
            (SingularMayerVietoris.formalBoundary 4) +
          SingularHomology.triplePrecompLast (SingularHomology.formalAssociatorHomotopy 0)
            (SingularMayerVietoris.formalBoundary 1) =
        SingularHomology.formalAssociatorDefect 1 := by
      apply SingularHomology.formalChains_trilinear_ext
      intro v w z
      change
        SingularMayerVietoris.formalBoundary 4
              (SingularHomology.formalAssociatorHomotopy 1 (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z)) +
            SingularHomology.formalAssociatorHomotopy 0 (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w)
              (SingularMayerVietoris.formalBoundary 1 (SingularMayerVietoris.formalSimplex z)) =
          SingularHomology.formalAssociatorDefect 1 (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z)
      have hz :
        SingularMayerVietoris.formalBoundary 3
            (SingularHomology.formalAssociatorDefect 1 (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z) -
              SingularHomology.formalAssociatorHomotopy 0 (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalSimplex w)
                (SingularMayerVietoris.formalBoundary 1
                  (SingularMayerVietoris.formalSimplex z))) =
          0 := by
        rw [map_sub, SingularHomology.formalBoundary_associatorDefect, SingularHomology.formalAssociatorDefect_zero,
          SingularHomology.formalAssociatorHomotopy_zero, map_zero, sub_self]
      rw [SingularHomology.formalAssociatorHomotopy_simplex_succ, SingularMayerVietoris.formalBoundary_cone, hz,
        map_zero, sub_zero, sub_add_cancel]
    exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c
  | succ q ih =>
    intro a b c
    have heq :
      SingularHomology.triplePostcomp (SingularHomology.formalAssociatorHomotopy (V := V) (W := W) (Z := Z) (q + 2))
            (SingularMayerVietoris.formalBoundary (q + 5)) +
          SingularHomology.triplePrecompLast (SingularHomology.formalAssociatorHomotopy (q + 1))
            (SingularMayerVietoris.formalBoundary (q + 2)) =
        SingularHomology.formalAssociatorDefect (q + 2) := by
      apply SingularHomology.formalChains_trilinear_ext
      intro v w z
      change
        SingularMayerVietoris.formalBoundary (q + 5)
              (SingularHomology.formalAssociatorHomotopy (q + 2) (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z)) +
            SingularHomology.formalAssociatorHomotopy (q + 1) (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w)
              (SingularMayerVietoris.formalBoundary (q + 2)
                (SingularMayerVietoris.formalSimplex z)) =
          SingularHomology.formalAssociatorDefect (q + 2) (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z)
      have hp :
        SingularMayerVietoris.formalBoundary (q + 4)
            (SingularHomology.formalAssociatorHomotopy (q + 1) (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w)
              (SingularMayerVietoris.formalBoundary (q + 2)
                (SingularMayerVietoris.formalSimplex z))) =
          SingularHomology.formalAssociatorDefect (q + 1) (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w)
            (SingularMayerVietoris.formalBoundary (q + 2)
              (SingularMayerVietoris.formalSimplex z)) := by
        simpa only [SingularMayerVietoris.formalBoundary_boundary, map_zero, add_zero] using
          ih (SingularMayerVietoris.formalSimplex v) (SingularMayerVietoris.formalSimplex w)
            (SingularMayerVietoris.formalBoundary (q + 2) (SingularMayerVietoris.formalSimplex z))
      have hz :
        SingularMayerVietoris.formalBoundary (q + 4)
            (SingularHomology.formalAssociatorDefect (q + 2) (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z) -
              SingularHomology.formalAssociatorHomotopy (q + 1) (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalSimplex w)
                (SingularMayerVietoris.formalBoundary (q + 2)
                  (SingularMayerVietoris.formalSimplex z))) =
          0 := by rw [map_sub, SingularHomology.formalBoundary_associatorDefect, hp, sub_self]
      rw [SingularHomology.formalAssociatorHomotopy_simplex_succ, SingularMayerVietoris.formalBoundary_cone, hz,
        map_zero, sub_zero, sub_add_cancel]
    exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c
/-- The associator homotopy is natural under maps of the three factors. -/
theorem SingularHomology.formalMap_associatorHomotopy {V W Z V' W' Z' : Type*}
    (f : V → V') (g : W → W') (h : Z → Z') :
    ∀ (q : ℕ) (a : SingularMayerVietoris.FormalChains V 2)
      (b : SingularMayerVietoris.FormalChains W 2)
      (c : SingularMayerVietoris.FormalChains Z (q + 1)),
      SingularMayerVietoris.formalMap (Prod.map f (Prod.map g h)) (q + 4)
          (SingularHomology.formalAssociatorHomotopy q a b c) =
        SingularHomology.formalAssociatorHomotopy q (SingularMayerVietoris.formalMap f 2 a)
          (SingularMayerVietoris.formalMap g 2 b) (SingularMayerVietoris.formalMap h (q + 1) c) :=
  by
  intro q
  induction q with
  | zero =>
    intro a b c
    simp only [SingularHomology.formalAssociatorHomotopy_zero, map_zero]
  | succ q ih =>
    intro a b c
    have heq :
      SingularHomology.triplePostcomp (SingularHomology.formalAssociatorHomotopy (V := V) (W := W) (Z := Z) (q + 1))
          (SingularMayerVietoris.formalMap (Prod.map f (Prod.map g h)) (q + 5)) =
        ((SingularHomology.triplePrecompLast (SingularHomology.formalAssociatorHomotopy (q + 1))
                  (SingularMayerVietoris.formalMap h (q + 2))).compl₂
              (SingularMayerVietoris.formalMap g 2)).comp
          (SingularMayerVietoris.formalMap f 2) := by
      apply SingularHomology.formalChains_trilinear_ext
      intro v w z
      change
        SingularMayerVietoris.formalMap (Prod.map f (Prod.map g h)) (q + 5)
            (SingularHomology.formalAssociatorHomotopy (q + 1) (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z)) =
          SingularHomology.formalAssociatorHomotopy (q + 1)
            (SingularMayerVietoris.formalMap f 2 (SingularMayerVietoris.formalSimplex v))
            (SingularMayerVietoris.formalMap g 2 (SingularMayerVietoris.formalSimplex w))
            (SingularMayerVietoris.formalMap h (q + 2) (SingularMayerVietoris.formalSimplex z))
      simp only [SingularMayerVietoris.formalMap_simplex, SingularHomology.formalAssociatorHomotopy_simplex_succ]
      rw [SingularMayerVietoris.formalMap_cone]
      congr 1
      rw [map_sub, SingularHomology.formalMap_associatorDefect, ih, SingularMayerVietoris.formalMap_boundary,
        SingularMayerVietoris.formalMap_simplex, SingularMayerVietoris.formalMap_simplex,
        SingularMayerVietoris.formalMap_simplex]
    exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c

/-! ### The associator on singular chains -/

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The associativity defect of the homology cross product on the space level: the difference of the two bracketings after re-associating `X × (Y × Z)`. -/
def SingularHomology.crossProductAssociatorDefect (X Y Z : Type) [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (n : ℕ) :
    SingularChains.Chains X 1 →ₗ[ℤ]
      SingularChains.Chains Y 1 →ₗ[ℤ]
        SingularChains.Chains Z n →ₗ[ℤ] SingularChains.Chains (X × (Y × Z)) (n + 2) :=
  SingularHomology.integerTrilinearPostcompose
      (SingularHomology.integerTrilinearLeftAssociated (SingularHomology.crossProductEdge X Y 1) (SingularHomology.crossProductTriangle (X × Y) Z n))
      (SingularChains.inducedChain (Homeomorph.prodAssoc X Y Z : C(_, _)) (n + 2)) -
    SingularHomology.integerTrilinearRightAssociated (SingularHomology.crossProductEdge X (Y × Z) (n + 1)) (SingularHomology.crossProductEdge Y Z n)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- Explicit form: the defect is the pushforward of the two bracketings along the product-association homeomorphism. -/
@[simp]
theorem SingularHomology.crossProductAssociatorDefect_apply (X Y Z : Type)
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (n : ℕ)
    (a : SingularChains.Chains X 1) (b : SingularChains.Chains Y 1) (c : SingularChains.Chains Z n) :
    SingularHomology.crossProductAssociatorDefect X Y Z n a b c =
      SingularChains.inducedChain (Homeomorph.prodAssoc X Y Z : C(_, _)) (n + 2)
          (SingularHomology.crossProductTriangle (X × Y) Z n (SingularHomology.crossProductEdge X Y 1 a b) c) -
        SingularHomology.crossProductEdge X (Y × Z) (n + 1) a (SingularHomology.crossProductEdge Y Z n b c) :=
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The chain homotopy on the space level carrying one bracketing of the triple cross product to the other, degree by degree. -/
def SingularHomology.crossProductAssociatorHomotopy (X Y Z : Type) [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (n : ℕ) :
    SingularChains.Chains X 1 →ₗ[ℤ]
      SingularChains.Chains Y 1 →ₗ[ℤ]
        SingularChains.Chains Z n →ₗ[ℤ] SingularChains.Chains (X × (Y × Z)) (n + 3) :=
  SingularHomology.chainTrilinearLift X Y Z 1 1 n fun σ τ υ =>
    SingularChains.inducedChain (σ.prodMap (τ.prodMap υ)) (n + 3)
      (SingularHomology.tripleAffineChainMap 1 1 n (n + 3)
        (SingularHomology.formalAssociatorHomotopy n
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n))))

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- On simplices the associator homotopy is induced by the explicit prism data. -/
@[simp]
theorem SingularHomology.crossProductAssociatorHomotopy_simplex (X Y Z : Type)
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (n : ℕ)
    (σ : SingularChains.SingularSimplex X 1) (τ : SingularChains.SingularSimplex Y 1)
    (υ : SingularChains.SingularSimplex Z n) :
    SingularHomology.crossProductAssociatorHomotopy X Y Z n (SingularChains.simplexChain X 1 σ)
        (SingularChains.simplexChain Y 1 τ) (SingularChains.simplexChain Z n υ) =
      SingularChains.inducedChain (σ.prodMap (τ.prodMap υ)) (n + 3)
        (SingularHomology.tripleAffineChainMap 1 1 n (n + 3)
          (SingularHomology.formalAssociatorHomotopy n
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) :=
  SingularHomology.chainTrilinearLift_simplex X Y Z 1 1 n _ σ τ υ

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The associator homotopy is natural under maps of the three factors. -/
theorem SingularHomology.crossProductAssociatorHomotopy_natural {X : Type} {Y : Type}
    {Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {X' Y' Z' : Type}
    [TopologicalSpace X'] [TopologicalSpace Y'] [TopologicalSpace Z'] (f : C(X, X'))
    (g : C(Y, Y')) (h : C(Z, Z')) (n : ℕ) (a : SingularChains.Chains X 1)
    (b : SingularChains.Chains Y 1) (c : SingularChains.Chains Z n) :
    SingularChains.inducedChain (f.prodMap (g.prodMap h)) (n + 3)
        (SingularHomology.crossProductAssociatorHomotopy X Y Z n a b c) =
      SingularHomology.crossProductAssociatorHomotopy X' Y' Z' n (SingularChains.inducedChain f 1 a)
        (SingularChains.inducedChain g 1 b) (SingularChains.inducedChain h n c) := by
  have heq :
    SingularHomology.integerTrilinearPostcompose (SingularHomology.crossProductAssociatorHomotopy X Y Z n)
        (SingularChains.inducedChain (f.prodMap (g.prodMap h)) (n + 3)) =
      SingularHomology.integerTrilinearPrecompose (SingularHomology.crossProductAssociatorHomotopy X' Y' Z' n)
        (SingularChains.inducedChain f 1) (SingularChains.inducedChain g 1)
        (SingularChains.inducedChain h n) := by
    apply SingularHomology.chainTrilinearMap_ext X Y Z 1 1 n
    intro σ τ υ
    simp only [SingularHomology.integerTrilinearPostcompose_apply, SingularHomology.integerTrilinearPrecompose_apply,
      SingularChains.inducedChain_simplex, SingularHomology.crossProductAssociatorHomotopy_simplex]
    have hc :
      (f.comp σ).prodMap ((g.comp τ).prodMap (h.comp υ)) =
        (f.prodMap (g.prodMap h)).comp (σ.prodMap (τ.prodMap υ)) :=
      rfl
    rw [hc, SingularChains.inducedChain_comp]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- Chains induced along the product association commute with product pushforwards. -/
theorem SingularHomology.inducedChain_prodAssoc_natural {X : Type} {Y : Type} {Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {X' Y' Z' : Type}
    [TopologicalSpace X'] [TopologicalSpace Y'] [TopologicalSpace Z'] (f : C(X, X'))
    (g : C(Y, Y')) (h : C(Z, Z')) (n : ℕ) (c : SingularChains.Chains ((X × Y) × Z) n) :
    SingularChains.inducedChain (f.prodMap (g.prodMap h)) n
        (SingularChains.inducedChain (Homeomorph.prodAssoc X Y Z : C(_, _)) n c) =
      SingularChains.inducedChain (Homeomorph.prodAssoc X' Y' Z' : C(_, _)) n
        (SingularChains.inducedChain ((f.prodMap g).prodMap h) n c) := by
  have hc :
    (f.prodMap (g.prodMap h)).comp (Homeomorph.prodAssoc X Y Z : C(_, _)) =
      (Homeomorph.prodAssoc X' Y' Z' : C(_, _)).comp ((f.prodMap g).prodMap h) :=
    rfl
  have heq := congrArg (fun k => SingularChains.inducedChain k n c) hc
  simpa only [SingularChains.inducedChain_comp, LinearMap.comp_apply] using heq

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The associator defect is natural under maps of the three factors. -/
theorem SingularHomology.crossProductAssociatorDefect_natural {X : Type} {Y : Type}
    {Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {X' Y' Z' : Type}
    [TopologicalSpace X'] [TopologicalSpace Y'] [TopologicalSpace Z'] (f : C(X, X'))
    (g : C(Y, Y')) (h : C(Z, Z')) (n : ℕ) (a : SingularChains.Chains X 1)
    (b : SingularChains.Chains Y 1) (c : SingularChains.Chains Z n) :
    SingularChains.inducedChain (f.prodMap (g.prodMap h)) (n + 2)
        (SingularHomology.crossProductAssociatorDefect X Y Z n a b c) =
      SingularHomology.crossProductAssociatorDefect X' Y' Z' n (SingularChains.inducedChain f 1 a)
        (SingularChains.inducedChain g 1 b) (SingularChains.inducedChain h n c) := by
  simp only [SingularHomology.crossProductAssociatorDefect_apply, map_sub, SingularHomology.inducedChain_prodAssoc_natural,
    SingularHomology.crossProductTriangle_natural, SingularHomology.crossProductEdge_natural]


/-! ### Computation on affine chains and the boundary identity -/

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The triangle cross product on the left-associated product transfers across the product association on standard simplices. -/
theorem SingularHomology.crossProductTriangle_productAffineChainMap_left (p q r n : ℕ)
    (a : SingularMayerVietoris.FormalChains (SingularChains.Simplex p × SingularChains.Simplex q) 3)
    (b : SingularMayerVietoris.FormalChains (SingularChains.Simplex r) (n + 1)) :
    SingularChains.inducedChain
        (Homeomorph.prodAssoc (SingularChains.Simplex p) (SingularChains.Simplex q)
            (SingularChains.Simplex r) :
          C(_, _))
        (n + 2)
        (SingularHomology.crossProductTriangle (SingularChains.Simplex p × SingularChains.Simplex q)
          (SingularChains.Simplex r) n (SingularHomology.productAffineChainMap p q 2 a)
          (SingularMayerVietoris.affineChainMap r n b)) =
      SingularHomology.tripleAffineChainMap p q r (n + 2)
        (SingularMayerVietoris.formalMap
          (fun x :
              (SingularChains.Simplex p × SingularChains.Simplex q) × SingularChains.Simplex r =>
            (x.1.1, (x.1.2, x.2)))
          (n + 3) (SingularHomology.formalTriangleCrossProduct n a b)) := by
  have h :
    SingularHomology.integerBilinearPostcompose
        (SingularHomology.integerBilinearPrecompose
          (SingularHomology.crossProductTriangle (SingularChains.Simplex p × SingularChains.Simplex q)
            (SingularChains.Simplex r) n)
          (SingularHomology.productAffineChainMap p q 2) (SingularMayerVietoris.affineChainMap r n))
        (SingularChains.inducedChain
          (Homeomorph.prodAssoc (SingularChains.Simplex p) (SingularChains.Simplex q)
              (SingularChains.Simplex r) :
            C(_, _))
          (n + 2)) =
      SingularHomology.integerBilinearPostcompose (SingularHomology.formalTriangleCrossProduct n)
        ((SingularHomology.tripleAffineChainMap p q r (n + 2)).comp
          (SingularMayerVietoris.formalMap
            (fun x :
                (SingularChains.Simplex p × SingularChains.Simplex q) × SingularChains.Simplex r =>
              (x.1.1, (x.1.2, x.2)))
            (n + 3))) := by
    apply SingularHomology.integerFormalBilinearMap_ext
    intro v w
    simp only [SingularHomology.integerBilinearPostcompose_apply, SingularHomology.integerBilinearPrecompose_apply,
      SingularHomology.productAffineChainMap_simplex, SingularMayerVietoris.affineChainMap_simplex,
      SingularHomology.crossProductTriangle_simplex, LinearMap.comp_apply]
    rw [← LinearMap.comp_apply, ← SingularChains.inducedChain_comp]
    change
      SingularChains.inducedChain (SingularHomology.affineProductLeft v w) (n + 2)
          (SingularHomology.productAffineChainMap 2 n (n + 2)
            (SingularHomology.formalTriangleCrossProduct n
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) =
        _
    rw [SingularHomology.inducedChain_affineProductLeft]
    apply congrArg (SingularHomology.tripleAffineChainMap p q r (n + 2))
    change
      SingularMayerVietoris.formalMap
          ((fun x :
                (SingularChains.Simplex p × SingularChains.Simplex q) × SingularChains.Simplex r =>
              (x.1.1, (x.1.2, x.2))) ∘
            Prod.map (SingularHomology.productAffineSimplex v) (SingularMayerVietoris.affineSimplex w))
          (n + 3)
          (SingularHomology.formalTriangleCrossProduct n
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n))) =
        _
    rw [← SingularHomology.formalMap_comp_apply, SingularHomology.formalMap_triangleCrossProduct,
      SingularMayerVietoris.formalMap_simplex, SingularMayerVietoris.formalMap_simplex,
      SingularHomology.productAffineSimplex_stdVertices_image, SingularHomology.affineSimplex_stdVertices_image]
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The edge cross product on the right-associated product transfers across the product association on standard simplices. -/
theorem SingularHomology.crossProductEdge_productAffineChainMap_right (p q r n : ℕ)
    (a : SingularMayerVietoris.FormalChains (SingularChains.Simplex p) 2)
    (b :
      SingularMayerVietoris.FormalChains (SingularChains.Simplex q × SingularChains.Simplex r)
        (n + 1)) :
    SingularHomology.crossProductEdge (SingularChains.Simplex p) (SingularChains.Simplex q × SingularChains.Simplex r)
        n (SingularMayerVietoris.affineChainMap p 1 a) (SingularHomology.productAffineChainMap q r n b) =
      SingularHomology.tripleAffineChainMap p q r (n + 1) (SingularHomology.formalEdgeCrossProduct n a b) := by
  have h :
    SingularHomology.integerBilinearPrecompose
        (SingularHomology.crossProductEdge (SingularChains.Simplex p)
          (SingularChains.Simplex q × SingularChains.Simplex r) n)
        (SingularMayerVietoris.affineChainMap p 1) (SingularHomology.productAffineChainMap q r n) =
      SingularHomology.integerBilinearPostcompose (SingularHomology.formalEdgeCrossProduct n)
        (SingularHomology.tripleAffineChainMap p q r (n + 1)) := by
    apply SingularHomology.integerFormalBilinearMap_ext
    intro v w
    simp only [SingularHomology.integerBilinearPrecompose_apply, SingularHomology.integerBilinearPostcompose_apply,
      SingularMayerVietoris.affineChainMap_simplex, SingularHomology.productAffineChainMap_simplex,
      SingularHomology.crossProductEdge_simplex]
    change
      SingularChains.inducedChain (SingularHomology.affineProductRight v w) (n + 1)
          (SingularHomology.productAffineChainMap 1 n (n + 1)
            (SingularHomology.formalEdgeCrossProduct n
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) =
        _
    rw [SingularHomology.inducedChain_affineProductRight]
    change
      SingularHomology.tripleAffineChainMap p q r (n + 1)
          (SingularMayerVietoris.formalMap
            (Prod.map (SingularMayerVietoris.affineSimplex v) (SingularHomology.productAffineSimplex w)) (n + 2)
            (SingularHomology.formalEdgeCrossProduct n
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) =
        _
    rw [SingularHomology.formalMap_edgeCrossProduct, SingularMayerVietoris.formalMap_simplex,
      SingularMayerVietoris.formalMap_simplex, SingularHomology.affineSimplex_stdVertices_image,
      SingularHomology.productAffineSimplex_stdVertices_image]
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The associator homotopy commutes with the affine chain maps on standard simplices. -/
theorem SingularHomology.crossProductAssociatorHomotopy_affineChainMap (p q r n : ℕ)
    (a : SingularMayerVietoris.FormalChains (SingularChains.Simplex p) 2)
    (b : SingularMayerVietoris.FormalChains (SingularChains.Simplex q) 2)
    (c : SingularMayerVietoris.FormalChains (SingularChains.Simplex r) (n + 1)) :
    SingularHomology.crossProductAssociatorHomotopy (SingularChains.Simplex p) (SingularChains.Simplex q)
        (SingularChains.Simplex r) n (SingularMayerVietoris.affineChainMap p 1 a)
        (SingularMayerVietoris.affineChainMap q 1 b)
        (SingularMayerVietoris.affineChainMap r n c) =
      SingularHomology.tripleAffineChainMap p q r (n + 3) (SingularHomology.formalAssociatorHomotopy n a b c) := by
  have heq :
    SingularHomology.integerTrilinearPrecompose
        (SingularHomology.crossProductAssociatorHomotopy (SingularChains.Simplex p) (SingularChains.Simplex q)
          (SingularChains.Simplex r) n)
        (SingularMayerVietoris.affineChainMap p 1) (SingularMayerVietoris.affineChainMap q 1)
        (SingularMayerVietoris.affineChainMap r n) =
      SingularHomology.integerTrilinearPostcompose (SingularHomology.formalAssociatorHomotopy n)
        (SingularHomology.tripleAffineChainMap p q r (n + 3)) := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    apply SingularMayerVietoris.formalChains_ext
    intro w
    apply SingularMayerVietoris.formalChains_ext
    intro z
    simp only [SingularHomology.integerTrilinearPrecompose_apply, SingularHomology.integerTrilinearPostcompose_apply,
      SingularMayerVietoris.affineChainMap_simplex, SingularHomology.crossProductAssociatorHomotopy_simplex]
    rw [SingularHomology.inducedChain_tripleAffineChainMap]
    change
      SingularHomology.tripleAffineChainMap p q r (n + 3)
          (SingularMayerVietoris.formalMap
            (Prod.map (SingularMayerVietoris.affineSimplex v)
              (Prod.map (SingularMayerVietoris.affineSimplex w)
                (SingularMayerVietoris.affineSimplex z)))
            (n + 4)
            (SingularHomology.formalAssociatorHomotopy n
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) =
        _
    rw [SingularHomology.formalMap_associatorHomotopy, SingularMayerVietoris.formalMap_simplex,
      SingularMayerVietoris.formalMap_simplex, SingularMayerVietoris.formalMap_simplex,
      SingularHomology.affineSimplex_stdVertices_image, SingularHomology.affineSimplex_stdVertices_image,
      SingularHomology.affineSimplex_stdVertices_image]
  exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The associator defect commutes with the affine chain maps on standard simplices. -/
theorem SingularHomology.crossProductAssociatorDefect_affineChainMap (p q r n : ℕ)
    (a : SingularMayerVietoris.FormalChains (SingularChains.Simplex p) 2)
    (b : SingularMayerVietoris.FormalChains (SingularChains.Simplex q) 2)
    (c : SingularMayerVietoris.FormalChains (SingularChains.Simplex r) (n + 1)) :
    SingularHomology.crossProductAssociatorDefect (SingularChains.Simplex p) (SingularChains.Simplex q)
        (SingularChains.Simplex r) n (SingularMayerVietoris.affineChainMap p 1 a)
        (SingularMayerVietoris.affineChainMap q 1 b)
        (SingularMayerVietoris.affineChainMap r n c) =
      SingularHomology.tripleAffineChainMap p q r (n + 2) (SingularHomology.formalAssociatorDefect n a b c) := by
  simp only [SingularHomology.crossProductAssociatorDefect_apply, SingularHomology.crossProductEdge_affineChainMap, Nat.reduceAdd,
    SingularHomology.crossProductTriangle_productAffineChainMap_left, SingularHomology.crossProductEdge_productAffineChainMap_right,
    SingularHomology.formalAssociatorDefect_apply, map_sub]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- Affine, degree-zero boundary identity for the associator homotopy. -/
theorem SingularHomology.crossProductAssociatorHomotopy_boundary_zero_affine (p q r : ℕ)
    (a : SingularMayerVietoris.FormalChains (SingularChains.Simplex p) 2)
    (b : SingularMayerVietoris.FormalChains (SingularChains.Simplex q) 2)
    (c : SingularMayerVietoris.FormalChains (SingularChains.Simplex r) 1) :
    ((SingularChains.singularComplex
                (SingularChains.Simplex p × (SingularChains.Simplex q × SingularChains.Simplex r))).d
            3 2).hom
        (SingularHomology.crossProductAssociatorHomotopy (SingularChains.Simplex p) (SingularChains.Simplex q)
          (SingularChains.Simplex r) 0 (SingularMayerVietoris.affineChainMap p 1 a)
          (SingularMayerVietoris.affineChainMap q 1 b)
          (SingularMayerVietoris.affineChainMap r 0 c)) =
      SingularHomology.crossProductAssociatorDefect (SingularChains.Simplex p) (SingularChains.Simplex q)
        (SingularChains.Simplex r) 0 (SingularMayerVietoris.affineChainMap p 1 a)
        (SingularMayerVietoris.affineChainMap q 1 b)
        (SingularMayerVietoris.affineChainMap r 0 c) := by
  rw [SingularHomology.crossProductAssociatorHomotopy_affineChainMap, SingularHomology.tripleAffineChainMap_boundary,
    SingularHomology.formalAssociatorHomotopy_boundary_zero, SingularHomology.crossProductAssociatorDefect_affineChainMap]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- Affine Leibniz-type identity for the associator homotopy on standard simplices. -/
theorem SingularHomology.crossProductAssociatorHomotopy_boundary_affine (p q r n : ℕ)
    (a : SingularMayerVietoris.FormalChains (SingularChains.Simplex p) 2)
    (b : SingularMayerVietoris.FormalChains (SingularChains.Simplex q) 2)
    (c : SingularMayerVietoris.FormalChains (SingularChains.Simplex r) (n + 2)) :
    ((SingularChains.singularComplex
                  (SingularChains.Simplex p ×
                    (SingularChains.Simplex q × SingularChains.Simplex r))).d
              (n + 4) (n + 3)).hom
          (SingularHomology.crossProductAssociatorHomotopy (SingularChains.Simplex p) (SingularChains.Simplex q)
            (SingularChains.Simplex r) (n + 1) (SingularMayerVietoris.affineChainMap p 1 a)
            (SingularMayerVietoris.affineChainMap q 1 b)
            (SingularMayerVietoris.affineChainMap r (n + 1) c)) +
        SingularHomology.crossProductAssociatorHomotopy (SingularChains.Simplex p) (SingularChains.Simplex q)
          (SingularChains.Simplex r) n (SingularMayerVietoris.affineChainMap p 1 a)
          (SingularMayerVietoris.affineChainMap q 1 b)
          (((SingularChains.singularComplex (SingularChains.Simplex r)).d (n + 1) n).hom
            (SingularMayerVietoris.affineChainMap r (n + 1) c)) =
      SingularHomology.crossProductAssociatorDefect (SingularChains.Simplex p) (SingularChains.Simplex q)
        (SingularChains.Simplex r) (n + 1) (SingularMayerVietoris.affineChainMap p 1 a)
        (SingularMayerVietoris.affineChainMap q 1 b)
        (SingularMayerVietoris.affineChainMap r (n + 1) c) := by
  rw [SingularHomology.crossProductAssociatorHomotopy_affineChainMap, SingularHomology.tripleAffineChainMap_boundary,
    SingularMayerVietoris.affineChainMap_boundary, SingularHomology.crossProductAssociatorHomotopy_affineChainMap,
    ← map_add, SingularHomology.formalAssociatorHomotopy_boundary, SingularHomology.crossProductAssociatorDefect_affineChainMap]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- Degree-zero case of the associator homotopy's defining boundary identity. -/
theorem SingularHomology.crossProductAssociatorHomotopy_boundary_zero {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (a : SingularChains.Chains X 1)
    (b : SingularChains.Chains Y 1) (c : SingularChains.Chains Z 0) :
    ((SingularChains.singularComplex (X × (Y × Z))).d 3 2).hom
        (SingularHomology.crossProductAssociatorHomotopy X Y Z 0 a b c) =
      SingularHomology.crossProductAssociatorDefect X Y Z 0 a b c := by
  have heq :
    SingularHomology.integerTrilinearPostcompose (SingularHomology.crossProductAssociatorHomotopy X Y Z 0)
        ((SingularChains.singularComplex (X × (Y × Z))).d 3 2).hom =
      SingularHomology.crossProductAssociatorDefect X Y Z 0 := by
    apply SingularHomology.chainTrilinearMap_ext X Y Z 1 1 0
    intro σ τ υ
    have hstd :=
      SingularHomology.crossProductAssociatorHomotopy_boundary_zero_affine 1 1 0
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 0))
    have hστυ := congrArg (SingularChains.inducedChain (σ.prodMap (τ.prodMap υ)) 2) hstd
    simpa only [SingularHomology.integerTrilinearPostcompose_apply, SingularChains.inducedChain_boundary,
      SingularHomology.crossProductAssociatorHomotopy_natural, SingularHomology.crossProductAssociatorDefect_natural,
      SingularMayerVietoris.affineChainMap_stdVertices, SingularChains.inducedChain_simplex,
      ContinuousMap.comp_id] using hστυ
  exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The defining identity of the associator homotopy on the space level: its boundary is the associativity defect. -/
theorem SingularHomology.crossProductAssociatorHomotopy_boundary {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (n : ℕ)
    (a : SingularChains.Chains X 1) (b : SingularChains.Chains Y 1)
    (c : SingularChains.Chains Z (n + 1)) :
    ((SingularChains.singularComplex (X × (Y × Z))).d (n + 4) (n + 3)).hom
          (SingularHomology.crossProductAssociatorHomotopy X Y Z (n + 1) a b c) +
        SingularHomology.crossProductAssociatorHomotopy X Y Z n a b
          (((SingularChains.singularComplex Z).d (n + 1) n).hom c) =
      SingularHomology.crossProductAssociatorDefect X Y Z (n + 1) a b c := by
  have heq :
    SingularHomology.integerTrilinearPostcompose (SingularHomology.crossProductAssociatorHomotopy X Y Z (n + 1))
          ((SingularChains.singularComplex (X × (Y × Z))).d (n + 4) (n + 3)).hom +
        SingularHomology.integerTrilinearPrecompose (SingularHomology.crossProductAssociatorHomotopy X Y Z n) LinearMap.id
          LinearMap.id ((SingularChains.singularComplex Z).d (n + 1) n).hom =
      SingularHomology.crossProductAssociatorDefect X Y Z (n + 1) := by
    apply SingularHomology.chainTrilinearMap_ext X Y Z 1 1 (n + 1)
    intro σ τ υ
    have hstd :=
      SingularHomology.crossProductAssociatorHomotopy_boundary_affine 1 1 (n + 1) n
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices (n + 1)))
    have hστυ := congrArg (SingularChains.inducedChain (σ.prodMap (τ.prodMap υ)) (n + 3)) hstd
    simpa only [SingularHomology.integerTrilinearPostcompose_apply, SingularHomology.integerTrilinearPrecompose_apply,
      LinearMap.add_apply, LinearMap.id_apply, map_add, SingularChains.inducedChain_boundary,
      SingularHomology.crossProductAssociatorHomotopy_natural, SingularHomology.crossProductAssociatorDefect_natural,
      SingularMayerVietoris.affineChainMap_stdVertices, SingularChains.inducedChain_simplex,
      ContinuousMap.comp_id] using hστυ
  exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- If the third chain is a cycle, the boundary of the associator homotopy reduces to the defect of the cycle data alone. -/
theorem SingularHomology.crossProductAssociatorHomotopy_boundary_of_cycle {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (n : ℕ)
    (a : SingularChains.Chains X 1) (b : SingularChains.Chains Y 1) (c : SingularChains.Chains Z n)
    (hc : ((SingularChains.singularComplex Z).d n (n - 1)).hom c = 0) :
    ((SingularChains.singularComplex (X × (Y × Z))).d (n + 3) (n + 2)).hom
        (SingularHomology.crossProductAssociatorHomotopy X Y Z n a b c) =
      SingularHomology.crossProductAssociatorDefect X Y Z n a b c := by
  cases n with
  | zero => exact SingularHomology.crossProductAssociatorHomotopy_boundary_zero a b c
  | succ
    n =>
    have hc' : ((SingularChains.singularComplex Z).d (n + 1) n).hom c = 0 := by
      simpa only [Nat.succ_sub_one] using hc
    simpa only [hc', map_zero, add_zero] using SingularHomology.crossProductAssociatorHomotopy_boundary n a b c


/-! ### Associativity and cyclicity on homology -/

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- Associativity of the cross product on cycle classes: the two bracketings agree after the product re-association. -/
theorem SingularHomology.crossProductCycleClasses_associative {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (a : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 1)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) 1)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Z) 1) :
    (HomologicalComplex.homologyMap
            (SingularChains.singularChainMap (Homeomorph.prodAssoc X Y Z : C(_, _))) 3).hom
        (SingularMayerVietoris.ModuleHomology.cycleClass
          (SingularChains.singularComplex ((X × Y) × Z)) 3
          (SingularHomology.crossProductTwoOneCycles (X × Y) Z (SingularHomology.crossProductCycles X Y 1 a b) c)) =
      SingularMayerVietoris.ModuleHomology.cycleClass
        (SingularChains.singularComplex (X × (Y × Z))) 3
        (SingularHomology.crossProductCycles X (Y × Z) 2 a (SingularHomology.crossProductCycles Y Z 1 b c)) := by
  rw [SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass]
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff
        (SingularChains.singularComplex (X × (Y × Z))) 3 _ _).mpr
  refine ⟨SingularHomology.crossProductAssociatorHomotopy X Y Z 1 a.1 b.1 c.1, ?_⟩
  simp only [SingularMayerVietoris.ModuleHomology.mapCycles_val, SingularHomology.crossProductTwoOneCycles_val,
    SingularHomology.crossProductCycles_val]
  exact
    SingularHomology.crossProductAssociatorHomotopy_boundary_of_cycle 1 a.1 b.1 c.1
      (SingularMayerVietoris.ModuleHomology.cycle_condition (SingularChains.singularComplex Z) 1 c)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- Associativity of the homology cross product: `(a × b) × c = (a × (b × c))` after the canonical re-association of the product space. -/
theorem SingularHomology.crossProductHomology_associative {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (a : SingularMayerVietoris.SingularHomology X 1)
    (b : SingularMayerVietoris.SingularHomology Y 1)
    (c : SingularMayerVietoris.SingularHomology Z 1) :
    SingularMayerVietoris.singularHomologyMap (Homeomorph.prodAssoc X Y Z : C(_, _)) 3
        (SingularHomology.crossProductHomologyTwoOne (X × Y) Z (SingularHomology.crossProductHomology X Y 1 a b) c) =
      SingularHomology.crossProductHomology X (Y × Z) 2 a (SingularHomology.crossProductHomology Y Z 1 b c) := by
  obtain ⟨a, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (SingularChains.singularComplex X) 1
      a
  obtain ⟨b, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (SingularChains.singularComplex Y) 1
      b
  obtain ⟨c, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (SingularChains.singularComplex Z) 1
      c
  rw [SingularHomology.crossProductHomology_cycleClass, SingularHomology.crossProductHomologyTwoOne_cycleClass,
    SingularHomology.crossProductHomology_cycleClass, SingularHomology.crossProductHomology_cycleClass]
  exact SingularHomology.crossProductCycleClasses_associative a b c

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The cyclic re-association map `Y × (Z × X) → X × (Y × Z)` used to state cyclicity of the triple cross product. -/
def SingularHomology.crossProductCyclicMap (X Y Z : Type) [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] : C(Y × (Z × X), X × (Y × Z)) :=
  ContinuousMap.prodSwap.comp ((Homeomorph.prodAssoc Y Z X).symm : C(_, _))

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The cyclic map composes with association and swap to the identity: it is a homeomorphism with two-fold inverse data. -/
theorem SingularHomology.crossProductCyclicMap_assoc_swap {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] :
    (SingularHomology.crossProductCyclicMap X Y Z).comp
        ((Homeomorph.prodAssoc Y Z X : C(_, _)).comp ContinuousMap.prodSwap) =
      ContinuousMap.id (X × (Y × Z)) :=
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- Cyclicity of the triple 1-class cross product: cyclically permuting the three factors rotates the value, the Jacobi-type identity for the cross product. -/
theorem SingularHomology.crossProductHomology_cyclic {X Y Z : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (a : SingularMayerVietoris.SingularHomology X 1)
    (b : SingularMayerVietoris.SingularHomology Y 1)
    (c : SingularMayerVietoris.SingularHomology Z 1) :
    SingularHomology.crossProductHomology X (Y × Z) 2 a (SingularHomology.crossProductHomology Y Z 1 b c) =
      SingularMayerVietoris.singularHomologyMap (SingularHomology.crossProductCyclicMap X Y Z) 3
        (SingularHomology.crossProductHomology Y (Z × X) 2 b (SingularHomology.crossProductHomology Z X 1 c a)) := by
  have h := SingularHomology.crossProductHomology_associative b c a
  rw [SingularHomology.crossProductHomologyTwoOne_apply] at h
  have h' :=
    congrArg (SingularMayerVietoris.singularHomologyMap (SingularHomology.crossProductCyclicMap X Y Z) 3) h
  have hmap :
    (SingularMayerVietoris.singularHomologyMap (SingularHomology.crossProductCyclicMap X Y Z) 3).comp
        ((SingularMayerVietoris.singularHomologyMap (Homeomorph.prodAssoc Y Z X : C(_, _)) 3).comp
          (SingularMayerVietoris.singularHomologyMap
            (ContinuousMap.prodSwap : C(X × (Y × Z), (Y × Z) × X)) 3)) =
      LinearMap.id := by
    rw [← SingularHomology.singularHomologyMap_comp, ← SingularHomology.singularHomologyMap_comp, SingularHomology.crossProductCyclicMap_assoc_swap,
      SingularHomology.singularHomologyMap_id]
  exact
    (LinearMap.congr_fun hmap
          (SingularHomology.crossProductHomology X (Y × Z) 2 a (SingularHomology.crossProductHomology Y Z 1 b c))).symm.trans
      h'
