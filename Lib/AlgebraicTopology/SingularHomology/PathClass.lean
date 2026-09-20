/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.Chains
public import Lib.AlgebraicTopology.SingularHomology.CircleProduct
public import Lib.AlgebraicTopology.SingularHomology.Coproduct
public import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
public import Lib.AlgebraicTopology.SingularHomology.ModuleHomology
public import Lib.AlgebraicTopology.SingularHomology.Sphere
public import Lib.AlgebraicTopology.SingularHomology.SphereHomology
public import Lib.AlgebraicTopology.SingularHomology.Sum
public import Lib.AlgebraicTopology.SingularHomology.Suspension
public import Lib.Topology.Homotopy.Suspension
/-!
# Path classes in one-chains and the loop-homology class

  Chain-level path classes: the class of a path in one-chains modulo boundaries,
  its homotopy invariance, additivity under concatenation, and the induced class
  of loops (Hatcher, Algebraic Topology, proof of Theorem 2A.1).
-/



open Set Function Filter Manifold Topology

@[expose] public noncomputable section

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-! ### Loop classes and the abelianized fundamental group -/

/-- The abelianized fundamental group at a basepoint. -/
abbrev SingularChains.AbelianPi1 (X : Type*) [TopologicalSpace X] (b : X) :=
  Additive (Abelianization (FundamentalGroup X b))

/-- The abelianized class of a loop. -/
def SingularChains.loopQuotient {X : Type*} [TopologicalSpace X] {b : X} (p : Path b b) :
    FundamentalGroup X b :=
  Path.Homotopic.Quotient.mk p

/-- The loop class in the abelianized fundamental group. -/
def SingularChains.loopClass {X : Type*} [TopologicalSpace X] {b : X} (p : Path b b) :
    AbelianPi1 X b :=
  Additive.ofMul (Abelianization.of (loopQuotient p))

/-- Every abelianized class is represented by a loop. -/
theorem SingularChains.loopClass_surjective {X : Type*} [TopologicalSpace X] {b : X} :
    Function.Surjective (loopClass (b := b)) := by
  intro a
  obtain ⟨g, hg⟩ := Quotient.exists_rep a.toMul
  change Abelianization.of g = a.toMul at hg
  obtain ⟨p, hp⟩ := Path.Homotopic.Quotient.mk_surjective g
  have hp' : loopQuotient p = g := hp
  refine ⟨p, ?_⟩
  rw [loopClass, hp', hg]
  rfl

/-- Concatenation becomes addition in the abelianized quotient. -/
theorem SingularChains.loopQuotient_trans {X : Type*} [TopologicalSpace X] {b : X}
    (p q : Path b b) : loopQuotient (p.trans q) = loopQuotient q * loopQuotient p :=
  rfl

/-- Reversal becomes negation in the abelianized quotient. -/
theorem SingularChains.loopQuotient_symm {X : Type*} [TopologicalSpace X] {b : X} (p : Path b b) :
    loopQuotient p.symm = (loopQuotient p)⁻¹ :=
  rfl

/-- Homotopic loops have the same abelianized class. -/
theorem SingularChains.loopClass_homotopic {X : Type*} [TopologicalSpace X] {b : X}
    {p q : Path b b} (h : p.Homotopic q) : loopClass p = loopClass q :=
  congrArg (fun g : FundamentalGroup X b => Additive.ofMul (Abelianization.of g))
    (Path.Homotopic.Quotient.eq.mpr h)

/-- The loop class of a concatenation is the sum. -/
theorem SingularChains.loopClass_trans {X : Type*} [TopologicalSpace X] {b : X} (p q : Path b b) :
    loopClass (p.trans q) = loopClass p + loopClass q := by
  rw [loopClass, loopQuotient_trans, map_mul, ofMul_mul, add_comm]
  rfl

/-- The loop class of a reversal is the negative. -/
@[simp]
theorem SingularChains.loopClass_symm {X : Type*} [TopologicalSpace X] {b : X} (p : Path b b) :
    loopClass p.symm = -loopClass p := by
  rw [loopClass, loopQuotient_symm, map_inv, ofMul_inv]
  rfl

/-- The loop formed by conjugating a path by chosen basepoint paths. -/
def SingularChains.basedLoop {X : Type*} [TopologicalSpace X] {b x y : X} (r : ∀ x : X, Path b x)
    (p : Path x y) : Path b b :=
  (r x).trans (p.trans (r y).symm)

/-- The abelianized class of a based loop. -/
def SingularChains.basedLoopQuotient {X : Type*} [TopologicalSpace X] {b x y : X}
    (r : ∀ x : X, Path b x) (p : Path x y) : FundamentalGroup X b :=
  Path.Homotopic.Quotient.mk (basedLoop r p)

/-- The based loop's class in the abelianized fundamental group. -/
def SingularChains.basedLoopClass {X : Type*} [TopologicalSpace X] {b x y : X}
    (r : ∀ x : X, Path b x) (p : Path x y) : AbelianPi1 X b :=
  loopClass (basedLoop r p)

/-- Two descriptions of a based loop class agree. -/
theorem SingularChains.basedLoopClass_eq {X : Type*} [TopologicalSpace X] {b x y : X}
    (r : ∀ x : X, Path b x) (p : Path x y) :
    basedLoopClass r p = Additive.ofMul (Abelianization.of (basedLoopQuotient r p)) :=
  rfl

/-- The based loop depends only on the homotopy class of the path. -/
theorem SingularChains.basedLoop_homotopic {X : Type*} [TopologicalSpace X] {b x y : X}
    (r : ∀ x : X, Path b x) {p q : Path x y} (h : p.Homotopic q) :
    (basedLoop r p).Homotopic (basedLoop r q) :=
  (Path.Homotopic.refl (r x)).hcomp (h.hcomp (Path.Homotopic.refl (r y).symm))

/-- The based loop class depends only on the homotopy class. -/
theorem SingularChains.basedLoopClass_homotopic {X : Type*} [TopologicalSpace X] {b x y : X}
    (r : ∀ x : X, Path b x) {p q : Path x y} (h : p.Homotopic q) :
    basedLoopClass r p = basedLoopClass r q :=
  loopClass_homotopic (basedLoop_homotopic r h)

/-- Based loop classes add under transitivity. -/
theorem SingularChains.basedLoopQuotient_trans {X : Type*} [TopologicalSpace X] {b x y z : X}
    (r : ∀ x : X, Path b x) (p : Path x y) (q : Path y z) :
    basedLoopQuotient r (p.trans q) = basedLoopQuotient r q * basedLoopQuotient r p := by
  simp only [basedLoopQuotient, basedLoop, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm, FundamentalGroup.mul_def,
    Path.Homotopic.Quotient.trans_assoc]
  rw [←
    Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.mk (r y)).symm
      (Path.Homotopic.Quotient.mk (r y)),
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]

/-- The based loop class of a composite path is the sum. -/
theorem SingularChains.basedLoopClass_trans {X : Type*} [TopologicalSpace X] {b x y z : X}
    (r : ∀ x : X, Path b x) (p : Path x y) (q : Path y z) :
    basedLoopClass r (p.trans q) = basedLoopClass r p + basedLoopClass r q := by
  rw [basedLoopClass_eq, basedLoopQuotient_trans, map_mul, ofMul_mul, add_comm, ←
    basedLoopClass_eq, ← basedLoopClass_eq]

/-- A loop's based class is its own class. -/
@[simp]
theorem SingularChains.basedLoopClass_loop {X : Type*} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (p : Path b b) : basedLoopClass r p = loopClass p := by
  rw [basedLoopClass, basedLoop, loopClass_trans, loopClass_trans, loopClass_symm]
  abel

/-- The based loop class of a triangle boundary vanishes. -/
theorem SingularChains.basedLoopClass_triangle {X : Type*} [TopologicalSpace X] {b x y z : X}
    (r : ∀ x : X, Path b x) (p₀₁ : Path x y) (p₁₂ : Path y z) (p₀₂ : Path x z)
    (h : (p₀₁.trans p₁₂).Homotopic p₀₂) :
    basedLoopClass r p₀₁ + basedLoopClass r p₁₂ = basedLoopClass r p₀₂ := by
  rw [← basedLoopClass_trans]
  exact basedLoopClass_homotopic r h

/-- The triangle boundary's based loop class is zero. -/
theorem SingularChains.basedLoopClass_triangle_boundary {X : Type*} [TopologicalSpace X]
    {b x y z : X} (r : ∀ x : X, Path b x) (p₀₁ : Path x y) (p₁₂ : Path y z) (p₀₂ : Path x z)
    (h : (p₀₁.trans p₁₂).Homotopic p₀₂) :
    basedLoopClass r p₁₂ - basedLoopClass r p₀₂ + basedLoopClass r p₀₁ = 0 := by
  rw [← basedLoopClass_triangle r p₀₁ p₁₂ p₀₂ h]
  abel

/-! ### Path classes as chains -/

/-- The path-homotopy class of a path. -/
def SingularChains.pathClass {X : Type} [TopologicalSpace X] {x y : X} (p : Path x y) :
    Opchains X :=
  chainClass X (pathChain p)

/-- The path class is unchanged under endpoint-fixed homotopy. -/
theorem SingularChains.pathClass_homotopy {X : Type} [TopologicalSpace X] {x y : X}
    {p q : Path x y} (H : p.Homotopy q) : pathClass p = pathClass q :=
  (chainClass_eq_iff X _ _).mpr ⟨correctedHomotopyChain H, boundaryTwo_correctedHomotopyChain H⟩

/-- Homotopic paths have equal path classes. -/
theorem SingularChains.pathClass_homotopic {X : Type} [TopologicalSpace X] {x y : X}
    {p q : Path x y} (h : p.Homotopic q) : pathClass p = pathClass q := by
  obtain ⟨H⟩ := h
  exact pathClass_homotopy H

/-- The class of the constant path is reflexivity. -/
@[simp]
theorem SingularChains.pathClass_refl {X : Type} [TopologicalSpace X] (x : X) :
    pathClass (Path.refl x) = 0 := by
  change chainClass X (pathChain (Path.refl x)) = 0
  rw [pathChain_refl, ← boundaryTwo_constantTriangleChain]
  exact chainClass_boundary X _

/-- The class of a concatenation is the transitivity composite. -/
theorem SingularChains.pathClass_trans {X : Type} [TopologicalSpace X] {x y z : X} (p : Path x y)
    (q : Path y z) : pathClass (p.trans q) = pathClass p + pathClass q := by
  have h := chainClass_boundary X (concatChain p q)
  rw [boundaryTwo_concatChain, map_add, map_sub] at h
  change pathClass q - pathClass (p.trans q) + pathClass p = 0 at h
  apply sub_eq_zero.mp
  calc
    pathClass (p.trans q) - (pathClass p + pathClass q) =
        -(pathClass q - pathClass (p.trans q) + pathClass p) := by abel
    _ = 0 := by rw [h, neg_zero]

/-- The class of a reversed path is the inverse. -/
@[simp]
theorem SingularChains.pathClass_symm {X : Type} [TopologicalSpace X] {x y : X} (p : Path x y) :
    pathClass p.symm = -pathClass p := by
  have h := pathClass_homotopic (Path.Homotopic.trans_symm p)
  rw [pathClass_trans, pathClass_refl] at h
  exact eq_neg_of_add_eq_zero_right h

/-- The path class is stable under endpoint casts. -/
@[simp]
theorem SingularChains.pathClass_cast {X : Type} [TopologicalSpace X] {x y : X} (p : Path x y)
    {x' y' : X} (hx : x' = x) (hy : y' = y) : pathClass (p.cast hx hy) = pathClass p :=
  rfl

/-! ### The Hurewicz map -/

/-- A loop viewed as a singular 1-cycle. -/
def SingularChains.loopCycle {X : Type} [TopologicalSpace X] {x : X} (p : Path x x) : Cycles1 X :=
  mkCycle1 X (pathChain p) (boundaryOne_loop p)

/-- The loop cycle's chain is the loop simplex. -/
@[simp]
theorem SingularChains.loopCycle_val {X : Type} [TopologicalSpace X] {x : X} (p : Path x x) :
    (loopCycle p).1 = pathChain p :=
  rfl

/-- The homology class of a loop cycle. -/
def SingularChains.loopHomologyClass {X : Type} [TopologicalSpace X] {x : X} (p : Path x x) :
    SingularH1 X :=
  cycleClass X (loopCycle p)

/-- The loop homology class computed as a chain class. -/
@[simp]
theorem SingularChains.homologyToChainClass_loopHomologyClass {X : Type} [TopologicalSpace X]
    {x : X} (p : Path x x) : homologyToChainClass X (loopHomologyClass p) = pathClass p := by
  rw [loopHomologyClass, homologyToChainClass_cycleClass]
  rfl

/-- Homotopic loops have the same homology class. -/
theorem SingularChains.loopHomologyClass_homotopic {X : Type} [TopologicalSpace X] {x : X}
    {p q : Path x x} (h : p.Homotopic q) : loopHomologyClass p = loopHomologyClass q := by
  apply homologyToChainClass_injective X
  rw [homologyToChainClass_loopHomologyClass, homologyToChainClass_loopHomologyClass]
  exact pathClass_homotopic h

/-- The constant loop has zero homology class. -/
@[simp]
theorem SingularChains.loopHomologyClass_refl {X : Type} [TopologicalSpace X] (x : X) :
    loopHomologyClass (Path.refl x) = 0 := by
  apply homologyToChainClass_injective X
  rw [homologyToChainClass_loopHomologyClass, pathClass_refl, map_zero]

/-- The homology class of a concatenation is the sum. -/
theorem SingularChains.loopHomologyClass_trans {X : Type} [TopologicalSpace X] {x : X}
    (p q : Path x x) :
    loopHomologyClass (p.trans q) = loopHomologyClass p + loopHomologyClass q := by
  apply homologyToChainClass_injective X
  rw [homologyToChainClass_loopHomologyClass, map_add, homologyToChainClass_loopHomologyClass,
    homologyToChainClass_loopHomologyClass, pathClass_trans]

/-- The function sending a loop to its homology class. -/
def SingularChains.hurewiczFunction {X : Type} [TopologicalSpace X] (b : X) :
    FundamentalGroup X b → SingularH1 X :=
  Quotient.lift (fun p : Path b b => loopHomologyClass p)
    (fun _ _ h => loopHomologyClass_homotopic h)

/-- The Hurewicz map on the fundamental group. -/
def SingularChains.hurewiczPi1 {X : Type} [TopologicalSpace X] (b : X) :
    FundamentalGroup X b →* Multiplicative (SingularH1 X)
    where
  toFun g := Multiplicative.ofAdd (hurewiczFunction b g)
  map_one' := congrArg Multiplicative.ofAdd (loopHomologyClass_refl b)
  map_mul' g
    h := by
    obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective g
    obtain ⟨q, rfl⟩ := Path.Homotopic.Quotient.mk_surjective h
    change
      Multiplicative.ofAdd (loopHomologyClass (q.trans p)) =
        Multiplicative.ofAdd (loopHomologyClass p + loopHomologyClass q)
    rw [loopHomologyClass_trans, add_comm]

/-- The Hurewicz homomorphism into the abelianization target. -/
def SingularChains.hurewiczMap {X : Type} [TopologicalSpace X] (b : X) :
    AbelianPi1 X b →ₗ[ℤ] SingularH1 X
    where
  toFun := (Abelianization.lift (hurewiczPi1 b)).toAdditiveLeft
  map_add' := (Abelianization.lift (hurewiczPi1 b)).toAdditiveLeft.map_add
  map_smul' n
    a := by
    simpa using map_intCast_smul (Abelianization.lift (hurewiczPi1 b)).toAdditiveLeft ℤ ℤ n a

/-- The Hurewicz map computes the loop's homology class. -/
@[simp]
theorem SingularChains.hurewiczMap_loopClass {X : Type} [TopologicalSpace X] (b : X)
    (p : Path b b) : hurewiczMap b (loopClass p) = loopHomologyClass p :=
  rfl

/-- The Hurewicz class computed as a chain class. -/
theorem SingularChains.homologyToChainClass_hurewiczMap_loopClass {X : Type} [TopologicalSpace X]
    (b : X) (p : Path b b) : homologyToChainClass X (hurewiczMap b (loopClass p)) = pathClass p :=
  by rw [hurewiczMap_loopClass, homologyToChainClass_loopHomologyClass]

/-- The Hurewicz map on a based loop class. -/
theorem SingularChains.hurewiczMap_basedLoopClass {X : Type} [TopologicalSpace X] {x y : X} (b : X)
    (r : ∀ a : X, Path b a) (p : Path x y) :
    homologyToChainClass X (hurewiczMap b (basedLoopClass r p)) =
      pathClass (r x) + pathClass p - pathClass (r y) := by
  change homologyToChainClass X (hurewiczMap b (loopClass (basedLoop r p))) = _
  rw [homologyToChainClass_hurewiczMap_loopClass]
  change pathClass ((r x).trans (p.trans (r y).symm)) = _
  rw [pathClass_trans, pathClass_trans, pathClass_symm]
  abel

/-- The based loop class is stable under endpoint casts. -/
theorem SingularChains.basedLoopClass_cast {X : Type} [TopologicalSpace X] {b x y : X}
    (r : ∀ x : X, Path b x) (p : Path x y) {x' y' : X} (hx : x' = x) (hy : y' = y) :
    basedLoopClass r (p.cast hx hy) = basedLoopClass r p := by
  cases hx
  cases hy
  rfl

/-- The simplex path of a cast path simplex. -/
theorem SingularChains.simplexPath_pathSimplex_cast {X : Type} [TopologicalSpace X] {x y : X}
    (p : Path x y) :
    simplexPath (pathSimplex p) = p.cast (pathSimplex_vertex_zero p) (pathSimplex_vertex_one p) :=
  by
  apply Path.ext
  funext t
  change p (stdSimplexHomeomorphUnitInterval (stdSimplexHomeomorphUnitInterval.symm t)) = p t
  rw [Homeomorph.apply_symm_apply]

/-- The based loop class of a simplex path. -/
@[simp]
theorem SingularChains.basedLoopClass_simplexPath_pathSimplex {X : Type} [TopologicalSpace X]
    {b x y : X} (r : ∀ x : X, Path b x) (p : Path x y) :
    basedLoopClass r (simplexPath (pathSimplex p)) = basedLoopClass r p := by
  rw [simplexPath_pathSimplex_cast, basedLoopClass_cast]

/-! ### Edge-loop bookkeeping -/

/-- The cochain assigning to an edge its based loop class. -/
def SingularChains.edgeLoopCochain {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) : Chains X 1 →ₗ[ℤ] AbelianPi1 X b :=
  chainLift X 1 (fun σ => basedLoopClass r (simplexPath σ))

/-- The edge-loop cochain computes on a simplex. -/
@[simp]
theorem SingularChains.edgeLoopCochain_simplex {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (σ : SingularSimplex X 1) :
    edgeLoopCochain r (simplexChain X 1 σ) = basedLoopClass r (simplexPath σ) :=
  chainLift_simplex X 1 (fun σ => basedLoopClass r (simplexPath σ)) σ

/-- The edge-loop cochain on a path simplex. -/
@[simp]
theorem SingularChains.edgeLoopCochain_pathSimplex {X : Type} [TopologicalSpace X] {b x y : X}
    (r : ∀ x : X, Path b x) (p : Path x y) :
    edgeLoopCochain r (simplexChain X 1 (pathSimplex p)) = basedLoopClass r p := by
  rw [edgeLoopCochain_simplex, basedLoopClass_simplexPath_pathSimplex]

/-- The edge-loop cochain on a loop simplex. -/
@[simp]
theorem SingularChains.edgeLoopCochain_loopSimplex {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (p : Path b b) :
    edgeLoopCochain r (simplexChain X 1 (pathSimplex p)) = loopClass p := by
  rw [edgeLoopCochain_pathSimplex, basedLoopClass_loop]

/-- The chain built from chosen basepoint paths. -/
def SingularChains.basePathChain {X : Type} [TopologicalSpace X] {b : X} (r : ∀ x : X, Path b x) :
    Chains X 0 →ₗ[ℤ] Chains X 1 :=
  chainLift X 0 (fun σ => pathChain (r (σ (stdSimplex.vertex (S := ℝ) (0 : Fin 1)))))

/-- The base path chain on a point chain. -/
@[simp]
theorem SingularChains.basePathChain_pointChain {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (x : X) : basePathChain r (pointChain x) = pathChain (r x) :=
  chainLift_simplex X 0 _ (ContinuousMap.const (Simplex 0) x)

/-- The edge closure of a path chain. -/
theorem SingularChains.edgeClosure_pathChain {X : Type} [TopologicalSpace X] {b x y : X}
    (r : ∀ x : X, Path b x) (p : Path x y) :
    homologyToChainClass X (hurewiczMap b (edgeLoopCochain r (pathChain p))) =
      chainClass X (pathChain p) - chainClass X (basePathChain r (boundaryOne X (pathChain p))) :=
  by
  have he : edgeLoopCochain r (pathChain p) = basedLoopClass r p :=
    edgeLoopCochain_pathSimplex r p
  rw [he, hurewiczMap_basedLoopClass, boundaryOne_pathChain, map_sub, basePathChain_pointChain,
    basePathChain_pointChain, map_sub]
  change
    pathClass (r x) + pathClass p - pathClass (r y) =
      pathClass p - (pathClass (r y) - pathClass (r x))
  abel

/-- The edge-closure chain identity relating boundary and base paths. -/
theorem SingularChains.edgeClosure_chain_identity {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) :
    (homologyToChainClass X).comp ((hurewiczMap b).comp (edgeLoopCochain r)) =
      chainClass X - (chainClass X).comp ((basePathChain r).comp (boundaryOne X)) := by
  apply chainMap_ext X 1
  intro σ
  have h := edgeClosure_pathChain r (simplexPath σ)
  simpa only [pathChain, pathSimplex_simplexPath, LinearMap.comp_apply, LinearMap.sub_apply] using
    h

/-- The edge closure of a loop is a cycle. -/
theorem SingularChains.edgeClosure_cycle {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (c : Cycles1 X) :
    homologyToChainClass X (hurewiczMap b (edgeLoopCochain r c.1)) = chainClass X c.1 := by
  have h := LinearMap.congr_fun (edgeClosure_chain_identity r) c.1
  change
    homologyToChainClass X (hurewiczMap b (edgeLoopCochain r c.1)) =
      chainClass X c.1 - chainClass X (basePathChain r (boundaryOne X c.1)) at h
  simpa only [cycles1_boundary, map_zero, sub_zero] using h

/-! ### The abelianization equivalence -/

/-- A map out of the fundamental group to an abelian group factors through the abelianization. -/
def SingularChains.abelianPi1EquivOfPi1 {X : Type} [TopologicalSpace X] (b : X) {A : Type*}
    [AddCommGroup A] [Module ℤ A] (e : FundamentalGroup X b ≃* Multiplicative A) :
    AbelianPi1 X b ≃ₗ[ℤ] A :=
  (e.abelianizationCongr.trans
      (Abelianization.equivOfComm (H := Multiplicative A)).symm).toAdditiveLeft.toIntLinearEquiv

/-- The abelianization equivalence computes on representatives. -/
@[simp]
theorem SingularChains.abelianPi1EquivOfPi1_of {X : Type} [TopologicalSpace X] (b : X) {A : Type*}
    [AddCommGroup A] [Module ℤ A] (e : FundamentalGroup X b ≃* Multiplicative A)
    (g : FundamentalGroup X b) :
    abelianPi1EquivOfPi1 b e (Additive.ofMul (Abelianization.of g)) = (e g).toAdd :=
  rfl

/-! ### Functoriality -/

/-- Path simplices are mapped functorially. -/
theorem SingularChains.pathSimplex_map {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {x y : X} (f : C(X, Y)) (p : Path x y) :
    pathSimplex (p.map f.continuous) = f.comp (pathSimplex p) :=
  rfl

/-- The induced chain of a path chain is the path chain of the image. -/
@[simp]
theorem SingularChains.inducedChain_pathChain {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {x y : X} (f : C(X, Y)) (p : Path x y) :
    inducedChain f 1 (pathChain p) = pathChain (p.map f.continuous) := by
  simp only [pathChain, inducedChain_simplex, pathSimplex_map]

/-- The induced cycle of a loop cycle is the image loop's cycle. -/
@[simp]
theorem SingularChains.inducedCycles_loopCycle {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (b : X) (p : Path b b) :
    inducedCycles f (loopCycle p) = loopCycle (p.map f.continuous) := by
  apply Subtype.ext
  rw [inducedCycles_val, loopCycle_val, loopCycle_val, inducedChain_pathChain]

/-- The induced homology class of a loop is the image loop's class. -/
@[simp]
theorem SingularChains.inducedHomology_loopHomologyClass {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (b : X) (p : Path b b) :
    inducedHomology f (loopHomologyClass p) = loopHomologyClass (p.map f.continuous) := by
  rw [loopHomologyClass, inducedHomology_cycleClass, inducedCycles_loopCycle]
  rfl
