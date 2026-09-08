/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.AlgebraicTopology.SingularHomology.Chains
import Lib.AlgebraicTopology.SingularHomology.CircleProduct
import Lib.AlgebraicTopology.SingularHomology.Coproduct
import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
import Lib.AlgebraicTopology.SingularHomology.ModuleHomology
import Lib.AlgebraicTopology.SingularHomology.Sphere
import Lib.AlgebraicTopology.SingularHomology.SphereHomology
import Lib.AlgebraicTopology.SingularHomology.Sum
import Lib.AlgebraicTopology.SingularHomology.Suspension
import Lib.Topology.Homotopy.CylinderHEP
import Lib.Topology.Homotopy.Suspension


set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

abbrev SingularChains.AbelianPi1 (X : Type*) [TopologicalSpace X] (b : X) :=
  Additive (Abelianization (FundamentalGroup X b))

def SingularChains.loopQuotient {X : Type*} [TopologicalSpace X] {b : X} (p : Path b b) :
    FundamentalGroup X b :=
  Path.Homotopic.Quotient.mk p

def SingularChains.loopClass {X : Type*} [TopologicalSpace X] {b : X} (p : Path b b) :
    AbelianPi1 X b :=
  Additive.ofMul (Abelianization.of (loopQuotient p))

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

theorem SingularChains.loopQuotient_trans {X : Type*} [TopologicalSpace X] {b : X}
    (p q : Path b b) : loopQuotient (p.trans q) = loopQuotient q * loopQuotient p :=
  rfl

theorem SingularChains.loopQuotient_symm {X : Type*} [TopologicalSpace X] {b : X} (p : Path b b) :
    loopQuotient p.symm = (loopQuotient p)⁻¹ :=
  rfl

theorem SingularChains.loopClass_homotopic {X : Type*} [TopologicalSpace X] {b : X}
    {p q : Path b b} (h : p.Homotopic q) : loopClass p = loopClass q :=
  congrArg (fun g : FundamentalGroup X b => Additive.ofMul (Abelianization.of g))
    (Path.Homotopic.Quotient.eq.mpr h)

theorem SingularChains.loopClass_trans {X : Type*} [TopologicalSpace X] {b : X} (p q : Path b b) :
    loopClass (p.trans q) = loopClass p + loopClass q := by
  rw [loopClass, loopQuotient_trans, map_mul, ofMul_mul, add_comm]
  rfl

@[simp]
theorem SingularChains.loopClass_symm {X : Type*} [TopologicalSpace X] {b : X} (p : Path b b) :
    loopClass p.symm = -loopClass p := by
  rw [loopClass, loopQuotient_symm, map_inv, ofMul_inv]
  rfl

def SingularChains.basedLoop {X : Type*} [TopologicalSpace X] {b x y : X} (r : ∀ x : X, Path b x)
    (p : Path x y) : Path b b :=
  (r x).trans (p.trans (r y).symm)

def SingularChains.basedLoopQuotient {X : Type*} [TopologicalSpace X] {b x y : X}
    (r : ∀ x : X, Path b x) (p : Path x y) : FundamentalGroup X b :=
  Path.Homotopic.Quotient.mk (basedLoop r p)

def SingularChains.basedLoopClass {X : Type*} [TopologicalSpace X] {b x y : X}
    (r : ∀ x : X, Path b x) (p : Path x y) : AbelianPi1 X b :=
  loopClass (basedLoop r p)

theorem SingularChains.basedLoopClass_eq {X : Type*} [TopologicalSpace X] {b x y : X}
    (r : ∀ x : X, Path b x) (p : Path x y) :
    basedLoopClass r p = Additive.ofMul (Abelianization.of (basedLoopQuotient r p)) :=
  rfl

theorem SingularChains.basedLoop_homotopic {X : Type*} [TopologicalSpace X] {b x y : X}
    (r : ∀ x : X, Path b x) {p q : Path x y} (h : p.Homotopic q) :
    (basedLoop r p).Homotopic (basedLoop r q) :=
  (Path.Homotopic.refl (r x)).hcomp (h.hcomp (Path.Homotopic.refl (r y).symm))

theorem SingularChains.basedLoopClass_homotopic {X : Type*} [TopologicalSpace X] {b x y : X}
    (r : ∀ x : X, Path b x) {p q : Path x y} (h : p.Homotopic q) :
    basedLoopClass r p = basedLoopClass r q :=
  loopClass_homotopic (basedLoop_homotopic r h)

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

theorem SingularChains.basedLoopClass_trans {X : Type*} [TopologicalSpace X] {b x y z : X}
    (r : ∀ x : X, Path b x) (p : Path x y) (q : Path y z) :
    basedLoopClass r (p.trans q) = basedLoopClass r p + basedLoopClass r q := by
  rw [basedLoopClass_eq, basedLoopQuotient_trans, map_mul, ofMul_mul, add_comm, ←
    basedLoopClass_eq, ← basedLoopClass_eq]

@[simp]
theorem SingularChains.basedLoopClass_loop {X : Type*} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (p : Path b b) : basedLoopClass r p = loopClass p := by
  rw [basedLoopClass, basedLoop, loopClass_trans, loopClass_trans, loopClass_symm]
  abel

theorem SingularChains.basedLoopClass_triangle {X : Type*} [TopologicalSpace X] {b x y z : X}
    (r : ∀ x : X, Path b x) (p₀₁ : Path x y) (p₁₂ : Path y z) (p₀₂ : Path x z)
    (h : (p₀₁.trans p₁₂).Homotopic p₀₂) :
    basedLoopClass r p₀₁ + basedLoopClass r p₁₂ = basedLoopClass r p₀₂ := by
  rw [← basedLoopClass_trans]
  exact basedLoopClass_homotopic r h

theorem SingularChains.basedLoopClass_triangle_boundary {X : Type*} [TopologicalSpace X]
    {b x y z : X} (r : ∀ x : X, Path b x) (p₀₁ : Path x y) (p₁₂ : Path y z) (p₀₂ : Path x z)
    (h : (p₀₁.trans p₁₂).Homotopic p₀₂) :
    basedLoopClass r p₁₂ - basedLoopClass r p₀₂ + basedLoopClass r p₀₁ = 0 := by
  rw [← basedLoopClass_triangle r p₀₁ p₁₂ p₀₂ h]
  abel

def SingularChains.pathClass {X : Type} [TopologicalSpace X] {x y : X} (p : Path x y) :
    Opchains X :=
  chainClass X (pathChain p)

theorem SingularChains.pathClass_homotopy {X : Type} [TopologicalSpace X] {x y : X}
    {p q : Path x y} (H : p.Homotopy q) : pathClass p = pathClass q :=
  (chainClass_eq_iff X _ _).mpr ⟨correctedHomotopyChain H, boundaryTwo_correctedHomotopyChain H⟩

theorem SingularChains.pathClass_homotopic {X : Type} [TopologicalSpace X] {x y : X}
    {p q : Path x y} (h : p.Homotopic q) : pathClass p = pathClass q := by
  obtain ⟨H⟩ := h
  exact pathClass_homotopy H

@[simp]
theorem SingularChains.pathClass_refl {X : Type} [TopologicalSpace X] (x : X) :
    pathClass (Path.refl x) = 0 := by
  change chainClass X (pathChain (Path.refl x)) = 0
  rw [pathChain_refl, ← boundaryTwo_constantTriangleChain]
  exact chainClass_boundary X _

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

@[simp]
theorem SingularChains.pathClass_symm {X : Type} [TopologicalSpace X] {x y : X} (p : Path x y) :
    pathClass p.symm = -pathClass p := by
  have h := pathClass_homotopic (Path.Homotopic.trans_symm p)
  rw [pathClass_trans, pathClass_refl] at h
  exact eq_neg_of_add_eq_zero_right h

@[simp]
theorem SingularChains.pathClass_cast {X : Type} [TopologicalSpace X] {x y : X} (p : Path x y)
    {x' y' : X} (hx : x' = x) (hy : y' = y) : pathClass (p.cast hx hy) = pathClass p :=
  rfl

def SingularChains.loopCycle {X : Type} [TopologicalSpace X] {x : X} (p : Path x x) : Cycles1 X :=
  mkCycle1 X (pathChain p) (boundaryOne_loop p)

@[simp]
theorem SingularChains.loopCycle_val {X : Type} [TopologicalSpace X] {x : X} (p : Path x x) :
    (loopCycle p).1 = pathChain p :=
  rfl

def SingularChains.loopHomologyClass {X : Type} [TopologicalSpace X] {x : X} (p : Path x x) :
    SingularH1 X :=
  cycleClass X (loopCycle p)

@[simp]
theorem SingularChains.homologyToChainClass_loopHomologyClass {X : Type} [TopologicalSpace X]
    {x : X} (p : Path x x) : homologyToChainClass X (loopHomologyClass p) = pathClass p := by
  rw [loopHomologyClass, homologyToChainClass_cycleClass]
  rfl

theorem SingularChains.loopHomologyClass_homotopic {X : Type} [TopologicalSpace X] {x : X}
    {p q : Path x x} (h : p.Homotopic q) : loopHomologyClass p = loopHomologyClass q := by
  apply homologyToChainClass_injective X
  rw [homologyToChainClass_loopHomologyClass, homologyToChainClass_loopHomologyClass]
  exact pathClass_homotopic h

@[simp]
theorem SingularChains.loopHomologyClass_refl {X : Type} [TopologicalSpace X] (x : X) :
    loopHomologyClass (Path.refl x) = 0 := by
  apply homologyToChainClass_injective X
  rw [homologyToChainClass_loopHomologyClass, pathClass_refl, map_zero]

theorem SingularChains.loopHomologyClass_trans {X : Type} [TopologicalSpace X] {x : X}
    (p q : Path x x) :
    loopHomologyClass (p.trans q) = loopHomologyClass p + loopHomologyClass q := by
  apply homologyToChainClass_injective X
  rw [homologyToChainClass_loopHomologyClass, map_add, homologyToChainClass_loopHomologyClass,
    homologyToChainClass_loopHomologyClass, pathClass_trans]

def SingularChains.hurewiczFunction {X : Type} [TopologicalSpace X] (b : X) :
    FundamentalGroup X b → SingularH1 X :=
  Quotient.lift (fun p : Path b b => loopHomologyClass p)
    (fun _ _ h => loopHomologyClass_homotopic h)

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

def SingularChains.hurewiczMap {X : Type} [TopologicalSpace X] (b : X) :
    AbelianPi1 X b →ₗ[ℤ] SingularH1 X
    where
  toFun := (Abelianization.lift (hurewiczPi1 b)).toAdditiveLeft
  map_add' := (Abelianization.lift (hurewiczPi1 b)).toAdditiveLeft.map_add
  map_smul' n
    a := by
    simpa using map_intCast_smul (Abelianization.lift (hurewiczPi1 b)).toAdditiveLeft ℤ ℤ n a

@[simp]
theorem SingularChains.hurewiczMap_loopClass {X : Type} [TopologicalSpace X] (b : X)
    (p : Path b b) : hurewiczMap b (loopClass p) = loopHomologyClass p :=
  rfl

theorem SingularChains.homologyToChainClass_hurewiczMap_loopClass {X : Type} [TopologicalSpace X]
    (b : X) (p : Path b b) : homologyToChainClass X (hurewiczMap b (loopClass p)) = pathClass p :=
  by rw [hurewiczMap_loopClass, homologyToChainClass_loopHomologyClass]

theorem SingularChains.hurewiczMap_basedLoopClass {X : Type} [TopologicalSpace X] {x y : X} (b : X)
    (r : ∀ a : X, Path b a) (p : Path x y) :
    homologyToChainClass X (hurewiczMap b (basedLoopClass r p)) =
      pathClass (r x) + pathClass p - pathClass (r y) := by
  change homologyToChainClass X (hurewiczMap b (loopClass (basedLoop r p))) = _
  rw [homologyToChainClass_hurewiczMap_loopClass]
  change pathClass ((r x).trans (p.trans (r y).symm)) = _
  rw [pathClass_trans, pathClass_trans, pathClass_symm]
  abel

theorem SingularChains.basedLoopClass_cast {X : Type} [TopologicalSpace X] {b x y : X}
    (r : ∀ x : X, Path b x) (p : Path x y) {x' y' : X} (hx : x' = x) (hy : y' = y) :
    basedLoopClass r (p.cast hx hy) = basedLoopClass r p := by
  cases hx
  cases hy
  rfl

theorem SingularChains.simplexPath_pathSimplex_cast {X : Type} [TopologicalSpace X] {x y : X}
    (p : Path x y) :
    simplexPath (pathSimplex p) = p.cast (pathSimplex_vertex_zero p) (pathSimplex_vertex_one p) :=
  by
  apply Path.ext
  funext t
  change p (stdSimplexHomeomorphUnitInterval (stdSimplexHomeomorphUnitInterval.symm t)) = p t
  rw [Homeomorph.apply_symm_apply]

@[simp]
theorem SingularChains.basedLoopClass_simplexPath_pathSimplex {X : Type} [TopologicalSpace X]
    {b x y : X} (r : ∀ x : X, Path b x) (p : Path x y) :
    basedLoopClass r (simplexPath (pathSimplex p)) = basedLoopClass r p := by
  rw [simplexPath_pathSimplex_cast, basedLoopClass_cast]

def SingularChains.edgeLoopCochain {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) : Chains X 1 →ₗ[ℤ] AbelianPi1 X b :=
  chainLift X 1 (fun σ => basedLoopClass r (simplexPath σ))

@[simp]
theorem SingularChains.edgeLoopCochain_simplex {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (σ : SingularSimplex X 1) :
    edgeLoopCochain r (simplexChain X 1 σ) = basedLoopClass r (simplexPath σ) :=
  chainLift_simplex X 1 (fun σ => basedLoopClass r (simplexPath σ)) σ

@[simp]
theorem SingularChains.edgeLoopCochain_pathSimplex {X : Type} [TopologicalSpace X] {b x y : X}
    (r : ∀ x : X, Path b x) (p : Path x y) :
    edgeLoopCochain r (simplexChain X 1 (pathSimplex p)) = basedLoopClass r p := by
  rw [edgeLoopCochain_simplex, basedLoopClass_simplexPath_pathSimplex]

@[simp]
theorem SingularChains.edgeLoopCochain_loopSimplex {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (p : Path b b) :
    edgeLoopCochain r (simplexChain X 1 (pathSimplex p)) = loopClass p := by
  rw [edgeLoopCochain_pathSimplex, basedLoopClass_loop]

def SingularChains.basePathChain {X : Type} [TopologicalSpace X] {b : X} (r : ∀ x : X, Path b x) :
    Chains X 0 →ₗ[ℤ] Chains X 1 :=
  chainLift X 0 (fun σ => pathChain (r (σ (stdSimplex.vertex (S := ℝ) (0 : Fin 1)))))

@[simp]
theorem SingularChains.basePathChain_pointChain {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (x : X) : basePathChain r (pointChain x) = pathChain (r x) :=
  chainLift_simplex X 0 _ (ContinuousMap.const (Simplex 0) x)

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

theorem SingularChains.edgeClosure_chain_identity {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) :
    (homologyToChainClass X).comp ((hurewiczMap b).comp (edgeLoopCochain r)) =
      chainClass X - (chainClass X).comp ((basePathChain r).comp (boundaryOne X)) := by
  apply chainMap_ext X 1
  intro σ
  have h := edgeClosure_pathChain r (simplexPath σ)
  simpa only [pathChain, pathSimplex_simplexPath, LinearMap.comp_apply, LinearMap.sub_apply] using
    h

theorem SingularChains.edgeClosure_cycle {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (c : Cycles1 X) :
    homologyToChainClass X (hurewiczMap b (edgeLoopCochain r c.1)) = chainClass X c.1 := by
  have h := LinearMap.congr_fun (edgeClosure_chain_identity r) c.1
  change
    homologyToChainClass X (hurewiczMap b (edgeLoopCochain r c.1)) =
      chainClass X c.1 - chainClass X (basePathChain r (boundaryOne X c.1)) at h
  simpa only [cycles1_boundary, map_zero, sub_zero] using h

def SingularChains.abelianPi1EquivOfPi1 {X : Type} [TopologicalSpace X] (b : X) {A : Type*}
    [AddCommGroup A] [Module ℤ A] (e : FundamentalGroup X b ≃* Multiplicative A) :
    AbelianPi1 X b ≃ₗ[ℤ] A :=
  (e.abelianizationCongr.trans
      (Abelianization.equivOfComm (H := Multiplicative A)).symm).toAdditiveLeft.toIntLinearEquiv

@[simp]
theorem SingularChains.abelianPi1EquivOfPi1_of {X : Type} [TopologicalSpace X] (b : X) {A : Type*}
    [AddCommGroup A] [Module ℤ A] (e : FundamentalGroup X b ≃* Multiplicative A)
    (g : FundamentalGroup X b) :
    abelianPi1EquivOfPi1 b e (Additive.ofMul (Abelianization.of g)) = (e g).toAdd :=
  rfl

theorem SingularChains.pathSimplex_map {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {x y : X} (f : C(X, Y)) (p : Path x y) :
    pathSimplex (p.map f.continuous) = f.comp (pathSimplex p) :=
  rfl

@[simp]
theorem SingularChains.inducedChain_pathChain {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {x y : X} (f : C(X, Y)) (p : Path x y) :
    inducedChain f 1 (pathChain p) = pathChain (p.map f.continuous) := by
  simp only [pathChain, inducedChain_simplex, pathSimplex_map]

@[simp]
theorem SingularChains.inducedCycles_loopCycle {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (b : X) (p : Path b b) :
    inducedCycles f (loopCycle p) = loopCycle (p.map f.continuous) := by
  apply Subtype.ext
  rw [inducedCycles_val, loopCycle_val, loopCycle_val, inducedChain_pathChain]

@[simp]
theorem SingularChains.inducedHomology_loopHomologyClass {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (b : X) (p : Path b b) :
    inducedHomology f (loopHomologyClass p) = loopHomologyClass (p.map f.continuous) := by
  rw [loopHomologyClass, inducedHomology_cycleClass, inducedCycles_loopCycle]
  rfl
end Mathoverflow1973
