/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
/-!
# The two-open transition structure

  Two-open transitions: the change-of-chart data of a bundle trivialized over
  two open sets - sets, index map, and the cocycle condition - the atlas-level
  precursor of the mapping torus (Hatcher, Algebraic Topology, Example 1.46).
-/



open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-! ### Two-chart transition data -/

/-- A two-open cover of `X` together with a `G`-valued transition function continuous on the overlap. -/
structure TwoOpenTransition (X G : Type*) [TopologicalSpace X] [TopologicalSpace G] where
  U : TopologicalSpace.Opens X
  V : TopologicalSpace.Opens X
  cover : (U : Set X) ∪ (V : Set X) = Set.univ
  transition : X → G
  continuousOn_transition : ContinuousOn transition ((U : Set X) ∩ (V : Set X))

/-- The `Bool`-indexed family naming the two cover sets. -/
def TwoOpenTransition.baseSet {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) : Bool → Set X
  | false => D.U
  | true => D.V

/-- Index `false` selects `U`. -/
@[simp]
theorem TwoOpenTransition.baseSet_false {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) : D.baseSet Bool.false = (D.U : Set X) :=
  rfl

/-- Index `true` selects `V`. -/
@[simp]
theorem TwoOpenTransition.baseSet_true {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) : D.baseSet Bool.true = (D.V : Set X) :=
  rfl

/-- The index of a cover set containing `x`, preferring `U`. -/
def TwoOpenTransition.indexAt {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) (x : X) : Bool := by
  classical exact if x ∈ D.U then Bool.false else Bool.true

/-- Points of `U` select index `false`. -/
@[simp]
theorem TwoOpenTransition.indexAt_of_mem_U {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) {x : X} (hx : x ∈ D.U) : D.indexAt x = Bool.false := by
  simp [indexAt, hx]

/-- Points outside `U` select index `true`. -/
@[simp]
theorem TwoOpenTransition.indexAt_of_not_mem_U {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] (D : TwoOpenTransition X G) {x : X} (hx : x ∉ D.U) :
    D.indexAt x = Bool.true := by simp [indexAt, hx]

/-- A point lies in its selected cover set. -/
theorem TwoOpenTransition.mem_baseSet_indexAt {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] (D : TwoOpenTransition X G) (x : X) : x ∈ D.baseSet (D.indexAt x) := by
  by_cases hx : x ∈ D.U
  · simpa only [D.indexAt_of_mem_U hx, baseSet_false, SetLike.mem_coe] using hx
  · have hcover : x ∈ (D.U : Set X) ∪ (D.V : Set X) := by
      rw [D.cover]
      exact Set.mem_univ x
    simpa only [D.indexAt_of_not_mem_U hx, baseSet_true] using hcover.resolve_left hx

/-- The coordinate change between the two trivializations by the transition function. -/
def TwoOpenTransition.coordChange {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) [Group G] : Bool → Bool → X → G → G
  | false, Bool.false, _, w => w
  | false, Bool.true, x, w => w * D.transition x
  | true, Bool.false, x, w => w * (D.transition x)⁻¹
  | true, Bool.true, _, w => w

/-- The diagonal coordinate change is the identity. -/
@[simp]
theorem TwoOpenTransition.coordChange_self {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) [Group G] (i : Bool) (x : X) (w : G) :
    D.coordChange i i x w = w := by cases i <;> rfl

/-- Coordinate changes compose through a third trivialization. -/
theorem TwoOpenTransition.coordChange_comp {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) [Group G] (i j k : Bool) (x : X) (w : G) :
    D.coordChange j k x (D.coordChange i j x w) = D.coordChange i k x w := by
  cases i <;> cases j <;> cases k <;> simp [coordChange, mul_assoc]

/-- Coordinate changes commute with left multiplication. -/
theorem TwoOpenTransition.coordChange_mul_left {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] (D : TwoOpenTransition X G) [Group G] (i j : Bool) (x : X) (g w : G) :
    D.coordChange i j x (g * w) = g * D.coordChange i j x w := by
  cases i <;> cases j <;> simp [coordChange, mul_assoc]

/-- Coordinate changes are continuous on the overlap, using discreteness of `G`. -/
theorem TwoOpenTransition.continuousOn_coordChange {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] (D : TwoOpenTransition X G) [Group G] [DiscreteTopology G] (i j : Bool) :
    ContinuousOn (fun p : X × G => D.coordChange i j p.1 p.2)
      ((D.baseSet i ∩ D.baseSet j) ×ˢ Set.univ) := by
  cases i <;> cases j
  · exact continuous_snd.continuousOn
  · exact
      continuous_snd.continuousOn.mul
        (D.continuousOn_transition.comp continuous_fst.continuousOn (fun _ hp => hp.1))
  · exact
      continuous_snd.continuousOn.mul
        (D.continuousOn_transition.comp continuous_fst.continuousOn
            (fun _ hp => ⟨hp.1.2, hp.1.1⟩)).inv
  · exact continuous_snd.continuousOn

/-! ### The associated fiber bundle -/

/-- The fiber-bundle core assembled from the two-chart transition data. -/
def TwoOpenTransition.core {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) [Group G] [DiscreteTopology G] : FiberBundleCore Bool X G
    where
  baseSet := D.baseSet
  isOpen_baseSet := by
    intro i
    cases i
    · exact D.U.isOpen
    · exact D.V.isOpen
  indexAt := D.indexAt
  mem_baseSet_at := D.mem_baseSet_indexAt
  coordChange := D.coordChange
  coordChange_self := fun i x _ w => D.coordChange_self i x w
  continuousOn_coordChange := D.continuousOn_coordChange
  coordChange_comp := fun i j k x _ w => D.coordChange_comp i j k x w

/-- The total space of the bundle built from the transition data. -/
abbrev TwoOpenTransition.TotalSpace {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) [Group G] [DiscreteTopology G] :=
  D.core.TotalSpace

/-- The bundle projection to the base. -/
abbrev TwoOpenTransition.proj {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) [Group G] [DiscreteTopology G] : D.TotalSpace → X :=
  D.core.proj

/-- The trivialization over `U`. -/
abbrev TwoOpenTransition.localTrivU {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) [Group G] [DiscreteTopology G] : Bundle.Trivialization G D.proj :=
  D.core.localTriv Bool.false

/-- The trivialization over `V`. -/
abbrev TwoOpenTransition.localTrivV {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) [Group G] [DiscreteTopology G] : Bundle.Trivialization G D.proj :=
  D.core.localTriv Bool.true

/-- The point of the total space over `x` with `U`-coordinate `g`. -/
def TwoOpenTransition.pointU {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) [Group G] [DiscreteTopology G] (x : X) (g : G) : D.TotalSpace :=
  D.localTrivU.toOpenPartialHomeomorph.symm (x, g)

/-- The point of the total space over `x` with `V`-coordinate `g`. -/
def TwoOpenTransition.pointV {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) [Group G] [DiscreteTopology G] (x : X) (g : G) : D.TotalSpace :=
  D.localTrivV.toOpenPartialHomeomorph.symm (x, g)

/-- The `U`-coordinate point lies over `x`. -/
@[simp]
theorem TwoOpenTransition.proj_pointU {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) [Group G] [DiscreteTopology G] (x : X) (g : G) :
    D.proj (D.pointU x g) = x :=
  rfl

/-- The `V`-coordinate point lies over `x`. -/
@[simp]
theorem TwoOpenTransition.proj_pointV {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) [Group G] [DiscreteTopology G] (x : X) (g : G) :
    D.proj (D.pointV x g) = x :=
  rfl

/-- On the overlap the two coordinates differ by the transition function. -/
theorem TwoOpenTransition.pointU_eq_pointV {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) [Group G] [DiscreteTopology G] (x : X) (g : G)
    (hx : x ∈ (D.U : Set X) ∩ (D.V : Set X)) : D.pointU x g = D.pointV x (g * D.transition x) := by
  change
    (⟨x, D.core.coordChange Bool.false (D.core.indexAt x) x g⟩ : D.TotalSpace) =
      ⟨x, D.core.coordChange Bool.true (D.core.indexAt x) x (g * D.transition x)⟩
  apply congrArg (fun w : G => (⟨x, w⟩ : D.TotalSpace))
  exact
    (D.core.coordChange_comp Bool.false Bool.true (D.core.indexAt x) x
        ⟨⟨hx.1, hx.2⟩, D.core.mem_baseSet_at x⟩ g).symm

/-- The projection of a discrete-fibre two-chart bundle is a covering map. -/
theorem TwoOpenTransition.isCoveringMap {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (D : TwoOpenTransition X G) [Group G] [DiscreteTopology G] : IsCoveringMap D.proj := by
  exact FiberBundle.isCoveringMap (F := G) (E := D.core.Fiber)

/-! ### The group action on the total space -/

/-- Left multiplication on the fibre lifts to a `G`-action on the total space. -/
instance TwoOpenTransition.totalMulAction {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G) : MulAction G D.TotalSpace
    where
  smul g p := ⟨p.proj, g * (show G from p.2)⟩
  one_smul
    p := by
    rcases p with ⟨b, v⟩
    change G at v
    change (⟨b, 1 * v⟩ : D.TotalSpace) = ⟨b, v⟩
    exact congrArg (fun w : G => (⟨b, w⟩ : D.TotalSpace)) (one_mul v)
  mul_smul g h
    p := by
    rcases p with ⟨b, v⟩
    change G at v
    change (⟨b, (g * h) * v⟩ : D.TotalSpace) = ⟨b, g * (h * v)⟩
    exact congrArg (fun w : G => (⟨b, w⟩ : D.TotalSpace)) (mul_assoc g h v)

/-- The `G`-action is left multiplication in each trivialization. -/
theorem TwoOpenTransition.localTriv_smul {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G) (i : Bool) (g : G)
    (p : D.TotalSpace) : D.core.localTriv i (g • p) = (D.proj p, g * (D.core.localTriv i p).2) := by
  apply Prod.ext
  · rfl
  exact D.coordChange_mul_left _ _ _ _ _

/-- The group action scales the `U`-coordinate. -/
@[simp]
theorem TwoOpenTransition.smul_pointU {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G) (g : G) (x : X) (w : G) :
    g • D.pointU x w = D.pointU x (g * w) := by
  change
    (⟨x, g * D.coordChange Bool.false (D.indexAt x) x w⟩ : D.TotalSpace) =
      ⟨x, D.coordChange Bool.false (D.indexAt x) x (g * w)⟩
  exact
    congrArg (fun v : G => (⟨x, v⟩ : D.TotalSpace))
      (D.coordChange_mul_left Bool.false (D.indexAt x) x g w).symm

/-- The `G`-action on the total space is continuous in each element. -/
instance TwoOpenTransition.totalContinuousConstSMul {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G) :
    ContinuousConstSMul G D.TotalSpace where
  continuous_const_smul
    g := by
    apply continuous_iff_continuousAt.mpr
    intro p
    let e := D.core.localTriv (D.core.indexAt p.proj)
    have he : D.proj p ∈ e.baseSet := D.core.mem_baseSet_at p.proj
    have hecont : ContinuousAt e p := e.continuousAt (e.mem_source.mpr he)
    apply
      e.continuousAt_of_comp_left
        (show ContinuousAt (D.proj ∘ (g • ·)) p from D.core.continuous_proj.continuousAt) he
    convert
      D.core.continuous_proj.continuousAt.prodMk
        ((show ContinuousAt (fun _ : D.TotalSpace => g) p from continuousAt_const).mul
          hecont.snd) using
      1
    funext q
    exact D.localTriv_smul _ _ _

/-- The `G`-action on the total space is cancellative. -/
instance TwoOpenTransition.totalIsCancelSMul {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G) :
    IsCancelSMul G D.TotalSpace where
  right_cancel' g h p
    he := by
    have he' := congrArg (fun q : D.TotalSpace => (q.2 : G)) he
    exact mul_right_cancel he'

/-- Two points share a projection exactly when they lie in one orbit. -/
theorem TwoOpenTransition.proj_eq_iff_mem_orbit {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G)
    {p q : D.TotalSpace} : D.proj p = D.proj q ↔ p ∈ MulAction.orbit G q := by
  constructor
  · cases p with
    | mk b w =>
      cases q with
      | mk c v =>
        change G at w v
        intro h
        change b = c at h
        subst c
        refine ⟨w * v⁻¹, ?_⟩
        change (⟨b, (w * v⁻¹) * v⟩ : D.TotalSpace) = ⟨b, w⟩
        exact congrArg (fun z : G => (⟨b, z⟩ : D.TotalSpace)) (inv_mul_cancel_right w v)
  · rintro ⟨g, rfl⟩
    rfl

/-- The projection is the quotient covering by the `G`-action. -/
theorem TwoOpenTransition.isQuotientCoveringMap {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G) :
    IsQuotientCoveringMap D.proj G := by
  apply (isQuotientCoveringMap_iff_isCoveringMap_and D.proj G).mpr
  exact
    ⟨D.isCoveringMap, fun x => ⟨D.pointU x 1, D.proj_pointU x 1⟩, inferInstance, inferInstance,
      D.proj_eq_iff_mem_orbit⟩

private def TwoOpenTransition.chartPath {E X F : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [TopologicalSpace F] {p : E → X} (e : Bundle.Trivialization F p)
    {b c : X} (γ : Path b c) (hγ : ∀ s, γ s ∈ e.baseSet) (v : F) :
    Path (e.toOpenPartialHomeomorph.symm (b, v)) (e.toOpenPartialHomeomorph.symm (c, v))
    where
  toFun s := e.toOpenPartialHomeomorph.symm (γ s, v)
  continuous_toFun := e.continuousOn_symm_prodMk_left.comp_continuous γ.continuous hγ
  source' := by simp
  target' := by simp

private theorem TwoOpenTransition.chartPath_monodromy {E X F : Type*}
    [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace F] {p : E → X}
    (hp : IsCoveringMap p) (e : Bundle.Trivialization F p) {b c : X} (γ : Path b c)
    (hγ : ∀ s, γ s ∈ e.baseSet) (hb : b ∈ e.baseSet) (hc : c ∈ e.baseSet) (v : F) :
    hp.monodromy (.mk γ) ⟨e.toOpenPartialHomeomorph.symm (b, v), e.proj_symm_apply' hb⟩ =
      ⟨e.toOpenPartialHomeomorph.symm (c, v), e.proj_symm_apply' hc⟩ := by
  apply hp.monodromy_eq_of_map_eq (.mk (chartPath e γ hγ v))
  apply congrArg Path.Homotopic.Quotient.mk
  ext s
  exact e.proj_symm_apply' (hγ s)

/-! ### Monodromy through the two charts -/

/-- The fibre point over `b` with `U`-coordinate `g`. -/
def TwoOpenTransition.fiberPointU {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G) (b : X) (g : G) :
    D.proj ⁻¹' { b } :=
  ⟨D.pointU b g, D.proj_pointU b g⟩

/-- The fibre point over `b` with `V`-coordinate `g`. -/
def TwoOpenTransition.fiberPointV {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G) (b : X) (g : G) :
    D.proj ⁻¹' { b } :=
  ⟨D.pointV b g, D.proj_pointV b g⟩

/-- The fibre point coerces to the `U`-coordinate point. -/
@[simp]
theorem TwoOpenTransition.fiberPointU_val {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G) (b : X) (g : G) :
    (D.fiberPointU b g : D.TotalSpace) = D.pointU b g :=
  rfl

/-- On the overlap a `V`-coordinate point equals a rescaled `U`-coordinate point. -/
theorem TwoOpenTransition.pointV_eq_pointU {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G) (b : X) (g : G)
    (hb : b ∈ (D.U : Set X) ∩ (D.V : Set X)) :
    D.pointV b g = D.pointU b (g * (D.transition b)⁻¹) := by
  simpa only [inv_mul_cancel_right] using (D.pointU_eq_pointV b (g * (D.transition b)⁻¹) hb).symm

/-- The two fibre coordinates differ by the transition function. -/
theorem TwoOpenTransition.fiberPointU_eq_fiberPointV {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G) (b : X)
    (g : G) (hb : b ∈ (D.U : Set X) ∩ (D.V : Set X)) :
    D.fiberPointU b g = D.fiberPointV b (g * D.transition b) :=
  Subtype.ext (D.pointU_eq_pointV b g hb)

/-- The two fibre coordinates differ by the inverse transition function. -/
theorem TwoOpenTransition.fiberPointV_eq_fiberPointU {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G) (b : X)
    (g : G) (hb : b ∈ (D.U : Set X) ∩ (D.V : Set X)) :
    D.fiberPointV b g = D.fiberPointU b (g * (D.transition b)⁻¹) :=
  Subtype.ext (D.pointV_eq_pointU b g hb)

/-- Monodromy along a path inside `U` preserves the `U`-coordinate. -/
theorem TwoOpenTransition.monodromy_of_path_U {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G) {b c : X}
    (α : Path b c) (hα : ∀ s, α s ∈ D.U) (g : G) :
    D.isCoveringMap.monodromy (.mk α) (D.fiberPointU b g) = D.fiberPointU c g := by
  have hbase : D.localTrivU.baseSet = D.U := rfl
  exact
    chartPath_monodromy D.isCoveringMap D.localTrivU α hα
      (by simpa [hbase] using hα 0) (by simpa [hbase] using hα 1) g

/-- Monodromy along a path inside `V` preserves the `V`-coordinate. -/
theorem TwoOpenTransition.monodromy_of_path_V {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G) {b c : X}
    (β : Path b c) (hβ : ∀ s, β s ∈ D.V) (g : G) :
    D.isCoveringMap.monodromy (.mk β) (D.fiberPointV b g) = D.fiberPointV c g := by
  have hbase : D.localTrivV.baseSet = D.V := rfl
  exact
    chartPath_monodromy D.isCoveringMap D.localTrivV β hβ
      (by simpa [hbase] using hβ 0) (by simpa [hbase] using hβ 1) g

/-- Monodromy around a `U`-then-`V` loop applies the transition function. -/
theorem TwoOpenTransition.monodromy_trans_U_V {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G) {b c : X}
    (hb : b ∈ (D.U : Set X) ∩ (D.V : Set X)) (hc : c ∈ (D.U : Set X) ∩ (D.V : Set X))
    (α : Path b c) (β : Path c b) (hα : ∀ s, α s ∈ D.U) (hβ : ∀ s, β s ∈ D.V) (g : G) :
    D.isCoveringMap.monodromy (.mk (α.trans β)) (D.fiberPointU b g) =
      D.fiberPointU b ((g * D.transition c) * (D.transition b)⁻¹) := by
  rw [Path.Homotopic.Quotient.mk_trans, D.isCoveringMap.monodromy_trans_apply,
    D.monodromy_of_path_U α hα g, D.fiberPointU_eq_fiberPointV c g hc, D.monodromy_of_path_V β hβ,
    D.fiberPointV_eq_fiberPointU b _ hb]

/-- The fibre basepoint over `b` with trivial `U`-coordinate. -/
def TwoOpenTransition.basepointU {X G : Type*} [TopologicalSpace X] [TopologicalSpace G] [Group G]
    [DiscreteTopology G] (D : TwoOpenTransition X G) (b : X) (hb : b ∈ D.U) : D.proj ⁻¹' { b } :=
  ⟨D.pointU b 1, D.localTrivU.proj_symm_apply' hb⟩

/-- The fibre basepoint is the unit `U`-coordinate point. -/
@[simp]
theorem TwoOpenTransition.basepointU_eq_fiberPointU {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G) (b : X)
    (hb : b ∈ D.U) : D.basepointU b hb = D.fiberPointU b 1 :=
  rfl

/-- Monodromy gives a homomorphism from the fundamental group to `Gᵐᵒᵖ`. -/
def TwoOpenTransition.fundamentalGroupToMulOpposite {X G : Type*} [TopologicalSpace X]
    [TopologicalSpace G] [Group G] [DiscreteTopology G] (D : TwoOpenTransition X G) (b : X)
    (hb : b ∈ D.U) : FundamentalGroup X b →* Gᵐᵒᵖ :=
  D.isQuotientCoveringMap.fundamentalGroupToMulOpposite (D.basepointU b hb)

/-- The monodromy homomorphism computes the transition function on `U`-then-`V` loops. -/
theorem TwoOpenTransition.fundamentalGroupToMulOpposite_trans_U_V {X G : Type*}
    [TopologicalSpace X] [TopologicalSpace G] [Group G] [DiscreteTopology G]
    (D : TwoOpenTransition X G) {b c : X} (hb : b ∈ (D.U : Set X) ∩ (D.V : Set X))
    (hc : c ∈ (D.U : Set X) ∩ (D.V : Set X)) (α : Path b c) (β : Path c b) (hα : ∀ s, α s ∈ D.U)
    (hβ : ∀ s, β s ∈ D.V) :
    D.fundamentalGroupToMulOpposite b hb.1 (.mk (α.trans β)) =
      MulOpposite.op (D.transition c * (D.transition b)⁻¹) := by
  apply (D.isQuotientCoveringMap.fundamentalGroupToMulOpposite_apply_eq_Iff).mpr
  have hm := congrArg Subtype.val (D.monodromy_trans_U_V hb hc α β hα hβ 1)
  simpa only [MulOpposite.unop_op, basepointU_eq_fiberPointU, smul_pointU, mul_one, one_mul,
    fiberPointU_val] using hm.symm
