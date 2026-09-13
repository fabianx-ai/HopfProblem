/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.Handle
public import Lib.Analysis.Calculus.MorseLemma
public import Lib.Geometry.Manifold.Morse.SublevelSets
public import Lib.Geometry.Manifold.Morse.Index
public import Lib.Geometry.Manifold.Flow.HeightTranslating
public import Lib.AlgebraicTopology.SingularHomology.Chains
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
public import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Lib.Topology.Homotopy.HandleRetraction
public import Lib.AlgebraicTopology.SingularHomology.SphereHomology
/-!
# The homotopy extension property for cylinders

  The homotopy extension property for product cylinders `I x X`: homotopies of
  `X` extend over the cylinder, with the gluing used for deformation retractions
  (Hatcher, Algebraic Topology, Proposition 0.16-adjacent).
-/



set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

@[expose] public noncomputable section

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-! ### The cylinder-to-ball homeomorphism -/

/-- The boundary `I × S ∪ {0,1} × D` of the cylinder ball. -/
def CylinderBall.boundary {V : Type*} [NormedAddCommGroup V] :
    Set ((unitInterval) × DiskCylinder.Disk (E := V)) :=
  {p | p.1 = 0 ∨ p.1 = 1 ∨ ‖(p.2 : V)‖ = 1}

/-- The rescaled time coordinate has norm at most one. -/
theorem CylinderBall.time_norm_le (t : (unitInterval)) : ‖(2 * t.val - 1 : ℝ)‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [t.property.1, t.property.2]

/-- The forward map from the cylinder to the ball. -/
def CylinderBall.forward {V : Type*} [NormedAddCommGroup V] :
    C((unitInterval) × DiskCylinder.Disk (E := V), DiskCylinder.Disk (E := ℝ × V))
    where
  toFun
    p :=
    ⟨(2 * p.1.val - 1, p.2.val),
      mem_closedBall_zero_iff.mpr
        (max_le (time_norm_le p.1) (mem_closedBall_zero_iff.mp p.2.property))⟩
  continuous_toFun :=
    (((continuous_const.mul (continuous_subtype_val.comp continuous_fst)).sub
              continuous_const).prodMk
          (continuous_subtype_val.comp continuous_snd)).subtype_mk
      _

/-- The time coordinate of a ball point under the inverse. -/
def CylinderBall.inverseTime {V : Type*} [NormedAddCommGroup V]
    (z : DiskCylinder.Disk (E := ℝ × V)) : (unitInterval) :=
  ⟨(z.val.1 + 1) / 2,
    by
    have hn : |z.val.1| ≤ 1 := (max_le_iff.mp (mem_closedBall_zero_iff.mp z.property)).1
    rcases abs_le.mp hn with ⟨hl, hu⟩
    constructor <;> linarith⟩

/-- The space coordinate of a ball point under the inverse. -/
def CylinderBall.inverseSpace {V : Type*} [NormedAddCommGroup V]
    (z : DiskCylinder.Disk (E := ℝ × V)) : DiskCylinder.Disk (E := V) :=
  ⟨z.val.2,
    mem_closedBall_zero_iff.mpr ((max_le_iff.mp (mem_closedBall_zero_iff.mp z.property)).2)⟩

/-- The inverse map from the ball to the cylinder. -/
def CylinderBall.inverse {V : Type*} [NormedAddCommGroup V] :
    C(DiskCylinder.Disk (E := ℝ × V), (unitInterval) × DiskCylinder.Disk (E := V))
    where
  toFun z := (inverseTime z, inverseSpace z)
  continuous_toFun := by
    have ht : Continuous (fun z : DiskCylinder.Disk (E := ℝ × V) => (z.val.1 + 1) / 2) := by
      fun_prop
    exact (ht.subtype_mk _).prodMk ((continuous_snd.comp continuous_subtype_val).subtype_mk _)

/-- The cylinder `I × D` is homeomorphic to the ball. -/
def CylinderBall.homeomorph {V : Type*} [NormedAddCommGroup V] :
    ((unitInterval) × DiskCylinder.Disk (E := V)) ≃ₜ DiskCylinder.Disk (E := ℝ × V)
    where
  toFun := forward
  invFun := inverse
  left_inv
    p := by
    apply Prod.ext
    · apply Subtype.ext
      change ((2 * p.1.val - 1) + 1) / 2 = p.1.val
      ring
    · rfl
  right_inv
    z := by
    apply Subtype.ext
    apply Prod.ext
    · change 2 * ((z.val.1 + 1) / 2) - 1 = z.val.1
      ring
    · rfl
  continuous_toFun := forward.continuous
  continuous_invFun := inverse.continuous

/-- A ball point has norm one exactly on the cylinder boundary. -/
theorem CylinderBall.norm_eq_one_iff {V : Type*} [NormedAddCommGroup V]
    (p : (unitInterval) × DiskCylinder.Disk (E := V)) :
    ‖((homeomorph (V := V) p).val)‖ = 1 ↔ p ∈ boundary := by
  change Max.max ‖(2 * p.1.val - 1 : ℝ)‖ ‖p.2.val‖ = 1 ↔ _
  constructor
  · intro he
    rcases le_total ‖(2 * p.1.val - 1 : ℝ)‖ ‖p.2.val‖ with h | h
    · exact Or.inr (Or.inr (by rwa [max_eq_right h] at he))
    · rw [max_eq_left h, Real.norm_eq_abs] at he
      have he' : |2 * p.1.val - 1| = |(1 : ℝ)| := by simpa using he
      rcases abs_eq_abs.mp he' with h | h
      · exact Or.inr (Or.inl (Subtype.ext (show p.1.val = (1 : ℝ) by linarith)))
      · exact Or.inl (Subtype.ext (show p.1.val = (0 : ℝ) by linarith))
  · rintro (h | h | h)
    · have ht : p.1.val = 0 := congrArg Subtype.val h
      rw [ht]
      norm_num
      exact mem_closedBall_zero_iff.mp p.2.property
    · have ht : p.1.val = 1 := congrArg Subtype.val h
      rw [ht]
      norm_num
      exact mem_closedBall_zero_iff.mp p.2.property
    · rw [h, max_eq_right (time_norm_le p.1)]

/-- The ball sphere is homeomorphic to the cylinder boundary. -/
def CylinderBall.diskSphereHomeomorph {V : Type*} [NormedAddCommGroup V] :
    { z : DiskCylinder.Disk (E := V) // ‖(z : V)‖ = 1 } ≃ₜ
      DiskCylinder.Sphere (E := V)
    where
  toFun z := ⟨z.val.val, mem_sphere_zero_iff_norm.mpr z.property⟩
  invFun s := ⟨DiskCylinder.boundaryToDisk s, mem_sphere_zero_iff_norm.mp s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := DiskCylinder.boundaryToDisk.continuous.subtype_mk _

/-- The cylinder boundary is homeomorphic to the ball sphere. -/
def CylinderBall.boundaryHomeomorph {V : Type*} [NormedAddCommGroup V] :
    boundary (V := V) ≃ₜ DiskCylinder.Sphere (E := ℝ × V) :=
  ((homeomorph (V := V)).subtype (fun p => (norm_eq_one_iff p).symm)).trans diskSphereHomeomorph

/-! ### Gluing maps on the cylinder boundary -/

/-- The bottom-and-side inclusion into the boundary quotient. -/
def CylinderBoundary.lower {V : Type*} [NormedAddCommGroup V] :
    C(DiskCylinder.bottomOrSide (E := V), CylinderBall.boundary (V := V)) :=
  ⟨fun p => ⟨p.val, p.property.elim Or.inl (fun h => Or.inr (Or.inr h))⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- The top disk inclusion into the boundary quotient. -/
def CylinderBoundary.top {V : Type*} [NormedAddCommGroup V] :
    C(DiskCylinder.Disk (E := V), CylinderBall.boundary (V := V)) :=
  ⟨fun z => ⟨(1, z), Or.inr (Or.inl rfl)⟩, (continuous_const.prodMk continuous_id).subtype_mk _⟩

/-- The quotient map of the cylinder boundary. -/
def CylinderBoundary.quotient {V : Type*} [NormedAddCommGroup V] :
    C(DiskCylinder.bottomOrSide (E := V) ⊕ DiskCylinder.Disk (E := V),
      CylinderBall.boundary (V := V)) :=
  ⟨Sum.elim CylinderBoundary.lower top,
    CylinderBoundary.lower.continuous.sumElim top.continuous⟩

/-- The boundary quotient map is surjective. -/
theorem CylinderBoundary.quotient_surjective {V : Type*} [NormedAddCommGroup V] :
    Function.Surjective (quotient (V := V)) := by
  rintro ⟨⟨t, z⟩, ht | ht | hz⟩
  · exact ⟨.inl ⟨(t, z), Or.inl ht⟩, rfl⟩
  · change t = 1 at ht
    subst t
    exact ⟨.inr z, rfl⟩
  · exact ⟨.inl ⟨(t, z), Or.inr hz⟩, rfl⟩

/-- The boundary quotient map is a quotient map. -/
theorem CylinderBoundary.quotient_isQuotientMap {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] : Topology.IsQuotientMap (quotient (V := V)) := by
  have hclosed : IsClosed (DiskCylinder.bottomOrSide (E := V)) :=
    (isClosed_eq continuous_fst continuous_const).union
      (isClosed_eq (continuous_subtype_val.comp continuous_snd).norm continuous_const)
  let : CompactSpace (DiskCylinder.bottomOrSide (E := V)) :=
    isCompact_iff_compactSpace.mp hclosed.isCompact
  exact .of_surjective_continuous quotient_surjective quotient.continuous

/-- Bottom and top maps agreeing on the sphere descend to the quotient. -/
theorem CylinderBoundary.lower_top_compat {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] {X : Type*} [TopologicalSpace X]
    (f g : C(DiskCylinder.Disk (E := V), X))
    (H : C((unitInterval) × DiskCylinder.Sphere (E := V), X))
    (h0 : ∀ s, H (0, s) = f (DiskCylinder.boundaryToDisk s))
    (h1 : ∀ s, H (1, s) = g (DiskCylinder.boundaryToDisk s))
    (a : DiskCylinder.bottomOrSide (E := V)) (b : DiskCylinder.Disk (E := V))
    (he : CylinderBoundary.lower a = top b) :
    DiskCylinder.gluedBottomSide f H h0 a = g b := by
  have ht : a.val.1 = (1 : (unitInterval)) :=
    congrArg (fun p : CylinderBall.boundary (V := V) => p.val.1) he
  have hz : a.val.2 = b := congrArg (fun p : CylinderBall.boundary (V := V) => p.val.2) he
  have hs : ‖(a.val.2 : V)‖ = 1 := by
    rcases a.property with h | h
    · exact False.elim (zero_ne_one (h.symm.trans ht))
    · exact h
  let s : DiskCylinder.Sphere (E := V) := ⟨a.val.2.val, mem_sphere_zero_iff_norm.mpr hs⟩
  have ha : a = DiskCylinder.sideMap (1, s) := Subtype.ext (Prod.ext ht rfl)
  rw [ha, DiskCylinder.gluedBottomSide_side]
  exact (h1 s).trans (congrArg g hz)

/-- The boundary quotient data gluing bottom/side and top maps. -/
def CylinderBoundary.data {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {X : Type*} [TopologicalSpace X]
    (f g : C(DiskCylinder.Disk (E := V), X))
    (H : C((unitInterval) × DiskCylinder.Sphere (E := V), X))
    (h0 : ∀ s, H (0, s) = f (DiskCylinder.boundaryToDisk s)) :
    C(DiskCylinder.bottomOrSide (E := V) ⊕ DiskCylinder.Disk (E := V), X) :=
  ⟨Sum.elim (DiskCylinder.gluedBottomSide f H h0) g,
    (DiskCylinder.gluedBottomSide f H h0).continuous.sumElim g.continuous⟩

/-- The glued data is constant on quotient fibers. -/
theorem CylinderBoundary.data_constant_on_fibres {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] {X : Type*} [TopologicalSpace X]
    (f g : C(DiskCylinder.Disk (E := V), X))
    (H : C((unitInterval) × DiskCylinder.Sphere (E := V), X))
    (h0 : ∀ s, H (0, s) = f (DiskCylinder.boundaryToDisk s))
    (h1 : ∀ s, H (1, s) = g (DiskCylinder.boundaryToDisk s))
    (a b : DiskCylinder.bottomOrSide (E := V) ⊕ DiskCylinder.Disk (E := V))
    (he : quotient a = quotient b) : data f g H h0 a = data f g H h0 b := by
  cases a with
  | inl a =>
    cases b with
    | inl
      b =>
      have hv : a.val = b.val :=
        congrArg (fun p : CylinderBall.boundary (V := V) => p.val) he
      exact congrArg (DiskCylinder.gluedBottomSide f H h0) (Subtype.ext hv)
    | inr b => exact lower_top_compat f g H h0 h1 a b he
  | inr a =>
    cases b with
    | inl b => exact (lower_top_compat f g H h0 h1 b a he.symm).symm
    | inr b =>
      exact congrArg g (congrArg (fun p : CylinderBall.boundary (V := V) => p.val.2) he)

/-- The map glued from the boundary pieces. -/
def CylinderBoundary.glued {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {X : Type*} [TopologicalSpace X]
    (f g : C(DiskCylinder.Disk (E := V), X))
    (H : C((unitInterval) × DiskCylinder.Sphere (E := V), X))
    (h0 : ∀ s, H (0, s) = f (DiskCylinder.boundaryToDisk s))
    (h1 : ∀ s, H (1, s) = g (DiskCylinder.boundaryToDisk s)) :
    C(CylinderBall.boundary (V := V), X) :=
  quotient_isQuotientMap.lift (data f g H h0) (data_constant_on_fibres f g H h0 h1)

/-- The glued map on the bottom and side. -/
theorem CylinderBoundary.glued_lower {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {X : Type*} [TopologicalSpace X]
    (f g : C(DiskCylinder.Disk (E := V), X))
    (H : C((unitInterval) × DiskCylinder.Sphere (E := V), X))
    (h0 : ∀ s, H (0, s) = f (DiskCylinder.boundaryToDisk s))
    (h1 : ∀ s, H (1, s) = g (DiskCylinder.boundaryToDisk s))
    (a : DiskCylinder.bottomOrSide (E := V)) :
    glued f g H h0 h1 (CylinderBoundary.lower a) =
      DiskCylinder.gluedBottomSide f H h0 a :=
  ContinuousMap.congr_fun
    (quotient_isQuotientMap.lift_comp (data f g H h0) (data_constant_on_fibres f g H h0 h1))
    (.inl a)

/-- The glued map on the top. -/
theorem CylinderBoundary.glued_top {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {X : Type*} [TopologicalSpace X]
    (f g : C(DiskCylinder.Disk (E := V), X))
    (H : C((unitInterval) × DiskCylinder.Sphere (E := V), X))
    (h0 : ∀ s, H (0, s) = f (DiskCylinder.boundaryToDisk s))
    (h1 : ∀ s, H (1, s) = g (DiskCylinder.boundaryToDisk s))
    (z : DiskCylinder.Disk (E := V)) : glued f g H h0 h1 (top z) = g z :=
  ContinuousMap.congr_fun
    (quotient_isQuotientMap.lift_comp (data f g H h0) (data_constant_on_fibres f g H h0 h1))
    (.inr z)

/-- The glued map on the bottom disk. -/
theorem CylinderBoundary.glued_bottom {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {X : Type*} [TopologicalSpace X]
    (f g : C(DiskCylinder.Disk (E := V), X))
    (H : C((unitInterval) × DiskCylinder.Sphere (E := V), X))
    (h0 : ∀ s, H (0, s) = f (DiskCylinder.boundaryToDisk s))
    (h1 : ∀ s, H (1, s) = g (DiskCylinder.boundaryToDisk s))
    (z : DiskCylinder.Disk (E := V)) :
    glued f g H h0 h1 (CylinderBoundary.lower (DiskCylinder.bottomMap z)) = f z := by
  rw [glued_lower, DiskCylinder.gluedBottomSide_bottom]

/-- The glued map on the side. -/
theorem CylinderBoundary.glued_side {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {X : Type*} [TopologicalSpace X]
    (f g : C(DiskCylinder.Disk (E := V), X))
    (H : C((unitInterval) × DiskCylinder.Sphere (E := V), X))
    (h0 : ∀ s, H (0, s) = f (DiskCylinder.boundaryToDisk s))
    (h1 : ∀ s, H (1, s) = g (DiskCylinder.boundaryToDisk s)) (t : (unitInterval))
    (s : DiskCylinder.Sphere (E := V)) :
    glued f g H h0 h1 (CylinderBoundary.lower (DiskCylinder.sideMap (t, s))) =
      H (t, s) := by rw [glued_lower, DiskCylinder.gluedBottomSide_side]

/-! ### Homotopies as paths in mapping spaces -/

/-- A homotopy of continuous maps as a path in the mapping space. -/
def MappingPaths.ofHomotopy {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {f g : C(A, B)} (H : f.Homotopy g) : Path f g
    where
  toContinuousMap := H.curry
  source' := H.curry_zero
  target' := H.curry_one

/-- A path in the mapping space as a homotopy. -/
def MappingPaths.toHomotopy {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [LocallyCompactSpace A] {f g : C(A, B)} (p : Path f g) : f.Homotopy g
    where
  toContinuousMap := p.toContinuousMap.uncurry
  map_zero_left a := ContinuousMap.congr_fun p.source a
  map_one_left a := ContinuousMap.congr_fun p.target a

/-- `q` lies over `p` under `r`: each `q t` is `r (p t)`. -/
def MappingPaths.Over {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] {a₀ a₁ : A}
    {b₀ b₁ : B} (r : A → B) (p : Path a₀ a₁) (q : Path b₀ b₁) : Prop :=
  ∀ t, r (p t) = q t

/-- The `Over` relation is symmetric under path reversal. -/
theorem MappingPaths.Over.symm {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {a₀ a₁ : A} {b₀ b₁ : B} {r : A → B} {p : Path a₀ a₁} {q : Path b₀ b₁}
    (h : MappingPaths.Over r p q) : MappingPaths.Over r p.symm q.symm := fun t =>
  h (unitInterval.symm t)

/-- The `Over` relation is transitive under concatenation. -/
theorem MappingPaths.Over.trans {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {a₀ a₁ a₂ : A} {b₀ b₁ b₂ : B} {r : A → B} {p₀ : Path a₀ a₁} {p₁ : Path a₁ a₂}
    {q₀ : Path b₀ b₁} {q₁ : Path b₁ b₂} (h₀ : MappingPaths.Over r p₀ q₀)
    (h₁ : MappingPaths.Over r p₁ q₁) :
    MappingPaths.Over r (p₀.trans p₁) (q₀.trans q₁) := by
  intro t
  simp only [Path.trans_apply]
  split_ifs <;>
    first
    | exact h₀ _
    | exact h₁ _

/-- The normalized zigzag of paths is homotopic to the original. -/
theorem MappingPaths.normalization_cancellation {B : Type*} [TopologicalSpace B]
    {b₀ b₁ b₂ : B} (a : Path b₀ b₁) (h : Path b₁ b₂) :
    (a.symm.trans ((Path.refl b₀).trans ((h.symm.trans a.symm).symm))).Homotopic h := by
  rw [Path.trans_symm, Path.symm_symm, Path.symm_symm]
  have hunit := Path.Homotopic.refl_trans (a.trans h)
  have hfirst := (Path.Homotopic.refl a.symm).hcomp hunit
  have hassoc := (Path.Homotopic.trans_assoc a.symm a h).symm
  have hcancel := (Path.Homotopic.symm_trans a).hcomp (Path.Homotopic.refl h)
  exact hfirst.trans (hassoc.trans (hcancel.trans (Path.Homotopic.refl_trans h)))

/-! ### Boundary path transport -/

/-- A boundary path of cylinder maps transports to an extension. -/
theorem BoundaryPathTransport.exists_transport {V Y : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [TopologicalSpace Y]
    (f : C(DiskCylinder.Disk (E := V), Y))
    {a b : C(DiskCylinder.Sphere (E := V), Y)} (A : Path a b)
    (ha : f.comp DiskCylinder.boundaryToDisk = a) :
    ∃ g : C(DiskCylinder.Disk (E := V), Y),
      ∃ P : Path f g,
        MappingPaths.Over
            (fun v : C(DiskCylinder.Disk (E := V), Y) =>
              v.comp DiskCylinder.boundaryToDisk)
            P A ∧
          g.comp DiskCylinder.boundaryToDisk = b := by
  let H : C((unitInterval) × DiskCylinder.Sphere (E := V), Y) := A.toContinuousMap.uncurry
  have h0 : ∀ s, H (0, s) = f (DiskCylinder.boundaryToDisk s) := by
    intro s
    exact (ContinuousMap.congr_fun A.source s).trans (ContinuousMap.congr_fun ha.symm s)
  let g := DiskCylinder.extensionEndpoint f H h0
  let P := MappingPaths.ofHomotopy (DiskCylinder.extensionHomotopy f H h0)
  have hP :
    MappingPaths.Over
      (fun v : C(DiskCylinder.Disk (E := V), Y) =>
        v.comp DiskCylinder.boundaryToDisk)
      P A := by
    intro t
    apply ContinuousMap.ext
    intro s
    exact DiskCylinder.extend_side f H h0 t s
  refine ⟨g, P, hP, ?_⟩
  simpa using hP 1

/-! ### Homotopy extension for the disk cylinder -/

/-- The bottom family of a cylinder homotopy. -/
def CylinderBoundaryFamilies.bottomFamily {V Y : Type*} [NormedAddCommGroup V]
    [TopologicalSpace Y] (f : C((unitInterval) × DiskCylinder.Disk (E := V), Y)) :
    C(DiskCylinder.Disk (E := V), C((unitInterval), Y)) :=
  (f.comp ContinuousMap.prodSwap).curry

/-- The top family of a cylinder homotopy. -/
def CylinderBoundaryFamilies.topFamily {V Y : Type*} [NormedAddCommGroup V]
    [TopologicalSpace Y] (g : C((unitInterval) × DiskCylinder.Disk (E := V), Y)) :
    C(DiskCylinder.Disk (E := V), C((unitInterval), Y)) :=
  (g.comp ContinuousMap.prodSwap).curry

/-- The side family of a cylinder homotopy. -/
def CylinderBoundaryFamilies.sideFamily {V Y : Type*} [NormedAddCommGroup V]
    [TopologicalSpace Y]
    (H : C((unitInterval) × ((unitInterval) × DiskCylinder.Sphere (E := V)), Y)) :
    C((unitInterval) × DiskCylinder.Sphere (E := V), C((unitInterval), Y)) :=
  (H.comp ContinuousMap.prodSwap).curry

/-- A homotopy glued from bottom, top, and side families. -/
def CylinderBoundaryFamilies.glued {V Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace Y]
    (f g : C((unitInterval) × DiskCylinder.Disk (E := V), Y))
    (H : C((unitInterval) × ((unitInterval) × DiskCylinder.Sphere (E := V)), Y))
    (h0 : ∀ t s, H (t, 0, s) = f (t, DiskCylinder.boundaryToDisk s))
    (h1 : ∀ t s, H (t, 1, s) = g (t, DiskCylinder.boundaryToDisk s)) :
    C((unitInterval) × CylinderBall.boundary (V := V), Y) :=
  (CylinderBoundary.glued (bottomFamily f) (topFamily g) (sideFamily H)
        (fun s => ContinuousMap.ext (fun t => h0 t s))
        (fun s => ContinuousMap.ext (fun t => h1 t s))).uncurry.comp
    ContinuousMap.prodSwap

/-- The glued homotopy on the bottom. -/
theorem CylinderBoundaryFamilies.glued_bottom {V Y : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [TopologicalSpace Y]
    (f g : C((unitInterval) × DiskCylinder.Disk (E := V), Y))
    (H : C((unitInterval) × ((unitInterval) × DiskCylinder.Sphere (E := V)), Y))
    (h0 : ∀ t s, H (t, 0, s) = f (t, DiskCylinder.boundaryToDisk s))
    (h1 : ∀ t s, H (t, 1, s) = g (t, DiskCylinder.boundaryToDisk s)) (t : (unitInterval))
    (z : DiskCylinder.Disk (E := V)) :
    glued f g H h0 h1 (t, CylinderBoundary.lower (DiskCylinder.bottomMap z)) =
      f (t, z) :=
  ContinuousMap.congr_fun
    (CylinderBoundary.glued_bottom (bottomFamily f) (topFamily g) (sideFamily H)
      (fun s => ContinuousMap.ext (fun t => h0 t s))
      (fun s => ContinuousMap.ext (fun t => h1 t s)) z)
    t

/-- The glued homotopy on the top. -/
theorem CylinderBoundaryFamilies.glued_top {V Y : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [TopologicalSpace Y]
    (f g : C((unitInterval) × DiskCylinder.Disk (E := V), Y))
    (H : C((unitInterval) × ((unitInterval) × DiskCylinder.Sphere (E := V)), Y))
    (h0 : ∀ t s, H (t, 0, s) = f (t, DiskCylinder.boundaryToDisk s))
    (h1 : ∀ t s, H (t, 1, s) = g (t, DiskCylinder.boundaryToDisk s)) (t : (unitInterval))
    (z : DiskCylinder.Disk (E := V)) :
    glued f g H h0 h1 (t, CylinderBoundary.top z) = g (t, z) :=
  ContinuousMap.congr_fun
    (CylinderBoundary.glued_top (bottomFamily f) (topFamily g) (sideFamily H)
      (fun s => ContinuousMap.ext (fun t => h0 t s))
      (fun s => ContinuousMap.ext (fun t => h1 t s)) z)
    t

/-- The glued homotopy on the side. -/
theorem CylinderBoundaryFamilies.glued_side {V Y : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [TopologicalSpace Y]
    (f g : C((unitInterval) × DiskCylinder.Disk (E := V), Y))
    (H : C((unitInterval) × ((unitInterval) × DiskCylinder.Sphere (E := V)), Y))
    (h0 : ∀ t s, H (t, 0, s) = f (t, DiskCylinder.boundaryToDisk s))
    (h1 : ∀ t s, H (t, 1, s) = g (t, DiskCylinder.boundaryToDisk s)) (t r : (unitInterval))
    (s : DiskCylinder.Sphere (E := V)) :
    glued f g H h0 h1 (t, CylinderBoundary.lower (DiskCylinder.sideMap (r, s))) =
      H (t, r, s) :=
  ContinuousMap.congr_fun
    (CylinderBoundary.glued_side (bottomFamily f) (topFamily g) (sideFamily H)
      (fun s => ContinuousMap.ext (fun t => h0 t s))
      (fun s => ContinuousMap.ext (fun t => h1 t s)) r s)
    t

/-! ### The cylinder homotopy extension -/

/-- A cylinder boundary homotopy extends to the whole cylinder (HEP). -/
theorem CylinderHEP.exists_extension {V Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace Y]
    (f : C((unitInterval) × DiskCylinder.Disk (E := V), Y))
    (J : C((unitInterval) × CylinderBall.boundary (V := V), Y))
    (h0 : ∀ p, J (0, p) = f p.val) :
    ∃ K : C((unitInterval) × ((unitInterval) × DiskCylinder.Disk (E := V)), Y),
      (∀ p, K (0, p) = f p) ∧
        ∀ (t : (unitInterval)) (p : CylinderBall.boundary (V := V)),
          K (t, p.val) = J (t, p) := by
  let e := CylinderBall.homeomorph (V := V)
  let b := CylinderBall.boundaryHomeomorph (V := V)
  let f' : C(DiskCylinder.Disk (E := ℝ × V), Y) := f.comp (e.symm : C(_, _))
  let J' : C((unitInterval) × DiskCylinder.Sphere (E := ℝ × V), Y) :=
    J.comp ((ContinuousMap.id (unitInterval)).prodMap (b.symm : C(_, _)))
  have h0' : ∀ s, J' (0, s) = f' (DiskCylinder.boundaryToDisk s) := fun s => h0 (b.symm s)
  let H := DiskCylinder.extend f' J' h0'
  let K : C((unitInterval) × ((unitInterval) × DiskCylinder.Disk (E := V)), Y) :=
    H.comp ((ContinuousMap.id (unitInterval)).prodMap (e : C(_, _)))
  refine ⟨K, ?_, ?_⟩
  · intro p
    change H (0, e p) = f p
    exact
      (DiskCylinder.extend_bottom f' J' h0' (e p)).trans
        (congrArg f (e.symm_apply_apply p))
  · intro t p
    change H (t, DiskCylinder.boundaryToDisk (b p)) = J (t, p)
    exact
      (DiskCylinder.extend_side f' J' h0' t (b p)).trans
        (congrArg (fun p => J (t, p)) (b.symm_apply_apply p))

/-! ### Boundary rectification -/

/-- The cylinder boundary splits into bottom, side, and top cases. -/
theorem SideRectification.boundary_cases {V : Type*} [NormedAddCommGroup V]
    (p : CylinderBall.boundary (V := V)) :
    (∃ z, p = CylinderBoundary.lower (DiskCylinder.bottomMap z)) ∨
      (∃ z, p = CylinderBoundary.top z) ∨
        ∃ t s, p = CylinderBoundary.lower (DiskCylinder.sideMap (t, s)) := by
  rcases p with ⟨⟨t, z⟩, ht | ht | hz⟩
  · change t = 0 at ht
    subst t
    exact Or.inl ⟨z, rfl⟩
  · change t = 1 at ht
    subst t
    exact Or.inr (Or.inl ⟨z, rfl⟩)
  · exact Or.inr (Or.inr ⟨t, ⟨z.val, mem_sphere_zero_iff_norm.mpr hz⟩, rfl⟩)

/-- A side-fixed homotopy rectifies to one glued from the pieces. -/
theorem SideRectification.exists_rectification {V Y : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [TopologicalSpace Y]
    {f g : C(DiskCylinder.Disk (E := V), Y)} (P : Path f g)
    {a b : C(DiskCylinder.Sphere (E := V), Y)} (Q H : Path a b)
    (hP :
      MappingPaths.Over
        (fun v : C(DiskCylinder.Disk (E := V), Y) =>
          v.comp DiskCylinder.boundaryToDisk)
        P Q)
    (hQ : Q.Homotopic H) :
    ∃ G : C((unitInterval) × DiskCylinder.Disk (E := V), Y),
      (∀ z, G (0, z) = f z) ∧
        (∀ z, G (1, z) = g z) ∧ ∀ t s, G (t, DiskCylinder.boundaryToDisk s) = H t s := by
  obtain ⟨K⟩ := hQ
  have hfa : f.comp DiskCylinder.boundaryToDisk = a := by simpa using hP 0
  have hgb : g.comp DiskCylinder.boundaryToDisk = b := by simpa using hP 1
  let side : C((unitInterval) × ((unitInterval) × DiskCylinder.Sphere (E := V)), Y) :=
    K.toHomotopy.toContinuousMap.uncurry.comp
      ((Homeomorph.prodAssoc (unitInterval) (unitInterval)
            (DiskCylinder.Sphere (E := V))).symm :
        C(_, _))
  let fb : C((unitInterval) × DiskCylinder.Disk (E := V), Y) := f.comp ContinuousMap.snd
  let gt : C((unitInterval) × DiskCylinder.Disk (E := V), Y) := g.comp ContinuousMap.snd
  have hs0 : ∀ t s, side (t, 0, s) = fb (t, DiskCylinder.boundaryToDisk s) := by
    intro t s
    have he : K (t, 0) = a := (K.eq_fst t (by simp)).trans Q.source
    exact (congrArg (fun v => v s) he).trans (ContinuousMap.congr_fun hfa.symm s)
  have hs1 : ∀ t s, side (t, 1, s) = gt (t, DiskCylinder.boundaryToDisk s) := by
    intro t s
    have he : K (t, 1) = b := (K.eq_fst t (by simp)).trans Q.target
    exact (congrArg (fun v => v s) he).trans (ContinuousMap.congr_fun hgb.symm s)
  let J := CylinderBoundaryFamilies.glued fb gt side hs0 hs1
  have hJ0 :
    ∀ p : CylinderBall.boundary (V := V),
      J (0, p) = MappingPaths.toHomotopy P p.val := by
    intro p
    rcases boundary_cases p with ⟨z, rfl⟩ | ⟨z, rfl⟩ | ⟨t, s, rfl⟩
    · exact
        (CylinderBoundaryFamilies.glued_bottom fb gt side hs0 hs1 0 z).trans
          (ContinuousMap.congr_fun P.source z).symm
    · exact
        (CylinderBoundaryFamilies.glued_top fb gt side hs0 hs1 0 z).trans
          (ContinuousMap.congr_fun P.target z).symm
    · exact
        (CylinderBoundaryFamilies.glued_side fb gt side hs0 hs1 0 t s).trans
          ((congrArg (fun v => v s) (K.apply_zero t)).trans
            (ContinuousMap.congr_fun (hP t) s).symm)
  obtain ⟨W, _, hW⟩ :=
    CylinderHEP.exists_extension (MappingPaths.toHomotopy P).toContinuousMap J hJ0
  let G : C((unitInterval) × DiskCylinder.Disk (E := V), Y) :=
    W.comp ⟨fun p => (1, p), continuous_const.prodMk continuous_id⟩
  refine ⟨G, ?_, ?_, ?_⟩
  · intro z
    exact
      (hW 1 (CylinderBoundary.lower (DiskCylinder.bottomMap z))).trans
        (CylinderBoundaryFamilies.glued_bottom fb gt side hs0 hs1 1 z)
  · intro z
    exact
      (hW 1 (CylinderBoundary.top z)).trans
        (CylinderBoundaryFamilies.glued_top fb gt side hs0 hs1 1 z)
  · intro t s
    exact
      (hW 1 (CylinderBoundary.lower (DiskCylinder.sideMap (t, s)))).trans
        ((CylinderBoundaryFamilies.glued_side fb gt side hs0 hs1 1 t s).trans
          (congrArg (fun v => v s) (K.apply_one t)))
