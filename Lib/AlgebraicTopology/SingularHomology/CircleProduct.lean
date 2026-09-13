/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.Suspension
public import Lib.AlgebraicTopology.SingularHomology.Sum
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
public import Lib.AlgebraicTopology.SingularHomology.ModuleHomology
public import Lib.AlgebraicTopology.SingularHomology.Naturality

/-!
# The Künneth theorem for S¹ × X and the homology of the circle

For the product of the circle with a space, the homology splits as
`H_n(S¹ × X) ≅ H_n(X) ⊕ H_{n-1}(X)` — the Künneth formula for the circle (Hatcher, Cor 2.11's
content for one factor `S¹`). The engine is the two-open cover of `S¹` by contractible arcs,
transported to the product:

* `SingularHomology.circleProductHomologyEquiv`-family — the splitting of
  `H_n(S¹ × X)`, with the circle section and projection lemmas
  (`circleSectionHomology`, `circleProjection_section`, `productArcHomologyEquiv`);
* `SingularHomology.circle_homology_subsingleton` — `H_k(S¹) = 0` for `k ≥ 2`
  (Hatcher Cor 2.14's circle rows).

## Outline of the proof

1. *The circle as a two-open cover.*  `CircleTopology.intervalContractible` (arcs are
   contractible) and the overlap identifications give the MV cover of `S¹ × X` by
   `arc⁻ × X` and `arc⁺ × X`, each homotopy-equivalent to `X`.
2. *The product MV sequence.*  The intersection is `(arc⁻ ∩ arc⁺) × X`, two copies of `X`;
   the Mayer–Vietoris sequence (`MayerVietoris.lean`) becomes a split exact sequence with
   maps induced by the inclusions of the arcs (`productUInclusion_homology`,
   `productIntersectionToV_homology`, `productIntersectionHomologyEquiv`).
3. *The splitting.*  `circleProductLeftHomologyMap_apply` and the product maps exhibit the
   iso `H_n(S¹ × X) ≅ H_n(X) ⊕ H_{n-1}(X)` (`circleProductHomologyEquiv`,
   `circleProductHomologyZeroEquiv` for the degree-zero piece).
4. *The circle itself.*  `circleSectionHomology`/`circleProjection_section` and
   `circle_homology_subsingleton` conclude `H_1(S¹) = ℤ`, `H_k(S¹) = 0` for `k ≥ 2`.

## Main definitions and results

* `SingularHomology.circleProductHomologyEquiv` : the Künneth splitting for `S¹ × X`.
* `SingularHomology.circle_homology_subsingleton` : higher homology of `S¹`
  vanishes.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], Corollary 2.11 and §2.2's torus example

## Tags

Künneth, circle, product, Mayer–Vietoris
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

/-! ### The two-arc cover of the circle -/

/-- An open interval is contractible. -/
theorem SingularHomology.CircleTopology.intervalContractible (a b : ℝ) (hab : a < b) :
    ContractibleSpace (Set.Ioo a b) :=
  (convex_Ioo a b).contractibleSpace ⟨(a + b) / 2, by constructor <;> linarith⟩

/-- The lower half-interval into the punctured interval. -/
def SingularHomology.CircleTopology.puncturedIntervalInl (t : Set.Ioo (0 : ℝ) (1 / 2)) :
    { s : Set.Ioo (0 : ℝ) 1 // (s : ℝ) ≠ 1 / 2 } :=
  ⟨⟨t, t.property.1, t.property.2.trans (by norm_num)⟩, ne_of_lt t.property.2⟩

/-- The upper half-interval into the punctured interval. -/
def SingularHomology.CircleTopology.puncturedIntervalInr (t : Set.Ioo (1 / 2 : ℝ) 1) :
    { s : Set.Ioo (0 : ℝ) 1 // (s : ℝ) ≠ 1 / 2 } :=
  ⟨⟨t, (by norm_num : (0 : ℝ) < 1 / 2).trans t.property.1, t.property.2⟩, ne_of_gt t.property.1⟩

/-- The lower inclusion is continuous. -/
theorem SingularHomology.CircleTopology.puncturedIntervalInl_continuous :
    Continuous puncturedIntervalInl :=
  (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The upper inclusion is continuous. -/
theorem SingularHomology.CircleTopology.puncturedIntervalInr_continuous :
    Continuous puncturedIntervalInr :=
  (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The lower inclusion is an open map. -/
theorem SingularHomology.CircleTopology.puncturedIntervalInl_isOpenMap :
    IsOpenMap puncturedIntervalInl :=
  (isOpen_Ioo.isOpenMap_subtype_val.subtype_mk _).subtype_mk _

/-- The upper inclusion is an open map. -/
theorem SingularHomology.CircleTopology.puncturedIntervalInr_isOpenMap :
    IsOpenMap puncturedIntervalInr :=
  (isOpen_Ioo.isOpenMap_subtype_val.subtype_mk _).subtype_mk _

/-- The punctured interval is the sum of its two halves. -/
def SingularHomology.CircleTopology.puncturedIntervalSumEquiv :
    (Set.Ioo (0 : ℝ) (1 / 2) ⊕ Set.Ioo (1 / 2 : ℝ) 1) ≃
      { t : Set.Ioo (0 : ℝ) 1 // (t : ℝ) ≠ 1 / 2 } :=
  Equiv.ofBijective (Sum.elim puncturedIntervalInl puncturedIntervalInr)
    (by
      constructor
      · intro s t h
        have hcoord :=
          congrArg (fun u : { t : Set.Ioo (0 : ℝ) 1 // (t : ℝ) ≠ 1 / 2 } => (u.val : ℝ)) h
        rcases s with s | s <;> rcases t with t | t
        · exact congrArg Sum.inl (Subtype.ext hcoord)
        · change (s : ℝ) = (t : ℝ) at hcoord
          linarith [s.property.2, t.property.1]
        · change (s : ℝ) = (t : ℝ) at hcoord
          linarith [s.property.1, t.property.2]
        · exact congrArg Sum.inr (Subtype.ext hcoord)
      · intro t
        rcases lt_or_gt_of_ne t.property with ht | ht
        · exact ⟨Sum.inl ⟨t.val, t.val.property.1, ht⟩, rfl⟩
        · exact ⟨Sum.inr ⟨t.val, ht, t.val.property.2⟩, rfl⟩)

/-- The punctured interval model of the circle: the interval with the half point removed is homeomorphic to the circle minus a point. -/
def SingularHomology.CircleTopology.puncturedIntervalHomeomorph :
    { t : Set.Ioo (0 : ℝ) 1 // (t : ℝ) ≠ 1 / 2 } ≃ₜ
      (Set.Ioo (0 : ℝ) (1 / 2) ⊕ Set.Ioo (1 / 2 : ℝ) 1) :=
  (puncturedIntervalSumEquiv.toHomeomorphOfContinuousOpen
      (puncturedIntervalInl_continuous.sumElim puncturedIntervalInr_continuous)
      (puncturedIntervalInl_isOpenMap.sumElim puncturedIntervalInr_isOpenMap)).symm

/-- The circle as `R / Z`: the quotient group model used throughout the circle dictionary, with its base point and half point. -/
abbrev SingularHomology.CircleTopology.Circle :=
  AddCircle (1 : ℝ)

/-- The half point of the circle. -/
def SingularHomology.CircleTopology.halfPoint :
    SingularHomology.CircleTopology.Circle :=
  ((1 / 2 : ℝ) : SingularHomology.CircleTopology.Circle)

/-- The half point is not zero. -/
theorem SingularHomology.CircleTopology.halfPoint_ne_zero : halfPoint ≠ 0 := by
  intro h
  have he :=
    (AddCircle.coe_eq_zero_iff_of_mem_Ico (p := (1 : ℝ)) (a := (1 / 2 : ℝ)) (by norm_num)).mp h
  norm_num at he

/-- The open arc `U` of the two-arc cover of the circle: the complement of the antipodal point, contractible (Hatcher, Algebraic Topology, the cover used for `H_*(S^1)`). -/
def SingularHomology.CircleTopology.arcU :
    Set SingularHomology.CircleTopology.Circle :=
  ({0} : Set SingularHomology.CircleTopology.Circle)ᶜ

/-- The open arc `V` of the two-arc cover: the complementary contractible arc, disjoint intersection pattern giving the van Kampen/Mayer-Vietoris cover of the circle. -/
def SingularHomology.CircleTopology.arcV :
    Set SingularHomology.CircleTopology.Circle :=
  ({ halfPoint } : Set SingularHomology.CircleTopology.Circle)ᶜ

/-- `arcU` is the complement of zero. -/
@[simp]
theorem SingularHomology.CircleTopology.mem_arcU
    (x : SingularHomology.CircleTopology.Circle) : x ∈ arcU ↔ x ≠ 0 :=
  Iff.rfl

/-- `arcV` is the complement of the half point. -/
@[simp]
theorem SingularHomology.CircleTopology.mem_arcV
    (x : SingularHomology.CircleTopology.Circle) : x ∈ arcV ↔ x ≠ halfPoint :=
  Iff.rfl

/-- `arcU` is open. -/
theorem SingularHomology.CircleTopology.arcU_open : IsOpen arcU :=
  isOpen_compl_singleton

/-- `arcV` is open. -/
theorem SingularHomology.CircleTopology.arcV_open : IsOpen arcV :=
  isOpen_compl_singleton

/-- The two arcs cover the circle. -/
theorem SingularHomology.CircleTopology.arc_cover : arcU ∪ arcV = Set.univ := by
  ext x
  simp only [Set.mem_union, mem_arcU, mem_arcV, Set.mem_univ, iff_true]
  by_cases hx : x = 0
  · right
    rw [hx]
    exact Ne.symm halfPoint_ne_zero
  · exact Or.inl hx

/-- The punctured circle is homeomorphic to an open interval. -/
def SingularHomology.CircleTopology.puncturedCircleHomeomorph (a : ℝ) :
    ({(a : SingularHomology.CircleTopology.Circle)}ᶜ :
        Set SingularHomology.CircleTopology.Circle) ≃ₜ
      Set.Ioo a (a + 1) :=
  (AddCircle.openPartialHomeomorphCoe (1 : ℝ) a).toHomeomorphSourceTarget.symm

/-- `arcU` is homeomorphic to `(0,1)`. -/
def SingularHomology.CircleTopology.arcUHomeomorph : arcU ≃ₜ Set.Ioo (0 : ℝ) 1 :=
  (puncturedCircleHomeomorph 0).trans (Homeomorph.setCongr (by simp))

/-- `arcV` is homeomorphic to `(1/2,3/2)`. -/
def SingularHomology.CircleTopology.arcVHomeomorph :
    arcV ≃ₜ Set.Ioo (1 / 2 : ℝ) (3 / 2) :=
  (puncturedCircleHomeomorph (1 / 2)).trans (Homeomorph.setCongr (by norm_num))

/-- The `arcU` chart coerces back to the point. -/
@[simp]
theorem SingularHomology.CircleTopology.arcUHomeomorph_coe (x : arcU) :
    (((arcUHomeomorph x : Set.Ioo (0 : ℝ) 1) : ℝ) :
        SingularHomology.CircleTopology.Circle) =
      (x : SingularHomology.CircleTopology.Circle) :=
  congrArg Subtype.val (arcUHomeomorph.symm_apply_apply x)

/-- The `arcV` chart coerces back to the point. -/
@[simp]
theorem SingularHomology.CircleTopology.arcVHomeomorph_coe (x : arcV) :
    (((arcVHomeomorph x : Set.Ioo (1 / 2 : ℝ) (3 / 2)) : ℝ) :
        SingularHomology.CircleTopology.Circle) =
      (x : SingularHomology.CircleTopology.Circle) :=
  congrArg Subtype.val (arcVHomeomorph.symm_apply_apply x)

/-- `arcU` is contractible. -/
instance SingularHomology.CircleTopology.arcUContractible : ContractibleSpace arcU := by
  let : ContractibleSpace (Set.Ioo (0 : ℝ) 1) := intervalContractible 0 1 zero_lt_one
  exact arcUHomeomorph.contractibleSpace

/-- `arcV` is contractible. -/
instance SingularHomology.CircleTopology.arcVContractible : ContractibleSpace arcV := by
  let : ContractibleSpace (Set.Ioo (1 / 2 : ℝ) (3 / 2)) :=
    intervalContractible (1 / 2) (3 / 2) (by norm_num)
  exact arcVHomeomorph.contractibleSpace

/-- The lower half-interval is contractible. -/
instance SingularHomology.CircleTopology.leftIntervalContractible :
    ContractibleSpace (Set.Ioo (0 : ℝ) (1 / 2)) :=
  intervalContractible 0 (1 / 2) (by norm_num)

/-- The upper half-interval is contractible. -/
instance SingularHomology.CircleTopology.rightIntervalContractible :
    ContractibleSpace (Set.Ioo (1 / 2 : ℝ) 1) :=
  intervalContractible (1 / 2) 1 (by norm_num)

/-- The intersection subtype is a subspace of `U`. -/
def SingularHomology.CircleTopology.intersectionSubtypeHomeomorph {T : Type*}
    [TopologicalSpace T] (U V : Set T) : ↥(U ∩ V) ≃ₜ { x : U // (x : T) ∈ V }
    where
  toFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  invFun x := ⟨x.val.val, x.val.property, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- An `arcU` point lies in `arcV` exactly off the midpoint. -/
theorem SingularHomology.CircleTopology.arcU_mem_arcV_iff (x : arcU) :
    (x : SingularHomology.CircleTopology.Circle) ∈ arcV ↔
      (arcUHomeomorph x : ℝ) ≠ 1 / 2 := by
  change (x : SingularHomology.CircleTopology.Circle) ≠ halfPoint ↔ _
  let m : Set.Ioo (0 : ℝ) 1 := ⟨1 / 2, by norm_num⟩
  have hm :
    (arcUHomeomorph.symm m : SingularHomology.CircleTopology.Circle) = halfPoint := rfl
  constructor
  · intro hx ht
    have ht' : arcUHomeomorph x = m := Subtype.ext ht
    have hx' : x = arcUHomeomorph.symm m :=
      (arcUHomeomorph.symm_apply_apply x).symm.trans (congrArg arcUHomeomorph.symm ht')
    exact hx ((congrArg Subtype.val hx').trans hm)
  · intro hx ht
    have hx' : x = arcUHomeomorph.symm m := Subtype.ext (ht.trans hm.symm)
    apply hx
    change (arcUHomeomorph x : ℝ) = (m : ℝ)
    rw [hx', Homeomorph.apply_symm_apply]

/-- The arc intersection is the punctured interval. -/
def SingularHomology.CircleTopology.intersectionPuncturedHomeomorph :
    ↥(arcU ∩ arcV) ≃ₜ { t : Set.Ioo (0 : ℝ) 1 // (t : ℝ) ≠ 1 / 2 } :=
  (intersectionSubtypeHomeomorph arcU arcV).trans (arcUHomeomorph.subtype arcU_mem_arcV_iff)

/-- The arc intersection is two open intervals. -/
def SingularHomology.CircleTopology.intersectionHomeomorph :
    ↥(arcU ∩ arcV) ≃ₜ (Set.Ioo (0 : ℝ) (1 / 2) ⊕ Set.Ioo (1 / 2 : ℝ) 1) :=
  intersectionPuncturedHomeomorph.trans puncturedIntervalHomeomorph

/-! ### Contractibility and lifts -/

/-- A chosen contraction center of a contractible space. -/
def SingularHomology.CircleTopology.contractionPoint (S : Type*) [TopologicalSpace S]
    [ContractibleSpace S] : S :=
  Classical.choose (id_nullhomotopic S)

/-- The constant contraction map is homotopic to the identity. -/
theorem SingularHomology.CircleTopology.contractionPoint_homotopic (S : Type*)
    [TopologicalSpace S] [ContractibleSpace S] :
    (ContinuousMap.const S (contractionPoint S)).Homotopic (ContinuousMap.id S) :=
  (Classical.choose_spec (id_nullhomotopic S)).symm

/-- A contractible factor can be collapsed: `S × X ≃ₕ X`. -/
def SingularHomology.CircleTopology.contractibleProdHomotopyEquiv (S X : Type*)
    [TopologicalSpace S] [TopologicalSpace X] [ContractibleSpace S] : (S × X) ≃ₕ X
    where
  toFun := ContinuousMap.snd
  invFun := (ContinuousMap.const X (contractionPoint S)).prodMk (ContinuousMap.id X)
  left_inv := (contractionPoint_homotopic S).prodMap (.refl (ContinuousMap.id X))
  right_inv := .refl (ContinuousMap.id X)

/-- The sum of two continuous maps. -/
def SingularHomology.CircleTopology.sumContinuousMap {A A' B B' : Type*}
    [TopologicalSpace A] [TopologicalSpace A'] [TopologicalSpace B] [TopologicalSpace B']
    (f : C(A, A')) (g : C(B, B')) : C(A ⊕ B, A' ⊕ B') :=
  ⟨Sum.map f g, f.continuous.sumMap g.continuous⟩

/-- The sum of two homotopies. -/
def SingularHomology.CircleTopology.sumHomotopy {A A' B B' : Type*} [TopologicalSpace A]
    [TopologicalSpace A'] [TopologicalSpace B] [TopologicalSpace B'] {f₀ f₁ : C(A, A')}
    {g₀ g₁ : C(B, B')} (F : f₀.Homotopy f₁) (G : g₀.Homotopy g₁) :
    (sumContinuousMap f₀ g₀).Homotopy (sumContinuousMap f₁ g₁)
    where
  toFun := Sum.elim (fun p => Sum.inl (F p)) (fun p => Sum.inr (G p)) ∘ Homeomorph.prodSumDistrib
  continuous_toFun :=
    ((continuous_inl.comp F.continuous).sumElim (continuous_inr.comp G.continuous)).comp
      Homeomorph.prodSumDistrib.continuous
  map_zero_left := by
    intro x
    cases x with
    | inl a => exact congrArg Sum.inl (F.map_zero_left a)
    | inr b => exact congrArg Sum.inr (G.map_zero_left b)
  map_one_left := by
    intro x
    cases x with
    | inl a => exact congrArg Sum.inl (F.map_one_left a)
    | inr b => exact congrArg Sum.inr (G.map_one_left b)

/-- The sum of two homotopy equivalences. -/
def SingularHomology.CircleTopology.sumHomotopyEquiv {A A' B B' : Type*}
    [TopologicalSpace A] [TopologicalSpace A'] [TopologicalSpace B] [TopologicalSpace B']
    (eA : A ≃ₕ A') (eB : B ≃ₕ B') : (A ⊕ B) ≃ₕ (A' ⊕ B')
    where
  toFun := sumContinuousMap eA.toFun eB.toFun
  invFun := sumContinuousMap eA.invFun eB.invFun
  left_inv := by
    rcases eA.left_inv with ⟨F⟩
    rcases eB.left_inv with ⟨G⟩
    refine ⟨(sumHomotopy F G).cast ?_ ?_⟩
    · ext x
      cases x <;> rfl
    · ext x
      cases x <;> rfl
  right_inv := by
    rcases eA.right_inv with ⟨F⟩
    rcases eB.right_inv with ⟨G⟩
    refine ⟨(sumHomotopy F G).cast ?_ ?_⟩
    · ext x
      cases x <;> rfl
    · ext x
      cases x <;> rfl

/-- A map lifting to `ℝ` contracts to the constant map. -/
def SingularHomology.CircleTopology.circleLiftContraction {S : Type*}
    [TopologicalSpace S] (f : C(S, AddCircle (1 : ℝ))) (l : C(S, ℝ))
    (hlift : ∀ s, (l s : AddCircle (1 : ℝ)) = f s) : f.Homotopy (ContinuousMap.const S 0)
    where
  toFun p := (((1 - (p.1 : ℝ)) * l p.2 : ℝ) : AddCircle (1 : ℝ))
  continuous_toFun :=
    (AddCircle.continuous_mk' (1 : ℝ)).comp
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (l.continuous.comp continuous_snd))
  map_zero_left s := by simpa using hlift s
  map_one_left s := by simp

/-- A product map with a lifted circle coordinate contracts onto the `X` factor. -/
def SingularHomology.CircleTopology.circleProductLiftContraction {S X : Type*}
    [TopologicalSpace S] [TopologicalSpace X] (f : C(S, AddCircle (1 : ℝ) × X)) (l : C(S, ℝ))
    (hlift : ∀ s, (l s : AddCircle (1 : ℝ)) = (f s).1) :
    f.Homotopy ⟨fun s => (0, (f s).2), continuous_const.prodMk f.continuous.snd⟩
    where
  toFun p := ((((1 - (p.1 : ℝ)) * l p.2 : ℝ) : AddCircle (1 : ℝ)), (f p.2).2)
  continuous_toFun :=
    ((AddCircle.continuous_mk' (1 : ℝ)).comp
          ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
            (l.continuous.comp continuous_snd))).prodMk
      (f.continuous.snd.comp continuous_snd)
  map_zero_left
    s := by
    apply Prod.ext
    · simpa using hlift s
    · rfl
  map_one_left s := by simp

/-! ### The product cover -/

/-- The product cover element `arcU × X`. -/
def SingularHomology.CircleTopology.productU (X : Type*) :
    Set (SingularHomology.CircleTopology.Circle × X) :=
  Prod.fst ⁻¹' arcU

/-- The product cover element `arcV × X`. -/
def SingularHomology.CircleTopology.productV (X : Type*) :
    Set (SingularHomology.CircleTopology.Circle × X) :=
  Prod.fst ⁻¹' arcV

/-- The product `U` is open. -/
theorem SingularHomology.CircleTopology.productU_open (X : Type*) [TopologicalSpace X] :
    IsOpen (productU X) :=
  arcU_open.preimage continuous_fst

/-- The product `V` is open. -/
theorem SingularHomology.CircleTopology.productV_open (X : Type*) [TopologicalSpace X] :
    IsOpen (productV X) :=
  arcV_open.preimage continuous_fst

/-- The product arcs cover `Circle × X`. -/
theorem SingularHomology.CircleTopology.product_cover (X : Type*) :
    productU X ∪ productV X = Set.univ := by
  change
    Prod.fst ⁻¹' arcU ∪ Prod.fst ⁻¹' arcV =
      (Set.univ : Set (SingularHomology.CircleTopology.Circle × X))
  rw [← Set.preimage_union, arc_cover, Set.preimage_univ]

/-- The projection of the product onto `X`. -/
def SingularHomology.CircleTopology.productProjection (X : Type*) [TopologicalSpace X] :
    C(SingularHomology.CircleTopology.Circle × X, X) :=
  ContinuousMap.snd

/-- The zero-section inclusion of `X` into the product. -/
def SingularHomology.CircleTopology.productSection (X : Type*) [TopologicalSpace X] :
    C(X, SingularHomology.CircleTopology.Circle × X) :=
  (ContinuousMap.const X (0 : SingularHomology.CircleTopology.Circle)).prodMk
    (ContinuousMap.id X)

/-- The projection splits the section. -/
@[simp]
theorem SingularHomology.CircleTopology.productProjection_comp_productSection (X : Type*)
    [TopologicalSpace X] : (productProjection X).comp (productSection X) = ContinuousMap.id X :=
  rfl

/-- The inclusion of the product `U`. -/
def SingularHomology.CircleTopology.productUInclusion (X : Type*) [TopologicalSpace X] :
    C(productU X, SingularHomology.CircleTopology.Circle × X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The inclusion of the product `V`. -/
def SingularHomology.CircleTopology.productVInclusion (X : Type*) [TopologicalSpace X] :
    C(productV X, SingularHomology.CircleTopology.Circle × X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The intersection inclusion into `U`. -/
def SingularHomology.CircleTopology.productIntersectionToU (X : Type*)
    [TopologicalSpace X] : C(↥(productU X ∩ productV X), productU X) :=
  ⟨fun z => ⟨z.val, z.property.1⟩, continuous_subtype_val.subtype_mk _⟩

/-- The intersection inclusion into `V`. -/
def SingularHomology.CircleTopology.productIntersectionToV (X : Type*)
    [TopologicalSpace X] : C(↥(productU X ∩ productV X), productV X) :=
  ⟨fun z => ⟨z.val, z.property.2⟩, continuous_subtype_val.subtype_mk _⟩

/-- The fold `X ⊕ X → X`. -/
def SingularHomology.CircleTopology.foldMap (X : Type*) [TopologicalSpace X] :
    C(X ⊕ X, X) :=
  ⟨Sum.elim id id, continuous_id.sumElim continuous_id⟩

/-- The preimage of a circle subset is `S × X`. -/
def SingularHomology.CircleTopology.productArcHomeomorph (X : Type*) [TopologicalSpace X]
    (S : Set SingularHomology.CircleTopology.Circle) :
    ↥(Prod.fst ⁻¹' S : Set (SingularHomology.CircleTopology.Circle × X)) ≃ₜ S × X
    where
  toFun z := (⟨z.val.1, z.property⟩, z.val.2)
  invFun z := ⟨(z.1.val, z.2), z.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.fst.subtype_mk _).prodMk continuous_subtype_val.snd
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).subtype_mk _

/-- The product `U` is `arcU × X`. -/
def SingularHomology.CircleTopology.productUHomeomorph (X : Type*) [TopologicalSpace X] :
    productU X ≃ₜ arcU × X :=
  productArcHomeomorph X arcU

/-- The product `V` is `arcV × X`. -/
def SingularHomology.CircleTopology.productVHomeomorph (X : Type*) [TopologicalSpace X] :
    productV X ≃ₜ arcV × X :=
  productArcHomeomorph X arcV

/-- The product intersection is `(arcU ∩ arcV) × X`. -/
def SingularHomology.CircleTopology.productIntersectionArcHomeomorph (X : Type*)
    [TopologicalSpace X] : ↥(productU X ∩ productV X) ≃ₜ ↥(arcU ∩ arcV) × X :=
  productArcHomeomorph X (arcU ∩ arcV)

/-- The product intersection is two interval products. -/
def SingularHomology.CircleTopology.productIntersectionHomeomorph (X : Type*)
    [TopologicalSpace X] :
    ↥(productU X ∩ productV X) ≃ₜ (Set.Ioo (0 : ℝ) (1 / 2) × X) ⊕ (Set.Ioo (1 / 2 : ℝ) 1 × X) :=
  ((productIntersectionArcHomeomorph X).trans
        (intersectionHomeomorph.prodCongr (Homeomorph.refl X))).trans
    Homeomorph.sumProdDistrib

/-- The product `U` is homotopy equivalent to `X`. -/
def SingularHomology.CircleTopology.productUHomotopyEquiv (X : Type*)
    [TopologicalSpace X] : productU X ≃ₕ X :=
  (productUHomeomorph X).toHomotopyEquiv.trans (contractibleProdHomotopyEquiv arcU X)

/-- The product `V` is homotopy equivalent to `X`. -/
def SingularHomology.CircleTopology.productVHomotopyEquiv (X : Type*)
    [TopologicalSpace X] : productV X ≃ₕ X :=
  (productVHomeomorph X).toHomotopyEquiv.trans (contractibleProdHomotopyEquiv arcV X)

/-- The product intersection is homotopy equivalent to `X ⊕ X`. -/
def SingularHomology.CircleTopology.productIntersectionHomotopyEquiv (X : Type*)
    [TopologicalSpace X] : ↥(productU X ∩ productV X) ≃ₕ X ⊕ X :=
  (productIntersectionHomeomorph X).toHomotopyEquiv.trans
    (sumHomotopyEquiv (contractibleProdHomotopyEquiv (Set.Ioo (0 : ℝ) (1 / 2)) X)
      (contractibleProdHomotopyEquiv (Set.Ioo (1 / 2 : ℝ) 1) X))

/-- The fold of the intersection equivalence is the `X` coordinate. -/
@[simp]
theorem SingularHomology.CircleTopology.productIntersectionHomotopyEquiv_fold (X : Type*)
    [TopologicalSpace X] (z : ↥(productU X ∩ productV X)) :
    foldMap X (productIntersectionHomotopyEquiv X z) = z.val.2 := by
  let c : ↥(arcU ∩ arcV) := ⟨z.val.1, z.property⟩
  change
    Sum.elim id id
        (Sum.map (fun t : Set.Ioo (0 : ℝ) (1 / 2) × X => t.2)
          (fun t : Set.Ioo (1 / 2 : ℝ) 1 × X => t.2)
          (Homeomorph.sumProdDistrib (intersectionHomeomorph c, z.val.2))) =
      z.val.2
  cases h : intersectionHomeomorph c <;> rfl

/-- The `U` intersection map is the fold. -/
theorem SingularHomology.CircleTopology.productIntersectionToU_fold (X : Type*)
    [TopologicalSpace X] :
    (productUHomotopyEquiv X).toFun.comp (productIntersectionToU X) =
      (foldMap X).comp (productIntersectionHomotopyEquiv X).toFun := by
  apply ContinuousMap.ext
  intro z
  exact (productIntersectionHomotopyEquiv_fold X z).symm

/-- The `V` intersection map is the fold. -/
theorem SingularHomology.CircleTopology.productIntersectionToV_fold (X : Type*)
    [TopologicalSpace X] :
    (productVHomotopyEquiv X).toFun.comp (productIntersectionToV X) =
      (foldMap X).comp (productIntersectionHomotopyEquiv X).toFun := by
  apply ContinuousMap.ext
  intro z
  exact (productIntersectionHomotopyEquiv_fold X z).symm

/-- The real coordinate of a product `U` point. -/
def SingularHomology.CircleTopology.productUCoordinate (X : Type*) [TopologicalSpace X] :
    C(productU X, ℝ) :=
  ⟨fun z => (arcUHomeomorph ((productUHomeomorph X z).1) : ℝ),
    continuous_subtype_val.comp
      (arcUHomeomorph.continuous.comp (productUHomeomorph X).continuous.fst)⟩

/-- The real coordinate of a product `V` point. -/
def SingularHomology.CircleTopology.productVCoordinate (X : Type*) [TopologicalSpace X] :
    C(productV X, ℝ) :=
  ⟨fun z => (arcVHomeomorph ((productVHomeomorph X z).1) : ℝ),
    continuous_subtype_val.comp
      (arcVHomeomorph.continuous.comp (productVHomeomorph X).continuous.fst)⟩

/-- The `U` coordinate coerces back to the circle component. -/
@[simp]
theorem SingularHomology.CircleTopology.productUCoordinate_coe (X : Type*)
    [TopologicalSpace X] (z : productU X) :
    ((productUCoordinate X z : ℝ) : SingularHomology.CircleTopology.Circle) = z.val.1 :=
  arcUHomeomorph_coe _

/-- The `V` coordinate coerces back to the circle component. -/
@[simp]
theorem SingularHomology.CircleTopology.productVCoordinate_coe (X : Type*)
    [TopologicalSpace X] (z : productV X) :
    ((productVCoordinate X z : ℝ) : SingularHomology.CircleTopology.Circle) = z.val.1 :=
  arcVHomeomorph_coe _

/-- The `U` inclusion is homotopic to the section factorization. -/
def SingularHomology.CircleTopology.productUInclusionHomotopy (X : Type*)
    [TopologicalSpace X] :
    (productUInclusion X).Homotopy ((productSection X).comp (productUHomotopyEquiv X).toFun) :=
  circleProductLiftContraction (productUInclusion X) (productUCoordinate X)
    (productUCoordinate_coe X)

/-- The `V` inclusion is homotopic to the section factorization. -/
def SingularHomology.CircleTopology.productVInclusionHomotopy (X : Type*)
    [TopologicalSpace X] :
    (productVInclusion X).Homotopy ((productSection X).comp (productVHomotopyEquiv X).toFun) :=
  circleProductLiftContraction (productVInclusion X) (productVCoordinate X)
    (productVCoordinate_coe X)

/-- The arc-product homology equivalence: homology of the product with an arc is the homology of the other factor, the first rung of the Kunneth splitting for `S^1 x X` (Hatcher, Algebraic Topology, Corollary 2.11 content). -/
def SingularHomology.productArcHomologyEquiv (X : Type) [TopologicalSpace X] (n : ℕ) :
    (SingularMayerVietoris.SingularHomology (CircleTopology.productU X) n ×
        SingularMayerVietoris.SingularHomology (CircleTopology.productV X) n) ≃ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology X n × SingularMayerVietoris.SingularHomology X n) :=
  ((homotopyEquivHomologyEquiv (CircleTopology.productUHomotopyEquiv X) n).toAddEquiv.prodCongr
      (homotopyEquivHomologyEquiv (CircleTopology.productVHomotopyEquiv X)
          n).toAddEquiv).toIntLinearEquiv

/-! ### Homology of the product cover -/

/-- The product-intersection homology is two copies of `H_n(X)`. -/
def SingularHomology.productIntersectionHomologyEquiv (X : Type) [TopologicalSpace X]
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology
        (CircleTopology.productU X ∩ CircleTopology.productV X :
          Set ((SingularHomology.CircleTopology.Circle) × X))
        n ≃ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology X n × SingularMayerVietoris.SingularHomology X n) :=
  (homotopyEquivHomologyEquiv (CircleTopology.productIntersectionHomotopyEquiv X) n).trans
    (sumHomologyEquiv X X n)

/-- The equivalence computes through the homotopy equivalence. -/
@[simp]
theorem SingularHomology.productIntersectionHomologyEquiv_apply (X : Type)
    [TopologicalSpace X] (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (CircleTopology.productU X ∩ CircleTopology.productV X :
          Set ((SingularHomology.CircleTopology.Circle) × X))
        n) :
    productIntersectionHomologyEquiv X n a =
      sumHomologyEquiv X X n
        (SingularMayerVietoris.singularHomologyMap
          (CircleTopology.productIntersectionHomotopyEquiv X).toFun n a) :=
  rfl

/-- The circle section in homology: the map induced by the inclusion of the circle factor, a right inverse of the projection on homology. -/
abbrev SingularHomology.circleSectionHomology (X : Type) [TopologicalSpace X] (n : ℕ) :
    SingularMayerVietoris.SingularHomology X n →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology
        ((SingularHomology.CircleTopology.Circle) × X) n :=
  SingularMayerVietoris.singularHomologyMap (CircleTopology.productSection X) n

/-- The circle projection in homology: the map induced by projecting the product to the circle factor. -/
abbrev SingularHomology.circleProjectionHomology (X : Type) [TopologicalSpace X]
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology ((SingularHomology.CircleTopology.Circle) × X)
        n →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology X n :=
  SingularMayerVietoris.singularHomologyMap (CircleTopology.productProjection X) n

/-- The projection-section relation in homology: projecting after including the circle factor is the identity - the splitting datum for the Kuenneth decomposition of `H_n(S^1 x X)`. -/
@[simp]
theorem SingularHomology.circleProjection_section (X : Type) [TopologicalSpace X]
    (n : ℕ) : (circleProjectionHomology X n).comp (circleSectionHomology X n) = LinearMap.id := by
  rw [← singularHomologyMap_comp, CircleTopology.productProjection_comp_productSection,
    singularHomologyMap_id]

/-- The `U` inclusion on homology factors through the section. -/
theorem SingularHomology.productUInclusion_homology (X : Type) [TopologicalSpace X]
    (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (CircleTopology.productUInclusion X) n =
      (circleSectionHomology X n).comp
        (homotopyEquivHomologyEquiv (CircleTopology.productUHomotopyEquiv X) n).toLinearMap := by
  rw [homotopy_homologyMap (CircleTopology.productUInclusionHomotopy X) n,
    singularHomologyMap_comp]
  rfl

/-- The `V` inclusion on homology factors through the section. -/
theorem SingularHomology.productVInclusion_homology (X : Type) [TopologicalSpace X]
    (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (CircleTopology.productVInclusion X) n =
      (circleSectionHomology X n).comp
        (homotopyEquivHomologyEquiv (CircleTopology.productVHomotopyEquiv X) n).toLinearMap := by
  rw [homotopy_homologyMap (CircleTopology.productVInclusionHomotopy X) n,
    singularHomologyMap_comp]
  rfl

/-- The fold on homology sums the two coordinates. -/
theorem SingularHomology.productFold_homology (X : Type) [TopologicalSpace X] (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (X ⊕ X) n) :
    SingularMayerVietoris.singularHomologyMap (CircleTopology.foldMap X) n a =
      (sumHomologyEquiv X X n a).1 + (sumHomologyEquiv X X n a).2 :=
  sumHomologyEquiv_fold n a

/-- The `U` intersection map on homology is the fold. -/
theorem SingularHomology.productIntersectionToU_homology (X : Type) [TopologicalSpace X]
    (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (CircleTopology.productU X ∩ CircleTopology.productV X :
          Set ((SingularHomology.CircleTopology.Circle) × X))
        n) :
    homotopyEquivHomologyEquiv (CircleTopology.productUHomotopyEquiv X) n
        (SingularMayerVietoris.singularHomologyMap (CircleTopology.productIntersectionToU X) n
          a) =
      (productIntersectionHomologyEquiv X n a).1 + (productIntersectionHomologyEquiv X n a).2 := by
  change
    SingularMayerVietoris.singularHomologyMap (CircleTopology.productUHomotopyEquiv X).toFun n
        (SingularMayerVietoris.singularHomologyMap (CircleTopology.productIntersectionToU X) n
          a) =
      _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    CircleTopology.productIntersectionToU_fold, singularHomologyMap_comp]
  exact productFold_homology X n _

/-- The `V` intersection map on homology is the fold. -/
theorem SingularHomology.productIntersectionToV_homology (X : Type) [TopologicalSpace X]
    (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (CircleTopology.productU X ∩ CircleTopology.productV X :
          Set ((SingularHomology.CircleTopology.Circle) × X))
        n) :
    homotopyEquivHomologyEquiv (CircleTopology.productVHomotopyEquiv X) n
        (SingularMayerVietoris.singularHomologyMap (CircleTopology.productIntersectionToV X) n
          a) =
      (productIntersectionHomologyEquiv X n a).1 + (productIntersectionHomologyEquiv X n a).2 := by
  change
    SingularMayerVietoris.singularHomologyMap (CircleTopology.productVHomotopyEquiv X).toFun n
        (SingularMayerVietoris.singularHomologyMap (CircleTopology.productIntersectionToV X) n
          a) =
      _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    CircleTopology.productIntersectionToV_fold, singularHomologyMap_comp]
  exact productFold_homology X n _

/-- The left Mayer–Vietoris map in product coordinates. -/
theorem SingularHomology.circleProductLeftHomologyMap_apply (X : Type)
    [TopologicalSpace X] (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (CircleTopology.productU X ∩ CircleTopology.productV X :
          Set ((SingularHomology.CircleTopology.Circle) × X))
        n) :
    productArcHomologyEquiv X n
        (SingularMayerVietoris.leftHomologyMap (CircleTopology.productU X)
          (CircleTopology.productV X) n a) =
      ((productIntersectionHomologyEquiv X n a).1 + (productIntersectionHomologyEquiv X n a).2,
        -((productIntersectionHomologyEquiv X n a).1 +
            (productIntersectionHomologyEquiv X n a).2)) := by
  rw [SingularMayerVietoris.leftHomologyMap_apply]
  change
    (homotopyEquivHomologyEquiv (CircleTopology.productUHomotopyEquiv X) n
          (SingularMayerVietoris.singularHomologyMap (CircleTopology.productIntersectionToU X) n
            a),
        homotopyEquivHomologyEquiv (CircleTopology.productVHomotopyEquiv X) n
          (-SingularMayerVietoris.singularHomologyMap (CircleTopology.productIntersectionToV X) n
              a)) =
      _
  rw [map_neg, productIntersectionToU_homology, productIntersectionToV_homology]

/-- The right Mayer–Vietoris map in product coordinates. -/
theorem SingularHomology.circleProductRightHomologyMap_apply (X : Type)
    [TopologicalSpace X] (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology (CircleTopology.productU X) n ×
        SingularMayerVietoris.SingularHomology (CircleTopology.productV X) n) :
    SingularMayerVietoris.rightHomologyMap (CircleTopology.productU X) (CircleTopology.productV X)
        n a =
      circleSectionHomology X n
        ((productArcHomologyEquiv X n a).1 + (productArcHomologyEquiv X n a).2) := by
  rw [SingularMayerVietoris.rightHomologyMap_apply]
  change
    SingularMayerVietoris.singularHomologyMap (CircleTopology.productUInclusion X) n a.1 +
        SingularMayerVietoris.singularHomologyMap (CircleTopology.productVInclusion X) n a.2 =
      _
  rw [productUInclusion_homology, productVInclusion_homology]
  exact (map_add (circleSectionHomology X n) _ _).symm

/-- The Mayer–Vietoris connecting map of the circle product. -/
abbrev SingularHomology.circleMayerVietorisConnecting (X : Type) [TopologicalSpace X]
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology ((SingularHomology.CircleTopology.Circle) × X)
        (n + 1) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology
        (CircleTopology.productU X ∩ CircleTopology.productV X :
          Set ((SingularHomology.CircleTopology.Circle) × X))
        n :=
  SingularMayerVietoris.connectingHomomorphism (CircleTopology.productU X)
    (CircleTopology.productV X) (CircleTopology.productU_open X) (CircleTopology.productV_open X)
    (CircleTopology.product_cover X) n

/-- The connecting map in `X × X` coordinates. -/
def SingularHomology.circleBoundaryCoordinates (X : Type) [TopologicalSpace X] (n : ℕ) :
    SingularMayerVietoris.SingularHomology ((SingularHomology.CircleTopology.Circle) × X)
        (n + 1) →ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology X n × SingularMayerVietoris.SingularHomology X n) :=
  (productIntersectionHomologyEquiv X n).toLinearMap.comp (circleMayerVietorisConnecting X n)

/-- The boundary coordinates have range the fold kernel. -/
theorem SingularHomology.circleBoundaryCoordinates_range (X : Type) [TopologicalSpace X]
    (n : ℕ) :
    LinearMap.range (circleBoundaryCoordinates X n) =
      LinearMap.ker (pairSumMap (SingularMayerVietoris.SingularHomology X n)) := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    have hb :
      circleMayerVietorisConnecting X n b ∈ LinearMap.range (circleMayerVietorisConnecting X n) :=
      ⟨b, rfl⟩
    rw [SingularMayerVietoris.exact_at_intersection (CircleTopology.productU X)
        (CircleTopology.productV X) (CircleTopology.productU_open X)
        (CircleTopology.productV_open X) (CircleTopology.product_cover X)] at hb
    have he := congrArg (productArcHomologyEquiv X n) hb
    rw [circleProductLeftHomologyMap_apply, map_zero] at he
    exact congrArg Prod.fst he
  · intro ha
    have ha' : a.1 + a.2 = 0 := ha
    have hleft :
      SingularMayerVietoris.leftHomologyMap (CircleTopology.productU X)
          (CircleTopology.productV X) n ((productIntersectionHomologyEquiv X n).symm a) =
        0 := by
      apply (productArcHomologyEquiv X n).injective
      rw [circleProductLeftHomologyMap_apply, LinearEquiv.apply_symm_apply, map_zero]
      exact Prod.ext ha' (ha' ▸ neg_zero)
    have hi :
      (productIntersectionHomologyEquiv X n).symm a ∈
        LinearMap.range (circleMayerVietorisConnecting X n) := by
      rw [SingularMayerVietoris.exact_at_intersection (CircleTopology.productU X)
          (CircleTopology.productV X) (CircleTopology.productU_open X)
          (CircleTopology.productV_open X) (CircleTopology.product_cover X)]
      exact hleft
    obtain ⟨b, hb⟩ := hi
    refine ⟨b, ?_⟩
    change productIntersectionHomologyEquiv X n (circleMayerVietorisConnecting X n b) = a
    rw [hb, LinearEquiv.apply_symm_apply]

/-- The right map has range the section image. -/
theorem SingularHomology.circleProductRightHomologyMap_range (X : Type)
    [TopologicalSpace X] (n : ℕ) :
    LinearMap.range
        (SingularMayerVietoris.rightHomologyMap (CircleTopology.productU X)
          (CircleTopology.productV X) n) =
      LinearMap.range (circleSectionHomology X n) := by
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    exact
      ⟨(productArcHomologyEquiv X n a).1 + (productArcHomologyEquiv X n a).2,
        (circleProductRightHomologyMap_apply X n a).symm⟩
  · rintro ⟨a, rfl⟩
    refine ⟨(productArcHomologyEquiv X n).symm (a, 0), ?_⟩
    rw [circleProductRightHomologyMap_apply, LinearEquiv.apply_symm_apply]
    exact congrArg (circleSectionHomology X n) (add_zero a)

/-- The section image is the boundary-coordinates kernel. -/
theorem SingularHomology.circleBoundaryCoordinates_ker (X : Type) [TopologicalSpace X]
    (n : ℕ) :
    LinearMap.range (circleSectionHomology X (n + 1)) =
      LinearMap.ker (circleBoundaryCoordinates X n) := by
  rw [circleBoundaryCoordinates, SingularMayerVietoris.rightTransport_second_ker]
  rw [←
    SingularMayerVietoris.exact_at_ambient (CircleTopology.productU X) (CircleTopology.productV X)
      (CircleTopology.productU_open X) (CircleTopology.productV_open X)
      (CircleTopology.product_cover X)]
  exact (circleProductRightHomologyMap_range X (n + 1)).symm

/-- The circle-product boundary `H_{n+1}(S¹ × X) → H_n(X)`. -/
def SingularHomology.circleBoundary (X : Type) [TopologicalSpace X] (n : ℕ) :
    SingularMayerVietoris.SingularHomology ((SingularHomology.CircleTopology.Circle) × X)
        (n + 1) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology X n :=
  (negativeFirstMap (SingularMayerVietoris.SingularHomology X n)).comp
    (circleBoundaryCoordinates X n)

/-- The circle boundary is the negated first coordinate. -/
@[simp]
theorem SingularHomology.circleBoundary_apply (X : Type) [TopologicalSpace X] (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ((SingularHomology.CircleTopology.Circle) × X) (n + 1)) :
    circleBoundary X n a = -(circleBoundaryCoordinates X n a).1 :=
  rfl

/-- The circle boundary is surjective. -/
theorem SingularHomology.circleBoundary_surjective (X : Type) [TopologicalSpace X]
    (n : ℕ) : Function.Surjective (circleBoundary X n) :=
  circleBoundary_negativeFirst_surjective (circleBoundaryCoordinates X n)
    (circleBoundaryCoordinates_range X n)

/-- The section image is the boundary kernel. -/
theorem SingularHomology.circleBoundary_exact (X : Type) [TopologicalSpace X] (n : ℕ) :
    LinearMap.range (circleSectionHomology X (n + 1)) = LinearMap.ker (circleBoundary X n) :=
  (circleBoundaryCoordinates_ker X n).trans
    (circleBoundary_negativeFirst_ker (circleBoundaryCoordinates X n)
        (circleBoundaryCoordinates_range X n)).symm

/-- The Kuenneth splitting for the circle: `H_n(S^1 x X) is H_n(X) + H_{n-1}(X)` naturally in `X` (Hatcher, Algebraic Topology, Corollary 2.11 content for one factor `S^1`). -/
def SingularHomology.circleProductHomologyEquiv (X : Type) [TopologicalSpace X] (n : ℕ) :
    SingularMayerVietoris.SingularHomology ((SingularHomology.CircleTopology.Circle) × X)
        (n + 1) ≃ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology X (n + 1) ×
        SingularMayerVietoris.SingularHomology X n) :=
  circleSplitExactEquiv (circleSectionHomology X (n + 1)) (circleProjectionHomology X (n + 1))
    (circleBoundaryCoordinates X n) (circleProjection_section X (n + 1))
    (circleBoundaryCoordinates_ker X n) (circleBoundaryCoordinates_range X n)

/-- The product homology equivalence computes the boundary pair. -/
@[simp]
theorem SingularHomology.circleProductHomologyEquiv_apply (X : Type) [TopologicalSpace X]
    (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ((SingularHomology.CircleTopology.Circle) × X) (n + 1)) :
    circleProductHomologyEquiv X n a =
      (circleProjectionHomology X (n + 1) a, circleBoundary X n a) :=
  rfl

/-- A section class maps to `(a, 0)`. -/
@[simp]
theorem SingularHomology.circleProductHomologyEquiv_section (X : Type)
    [TopologicalSpace X] (n : ℕ) (a : SingularMayerVietoris.SingularHomology X (n + 1)) :
    circleProductHomologyEquiv X n (circleSectionHomology X (n + 1) a) = (a, 0) :=
  circleSplitExactEquiv_apply_inclusion _ _ _ _ _ _ a

/-- The degree-zero section map is surjective. -/
theorem SingularHomology.circleSectionHomology_zero_surjective (X : Type)
    [TopologicalSpace X] : Function.Surjective (circleSectionHomology X 0) := by
  intro b
  obtain ⟨a, ha⟩ :=
    SingularMayerVietoris.rightHomologyMap_zero_surjective (CircleTopology.productU X)
      (CircleTopology.productV X) (CircleTopology.productU_open X)
      (CircleTopology.productV_open X) (CircleTopology.product_cover X) b
  exact
    ⟨(productArcHomologyEquiv X 0 a).1 + (productArcHomologyEquiv X 0 a).2,
      (circleProductRightHomologyMap_apply X 0 a).symm.trans ha⟩

/-- The degree-zero homology of `S¹ × X` is `H_0(X)`. -/
def SingularHomology.circleProductHomologyZeroEquiv (X : Type) [TopologicalSpace X] :
    SingularMayerVietoris.SingularHomology ((SingularHomology.CircleTopology.Circle) × X)
        0 ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology X 0
    where
  toLinearMap := circleProjectionHomology X 0
  invFun := circleSectionHomology X 0
  left_inv
    b := by
    obtain ⟨a, rfl⟩ := circleSectionHomology_zero_surjective X b
    exact
      congrArg (circleSectionHomology X 0) (LinearMap.congr_fun (circleProjection_section X 0) a)
  right_inv a := LinearMap.congr_fun (circleProjection_section X 0) a

/-! ### Connecting maps and point classes -/

/-- The categorical cycle constructor agrees with the cycle subtype. -/
theorem SingularMayerVietoris.ModuleHomology.cyclesMk_eq_moduleCatCyclesIso_inv
    (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    (c : SingularMayerVietoris.ModuleHomology.Cycle K n) (j : ℕ)
    (hj : (ComplexShape.down ℕ).next n = j) (hc : (K.d n j).hom c.1 = 0) :
    K.cyclesMk c.1 j hj hc = ((K.sc n).moduleCatCyclesIso.inv).hom c := by
  apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
  have h₁ : (K.iCycles n).hom (K.cyclesMk c.1 j hj hc) = c.1 := K.i_cyclesMk c.1 j hj hc
  have h₂ := congrArg (fun f => f.hom c) ((K.sc n).moduleCatCyclesIso_inv_iCycles)
  exact h₁.trans h₂.symm

/-- The cycle class is the homology class of the cycle. -/
theorem SingularMayerVietoris.ModuleHomology.cycleClass_eq_homologyClassOfCycle_of_next
    (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    (c : SingularMayerVietoris.ModuleHomology.Cycle K n) (j : ℕ)
    (hj : (ComplexShape.down ℕ).next n = j) (hc : (K.d n j).hom c.1 = 0) :
    cycleClass K n c = SingularMayerVietoris.homologyClassOfCycle K c.1 j hj hc := by
  rw [SingularMayerVietoris.homologyClassOfCycle, cyclesMk_eq_moduleCatCyclesIso_inv]
  exact (congrArg (fun f => f.hom c) ((K.sc n).moduleCatCyclesIso_inv_π)).symm

/-- The cycle class equals the homology class at the next index. -/
theorem SingularMayerVietoris.ModuleHomology.cycleClass_eq_homologyClassOfCycle
    (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    (c : SingularMayerVietoris.ModuleHomology.Cycle K n) :
    cycleClass K n c =
      SingularMayerVietoris.homologyClassOfCycle K c.1 (n - 1) (next_nat n)
        (cycle_condition K n c) :=
  cycleClass_eq_homologyClassOfCycle_of_next K n c (n - 1) (next_nat n) (cycle_condition K n c)

/-- The connecting map of a short exact sequence on cycle classes. -/
theorem SingularHomology.connectingMap_cycleClass
    {S : CategoryTheory.ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ)} (hS : S.ShortExact)
    (n : ℕ) (c : SingularMayerVietoris.ModuleHomology.Cycle S.X₃ (n + 1)) (z₂ : S.X₂.X (n + 1))
    (hz₂ : (S.g.f (n + 1)).hom z₂ = c.1) (z₁ : SingularMayerVietoris.ModuleHomology.Cycle S.X₁ n)
    (hz₁ : (S.f.f n).hom z₁.1 = (S.X₂.d (n + 1) n).hom z₂) :
    SingularMayerVietoris.connectingMap hS n
        (SingularMayerVietoris.ModuleHomology.cycleClass S.X₃ (n + 1) c) =
      SingularMayerVietoris.ModuleHomology.cycleClass S.X₁ n z₁ := by
  have hc : (S.X₃.d (n + 1) n).hom c.1 = 0 := by
    have h := SingularMayerVietoris.ModuleHomology.cycle_condition S.X₃ (n + 1) c
    rw [Nat.add_sub_cancel] at h
    exact h
  have hnext : (ComplexShape.down ℕ).next (n + 1) = n := (ComplexShape.down ℕ).next_eq' (by simp)
  have h₃ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_eq_homologyClassOfCycle_of_next S.X₃ (n + 1) c
      n hnext hc
  have hδ := SingularMayerVietoris.connectingMap_homologyClassOfCycle hS n c.1 hc z₂ hz₂ z₁.1 hz₁
  have h₁ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_eq_homologyClassOfCycle_of_next S.X₁ n z₁
      ((ComplexShape.down ℕ).next n) rfl
      (SingularMayerVietoris.connectingMap_lift_is_cycle hS n z₂ z₁.1 hz₁ _)
  exact (congrArg (SingularMayerVietoris.connectingMap hS n) h₃).trans (hδ.trans h₁.symm)

/-- The Mayer–Vietoris connecting map on small-complex cycle classes. -/
theorem SingularHomology.smallConnectingMap_cycleClass {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ)
    (c :
      SingularMayerVietoris.ModuleHomology.Cycle (SingularMayerVietoris.smallComplex U V) (n + 1))
    (z₂ : (SingularMayerVietoris.middleComplex U V).X (n + 1))
    (hz₂ : ((SingularMayerVietoris.rightMap U V).f (n + 1)).hom z₂ = c.1)
    (z₁ :
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex (U ∩ V : Set X))
        n)
    (hz₁ :
      ((SingularMayerVietoris.leftMap U V).f n).hom z₁.1 =
        ((SingularMayerVietoris.middleComplex U V).d (n + 1) n).hom z₂) :
    SingularMayerVietoris.smallConnectingMap U V n
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularMayerVietoris.smallComplex U V)
          (n + 1) c) =
      SingularMayerVietoris.ModuleHomology.cycleClass
        (SingularChains.singularComplex (U ∩ V : Set X)) n z₁ :=
  connectingMap_cycleClass (SingularMayerVietoris.chainSequence_shortExact U V) n c z₂ hz₂ z₁ hz₁

/-- The connecting homomorphism on cycle classes. -/
theorem SingularHomology.connectingHomomorphism_cycleClass {X : Type}
    [TopologicalSpace X] (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (n : ℕ)
    (c :
      SingularMayerVietoris.ModuleHomology.Cycle (SingularMayerVietoris.smallComplex U V) (n + 1))
    (z₂ : (SingularMayerVietoris.middleComplex U V).X (n + 1))
    (hz₂ : ((SingularMayerVietoris.rightMap U V).f (n + 1)).hom z₂ = c.1)
    (z₁ :
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex (U ∩ V : Set X))
        n)
    (hz₁ :
      ((SingularMayerVietoris.leftMap U V).f n).hom z₁.1 =
        ((SingularMayerVietoris.middleComplex U V).d (n + 1) n).hom z₂) :
    SingularMayerVietoris.connectingHomomorphism U V hU hV hcover n
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) (n + 1)
          (SingularMayerVietoris.ModuleHomology.mapCycles
            (SingularMayerVietoris.smallInclusion U V) (n + 1) c)) =
      SingularMayerVietoris.ModuleHomology.cycleClass
        (SingularChains.singularComplex (U ∩ V : Set X)) n z₁ := by
  rw [← SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass]
  change
    SingularMayerVietoris.connectingHomomorphism U V hU hV hcover n
        (SingularMayerVietoris.smallHomologyComparison U V (n + 1)
          (SingularMayerVietoris.ModuleHomology.cycleClass
            (SingularMayerVietoris.smallComplex U V) (n + 1) c)) =
      _
  rw [SingularMayerVietoris.connectingHomomorphism_comparison]
  exact smallConnectingMap_cycleClass U V n c z₂ hz₂ z₁ hz₁

/-- The zero-cycle of a point. -/
def SingularHomology.pointCycle {X : Type} [TopologicalSpace X] (x : X) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 0 :=
  SingularMayerVietoris.ModuleHomology.mkCycle (SingularChains.singularComplex X) 0
    (SingularChains.simplexChain X 0 (ContinuousMap.const (SingularChains.Simplex 0) x))
    (by
      have h := (SingularChains.singularComplex X).shape 0 0 (by simp)
      exact
        congrArg
          (fun f =>
            f.hom
              (SingularChains.simplexChain X 0 (ContinuousMap.const (SingularChains.Simplex 0) x)))
          h)

/-- The point cycle is the constant 0-simplex chain. -/
@[simp]
theorem SingularHomology.pointCycle_val {X : Type} [TopologicalSpace X] (x : X) :
    (pointCycle x).1 =
      SingularChains.simplexChain X 0 (ContinuousMap.const (SingularChains.Simplex 0) x) :=
  rfl

/-- The homology class of a point. -/
def SingularHomology.pointClass {X : Type} [TopologicalSpace X] (x : X) :
    SingularMayerVietoris.SingularHomology X 0 :=
  SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 0
    (pointCycle x)

/-- Mapping a point cycle gives the image point cycle. -/
@[simp]
theorem SingularHomology.mapCycles_pointCycle {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (x : X) :
    SingularMayerVietoris.ModuleHomology.mapCycles (SingularChains.singularChainMap f) 0
        (pointCycle x) =
      pointCycle (f x) := by
  apply Subtype.ext
  rw [SingularMayerVietoris.ModuleHomology.mapCycles_val, pointCycle_val, pointCycle_val]
  change
    SingularChains.inducedChain f 0
        (SingularChains.simplexChain X 0 (ContinuousMap.const (SingularChains.Simplex 0) x)) =
      _
  rw [SingularChains.inducedChain_simplex]
  apply congrArg (SingularChains.simplexChain Y 0)
  apply ContinuousMap.ext
  intro t
  rfl

/-- The induced map sends a point class to the image point class. -/
@[simp]
theorem SingularHomology.singularHomologyMap_pointClass {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (x : X) :
    SingularMayerVietoris.singularHomologyMap f 0 (pointClass x) = pointClass (f x) := by
  change
    (HomologicalComplex.homologyMap (SingularChains.singularChainMap f) 0).hom
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 0
          (pointCycle x)) =
      _
  rw [SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass, mapCycles_pointCycle]
  rfl

/-- The point cycle as a map from `ℤ` into the cycles. -/
def SingularHomology.pointCycleLift {X : Type} [TopologicalSpace X]
    (x : X) : ModuleCat.of ℤ ℤ ⟶ (SingularChains.singularComplex X).cycles 0 :=
  (SingularChains.singularComplex X).liftCycles
    ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := ModuleCat.of ℤ ℤ)
      (SingularChains.simplexIndex X 0 (ContinuousMap.const (SingularChains.Simplex 0) x)))
    0 (by simp) (by simp)

/-- The point class is the homology image of the cycle lift. -/
theorem SingularHomology.pointClass_eq_pointCycleLift {X : Type}
    [TopologicalSpace X] (x : X) :
    pointClass x =
      (SingularChains.singularComplex X).homologyπ 0 ((pointCycleLift x).hom 1) := by
  rw [pointClass, SingularMayerVietoris.ModuleHomology.cycleClass_eq_homologyClassOfCycle,
    SingularMayerVietoris.homologyClassOfCycle]
  apply congrArg ((SingularChains.singularComplex X).homologyπ 0).hom
  apply
    (ModuleCat.mono_iff_injective ((SingularChains.singularComplex X).iCycles 0)).mp inferInstance
  have h₁ :=
    (SingularChains.singularComplex X).i_cyclesMk (pointCycle x).1 (0 - 1)
      (SingularMayerVietoris.ModuleHomology.next_nat 0)
      (SingularMayerVietoris.ModuleHomology.cycle_condition (SingularChains.singularComplex X) 0
        (pointCycle x))
  have h₂ :=
    congrArg (fun f => f.hom 1)
      ((SingularChains.singularComplex X).liftCycles_i
        ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := ModuleCat.of ℤ ℤ)
          (SingularChains.simplexIndex X 0 (ContinuousMap.const (SingularChains.Simplex 0) x)))
        0 (by simp) (by simp))
  exact h₁.trans h₂.symm

/-- The augmentation of a point class is `1`. -/
@[simp]
theorem SingularHomology.pointClass_augmentation {X : Type} [TopologicalSpace X]
    (x : X) : ((TopCat.of X).singularHomology₀ε (ModuleCat.of ℤ ℤ)).hom (pointClass x) = 1 := by
  rw [pointClass_eq_pointCycleLift]
  exact
    congrArg (fun f => f.hom 1)
      ((TopCat.toSSet.obj (TopCat.of X)).liftCycles_ιChainComplex_homologyπ_homology₀ε
        (ModuleCat.of ℤ ℤ)
        (SingularChains.simplexIndex X 0 (ContinuousMap.const (SingularChains.Simplex 0) x)))

/-- The degree-zero equivalence sends a point class to `1`. -/
@[simp]
theorem SingularHomology.connectedHomologyZeroEquiv_pointClass {X : Type}
    [TopologicalSpace X] [PathConnectedSpace X] (x : X) :
    connectedHomologyZeroEquiv X (pointClass x) = 1 :=
  pointClass_augmentation x

/-- In a path-connected space every degree-zero class is a multiple of a point class. -/
theorem SingularHomology.eq_zsmul_pointClass {X : Type} [TopologicalSpace X]
    [PathConnectedSpace X] (x : X) (a : SingularMayerVietoris.SingularHomology X 0) :
    a = connectedHomologyZeroEquiv X a • pointClass x := by
  apply (connectedHomologyZeroEquiv X).injective
  rw [map_zsmul, connectedHomologyZeroEquiv_pointClass, zsmul_eq_mul, mul_one]
  simp

/-- The degree-zero equivalence is natural. -/
theorem SingularHomology.connectedHomologyZeroEquiv_natural {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [PathConnectedSpace X] [PathConnectedSpace Y]
    (f : C(X, Y)) (a : SingularMayerVietoris.SingularHomology X 0) :
    connectedHomologyZeroEquiv Y (SingularMayerVietoris.singularHomologyMap f 0 a) =
      connectedHomologyZeroEquiv X a := by
  let x : X := Classical.arbitrary X
  calc
    connectedHomologyZeroEquiv Y (SingularMayerVietoris.singularHomologyMap f 0 a) =
        connectedHomologyZeroEquiv Y
          (SingularMayerVietoris.singularHomologyMap f 0
            (connectedHomologyZeroEquiv X a • pointClass x)) :=
      congrArg
        (fun b => connectedHomologyZeroEquiv Y (SingularMayerVietoris.singularHomologyMap f 0 b))
        (eq_zsmul_pointClass x a)
    _ = connectedHomologyZeroEquiv X a := by
      rw [map_zsmul, map_zsmul, singularHomologyMap_pointClass,
        connectedHomologyZeroEquiv_pointClass, zsmul_eq_mul, mul_one]
      simp

/-! ### Circle homology in low degrees -/

/-- The first homology of a contractible-type space is trivial. -/
def SingularHomology.trivialFirstEquiv (A B : Type*) [AddCommGroup A]
    [AddCommGroup B] [Module ℤ B] [Subsingleton A] : (A × B) ≃ₗ[ℤ] B :=
  ({    toFun a := a.2
        invFun b := (0, b)
        left_inv _ := Prod.ext (Subsingleton.elim _ _) rfl
        right_inv _ := rfl
        map_add' _ _ := rfl } : (A × B) ≃+ B).toIntLinearEquiv

/-- The first homology of the circle is `ℤ`. -/
def SingularHomology.circleHomologyOneEquiv :
    SingularMayerVietoris.SingularHomology (SingularHomology.CircleTopology.Circle)
        1 ≃ₗ[ℤ]
      ℤ := by
  letI := point_homology_subsingleton 1 (by decide)
  exact
    ((homeomorphHomologyEquiv
              (Homeomorph.prodUnique (SingularHomology.CircleTopology.Circle) Unit).symm
              1).trans
          (circleProductHomologyEquiv Unit 0)).trans
      ((trivialFirstEquiv (SingularMayerVietoris.SingularHomology Unit 1)
            (SingularMayerVietoris.SingularHomology Unit 0)).trans
        pointHomologyZeroEquiv)

/-- The circle `H₁` equivalence computes the class. -/
theorem SingularHomology.circleHomologyOneEquiv_apply
    (a :
      SingularMayerVietoris.SingularHomology (SingularHomology.CircleTopology.Circle)
        1) :
    circleHomologyOneEquiv a =
      pointHomologyZeroEquiv
        (circleBoundary Unit 0
          (homeomorphHomologyEquiv
            (Homeomorph.prodUnique (SingularHomology.CircleTopology.Circle) Unit).symm 1
            a)) :=
  rfl

/-- The higher homology of the circle is trivial. -/
theorem SingularHomology.circle_homology_subsingleton (n : ℕ) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (SingularHomology.CircleTopology.Circle)
        (n + 2)) := by
  let := point_homology_subsingleton (n + 2) (Nat.succ_ne_zero _)
  let := point_homology_subsingleton (n + 1) (Nat.succ_ne_zero _)
  exact
    ((homeomorphHomologyEquiv
            (Homeomorph.prodUnique (SingularHomology.CircleTopology.Circle) Unit).symm
            (n + 2)).trans
        (circleProductHomologyEquiv Unit (n + 1))).injective.subsingleton
section

open SingularHomology

def PeriodTorusHigherHomology.circleProductMap {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :
    C((SingularHomology.CircleTopology.Circle) × X,
      (SingularHomology.CircleTopology.Circle) × Y) :=
  ⟨fun z => (z.1, f z.2), continuous_fst.prodMk (f.continuous.comp continuous_snd)⟩

def PeriodTorusHigherHomology.intersectionProductMap {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :
    C(↥(CircleTopology.productU X ∩ CircleTopology.productV X),
      ↥(CircleTopology.productU Y ∩ CircleTopology.productV Y)) :=
  ⟨fun z => ⟨circleProductMap f z.val, z.property⟩,
    ((circleProductMap f).continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem PeriodTorusHigherHomology.circleProductMap_projection {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :
    (CircleTopology.productProjection Y).comp (circleProductMap f) =
      f.comp (CircleTopology.productProjection X) :=
  rfl

theorem PeriodTorusHigherHomology.intersectionProductMap_homotopyEquiv {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    (CircleTopology.productIntersectionHomotopyEquiv Y).toFun.comp (intersectionProductMap f) =
      (CircleTopology.sumContinuousMap f f).comp
        (CircleTopology.productIntersectionHomotopyEquiv X).toFun := by
  apply ContinuousMap.ext
  intro z
  let c : ↥(CircleTopology.arcU ∩ CircleTopology.arcV) := ⟨z.val.1, z.property⟩
  change
    Sum.map (fun t : Set.Ioo (0 : ℝ) (1 / 2) × Y => t.2)
        (fun t : Set.Ioo (1 / 2 : ℝ) 1 × Y => t.2)
        (Homeomorph.sumProdDistrib (CircleTopology.intersectionHomeomorph c, f z.val.2)) =
      Sum.map f f
        (Sum.map (fun t : Set.Ioo (0 : ℝ) (1 / 2) × X => t.2)
          (fun t : Set.Ioo (1 / 2 : ℝ) 1 × X => t.2)
          (Homeomorph.sumProdDistrib (CircleTopology.intersectionHomeomorph c, z.val.2)))
  cases h : CircleTopology.intersectionHomeomorph c <;> rfl

theorem PeriodTorusHigherHomology.circleProjectionHomology_naturality {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ) :
    (circleProjectionHomology Y n).comp
        (SingularMayerVietoris.singularHomologyMap (circleProductMap f) n) =
      (SingularMayerVietoris.singularHomologyMap f n).comp (circleProjectionHomology X n) := by
  rw [← singularHomologyMap_comp, circleProductMap_projection, singularHomologyMap_comp]

theorem PeriodTorusHigherHomology.sumHomologyEquiv_naturality {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {X' Y' : Type} [TopologicalSpace X'] [TopologicalSpace Y'] (f : C(X, X'))
    (g : C(Y, Y')) (n : ℕ) (a : SingularMayerVietoris.SingularHomology (X ⊕ Y) n) :
    sumHomologyEquiv X' Y' n
        (SingularMayerVietoris.singularHomologyMap (CircleTopology.sumContinuousMap f g) n a) =
      (SingularMayerVietoris.singularHomologyMap f n (sumHomologyEquiv X Y n a).1,
        SingularMayerVietoris.singularHomologyMap g n (sumHomologyEquiv X Y n a).2) := by
  have hsum :
    CircleTopology.sumContinuousMap f g =
      sumElimMap ((sumInlMap X' Y').comp f) ((sumInrMap X' Y').comp g) := by
    ext x
    cases x <;> rfl
  simp only [hsum, sumHomologyEquiv_sumElim, singularHomologyMap_comp, LinearMap.comp_apply,
    map_add, sumHomologyEquiv_inl, sumHomologyEquiv_inr, Prod.mk_add_mk, add_zero, zero_add]

theorem PeriodTorusHigherHomology.productIntersectionHomologyEquiv_naturality {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (CircleTopology.productU X ∩ CircleTopology.productV X :
          Set ((SingularHomology.CircleTopology.Circle) × X))
        n) :
    productIntersectionHomologyEquiv Y n
        (SingularMayerVietoris.singularHomologyMap (intersectionProductMap f) n a) =
      (SingularMayerVietoris.singularHomologyMap f n (productIntersectionHomologyEquiv X n a).1,
        SingularMayerVietoris.singularHomologyMap f n
          (productIntersectionHomologyEquiv X n a).2) := by
  have h :=
    congrArg (fun g => SingularMayerVietoris.singularHomologyMap g n)
      (intersectionProductMap_homotopyEquiv f)
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at h
  calc
    _ =
        sumHomologyEquiv Y Y n
          (SingularMayerVietoris.singularHomologyMap (CircleTopology.sumContinuousMap f f) n
            (SingularMayerVietoris.singularHomologyMap
              (CircleTopology.productIntersectionHomotopyEquiv X).toFun n a)) :=
      congrArg (sumHomologyEquiv Y Y n) (LinearMap.congr_fun h a)
    _ = _ := sumHomologyEquiv_naturality f f n _

theorem PeriodTorusHigherHomology.circleProductMap_mapsToU {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :
    Set.MapsTo (circleProductMap f) (CircleTopology.productU X) (CircleTopology.productU Y) :=
  fun _ h => h

theorem PeriodTorusHigherHomology.circleProductMap_mapsToV {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :
    Set.MapsTo (circleProductMap f) (CircleTopology.productV X) (CircleTopology.productV Y) :=
  fun _ h => h

theorem PeriodTorusHigherHomology.circleProductIntersectionRestriction_eq {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    SingularMayerVietoris.intersectionRestriction (circleProductMap f) (CircleTopology.productU X)
        (CircleTopology.productV X) (CircleTopology.productU Y) (CircleTopology.productV Y)
        (circleProductMap_mapsToU f) (circleProductMap_mapsToV f) =
      intersectionProductMap f :=
  rfl

theorem PeriodTorusHigherHomology.circleMayerVietorisConnecting_naturality {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ) :
    (SingularMayerVietoris.singularHomologyMap (intersectionProductMap f) n).comp
        (circleMayerVietorisConnecting X n) =
      (circleMayerVietorisConnecting Y n).comp
        (SingularMayerVietoris.singularHomologyMap (circleProductMap f) (n + 1)) := by
  have h :=
    SingularMayerVietoris.connectingHomomorphism_naturality (circleProductMap f)
      (CircleTopology.productU X) (CircleTopology.productV X) (CircleTopology.productU Y)
      (CircleTopology.productV Y) (circleProductMap_mapsToU f) (circleProductMap_mapsToV f)
      (CircleTopology.productU_open X) (CircleTopology.productV_open X)
      (CircleTopology.product_cover X) (CircleTopology.productU_open Y)
      (CircleTopology.productV_open Y) (CircleTopology.product_cover Y) n
  rw [circleProductIntersectionRestriction_eq] at h
  exact h

theorem PeriodTorusHigherHomology.circleBoundaryCoordinates_naturality {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ((SingularHomology.CircleTopology.Circle) × X) (n + 1)) :
    circleBoundaryCoordinates Y n
        (SingularMayerVietoris.singularHomologyMap (circleProductMap f) (n + 1) a) =
      (SingularMayerVietoris.singularHomologyMap f n (circleBoundaryCoordinates X n a).1,
        SingularMayerVietoris.singularHomologyMap f n (circleBoundaryCoordinates X n a).2) := by
  have h := LinearMap.congr_fun (circleMayerVietorisConnecting_naturality f n) a
  change
    SingularMayerVietoris.singularHomologyMap (intersectionProductMap f) n
        (circleMayerVietorisConnecting X n a) =
      circleMayerVietorisConnecting Y n
        (SingularMayerVietoris.singularHomologyMap (circleProductMap f) (n + 1) a) at h
  change
    productIntersectionHomologyEquiv Y n
        (circleMayerVietorisConnecting Y n
          (SingularMayerVietoris.singularHomologyMap (circleProductMap f) (n + 1) a)) =
      _
  rw [← h]
  exact productIntersectionHomologyEquiv_naturality f n (circleMayerVietorisConnecting X n a)

theorem PeriodTorusHigherHomology.circleBoundary_naturality {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ((SingularHomology.CircleTopology.Circle) × X) (n + 1)) :
    circleBoundary Y n
        (SingularMayerVietoris.singularHomologyMap (circleProductMap f) (n + 1) a) =
      SingularMayerVietoris.singularHomologyMap f n (circleBoundary X n a) := by
  change
    -(circleBoundaryCoordinates Y n
            (SingularMayerVietoris.singularHomologyMap (circleProductMap f) (n + 1) a)).1 =
      SingularMayerVietoris.singularHomologyMap f n (-(circleBoundaryCoordinates X n a).1)
  rw [circleBoundaryCoordinates_naturality, map_neg]

theorem PeriodTorusHigherHomology.circleProductHomologyEquiv_naturality {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ((SingularHomology.CircleTopology.Circle) × X) (n + 1)) :
    circleProductHomologyEquiv Y n
        (SingularMayerVietoris.singularHomologyMap (circleProductMap f) (n + 1) a) =
      (SingularMayerVietoris.singularHomologyMap f (n + 1) (circleProductHomologyEquiv X n a).1,
        SingularMayerVietoris.singularHomologyMap f n (circleProductHomologyEquiv X n a).2) := by
  apply Prod.ext
  · exact LinearMap.congr_fun (circleProjectionHomology_naturality f (n + 1)) a
  · exact circleBoundary_naturality f n a

theorem PeriodTorusHigherHomology.circleProductHomologyEquiv_symm_naturality {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology X (n + 1) ×
        SingularMayerVietoris.SingularHomology X n) :
    SingularMayerVietoris.singularHomologyMap (circleProductMap f) (n + 1)
        ((circleProductHomologyEquiv X n).symm a) =
      (circleProductHomologyEquiv Y n).symm
        (SingularMayerVietoris.singularHomologyMap f (n + 1) a.1,
          SingularMayerVietoris.singularHomologyMap f n a.2) := by
  apply (circleProductHomologyEquiv Y n).injective
  rw [circleProductHomologyEquiv_naturality, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

end

