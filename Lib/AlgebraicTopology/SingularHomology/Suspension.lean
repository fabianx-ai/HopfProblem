/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.AlgebraicTopology.SingularHomology.Chains
public import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
public import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Lib.Topology.Homotopy.Suspension
public import Lib.AlgebraicTopology.SingularHomology.Sphere

/-!
# The suspension isomorphism in singular homology

For a nonempty space `X`, the (reduced-degree) homology of the unreduced suspension is the
suspension homology of `X`, shifted: `H_n(Suspension X) ≅ H_{n-1}(X)` for `n ≥ 1`, and
`H_1(Suspension X) ≅ H_0(X) / (the sum of the components' classes)` for path components. In
this development the isomorphism is presented on the two-open cover `{north cone, south
cone}`:

* `SphereHomology.suspensionHomologyHigherEquiv` — the suspension isomorphism in degrees
  `n ≥ 2` (Hatcher, Cor 2.14's engine: `H̃_n(ΣX) ≅ H̃_{n-1}(X)`);
* `Suspension.contractibleCoverHomologyOneEquivKernel` — the degree-one story: the
  connecting map of the contractible two-cone cover presents `H_1(ΣX)` as the cokernel of
  `H_0(X ∩ V) → H_0(X)`; `sphereCircleHomologyEquiv` specializes to `H_*(S¹)`.

## Outline of the proof

1. *The two-cone cover.*  The suspension is covered by the north and south open cones; each
   cone is contractible (`northContraction`, `southContraction`), and their intersection is
   a cylinder-band (`middleBand`), so the Mayer–Vietoris sequence of
   `Lib/AlgebraicTopology/SingularHomology/MayerVietoris.lean` applies
   (`contractibleCoverConnecting_injective`, `contractibleCoverConnectingToKernel`).
2. *The split-exact algebra.*  The connecting triangle of the cover splits
   (`splitExactPair_*`, `intLinearMapOfAddHom`): a class of `H_0(X)` determines the
   suspension's `H_1` class, and higher classes shift (`suspensionSphereMap`,
   `suspensionHomologyHigherEquiv`).
3. *The circle.*  For `X = S⁰`, the suspension is the circle; `sphereCircleHomologyEquiv`
   identifies its homology with the presentation via `CircleTopology`
   (`Lib/AlgebraicTopology/SingularHomology/CircleProduct.lean`).

## Main definitions and results

* `SphereHomology.suspensionSphereMap`, `SphereHomology.suspensionHomologyHigherEquiv` :
  the suspension isomorphism in higher degrees.
* `Suspension.contractibleCoverHomologyOneEquivKernel` : `H_1(ΣX)` from the
  components of `X`.
* `SphereHomology.sphereCircleHomologyEquiv` : `H_*(S¹)`.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], Corollary 2.14 (suspension isomorphism
  for reduced homology) and the two-cone argument of its proof

## Tags

suspension isomorphism, Mayer–Vietoris, circle
-/



set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

@[expose] public noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-! ### Suspension of spheres -/

/-- The map from the suspension of the `n`-sphere to the `n+1`-sphere along latitudes. -/
def SphereHomology.suspensionSphereMap (n : ℕ) :
    Suspension (UnitSphere n) → UnitSphere (n + 1) :=
  Quotient.lift (fun p => Latitude.point n p.1 p.2)
    (fun p q h => (Latitude.point_eq_iff n p.1 q.1 p.2 q.2).mpr h)

/-- The suspension-to-sphere latitude map is continuous. -/
@[continuity, fun_prop]
theorem SphereHomology.suspensionSphereMap_continuous (n : ℕ) :
    Continuous (suspensionSphereMap n) :=
  Suspension.isQuotientMap_mk.continuous_iff.mpr (Latitude.point_continuous n)

/-- The suspension-to-sphere latitude map is injective. -/
theorem SphereHomology.suspensionSphereMap_injective (n : ℕ) :
    Function.Injective (suspensionSphereMap n) := by
  intro a b
  induction a using Quotient.inductionOn with
  | _ p =>
    induction b using Quotient.inductionOn with
    | _ q =>
      intro h
      exact Quotient.sound ((Latitude.point_eq_iff n p.1 q.1 p.2 q.2).mp h)

/-- The suspension-to-sphere latitude map is surjective. -/
theorem SphereHomology.suspensionSphereMap_surjective (n : ℕ) :
    Function.Surjective (suspensionSphereMap n) := by
  intro y
  obtain ⟨⟨t, x⟩, h⟩ := Latitude.point_surjective n y
  exact ⟨Suspension.mk t x, h⟩

/-- The suspension of the `n`-sphere is homeomorphic to the `n+1`-sphere. -/
def SphereHomology.suspensionSphereHomeomorph (n : ℕ) :
    Suspension (UnitSphere n) ≃ₜ UnitSphere (n + 1) :=
  Continuous.homeoOfEquivCompactToT2 (f :=
    Equiv.ofBijective (suspensionSphereMap n)
      ⟨suspensionSphereMap_injective n, suspensionSphereMap_surjective n⟩)
    (suspensionSphereMap_continuous n)

/-- The suspension-sphere homeomorphism sends `mk t x` to the latitude point. -/
@[simp]
theorem SphereHomology.suspensionSphereHomeomorph_mk (n : ℕ) (t : unitInterval)
    (x : UnitSphere n) :
    suspensionSphereHomeomorph n (Suspension.mk t x) = Latitude.point n t x :=
  rfl

/-- Spheres of positive dimension are path connected. -/
instance SphereHomology.unitSphere_pathConnectedSpace (n : ℕ) :
    PathConnectedSpace (UnitSphere (n + 1)) :=
  (suspensionSphereHomeomorph n).surjective.pathConnectedSpace
    (suspensionSphereHomeomorph n).continuous

/-! ### Split exact pairs -/

/-- A retraction together with exactness makes the pair map injective. -/
theorem SingularHomology.splitExactPair_injective {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [Module ℤ A] [Module ℤ B] [Module ℤ C]
    (i : A →ₗ[ℤ] B) (p : B →ₗ[ℤ] A) (d : B →ₗ[ℤ] C) (hpi : p.comp i = LinearMap.id)
    (hex : LinearMap.range i = LinearMap.ker d) : Function.Injective (p.prod d) := by
  intro b b' h
  have hp : p b = p b' := congrArg Prod.fst h
  have hd : d b = d b' := congrArg Prod.snd h
  have hb : b - b' ∈ LinearMap.ker d := by
    change d (b - b') = 0
    rw [map_sub, hd, sub_self]
  rw [← hex] at hb
  obtain ⟨a, ha⟩ := hb
  have hpa : p (i a) = a := LinearMap.congr_fun hpi a
  have ha0 : a = 0 := by
    calc
      a = p (i a) := hpa.symm
      _ = p (b - b') := (congrArg p ha)
      _ = 0 := by rw [map_sub, hp, sub_self]
  have hdiff : b - b' = 0 := by rw [← ha, ha0, map_zero]
  exact sub_eq_zero.mp hdiff

/-- A split exact pair with surjective quotient map gives a surjective pair map. -/
theorem SingularHomology.splitExactPair_surjective {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [Module ℤ A] [Module ℤ B] [Module ℤ C]
    (i : A →ₗ[ℤ] B) (p : B →ₗ[ℤ] A) (d : B →ₗ[ℤ] C) (hpi : p.comp i = LinearMap.id)
    (hex : LinearMap.range i = LinearMap.ker d) (hsurj : Function.Surjective d) :
    Function.Surjective (p.prod d) := by
  rintro ⟨a, c⟩
  obtain ⟨b, hb⟩ := hsurj c
  refine ⟨b + i (a - p b), ?_⟩
  apply Prod.ext
  · change p (b + i (a - p b)) = a
    have hpa : p (i (a - p b)) = a - p b := LinearMap.congr_fun hpi (a - p b)
    rw [map_add, hpa, ← add_sub_assoc, add_comm (p b) a, add_sub_cancel_right]
  · change d (b + i (a - p b)) = c
    have hi : i (a - p b) ∈ LinearMap.range i := ⟨a - p b, rfl⟩
    rw [hex] at hi
    have hdi : d (i (a - p b)) = 0 := hi
    rw [map_add, hdi, add_zero, hb]

/-- A split short exact datum gives an equivalence `B ≃ A × C`. -/
def SingularHomology.splitExactEquiv {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module ℤ A] [Module ℤ B] [Module ℤ C] (i : A →ₗ[ℤ] B) (p : B →ₗ[ℤ] A)
    (d : B →ₗ[ℤ] C) (hpi : p.comp i = LinearMap.id) (hex : LinearMap.range i = LinearMap.ker d)
    (hsurj : Function.Surjective d) : B ≃ₗ[ℤ] (A × C) :=
  ({
        Equiv.ofBijective (fun b : B => (p b, d b))
          ⟨splitExactPair_injective i p d hpi hex,
            splitExactPair_surjective i p d hpi hex hsurj⟩ with
        map_add' b b' := Prod.ext (map_add p b b') (map_add d b b') } :
      B ≃+ (A × C)).toIntLinearEquiv

/-- The split-exact equivalence computes the two components. -/
@[simp]
theorem SingularHomology.splitExactEquiv_apply {A B C : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [Module ℤ A] [Module ℤ B] [Module ℤ C] (i : A →ₗ[ℤ] B)
    (p : B →ₗ[ℤ] A) (d : B →ₗ[ℤ] C) (hpi : p.comp i = LinearMap.id)
    (hex : LinearMap.range i = LinearMap.ker d) (hsurj : Function.Surjective d) (b : B) :
    splitExactEquiv i p d hpi hex hsurj b = (p b, d b) :=
  rfl

/-- The equivalence sends an included element to its first component. -/
@[simp]
theorem SingularHomology.splitExactEquiv_apply_inclusion {A B C : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [Module ℤ A] [Module ℤ B] [Module ℤ C] (i : A →ₗ[ℤ] B)
    (p : B →ₗ[ℤ] A) (d : B →ₗ[ℤ] C) (hpi : p.comp i = LinearMap.id)
    (hex : LinearMap.range i = LinearMap.ker d) (hsurj : Function.Surjective d) (a : A) :
    splitExactEquiv i p d hpi hex hsurj (i a) = (a, 0) := by
  have hpa : p (i a) = a := LinearMap.congr_fun hpi a
  have hi : i a ∈ LinearMap.range i := ⟨a, rfl⟩
  rw [hex] at hi
  have hdi : d (i a) = 0 := hi
  rw [splitExactEquiv_apply, hpa, hdi]

/-! ### Circle boundary splitting -/

/-- An additive homomorphism between `ℤ`-modules is automatically `ℤ`-linear. -/
def SingularHomology.intLinearMapOfAddHom {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    {modA : Module ℤ A} {modB : Module ℤ B} (f : A →+ B) : A →ₗ[ℤ] B
    where
  toFun := f
  map_add' := f.map_add
  map_smul' n
    a := by
    change f (modA.smul n a) = modB.smul n (f a)
    rw [int_smul_eq_zsmul, int_smul_eq_zsmul]
    exact f.map_zsmul n a

/-- The map summing the two components of a pair. -/
def SingularHomology.pairSumMap (A : Type*) [AddCommGroup A] [Module ℤ A] :
    (A × A) →ₗ[ℤ] A :=
  intLinearMapOfAddHom
    { toFun ac := ac.1 + ac.2
      map_zero' := add_zero 0
      map_add' ac bd := add_add_add_comm ac.1 bd.1 ac.2 bd.2 }

/-- The map negating the first component of a pair. -/
def SingularHomology.negativeFirstMap (A : Type*) [AddCommGroup A] [Module ℤ A] :
    (A × A) →ₗ[ℤ] A :=
  intLinearMapOfAddHom
    { toFun ac := -ac.1
      map_zero' := neg_zero
      map_add' ac bd := neg_add ac.1 bd.1 }

/-- The pair-sum map computes the sum of components. -/
@[simp]
theorem SingularHomology.pairSumMap_apply (A : Type*) [AddCommGroup A] [Module ℤ A]
    (ac : A × A) : pairSumMap A ac = ac.1 + ac.2 :=
  rfl

/-- A boundary landing in the kernel of pair-sum has components summing to zero. -/
theorem SingularHomology.circleBoundary_sum_eq_zero {A : Type*} [AddCommGroup A]
    [Module ℤ A] {B : Type*} [AddCommGroup B] [Module ℤ B] (δ : B →ₗ[ℤ] (A × A))
    (hrange : LinearMap.range δ = LinearMap.ker (pairSumMap A)) (b : B) : (δ b).1 + (δ b).2 = 0 :=
  by
  have hb : δ b ∈ LinearMap.range δ := ⟨b, rfl⟩
  rw [hrange] at hb
  exact hb

/-- Composing the boundary with the negative-first map preserves the kernel. -/
theorem SingularHomology.circleBoundary_negativeFirst_ker {A : Type*} [AddCommGroup A]
    [Module ℤ A] {B : Type*} [AddCommGroup B] [Module ℤ B] (δ : B →ₗ[ℤ] (A × A))
    (hrange : LinearMap.range δ = LinearMap.ker (pairSumMap A)) :
    LinearMap.ker ((negativeFirstMap A).comp δ) = LinearMap.ker δ := by
  ext b
  change -(δ b).1 = 0 ↔ δ b = 0
  constructor
  · intro hb
    have hfst : (δ b).1 = 0 := neg_eq_zero.mp hb
    have hsnd := circleBoundary_sum_eq_zero δ hrange b
    rw [hfst, zero_add] at hsnd
    exact Prod.ext hfst hsnd
  · intro hb
    rw [hb]
    exact neg_zero

/-- Composing the boundary with the negative-first map is surjective. -/
theorem SingularHomology.circleBoundary_negativeFirst_surjective {A : Type*}
    [AddCommGroup A] [Module ℤ A] {B : Type*} [AddCommGroup B] [Module ℤ B] (δ : B →ₗ[ℤ] (A × A))
    (hrange : LinearMap.range δ = LinearMap.ker (pairSumMap A)) :
    Function.Surjective ((negativeFirstMap A).comp δ) := by
  intro a
  have ha : (-a, a) ∈ LinearMap.ker (pairSumMap A) := neg_add_cancel a
  rw [← hrange] at ha
  obtain ⟨b, hb⟩ := ha
  refine ⟨b, ?_⟩
  change -(δ b).1 = a
  rw [hb]
  exact neg_neg a

/-- The circle boundary split gives `B ≃ P × A`. -/
def SingularHomology.circleSplitExactEquiv {A : Type*} [AddCommGroup A] [Module ℤ A]
    {B P : Type*} [AddCommGroup B] [AddCommGroup P] [Module ℤ B] [Module ℤ P] (i : P →ₗ[ℤ] B)
    (p : B →ₗ[ℤ] P) (δ : B →ₗ[ℤ] (A × A)) (hpi : p.comp i = LinearMap.id)
    (hker : LinearMap.range i = LinearMap.ker δ)
    (hrange : LinearMap.range δ = LinearMap.ker (pairSumMap A)) : B ≃ₗ[ℤ] (P × A) :=
  splitExactEquiv i p ((negativeFirstMap A).comp δ) hpi
    (hker.trans (circleBoundary_negativeFirst_ker δ hrange).symm)
    (circleBoundary_negativeFirst_surjective δ hrange)

/-- The circle split equivalence sends an included element to its first component. -/
@[simp]
theorem SingularHomology.circleSplitExactEquiv_apply_inclusion {A : Type*}
    [AddCommGroup A] [Module ℤ A] {B P : Type*} [AddCommGroup B] [AddCommGroup P] [Module ℤ B]
    [Module ℤ P] (i : P →ₗ[ℤ] B) (p : B →ₗ[ℤ] P) (δ : B →ₗ[ℤ] (A × A))
    (hpi : p.comp i = LinearMap.id) (hker : LinearMap.range i = LinearMap.ker δ)
    (hrange : LinearMap.range δ = LinearMap.ker (pairSumMap A)) (a : P) :
    circleSplitExactEquiv i p δ hpi hker hrange (i a) = (a, 0) :=
  splitExactEquiv_apply_inclusion i p ((negativeFirstMap A).comp δ) hpi
    (hker.trans (circleBoundary_negativeFirst_ker δ hrange).symm)
    (circleBoundary_negativeFirst_surjective δ hrange) a

/-! ### Homology of a contractible two-cover -/

/-- For a cover by contractible opens the connecting homomorphism is injective. -/
theorem Suspension.contractibleCoverConnecting_injective {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [ContractibleSpace U] [ContractibleSpace V] (n : ℕ) :
    Function.Injective (SingularMayerVietoris.connectingHomomorphism U V hU hV hcover n) := by
  let :=
    SingularHomology.contractible_homology_subsingleton U (n + 1) (Nat.succ_ne_zero _)
  let :=
    SingularHomology.contractible_homology_subsingleton V (n + 1) (Nat.succ_ne_zero _)
  apply LinearMap.ker_eq_bot.mp
  rw [← SingularMayerVietoris.exact_at_ambient U V hU hV hcover n]
  apply LinearMap.range_eq_bot.mpr
  apply LinearMap.ext
  intro a
  have ha : a = 0 := Subsingleton.elim _ _
  rw [ha, map_zero, LinearMap.zero_apply]

/-- For a cover by contractible opens the connecting homomorphism is surjective in positive degree. -/
theorem Suspension.contractibleCoverConnecting_surjective {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [ContractibleSpace U] [ContractibleSpace V] (n : ℕ) :
    Function.Surjective (SingularMayerVietoris.connectingHomomorphism U V hU hV hcover (n + 1)) :=
  by
  let :=
    SingularHomology.contractible_homology_subsingleton U (n + 1) (Nat.succ_ne_zero _)
  let :=
    SingularHomology.contractible_homology_subsingleton V (n + 1) (Nat.succ_ne_zero _)
  intro a
  have ha : a ∈ LinearMap.ker (SingularMayerVietoris.leftHomologyMap U V (n + 1)) := by
    exact Subsingleton.elim _ _
  rw [← SingularMayerVietoris.exact_at_intersection U V hU hV hcover (n + 1)] at ha
  exact ha

/-- Higher homology of a space covered by two contractible opens is the shifted homology of the intersection. -/
def Suspension.contractibleCoverHomologyHigherEquiv {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [ContractibleSpace U] [ContractibleSpace V] (n : ℕ) :
    SingularMayerVietoris.SingularHomology X (n + 2) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (U ∩ V : Set X) (n + 1) :=
  LinearEquiv.ofBijective (SingularMayerVietoris.connectingHomomorphism U V hU hV hcover (n + 1))
    ⟨contractibleCoverConnecting_injective U V hU hV hcover (n + 1),
      contractibleCoverConnecting_surjective U V hU hV hcover n⟩

/-- The degree-one connecting map into the kernel of the left map. -/
def Suspension.contractibleCoverConnectingToKernel {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    SingularMayerVietoris.SingularHomology X 1 →ₗ[ℤ]
      LinearMap.ker (SingularMayerVietoris.leftHomologyMap U V 0) :=
  SingularHomology.intLinearMapOfAddHom
    ((SingularMayerVietoris.connectingHomomorphism U V hU hV hcover 0).codRestrict
        (LinearMap.ker (SingularMayerVietoris.leftHomologyMap U V 0))
        (by
          intro a
          rw [← SingularMayerVietoris.exact_at_intersection U V hU hV hcover 0]
          exact ⟨a, rfl⟩)).toAddMonoidHom

/-- The degree-one connecting map onto the kernel is bijective for contractible covers. -/
theorem Suspension.contractibleCoverConnectingToKernel_bijective {X : Type}
    [TopologicalSpace X] (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [ContractibleSpace U] [ContractibleSpace V] :
    Function.Bijective (contractibleCoverConnectingToKernel U V hU hV hcover) := by
  constructor
  · intro a b hab
    apply contractibleCoverConnecting_injective U V hU hV hcover 0
    exact congrArg Subtype.val hab
  · intro a
    have ha :
      (a : SingularMayerVietoris.SingularHomology (U ∩ V : Set X) 0) ∈
        LinearMap.range (SingularMayerVietoris.connectingHomomorphism U V hU hV hcover 0) :=
      (SingularMayerVietoris.exact_at_intersection U V hU hV hcover 0).symm.le a.property
    obtain ⟨b, hb⟩ := ha
    exact ⟨b, Subtype.ext hb⟩

/-- Degree-one homology of a contractible two-cover is the kernel of the left map. -/
def Suspension.contractibleCoverHomologyOneEquivKernel {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [ContractibleSpace U] [ContractibleSpace V] :
    SingularMayerVietoris.SingularHomology X 1 ≃ₗ[ℤ]
      LinearMap.ker (SingularMayerVietoris.leftHomologyMap U V 0) :=
  LinearEquiv.ofBijective (contractibleCoverConnectingToKernel U V hU hV hcover)
    (contractibleCoverConnectingToKernel_bijective U V hU hV hcover)

/-- Higher homology of a suspension is the shifted homology of the base. -/
def SphereHomology.suspensionHomologyHigherEquiv (X : Type) [TopologicalSpace X] [Nonempty X]
    (k : ℕ) :
    SingularMayerVietoris.SingularHomology (Suspension X) (k + 2) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology X (k + 1) :=
  (Suspension.contractibleCoverHomologyHigherEquiv
        Suspension.northOpen Suspension.southOpen
        Suspension.northOpen_isOpen
        Suspension.southOpen_isOpen Suspension.open_cover
        k).trans
    (SingularHomology.homotopyEquivHomologyEquiv
      Suspension.middleBandHomotopyEquiv (k + 1))

/-- Higher homology of the `n+1`-sphere is the shifted homology of the `n`-sphere. -/
def SphereHomology.unitSphereHomologySuspensionEquiv (n k : ℕ) :
    SingularMayerVietoris.SingularHomology (UnitSphere (n + 1)) (k + 2) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (UnitSphere n) (k + 1) :=
  (SingularHomology.homeomorphHomologyEquiv (suspensionSphereHomeomorph n).symm
        (k + 2)).trans
    (suspensionHomologyHigherEquiv (UnitSphere n) k)

/-! ### The circle as a plane sphere -/

/-- The real Euclidean plane is isometric to `ℂ`. -/
def SphereHomology.euclideanPlaneComplexIsometry : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.symm

/-- The isometry preserves membership in centred spheres. -/
theorem SphereHomology.euclideanPlaneComplexIsometry_mem_sphere (x : EuclideanSpace ℝ (Fin 2))
    (r : ℝ) :
    euclideanPlaneComplexIsometry x ∈ Metric.sphere (0 : ℂ) r ↔
      x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) r := by
  simp only [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map]

/-- The unit sphere in the Euclidean plane is homeomorphic to `Circle`. -/
def SphereHomology.sphereCircleHomeomorph :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ _root_.Circle :=
  euclideanPlaneComplexIsometry.toHomeomorph.subtype
    (fun x => (euclideanPlaneComplexIsometry_mem_sphere x 1).symm)

/-- The plane unit sphere and `Circle` have equivalent singular homology. -/
def SphereHomology.sphereCircleHomologyEquiv (n : ℕ) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)
        n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology _root_.Circle n :=
  SingularHomology.homeomorphHomologyEquiv sphereCircleHomeomorph n
end Mathoverflow1973
