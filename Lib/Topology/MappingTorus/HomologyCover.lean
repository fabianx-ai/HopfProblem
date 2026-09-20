/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Topology.MappingTorus.Basic
import Lib.AlgebraicTopology.SingularHomology.Chains
import Lib.AlgebraicTopology.SingularHomology.ModuleHomology
import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Lib.AlgebraicTopology.SingularHomology.Sum
import Lib.AlgebraicTopology.SingularHomology.CircleProduct
import Lib.Algebra.Homology.MayerVietorisShortExact
import Lib.Topology.Homotopy.Suspension
import Lib.AlgebraicTopology.SingularHomology.Suspension
import Lib.AlgebraicTopology.SingularHomology.Sphere
import Lib.AlgebraicTopology.SingularHomology.SphereHomology
/-!
# Homology of the mapping torus via the two-open cover

  Homology of the mapping torus computed from its two-open cover: the
  Mayer-Vietoris assembly, the monodromy action on the fiber homology, and the
  resulting exact sequence (Hatcher, Algebraic Topology, Example 2.48).
-/



open Set Function Filter Manifold Topology

noncomputable section

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-! ### Wang sequence algebra -/

/-- The difference map `id − F`. -/
def MappingTorusHomology.Algebra.difference {M : Type*} [AddCommGroup M] [Module ℤ M]
    (F : M →ₗ[ℤ] M) : M →ₗ[ℤ] M :=
  LinearMap.id - F

/-- The Mayer–Vietoris difference map on the two-summand model `(u,v) ↦ (u+v, −(u+Fv))`. -/
def MappingTorusHomology.Algebra.twoArcMap {M : Type*} [AddCommGroup M] [Module ℤ M]
    (F : M →ₗ[ℤ] M) : (M × M) →ₗ[ℤ] (M × M) :=
  SingularHomology.intLinearMapOfAddHom
    { toFun p := (p.1 + p.2, -(p.1 + F p.2))
      map_zero' := by simp
      map_add' p
        q := by
        apply Prod.ext
        · exact add_add_add_comm p.1 q.1 p.2 q.2
        · change -((p.1 + q.1) + F (p.2 + q.2)) = -(p.1 + F p.2) + -(q.1 + F q.2)
          rw [map_add]
          abel }

/-- The two-arc map computes `(p₁ + p₂, −(p₁ + F p₂))`. -/
@[simp]
theorem MappingTorusHomology.Algebra.twoArcMap_apply {M : Type*} [AddCommGroup M] [Module ℤ M]
    (F : M →ₗ[ℤ] M) (p : M × M) : twoArcMap F p = (p.1 + p.2, -(p.1 + F p.2)) :=
  rfl

/-- The pair sum of a two-arc image is the difference on the second component. -/
theorem MappingTorusHomology.Algebra.pairSum_twoArcMap {M : Type*} [AddCommGroup M] [Module ℤ M]
    (F : M →ₗ[ℤ] M) (p : M × M) :
    SingularHomology.pairSumMap M (twoArcMap F p) = difference F p.2 := by
  change (p.1 + p.2) + -(p.1 + F p.2) = p.2 - F p.2
  abel

/-- The two-arc kernel is the antidiagonal of `ker (id − F)`. -/
theorem MappingTorusHomology.Algebra.twoArcMap_kernel_iff {M : Type*} [AddCommGroup M]
    [Module ℤ M] (F : M →ₗ[ℤ] M) (p : M × M) :
    twoArcMap F p = 0 ↔ p.1 = -p.2 ∧ difference F p.2 = 0 := by
  constructor
  · intro hp
    have hsum : p.1 + p.2 = 0 := congrArg Prod.fst hp
    refine ⟨eq_neg_of_add_eq_zero_left hsum, ?_⟩
    rw [← pairSum_twoArcMap F p, hp, map_zero]
  · rintro ⟨hfst, hfix⟩
    have hF : F p.2 = p.2 := (sub_eq_zero.mp hfix).symm
    rw [twoArcMap_apply, hfst, hF, neg_add_cancel, neg_zero]
    rfl

/-- Exactness identifies `range (id − F)` with the kernel of the fold. -/
theorem MappingTorusHomology.Algebra.range_difference_eq_ker {M N : Type*} [AddCommGroup M]
    [Module ℤ M] [AddCommGroup N] [Module ℤ N] (F : M →ₗ[ℤ] M) (i : M →ₗ[ℤ] N)
    (hJ :
      LinearMap.range (twoArcMap F) =
        LinearMap.ker (i.comp (SingularHomology.pairSumMap M))) :
    LinearMap.range (difference F) = LinearMap.ker i := by
  ext x
  constructor
  · rintro ⟨b, rfl⟩
    have hb : twoArcMap F (0, b) ∈ LinearMap.range (twoArcMap F) := ⟨(0, b), rfl⟩
    rw [hJ] at hb
    change i (SingularHomology.pairSumMap M (twoArcMap F (0, b))) = 0 at hb
    rw [pairSum_twoArcMap] at hb
    exact hb
  · intro hx
    have hix : i x = 0 := LinearMap.mem_ker.mp hx
    have hp : (x, 0) ∈ LinearMap.ker (i.comp (SingularHomology.pairSumMap M)) := by
      change i (x + 0) = 0
      simpa only [add_zero] using hix
    rw [← hJ] at hp
    obtain ⟨p, hp⟩ := hp
    refine ⟨p.2, ?_⟩
    calc
      difference F p.2 = SingularHomology.pairSumMap M (twoArcMap F p) :=
        (pairSum_twoArcMap F p).symm
      _ = x := by rw [hp, SingularHomology.pairSumMap_apply, add_zero]

/-! ### The connecting boundary -/

/-- The boundary `n ↦ −(d n)₁` through a kernel presentation. -/
def MappingTorusHomology.Algebra.boundary {N P : Type*} [AddCommGroup N] [Module ℤ N]
    [AddCommGroup P] [Module ℤ P] (d : N →ₗ[ℤ] (P × P)) : N →ₗ[ℤ] P :=
  (SingularHomology.negativeFirstMap P).comp d

/-- The boundary computes the negated first component. -/
@[simp]
theorem MappingTorusHomology.Algebra.boundary_apply {N P : Type*} [AddCommGroup N] [Module ℤ N]
    [AddCommGroup P] [Module ℤ P] (d : N →ₗ[ℤ] (P × P)) (n : N) : boundary d n = -(d n).1 :=
  rfl

/-- The connecting image lies in the two-arc kernel. -/
theorem MappingTorusHomology.Algebra.connecting_mem_kernel {N P : Type*} [AddCommGroup N]
    [Module ℤ N] [AddCommGroup P] [Module ℤ P] (F : P →ₗ[ℤ] P) (d : N →ₗ[ℤ] (P × P))
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F)) (n : N) :
    d n ∈ LinearMap.ker (twoArcMap F) := by
  rw [← hd]
  exact ⟨n, rfl⟩

/-- On the kernel the boundary also equals the second component. -/
theorem MappingTorusHomology.Algebra.boundary_eq_snd {N P : Type*} [AddCommGroup N] [Module ℤ N]
    [AddCommGroup P] [Module ℤ P] (F : P →ₗ[ℤ] P) (d : N →ₗ[ℤ] (P × P))
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F)) (n : N) : boundary d n = (d n).2 := by
  have hp := (twoArcMap_kernel_iff F (d n)).mp (connecting_mem_kernel F d hd n)
  rw [boundary_apply, hp.1, neg_neg]

/-- The connecting image is antidiagonal in the boundary. -/
theorem MappingTorusHomology.Algebra.connecting_eq_antidiagonal {N P : Type*} [AddCommGroup N]
    [Module ℤ N] [AddCommGroup P] [Module ℤ P] (F : P →ₗ[ℤ] P) (d : N →ₗ[ℤ] (P × P))
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F)) (n : N) :
    d n = (-boundary d n, boundary d n) := by
  apply Prod.ext
  · simp only [boundary_apply, neg_neg]
  · exact (boundary_eq_snd F d hd n).symm

/-- The boundary lands in `ker (id − F)`. -/
theorem MappingTorusHomology.Algebra.boundary_mem_kernel {N P : Type*} [AddCommGroup N]
    [Module ℤ N] [AddCommGroup P] [Module ℤ P] (F : P →ₗ[ℤ] P) (d : N →ₗ[ℤ] (P × P))
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F)) (n : N) :
    boundary d n ∈ LinearMap.ker (difference F) := by
  rw [boundary_eq_snd F d hd n]
  exact ((twoArcMap_kernel_iff F (d n)).mp (connecting_mem_kernel F d hd n)).2

/-- The boundary range is `ker (id − F)`. -/
theorem MappingTorusHomology.Algebra.boundary_range {N P : Type*} [AddCommGroup N] [Module ℤ N]
    [AddCommGroup P] [Module ℤ P] (F : P →ₗ[ℤ] P) (d : N →ₗ[ℤ] (P × P))
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F)) :
    LinearMap.range (boundary d) = LinearMap.ker (difference F) := by
  ext b
  constructor
  · rintro ⟨n, rfl⟩
    exact boundary_mem_kernel F d hd n
  · intro hb
    have hp : (-b, b) ∈ LinearMap.ker (twoArcMap F) :=
      (twoArcMap_kernel_iff F (-b, b)).mpr ⟨rfl, hb⟩
    rw [← hd] at hp
    obtain ⟨n, hn⟩ := hp
    refine ⟨n, ?_⟩
    rw [boundary_apply, hn]
    exact neg_neg b

/-- The boundary kernel equals the kernel of `d`. -/
theorem MappingTorusHomology.Algebra.boundary_ker {N P : Type*} [AddCommGroup N] [Module ℤ N]
    [AddCommGroup P] [Module ℤ P] (F : P →ₗ[ℤ] P) (d : N →ₗ[ℤ] (P × P))
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F)) :
    LinearMap.ker (boundary d) = LinearMap.ker d := by
  ext n
  change boundary d n = 0 ↔ d n = 0
  constructor
  · intro hn
    rw [connecting_eq_antidiagonal F d hd n, hn, neg_zero]
    rfl
  · intro hn
    rw [boundary_apply, hn]
    exact neg_zero

/-- Exactness identifies the inclusion range with the boundary kernel. -/
theorem MappingTorusHomology.Algebra.range_inclusion_eq_ker_boundary {M N P : Type*}
    [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N] [AddCommGroup P] [Module ℤ P]
    (F : P →ₗ[ℤ] P) (i : M →ₗ[ℤ] N) (d : N →ₗ[ℤ] (P × P))
    (hi : LinearMap.range i = LinearMap.ker d)
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F)) :
    LinearMap.range i = LinearMap.ker (boundary d) :=
  hi.trans (boundary_ker F d hd).symm

/-! ### Homology of the two-open cover -/

/-- The monodromy map `f_*` on homology. -/
abbrev MappingTorusHomology.monodromyHomologyMap {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology X n →ₗ[ℤ] SingularMayerVietoris.SingularHomology X n :=
  SingularMayerVietoris.singularHomologyMap (f : C(X, X)) n

/-- The fiber inclusion map on homology. -/
abbrev MappingTorusHomology.fibreHomologyMap {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology X n →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (MappingTorus.Torus f) n :=
  SingularMayerVietoris.singularHomologyMap (MappingTorus.HomologyCover.fibreInclusion f) n

/-- The homology of `U` and `V` is two copies of the fiber homology. -/
def MappingTorusHomology.arcHomologyEquiv {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) (n : ℕ) :
    (SingularMayerVietoris.SingularHomology (MappingTorus.HomologyCover.U f) n ×
        SingularMayerVietoris.SingularHomology (MappingTorus.HomologyCover.V f) n) ≃ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology X n × SingularMayerVietoris.SingularHomology X n) :=
  ((SingularHomology.homotopyEquivHomologyEquiv
          (MappingTorus.HomologyCover.homotopyEquivU f) n).toAddEquiv.prodCongr
      (SingularHomology.homotopyEquivHomologyEquiv
          (MappingTorus.HomologyCover.homotopyEquivV f) n).toAddEquiv).toIntLinearEquiv

/-- The intersection homology is two copies of the fiber homology. -/
def MappingTorusHomology.intersectionHomologyEquiv {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology
        (MappingTorus.HomologyCover.U f ∩ MappingTorus.HomologyCover.V f :
          Set (MappingTorus.Torus f))
        n ≃ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology X n × SingularMayerVietoris.SingularHomology X n) :=
  (SingularHomology.homotopyEquivHomologyEquiv
        (MappingTorus.HomologyCover.intersectionHomotopyEquiv f) n).trans
    (SingularHomology.sumHomologyEquiv X X n)

/-- The intersection equivalence computes through the homotopy equivalence. -/
@[simp]
theorem MappingTorusHomology.intersectionHomologyEquiv_apply {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (MappingTorus.HomologyCover.U f ∩ MappingTorus.HomologyCover.V f :
          Set (MappingTorus.Torus f))
        n) :
    intersectionHomologyEquiv f n a =
      SingularHomology.sumHomologyEquiv X X n
        (SingularMayerVietoris.singularHomologyMap
          (MappingTorus.HomologyCover.intersectionHomotopyEquiv f).toFun n a) :=
  rfl

/-- The `U` inclusion on homology factors through the homotopy equivalence. -/
theorem MappingTorusHomology.inclusionU_homology {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (MappingTorus.HomologyCover.inclusionU f) n =
      (fibreHomologyMap f n).comp
        (SingularHomology.homotopyEquivHomologyEquiv
            (MappingTorus.HomologyCover.homotopyEquivU f) n).toLinearMap := by
  rw [SingularHomology.homotopy_homologyMap
      (MappingTorus.HomologyCover.inclusionUHomotopy f) n,
    SingularHomology.singularHomologyMap_comp]
  rfl

/-- The `V` inclusion on homology factors through the homotopy equivalence. -/
theorem MappingTorusHomology.inclusionV_homology {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (MappingTorus.HomologyCover.inclusionV f) n =
      (fibreHomologyMap f n).comp
        (SingularHomology.homotopyEquivHomologyEquiv
            (MappingTorus.HomologyCover.homotopyEquivV f) n).toLinearMap := by
  rw [SingularHomology.homotopy_homologyMap
      (MappingTorus.HomologyCover.inclusionVHomotopy f) n,
    SingularHomology.singularHomologyMap_comp]
  rfl

/-- The `U` intersection map on homology is the fold. -/
theorem MappingTorusHomology.intersectionToU_homology {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (MappingTorus.HomologyCover.U f ∩ MappingTorus.HomologyCover.V f :
          Set (MappingTorus.Torus f))
        n) :
    SingularHomology.homotopyEquivHomologyEquiv
        (MappingTorus.HomologyCover.homotopyEquivU f) n
        (SingularMayerVietoris.singularHomologyMap (MappingTorus.HomologyCover.intersectionToU f)
          n a) =
      (intersectionHomologyEquiv f n a).1 + (intersectionHomologyEquiv f n a).2 := by
  change
    SingularMayerVietoris.singularHomologyMap (MappingTorus.HomologyCover.homotopyEquivU f).toFun
        n
        (SingularMayerVietoris.singularHomologyMap (MappingTorus.HomologyCover.intersectionToU f)
          n a) =
      _
  rw [← LinearMap.comp_apply, ← SingularHomology.singularHomologyMap_comp,
    MappingTorus.HomologyCover.intersectionToU_fold,
    SingularHomology.singularHomologyMap_comp]
  simp only [LinearMap.comp_apply, intersectionHomologyEquiv_apply]
  exact
    SingularHomology.sumHomologyEquiv_fold (X := X) n
      (SingularMayerVietoris.singularHomologyMap
        (MappingTorus.HomologyCover.intersectionHomotopyEquiv f).toFun n a)

/-- The `V` intersection map on homology is the twisted fold. -/
theorem MappingTorusHomology.intersectionToV_homology {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (MappingTorus.HomologyCover.U f ∩ MappingTorus.HomologyCover.V f :
          Set (MappingTorus.Torus f))
        n) :
    SingularHomology.homotopyEquivHomologyEquiv
        (MappingTorus.HomologyCover.homotopyEquivV f) n
        (SingularMayerVietoris.singularHomologyMap (MappingTorus.HomologyCover.intersectionToV f)
          n a) =
      (intersectionHomologyEquiv f n a).1 +
        monodromyHomologyMap f n (intersectionHomologyEquiv f n a).2 := by
  change
    SingularMayerVietoris.singularHomologyMap (MappingTorus.HomologyCover.homotopyEquivV f).toFun
        n
        (SingularMayerVietoris.singularHomologyMap (MappingTorus.HomologyCover.intersectionToV f)
          n a) =
      _
  rw [← LinearMap.comp_apply, ← SingularHomology.singularHomologyMap_comp,
    MappingTorus.HomologyCover.intersectionToV_twistedFold,
    SingularHomology.singularHomologyMap_comp]
  simp only [LinearMap.comp_apply, intersectionHomologyEquiv_apply]
  have h :=
    SingularHomology.sumHomologyEquiv_sumElim (ContinuousMap.id X) (f : C(X, X)) n
      (SingularMayerVietoris.singularHomologyMap
        (MappingTorus.HomologyCover.intersectionHomotopyEquiv f).toFun n a)
  simpa only [SingularHomology.singularHomologyMap_id, LinearMap.id_apply] using h

/-- The left Mayer–Vietoris map in fiber coordinates. -/
theorem MappingTorusHomology.leftHomologyMap_coordinates {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (MappingTorus.HomologyCover.U f ∩ MappingTorus.HomologyCover.V f :
          Set (MappingTorus.Torus f))
        n) :
    arcHomologyEquiv f n
        (SingularMayerVietoris.leftHomologyMap (MappingTorus.HomologyCover.U f)
          (MappingTorus.HomologyCover.V f) n a) =
      Algebra.twoArcMap (monodromyHomologyMap f n) (intersectionHomologyEquiv f n a) := by
  rw [SingularMayerVietoris.leftHomologyMap_apply]
  change
    (SingularHomology.homotopyEquivHomologyEquiv
          (MappingTorus.HomologyCover.homotopyEquivU f) n
          (SingularMayerVietoris.singularHomologyMap
            (MappingTorus.HomologyCover.intersectionToU f) n a),
        SingularHomology.homotopyEquivHomologyEquiv
          (MappingTorus.HomologyCover.homotopyEquivV f) n
          (-SingularMayerVietoris.singularHomologyMap
              (MappingTorus.HomologyCover.intersectionToV f) n a)) =
      _
  rw [map_neg, intersectionToU_homology, intersectionToV_homology]
  rfl

/-- The right Mayer–Vietoris map in fiber coordinates. -/
theorem MappingTorusHomology.rightHomologyMap_coordinates {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology (MappingTorus.HomologyCover.U f) n ×
        SingularMayerVietoris.SingularHomology (MappingTorus.HomologyCover.V f) n) :
    SingularMayerVietoris.rightHomologyMap (MappingTorus.HomologyCover.U f)
        (MappingTorus.HomologyCover.V f) n a =
      fibreHomologyMap f n ((arcHomologyEquiv f n a).1 + (arcHomologyEquiv f n a).2) := by
  rw [SingularMayerVietoris.rightHomologyMap_apply]
  change
    SingularMayerVietoris.singularHomologyMap (MappingTorus.HomologyCover.inclusionU f) n a.1 +
        SingularMayerVietoris.singularHomologyMap (MappingTorus.HomologyCover.inclusionV f) n
          a.2 =
      _
  rw [inclusionU_homology, inclusionV_homology]
  exact (map_add (fibreHomologyMap f n) _ _).symm

/-! ### Cokernel and kernel exactness -/

/-- The induced inclusion of the `id − F` cokernel. -/
def MappingTorusHomology.Algebra.cokernelInclusion {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (F : M →ₗ[ℤ] M) (i : M →ₗ[ℤ] N)
    (hJ :
      LinearMap.range (twoArcMap F) =
        LinearMap.ker (i.comp (SingularHomology.pairSumMap M))) :
    (M ⧸ LinearMap.range (difference F)) →ₗ[ℤ] N :=
  SingularHomology.intLinearMapOfAddHom
    ((LinearMap.range (difference F)).liftQ i (range_difference_eq_ker F i hJ).le).toAddMonoidHom

/-- The cokernel inclusion is injective. -/
theorem MappingTorusHomology.Algebra.cokernelInclusion_injective {M N : Type*} [AddCommGroup M]
    [Module ℤ M] [AddCommGroup N] [Module ℤ N] (F : M →ₗ[ℤ] M) (i : M →ₗ[ℤ] N)
    (hJ :
      LinearMap.range (twoArcMap F) =
        LinearMap.ker (i.comp (SingularHomology.pairSumMap M))) :
    Function.Injective (cokernelInclusion F i hJ) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := (LinearMap.range (difference F)).mkQ_surjective x
  obtain ⟨b, rfl⟩ := (LinearMap.range (difference F)).mkQ_surjective y
  change i a = i b at hxy
  apply (Submodule.Quotient.eq (LinearMap.range (difference F))).mpr
  rw [range_difference_eq_ker F i hJ]
  change i (a - b) = 0
  rw [map_sub, hxy, sub_self]

/-- The cokernel inclusion has range `range i`. -/
theorem MappingTorusHomology.Algebra.cokernelInclusion_range {M N : Type*} [AddCommGroup M]
    [Module ℤ M] [AddCommGroup N] [Module ℤ N] (F : M →ₗ[ℤ] M) (i : M →ₗ[ℤ] N)
    (hJ :
      LinearMap.range (twoArcMap F) =
        LinearMap.ker (i.comp (SingularHomology.pairSumMap M))) :
    LinearMap.range (cokernelInclusion F i hJ) = LinearMap.range i := by
  ext n
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := (LinearMap.range (difference F)).mkQ_surjective x
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨Submodule.Quotient.mk a, rfl⟩

/-- The boundary viewed as a map into `ker (id − F)`. -/
def MappingTorusHomology.Algebra.kernelBoundary {N P : Type*} [AddCommGroup N] [Module ℤ N]
    [AddCommGroup P] [Module ℤ P] (F : P →ₗ[ℤ] P) (d : N →ₗ[ℤ] (P × P))
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F)) :
    N →ₗ[ℤ] LinearMap.ker (difference F) :=
  SingularHomology.intLinearMapOfAddHom
    { toFun n := ⟨boundary d n, boundary_mem_kernel F d hd n⟩
      map_zero' := by
        apply Subtype.ext
        exact map_zero (boundary d)
      map_add' n
        m := by
        apply Subtype.ext
        exact map_add (boundary d) n m }

/-- The kernel boundary vanishes exactly when the boundary does. -/
theorem MappingTorusHomology.Algebra.kernelBoundary_eq_zero_iff {N P : Type*} [AddCommGroup N]
    [Module ℤ N] [AddCommGroup P] [Module ℤ P] (F : P →ₗ[ℤ] P) (d : N →ₗ[ℤ] (P × P))
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F)) (n : N) :
    kernelBoundary F d hd n = 0 ↔ boundary d n = 0 := by
  constructor
  · intro hn
    exact congrArg Subtype.val hn
  · intro hn
    exact Subtype.ext hn

/-- The kernel boundary's kernel is the boundary's kernel. -/
theorem MappingTorusHomology.Algebra.kernelBoundary_ker {N P : Type*} [AddCommGroup N]
    [Module ℤ N] [AddCommGroup P] [Module ℤ P] (F : P →ₗ[ℤ] P) (d : N →ₗ[ℤ] (P × P))
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F)) :
    LinearMap.ker (kernelBoundary F d hd) = LinearMap.ker (boundary d) := by
  ext n
  exact kernelBoundary_eq_zero_iff F d hd n

/-- The kernel boundary surjects onto `ker (id − F)`. -/
theorem MappingTorusHomology.Algebra.kernelBoundary_surjective {N P : Type*} [AddCommGroup N]
    [Module ℤ N] [AddCommGroup P] [Module ℤ P] (F : P →ₗ[ℤ] P) (d : N →ₗ[ℤ] (P × P))
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F)) :
    Function.Surjective (kernelBoundary F d hd) := by
  intro b
  have hb : (b : P) ∈ LinearMap.range (boundary d) := by
    rw [boundary_range F d hd]
    exact b.property
  obtain ⟨n, hn⟩ := hb
  exact ⟨n, Subtype.ext hn⟩

/-- The cokernel inclusion range is the kernel-boundary kernel. -/
theorem MappingTorusHomology.Algebra.cokernelInclusion_range_eq_ker_kernelBoundary {M N P : Type*}
    [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N] [AddCommGroup P] [Module ℤ P]
    (F : M →ₗ[ℤ] M) (F' : P →ₗ[ℤ] P) (i : M →ₗ[ℤ] N) (d : N →ₗ[ℤ] (P × P))
    (hJ :
      LinearMap.range (twoArcMap F) =
        LinearMap.ker (i.comp (SingularHomology.pairSumMap M)))
    (hi : LinearMap.range i = LinearMap.ker d)
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F')) :
    LinearMap.range (cokernelInclusion F i hJ) = LinearMap.ker (kernelBoundary F' d hd) := by
  rw [cokernelInclusion_range, kernelBoundary_ker, boundary_ker F' d hd]
  exact hi

/-! ### The Wang sequence -/

/-- The Wang difference `id − f_*` on homology. -/
def MappingTorusHomology.wangDifference {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) (n : ℕ) :
    SingularMayerVietoris.SingularHomology X n →ₗ[ℤ] SingularMayerVietoris.SingularHomology X n :=
  Algebra.difference (monodromyHomologyMap f n)

/-- The Wang difference computes `a − f_* a`. -/
@[simp]
theorem MappingTorusHomology.wangDifference_apply {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    wangDifference f n a = a - SingularMayerVietoris.singularHomologyMap (f : C(X, X)) n a :=
  rfl

/-- Exactness of the two-arc Mayer–Vietoris step at the pair. -/
theorem MappingTorusHomology.twoArc_exact_at_pair {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ) :
    LinearMap.range (Algebra.twoArcMap (monodromyHomologyMap f n)) =
      LinearMap.ker
        ((fibreHomologyMap f n).comp
          (SingularHomology.pairSumMap (SingularMayerVietoris.SingularHomology X n))) := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    have h :=
      LinearMap.congr_fun
        (SingularMayerVietoris.leftHomologyMap_comp_right (MappingTorus.HomologyCover.U f)
          (MappingTorus.HomologyCover.V f) n)
        ((intersectionHomologyEquiv f n).symm b)
    change
      SingularMayerVietoris.rightHomologyMap (MappingTorus.HomologyCover.U f)
          (MappingTorus.HomologyCover.V f) n
          (SingularMayerVietoris.leftHomologyMap (MappingTorus.HomologyCover.U f)
            (MappingTorus.HomologyCover.V f) n ((intersectionHomologyEquiv f n).symm b)) =
        0 at h
    rw [rightHomologyMap_coordinates, leftHomologyMap_coordinates,
      LinearEquiv.apply_symm_apply] at h
    exact h
  · intro ha
    have hright :
      (arcHomologyEquiv f n).symm a ∈
        LinearMap.ker
          (SingularMayerVietoris.rightHomologyMap (MappingTorus.HomologyCover.U f)
            (MappingTorus.HomologyCover.V f) n) := by
      change
        SingularMayerVietoris.rightHomologyMap (MappingTorus.HomologyCover.U f)
            (MappingTorus.HomologyCover.V f) n ((arcHomologyEquiv f n).symm a) =
          0
      rw [rightHomologyMap_coordinates, LinearEquiv.apply_symm_apply]
      exact ha
    rw [←
      SingularMayerVietoris.exact_at_pair (MappingTorus.HomologyCover.U f)
        (MappingTorus.HomologyCover.V f) (MappingTorus.HomologyCover.U_open f)
        (MappingTorus.HomologyCover.V_open f) (MappingTorus.HomologyCover.cover f) n] at hright
    obtain ⟨b, hb⟩ := hright
    refine ⟨intersectionHomologyEquiv f n b, ?_⟩
    rw [← leftHomologyMap_coordinates, hb, LinearEquiv.apply_symm_apply]

/-- The Mayer–Vietoris connecting map of the cover. -/
abbrev MappingTorusHomology.mayerVietorisConnecting {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology (MappingTorus.Torus f) (n + 1) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology
        (MappingTorus.HomologyCover.U f ∩ MappingTorus.HomologyCover.V f :
          Set (MappingTorus.Torus f))
        n :=
  SingularMayerVietoris.connectingHomomorphism (MappingTorus.HomologyCover.U f)
    (MappingTorus.HomologyCover.V f) (MappingTorus.HomologyCover.U_open f)
    (MappingTorus.HomologyCover.V_open f) (MappingTorus.HomologyCover.cover f) n

/-- The connecting map in `X × X` coordinates. -/
def MappingTorusHomology.boundaryCoordinates {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology (MappingTorus.Torus f) (n + 1) →ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology X n × SingularMayerVietoris.SingularHomology X n) :=
  (intersectionHomologyEquiv f n).toLinearMap.comp (mayerVietorisConnecting f n)

/-- The boundary coordinates are the connecting map's image. -/
@[simp]
theorem MappingTorusHomology.boundaryCoordinates_apply {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (MappingTorus.Torus f) (n + 1)) :
    boundaryCoordinates f n a = intersectionHomologyEquiv f n (mayerVietorisConnecting f n a) :=
  rfl

/-- The boundary coordinates have range the two-arc kernel. -/
theorem MappingTorusHomology.boundaryCoordinates_range {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (n : ℕ) :
    LinearMap.range (boundaryCoordinates f n) =
      LinearMap.ker (Algebra.twoArcMap (monodromyHomologyMap f n)) := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    have hb : mayerVietorisConnecting f n b ∈ LinearMap.range (mayerVietorisConnecting f n) :=
      ⟨b, rfl⟩
    rw [SingularMayerVietoris.exact_at_intersection (MappingTorus.HomologyCover.U f)
        (MappingTorus.HomologyCover.V f) (MappingTorus.HomologyCover.U_open f)
        (MappingTorus.HomologyCover.V_open f) (MappingTorus.HomologyCover.cover f)] at hb
    have h := congrArg (arcHomologyEquiv f n) hb
    rw [leftHomologyMap_coordinates, map_zero] at h
    exact h
  · intro ha
    have hl :
      SingularMayerVietoris.leftHomologyMap (MappingTorus.HomologyCover.U f)
          (MappingTorus.HomologyCover.V f) n ((intersectionHomologyEquiv f n).symm a) =
        0 := by
      apply (arcHomologyEquiv f n).injective
      rw [leftHomologyMap_coordinates, LinearEquiv.apply_symm_apply, map_zero]
      exact ha
    have hr :
      (intersectionHomologyEquiv f n).symm a ∈ LinearMap.range (mayerVietorisConnecting f n) := by
      rw [SingularMayerVietoris.exact_at_intersection (MappingTorus.HomologyCover.U f)
          (MappingTorus.HomologyCover.V f) (MappingTorus.HomologyCover.U_open f)
          (MappingTorus.HomologyCover.V_open f) (MappingTorus.HomologyCover.cover f)]
      exact hl
    obtain ⟨b, hb⟩ := hr
    refine ⟨b, ?_⟩
    rw [boundaryCoordinates_apply, hb, LinearEquiv.apply_symm_apply]

/-- The right Mayer–Vietoris map has range the fiber image. -/
theorem MappingTorusHomology.rightHomologyMap_range {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ) :
    LinearMap.range
        (SingularMayerVietoris.rightHomologyMap (MappingTorus.HomologyCover.U f)
          (MappingTorus.HomologyCover.V f) n) =
      LinearMap.range (fibreHomologyMap f n) := by
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    exact
      ⟨(arcHomologyEquiv f n a).1 + (arcHomologyEquiv f n a).2,
        (rightHomologyMap_coordinates f n a).symm⟩
  · rintro ⟨a, rfl⟩
    refine ⟨(arcHomologyEquiv f n).symm (a, 0), ?_⟩
    rw [rightHomologyMap_coordinates, LinearEquiv.apply_symm_apply]
    exact congrArg (fibreHomologyMap f n) (add_zero a)

/-- The fiber image is the boundary-coordinates kernel. -/
theorem MappingTorusHomology.boundaryCoordinates_ker {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ) :
    LinearMap.range (fibreHomologyMap f (n + 1)) = LinearMap.ker (boundaryCoordinates f n) := by
  rw [boundaryCoordinates, SingularMayerVietoris.rightTransport_second_ker]
  rw [←
    SingularMayerVietoris.exact_at_ambient (MappingTorus.HomologyCover.U f)
      (MappingTorus.HomologyCover.V f) (MappingTorus.HomologyCover.U_open f)
      (MappingTorus.HomologyCover.V_open f) (MappingTorus.HomologyCover.cover f)]
  exact (rightHomologyMap_range f (n + 1)).symm

/-- The Wang boundary `H_{n+1}(T_f) → H_n(X)`. -/
def MappingTorusHomology.wangBoundary {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) (n : ℕ) :
    SingularMayerVietoris.SingularHomology (MappingTorus.Torus f) (n + 1) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology X n :=
  Algebra.boundary (boundaryCoordinates f n)

/-- The Wang boundary is the negated first coordinate. -/
@[simp]
theorem MappingTorusHomology.wangBoundary_apply {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ) (a : SingularMayerVietoris.SingularHomology (MappingTorus.Torus f) (n + 1)) :
    wangBoundary f n a = -(boundaryCoordinates f n a).1 :=
  rfl

/-- The boundary coordinates are antidiagonal in the Wang boundary. -/
theorem MappingTorusHomology.boundaryCoordinates_eq_antidiagonal {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (MappingTorus.Torus f) (n + 1)) :
    boundaryCoordinates f n a = (-wangBoundary f n a, wangBoundary f n a) :=
  Algebra.connecting_eq_antidiagonal _ _ (boundaryCoordinates_range f n) a

/-- Wang exactness at the fiber: `range(id − f_*) = ker i_*`. -/
theorem MappingTorusHomology.wang_exact_at_fibre {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ) : LinearMap.range (wangDifference f n) = LinearMap.ker (fibreHomologyMap f n) :=
  Algebra.range_difference_eq_ker _ _ (twoArc_exact_at_pair f n)

/-- Wang exactness at the torus: `range i_* = ker ∂`. -/
theorem MappingTorusHomology.wang_exact_at_mappingTorus {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (n : ℕ) :
    LinearMap.range (fibreHomologyMap f (n + 1)) = LinearMap.ker (wangBoundary f n) :=
  Algebra.range_inclusion_eq_ker_boundary _ _ _ (boundaryCoordinates_ker f n)
    (boundaryCoordinates_range f n)

/-- The Wang boundary range is `ker(id − f_*)`. -/
theorem MappingTorusHomology.wangBoundary_range {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ) : LinearMap.range (wangBoundary f n) = LinearMap.ker (wangDifference f n) :=
  Algebra.boundary_range _ _ (boundaryCoordinates_range f n)

/-- The fiber map on the Wang cokernel. -/
def MappingTorusHomology.cokernelInclusion {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) (n : ℕ) :
    (SingularMayerVietoris.SingularHomology X n ⧸ LinearMap.range (wangDifference f n)) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (MappingTorus.Torus f) n :=
  Algebra.cokernelInclusion _ _ (twoArc_exact_at_pair f n)

/-- The cokernel inclusion computes the fiber map. -/
@[simp]
theorem MappingTorusHomology.cokernelInclusion_mk {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    cokernelInclusion f n (Submodule.Quotient.mk a) = fibreHomologyMap f n a :=
  rfl

/-- The cokernel inclusion is injective. -/
theorem MappingTorusHomology.cokernelInclusion_injective {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (n : ℕ) : Function.Injective (cokernelInclusion f n) :=
  Algebra.cokernelInclusion_injective _ _ (twoArc_exact_at_pair f n)

/-- The Wang boundary into `ker(id − f_*)`. -/
def MappingTorusHomology.kernelBoundary {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) (n : ℕ) :
    SingularMayerVietoris.SingularHomology (MappingTorus.Torus f) (n + 1) →ₗ[ℤ]
      LinearMap.ker (wangDifference f n) :=
  Algebra.kernelBoundary _ _ (boundaryCoordinates_range f n)

/-- The Wang boundary surjects onto the difference kernel. -/
theorem MappingTorusHomology.kernelBoundary_surjective {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (n : ℕ) : Function.Surjective (kernelBoundary f n) :=
  Algebra.kernelBoundary_surjective _ _ (boundaryCoordinates_range f n)

/-- The shifted cokernel inclusion range is the Wang-boundary kernel. -/
theorem MappingTorusHomology.cokernelInclusion_range_eq_ker_kernelBoundary {X : Type}
    [TopologicalSpace X] (f : X ≃ₜ X) (n : ℕ) :
    LinearMap.range (cokernelInclusion f (n + 1)) = LinearMap.ker (kernelBoundary f n) :=
  Algebra.cokernelInclusion_range_eq_ker_kernelBoundary _ _ _ _ (twoArc_exact_at_pair f (n + 1))
    (boundaryCoordinates_ker f n) (boundaryCoordinates_range f n)

/-- The degree-zero fiber homology map is surjective. -/
theorem MappingTorusHomology.fibreHomologyMap_zero_surjective {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) : Function.Surjective (fibreHomologyMap f 0) := by
  intro b
  obtain ⟨a, ha⟩ :=
    SingularMayerVietoris.rightHomologyMap_zero_surjective (MappingTorus.HomologyCover.U f)
      (MappingTorus.HomologyCover.V f) (MappingTorus.HomologyCover.U_open f)
      (MappingTorus.HomologyCover.V_open f) (MappingTorus.HomologyCover.cover f) b
  exact
    ⟨(arcHomologyEquiv f 0 a).1 + (arcHomologyEquiv f 0 a).2,
      (rightHomologyMap_coordinates f 0 a).symm.trans ha⟩

/-- The degree-zero cokernel inclusion is surjective. -/
theorem MappingTorusHomology.cokernelInclusion_zero_surjective {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) : Function.Surjective (cokernelInclusion f 0) := by
  intro b
  obtain ⟨a, ha⟩ := fibreHomologyMap_zero_surjective f b
  exact ⟨Submodule.Quotient.mk a, ha⟩

/-- The degree-zero homology of the mapping torus is the coinvariants of `f_*`. -/
def MappingTorusHomology.degreeZeroHomologyEquiv {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    SingularMayerVietoris.SingularHomology (MappingTorus.Torus f) 0 ≃ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology X 0 ⧸ LinearMap.range (wangDifference f 0)) :=
  (LinearEquiv.ofBijective (cokernelInclusion f 0)
      ⟨cokernelInclusion_injective f 0, cokernelInclusion_zero_surjective f⟩).symm
