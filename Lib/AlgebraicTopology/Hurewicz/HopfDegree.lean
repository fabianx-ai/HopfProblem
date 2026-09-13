/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.CubeSphere
import Lib.AlgebraicTopology.FundamentalGroupoid.SimplyConnectedSphere
import Lib.AlgebraicTopology.SingularHomology.SphereHomology

/-!
# The Hopf degree theorem

For a simply connected space whose integral homology vanishes in degrees `2 ≤ k < n`,
`Hurewicz.pi_subsingleton_of_homology_vanishing` proves that its homotopy groups
vanish in the same range. In particular, `Hurewicz.sphere_pi_subsingleton_of_lt`
proves `Subsingleton (π_ k (SphereCube.Sphere n) x)` for `2 ≤ k < n`.

On the classification side, equality of the pushed-forward cube homology class of two
based sphere maps already forces them to be homotopic relative to the basepoint:
`Hurewicz.sphere_homotopicRel_of_topClass_eq` detects equality through the
injective Hurewicz map and descends the resulting cube homotopy through the sphere
quotient. `Hurewicz.sphere_homotopic_id_of_topClass` specializes this to
self-maps of a sphere preserving the top class, and
`Hurewicz.right_inverse_is_left_inverse` turns a homotopy right inverse of a sphere map
that is injective on top homology into a two-sided inverse.

## Outline of the proof

1. Strong induction supplies all lower homotopy-group hypotheses to
   `Hurewicz.hurewiczLinearEquivOfTwoLE`.
2. Injectivity transfers the assumed homology vanishing back to homotopy.
3. `EuclideanSphere.simplyConnectedSpace` and
   `SphereHomology.unitSphere_homology_subsingleton` specialize the result to spheres.
4. Free maps are adjusted at the basepoint by the homotopy extension property of the
   simplex, transported to the cube via `Hurewicz.simplexCubeHomeomorph`, and the
   quotient cylinder lift descends the homotopy to the sphere
   (`Hurewicz.exists_basepoint_adjustment`).
5. Injectivity of the sphere map on top homology, followed by the sphere-map
   classification, turns its right inverse into a left inverse
   (`Hurewicz.right_inverse_is_left_inverse`).

## Main definitions and results

* `Hurewicz.pi_subsingleton_of_homology_vanishing`: homology vanishing implies
  homotopy vanishing below the first possible nonzero degree.
* `Hurewicz.sphere_pi_subsingleton_of_lt`: the higher connectivity of spheres.
* `Hurewicz.sphere_homotopicRel_of_topClass_eq`: based sphere maps with equal
  pushed-forward cube classes are homotopic relative to the basepoint.
* `Hurewicz.sphere_homotopic_id_of_topClass`: a self-map of a sphere fixing the
  top cube class is homotopic to the identity.
* `Hurewicz.right_inverse_is_left_inverse`: a right inverse of a sphere map
  that is injective on top homology is two-sided.

Spaces are in `Type` because the integral singular-chain interface is universe zero.
This file uses plain imports until its legacy dependencies support the module system.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], Theorem 4.32 and Corollary 4.25;
  the sphere bootstrap is the application recorded in `Lib/docs/C.md`, §15, and the
  classification seam is recorded in `Lib/docs/C.md`, §15–16.

## Tags

Hurewicz theorem, sphere, connectivity, homotopy group, Hopf degree
-/

open Topology

noncomputable section

namespace Mathoverflow1973.Hurewicz

/-! ### Homology vanishing and strong induction -/

/-- In a simply connected space, homology vanishing below a degree implies homotopy
vanishing in degrees at least two below that degree. -/
theorem pi_subsingleton_of_homology_vanishing {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (hH : ∀ k, 2 ≤ k → k < n → Subsingleton (SingularMayerVietoris.SingularHomology X k))
    (k : ℕ) (hk : 2 ≤ k) (hkn : k < n) : Subsingleton (π_ k X x) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    letI : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
    letI := hH k hk hkn
    have hpi : ∀ j, 2 ≤ j → j < k → Subsingleton (π_ j X x) :=
      fun j hj hjk => ih j hjk hj (by omega)
    have hsub : Subsingleton (Additive (π_ k X x)) :=
      (hurewiczLinearEquivOfTwoLE x k hk hpi).injective.subsingleton
    exact ⟨fun a b => congrArg Additive.toMul
      (@Subsingleton.elim _ hsub (Additive.ofMul a) (Additive.ofMul b))⟩

/-! ### Sphere connectivity -/

/-- The homotopy groups of the n-sphere vanish in degrees `2 ≤ k < n`. -/
theorem sphere_pi_subsingleton_of_lt (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n)
    (x : SphereCube.Sphere n) : Subsingleton (π_ k (SphereCube.Sphere n) x) := by
  rcases n with _ | n
  · omega
  rcases n with _ | n
  · omega
  letI : SimplyConnectedSpace (SphereCube.Sphere (n + 2)) :=
    EuclideanSphere.simplyConnectedSpace n
  exact pi_subsingleton_of_homology_vanishing x (n + 2)
    (fun j hj hjn => SphereHomology.unitSphere_homology_subsingleton (n + 1) j
      (by omega) (by omega)) k hk hkn

/-! ### Sphere-map classification via the top cube class -/

open SphereCube SecondHurewicz.SimplyConnected

/-- The higher Hurewicz map in degree two agrees with the second Hurewicz map. -/
theorem hurewiczMap_eq_second {X : Type} [TopologicalSpace X] (x : X) :
    hurewiczMap (m := 0) x = SecondHurewicz.hurewiczMap x := by
  ext a
  change hurewiczMap (m := 0) x (Additive.ofMul (Additive.toMul a)) =
    SecondHurewicz.hurewiczMap x (Additive.ofMul (Additive.toMul a))
  refine Quotient.inductionOn (Additive.toMul a) ?_
  intro p
  exact cubeHomologyClass_eq_squareHomologyClass p

/-- Under vanishing of the lower homotopy groups, the Hurewicz map in degree `m + 2`
is injective. -/
theorem hurewiczMap_injective {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) {m : ℕ} (hpi : ∀ j, 2 ≤ j → j < m + 2 → Subsingleton (π_ j X x)) :
    Function.Injective (hurewiczMap (m := m) x) := by
  cases m with
  | zero =>
    rw [hurewiczMap_eq_second]
    exact (Hurewicz.degreeTwoLinearEquiv x).injective
  | succ m => exact (hurewiczLinearEquiv (m := m) x hpi).injective

/-- The descended cylinder homotopy agrees with the given cube homotopy on quotient
points. -/
theorem factorMap_homotopy_apply {n : ℕ} (hn : 0 < n) {X : Type*} [TopologicalSpace X]
    {x : X} {p q : GenLoop (Fin n) X x}
    (H : p.val.HomotopyRel q.val (Cube.boundary (Fin n))) (t : unitInterval)
    (u : Fin n → unitInterval) :
    factorMap_homotopy hn H (t, quotient n u) = H (t, u) := by
  have hfib : Function.FactorsThrough ⇑H.toHomotopy.toContinuousMap ⇑(cylinder n) := by
    rintro ⟨t, z⟩ ⟨s, w⟩ h
    have ht : t = s := congrArg Prod.fst h
    subst s
    have hzw : quotient n z = quotient n w := congrArg Prod.snd h
    rcases (quotient_eq_iff n z w).mp hzw with rfl | ⟨hz, hw⟩
    · rfl
    · exact
        ((H.eq_fst t hz).trans (p.property z hz)).trans
          ((H.eq_fst t hw).trans (p.property w hw)).symm
  change ((cylinder_isQuotientMap hn).lift H.toHomotopy.toContinuousMap hfib)
      (t, quotient n u) = H (t, u)
  exact ContinuousMap.congr_fun
    ((cylinder_isQuotientMap hn).lift_comp H.toContinuousMap hfib) (t, u)

/-- A homotopy of based cubes relative to the boundary descends to a homotopy of the
factor maps relative to the sphere basepoint. -/
def factorMap_homotopyRel {n : ℕ} (hn : 0 < n) {X : Type*} [TopologicalSpace X]
    {x : X} {p q : GenLoop (Fin n) X x}
    (H : p.val.HomotopyRel q.val (Cube.boundary (Fin n))) :
    (factorMap hn p).HomotopyRel (factorMap hn q) {point n}
    where
  toHomotopy := factorMap_homotopy hn H
  prop' t z hz := by
    have hz' : z = point n := hz
    subst z
    rw [← quotient_boundary n 0 (zero_boundary hn)]
    change (factorMap_homotopy hn H) (t, quotient n 0) = (factorMap hn p) (quotient n 0)
    rw [factorMap_homotopy_apply, factorMap_quotient]
    exact H.eq_fst t (zero_boundary hn)

/-- The based cube obtained from a map on the sphere that preserves the basepoint. -/
def basedSphereCube {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (f : C(Sphere n, X)) (hf : f (point n) = x) :
    GenLoop (Fin n) X x :=
  ⟨f.comp (quotient n), by
    intro u hu
    change f (quotient n u) = x
    rw [quotient_boundary n u hu]
    exact hf⟩

/-- Factoring the based cube of a based sphere map recovers the map. -/
theorem factorMap_basedSphereCube {n : ℕ} (hn : 0 < n) {X : Type} [TopologicalSpace X] {x : X}
    (f : C(Sphere n, X)) (hf : f (point n) = x) :
    factorMap hn (basedSphereCube f hf) = f :=
  (factorMap_unique hn (basedSphereCube f hf) f rfl).symm

/-- The cube homology class of a based sphere map's cube is the map's push-forward of
the quotient class. -/
theorem basedSphereCube_homologyClass {m : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (f : C(Sphere (m + 2), X))
    (hf : f (point (m + 2)) = x) :
    cubeHomologyClass (basedSphereCube f hf) =
      SingularMayerVietoris.singularHomologyMap f (m + 2)
        (cubeHomologyClass (quotientLoop (m + 2))) := by
  rw [← factor_cubeHomologyClass_cycle (basedSphereCube f hf), factorMap_basedSphereCube]

/-- Two based maps on a sphere whose push-forwards of the quotient cube class agree
are homotopic relative to the basepoint. -/
theorem sphere_homotopicRel_of_topClass_eq {m : ℕ} {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] {x : X}
    (hpi : ∀ j, 2 ≤ j → j < m + 2 → Subsingleton (π_ j X x))
    (f g : C(Sphere (m + 2), X))
    (hf : f (point (m + 2)) = x)
    (hg : g (point (m + 2)) = x)
    (h : SingularMayerVietoris.singularHomologyMap f (m + 2)
          (cubeHomologyClass (quotientLoop (m + 2))) =
        SingularMayerVietoris.singularHomologyMap g (m + 2)
          (cubeHomologyClass (quotientLoop (m + 2)))) :
    f.HomotopicRel g {point (m + 2)} := by
  have he : (⟦basedSphereCube f hf⟧ : π_ (m + 2) X x) = ⟦basedSphereCube g hg⟧ := by
    have hmap : hurewiczMap (m := m) x (Additive.ofMul (⟦basedSphereCube f hf⟧ : π_ (m + 2) X x)) =
        hurewiczMap (m := m) x (Additive.ofMul (⟦basedSphereCube g hg⟧ : π_ (m + 2) X x)) := by
      rw [hurewiczMap_representative, hurewiczMap_representative,
        basedSphereCube_homologyClass, basedSphereCube_homologyClass]
      exact h
    exact congrArg Additive.toMul (hurewiczMap_injective x hpi hmap)
  obtain ⟨H⟩ := Quotient.exact he
  have hh : (factorMap (show 0 < m + 2 by omega) (basedSphereCube f hf)).HomotopicRel
      (factorMap (show 0 < m + 2 by omega) (basedSphereCube g hg)) {point (m + 2)} :=
    ⟨factorMap_homotopyRel (by omega) H⟩
  simpa only [factorMap_basedSphereCube] using hh

/-- A map on a sphere can be adjusted along a path so that it becomes based at a
prescribed point, staying homotopic to the original map. -/
theorem exists_basepoint_adjustment {n : ℕ} (hn : 0 < n) {Y : Type*} [TopologicalSpace Y] {y : Y}
    (u : C(Sphere n, Y)) (P : Path (u (point n)) y) :
    ∃ v : C(Sphere n, Y), v (point n) = y ∧ u.Homotopic v := by
  let e := simplexCubeHomeomorph n
  let f : C(SingularChains.Simplex n, Y) := u.comp ((quotient n).comp (e : C(_, _)))
  let side : C(unitInterval × SimplexBoundary n, Y) := P.toContinuousMap.comp ContinuousMap.fst
  have h0 : ∀ s, side (0, s) = f s.val := by
    intro s
    change P 0 = u (quotient n (e s.val))
    rw [quotient_boundary n (e s.val) ((simplexCubeHomeomorph_boundary_iff n s.val).mpr s.property)]
    exact P.source
  let W := extendBoundaryHomotopy f side h0
  let C : C(unitInterval × (Fin n → unitInterval), Y) :=
    W.comp ((ContinuousMap.id unitInterval).prodMap (e.symm : C(_, _)))
  have hCboundary (t : unitInterval) (z : Fin n → unitInterval)
      (hz : z ∈ Cube.boundary (Fin n)) : C (t, z) = P t := by
    let s : SimplexBoundary n := ⟨e.symm z, (simplexCubeHomeomorph_symm_boundary_iff n z).mpr hz⟩
    exact extendBoundaryHomotopy_side f side h0 t s
  have hfib : ∀ a b, cylinder n a = cylinder n b → C a = C b := by
    rintro ⟨t, z⟩ ⟨s, w⟩ h
    have ht : t = s := congrArg Prod.fst h
    subst s
    have hzw : quotient n z = quotient n w := congrArg Prod.snd h
    rcases (quotient_eq_iff n z w).mp hzw with rfl | ⟨hz, hw⟩
    · rfl
    · exact (hCboundary t z hz).trans (hCboundary t w hw).symm
  let G := (cylinder_isQuotientMap hn).lift C hfib
  have hG (t : unitInterval) (z : Fin n → unitInterval) : G (t, quotient n z) = C (t, z) :=
    ContinuousMap.congr_fun ((cylinder_isQuotientMap hn).lift_comp C hfib) (t, z)
  let v : C(Sphere n, Y) := G.comp ⟨fun z => (1, z), continuous_const.prodMk continuous_id⟩
  refine ⟨v, ?_, ⟨{ toContinuousMap := G, map_zero_left := ?_, map_one_left := fun _ => rfl }⟩⟩
  · change G (1, point n) = y
    rw [← quotient_boundary n 0 (zero_boundary hn), hG]
    exact (hCboundary 1 0 (zero_boundary hn)).trans P.target
  · intro z
    obtain ⟨w, rfl⟩ := quotient_surjective hn z
    exact (hG 0 w).trans ((extendBoundaryHomotopy_bottom f side h0 (e.symm w)).trans
      (congrArg (fun q => u (quotient n q)) (e.apply_symm_apply w)))

/-- A self-map of a sphere that fixes the quotient cube class in top homology is
homotopic to the identity. -/
theorem sphere_homotopic_id_of_topClass {m : ℕ}
    (g : C(Sphere (m + 2), Sphere (m + 2)))
    (hd : SingularMayerVietoris.singularHomologyMap g (m + 2)
          (cubeHomologyClass (quotientLoop (m + 2))) =
        cubeHomologyClass (quotientLoop (m + 2))) :
    g.Homotopic (ContinuousMap.id (Sphere (m + 2))) := by
  letI : SimplyConnectedSpace (Sphere (m + 2)) := EuclideanSphere.simplyConnectedSpace m
  obtain ⟨v, hv, hgv⟩ := exists_basepoint_adjustment (show 0 < m + 2 by omega) g
    (PathConnectedSpace.somePath (g (point (m + 2))) (point (m + 2)))
  have hmap := SingularHomology.homotopic_homologyMap hgv (m + 2)
  have hvd : SingularMayerVietoris.singularHomologyMap v (m + 2)
      (cubeHomologyClass (quotientLoop (m + 2))) = cubeHomologyClass (quotientLoop (m + 2)) :=
    (LinearMap.congr_fun hmap _).symm.trans hd
  have hh := sphere_homotopicRel_of_topClass_eq
    (x := point (m + 2)) (fun j hj hjn => sphere_pi_subsingleton_of_lt (m + 2) j hj hjn (point (m + 2)))
    v (ContinuousMap.id (Sphere (m + 2))) hv rfl
    (by simpa only [SingularHomology.singularHomologyMap_id, LinearMap.id_apply] using hvd)
  obtain ⟨H⟩ := hh
  exact hgv.trans ⟨H.toHomotopy⟩

/-- A homotopy right inverse of a sphere map that is injective on top homology is
also a left homotopy inverse. -/
theorem right_inverse_is_left_inverse {m : ℕ} {X : Type} [TopologicalSpace X]
    (F : C(Sphere (m + 2), X))
    (g : C(X, Sphere (m + 2)))
    (hF : Function.Injective (SingularMayerVietoris.singularHomologyMap F (m + 2)))
    (hfg : (F.comp g).Homotopic (ContinuousMap.id X)) :
    (g.comp F).Homotopic (ContinuousMap.id (Sphere (m + 2))) := by
  have hh : (F.comp (g.comp F)).Homotopic F := by
    simpa only [ContinuousMap.comp_assoc, ContinuousMap.id_comp] using
      hfg.comp (ContinuousMap.Homotopic.refl F)
  apply sphere_homotopic_id_of_topClass
  apply hF
  have he := LinearMap.congr_fun (SingularHomology.homotopic_homologyMap hh (m + 2))
    (cubeHomologyClass (quotientLoop (m + 2)))
  rw [SingularHomology.singularHomologyMap_comp, LinearMap.comp_apply] at he
  exact he

end Mathoverflow1973.Hurewicz
