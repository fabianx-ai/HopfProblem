/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.SimplexCube
import Lib.AlgebraicTopology.SingularHomology.CrossProduct

set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

noncomputable section

namespace Mathoverflow1973

@[simp]
theorem SingularChains.simplexFace_vertex (n : ℕ) (i : Fin (n + 2)) (k : Fin (n + 1)) :
    simplexFace n i (stdSimplex.vertex (S := ℝ) k) = stdSimplex.vertex (S := ℝ) (i.succAbove k) :=
  by rw [simplexFace_apply, stdSimplex.map_vertex]

theorem SingularChains.simplex_contractible (n : ℕ) : ContractibleSpace (Simplex n) :=
  (convex_stdSimplex ℝ (Fin (n + 1))).contractibleSpace
    ⟨(stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1))).val,
      (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1))).property⟩

theorem SingularChains.simplex_simplyConnected (n : ℕ) : SimplyConnectedSpace (Simplex n) := by
  let _ := simplex_contractible n
  infer_instance

def SingularChains.triangleFacePath {X : Type*} [TopologicalSpace X] (σ : C(Simplex 2, X))
    (i : Fin 3) :
    Path (σ (stdSimplex.vertex (S := ℝ) (i.succAbove (0 : Fin 2))))
      (σ (stdSimplex.vertex (S := ℝ) (i.succAbove (1 : Fin 2)))) :=
  (simplexPath (σ.comp (simplexFace 1 i))).cast (congrArg σ (simplexFace_vertex 1 i 0)).symm
    (congrArg σ (simplexFace_vertex 1 i 1)).symm

abbrev SingularChains.triangleEdge01 {X : Type*} [TopologicalSpace X] (σ : C(Simplex 2, X)) :
    Path (σ (stdSimplex.vertex (S := ℝ) (0 : Fin 3)))
      (σ (stdSimplex.vertex (S := ℝ) (1 : Fin 3))) :=
  triangleFacePath σ 2

abbrev SingularChains.triangleEdge12 {X : Type*} [TopologicalSpace X] (σ : C(Simplex 2, X)) :
    Path (σ (stdSimplex.vertex (S := ℝ) (1 : Fin 3)))
      (σ (stdSimplex.vertex (S := ℝ) (2 : Fin 3))) :=
  triangleFacePath σ 0

abbrev SingularChains.triangleEdge02 {X : Type*} [TopologicalSpace X] (σ : C(Simplex 2, X)) :
    Path (σ (stdSimplex.vertex (S := ℝ) (0 : Fin 3)))
      (σ (stdSimplex.vertex (S := ℝ) (2 : Fin 3))) :=
  triangleFacePath σ 1

theorem SingularChains.triangleEdges_homotopic {X : Type*} [TopologicalSpace X]
    (σ : C(Simplex 2, X)) :
    ((triangleEdge01 σ).trans (triangleEdge12 σ)).Homotopic (triangleEdge02 σ) := by
  let _ := simplex_simplyConnected 2
  have h :=
    SimplyConnectedSpace.paths_homotopic
      ((triangleEdge01 (ContinuousMap.id (Simplex 2))).trans
        (triangleEdge12 (ContinuousMap.id (Simplex 2))))
      (triangleEdge02 (ContinuousMap.id (Simplex 2)))
  have hmap := h.map σ
  rw [Path.map_trans] at hmap
  exact hmap

def SecondHurewicz.SimplyConnected.VerticesBased {X : Type} [TopologicalSpace X] (x : X) (n : ℕ)
    (smp : C(SingularChains.Simplex n, X)) : Prop :=
  ∀ i : Fin (n + 1), smp (stdSimplex.vertex (S := ℝ) i) = x

theorem SecondHurewicz.SimplyConnected.VerticesBased.face {X : Type} [TopologicalSpace X] {x : X}
    {n : ℕ} {smp : C(SingularChains.Simplex (n + 1), X)}
    (h : SecondHurewicz.SimplyConnected.VerticesBased x (n + 1) smp) (i : Fin (n + 2)) :
    SecondHurewicz.SimplyConnected.VerticesBased x n (smp.comp (SingularChains.simplexFace n i)) :=
  by
  intro j
  change smp (SingularChains.simplexFace n i (stdSimplex.vertex (S := ℝ) j)) = x
  rw [SingularChains.simplexFace_vertex]
  exact h (i.succAbove j)

@[simp]
theorem SecondHurewicz.SimplyConnected.verticesBased_const {X : Type} [TopologicalSpace X] (x : X)
    (n : ℕ) : VerticesBased x n (ContinuousMap.const (SingularChains.Simplex n) x) := fun _ => rfl

theorem SecondHurewicz.SimplyConnected.verticesBased_zero_iff {X : Type} [TopologicalSpace X]
    {x : X} {smp : C(SingularChains.Simplex 0, X)} :
    VerticesBased x 0 smp ↔ smp = ContinuousMap.const (SingularChains.Simplex 0) x := by
  constructor
  · intro h
    apply ContinuousMap.ext
    intro s
    change smp s = x
    rw [SingularChains.simplexZero_eq_vertex s]
    exact h 0
  · rintro rfl
    exact verticesBased_const x 0

theorem SecondHurewicz.SimplyConnected.simplexVertex_exists_face (n : ℕ) (k : Fin (n + 2)) :
    ∃ i : Fin (n + 2),
      ∃ j : Fin (n + 1),
        SingularChains.simplexFace n i (stdSimplex.vertex (S := ℝ) j) =
          stdSimplex.vertex (S := ℝ) k := by
  obtain ⟨i, hi⟩ := exists_ne k
  obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hi.symm
  refine ⟨i, j, ?_⟩
  rw [SingularChains.simplexFace_vertex, hj]

def SecondHurewicz.SimplyConnected.simplexFaceInverse (n : ℕ) (i : Fin (n + 2)) :
    C({ s : SingularChains.Simplex (n + 1) // s i = 0 }, SingularChains.Simplex n)
    where
  toFun
    s :=
    ⟨fun k => s.val (i.succAbove k),
      ⟨fun k => stdSimplex.zero_le s.val (i.succAbove k),
        by
        have hs := stdSimplex.sum_eq_one s.val
        rw [Fin.sum_univ_succAbove _ i, s.property, zero_add] at hs
        exact hs⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro k
    have hc : Continuous (fun s : SingularChains.Simplex (n + 1) => s (i.succAbove k)) :=
      (continuous_apply (i.succAbove k)).comp continuous_subtype_val
    exact hc.comp continuous_subtype_val

@[simp]
theorem SecondHurewicz.SimplyConnected.simplexFace_inverse (n : ℕ) (i : Fin (n + 2))
    (s : { s : SingularChains.Simplex (n + 1) // s i = 0 }) :
    SingularChains.simplexFace n i (simplexFaceInverse n i s) = s.val := by
  apply Subtype.ext
  funext k
  change SingularChains.simplexFace n i (simplexFaceInverse n i s) k = s.val k
  by_cases hk : k = i
  · subst k
    exact (SingularChains.simplexFace_apply_self n i _).trans s.property.symm
  · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hk
    exact SingularChains.simplexFace_apply_succAbove n i _ l

theorem SecondHurewicz.SimplyConnected.simplexFace_range (n : ℕ) (i : Fin (n + 2)) :
    Set.range (SingularChains.simplexFace n i) = {s : SingularChains.Simplex (n + 1) | s i = 0} := by
  ext s
  constructor
  · rintro ⟨t, rfl⟩
    exact SingularChains.simplexFace_apply_self n i t
  · intro hs
    exact ⟨simplexFaceInverse n i ⟨s, hs⟩, simplexFace_inverse n i ⟨s, hs⟩⟩

theorem SecondHurewicz.SimplyConnected.simplexFace_injective (n : ℕ) (i : Fin (n + 2)) :
    Function.Injective (SingularChains.simplexFace n i) := by
  intro s t h
  apply Subtype.ext
  funext k
  change s k = t k
  have hk := congrArg (fun u : SingularChains.Simplex (n + 1) => u (i.succAbove k)) h
  simpa only [SingularChains.simplexFace_apply_succAbove] using hk

def SecondHurewicz.SimplyConnected.simplexFaceBoundary (n : ℕ) (i : Fin (n + 2)) :
    C(SingularChains.Simplex n, SimplexBoundary (n + 1))
    where
  toFun s := ⟨SingularChains.simplexFace n i s, simplexFace_mem_boundary n i s⟩
  continuous_toFun := (SingularChains.simplexFace n i).continuous.subtype_mk _

theorem SecondHurewicz.SimplyConnected.simplexBoundary_exists_face (n : ℕ)
    (s : SimplexBoundary (n + 1)) :
    ∃ i : Fin (n + 2), ∃ t : SingularChains.Simplex n, simplexFaceBoundary n i t = s := by
  obtain ⟨i, hi⟩ := s.property
  have hmem : s.val ∈ Set.range (SingularChains.simplexFace n i) := by
    rw [simplexFace_range]
    exact hi
  obtain ⟨t, ht⟩ := hmem
  exact ⟨i, t, Subtype.ext ht⟩

def SecondHurewicz.SimplyConnected.simplexFaceCylinder (n : ℕ) (i : Fin (n + 2)) :
    C((unitInterval) × SingularChains.Simplex n, (unitInterval) × SimplexBoundary (n + 1)) :=
  (ContinuousMap.id (unitInterval)).prodMap (simplexFaceBoundary n i)

def SecondHurewicz.SimplyConnected.simplexFaceCover (n : ℕ) :
    C((Σ _i : Fin (n + 2), (unitInterval) × SingularChains.Simplex n),
      (unitInterval) × SimplexBoundary (n + 1))
    where
  toFun a := simplexFaceCylinder n a.fst a.snd
  continuous_toFun := continuous_sigma fun i => (simplexFaceCylinder n i).continuous

theorem SecondHurewicz.SimplyConnected.simplexFaceCover_surjective (n : ℕ) :
    Function.Surjective (simplexFaceCover n) := by
  rintro ⟨r, s⟩
  obtain ⟨i, t, rfl⟩ := simplexBoundary_exists_face n s
  exact ⟨⟨i, (r, t)⟩, rfl⟩

theorem SecondHurewicz.SimplyConnected.simplexFaceCover_isQuotientMap (n : ℕ) :
    Topology.IsQuotientMap (simplexFaceCover n) :=
  Topology.IsQuotientMap.of_surjective_continuous (simplexFaceCover_surjective n)
    (simplexFaceCover n).continuous

def SecondHurewicz.SimplyConnected.FaceCompatible {X : Type} [TopologicalSpace X] {n : ℕ}
    (F : Fin (n + 2) → C((unitInterval) × SingularChains.Simplex n, X)) : Prop :=
  ∀ (i j : Fin (n + 2)) (s t : SingularChains.Simplex n),
    SingularChains.simplexFace n i s = SingularChains.simplexFace n j t →
      ∀ r : (unitInterval), F i (r, s) = F j (r, t)

def SecondHurewicz.SimplyConnected.faceFamilyMap {X : Type} [TopologicalSpace X] {n : ℕ}
    (F : Fin (n + 2) → C((unitInterval) × SingularChains.Simplex n, X)) :
    C((Σ _i : Fin (n + 2), (unitInterval) × SingularChains.Simplex n), X)
    where
  toFun a := F a.fst a.snd
  continuous_toFun := continuous_sigma fun i => (F i).continuous

theorem SecondHurewicz.SimplyConnected.faceFamilyMap_factorsThrough {X : Type}
    [TopologicalSpace X] {n : ℕ}
    (F : Fin (n + 2) → C((unitInterval) × SingularChains.Simplex n, X)) (hF : FaceCompatible F) :
    Function.FactorsThrough (faceFamilyMap F) (simplexFaceCover n) := by
  rintro ⟨i, r, s⟩ ⟨j, q, t⟩ h
  have hr : r = q := congrArg Prod.fst h
  have hs : SingularChains.simplexFace n i s = SingularChains.simplexFace n j t :=
    congrArg (fun u : (unitInterval) × SimplexBoundary (n + 1) => u.2.val) h
  subst q
  exact hF i j s t hs r

def SecondHurewicz.SimplyConnected.glueFaceHomotopies {X : Type} [TopologicalSpace X] {n : ℕ}
    (F : Fin (n + 2) → C((unitInterval) × SingularChains.Simplex n, X)) (hF : FaceCompatible F) :
    C((unitInterval) × SimplexBoundary (n + 1), X) :=
  (simplexFaceCover_isQuotientMap n).lift (faceFamilyMap F) (faceFamilyMap_factorsThrough F hF)

@[simp]
theorem SecondHurewicz.SimplyConnected.glueFaceHomotopies_face {X : Type} [TopologicalSpace X]
    {n : ℕ} (F : Fin (n + 2) → C((unitInterval) × SingularChains.Simplex n, X))
    (hF : FaceCompatible F) (i : Fin (n + 2)) (r : (unitInterval)) (s : SingularChains.Simplex n) :
    glueFaceHomotopies F hF (r, simplexFaceBoundary n i s) = F i (r, s) := by
  exact
    congrArg (fun f => f ⟨i, (r, s)⟩)
      ((simplexFaceCover_isQuotientMap n).lift_comp (faceFamilyMap F)
        (faceFamilyMap_factorsThrough F hF))

theorem SecondHurewicz.SimplyConnected.glueFaceHomotopies_time {X : Type} [TopologicalSpace X]
    {n : ℕ} (F : Fin (n + 2) → C((unitInterval) × SingularChains.Simplex n, X))
    (hF : FaceCompatible F) (r : (unitInterval)) (g : SingularChains.Simplex (n + 1) → X)
    (h :
      ∀ (i : Fin (n + 2)) (s : SingularChains.Simplex n),
        F i (r, s) = g (SingularChains.simplexFace n i s))
    (b : SimplexBoundary (n + 1)) : glueFaceHomotopies F hF (r, b) = g b.val := by
  obtain ⟨i, s, rfl⟩ := simplexBoundary_exists_face n b
  exact (glueFaceHomotopies_face F hF i r s).trans (h i s)

theorem SecondHurewicz.SimplyConnected.glueFaceHomotopies_zero {X : Type} [TopologicalSpace X]
    {n : ℕ} (F : Fin (n + 2) → C((unitInterval) × SingularChains.Simplex n, X))
    (hF : FaceCompatible F) (g : C(SingularChains.Simplex (n + 1), X))
    (h :
      ∀ (i : Fin (n + 2)) (s : SingularChains.Simplex n),
        F i (0, s) = g (SingularChains.simplexFace n i s))
    (b : SimplexBoundary (n + 1)) : glueFaceHomotopies F hF (0, b) = g b.val :=
  glueFaceHomotopies_time F hF 0 g h b

theorem SecondHurewicz.SimplyConnected.glueFaceHomotopies_unique {X : Type} [TopologicalSpace X]
    {n : ℕ} (F : Fin (n + 2) → C((unitInterval) × SingularChains.Simplex n, X))
    (hF : FaceCompatible F) (G : C((unitInterval) × SimplexBoundary (n + 1), X))
    (hG :
      ∀ (i : Fin (n + 2)) (r : (unitInterval)) (s : SingularChains.Simplex n),
        G (r, simplexFaceBoundary n i s) = F i (r, s)) :
    G = glueFaceHomotopies F hF := by
  ext u
  rcases u with ⟨r, b⟩
  obtain ⟨i, s, rfl⟩ := simplexBoundary_exists_face n b
  exact (hG i r s).trans (glueFaceHomotopies_face F hF i r s).symm

theorem SingularChains.simplexFace_comp {n : ℕ} {i j : Fin (n + 2)}
    (h : i ≤ j) :
    (SingularChains.simplexFace (n + 1) j.succ).comp (SingularChains.simplexFace n i) =
      (SingularChains.simplexFace (n + 1) i.castSucc).comp (SingularChains.simplexFace n j) := by
  have hf :=
    congrArg
      (fun f : (SimplexCategory.mk (n)) ⟶ (SimplexCategory.mk (n + 2)) =>
        (SimplexCategory.toTop₀.map f).hom)
      (SimplexCategory.δ_comp_δ h)
  have hl :=
    congrArg
      (fun f :
          SimplexCategory.toTop₀.obj (SimplexCategory.mk (n)) ⟶
            SimplexCategory.toTop₀.obj (SimplexCategory.mk (n + 2)) =>
        f.hom)
      (SimplexCategory.toTop₀.map_comp (SimplexCategory.δ i) (SimplexCategory.δ j.succ))
  have hr :=
    congrArg
      (fun f :
          SimplexCategory.toTop₀.obj (SimplexCategory.mk (n)) ⟶
            SimplexCategory.toTop₀.obj (SimplexCategory.mk (n + 2)) =>
        f.hom)
      (SimplexCategory.toTop₀.map_comp (SimplexCategory.δ j) (SimplexCategory.δ i.castSucc))
  exact hl.symm.trans (hf.trans hr)

theorem SingularChains.singularSimplex_face_face {X : Type*}
    [TopologicalSpace X] {n : ℕ} (σ : C(SingularChains.Simplex (n + 2), X)) {i j : Fin (n + 2)}
    (h : i ≤ j) :
    (σ.comp (SingularChains.simplexFace (n + 1) j.succ)).comp (SingularChains.simplexFace n i) =
      (σ.comp (SingularChains.simplexFace (n + 1) i.castSucc)).comp
        (SingularChains.simplexFace n j) := by
  simpa only [ContinuousMap.comp_assoc] using
    congrArg (fun f : C(SingularChains.Simplex n, SingularChains.Simplex (n + 2)) => σ.comp f)
      (simplexFace_comp h)

theorem SecondHurewicz.SimplyConnected.simplexFace_intersection {n : ℕ} {i j : Fin (n + 2)}
    (hij : i ≤ j) {s t : SingularChains.Simplex (n + 1)}
    (h :
      SingularChains.simplexFace (n + 1) j.succ s =
        SingularChains.simplexFace (n + 1) i.castSucc t) :
    ∃ u : SingularChains.Simplex n,
      SingularChains.simplexFace n i u = s ∧ SingularChains.simplexFace n j u = t := by
  have hs : s i = 0 := by
    calc
      s i = SingularChains.simplexFace (n + 1) j.succ s (j.succ.succAbove i) :=
        (SingularChains.simplexFace_apply_succAbove (n + 1) j.succ s i).symm
      _ = SingularChains.simplexFace (n + 1) j.succ s i.castSucc := by
        rw [Fin.succAbove_succ_of_le j i hij]
      _ = SingularChains.simplexFace (n + 1) i.castSucc t i.castSucc :=
        (congrArg (fun v : SingularChains.Simplex (n + 2) => v i.castSucc) h)
      _ = 0 := SingularChains.simplexFace_apply_self (n + 1) i.castSucc t
  let u := simplexFaceInverse n i ⟨s, hs⟩
  have hu : SingularChains.simplexFace n i u = s := simplexFace_inverse n i ⟨s, hs⟩
  refine ⟨u, hu, simplexFace_injective (n + 1) i.castSucc ?_⟩
  calc
    SingularChains.simplexFace (n + 1) i.castSucc (SingularChains.simplexFace n j u) =
        SingularChains.simplexFace (n + 1) j.succ (SingularChains.simplexFace n i u) :=
      (congrArg (fun f : C(SingularChains.Simplex n, SingularChains.Simplex (n + 2)) => f u)
          (SingularChains.simplexFace_comp hij)).symm
    _ = SingularChains.simplexFace (n + 1) j.succ s :=
      (congrArg (SingularChains.simplexFace (n + 1) j.succ) hu)
    _ = SingularChains.simplexFace (n + 1) i.castSucc t := h

def SecondHurewicz.SimplyConnected.CofaceCompatible {X : Type} [TopologicalSpace X] {n : ℕ}
    (F : Fin (n + 3) → C((unitInterval) × SingularChains.Simplex (n + 1), X)) : Prop :=
  ∀ (i j : Fin (n + 2)),
    i ≤ j →
      ∀ (r : (unitInterval)) (u : SingularChains.Simplex n),
        F j.succ (r, SingularChains.simplexFace n i u) =
          F i.castSucc (r, SingularChains.simplexFace n j u)

private theorem SecondHurewicz.SimplyConnected.faceCompatible_of_cofaceCompatible_lt_mo1973_6084
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (F : Fin (n + 3) → C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (hF : CofaceCompatible F) {a b : Fin (n + 3)} (hab : a < b)
    {s t : SingularChains.Simplex (n + 1)}
    (hst : SingularChains.simplexFace (n + 1) a s = SingularChains.simplexFace (n + 1) b t)
    (r : (unitInterval)) : F a (r, s) = F b (r, t) := by
  obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr (Fin.ne_last_of_lt hab)
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr (Fin.ne_zero_of_lt hab)
  have hij : i ≤ j := Fin.castSucc_lt_succ_iff.mp hab
  obtain ⟨u, hu, hv⟩ := simplexFace_intersection hij hst.symm
  rw [← hu, ← hv]
  exact (hF i j hij r u).symm

theorem SecondHurewicz.SimplyConnected.faceCompatible_of_cofaceCompatible {X : Type}
    [TopologicalSpace X] {n : ℕ}
    (F : Fin (n + 3) → C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (hF : CofaceCompatible F) : FaceCompatible F := by
  intro a b s t hst r
  rcases lt_trichotomy a b with hab | hab | hba
  · exact faceCompatible_of_cofaceCompatible_lt_mo1973_6084 F hF hab hst r
  · subst b
    exact congrArg (fun u => F a (r, u)) (simplexFace_injective (n + 1) a hst)
  · exact (faceCompatible_of_cofaceCompatible_lt_mo1973_6084 F hF hba hst.symm r).symm

theorem SecondHurewicz.SimplyConnected.faceCompatible_zero {X : Type} [TopologicalSpace X]
    (F : Fin 2 → C((unitInterval) × SingularChains.Simplex 0, X)) : FaceCompatible F := by
  intro i j s t hst r
  have hs : s = t := by
    rw [SingularChains.simplexZero_eq_vertex s, SingularChains.simplexZero_eq_vertex t]
  subst t
  fin_cases i <;> fin_cases j
  · rfl
  · have h : (1 : Fin 2) = 0 :=
      stdSimplex.vertex_injective
        ((SingularChains.simplexFace_zero_zero s).symm.trans
          (hst.trans (SingularChains.simplexFace_zero_one s)))
    exact False.elim ((by decide : (1 : Fin 2) ≠ 0) h)
  · have h : (0 : Fin 2) = 1 :=
      stdSimplex.vertex_injective
        ((SingularChains.simplexFace_zero_one s).symm.trans
          (hst.trans (SingularChains.simplexFace_zero_zero s)))
    exact False.elim ((by decide : (0 : Fin 2) ≠ 1) h)
  · rfl

def SecondHurewicz.SimplyConnected.minimumCoordinate {n : ℕ} (s : SingularChains.Simplex n) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => s i)

theorem SecondHurewicz.SimplyConnected.minimumCoordinate_nonneg {n : ℕ}
    (s : SingularChains.Simplex n) : 0 ≤ minimumCoordinate s :=
  Finset.le_inf' _ _ fun i _ => stdSimplex.zero_le s i

theorem SecondHurewicz.SimplyConnected.minimumCoordinate_le {n : ℕ} (s : SingularChains.Simplex n)
    (i : Fin (n + 1)) : minimumCoordinate s ≤ s i :=
  Finset.inf'_le _ (Finset.mem_univ i)

theorem SecondHurewicz.SimplyConnected.exists_coordinate_eq_minimum {n : ℕ}
    (s : SingularChains.Simplex n) : ∃ i : Fin (n + 1), s i = minimumCoordinate s := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun i => s i)
  exact ⟨i, hi.symm⟩

theorem SecondHurewicz.SimplyConnected.continuous_minimumCoordinate (n : ℕ) :
    Continuous (minimumCoordinate (n := n)) :=
  Continuous.finset_inf'_apply _ fun i _ => (continuous_apply i).comp continuous_subtype_val

theorem SecondHurewicz.SimplyConnected.minimumCoordinate_eq_zero_of_mem_boundary {n : ℕ}
    {s : SingularChains.Simplex n} (hs : s ∈ simplexBoundary n) : minimumCoordinate s = 0 := by
  obtain ⟨i, hi⟩ := hs
  exact le_antisymm (hi ▸ minimumCoordinate_le s i) (minimumCoordinate_nonneg s)

def SecondHurewicz.SimplyConnected.barycenterCoordinate (n : ℕ) : ℝ :=
  ((n : ℝ) + 1)⁻¹

theorem SecondHurewicz.SimplyConnected.simplexCard_pos (n : ℕ) : 0 < (n : ℝ) + 1 := by positivity

theorem SecondHurewicz.SimplyConnected.barycenterCoordinate_pos (n : ℕ) :
    0 < barycenterCoordinate n :=
  inv_pos.mpr (simplexCard_pos n)

theorem SecondHurewicz.SimplyConnected.card_mul_barycenterCoordinate (n : ℕ) :
    ((n : ℝ) + 1) * barycenterCoordinate n = 1 :=
  mul_inv_cancel₀ (ne_of_gt (simplexCard_pos n))

def SecondHurewicz.SimplyConnected.cylinderDenominator {n : ℕ}
    (u : unitInterval × SingularChains.Simplex n) : ℝ :=
  Max.max (1 - (u.1 : ℝ) / 2) (1 - ((n : ℝ) + 1) * minimumCoordinate u.2)

theorem SecondHurewicz.SimplyConnected.cylinderDenominator_half_le {n : ℕ}
    (u : unitInterval × SingularChains.Simplex n) : 1 / 2 ≤ cylinderDenominator u := by
  have ht := u.1.property.2
  exact (show 1 / 2 ≤ 1 - (u.1 : ℝ) / 2 by linarith).trans (le_max_left _ _)

theorem SecondHurewicz.SimplyConnected.cylinderDenominator_pos {n : ℕ}
    (u : unitInterval × SingularChains.Simplex n) : 0 < cylinderDenominator u :=
  lt_of_lt_of_le (by norm_num) (cylinderDenominator_half_le u)

theorem SecondHurewicz.SimplyConnected.cylinderDenominator_ne_zero {n : ℕ}
    (u : unitInterval × SingularChains.Simplex n) : cylinderDenominator u ≠ 0 :=
  ne_of_gt (cylinderDenominator_pos u)

theorem SecondHurewicz.SimplyConnected.cylinderDenominator_le_one {n : ℕ}
    (u : unitInterval × SingularChains.Simplex n) : cylinderDenominator u ≤ 1 := by
  apply max_le
  · have ht := u.1.property.1
    linarith
  · have hm := mul_nonneg (le_of_lt (simplexCard_pos n)) (minimumCoordinate_nonneg u.2)
    linarith

theorem SecondHurewicz.SimplyConnected.bottomDenominator_le {n : ℕ}
    (u : unitInterval × SingularChains.Simplex n) : 1 - (u.1 : ℝ) / 2 ≤ cylinderDenominator u :=
  le_max_left _ _

theorem SecondHurewicz.SimplyConnected.sideDenominator_le {n : ℕ}
    (u : unitInterval × SingularChains.Simplex n) :
    1 - ((n : ℝ) + 1) * minimumCoordinate u.2 ≤ cylinderDenominator u :=
  le_max_right _ _

theorem SecondHurewicz.SimplyConnected.coordinateDenominator_le {n : ℕ}
    (u : unitInterval × SingularChains.Simplex n) (i : Fin (n + 1)) :
    1 - ((n : ℝ) + 1) * u.2 i ≤ cylinderDenominator u := by
  have hm := mul_le_mul_of_nonneg_left (minimumCoordinate_le u.2 i) (le_of_lt (simplexCard_pos n))
  exact (sub_le_sub_left hm 1).trans (sideDenominator_le u)

theorem SecondHurewicz.SimplyConnected.continuous_cylinderDenominator (n : ℕ) :
    Continuous (cylinderDenominator (n := n)) :=
  (continuous_const.sub ((continuous_subtype_val.comp continuous_fst).div_const 2)).max
    (continuous_const.sub
      (continuous_const.mul ((continuous_minimumCoordinate n).comp continuous_snd)))

theorem SecondHurewicz.SimplyConnected.cylinderDenominator_eq_one_of_mem {n : ℕ}
    {u : unitInterval × SingularChains.Simplex n} (hu : u ∈ bottomOrSide n) :
    cylinderDenominator u = 1 := by
  apply le_antisymm (cylinderDenominator_le_one u)
  rcases hu with ht | hs
  · have h := bottomDenominator_le u
    rw [ht] at h
    change 1 - (0 : ℝ) / 2 ≤ cylinderDenominator u at h
    simpa only [zero_div, sub_zero] using h
  · have h := sideDenominator_le u
    simpa only [minimumCoordinate_eq_zero_of_mem_boundary hs, MulZeroClass.mul_zero,
      sub_zero] using h

theorem SecondHurewicz.SimplyConnected.retractedTime_nonneg {n : ℕ}
    (u : unitInterval × SingularChains.Simplex n) :
    0 ≤ ((u.1 : ℝ) + 2 * cylinderDenominator u - 2) / cylinderDenominator u := by
  apply div_nonneg _ (le_of_lt (cylinderDenominator_pos u))
  have h := bottomDenominator_le u
  linarith

theorem SecondHurewicz.SimplyConnected.retractedTime_le_one {n : ℕ}
    (u : unitInterval × SingularChains.Simplex n) :
    ((u.1 : ℝ) + 2 * cylinderDenominator u - 2) / cylinderDenominator u ≤ 1 := by
  apply (div_le_one (cylinderDenominator_pos u)).mpr
  have ht := u.1.property.2
  have hd := cylinderDenominator_le_one u
  linarith

def SecondHurewicz.SimplyConnected.retractedTime {n : ℕ}
    (u : unitInterval × SingularChains.Simplex n) : unitInterval :=
  ⟨((u.1 : ℝ) + 2 * cylinderDenominator u - 2) / cylinderDenominator u, retractedTime_nonneg u,
    retractedTime_le_one u⟩

theorem SecondHurewicz.SimplyConnected.continuous_retractedTime (n : ℕ) :
    Continuous (retractedTime (n := n)) := by
  apply Continuous.subtype_mk
  exact
    (((continuous_subtype_val.comp continuous_fst).add
              (continuous_const.mul (continuous_cylinderDenominator n))).sub
          continuous_const).div
      (continuous_cylinderDenominator n) cylinderDenominator_ne_zero

theorem SecondHurewicz.SimplyConnected.retractedCoordinate_numerator_nonneg {n : ℕ}
    (u : unitInterval × SingularChains.Simplex n) (i : Fin (n + 1)) :
    0 ≤ u.2 i + (cylinderDenominator u - 1) * barycenterCoordinate n := by
  have h :=
    mul_nonneg (sub_nonneg.mpr (coordinateDenominator_le u i))
      (le_of_lt (barycenterCoordinate_pos n))
  have he :
    (cylinderDenominator u - (1 - ((n : ℝ) + 1) * u.2 i)) * barycenterCoordinate n =
      u.2 i + (cylinderDenominator u - 1) * barycenterCoordinate n := by
    calc
      _ =
          (cylinderDenominator u - 1) * barycenterCoordinate n +
            u.2 i * (((n : ℝ) + 1) * barycenterCoordinate n) := by ring
      _ = _ := by rw [card_mul_barycenterCoordinate]; ring
  exact he ▸ h

theorem SecondHurewicz.SimplyConnected.retractedCoordinate_nonneg {n : ℕ}
    (u : unitInterval × SingularChains.Simplex n) (i : Fin (n + 1)) :
    0 ≤ (u.2 i + (cylinderDenominator u - 1) * barycenterCoordinate n) / cylinderDenominator u :=
  div_nonneg (retractedCoordinate_numerator_nonneg u i) (le_of_lt (cylinderDenominator_pos u))

theorem SecondHurewicz.SimplyConnected.retractedCoordinates_sum {n : ℕ}
    (u : unitInterval × SingularChains.Simplex n) :
    ∑ i : Fin (n + 1),
        (u.2 i + (cylinderDenominator u - 1) * barycenterCoordinate n) / cylinderDenominator u =
      1 := by
  have hsum :
    (∑ _i : Fin (n + 1), (cylinderDenominator u - 1) * barycenterCoordinate n) =
      cylinderDenominator u - 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
      Nat.cast_one]
    calc
      _ = (cylinderDenominator u - 1) * (((n : ℝ) + 1) * barycenterCoordinate n) := by ring
      _ = _ := by rw [card_mul_barycenterCoordinate, mul_one]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, Finset.sum_add_distrib, stdSimplex.sum_eq_one, hsum]
  rw [show 1 + (cylinderDenominator u - 1) = cylinderDenominator u by ring,
    mul_inv_cancel₀ (cylinderDenominator_ne_zero u)]

def SecondHurewicz.SimplyConnected.retractedSimplex {n : ℕ}
    (u : unitInterval × SingularChains.Simplex n) : SingularChains.Simplex n :=
  ⟨fun i =>
    (u.2 i + (cylinderDenominator u - 1) * barycenterCoordinate n) / cylinderDenominator u,
    retractedCoordinate_nonneg u, retractedCoordinates_sum u⟩

theorem SecondHurewicz.SimplyConnected.continuous_retractedSimplex (n : ℕ) :
    Continuous (retractedSimplex (n := n)) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact
    (((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)).add
          (((continuous_cylinderDenominator n).sub continuous_const).mul continuous_const)).div
      (continuous_cylinderDenominator n) cylinderDenominator_ne_zero

theorem SecondHurewicz.SimplyConnected.retractedTime_eq_of_mem {n : ℕ}
    {u : unitInterval × SingularChains.Simplex n} (hu : u ∈ bottomOrSide n) :
    retractedTime u = u.1 := by
  apply Subtype.ext
  change ((u.1 : ℝ) + 2 * cylinderDenominator u - 2) / cylinderDenominator u = (u.1 : ℝ)
  rw [cylinderDenominator_eq_one_of_mem hu]
  ring

theorem SecondHurewicz.SimplyConnected.retractedSimplex_eq_of_mem {n : ℕ}
    {u : unitInterval × SingularChains.Simplex n} (hu : u ∈ bottomOrSide n) :
    retractedSimplex u = u.2 := by
  apply Subtype.ext
  funext i
  change
    (u.2 i + (cylinderDenominator u - 1) * barycenterCoordinate n) / cylinderDenominator u = u.2 i
  rw [cylinderDenominator_eq_one_of_mem hu]
  simp

theorem SecondHurewicz.SimplyConnected.retracted_mem_bottomOrSide {n : ℕ}
    (u : unitInterval × SingularChains.Simplex n) :
    (retractedTime u, retractedSimplex u) ∈ bottomOrSide n := by
  rcases le_total (1 - ((n : ℝ) + 1) * minimumCoordinate u.2) (1 - (u.1 : ℝ) / 2) with h | h
  · have hd : cylinderDenominator u = 1 - (u.1 : ℝ) / 2 := max_eq_left h
    left
    apply Subtype.ext
    change ((u.1 : ℝ) + 2 * cylinderDenominator u - 2) / cylinderDenominator u = 0
    have hn : (u.1 : ℝ) + 2 * cylinderDenominator u - 2 = 0 := by rw [hd]; ring
    rw [hn, zero_div]
  · have hd : cylinderDenominator u = 1 - ((n : ℝ) + 1) * minimumCoordinate u.2 := max_eq_right h
    right
    obtain ⟨i, hi⟩ := exists_coordinate_eq_minimum u.2
    refine ⟨i, ?_⟩
    change
      (u.2 i + (cylinderDenominator u - 1) * barycenterCoordinate n) / cylinderDenominator u = 0
    have hn : u.2 i + (cylinderDenominator u - 1) * barycenterCoordinate n = 0 := by
      rw [hi, hd]
      calc
        _ =
            minimumCoordinate u.2 -
              minimumCoordinate u.2 * (((n : ℝ) + 1) * barycenterCoordinate n) := by ring
        _ = 0 := by rw [card_mul_barycenterCoordinate]; ring
    rw [hn, zero_div]

def SecondHurewicz.SimplyConnected.cylinderRetraction (n : ℕ) :
    C(unitInterval × SingularChains.Simplex n, ↥(bottomOrSide n))
    where
  toFun u := ⟨(retractedTime u, retractedSimplex u), retracted_mem_bottomOrSide u⟩
  continuous_toFun :=
    ((continuous_retractedTime n).prodMk (continuous_retractedSimplex n)).subtype_mk _

theorem SecondHurewicz.SimplyConnected.cylinderRetraction_val_of_mem {n : ℕ}
    {u : unitInterval × SingularChains.Simplex n} (hu : u ∈ bottomOrSide n) :
    (cylinderRetraction n u).val = u :=
  Prod.ext (retractedTime_eq_of_mem hu) (retractedSimplex_eq_of_mem hu)

@[simp]
theorem SecondHurewicz.SimplyConnected.cylinderRetraction_fix {n : ℕ} (u : ↥(bottomOrSide n)) :
    cylinderRetraction n u.val = u :=
  Subtype.ext (cylinderRetraction_val_of_mem u.property)

@[simp]
theorem SecondHurewicz.SimplyConnected.cylinderRetraction_bottom (n : ℕ)
    (s : SingularChains.Simplex n) : cylinderRetraction n (0, s) = bottomInclusion n s :=
  cylinderRetraction_fix (bottomInclusion n s)

@[simp]
theorem SecondHurewicz.SimplyConnected.cylinderRetraction_side (n : ℕ) (t : unitInterval)
    (s : SimplexBoundary n) : cylinderRetraction n (t, s.val) = sideInclusion n (t, s) :=
  cylinderRetraction_fix (sideInclusion n (t, s))

private def SecondHurewicz.SimplyConnected.gluedBoundaryFunction_mo1973_6129 {n : ℕ} {X : Type*}
    [TopologicalSpace X] (f : C(SingularChains.Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X)) (u : ↥(bottomOrSide n)) : X :=
  if hu : u.val.1 = 0 then f u.val.2 else h (u.val.1, ⟨u.val.2, u.property.resolve_left hu⟩)

private theorem SecondHurewicz.SimplyConnected.gluedBoundaryFunction_bottom_mo1973_6130 {n : ℕ}
    {X : Type*} [TopologicalSpace X] (f : C(SingularChains.Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X)) (u : ↥(bottomOrSide n)) (hu : u.val.1 = 0) :
    gluedBoundaryFunction_mo1973_6129 f h u = f u.val.2 := by classical exact dif_pos hu

private theorem SecondHurewicz.SimplyConnected.gluedBoundaryFunction_side_mo1973_6131 {n : ℕ}
    {X : Type*} [TopologicalSpace X] (f : C(SingularChains.Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X)) (h0 : ∀ s, h (0, s) = f s.val)
    (u : ↥(bottomOrSide n)) (hu : u.val.2 ∈ simplexBoundary n) :
    gluedBoundaryFunction_mo1973_6129 f h u = h (u.val.1, ⟨u.val.2, hu⟩) := by
  classical
  by_cases ht : u.val.1 = 0
  · rw [gluedBoundaryFunction_bottom_mo1973_6130 f h u ht]
    simpa only [ht] using (h0 ⟨u.val.2, hu⟩).symm
  · exact dif_neg ht

private theorem SecondHurewicz.SimplyConnected.continuous_gluedBoundaryFunction_mo1973_6132
    {n : ℕ} {X : Type*} [TopologicalSpace X] (f : C(SingularChains.Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X)) (h0 : ∀ s, h (0, s) = f s.val) :
    Continuous (gluedBoundaryFunction_mo1973_6129 f h) := by
  let B : Set (↥(bottomOrSide n)) := {u | u.val.1 = 0}
  let S : Set (↥(bottomOrSide n)) := {u | u.val.2 ∈ simplexBoundary n}
  have hB : IsClosed B :=
    isClosed_eq (continuous_fst.comp continuous_subtype_val) continuous_const
  have hS : IsClosed S :=
    (isClosed_simplexBoundary n).preimage (continuous_snd.comp continuous_subtype_val)
  have hcover : B ∪ S = Set.univ := by
    apply Set.eq_univ_of_forall
    intro u
    exact u.property
  have hbottom : ContinuousOn (gluedBoundaryFunction_mo1973_6129 f h) B :=
    (f.continuous.comp (continuous_snd.comp continuous_subtype_val)).continuousOn.congr
      (fun u hu => gluedBoundaryFunction_bottom_mo1973_6130 f h u hu)
  have hside : ContinuousOn (gluedBoundaryFunction_mo1973_6129 f h) S := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hc : Continuous (fun u : S => h (u.val.val.1, ⟨u.val.val.2, u.property⟩)) :=
      h.continuous.comp
        ((continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).prodMk
          ((continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk
            _))
    exact hc.congr fun u => (gluedBoundaryFunction_side_mo1973_6131 f h h0 u.val u.property).symm
  apply continuousOn_univ.mp
  rw [← hcover]
  exact hbottom.union_of_isClosed hside hB hS

def SecondHurewicz.SimplyConnected.gluedBoundaryMap {n : ℕ} {X : Type*} [TopologicalSpace X]
    (f : C(SingularChains.Simplex n, X)) (h : C(unitInterval × SimplexBoundary n, X))
    (h0 : ∀ s, h (0, s) = f s.val) : C(↥(bottomOrSide n), X)
    where
  toFun := gluedBoundaryFunction_mo1973_6129 f h
  continuous_toFun := continuous_gluedBoundaryFunction_mo1973_6132 f h h0

@[simp]
theorem SecondHurewicz.SimplyConnected.gluedBoundaryMap_bottomInclusion {n : ℕ} {X : Type*}
    [TopologicalSpace X] (f : C(SingularChains.Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X)) (h0 : ∀ s, h (0, s) = f s.val)
    (s : SingularChains.Simplex n) : gluedBoundaryMap f h h0 (bottomInclusion n s) = f s :=
  gluedBoundaryFunction_bottom_mo1973_6130 f h (bottomInclusion n s) rfl

@[simp]
theorem SecondHurewicz.SimplyConnected.gluedBoundaryMap_sideInclusion {n : ℕ} {X : Type*}
    [TopologicalSpace X] (f : C(SingularChains.Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X)) (h0 : ∀ s, h (0, s) = f s.val)
    (u : unitInterval × SimplexBoundary n) : gluedBoundaryMap f h h0 (sideInclusion n u) = h u :=
  gluedBoundaryFunction_side_mo1973_6131 f h h0 (sideInclusion n u) u.2.property

def SecondHurewicz.SimplyConnected.extendBoundaryHomotopy {n : ℕ} {X : Type*} [TopologicalSpace X]
    (f : C(SingularChains.Simplex n, X)) (h : C(unitInterval × SimplexBoundary n, X))
    (h0 : ∀ s, h (0, s) = f s.val) : C(unitInterval × SingularChains.Simplex n, X) :=
  (gluedBoundaryMap f h h0).comp (cylinderRetraction n)

@[simp]
theorem SecondHurewicz.SimplyConnected.extendBoundaryHomotopy_bottom {n : ℕ} {X : Type*}
    [TopologicalSpace X] (f : C(SingularChains.Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X)) (h0 : ∀ s, h (0, s) = f s.val)
    (s : SingularChains.Simplex n) : extendBoundaryHomotopy f h h0 (0, s) = f s := by
  change gluedBoundaryMap f h h0 (cylinderRetraction n (0, s)) = f s
  rw [cylinderRetraction_bottom, gluedBoundaryMap_bottomInclusion]

@[simp]
theorem SecondHurewicz.SimplyConnected.extendBoundaryHomotopy_side {n : ℕ} {X : Type*}
    [TopologicalSpace X] (f : C(SingularChains.Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X)) (h0 : ∀ s, h (0, s) = f s.val) (t : unitInterval)
    (s : SimplexBoundary n) : extendBoundaryHomotopy f h h0 (t, s.val) = h (t, s) := by
  change gluedBoundaryMap f h h0 (cylinderRetraction n (t, s.val)) = h (t, s)
  rw [cylinderRetraction_side, gluedBoundaryMap_sideInclusion]

theorem SecondHurewicz.SimplyConnected.extendBoundaryHomotopy_boundary {n : ℕ} {X : Type*}
    [TopologicalSpace X] (f : C(SingularChains.Simplex n, X))
    (h : C(unitInterval × SimplexBoundary n, X)) (h0 : ∀ s, h (0, s) = f s.val) (t : unitInterval)
    (s : SingularChains.Simplex n) (hs : s ∈ simplexBoundary n) :
    extendBoundaryHomotopy f h h0 (t, s) = h (t, ⟨s, hs⟩) :=
  extendBoundaryHomotopy_side f h h0 t ⟨s, hs⟩

theorem SecondHurewicz.SimplyConnected.extendBoundaryHomotopy_face {n : ℕ} {X : Type*}
    [TopologicalSpace X] (f : C(SingularChains.Simplex (n + 1), X))
    (h : C(unitInterval × SimplexBoundary (n + 1), X)) (h0 : ∀ s, h (0, s) = f s.val)
    (t : unitInterval) (i : Fin (n + 2)) (s : SingularChains.Simplex n) :
    extendBoundaryHomotopy f h h0 (t, SingularChains.simplexFace n i s) =
      h (t, ⟨SingularChains.simplexFace n i s, simplexFace_mem_boundary n i s⟩) :=
  extendBoundaryHomotopy_boundary f h h0 t _ (simplexFace_mem_boundary n i s)

end Mathoverflow1973
