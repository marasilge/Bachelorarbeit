/-
Copyright (c) 2026 Mara Silge. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mara Silge
-/

import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Constructions.SumProd
import Formalisation.HEP_ball_cube

open Metric
open Set.Notation
open Topology
open RelCWComplex

noncomputable section

/- The notation follows the convention fixed in `HEP_definition`: `Y` is the ambient type,
`X : Set Y` the relative CW-complex and `C : Set Y` its base. The dimensions `m` and `n` are
bound in each declaration separately. -/

universe u

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] (X : Set Y) {C : Set Y} [RelCWComplex X C]

/- `SkeletonProjection (m : ℕ)` is a map from the `ungluedSkel` to the (m-1)-skeleton of a
  relative CW complex. After the construction of the map, we proved that it is a quotient map,
  namely its surjectivity, continuity and that a set is closed, if its preimage is closed.
-/
abbrev ungluedSkel (m : ℕ) :=
  C ⊕ (Σ (n : Fin m) (_ : cell X n), (closedBall (0 : Fin n → ℝ) 1))

def SkeletonProjection (m : ℕ) :
  ungluedSkel X m → skeletonLT X m :=
  Sum.elim
  (fun c ↦ ⟨c, by
    apply skeletonLT_mono (by positivity)
    rw[Topology.RelCWComplex.skeletonLT_zero_eq_base]
    exact c.prop ⟩)
  (fun ⟨n, i, x⟩ => ⟨map n i x, by
    have : (n + 1 : ℕ∞) ≤ (m : ℕ∞) := by exact_mod_cast Nat.succ_le_of_lt n.isLt
    apply skeletonLT_mono this
    apply closedCell_subset_skeletonLT n i
    exact Set.mem_image_of_mem ↑(map (↑n) i) x.prop⟩)

lemma SkeletonProjection_Surjective (m : ℕ) : (SkeletonProjection X m).Surjective := by
  intro ⟨y, yprop⟩
  rw [mem_skeletonLT_iff] at yprop
  rcases yprop with hyBasis | hyCell
  · refine Sum.exists.mpr ?_
    left
    use ⟨y, hyBasis⟩
    simp [SkeletonProjection]
  · obtain ⟨n, hn1, ⟨i, hi⟩⟩ := hyCell
    rw [show (↑y ∈ openCell n i) = ∃ a ∈ ball 0 1, (map n i) a = ↑y from rfl] at hi
    obtain ⟨x, hx1, hx2⟩ := hi
    apply ball_subset_closedBall at hx1
    refine Sum.exists.mpr ?_
    right
    use ⟨Fin.mk n (ENat.coe_lt_coe.mp hn1), i, (⟨x, hx1⟩ : closedBall (0 : Fin n → ℝ) 1)⟩
    exact SetLike.coe_eq_coe.mp hx2

lemma SkeletonProjection_Continuous (m : ℕ) : Continuous (SkeletonProjection X m) := by
  refine continuous_sum_dom.mpr ⟨?_, ?_ ⟩
  · simp only [SkeletonProjection, Sum.elim_comp_inl]
    fun_prop
  · simp only [SkeletonProjection, Sum.elim_comp_inr, continuous_sigma_iff]
    intro n j
    rw [continuous_induced_rng]
    apply ContinuousOn.restrict (continuousOn n j)

-- to shorten
lemma memBase_memSkeletonLT {y : Y} (hC : y ∈ C) (m : ℕ) :
  y ∈ skeletonLT X m := mem_skeletonLT_iff.mpr (Or.inl hC)

lemma hClosedBase (m : ℕ) {S : Set (skeletonLT X m)}
    (hBase : IsClosed (Sum.inl ⁻¹' SkeletonProjection X m ⁻¹' S))
    (S' : Set Y) (hS'def : S' = Subtype.val '' S) : IsClosed (S' ∩ C) := by
  suffices hrw : (Sum.inl ⁻¹' (SkeletonProjection X m⁻¹' S)) = S' ∩ C by
    rw [← hrw]
    exact hBase.trans (isClosedBase X)
  ext s
  simp only [SkeletonProjection, Set.mem_image, Set.mem_preimage, Sum.elim_inl,
    Subtype.exists, exists_and_right, exists_eq_right, Set.mem_inter_iff, hS'def]
  constructor
  · intro ⟨hs_memC, _ ⟩
    refine ⟨?_ , hs_memC⟩
    use memBase_memSkeletonLT X hs_memC m
  · intro ⟨⟨_ , _ ⟩, hs_memC⟩
    use hs_memC

lemma hClosedLT (m : ℕ) {S : Set (skeletonLT X m)}
    (hBall : ∀ (k : Fin m) (j : cell X k),
      IsClosed ((fun x => SkeletonProjection X m (Sum.inr ⟨k, j, x⟩)) ⁻¹' S))
    (S' : Set Y) (hS'def : S' = Subtype.val '' S) :
    ∀ (k : ℕ), k < m → ∀ (j : cell X k), IsClosed (S' ∩ closedCell k j) := by
  subst hS'def
  intro k hk j
  set g : (closedBall (0 : Fin k → ℝ) 1) → Y := fun p => map k j p.1 with hg_def
  have hrange : Set.range g = closedCell k j := by
    rw [show closedCell k j = map k j '' closedBall 0 1 by rfl, hg_def,
      show (fun p : ↥(closedBall (0 : Fin k → ℝ) 1) => map k j (p : Fin k → ℝ))
      = map k j ∘ (Subtype.val) by rfl, Set.range_comp, Subtype.range_coe]
  rw [← hrange, ← Set.image_preimage_eq_inter_range]
  apply (continuousOn k j).restrict.isClosedMap
  convert hBall ⟨k, hk⟩ j
  ext x
  constructor
  · intro hx
    apply Set.mem_image_of_mem g at hx
    rw [Set.image_preimage_eq_inter_range, hrange] at hx
    simp only [SkeletonProjection, Sum.elim_inr, Set.mem_preimage]
    exact (Subtype.val_injective.mem_set_image).1 (Set.mem_of_mem_inter_left hx)
  · intro hx
    apply Set.mem_preimage.1 at hx
    exact (Subtype.val_injective.mem_set_image).2 hx

lemma SkeletonProjectionIsQuotientMap (m : ℕ) :
    IsQuotientMap (SkeletonProjection X m) := by
  refine (isQuotientMap_iff (SkeletonProjection X m)).mpr  ⟨?_ , SkeletonProjection_Surjective X m⟩
  refine IsCoinducing.of_isClosed_preimage_iff_isClosed ?_
  intro S
  constructor
  · intro hS
    simp only [isClosed_sum_iff, isClosed_sigma_iff] at hS
    obtain ⟨hBase, hBall⟩ := hS
    set S' : Set Y := Subtype.val '' S with hS'def
    have hS'sub : S' ⊆ (skeletonLT X m):= by
      rintro _ ⟨a, _ , rfl⟩;
      exact a.2
    rw[(S.preimage_image_eq Subtype.val_injective).symm]
    apply IsClosed.preimage_val ?_
    refine isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell hS'sub
      (hClosedBase X m hBase S' hS'def) ?_
    intro n hn j
    by_cases h : n < m
    · exact Or.inr (hClosedLT X m hBall S' hS'def n h _ )
    · rw [Nat.not_lt] at h
      exact Or.inl (Set.disjoint_of_subset_left hS'sub
        (disjoint_skeletonLT_openCell (ENat.coe_le_coe.mpr h)))
  · exact fun hS => hS.preimage (SkeletonProjection_Continuous X m)

lemma SkeletonProj_const_C (m : ℕ) (n : ℕ) (c : C) :
    (SkeletonProjection X m (Sum.inl c)).1 = (SkeletonProjection X n (Sum.inl c)).1 := rfl
/-
`r_cube` are retractions obtained from the HEP for cubes relative boundary. They are used to define
the retraction on the skeleton. In a first step we define `SumMap` on the unglued Skeleton
-/
def r_cube (m : ℕ) : (closedBall (0 : Fin m → ℝ) 1) × ℝ → (closedBall (0 : Fin m → ℝ) 1) × ℝ :=
  Exists.choose ((retraction_criterion_closed isClosed_sphere).mp
  (HEP_cube_boundary m ))

lemma r_cube_RetractionOn (m : ℕ) : RetractionOn (r_cube m) (cyl _)
    (anchor (closedBall (0 : Fin m → ℝ) 1 ↓∩ sphere 0 1)) :=
  Exists.choose_spec ((retraction_criterion_closed isClosed_sphere).mp
  (HEP_cube_boundary m))

-- `cubesretract` is on top dimesnional cell `r_cube` and in all other dimensions the identity
def cubesretract {m : ℕ} (n : Fin (m + 1)) :
    (closedBall (0 : Fin (n : ℕ) → ℝ) 1) × unitInterval →
    (closedBall (0 : Fin (n : ℕ) → ℝ) 1) × ℝ := fun p ↦
  if n = m then (r_cube n (p.1, Subtype.val p.2))
  else (p.1, Subtype.val p.2)

-- We prove usefull lemma about `cubestract`
lemma cubesretract_continuous {m : ℕ} (n : Fin (m + 1)) : Continuous (cubesretract n) := by
  unfold cubesretract
  by_cases hnm : n =  m
  · simp only [hnm]
    exact (r_cube_RetractionOn n).continuousOn.comp_continuous (by fun_prop) (fun x ↦ x.2.2)
  · simp only [hnm, continuous_prodMk]
    refine ⟨by fun_prop, by fun_prop⟩

lemma cubesretract_fixedOn {m : ℕ} {n : Fin (m + 1)}
    (x : (closedBall (0 : Fin n → ℝ) 1) × unitInterval) :
    (n < m → cubesretract n x = (x.1, x.2.1)) ∧
    (n = m → x ∈ {z | z.2 = 0 ∨ z.1 ∈ (sphere ⟨0, by simp⟩ 1 : Set (closedBall (0 : Fin n → ℝ) 1)) }
      → cubesretract n x = (x.1, x.2.1)) := by
  by_cases h : n = m
  · simp only [h, lt_self_iff_false, IsEmpty.forall_iff, mem_sphere, Set.mem_setOf_eq,
    forall_const, true_and]
    intro hx
    have := (r_cube_RetractionOn n).fixesOn (x.1, x.2) (by
      obtain hx1 | hx2 :=  hx
      · exact Or.inl (Set.Icc.coe_eq_zero.mpr hx1)
      · exact Or.inr ⟨mem_sphere.mpr hx2, unitInterval.mem_unitIntervalSubmonoid.mp x.2.prop⟩)
    simp [cubesretract, this]
  · simp[cubesretract, h]

/-
The following `MapsTo` results will be used later one, here we derive the weaker version
  `cubesretract_mapsto_weak` from it, that proofs that the image of `SumMap`
  lies in the required codomain.
-/
lemma cubesretract_mapsto_lt {m : ℕ} (n : Fin (m + 1)) (i : cell X n)
    (p : (closedBall 0 1) × ↑unitInterval) (hn : n < m) :
    (map n i) (cubesretract n p).1 ∈ skeletonLT X m
    ∧ (cubesretract n p).2 ∈ unitInterval
    := by
  simp only [cubesretract, Nat.ne_of_lt hn, ↓reduceIte, Subtype.coe_prop, and_true]
  apply Topology.CWComplex.skeletonLT_mono (m := n + 1) ?_ ?_
  · rw [ENat.add_one_le_iff (ENat.coe_ne_top ↑n)]
    exact ENat.coe_lt_coe.mpr hn
  · apply closedCell_subset_skeletonLT n i
    apply Set.mem_image_of_mem
    exact Subtype.coe_prop p.1

lemma cubesretract_mapsto_top {m : ℕ} (n : Fin (m + 1)) (i : cell X n)
    (p : (closedBall 0 1) × ↑unitInterval) (hn : n = m) :
    (cubesretract n p).2 = 0 ∨ (map n i) (cubesretract n p).1 ∈ skeletonLT X m ∧
    (cubesretract n p).2 ∈ unitInterval := by
  have mapsto := by
    have : (p.1, (p.2 : ℝ)) ∈ cyl _ := Set.mem_setOf.mpr p.2.2
    exact (r_cube_RetractionOn n).mapsTo this
  simp only [cubesretract, hn, ↓reduceIte]
  rcases mapsto with h0 | h1
  · simp [h0]
  · refine Or.inr ⟨?_, h1.2⟩
    apply Set.Subset.trans (cellFrontier_subset_skeletonLT n i)
      (skeletonLT_mono (Std.le_of_eq (congrArg Nat.cast hn)))
    apply Set.mem_image_of_mem
    exact h1.1

lemma FinNeq_lt {n : ℕ} (m : Fin (n + 1)) (hnm : m ≠ n) : m < n := Nat.lt_of_le_of_ne m.is_le hnm

lemma cubesretract_mapsto_weak {m : ℕ} (n : Fin (m + 1)) (i : cell X n)
    (p : (closedBall 0 1) × ↑unitInterval) :
    (map n i) (cubesretract n p).1 ∈ skeletonLT X (m + 1) := by
  by_cases hn : n = m
  · obtain h0 | h1 := cubesretract_mapsto_top X n i p hn
    · apply Set.mem_of_mem_of_subset (s := skeletonLT X (n + 1)) ?_ (skeletonLT_mono (by rw[hn]))
      apply closedCell_subset_skeletonLT n i
      exact Set.mem_image_of_mem _ (Subtype.coe_prop (cubesretract n p).1)
    · exact skeletonLT_mono le_self_add h1.1
  · exact skeletonLT_mono le_self_add
      (cubesretract_mapsto_lt X n i p (FinNeq_lt n hn)).1

def sumMap (m : ℕ) :
    (ungluedSkel X (m + 1)) × unitInterval → skeletonLT X (m+1) × ℝ := fun p ↦
    p.1.elim
      (fun c => (⟨c.val, memBase_memSkeletonLT X c.prop (m + 1)⟩, p.2))
      (fun ⟨n, i, x⟩ => (⟨map n i (cubesretract n (x,p.2)).1,
        cubesretract_mapsto_weak X n i (x,p.2)⟩, (cubesretract n (x,p.2)).2))

/- On the base space C, on balls, which are not in the top dimension, as well as in the sphere
of top dimensional balls, `sumMap` is "the same" as applying the `SkeletonProjection` to the
first coordinate -/

lemma sumMap_eq_SkelProj_C (m : ℕ)
    (x : C) (t : unitInterval) : sumMap X m (Sum.inl x, t) =
    Prod.map id (Subtype.val) (SkeletonProjection X (m + 1) (Sum.inl x), t) := by
  simp [sumMap, SkeletonProjection]
  rfl

lemma sumMap_eq_SkelProj_LtOrSphere {m : ℕ}
    (n : Fin (m + 1)) (i : cell X n) (x' : closedBall (0 : Fin n → ℝ) 1) (t : unitInterval)
    (hx : n < m ∨ n = m ∧ x' ∈ sphere ⟨0, by simp⟩ 1) :
    sumMap X m (Sum.inr ⟨n, ⟨i, x'⟩⟩, t) =
    Prod.map (SkeletonProjection X (m + 1)) Subtype.val (Sum.inr ⟨n, ⟨i, x'⟩⟩, t) := by
  obtain hx_lt | ⟨hx_eq, hx_sphere⟩ := hx
  · simp [sumMap,  cubesretract, SkeletonProjection, (Nat.ne_of_lt hx_lt), Sum.elim_inr]
    rfl
  · have := (cubesretract_fixedOn (x', t)).2 hx_eq (Or.inr hx_sphere)
    simp [sumMap, this, SkeletonProjection]
    rfl
/-
-- eventuell unnötig, weil kaum erkennisse -- möchte man vielleicht sinnvoller abändern
lemma sumMap_top_open_apply (m : ℕ)
    (n : Fin (m + 1)) (i : cell X n) (x' : closedBall (0 : Fin n → ℝ) 1) (t : unitInterval)
   -- (hnm : n = m) (hx : x' ∉ sphere ⟨0, by simp⟩ 1)
    :
    sumMap m ((Sum.inr ⟨n, ⟨i, x'⟩⟩, t)) = (⟨map n i (cubesretract n (x',t)).1,
    cubesretract_mapsto n i (x',t)⟩, (cubesretract n (x',t)).2) := by simp[sumMap, cubeMap]
-/

 -- to shorten

-- lemma xx {m : ℕ} (n : Fin (m + 1)) (hnm : n = m) (i : cell X n)
--   (x' : ↑(closedBall 0 1)) (hx' : x' ∉ sphere ⟨0, by simp⟩ 1)
--   (n_y : Fin (m + 1)) (j_y : cell X ↑n_y) (y' : ↑(closedBall 0 1) ) :
--   Sum.inr (⟨n_y, ⟨j_y, y'⟩⟩: (n : ℕ) × cell X n × (closedBall ⟨0 , by simp⟩ 1))
--   = Sum.inr ⟨n, ⟨i, x'⟩⟩ := sorry

-- Points from the open m-dimensional ball are not maped to the (m-1) skeleton:
lemma topopen_notLT {n : ℕ} (i : cell X n)
    (x' : closedBall (0 : Fin n → ℝ) 1) (hx : x'.1 ∈ ball (0 : Fin n → ℝ) 1) (m : Fin (n + 1)) :
    (map n i ↑x') ∉ skeletonLT X m := by
  have h : (map n i ↑x') ∉ skeletonLT X n :=
    (disjoint_skeletonLT_openCell (by rfl)).notMem_of_mem_right (Set.mem_image_of_mem _ hx)
  have le : (m : ℕ∞) ≤ n := ENat.coe_le_coe.mpr (Order.lt_add_one_iff.1 m.isLt )
  exact fun mem ↦ h ((skeletonLT_mono le) mem)

omit [T2Space Y] in
lemma same_point {m : ℕ} (n_y : Fin (m + 1)) (j_y : cell X ↑n_y) (y' : (closedBall 0 1))
    (i : cell X ↑n_y) (x' : (closedBall 0 1)) (x_ball : x'.1 ∈ ball (0 : Fin n_y → ℝ) 1)
    (y_ball : y' ∈ ball (⟨0, by simp⟩ : closedBall (0 : Fin n_y → ℝ) 1) 1)
    (map_eq : (map (n_y) j_y) ↑y' = (map n_y i) x') (same_cell : j_y = i) : y' = x' := by
  rw [same_cell] at map_eq
  apply (map n_y i).injOn at map_eq
  · exact SetCoe.ext map_eq
  · rw [source_eq]; exact y_ball
  · rw [source_eq]; exact x_ball

/- If a point `x` from a top dimensional open ball has the same image under `SkeletonProjection`
  as a point `y` from `ungluedSkel`, the `y = Sum.inr ⟨n, i, x⟩`  -/
lemma SkeletonProj_inj_top {m : ℕ} {n : Fin (m + 1)} (hnm : ↑n = m) (i : cell X n)
    (x : closedBall (0 : Fin n → ℝ) 1) (x_ball : x.1 ∈ ball (0 : Fin n → ℝ) 1)
    (y : ungluedSkel X (m + 1))
    (hskel : SkeletonProjection X (m + 1) (Sum.inr ⟨n, ⟨i, x⟩⟩) = SkeletonProjection X (m + 1) y) :
    y = Sum.inr ⟨n, i, x⟩ := by
  have x_notSkelTop : (SkeletonProjection X (m + 1) (Sum.inr ⟨n, ⟨i, x⟩⟩)).1 ∉ skeletonLT X m :=
    topopen_notLT X i x x_ball ⟨m, by simp [hnm]⟩
  obtain c | ⟨n_y, ⟨j_y, y'⟩⟩ := y
  · rw [hskel, SkeletonProj_const_C X (m + 1) 0 c] at x_notSkelTop
    exact (x_notSkelTop (memBase_memSkeletonLT X c.prop m)).elim
  · have map_eq : map n_y j_y y' = map n i x := by
      simp [SkeletonProjection] at hskel
      exact hskel.symm
    by_cases y_ball : y' ∈ ball ⟨0, by simp⟩ 1
    · have same_cell : (⟨n_y, j_y⟩ : (n : ℕ) × cell X n) = ⟨n, i⟩ := by
        refine eq_of_not_disjoint_openCell ?_
        rw [Set.not_disjoint_iff]
        use map n i x
        constructor
        · rw[← map_eq]
          apply Set.mem_image_of_mem; exact y_ball
        · exact Set.mem_image_of_mem _ x_ball
      rw [Sum.inr.inj_iff]
      rw [Sigma.mk.inj_iff, Fin.val_inj] at same_cell
      have hn : n_y = n := same_cell.1
      subst hn
      simp only [heq_eq_eq, true_and, Sigma.mk.injEq] at same_cell ⊢
      exact ⟨same_cell , same_point X n_y j_y y' i x x_ball y_ball map_eq same_cell ⟩
    · apply (x_notSkelTop ?_).elim
      apply skeletonLT_mono (ENat.coe_le_coe.mpr n_y.is_le)
      apply Set.mem_of_subset_of_mem (cellFrontier_subset_skeletonLT n_y j_y)
      simp only [SkeletonProjection, Sum.elim_inr, map_eq.symm]
      apply Set.mem_image_of_mem
      rw [← Metric.closedBall_sdiff_ball]
      exact ⟨y'.prop, y_ball⟩

lemma TopOpen {m : ℕ} (n_y : Fin (m + 1)) (y' : closedBall 0 1)
    (h : ¬(n_y < m ∨ n_y = m ∧ y' ∈ sphere (⟨0, by simp⟩ : closedBall (0 : Fin n_y → ℝ) 1) 1)) :
    n_y = m ∧ y' ∈ ball ⟨0, by simp⟩ 1 := by
  simp only [not_or, not_lt, not_and] at h
  have ny_eq_m : ↑n_y = m := Nat.le_antisymm_iff.2 ⟨Fin.is_le n_y, h.1⟩
  refine ⟨ny_eq_m , ?_ ⟩
  rw [← Metric.closedBall_sdiff_sphere]
  exact ⟨y'.prop, h.2 ny_eq_m⟩

-- `sumMap` factors through applying `SkeletonProjection` on the first coordinate.
lemma factors (m : ℕ) : (sumMap X m).FactorsThrough
    (fun p ↦ ((SkeletonProjection X (m + 1) p.1), p.2)) := by
  intro x y hxy
  rw [Prod.mk_inj] at hxy
  obtain ⟨heq1, heq2⟩ := hxy
  obtain ⟨cx | ⟨n, i, x'⟩, tx⟩ := x
  · rw [sumMap_eq_SkelProj_C, heq1]
    obtain ⟨ c_y | ⟨n_y, i_y, y'⟩, t⟩ := y
    · rw [← sumMap_eq_SkelProj_C]
      congr
    · simp only at heq2
      suffices hyLtSphere : ↑n_y < m ∨ ↑n_y = m ∧ y' ∈ sphere ⟨0, by simp⟩ 1 by
        rw [sumMap_eq_SkelProj_LtOrSphere X n_y i_y y' t hyLtSphere, heq2, Prod.map_apply,
          Prod.map_apply, id_eq]
      by_contra hynotLTSphere
      have hytop_open : n_y = m ∧ y' ∈ ball ⟨0, by simp⟩ 1 := TopOpen n_y y' hynotLTSphere
      have : ↑(SkeletonProjection X (m + 1) (Sum.inl cx, tx).1) ∉ skeletonLT X ↑m := by
        rw[heq1]
        apply topopen_notLT X i_y y' hytop_open.2 ⟨m, by linarith⟩
      exact this (memBase_memSkeletonLT X cx.prop m)
  · by_cases hxLtSphere : n < m ∨ n = m ∧ x' ∈ sphere ⟨0, by simp⟩ 1
    · simp only at heq2
      rw [sumMap_eq_SkelProj_LtOrSphere X n i x' tx hxLtSphere, Prod.map_apply, heq1]
      obtain ⟨c | ⟨n_y, i_y, y'⟩, t⟩ := y
      · congr
      · suffices hynotTop : n_y < m ∨ ↑n_y = m ∧ y' ∈ sphere ⟨0, by simp⟩ 1 by
          rw [sumMap_eq_SkelProj_LtOrSphere X n_y i_y y' t hynotTop, heq2, Prod.map_apply]
        by_contra hynotLTSphere
        have top_open : n_y = m ∧ y' ∈ ball ⟨0, by simp⟩ 1 := TopOpen n_y y' hynotLTSphere
        have hTopInj := SkeletonProj_inj_top X top_open.1 i_y y' top_open.2
          (Sum.inr ⟨n,i,x'⟩) heq1.symm
        rw [Sum.inr.inj_iff, Sigma.mk.injEq] at hTopInj
        have : n = n_y := hTopInj.1
        subst this
        simp only [heq_eq_eq, Sigma.mk.injEq, true_and] at hTopInj
        have : x' = y' := hTopInj.2
        subst this
        exact hynotLTSphere hxLtSphere
    · congr
      simp only [not_or, not_lt, not_and] at hxLtSphere
      have n_eq_m : ↑n = m :=  Eq.symm (Nat.le_antisymm hxLtSphere.1 (Fin.is_le n))
      refine (SkeletonProj_inj_top X n_eq_m i x' ?_ y.1 heq1).symm
      rw [← closedBall_sdiff_sphere]
      exact ⟨x'.prop, hxLtSphere.2 n_eq_m⟩

def r (m : ℕ) : skeletonLT X (m + 1) × unitInterval → skeletonLT X (m + 1) × ℝ :=
  Function.extend (fun p ↦ ((SkeletonProjection X (m + 1) p.1), p.2)) (sumMap X m)
  (Prod.map id Subtype.val)


lemma r_apply_SumMap (m : ℕ) (p : skeletonLT X (m + 1) × unitInterval) :
    ∃ (s : (ungluedSkel X (m + 1)) × unitInterval),
    SkeletonProjection X (m+1) s.1 = p.1 ∧ s.2 = p.2 ∧
    r X m p = sumMap X m s := by
  set s := Function.surjInv (SkeletonProjection_Surjective X (m + 1)) p.1
  use (s, p.2)
  have inv : p = (SkeletonProjection X (m + 1) s, p.2) := Prod.fst_eq_iff.mp
    (Function.surjInv_eq (SkeletonProjection_Surjective X (m + 1)) p.1).symm
  refine ⟨?_ , by rfl, ?_ ⟩
  · rw [Prod.ext_iff] at inv
    exact inv.1.symm
  · rw[inv]
    exact (factors X m).extend_apply (Prod.map id Subtype.val) (s, p.2)

-- the next two defintions and two simp-lemma are written by claude (Opus 5)
-- (I made smal changes)
def Homeomorph.sigmaCongrRight' {ι : Type*} {σ τ : ι → Type*} [∀ i, TopologicalSpace (σ i)]
  [∀ i, TopologicalSpace (τ i)] (F : ∀ i, σ i ≃ₜ τ i) : (Σ i, σ i) ≃ₜ Σ i, τ i where
  toEquiv := Equiv.sigmaCongrRight (fun i ↦ F i)
  continuous_toFun := by
    rw [continuous_sigma_iff]
    exact fun i ↦ continuous_sigmaMk.comp (F i).continuous
  continuous_invFun := by
    rw [continuous_sigma_iff]
    exact fun i ↦ continuous_sigmaMk.comp (F i).symm.continuous

def homeoProd (m : ℕ) :
  (C × unitInterval) ⊕ (Σ (n : Fin (m + 1)) (_ : cell X n),
    (closedBall (0 : Fin n → ℝ) 1) × unitInterval) ≃ₜ
    (C ⊕ (Σ (n : Fin (m + 1)) (_ : cell X n), closedBall (0 : Fin n → ℝ) 1)) × unitInterval :=
  ( Homeomorph.sumProdDistrib.trans
    ((Homeomorph.refl _ ).sumCongr (Homeomorph.sigmaProdDistrib.trans
    (Homeomorph.sigmaCongrRight' fun _ ↦ Homeomorph.sigmaProdDistrib)))).symm

omit [T2Space Y] in
@[simp] lemma homeoProd_inl (m : ℕ) (c : C) (t : unitInterval) :
    (homeoProd (X := X) m) (Sum.inl (c, t)) = (Sum.inl c, t) := rfl

omit [T2Space Y] in
@[simp] lemma homeoProd_inr (m : ℕ) (n : Fin (m + 1)) (i : cell X n)
    (x : closedBall (0 : Fin n → ℝ) 1) (t : unitInterval) :
    (homeoProd (X := X) m) (Sum.inr ⟨n, i, (x, t)⟩) = (Sum.inr ⟨n, i, x⟩, t) := rfl

-- Here my own code continues:

lemma cts_sumMap_prehomeo (m : ℕ) : Continuous ((sumMap X m) ∘ (homeoProd (X := X) m))  := by
  have : (Sum.elim
    (fun (q : C × unitInterval) ↦ sumMap X m ((Sum.inl q.1), q.2))
    (fun (q : Σ (n : Fin (m + 1)) (_ : cell X n), (closedBall (0 : Fin n → ℝ) 1 × unitInterval)) ↦
    sumMap X m ((Sum.inr ⟨q.1 , ⟨q.2.1, q.2.2.1⟩⟩), q.2.2.2)))
    = (sumMap X m) ∘ (homeoProd X m) := by
    ext x <;>
    · obtain ⟨_ ,_ ⟩ | ⟨_ ,_ ,_ ,_ ⟩ := x
      · simp only [Sum.elim_inl, Function.comp_apply, homeoProd_inl]
      · simp only [Sum.elim_inr, Function.comp_apply, homeoProd_inr]
  rw[← this]
  apply Continuous.sumElim ?_ ?_
  · simp only [sumMap,  Sum.elim_inl, continuous_prodMk]
    refine ⟨by fun_prop , by fun_prop⟩
  · simp only [sumMap, Sum.elim_inr, Prod.mk.eta, continuous_sigma_iff]
    intro n i
    simp only [continuous_prodMk]
    constructor
    · refine Continuous.subtype_mk ?_ (cubesretract_mapsto_weak X n i)
      apply (continuousOn n i).comp_continuous ?_ ?_
      · apply continuous_subtype_val.comp
        exact continuous_fst.comp (cubesretract_continuous n)
      · intro x
        exact Subtype.coe_prop (cubesretract n x).1
    · exact continuous_snd.comp (cubesretract_continuous n)

lemma continuousRetract (m : ℕ) : Continuous (r (X := X) m) := by
  refine (SkeletonProjectionIsQuotientMap X (m +1)).continuous_lift_prod_left ?_
  have cts_sumMap : Continuous (sumMap (X := X) m) :=
    (homeoProd X m).comp_continuous_iff'.1 (cts_sumMap_prehomeo X m)
  apply cts_sumMap.congr ?_
  intro x
  rw [← (factors X m).extend_apply (Prod.map id Subtype.val) x]
  rfl

/-
r ist now almost the retraction, we need for the retraction criterion. Only we have to extend the
second coordinate onto all of ℝ and then proof, it satisfies all conditions of a retraction:
-/

def retr_skeleton (m : ℕ) : (skeletonLT X (m + 1)) × ℝ → (skeletonLT X (m + 1)) × ℝ := fun p ↦
  (r X m) (p.1, ⟨ProjIcc p.2, proj_mem p.2 ⟩)

lemma sumMap_mapsTo (m : ℕ) (x : (ungluedSkel X (m + 1)) × ↑unitInterval) :
    (sumMap X m x).2 = 0 ∨
    ↑(sumMap X m x).1 ∈ skeletonLT X ↑m ∧ ↑(sumMap X m x).2 ∈ unitInterval := by
  obtain ⟨c |⟨n, i, x'⟩, t⟩ := x
  · simp only [sumMap, Sum.elim_inl, Subtype.coe_prop, and_true]
    exact Or.inr (mem_skeletonLT_iff.mpr (Or.inl c.prop))
  · simp only [sumMap, Sum.elim_inr]
    by_cases hn : n = m
    · exact cubesretract_mapsto_top X n i (x',t) hn
    · exact Or.inr (cubesretract_mapsto_lt X n i (x',t) (FinNeq_lt n hn))

lemma sumMap_fixedOn (m : ℕ) {s : ↑(skeletonLT X (↑m + 1)).carrier × ℝ} (hs : s ∈ anchor
  ((skeletonLT X (↑m + 1)).carrier ↓∩ ↑(skeletonLT X ↑m))) (hs2 : s.2 ∈ unitInterval)
  (t : unitInterval) (n : Fin (m + 1)) (i : cell X ↑n) (x' : closedBall 0 1)
  (hxproj1 : SkeletonProjection X (m + 1) (Sum.inr ⟨n, ⟨i, x'⟩⟩, t).1 = s.1)
  (hxproj2 : t = ⟨s.2, hs2⟩) : sumMap X m (Sum.inr ⟨n, ⟨i, x'⟩⟩, t) = s := by
  simp only [sumMap, Sum.elim_inr]
  have cubesFixed : cubesretract n (x', t) = ((x', t).1, ↑(x', t).2) := by
    by_cases h : n = Fin.last m
    · subst h
      apply (cubesretract_fixedOn (x', t)).2 (Fin.val_last m)
      rcases hs with hs0 | hs1
      · apply Or.inl
        rw [hxproj2]
        exact Eq.symm (SetCoe.ext hs0.symm)
      · simp only [Set.mem_preimage, SetLike.mem_coe, ← hxproj1, Fin.val_last] at hs1
        apply Or.inr
        by_contra notSphere
        have := topopen_notLT X i x' (by rw [← closedBall_sdiff_sphere]; exact ⟨x'.prop, notSphere⟩)
          (Fin.last m)
        exact this hs1.1
    · exact (cubesretract_fixedOn (x', t)).1 (Fin.val_lt_last h)
  simp only [cubesFixed]
  refine Prod.ext_iff.mpr ⟨ ?_, SetCoe.ext_iff.2 hxproj2 ⟩
  simp only [SkeletonProjection, Sum.elim_inr] at hxproj1
  exact hxproj1

lemma HEP'_skeleton (m : ℕ) : HEP' (skeletonLT X (m + 1)).carrier (skeletonLT X m).carrier := by
  apply (retraction_criterion_closed (skeletonLT X ↑m).closed'.preimage_val).2
  use retr_skeleton X m
  have ProjId (s : (skeletonLT X (↑m + 1)).carrier × ℝ) (hs : s.2 ∈ unitInterval ) :
      (⟨ProjIcc s.2, proj_mem s.2⟩ : unitInterval) = ⟨s.2, hs⟩ := by
    simp only [Subtype.mk.injEq]
    exact proj_id hs
  constructor
  · simp only [Set.mem_preimage, Set.mem_Icc, Set.setOf_subset_setOf, Prod.forall,
      forall_eq_or_imp, Std.le_refl, zero_le_one, and_self, and_imp, imp_self, implies_true]
  · apply (continuousRetract X m).comp_continuousOn ?_
    refine ContinuousOn.prodMk continuousOn_fst (by fun_prop [proj_cont])
  · intro s hs
    unfold retr_skeleton
    obtain ⟨x, hxproj1, _ , hxsum⟩ := r_apply_SumMap X m (s.1, ⟨s.2, hs⟩)
    simp only [ProjId s hs, Set.mem_preimage, Set.mem_setOf_eq, hxsum]
    exact sumMap_mapsTo X m x
  · intro s hs
    have hs2 : s.2 ∈ unitInterval := by -- shorten
      rcases hs with h0 | hI
      · rw[h0]
        exact unitInterval.zero_mem
      · exact hI.2
    obtain ⟨x, hxproj1, hxproj2, hxsum⟩ := r_apply_SumMap X m (s.1, ⟨s.2, hs2⟩)
    simp only [retr_skeleton, ProjId s hs2, hxsum]
    obtain ⟨c | ⟨n, i, x'⟩, t⟩ := x
    · simp only [SkeletonProjection, Sum.elim_inl] at hxproj1 hxproj2
      refine Prod.ext_iff.mpr ⟨ ?_, ?_ ⟩
      · simp only [sumMap, Sum.elim_inl]
        exact hxproj1
      · simp [sumMap, hxproj2]
    · exact sumMap_fixedOn X m hs hs2 t n i x' hxproj1 hxproj2
