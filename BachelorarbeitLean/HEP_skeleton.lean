import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Data.Set.Subset
import Mathlib.Topology.Defs.Filter
import Mathlib.Data.PEquiv
import BachelorarbeitLean.HEP_definition
import BachelorarbeitLean.HEP_ball_cube
import BachelorarbeitLean.HEP_cell

open Metric
open Set.Notation
open Topology
open RelCWComplex

noncomputable section

abbrev ungluedSkel {Y : Type*} [hY : TopologicalSpace Y] [T2Space Y] (X : Set Y) (C : Set Y)
    [RelCWComplex X C] (m : ℕ) :=
  C ⊕ (Σ (n : Fin m) (_ : cell X n), (closedBall (0 : Fin n → ℝ) 1))

def SkeletonProjection {Y : Type*} [TopologicalSpace Y] [T2Space Y] (X : Set Y) {C : Set Y}
  [RelCWComplex X C] (m : ℕ) : ungluedSkel X C m → skeletonLT X m :=
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

lemma SkeletonProjection_Surjective (m : ℕ) {Y : Type*} [hY : TopologicalSpace Y] [T2Space Y]
  (X : Set Y) {C : Set Y} [RelCWComplex X C] : Function.Surjective (SkeletonProjection X m) := by
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
    apply Metric.ball_subset_closedBall at hx1
    refine Sum.exists.mpr ?_
    right
    use ⟨@Fin.mk m n (ENat.coe_lt_coe.mp hn1) , i , (⟨x, hx1⟩ : closedBall (0 : Fin n → ℝ) 1)⟩
    unfold SkeletonProjection
    exact SetLike.coe_eq_coe.mp hx2

lemma SkeletonProjection_Continuous (m : ℕ) {Y : Type*} [hY : TopologicalSpace Y] [T2Space Y]
    (X : Set Y) {C : Set Y} [RelCWComplex X C] : Continuous (SkeletonProjection X m) := by
  refine continuous_sum_dom.mpr ?_
  refine ⟨?_, ?_ ⟩
  · simp only [SkeletonProjection, Sum.elim_comp_inl]
    fun_prop
  · simp only [SkeletonProjection, Sum.elim_comp_inr, continuous_sigma_iff]
    intro n j
    rw [continuous_induced_rng]
    apply ContinuousOn.restrict (continuousOn n j)


#check Function.Embedding.inl
#check Function.Embedding.sumSet
#check Function.Embedding.sumSet_preimage_inl

@[simp] -- to shorten
lemma memBase_memSkeletonLT {Y : Type*} [hY : TopologicalSpace Y] [T2Space Y]
    (X : Set Y) {C : Set Y} [RelCWComplex X C] {x : Y} (hC : x ∈ C) (m : ℕ) :
  x ∈ skeletonLT X m := by
  exact (mem_skeletonLT_iff (C := X) (n := m)).mpr (Or.inl hC)


lemma hClosedBase {Y : Type*} [hY : TopologicalSpace Y] [T2Space Y]
    (X : Set Y) {C : Set Y} [RelCWComplex X C] (m : ℕ) {S : Set (skeletonLT X m)}
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
  · intro ⟨⟨ _ , _⟩, hs_memC⟩
    use hs_memC

lemma hClosedLT {Y : Type*} [hY : TopologicalSpace Y] [T2Space Y]
    (X : Set Y) {C : Set Y} [RelCWComplex X C] (m : ℕ) {S : Set (skeletonLT X m)}
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
    apply (Subtype.val_injective.mem_set_image).2 hx

lemma SkeletonProjectionIsQuotientMap (m : ℕ) {Y : Type*} [hY : TopologicalSpace Y] [T2Space Y]
  (X : Set Y) {C : Set Y} [RelCWComplex X C] :
    IsQuotientMap (SkeletonProjection X m) := by
  refine (isQuotientMap_iff (SkeletonProjection X m)).mpr  ⟨?_ , SkeletonProjection_Surjective m X⟩
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
    refine isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell hS'sub
      (hClosedBase X m hBase S' hS'def) ?_
    intro n hn j
    by_cases h : n < m
    · exact Or.inr (hClosedLT X m hBall S' hS'def n h _ )
    · suffices hempty : S' ∩ openCell n j = ∅ by
        rw[hempty]
        exact Or.inl isClosed_empty
      rw [Nat.not_lt] at h
      apply Disjoint.inter_eq
      exact Set.disjoint_of_subset_left hS'sub
        (disjoint_skeletonLT_openCell (ENat.coe_le_coe.mpr h))
  · intro hS
    exact hS.preimage (SkeletonProjection_Continuous m X)

lemma SkeletonProj_const_C {Y : Type*} [TopologicalSpace Y] [T2Space Y] (X : Set Y)
    {C : Set Y} [RelCWComplex X C] (m : ℕ) (n : ℕ) (c : C) :
    (SkeletonProjection X m (Sum.inl c)).1 = (SkeletonProjection X n (Sum.inl c)).1 := rfl

open RelCWComplex
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] {X : Set Y} {C : Set Y} [RelCWComplex X C]

#check r_cube
#check r_cube_IsretractionOn
#check Set.iUnion
#check Topology.RelCWComplex.skeleton_mono
#check Topology.RelCWComplex.closedCell_subset_skeletonLT

def cubesretract {m : ℕ} (n : Fin (m + 1)) :
    (closedBall (0 : Fin (n : ℕ) → ℝ) 1) × unitInterval →
    (closedBall (0 : Fin (n : ℕ) → ℝ) 1) × ℝ := fun p ↦
  if n = m then (r_cube n (p.1, Subtype.val p.2))
  else (p.1, Subtype.val p.2)

lemma cubesretract_continuous {m : ℕ} (n : Fin (m + 1)) : Continuous (cubesretract n) := by
  unfold cubesretract
  by_cases hnm : n = m
  · simp only [hnm,]
    exact (r_cube_IsretractionOn n).continuousOn.comp_continuous (by fun_prop) (fun x ↦ x.2.2)
  · simp only [hnm, continuous_prodMk]
    refine ⟨by fun_prop, by fun_prop⟩

lemma cubesretract_fixedOn {m : ℕ} {n : Fin (m + 1)}
    (x : (closedBall (0 : Fin n → ℝ) 1) × unitInterval) :
    (n < m → cubesretract n x = (x.1, x.2.1)) ∧
    (n = m → x ∈ {z | z.2 = 0 ∨ z.1 ∈ sphere ⟨0, by simp⟩ 1 } → cubesretract n x = (x.1, x.2.1))
    := by
  by_cases h : n = m
  · simp only [h, lt_self_iff_false, IsEmpty.forall_iff, Set.mem_setOf_eq,
    forall_const, true_and]
    intro hx
    have := (r_cube_IsretractionOn n).fixesOn (x.1, x.2) (by
      obtain hx1 | hx2 :=  hx
      · exact Or.inl (Set.Icc.coe_eq_zero.mpr hx1)
      · exact Or.inr ⟨mem_sphere.mpr hx2, unitInterval.mem_unitIntervalSubmonoid.mp x.2.prop⟩)
    simp [cubesretract, this]
  · simp[cubesretract, h]

lemma cubesretract_mapsto_lt {m : ℕ} (n : Fin (m + 1)) (i : cell X n)
    (p : (closedBall 0 1) × ↑unitInterval) (hn : n < m) :
    (map n i) (cubesretract n p).1 ∈ skeletonLT X m
    ∧ (cubesretract n p).2 ∈ unitInterval
    := by
  unfold cubesretract
  simp only [Nat.ne_of_lt hn, ↓reduceIte]
  constructor
  · apply Topology.CWComplex.skeletonLT_mono (m := n + 1) ?_ ?_
    · rw [ENat.add_one_le_iff (ENat.coe_ne_top ↑n)]
      exact ENat.coe_lt_coe.mpr hn
    · apply closedCell_subset_skeletonLT n i
      apply Set.mem_image_of_mem
      exact Subtype.coe_prop p.1
  · exact p.2.2

lemma cubesretract_mapsto_top {m : ℕ} (n : Fin (m + 1)) (i : cell X n)
    (p : (closedBall 0 1) × ↑unitInterval) (hn : n = m) :
    (cubesretract n p).2 = 0 ∨ (map n i) (cubesretract n p).1 ∈ skeletonLT X m ∧
    (cubesretract n p).2 ∈ unitInterval := by
  have mapsto := by
    have : (p.1, (p.2 : ℝ)) ∈ (bigcyl _) := Set.mem_setOf.mpr p.2.2
    exact (r_cube_IsretractionOn n).mapsTo this
  simp only [cubesretract, hn, ↓reduceIte]
  rcases mapsto with h0 | h1
  · simp [h0]
  · refine Or.inr ⟨?_, h1.2⟩
    apply Set.Subset.trans (cellFrontier_subset_skeletonLT n i)
      (skeletonLT_mono (Std.le_of_eq (congrArg Nat.cast hn)))
    apply Set.mem_image_of_mem
    exact h1.1

lemma cubesretract_mapsto_weak {m : ℕ} (n : Fin (m + 1)) (i : cell X n)
    (p : (closedBall 0 1) × ↑unitInterval) :
    (map n i) (cubesretract n p).1 ∈ skeletonLT X (m + 1) := by
  by_cases hn : n = m
  · obtain h0 | h1 := cubesretract_mapsto_top n i p hn
    · apply Set.mem_of_mem_of_subset (s := skeletonLT X (n + 1)) ?_ (skeletonLT_mono (by rw[hn]))
      apply closedCell_subset_skeletonLT n i
      exact Set.mem_image_of_mem _ (Subtype.coe_prop (cubesretract n p).1)
    · exact skeletonLT_mono le_self_add h1.1
  · exact skeletonLT_mono le_self_add
      (cubesretract_mapsto_lt n i p (lt_of_le_of_ne (Fin.is_le n) hn)).1

def sumMap (m : ℕ) :
    (ungluedSkel X C (m + 1)) × unitInterval → skeletonLT X (m+1) × ℝ := fun p ↦
    p.1.elim
      (fun c => (⟨c.val, memBase_memSkeletonLT X c.prop (m + 1)⟩, p.2))
      (fun ⟨n, i, x⟩ => (⟨map n i (cubesretract n (x,p.2)).1, cubesretract_mapsto_weak n i (x,p.2)⟩,
        (cubesretract n (x,p.2)).2))

lemma sumMap_eq_SkelProj_C (m : ℕ)
    (x : C) (t : unitInterval) : sumMap m (Sum.inl x, t) =
    Prod.map id (Subtype.val) (SkeletonProjection X (m + 1) (Sum.inl x), t) := by
  simp [sumMap, SkeletonProjection]
  rfl

lemma sumMap_eq_SkelProj_LtOrSphere {m : ℕ}
    (n : Fin (m + 1)) (i : cell X n) (x' : closedBall (0 : Fin n → ℝ) 1) (t : unitInterval)
    (hx : n < m ∨ n = m ∧ x' ∈ sphere ⟨0, by simp⟩ 1) :
    sumMap m (Sum.inr ⟨n, ⟨i, x'⟩⟩, t) =
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

#check Topology.IsQuotientMap.continuous_lift_prod_left


 -- to shorten
lemma FinNeq_lt {n : ℕ} (m : Fin (n + 1)) (hnm : m ≠ n) : m < n := Nat.lt_of_le_of_ne m.is_le hnm

-- lemma xx {m : ℕ} (n : Fin (m + 1)) (hnm : n = m) (i : cell X n) (x' : ↑(closedBall 0 1)) (hx' : x' ∉ sphere ⟨0, by simp⟩ 1)
--   (n_y : Fin (m + 1)) (j_y : cell X ↑n_y) (y' : ↑(closedBall 0 1) ):
--   Sum.inr (⟨n_y, ⟨j_y, y'⟩⟩: (n : ℕ) × cell X n × (closedBall ⟨0 , by simp⟩ 1)) = Sum.inr ⟨n, ⟨i, x'⟩⟩ := sorry

lemma topopen_notLT {Y : Type*} [TopologicalSpace Y] [T2Space Y] (X : Set Y)
    {C : Set Y} [RelCWComplex X C] {n : ℕ} (i : cell X n)
    (x' : closedBall (0 : Fin n → ℝ) 1) (hx : x'.1 ∈ ball (0 : Fin n → ℝ) 1) (m : Fin (n + 1)) :
    (map n i ↑x') ∉ skeletonLT X m := by
  have h : (map n i ↑x') ∉ skeletonLT X n :=
    (disjoint_skeletonLT_openCell (by rfl)).notMem_of_mem_right (Set.mem_image_of_mem _ hx)
  have le : (m : ℕ∞) ≤ n := ENat.coe_le_coe.mpr (Order.lt_add_one_iff.1 m.isLt )
  exact fun mem ↦ h ((skeletonLT_mono le) mem)

lemma same_point {m : ℕ} (n_y : Fin (m + 1)) (j_y : cell X ↑n_y) (y' : (closedBall 0 1))
    (i : cell X ↑n_y) (x' : (closedBall 0 1)) (x_ball : ↑x' ∈ ball (0 : Fin n_y → ℝ) 1)
    (y_ball : y' ∈ ball (⟨0, by simp⟩ : closedBall (0 : Fin n_y → ℝ) 1) 1)
    (map_eq : (map (n_y) j_y) ↑y' = (map n_y i) x') (same_cell : j_y = i) : y' = x' := by
  rw [same_cell] at map_eq
  apply (map n_y i).injOn at map_eq
  · exact SetCoe.ext map_eq
  · rw [source_eq]; exact y_ball
  · rw [source_eq]; exact x_ball

lemma SkeletonProj_inj_top {Y : Type*} [TopologicalSpace Y] [T2Space Y] (X : Set Y)
    {C : Set Y} [RelCWComplex X C] {m : ℕ} {n : Fin (m + 1)} (hnm : ↑n = m) (i : cell X n)
    (x' : closedBall (0 : Fin n → ℝ) 1) (x_ball : x'.1 ∈ ball (0 : Fin n → ℝ) 1)
    (y : ungluedSkel X C (m + 1))
    (hskel : SkeletonProjection X (m + 1) (Sum.inr ⟨n, ⟨i, x'⟩⟩) = SkeletonProjection X (m + 1) y) :
    y = Sum.inr ⟨n, i, x'⟩ := by
  have x_notSkelTop : (SkeletonProjection X (m + 1) (Sum.inr ⟨n, ⟨i, x'⟩⟩)).1 ∉ skeletonLT X m :=
    topopen_notLT X i x' x_ball ⟨m, by simp [hnm]⟩
  obtain c | ⟨n_y, ⟨j_y, y'⟩⟩ := y
  · rw [hskel, SkeletonProj_const_C X (m + 1) 0 c] at x_notSkelTop
    exact (x_notSkelTop (memBase_memSkeletonLT X c.prop m)).elim
  · have map_eq : map n_y j_y y' = map n i x' := by
      simp [SkeletonProjection] at hskel
      exact hskel.symm
    by_cases y_ball : y' ∈ ball ⟨0, by simp⟩ 1
    · have same_cell : (⟨n_y, j_y⟩ : (n : ℕ) × cell X n) = ⟨n, i⟩ := by
        refine eq_of_not_disjoint_openCell ?_
        rw [Set.not_disjoint_iff]
        use map n i x'
        constructor
        · rw[← map_eq]
          apply Set.mem_image_of_mem; exact y_ball
        · exact Set.mem_image_of_mem _ x_ball
      rw [Sum.inr.inj_iff]
      rw [Sigma.mk.inj_iff, Fin.val_inj] at same_cell
      have hn : n_y = n := same_cell.1
      subst hn
      simp only [heq_eq_eq, true_and, Sigma.mk.injEq] at same_cell ⊢
      refine ⟨same_cell , ?_ ⟩
      exact same_point n_y j_y y' i x' x_ball y_ball map_eq same_cell
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
  exact ⟨y'.prop , h.2 ny_eq_m⟩

lemma factors (m : ℕ) : (sumMap m).FactorsThrough
    (fun p ↦ ((SkeletonProjection X (m + 1) p.1), p.2)) := by
  intro x y hxy
  rw [Prod.mk_inj] at hxy
  obtain ⟨heq1, heq2⟩ := hxy
  obtain ⟨cx | ⟨n, i, x'⟩, tx⟩ := x
  · -- x ∈ C
    rw [sumMap_eq_SkelProj_C, heq1]
    obtain ⟨ c_y | ⟨n_y, i_y, y'⟩, t⟩ := y
    · rw [← sumMap_eq_SkelProj_C]
      congr
    · simp only at heq2
      suffices hyLtSphere : ↑n_y < m ∨ ↑n_y = m ∧ y' ∈ sphere ⟨0, by simp⟩ 1 by
        rw [sumMap_eq_SkelProj_LtOrSphere n_y i_y y' t hyLtSphere, heq2, Prod.map_apply,
          Prod.map_apply, id_eq]
      by_contra hynotLTSphere
      have hytop_open : n_y = m ∧ y' ∈ ball ⟨0, by simp⟩ 1 := TopOpen n_y y' hynotLTSphere
      have : ↑(SkeletonProjection X (m + 1) (Sum.inl cx, tx).1) ∉ skeletonLT X ↑m := by
        rw[heq1]
        apply topopen_notLT X i_y y' hytop_open.2 ⟨m, by linarith⟩
      exact this (memBase_memSkeletonLT X cx.prop m)
  · -- x in some closed ball
    by_cases hxLtSphere : n < m ∨ n = m ∧ x' ∈ sphere ⟨0, by simp⟩ 1
    · simp only at heq2
      rw [sumMap_eq_SkelProj_LtOrSphere n i x' tx hxLtSphere, Prod.map_apply, heq1]
      obtain ⟨c | ⟨n_y, i_y, y'⟩, t⟩ := y
      · congr
      · suffices hynotTop : n_y < m ∨ ↑n_y = m ∧ y' ∈ sphere ⟨0, by simp⟩ 1 by
          rw [sumMap_eq_SkelProj_LtOrSphere n_y i_y y' t hynotTop, heq2, Prod.map_apply]
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
  Function.extend (fun p ↦ ((SkeletonProjection X (m + 1) p.1), p.2)) (sumMap m)
  (Prod.map id Subtype.val)

lemma r_apply_SumMap (m : ℕ) (p : skeletonLT X (m + 1) × unitInterval) :
    ∃ (s : (ungluedSkel X C (m + 1)) × unitInterval),
    SkeletonProjection X (m+1) s.1 = p.1 ∧ s.2 = p.2 ∧
    r m p = sumMap m s := by
  set s := Function.surjInv (SkeletonProjection_Surjective (m + 1) X) p.1
  use (s, p.2)
  have inv : p = (SkeletonProjection X (m + 1) s, p.2) := Prod.fst_eq_iff.mp
    (Function.surjInv_eq (SkeletonProjection_Surjective (m + 1) X) p.1).symm
  refine ⟨?_ , by rfl, ?_ ⟩
  · rw [Prod.ext_iff] at inv
    exact inv.1.symm
  · rw[inv, ← (factors m).extend_apply (Prod.map id Subtype.val) (s, p.2)]
    rfl

#check r_cube_IsretractionOn


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
  (C ⊕ (Σ (n : Fin (m + 1)) (_ : cell X n), closedBall (0 : Fin n → ℝ) 1)) × unitInterval ≃ₜ
  (C × unitInterval) ⊕ (Σ (n : Fin (m + 1)) (_ : cell X n),
    (closedBall (0 : Fin n → ℝ) 1) × unitInterval) :=
  Homeomorph.sumProdDistrib.trans
  ((Homeomorph.refl _ ).sumCongr (Homeomorph.sigmaProdDistrib.trans
    (Homeomorph.sigmaCongrRight' fun _ ↦ Homeomorph.sigmaProdDistrib)))

set_option linter.unusedSectionVars false

@[simp] lemma homeoProd_inl_symm (m : ℕ) (c : C) (t : unitInterval) :
    (homeoProd (X := X) m).symm (Sum.inl (c, t)) =  (Sum.inl c, t) := rfl

@[simp] lemma homeoProd_inr_symm (m : ℕ) (n : Fin (m + 1)) (i : cell X n)
    (x : closedBall (0 : Fin n → ℝ) 1) (t : unitInterval) :
    (homeoProd (X := X) m).symm (Sum.inr ⟨n, i, (x, t)⟩) = (Sum.inr ⟨n, i, x⟩, t) := rfl

#check Homeomorph.sumProdDistrib
#check Homeomorph.sigmaProdDistrib

lemma cts_sumMap_prehomeo (m : ℕ) : Continuous ((sumMap m) ∘ (homeoProd (X := X) m).symm)  := by
  have : (Sum.elim
    (fun (q : C × unitInterval) ↦ sumMap m ((Sum.inl q.1), q.2))
    (fun (q : Σ (n : Fin (m + 1)) (_ : cell X n), (closedBall (0 : Fin n → ℝ) 1 × unitInterval)) ↦
    sumMap m ((Sum.inr ⟨q.1 , ⟨q.2.1, q.2.2.1⟩⟩), q.2.2.2))) = (sumMap m) ∘ (homeoProd m).symm := by
    ext x <;>
    · obtain ⟨_ ,_ ⟩ | ⟨_ ,_ ,_ ,_ ⟩ := x
      · simp only [Sum.elim_inl, Function.comp_apply, homeoProd_inl_symm]
      · simp only [Sum.elim_inr, Function.comp_apply, homeoProd_inr_symm]
  rw[← this]
  apply Continuous.sumElim ?_ ?_
  · simp only [sumMap,  Sum.elim_inl, continuous_prodMk]
    refine ⟨by fun_prop , by fun_prop⟩
  · simp only [sumMap, Sum.elim_inr, Prod.mk.eta, continuous_sigma_iff]
    intro n i
    simp only [continuous_prodMk]
    constructor
    · refine Continuous.subtype_mk ?_ (cubesretract_mapsto_weak n i)
      apply (continuousOn n i).comp_continuous ?_ ?_
      · apply continuous_subtype_val.comp
        exact continuous_fst.comp (cubesretract_continuous n)
      · intro x
        exact Subtype.coe_prop (cubesretract n x).1
    · exact continuous_snd.comp (cubesretract_continuous n)

lemma continuousRetract (m : ℕ) : Continuous (r (X := X) m) := by
  refine (SkeletonProjectionIsQuotientMap (m +1) X).continuous_lift_prod_left ?_
  have cts_sumMap : Continuous (sumMap (X := X) m) :=
    (homeoProd m).symm.comp_continuous_iff'.1 (cts_sumMap_prehomeo m)
  apply cts_sumMap.congr ?_
  intro x
  rw [← (factors m).extend_apply (Prod.map id Subtype.val) x]
  rfl

/-
r ist now almost the retraction, we need for the retraction criterion. Only we have to extend the
second coordinate onto all of ℝ and then proof, it satisfies all conditions of a retraction:
-/


def retr_skeleton (m : ℕ) : (skeletonLT X (m + 1)) × ℝ → (skeletonLT X (m + 1)) × ℝ := fun p ↦
  (r m) (p.1, ⟨ProjIcc p.2, proj_mem p.2 ⟩)

lemma sumMap_mapsTo (m : ℕ) (x : (ungluedSkel X C (m + 1)) × ↑unitInterval) :
  (sumMap m x).2 = 0 ∨ ↑(sumMap m x).1 ∈ skeletonLT X ↑m ∧ ↑(sumMap m x).2 ∈ unitInterval := by
  obtain ⟨c |⟨n, i, x'⟩, t⟩ := x
  · simp only [sumMap,  Sum.elim_inl, Subtype.coe_prop, and_true]
    exact Or.inr (mem_skeletonLT_iff.mpr (Or.inl c.prop))
  · simp only [sumMap, Sum.elim_inr]
    by_cases hn : n = m
    · exact cubesretract_mapsto_top n i (x',t) hn
    · exact Or.inr (cubesretract_mapsto_lt n i (x',t) (lt_of_le_of_ne (Fin.is_le n) hn))

lemma sumMap_fixedOn (m : ℕ) {s : ↑(skeletonLT X (↑m + 1)).carrier × ℝ} (hs : s ∈ anchor
  ((skeletonLT X (↑m + 1)).carrier ↓∩ ↑(skeletonLT X ↑m))) (hs2 : s.2 ∈ unitInterval)
  (t : ↑unitInterval) (n : Fin (m + 1)) (i : cell X ↑n) (x' : ↑(closedBall 0 1))
  (hxproj1 : SkeletonProjection X (m + 1) (Sum.inr ⟨n, ⟨i, x'⟩⟩, t).1 = s.1)
  (hxproj2 : t = ⟨s.2, hs2⟩) : sumMap m (Sum.inr ⟨n, ⟨i, x'⟩⟩, t) = s := by
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
  apply (retraction_criterion_closed (IsClosed.preimage_val (skeletonLT X ↑m).closed') ).2
  use retr_skeleton m
  have ProjId (s : (skeletonLT X (↑m + 1)).carrier × ℝ) (hs : s.2 ∈ unitInterval ) :
      (⟨ProjIcc s.2, proj_mem s.2⟩ : unitInterval) = ⟨s.2, hs⟩ := by
    simp only [Subtype.mk.injEq]
    exact proj_id hs
  constructor
  · simp only [Set.mem_preimage, Set.mem_Icc, Set.setOf_subset_setOf, Prod.forall,
      forall_eq_or_imp, Std.le_refl, zero_le_one, and_self, and_imp, imp_self, implies_true]
  · apply (continuousRetract m).comp_continuousOn ?_
    refine ContinuousOn.prodMk continuousOn_fst (by fun_prop [proj_cont])
  · intro s hs
    unfold retr_skeleton
    obtain ⟨x, hxproj1, _ , hxsum⟩ := r_apply_SumMap m (s.1, ⟨s.2, hs⟩)
    simp only [ProjId s hs, Set.mem_preimage, Set.mem_setOf_eq, hxsum]
    exact sumMap_mapsTo m x
  · intro s hs
    have hs2 : s.2 ∈ unitInterval := by -- shorten
      rcases hs with h0 | hI
      · rw[h0]
        exact unitInterval.zero_mem
      · exact hI.2
    obtain ⟨x, hxproj1, hxproj2, hxsum⟩ := r_apply_SumMap (X := X) m (s.1, ⟨s.2, hs2⟩)
    simp only [retr_skeleton, ProjId s hs2, hxsum]
    obtain ⟨c | ⟨n, i, x'⟩, t⟩ := x
    · simp only [SkeletonProjection, Sum.elim_inl] at hxproj1 hxproj2
      refine Prod.ext_iff.mpr ⟨ ?_, ?_ ⟩
      · simp only [sumMap, Sum.elim_inl]
        exact hxproj1
      · simp [sumMap, hxproj2]
    · exact sumMap_fixedOn m hs hs2 t n i x' hxproj1 hxproj2
