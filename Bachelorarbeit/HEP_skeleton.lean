import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Data.Set.Subset
import Mathlib.Topology.Defs.Filter
import Mathlib.Data.PEquiv
import Bachelorarbeit.HEP_definition
import Bachelorarbeit.HEP_ball_cube
import Bachelorarbeit.HEP_cell

open Metric
open Set.Notation
open Topology
open RelCWComplex

noncomputable section

#check r_cube
#check r_cube_IsretractionOn
#check Set.iUnion
#check Topology.RelCWComplex.skeleton_mono
#check Topology.RelCWComplex.closedCell_subset_skeletonLT

def SkeletonProjection (m : ℕ) {Y : Type*} [TopologicalSpace Y] [T2Space Y] (X : Set Y) {C : Set Y}
  [RelCWComplex X C] :
    C ⊕ (Σ (n : Fin m) ( _ : cell X n), (closedBall (0 : Fin n → ℝ) 1)) → skeletonLT X m :=
  Sum.elim
  (fun c ↦ ⟨c, by
    apply Topology.RelCWComplex.skeletonLT_mono (by positivity)
    rw[Topology.RelCWComplex.skeletonLT_zero_eq_base]
    exact c.prop ⟩)
  (fun ⟨n, i, x⟩ => ⟨map n i x, by
    have : (n +1 : ℕ∞) ≤ (m : ℕ∞) := by exact_mod_cast Nat.succ_le_of_lt n.isLt
    apply Topology.RelCWComplex.skeletonLT_mono this
    apply Topology.RelCWComplex.closedCell_subset_skeletonLT n i
    exact Set.mem_image_of_mem ↑(map (↑n) i) x.prop⟩)

#check Fin.mk

lemma SkeletonProjection_Surjective (m : ℕ) {Y : Type*} [hY : TopologicalSpace Y] [T2Space Y]
  (X : Set Y) {C : Set Y} [RelCWComplex X C] : Function.Surjective (SkeletonProjection m X) := by
  intro y
  have yprop := y.prop
  rw [mem_skeletonLT_iff] at yprop
  rcases yprop with hyBasis | hyCell
  · refine Sum.exists.mpr ?_
    left
    use ⟨y.1, hyBasis⟩
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
    (X : Set Y) {C : Set Y} [RelCWComplex X C] : Continuous (SkeletonProjection m X) := by
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
-- IsClosed (Sum.inl ⁻¹' (SkeletonProjection m X ⁻¹' S))

lemma SkeletonProjectionIsQuotientMap (m : ℕ) {Y : Type*} [hY : TopologicalSpace Y] [T2Space Y]
  (X : Set Y) {C : Set Y} [RelCWComplex X C] :
    IsQuotientMap (SkeletonProjection m X) := by
  refine (isQuotientMap_iff (SkeletonProjection m X)).mpr ?_
  refine ⟨?_ , SkeletonProjection_Surjective m X⟩
  refine IsCoinducing.of_isClosed_preimage_iff_isClosed ?_
  intro S
  constructor
  · intro hS
    simp only [isClosed_sum_iff, isClosed_sigma_iff] at hS
    obtain ⟨hBase, hBall⟩ := hS
    set S' : Set Y := Subtype.val '' S with hS'def
    have hS'sub : S' ⊆ (skeletonLT X m):= by
      rintro _ ⟨a, -, rfl⟩;
      exact a.2
    have hpre_base : (Sum.inl ⁻¹' (SkeletonProjection m X ⁻¹' S)) = S' ∩ C := by
      ext s
      simp only [SkeletonProjection, Set.mem_image, Set.mem_preimage, Sum.elim_inl,
        Subtype.exists, exists_and_right, exists_eq_right, Set.mem_inter_iff, hS'def]
      constructor
      · intro ⟨hs_memC, _ ⟩
        refine ⟨?_ , hs_memC⟩
        rw[← Topology.RelCWComplex.skeletonLT_zero_eq_base (C := X) ] at hs_memC
        apply Topology.RelCWComplex.skeletonLT_mono (by positivity) at hs_memC
        use hs_memC
      · intro ⟨⟨ _ , _⟩, hs_memC⟩
        use hs_memC
    have hlow : ∀ (k : ℕ), k < m → ∀ (j : cell X k), IsClosed (S' ∩ closedCell k j) := by
      intro k hk j
      set g : (closedBall (0 : Fin k → ℝ) 1) → Y := fun p => map k j (p : Fin k → ℝ) with hg_def
      have hg_closedMap: IsClosedMap g := (ContinuousOn.restrict (continuousOn k j)).isClosedMap
      have hrange : Set.range g = closedCell k j := by
        rw [show closedCell k j = map k j '' closedBall 0 1 by rfl, hg_def,
          show (fun p : ↥(closedBall (0 : Fin k → ℝ) 1) => map k j (p : Fin k → ℝ))
          = map k j ∘ (Subtype.val) by rfl, Set.range_comp, Subtype.range_coe]
      have himg : S' ∩ closedCell k j = g '' (g ⁻¹' S') := by
        rw [Set.image_preimage_eq_inter_range, hrange]
      rw [himg]
      apply hg_closedMap
      convert hBall ⟨k, hk⟩ j
      ext x
      constructor
      · intro hx
        apply Set.mem_image_of_mem g at hx
        rw[← himg] at hx
        simp only [SkeletonProjection, Sum.elim_inr,Set.mem_preimage]
        apply (Subtype.val_injective.mem_set_image).1 ?_
        exact Set.mem_of_mem_inter_left hx
      · intro hx
        simp only [Set.mem_preimage] at hx
        apply (Subtype.val_injective.mem_set_image).2 hx
    have : S = (skeletonLT X m).carrier ↓∩ S' := (S.preimage_image_eq Subtype.val_injective).symm
    rw[this]
    apply IsClosed.preimage_val ?_
    have hbaseClosed : IsClosed (S' ∩ C) := by
      rw [← hpre_base]
      exact IsClosed.trans hBase (isClosedBase X)
    refine isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell hS'sub hbaseClosed ?_
    intro n hn j
    by_cases h : n < m
    · right
      apply (hlow n h)
    · left
      suffices hempty : S' ∩ openCell n j = ∅ by
        rw[hempty]
        exact isClosed_empty
      rw [Nat.not_lt] at h
      apply Disjoint.inter_eq
      exact Set.disjoint_of_subset_left hS'sub
        (disjoint_skeletonLT_openCell (ENat.coe_le_coe.mpr h))
  · intro hS
    refine IsClosed.preimage ?_ hS
    exact SkeletonProjection_Continuous m X

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] (X : Set Y) {C : Set Y} [RelCWComplex X C]

#check Topology.IsQuotientMap.continuous_lift_prod_left

def φ {m : ℕ} (n : Fin (m + 1)) (i : cell X n) : ℝ → (Fin n → ℝ) → (Fin n → ℝ) :=
  fun t ↦ sorry




open Classical in
def RetractIntervalSkeleton {m : ℕ} (hm : 0 < m) :
  skeletonLT X (m + 1) × unitInterval → skeletonLT X (m +1) × ℝ := fun (p,t) ↦
  if hi : (∃ i : cell X m, (p : Y) ∈ openCell m i) then
    let i : cell X m := hi.choose
    let hi_i : (p : Y) ∈ openCell m i := hi.choose_spec
    let y := (map m i).symm p
    let p_mem : y ∈ ball (0 : Fin m → ℝ) 1 := by
      rw [show openCell m i = map m i ''ball (0 : Fin m → ℝ) 1 by rfl] at hi_i
      --have : ball (0 : Fin m → ℝ) 1 = (map (C := X) m i).target := by sorry
      --have := PartialEquiv.map_source (map m i)
      sorry
    let valC := r_cube hm (⟨y, by
      apply ball_subset_closedBall (mem_ball.mpr p_mem)⟩ , t)
    let val := (map m i valC.1, valC.2)
    let val1mem : map m i valC.1 ∈ closedCell m i := by

      sorry
    (⟨val.1, closedCell_subset_skeleton m i val1mem ⟩, val.2)
  else (p, t)

/-
lemma RetractIntervalSkeleton_applyCell {m : ℕ} (hm : 0 < m) {Y : Type*} [TopologicalSpace Y]
  [T2Space Y] (X : Set Y) {C : Set Y} [RelCWComplex X C] (i : cell X m)
    (p : skeletonLT X (m + 1)) (hp : (p : Y) ∈ closedCell m i) (t : unitInterval) :
    RetractIntervalSkeleton hm X (p, t) = (⟨(r_cell hm i (⟨p, hp ⟩, t)).1.1 , by
      suffices h : ((r_cell hm i (⟨p, hp ⟩, t)).1 : Y ) ∈ closedCell m i by
        exact Topology.RelCWComplex.closedCell_subset_skeleton m i h
      exact Subtype.coe_prop (r_cell hm i (⟨↑p, hp⟩, t)).1⟩ , (r_cell hm i (⟨p, hp ⟩, t)).2) := by
  unfold RetractIntervalSkeleton
  by_cases h : (p : Y)  ∈ openCell m i
  · have hj : ∃ (j : cell X m), (p : Y) ∈ openCell m j := by use i
    simp only [hj, ↓reduceDIte, Prod.mk.injEq, Subtype.mk.injEq]
    have heq : hj.choose = i := (uniqueOpenCell (p :Y) hj).unique hj.choose_spec h
    subst heq
    refine ⟨?_, ?_⟩
    ·
      sorry

    sorry

  sorry -/
  /-
  unfold r_dimCW
  by_cases h : (p : Y)  ∈ openCell m i
  · have hj : ∃ (j : cell X m), (p : Y) ∈ openCell m j := by use i
    simp only [hj, ↓reduceDIte, Prod.mk.injEq, Subtype.mk.injEq]
    have heq : hj.choose = i := (uniqueOpenCell (p :Y) hj).unique hj.choose_spec h
    subst heq
    refine ⟨rfl,rfl⟩
  · have hj : ¬ (∃ (j : cell X m), (p : Y) ∈ openCell m j) := by
      have pSkeleton: (p : Y) ∈ skeletonLT X m := by
        apply Topology.RelCWComplex.iUnion_cellFrontier_subset_skeletonLT
        refine Set.mem_iUnion.mpr ?_
        use i
        rw [CellFroniterEqClosedWithoutOpen m i] --!
        exact Set.mem_diff_of_mem hp h
      by_contra
      obtain ⟨j, hj⟩ := this
      have mm : (m : ℕ∞ ) ≤ m := ENat.forall_natCast_le_iff_le.mp fun a a_1 ↦ a_1
      exact Disjoint.notMem_of_mem_left (@Topology.RelCWComplex.disjoint_skeletonLT_openCell
        Y _ X C _ _ _ m j mm) pSkeleton hj
    simp only [hj, ↓reduceDIte, Prod.mk.injEq]
    suffices h : r_cell hm i (⟨↑p, hp⟩, t) = (⟨↑p, hp⟩,t) by simp[h]
    have fixmem : (⟨p, hp⟩,t) ∈ {p : closedCell m i × ℝ | p.2 = 0 ∨ ↑p.1 ∈ cellFrontier m i ∧
        p.2 ∈ unitInterval} := by
      right
      refine ⟨?_, unitInterval.mem_unitIntervalSubmonoid.mp ht⟩
      rw [CellFroniterEqClosedWithoutOpen m i]
      exact Set.mem_diff_of_mem hp h
    exact (r_cell_IsretractionOn hm i ).3 _ fixmem-/

/-
lemma RetractionSkeletonContinuous (m : ℕ) (hm : 0 < m) {Y : Type*} [TopologicalSpace Y] [T2Space Y] (X : Set Y)
    {C : Set Y} [RelCWComplex X C] : Continuous (RetractIntervalSkeleton hm X) := by
  apply @IsQuotientMap.continuous_lift_prod_left (C ⊕ (Σ (n : Fin (m + 1)) ( _ : cell X n),
    (closedBall 0 1))) (skeletonLT X (m + 1)) unitInterval ((skeletonLT X (m + 1)) × ℝ)
    _ _ _ _ _ (SkeletonProjection (m+1) X) (SkeletonProjectionIsQuotientMap (m +1) X)
  sorry
-/
