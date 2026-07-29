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

def SkeletonProjection {Y : Type*} [TopologicalSpace Y] [T2Space Y] (X : Set Y) {C : Set Y}
  [RelCWComplex X C] (m : ℕ) :
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

-- unnötig lang. einfach direkt Sum.inr ....
def cell_incl {Y : Type*} [TopologicalSpace Y] [T2Space Y] (X : Set Y) {C : Set Y}
  [RelCWComplex X C] (m : ℕ) (n : Fin m) (i : cell X n) : (closedBall (0 : Fin n → ℝ) 1) →
  C ⊕ (Σ (n : Fin m) ( _ : cell X n), (closedBall (0 : Fin n → ℝ) 1)) := fun p ↦ Sum.inr ⟨n,i,p⟩


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
-- IsClosed (Sum.inl ⁻¹' (SkeletonProjection m X ⁻¹' S))

lemma SkeletonProjectionIsQuotientMap (m : ℕ) {Y : Type*} [hY : TopologicalSpace Y] [T2Space Y]
  (X : Set Y) {C : Set Y} [RelCWComplex X C] :
    IsQuotientMap (SkeletonProjection X m) := by
  refine (isQuotientMap_iff (SkeletonProjection X m)).mpr ?_
  refine ⟨?_ , SkeletonProjection_Surjective m X⟩
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
    have hpre_base : (Sum.inl ⁻¹' (SkeletonProjection X m⁻¹' S)) = S' ∩ C := by
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
      have hg_closedMap: IsClosedMap g := (continuousOn k j).restrict.isClosedMap
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
        exact (Subtype.val_injective.mem_set_image).1 (Set.mem_of_mem_inter_left hx)
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
    exact hS.preimage (SkeletonProjection_Continuous m X)

lemma SkeletonProj_mono_C {Y : Type*} [TopologicalSpace Y] [T2Space Y] (X : Set Y)
    {C : Set Y} [RelCWComplex X C] (m : ℕ) (n : ℕ) (c : C) :
    (SkeletonProjection X m (Sum.inl c)) = (SkeletonProjection X n (Sum.inl c)).1 := rfl


    /-
    have : (m : ℕ∞) ≤ n := by exact ENat.coe_le_coe.mpr hmn
    apply Topology.CWComplex.skeletonLT_mono this
     , by
    exact Subtype.coe_prop (SkeletonProjection X m (Sum.inl c))⟩ := by rfl
-/
open RelCWComplex

lemma SkeletonProj_inj_top {Y : Type*} [TopologicalSpace Y] [T2Space Y] (X : Set Y)
    {C : Set Y} [RelCWComplex X C] (m : ℕ) (y : skeletonLT X m) (hy : ∃ (j : cell X (m - 1)),
    y.1 ∈ openCell (m - 1) j) (x : C ⊕ (Σ (n : Fin m) (_ : cell X n),
    (closedBall (0 : Fin n → ℝ) 1))) :
    SkeletonProjection X m x = y → Sum.elim (fun _ ↦ false) (fun p ↦ p.1 = m - 1) x := by
  intro hxy
  obtain ⟨j, hyj ⟩ := hy
  have y_notMem:  y.1 ∉ skeletonLT X (m - 1):= by
    have : Disjoint ((skeletonLT X (m - 1 : ℕ∞)).carrier) (openCell (m-1) j) :=
      RelCWComplex.disjoint_skeletonLT_openCell (ENat.forall_natCast_le_iff_le.mp fun a a_1 ↦ a_1)
    intro h
    exact (Set.disjoint_right.1 this hyj) h
  obtain c | ⟨n, i, x'⟩  := x
  · simp only [Bool.false_eq_true, Sum.elim_inl]
    have := (SkeletonProjection X (m-1) (Sum.inl c)).2
    rw [SkeletonProj_mono_C X (m-1) m c] at this -- ist m - 1 eine natürliche Zahl?? nein hehe
    rw [hxy] at this
    exact y_notMem this
  · simp only [Bool.false_eq_true, Sum.elim_inr]
    rw[← hxy] at y_notMem
    simp only [SkeletonProjection, Sum.elim_inr] at y_notMem
    have mem : (map (↑n) i) ↑x' ∈ closedCell n i := by
      rw [show closedCell n i = map n i '' closedBall 0 1 by rfl]
      refine Set.mem_image_of_mem ↑(map (↑n) i) x'.prop
    by_contra h
    have le : (n + 1 : ℕ∞)  ≤ m - 1 := by
      have : (n + 1)  ≤ m - 1 := Nat.lt_of_le_of_ne (Nat.le_sub_one_of_lt n.prop) h
      rw[← ENat.coe_le_coe] at this
      exact le_of_eq_of_le rfl this
    exact y_notMem (skeletonLT_mono le (closedCell_subset_skeletonLT n i mem))

lemma SkeletonProj_not_top {Y : Type*} [TopologicalSpace Y] [T2Space Y] (X : Set Y)
    {C : Set Y} [RelCWComplex X C] (m : ℕ) (y : skeletonLT X m) (hy : ¬ ( ∃ (j : cell X m),
    y.1 ∈ openCell m j)) (x : C ⊕ (Σ (n : Fin m) (_ : cell X n), (closedBall (0 : Fin n → ℝ) 1))) :
    SkeletonProjection X m x = y → Sum.elim (fun _ ↦ true) (fun p ↦ p.1 < m) x := by
  intro hxy
  simp at hy
  have : y.1 ∈ C ∨ (∃ (n : Fin m) (j : cell X n),  y.1 ∈ openCell n j) := by sorry
  --obtain ⟨ ⟩
  sorry

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] (X : Set Y) {C : Set Y} [RelCWComplex X C]

#check r_cube
#check r_cube_IsretractionOn
#check Set.iUnion
#check Topology.RelCWComplex.skeleton_mono
#check Topology.RelCWComplex.closedCell_subset_skeletonLT

def R_I : ℝ → unitInterval := fun p ↦
  if h : p ∈ unitInterval then ⟨p, h⟩
  else Classical.choice Zero.instNonempty

lemma id_R_I (t : unitInterval) : R_I t.1 = t := by simp [R_I]

lemma cts_R_I : ContinuousOn R_I unitInterval := by
  refine continuousOn_iff_continuous_restrict.mpr ?_
  have : (unitInterval.restrict R_I) = id := by
    ext x
    simp only [R_I, Set.restrict_apply, Subtype.coe_eta, dite_eq_ite, id_eq]
    simp only [x.2, ↓reduceIte]
  rw [this]
  exact continuous_id

-- ursprüngliche Version, kann hier später den Beweis, dass R_I nichts verändert, klauen, wenn ich
-- was über cubesretract beweisen will
def cubesretract' (m : ℕ) (n : Fin (m + 1)) :
    (closedBall (0 : Fin (n : ℕ) → ℝ) 1) × unitInterval →
    (closedBall (0 : Fin (n : ℕ) → ℝ) 1) × unitInterval := fun p ↦
  if n = m then ((r_cube (n : ℕ) (p.1,p.2)).1, ⟨(r_cube (n : ℕ) (p.1,p.2)).2, by
    have : (p.1, (p.2 : ℝ)) ∈ {p | p.2 ∈ unitInterval} := Set.mem_sep_iff.mpr p.2.2
    obtain h | h := (r_cube_IsretractionOn n).mapsTo this
    · rw[h]
      exact unitInterval.zero_mem
    · exact h.2 ⟩)
  else id p
-- bis hier

def cubesretract (m : ℕ) (n : Fin (m + 1)) :
    (closedBall (0 : Fin (n : ℕ) → ℝ) 1) × unitInterval →
    (closedBall (0 : Fin (n : ℕ) → ℝ) 1) × unitInterval := fun p ↦
  if n = m then ((r_cube (n : ℕ) (p.1,p.2)).1, R_I (r_cube (n : ℕ) (p.1,p.2)).2)
  else id p

lemma cubesretract_of_eq {m : ℕ} {n : Fin (m + 1)} (h : (n : ℕ) = m) : true := by sorry
--- dinge von r_cube beweisen (continuous, mapsto, fixedOn, ...)

#check r_cube
#check (r_cube_IsretractionOn 2).fixesOn

lemma cubesretract_fixedOn {m : ℕ} {n : Fin (m + 1)}
    (x : (closedBall (0 : Fin (n : ℕ) → ℝ) 1) × unitInterval) :
    (n < m → cubesretract m n x = x) ∧
    (n = m → x ∈ {z | z.2 = 0 ∨ z.1 ∈ sphere ⟨0, by simp⟩ 1 } → cubesretract m n x = x):= by
  by_cases h : n = m
  · simp only [h, lt_self_iff_false, IsEmpty.forall_iff, Set.mem_setOf_eq,
    forall_const, true_and]
    intro hx
    have := (r_cube_IsretractionOn n).fixesOn (x.1,x.2) (by
      obtain hx1 | hx2 :=  hx
      · exact Or.inl (Set.Icc.coe_eq_zero.mpr hx1)
      · exact Or.inr ⟨ mem_sphere.mpr hx2, unitInterval.mem_unitIntervalSubmonoid.mp x.2.prop⟩)
    simp[ cubesretract, this, id_R_I]
  · simp[cubesretract, h]

lemma cubesretract_of_ne {m : ℕ} {n : Fin (m + 1)} (h : (n : ℕ) ≠ m) :
    cubesretract m n = id := by
  unfold cubesretract
  simp only [h, ↓reduceIte, id_eq]
  exact Prod.id_prod

def baseMap (m : ℕ) : C × unitInterval → ↥(skeletonLT X (m + 1)) × unitInterval := fun p ↦
  (⟨p.1 , mem_skeleton_iff.mpr (Or.inl p.1.2)⟩, p.2)

lemma cubesretract_mapsto (m : ℕ) (n : Fin (m + 1)) (i : cell X n)
    (p : (closedBall 0 1) × ↑unitInterval) :
    (map n i) (cubesretract m n p).1 ∈ skeletonLT X (m + 1) := by
  unfold cubesretract
  have : (p.1, (p.2 : ℝ )) ∈ {p | p.2 ∈ unitInterval} := Set.mem_sep_iff.mpr p.2.2
  have mapsto := (r_cube_IsretractionOn n).mapsTo this
  by_cases h : m = n
  · simp only [h, ↓reduceIte]
    apply closedCell_subset_skeletonLT n i
    apply Set.mem_image_of_mem
    exact Subtype.coe_prop (r_cube ↑n (p.1, ↑p.2)).1
  · rw[eq_comm] at h
    simp only [h, ↓reduceIte, id_eq]
    apply Topology.CWComplex.skeletonLT_mono (m := n + 1) ?_ ?_
    · rw [le_iff_eq_or_lt, ← Nat.cast_add_one m]
      simp only [Nat.cast_add, Nat.cast_one, ne_eq, ENat.one_ne_top, not_false_eq_true,
        add_lt_add_iff_left_of_ne_top, Nat.cast_lt, Nat.lt_iff_le_and_ne ]
      exact Or.inr ⟨Nat.le_iff_lt_add_one.2 n.prop, Ne.intro h⟩
    · apply closedCell_subset_skeletonLT n i
      apply Set.mem_image_of_mem
      exact Subtype.coe_prop p.1

def cubeMap (m : ℕ) (n : Fin (m + 1)) (i : cell X n) :
    (closedBall (0 : Fin (n : ℕ) → ℝ) 1) × unitInterval → ↥(skeletonLT X (m + 1)) × unitInterval :=
  fun p =>
    (⟨map (n : ℕ) i (cubesretract m n p).1, cubesretract_mapsto X m n i p⟩, (cubesretract m n p).2)

lemma cubeMap_cell_lt_apply (m : ℕ) (n : Fin (m + 1)) (hn : n < m) (i : cell X n)
    (x : (closedBall (0 : Fin (n : ℕ) → ℝ) 1) × unitInterval) :
    cubeMap X m n i x = (SkeletonProjection X (m + 1) (Sum.inr ⟨n,i,x.1⟩), x.2) := by
  simp[cubeMap, SkeletonProjection, cubesretract, ( Nat.ne_of_lt hn)]
  rfl

def sumMap (m : ℕ) :
    (C ⊕ (Σ (n : Fin (m + 1)) (_ : cell X n), closedBall (0 : Fin n → ℝ) 1)) × unitInterval →
    skeletonLT X (m+1) × unitInterval := fun p ↦
    p.1.elim
      (fun c => baseMap X m (c, p.2))
      (fun ⟨n, i, x⟩ => cubeMap X m n i (x, p.2))

#check Sum.elim

lemma sumMap_C_apply (m : ℕ)
    (x : C) (t : unitInterval) :
    sumMap X m (Sum.inl x, t) = (SkeletonProjection X (m + 1) (Sum.inl x), t) := by
  simp [sumMap, SkeletonProjection, baseMap]
  rfl

lemma sumMap_lt_sphere_apply (m : ℕ)
    (x : (Σ (n : Fin (m + 1)) (_ : cell X n), closedBall (0 : Fin n → ℝ) 1)) (t : unitInterval)
    (hx : x.1 < m ∨ x.1 = m ∧ x.2.2 ∈ sphere ⟨0, by simp⟩ 1) :
    sumMap X m (Sum.inr x, t) = (SkeletonProjection X (m + 1) (Sum.inr x), t) := by
  obtain ⟨n, i, x'⟩ := x
  obtain hx_lt | ⟨ hx_eq, hx_sphere⟩  := hx
  · have := cubeMap_cell_lt_apply X m n (Nat.lt_of_succ_le hx_lt) i (x',t)
    simp only [sumMap, Sum.elim_inr, this]
  · simp only at hx_eq
    have := (cubesretract_fixedOn (x', t)).2 hx_eq (Or.inr hx_sphere)
    simp[sumMap, cubeMap, this, SkeletonProjection]
    rfl


#check Topology.IsQuotientMap.continuous_lift_prod_left


lemma factors (m : ℕ) : Function.FactorsThrough (sumMap X m) (fun p ↦ ((SkeletonProjection X (m +1) p.1), id p.2)) := by
  intro x y hxy
  rw [Prod.mk_inj] at hxy
  obtain ⟨x1_eq_y1, h2 ⟩ := hxy
  have x2_eq_y2 : x.2 = y.2 := by
    rw [id_eq, id_eq] at h2
    exact h2
  obtain ⟨cx | ⟨n, i, x'⟩, tx⟩ := x
  · simp only at x2_eq_y2
    sorry
  · simp only at x2_eq_y2
    by_cases hnm : n < m ∨ n = m ∧ x' ∈ sphere ⟨0, by simp⟩ 1
    · have := sumMap_lt_sphere_apply X m ⟨n, i, x'⟩ tx hnm
      sorry
    · simp only [not_or, not_lt, not_and] at hnm
      have n_eq_m : ↑n = m :=  Eq.symm (Nat.le_antisymm hnm.1 (Fin.is_le n))
      set x'skel : skeletonLT X (m + 1) := SkeletonProjection X (m + 1) (Sum.inr ⟨n, ⟨i, x'⟩⟩, tx).1
      have x'_mem_ball: x' ∈ ball ⟨0, by simp⟩ 1 := by
        rw[← Metric.closedBall_sdiff_sphere]
        exact ⟨x'.prop, hnm.2 n_eq_m⟩
      have x'skel_mem_cell : x'skel.1 ∈ openCell n i := by
        rw [show openCell n i = map n i '' ball 0 1 by rfl]
        

        sorry
      have := SkeletonProj_inj_top X (m + 1) x'skel


      -- (y : skeletonLT X m) (hy : ∃ (j : cell X (m - 1)), y.1 ∈ openCell (m - 1) j)
      sorry

  /-
  unfold sumMap
  cases x.1 with
    | inl c =>
      simp [baseMap]
      sorry
    | inr s => sorry
  -/

def r (m : ℕ) : skeletonLT X (m + 1) × unitInterval → skeletonLT X (m + 1) × unitInterval :=
  Function.extend (fun p ↦ ((SkeletonProjection X (m +1) p.1), id p.2)) (sumMap X m) id

lemma r_rw (m : ℕ) :
  sumMap X m = fun q ↦ r X m ((SkeletonProjection X (m +1) q.1), id q.2) := by
  apply funext_iff.2
  intro x
  rw [← Function.FactorsThrough.extend_apply (factors X m) id x]
  rfl

lemma cts (m : ℕ) : Continuous fun (q : (C ⊕ (Σ (n : Fin (m + 1)) (_ : cell X n),
  (closedBall (0 : Fin n → ℝ) 1))) × unitInterval) ↦ r X m ((SkeletonProjection X (m +1) q.1), id q.2) := by
  rw[← r_rw X m ]
  unfold sumMap

  sorry

lemma continuousRetract (m : ℕ) : Continuous (r X m) := by
  exact (SkeletonProjectionIsQuotientMap (m +1) X).continuous_lift_prod_left (cts X m)


/-
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
    let valC := r_cube m (⟨y, by
      apply ball_subset_closedBall (mem_ball.mpr p_mem)⟩ , t)
    let val := (map m i valC.1, valC.2)
    let val1mem : map m i valC.1 ∈ closedCell m i := by

      sorry
    (⟨val.1, closedCell_subset_skeleton m i val1mem ⟩, val.2)
  else (p, t)


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
