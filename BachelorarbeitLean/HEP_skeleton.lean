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

open RelCWComplex

/- erste version nicht nru geliche zelle, nicht komplett gleiches urbild-/

/-
lemma SkeletonProj_inj_top {Y : Type*} [TopologicalSpace Y] [T2Space Y] (X : Set Y)
    {C : Set Y} [RelCWComplex X C] (m : ℕ) (y : skeletonLT X m) (hy : ∃ (j : cell X (m - 1)),
    y.1 ∈ openCell (m - 1) j) (x : C ⊕ (Σ (n : Fin m) (_ : cell X n),
    (closedBall (0 : Fin n → ℝ) 1))) :
    SkeletonProjection X m x = y → Sum.elim (fun _ ↦ false) (fun p ↦ p.1 = m - 1) x := by
  intro hxy
  obtain ⟨j, hyj⟩ := hy
  have y_notMem:  y.1 ∉ skeletonLT X (m - 1):= by
    intro h
    refine (Set.disjoint_right.1 ?_ hyj) h
    exact RelCWComplex.disjoint_skeletonLT_openCell (ENat.forall_natCast_le_iff_le.mp fun a a ↦ a)
  obtain c | ⟨n, i, x'⟩ := x
  · simp only [Bool.false_eq_true, Sum.elim_inl]
    have := (SkeletonProjection X (m-1) (Sum.inl c)).2
    rw [SkeletonProj_mono_C X (m-1) m c, hxy] at this -- ist m - 1 eine natürliche Zahl?? nein hehe
    exact y_notMem this
  · simp only [Bool.false_eq_true, Sum.elim_inr]
    simp only [hxy.symm, SkeletonProjection, Sum.elim_inr] at y_notMem
    by_contra h
    refine y_notMem (skeletonLT_mono ?_ (closedCell_subset_skeletonLT n i ?_))
    · refine le_of_eq_of_le rfl ?_
      exact ENat.coe_le_coe.mpr (Nat.lt_of_le_of_ne (Nat.le_sub_one_of_lt n.prop) h)
    · rw [show closedCell n i = map n i '' closedBall 0 1 by rfl]
      exact Set.mem_image_of_mem ↑(map (↑n) i) x'.prop
-/

-- durchschauen, wo dieses lemma benutzen (wurde erst nachträglich geschrieben, weil oft benutzt)
lemma C_zeroskel {Y : Type*} [TopologicalSpace Y] [T2Space Y] {X : Set Y}
    {C : Set Y} [RelCWComplex X C] {m : ℕ} (c : C) :
  (SkeletonProjection X m  (Sum.inl c)).1 ∈ (skeletonLT X 0).carrier := by
  rw[ SkeletonProj_mono_C X m 0]
  exact Subtype.coe_prop (SkeletonProjection X 0 (Sum.inl c))

-- same hier
lemma topopen_notLT {Y : Type*} [TopologicalSpace Y] [T2Space Y] {X : Set Y}
    {C : Set Y} [RelCWComplex X C] (n : ℕ) (i : cell X n) (x' : closedBall (0 : Fin n → ℝ) 1)
    (hx : x'.1 ∈ ball (0 : Fin n → ℝ) 1) :
    (map n i ↑x') ∉ skeletonLT X n := by
  apply Disjoint.notMem_of_mem_left (disjoint_skeletonLT_openCell (by rfl)).symm
  apply Set.mem_image_of_mem
  exact hx

lemma SkeletonProj_inj_top {Y : Type*} [TopologicalSpace Y] [T2Space Y] (X : Set Y)
    {C : Set Y} [RelCWComplex X C] {m : ℕ} {n : Fin (m + 1)} (hnm : ↑n = m) (i : cell X n)
    (x' : closedBall (0 : Fin n → ℝ) 1)
    (hx' : x' ∉ sphere (⟨0, by simp⟩ : closedBall (0 : Fin n → ℝ) 1) 1)
    (y : C ⊕ (Σ (n : Fin (m + 1)) (_ : cell X n), (closedBall (0 : Fin n → ℝ) 1)))
    (hskel : SkeletonProjection X (m + 1) (Sum.inr ⟨n, ⟨i, x'⟩⟩) = SkeletonProjection X (m + 1) y) :
    y = Sum.inr ⟨n, i, x'⟩ := by
  have x_ball : x'.1 ∈ ball (0 : Fin n → ℝ) 1 := by
    rw [← Metric.closedBall_sdiff_sphere]
    exact ⟨Subtype.coe_prop x', hx'⟩
  obtain c | ⟨n_y, ⟨j_y, y'⟩⟩:= y
  · suffices h : (SkeletonProjection X (m + 1) (Sum.inr ⟨n, ⟨i, x'⟩⟩)).1 ∉ skeletonLT X m by
      rw[hskel, SkeletonProj_mono_C X (m + 1) 0 c] at h
      have : (SkeletonProjection X 0 (Sum.inl c)).1 ∈ (skeletonLT X ↑0).carrier :=
        Subtype.coe_prop (SkeletonProjection X 0 (Sum.inl c))
      exact (h (skeletonLT_mono zero_le this)).elim
    rw [SkeletonProjection, Sum.elim_inr]
    have : skeletonLT X m = skeletonLT X n := by rw [hnm]
    rw[this]
    apply Disjoint.notMem_of_mem_left (disjoint_skeletonLT_openCell (by rfl)).symm
    apply Set.mem_image_of_mem
    exact x_ball
  · have hY : map ↑n_y j_y y' = map ↑n i x' := by
      simp[SkeletonProjection] at hskel
      exact hskel.symm
    by_cases h : y' ∈ ball ⟨0, by simp⟩ 1
    · have same_cell : (⟨n_y, j_y⟩ : (n : ℕ) × cell X n) = ⟨n, i⟩ := by
        refine Topology.RelCWComplex.eq_of_not_disjoint_openCell ?_
        rw [Set.not_disjoint_iff]
        use map n i x'
        constructor
        · rw[← hY]
          apply Set.mem_image_of_mem; exact h
        · apply Set.mem_image_of_mem; exact x_ball
      rw[Sum.inr.inj_iff]
      rw [Sigma.mk.inj_iff, Fin.val_inj] at same_cell
      have hn : n_y = n := same_cell.1
      subst hn
      simp only [heq_eq_eq, true_and, Sigma.mk.injEq] at same_cell ⊢
      refine ⟨same_cell , ?_ ⟩
      rw [same_cell] at hY
      apply PartialEquiv.injOn at hY
      · exact SetCoe.ext hY
      · rw [source_eq]; exact h
      · rw [source_eq]; exact x_ball
    · have map_y'_skelLT : map n_y j_y y' ∈ (skeletonLT X n_y) := by
        apply Set.mem_of_subset_of_mem (RelCWComplex.cellFrontier_subset_skeletonLT n_y j_y)
        apply Set.mem_image_of_mem
        rw [← Metric.closedBall_sdiff_ball]
        exact ⟨y'.prop, h⟩
      have map_x'_not_skelLT : map n i x' ∉ (skeletonLT X n_y)  := by
        have le : (n_y : ℕ∞) ≤ n:= by
          rw [hnm, ← ENat.lt_coe_add_one_iff, ← Nat.cast_add_one m]
          exact ENat.coe_lt_coe.mpr  n_y.prop
        apply Disjoint.notMem_of_mem_left (disjoint_skeletonLT_openCell le).symm
        apply Set.mem_image_of_mem
        exact x_ball
      rw[hY] at map_y'_skelLT
      exact (map_x'_not_skelLT map_y'_skelLT).elim

-- brauche ich nicht
/-
lemma SkeletonProj_not_top {Y : Type*} [TopologicalSpace Y] [T2Space Y] (X : Set Y)
    {C : Set Y} [RelCWComplex X C] (m : ℕ) (y : skeletonLT X m) (hy : ¬ ( ∃ (j : cell X m),
    y.1 ∈ openCell m j)) (x : C ⊕ (Σ (n : Fin m) (_ : cell X n), (closedBall (0 : Fin n → ℝ) 1))) :
    SkeletonProjection X m x = y → Sum.elim (fun _ ↦ true) (fun p ↦ p.1 < m) x := by
  intro hxy
  simp at hy
  have : y.1 ∈ C ∨ (∃ (n : Fin m) (j : cell X n),  y.1 ∈ openCell n j) := by sorry
  --obtain ⟨ ⟩
  sorry-/

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] {X : Set Y} {C : Set Y} [RelCWComplex X C]

#check r_cube
#check r_cube_IsretractionOn
#check Set.iUnion
#check Topology.RelCWComplex.skeleton_mono
#check Topology.RelCWComplex.closedCell_subset_skeletonLT

def R_I : ℝ → unitInterval := fun p ↦
  if h : p ∈ unitInterval then ⟨p, h⟩
  else Classical.choice Zero.instNonempty

@[simp] lemma id_R_I (t : unitInterval) : R_I t.1 = t := by simp [R_I]

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

def cubesretract {m : ℕ} (n : Fin (m + 1)) :
    (closedBall (0 : Fin (n : ℕ) → ℝ) 1) × unitInterval →
    (closedBall (0 : Fin (n : ℕ) → ℝ) 1) × unitInterval := fun p ↦
  if n = m then ((r_cube (n : ℕ) (p.1,p.2)).1, R_I (r_cube (n : ℕ) (p.1,p.2)).2)
  else id p

lemma cubesretract_continuous {m : ℕ} (n : Fin (m + 1)) : Continuous (cubesretract n) := by
  unfold cubesretract
  by_cases hnm : n = m
  · simp only [hnm, ↓reduceIte, continuous_prodMk]
    refine ⟨ ?_ , ?_⟩
    · apply Continuous.comp continuous_fst ?_
      exact (r_cube_IsretractionOn n).continuousOn.comp_continuous (by fun_prop) (fun x ↦ x.2.2)
    · have hs : ∀ (x : ↑(closedBall (0 : Fin n → ℝ) 1) × ↑unitInterval),
        (fun z ↦ (r_cube ↑n (z.1, ↑z.2)).2) x ∈ unitInterval := by
        intro x
        have mapstoI: Set.MapsTo (r_cube ↑n) {p | p.2 ∈ unitInterval} {p | p.2 ∈ unitInterval}:= by
          intro x hx
          have sub : {p : (closedBall (0: Fin n → ℝ) 1) × ℝ | p.2 = 0 ∨
              p.1 ∈ sphere (⟨0, by simp⟩) 1 ∧ p.2 ∈ unitInterval} ⊆ {p | p.2 ∈ unitInterval} := by
            intro p ph
            obtain h0 | hI := ph
            · simp [h0]
            · exact hI.2
          exact sub ((r_cube_IsretractionOn n).mapsTo hx)
        apply mapstoI
        rw [Set.mem_setOf_eq]
        exact x.2.prop
      refine ContinuousOn.comp_continuous cts_R_I ?_ hs
      apply Continuous.comp continuous_snd ?_
      exact (r_cube_IsretractionOn n).continuousOn.comp_continuous (by fun_prop) (fun x ↦ x.2.2)
  · simp only [hnm, ↓reduceIte, id_eq, continuous_prodMk]
    refine ⟨ by fun_prop, by fun_prop⟩


#check r_cube
#check (r_cube_IsretractionOn 2).fixesOn

lemma cubesretract_fixedOn {m : ℕ} {n : Fin (m + 1)}
    (x : (closedBall (0 : Fin (n : ℕ) → ℝ) 1) × unitInterval) :
    (n < m → cubesretract n x = x) ∧
    (n = m → x ∈ {z | z.2 = 0 ∨ z.1 ∈ sphere ⟨0, by simp⟩ 1 } → cubesretract n x = x):= by
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
    cubesretract n = id := by
  unfold cubesretract
  simp only [h, ↓reduceIte, id_eq]
  exact Prod.id_prod

lemma cubesretract_mapsto_lt {m : ℕ} (n : Fin (m + 1)) (i : cell X n)
    (p : (closedBall 0 1) × ↑unitInterval) (hn : n < m) :
    (map n i) (cubesretract n p).1 ∈ skeletonLT X m := by
  unfold cubesretract
  have : (p.1, (p.2 : ℝ)) ∈ {p | p.2 ∈ unitInterval} := Set.mem_setOf.mpr p.2.2
  have mapsto := (r_cube_IsretractionOn n).mapsTo this
  simp only [Nat.ne_of_lt hn, ↓reduceIte, id_eq]
  apply Topology.CWComplex.skeletonLT_mono (m := n + 1) ?_ ?_
  · rw [ENat.add_one_le_iff (ENat.coe_ne_top ↑n)]
    exact ENat.coe_lt_coe.mpr hn
  · apply closedCell_subset_skeletonLT n i
    apply Set.mem_image_of_mem
    exact Subtype.coe_prop p.1

lemma cubesretract_mapsto_top {m : ℕ} (n : Fin (m + 1)) (i : cell X n)
    (p : (closedBall 0 1) × ↑unitInterval) (hn : n = m) :
    (cubesretract n p).2 = 0 ∨ (map n i) (cubesretract n p).1 ∈ skeletonLT X m := by
  unfold cubesretract
  have : (p.1, (p.2 : ℝ)) ∈ {p | p.2 ∈ unitInterval} := Set.mem_setOf.mpr p.2.2
  have mapsto := (r_cube_IsretractionOn n).mapsTo this
  simp only [hn, ↓reduceIte]
  rcases mapsto with h0 | h1
  · simp [h0, R_I]
  · right
    apply Set.Subset.trans (cellFrontier_subset_skeletonLT n i)
        (skeletonLT_mono (Std.le_of_eq (congrArg Nat.cast hn)))
    apply Set.mem_image_of_mem
    exact h1.1

lemma cubesretract_mapsto_weak {m : ℕ} (n : Fin (m + 1)) (i : cell X n)
    (p : (closedBall 0 1) × ↑unitInterval) :
    (map n i) (cubesretract n p).1 ∈ skeletonLT X (m + 1) := by
  by_cases hn : n = m
  · obtain h0 | h1 := cubesretract_mapsto_top n i p hn
    · have : (map n i) (cubesretract n p).1 ∈ skeletonLT X (n + 1) := by
        apply closedCell_subset_skeletonLT n i
        apply Set.mem_image_of_mem
        exact Subtype.coe_prop (cubesretract n p).1
      refine Set.mem_of_mem_of_subset this (skeletonLT_mono ?_)
      simp only [hn, Std.le_refl]
    · exact skeletonLT_mono le_self_add h1
  · have := cubesretract_mapsto_lt n i p (lt_of_le_of_ne (Fin.is_le n) hn)
    apply skeletonLT_mono le_self_add this

  /-
  unfold cubesretract
  have : (p.1, (p.2 : ℝ )) ∈ {p | p.2 ∈ unitInterval} := Set.mem_setOf.mpr p.2.2
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
      exact Subtype.coe_prop p.1 -/

def baseMap (m : ℕ) : C × unitInterval → ↥(skeletonLT X (m + 1)) × unitInterval := fun p ↦
  (⟨p.1 , mem_skeleton_iff.mpr (Or.inl p.1.2)⟩, p.2)

def cubeMap (m : ℕ) (n : Fin (m + 1)) (i : cell X n) :
    (closedBall (0 : Fin (n : ℕ) → ℝ) 1) × unitInterval → ↥(skeletonLT X (m + 1)) × unitInterval :=
  fun p =>
    (⟨map (n : ℕ) i (cubesretract n p).1, cubesretract_mapsto_weak n i p⟩, (cubesretract n p).2)

lemma cubeMap_cell_lt_apply {m : ℕ} (n : Fin (m + 1)) (hn : n < m) (i : cell X n)
    (x : (closedBall (0 : Fin (n : ℕ) → ℝ) 1) × unitInterval) :
    cubeMap m n i x = (SkeletonProjection X (m + 1) (Sum.inr ⟨n,i,x.1⟩), x.2) := by
  simp[cubeMap, SkeletonProjection, cubesretract, ( Nat.ne_of_lt hn)]
  rfl

def sumMap (m : ℕ) :
    (C ⊕ (Σ (n : Fin (m + 1)) (_ : cell X n), closedBall (0 : Fin n → ℝ) 1)) × unitInterval →
    skeletonLT X (m+1) × unitInterval := fun p ↦
    p.1.elim
      (fun c => baseMap m (c, p.2))
      (fun ⟨n, i, x⟩ => cubeMap m n i (x, p.2))

#check Sum.elim

-- für eine der versionen entscheiden:
lemma sumMap_C_apply (m : ℕ)
    (x : C) (t : unitInterval) :
    sumMap m (Sum.inl x, t) = (SkeletonProjection X (m + 1) (Sum.inl x), t) := by
  simp [sumMap, SkeletonProjection, baseMap]
  rfl

/-
lemma sumMap_C_apply_fun {m : ℕ} :
    ((fun p ↦ sumMap m (Sum.inl p.1, p.2))) =
    Prod.map (SkeletonProjection X (m + 1) ∘ (fun p ↦ Sum.inl p)) id := by
  simp [SkeletonProjection]
  rfl
-/

lemma sumMap_lt_sphere_apply {m : ℕ}
    (n : Fin (m + 1)) (i : cell X n) (x' : closedBall (0 : Fin n → ℝ) 1) (t : unitInterval)
    (hx : n < m ∨ n = m ∧ x' ∈ sphere ⟨0, by simp⟩ 1) :
    sumMap m (Sum.inr ⟨n, ⟨i, x'⟩⟩, t) =
    Prod.map (SkeletonProjection X (m + 1)) id (Sum.inr ⟨n, ⟨i, x'⟩⟩, t) := by
  obtain hx_lt | ⟨ hx_eq, hx_sphere⟩ := hx
  · have := cubeMap_cell_lt_apply n (Nat.lt_of_succ_le hx_lt) i (x',t)
    simp [sumMap, Sum.elim_inr, this]
  · have := (cubesretract_fixedOn (x', t)).2 hx_eq (Or.inr hx_sphere)
    simp[sumMap, cubeMap, this, SkeletonProjection]
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

lemma factors (m : ℕ) : Function.FactorsThrough (sumMap m)
    (fun p ↦ ((SkeletonProjection X (m + 1) p.1), p.2)) := by
  intro x y hxy
  rw [Prod.mk_inj] at hxy
  obtain ⟨heq1, heq2 ⟩ := hxy
  obtain ⟨cx | ⟨n, i, x'⟩, tx⟩ := x
  · rw [sumMap_C_apply, heq1]
    obtain ⟨y1, t⟩ := y
    obtain c_y | ⟨n_y, i_y, y'⟩ := y1
    · rw [← sumMap_C_apply]
      congr
    · simp only at heq2
      suffices h_nottop : ↑n_y < m ∨ ↑n_y = m ∧ y' ∈ sphere ⟨0, by simp⟩ 1 by
        rw [sumMap_lt_sphere_apply n_y i_y y' t h_nottop, heq2, Prod.map_apply, id_eq]
      by_contra h
      have top_open : n_y = m ∧ y' ∈ ball ⟨0, by simp⟩ 1 := by
        simp only [not_or, not_lt, not_and] at h
        have ny_eq_m : ↑n_y = m := Nat.le_antisymm_iff.2 ⟨Fin.is_le n_y, h.1⟩
        refine ⟨ny_eq_m , ?_ ⟩
        rw [← Metric.closedBall_sdiff_sphere]
        exact ⟨y'.prop , h.2 ny_eq_m⟩
      have h_mem : (SkeletonProjection X (m + 1) (Sum.inl cx)).1 ∈ (skeletonLT X m) := by
        apply Topology.CWComplex.skeletonLT_mono (by positivity)
        exact C_zeroskel cx
      have h_mem_false : (SkeletonProjection X (m + 1) (Sum.inr ⟨n_y, ⟨i_y, y'⟩⟩, t).1).1 ∉
          (skeletonLT X n_y) := by
        apply topopen_notLT n_y i_y y' ?_
        exact top_open.2
      simp only [top_open.1] at h_mem_false
      rw [← heq1] at h_mem_false
      exact h_mem_false h_mem
  · by_cases hnm : n < m ∨ n = m ∧ x' ∈ sphere ⟨0, by simp⟩ 1
    · simp only at heq2
      rw [sumMap_lt_sphere_apply n i x' tx hnm, Prod.map_apply, id_eq, heq1]
      obtain ⟨y1, t⟩ := y
      obtain c | ⟨n_y, i_y, y'⟩ := y1
      · rw [← sumMap_C_apply]
        congr
      · suffices h_nottop : ↑n_y < m ∨ ↑n_y = m ∧ y' ∈ sphere ⟨0, by simp⟩ 1 by
          rw [sumMap_lt_sphere_apply n_y i_y y' t h_nottop, heq2, Prod.map_apply, id_eq]
        by_contra h
        have top_open : n_y = m ∧ y' ∈ ball ⟨0, by simp⟩ 1 := by
          simp only [not_or, not_lt, not_and] at h
          have ny_eq_m : ↑n_y = m := Nat.le_antisymm_iff.2 ⟨Fin.is_le n_y, h.1⟩
          refine ⟨ny_eq_m , ?_ ⟩
          rw [← Metric.closedBall_sdiff_sphere]
          exact ⟨y'.prop , h.2 ny_eq_m⟩
        have h_mem : (SkeletonProjection X (m + 1) (Sum.inr ⟨n_y, ⟨i_y, y'⟩⟩)).1 ∈ skeletonLT X m :=
          by
          rw[← heq1, SkeletonProjection, Sum.elim_inr]
          rcases hnm with hnm | hsphere
          · have : (map (↑n) i) ↑x' ∈ (skeletonLT X (n + 1)) := by
              refine (Topology.RelCWComplex.closedCell_subset_skeletonLT n i) ?_
              apply Set.mem_image_of_mem; exact x'.prop
            refine (skeletonLT_mono ?_ ) this
            rw [ENat.add_one_le_iff (ENat.coe_ne_top ↑n)]
            exact ENat.coe_lt_coe.mpr hnm
          · simp only
            have : (map (↑n) i) ↑x' ∈ skeletonLT X n := by
              refine cellFrontier_subset_skeletonLT n i ?_
              apply Set.mem_image_of_mem; exact hsphere.2
            refine (skeletonLT_mono ?_) this
            refine ENat.coe_le_coe.mpr (Fin.is_le n)
        have h_mem_false : (SkeletonProjection X (m + 1) (Sum.inr ⟨n_y, ⟨i_y, y'⟩⟩, t).1).1 ∉
          (skeletonLT X n_y) := by
          apply topopen_notLT n_y i_y y' ?_
          exact top_open.2
        simp only [top_open.1] at h_mem_false
        exact h_mem_false h_mem
    · congr
      simp only [not_or, not_lt, not_and] at hnm
      have n_eq_m : ↑n = m :=  Eq.symm (Nat.le_antisymm hnm.1 (Fin.is_le n))
      refine (SkeletonProj_inj_top X n_eq_m i x' ?_ y.1 heq1).symm
      refine sphere_disjoint_ball.symm.notMem_of_mem_left ?_
      rw[← Metric.closedBall_sdiff_sphere]
      exact ⟨x'.prop, hnm.2 n_eq_m⟩

def r (m : ℕ) : skeletonLT X (m + 1) × unitInterval → skeletonLT X (m + 1) × unitInterval :=
  Function.extend (fun p ↦ ((SkeletonProjection X (m + 1) p.1), p.2)) (sumMap m) id

lemma r_apply (m : ℕ) (p : skeletonLT X (m + 1) × unitInterval) :
    ∃ (s : (↑C ⊕ (n : Fin (m + 1)) × (_ : cell X ↑n) × ↑(closedBall 0 1)) × ↑unitInterval),
    SkeletonProjection X (m+1) s.1 = p.1 ∧ s.2 = p.2 ∧ r m p = sumMap m s := by
  set s := Function.surjInv (SkeletonProjection_Surjective (m + 1) X) p.1
  use (s, p.2)
  have inv :  p = (SkeletonProjection X (m + 1) s, p.2) := Prod.fst_eq_iff.mp
    (Function.surjInv_eq (SkeletonProjection_Surjective (m + 1) X) p.1).symm
  refine ⟨?_ , ?_, ?_ ⟩
  · rw [Prod.ext_iff] at inv
    exact inv.1.symm
  · rfl
  · rw[inv, ← Function.FactorsThrough.extend_apply (factors m) id (s, p.2)]
    rfl

#check r_cube_IsretractionOn


-- the next two defintions and two of the four simp-lemma are written by claude (Opus 5)
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
@[simp] lemma homeoProd_inl (m : ℕ) (c : C) (t : unitInterval) :
    homeoProd (X := X) m (Sum.inl c, t) = Sum.inl (c, t) := rfl

@[simp] lemma homeoProd_inl_symm (m : ℕ) (c : C) (t : unitInterval) :
    (homeoProd (X := X) m).symm (Sum.inl (c, t)) =  (Sum.inl c, t) := rfl

@[simp] lemma homeoProd_inr (m : ℕ) (n : Fin (m + 1)) (i : cell X n)
    (x : closedBall (0 : Fin n → ℝ) 1) (t : unitInterval) :
    homeoProd (X := X) m (Sum.inr ⟨n, i, x⟩, t) = Sum.inr ⟨n, i, (x, t)⟩ := rfl

@[simp] lemma homeoProd_inr_symm (m : ℕ) (n : Fin (m + 1)) (i : cell X n)
    (x : closedBall (0 : Fin n → ℝ) 1) (t : unitInterval) :
    (homeoProd (X := X) m).symm (Sum.inr ⟨n, i, (x, t)⟩) = (Sum.inr ⟨n, i, x⟩, t) := rfl

#check Homeomorph.sumProdDistrib
#check Homeomorph.sigmaProdDistrib

lemma cts_sumMap_prehomeo (m : ℕ) : Continuous ((sumMap m) ∘ (homeoProd (X := X) m).symm)  := by
  have rww : (Sum.elim
    (fun (q : C × unitInterval) ↦ sumMap m ((Sum.inl q.1), q.2))
    (fun (q : Σ (n : Fin (m + 1)) (_ : cell X n), (closedBall (0 : Fin n → ℝ) 1 × unitInterval)) ↦
    sumMap m ((Sum.inr ⟨q.1 , ⟨q.2.1, q.2.2.1⟩⟩), q.2.2.2))) = (sumMap m) ∘ (homeoProd m).symm := by
    ext x <;>
    · obtain ⟨_ ,_ ⟩ | ⟨_ ,_ ,_ ,_ ⟩  := x
      · simp only [Sum.elim_inl, Function.comp_apply, homeoProd_inl_symm]
      · simp only [Sum.elim_inr, Function.comp_apply, homeoProd_inr_symm]
  rw[← rww]
  apply Continuous.sumElim ?_ ?_
  · simp only [sumMap, baseMap, Sum.elim_inl, continuous_prodMk]
    refine ⟨by fun_prop , continuous_snd⟩
  · simp only [sumMap, Sum.elim_inr, Prod.mk.eta, continuous_sigma_iff]
    intro n i
    simp only [cubeMap, continuous_prodMk]
    constructor
    · refine Continuous.subtype_mk ?_ (cubesretract_mapsto_weak n i)
      apply (continuousOn n i).comp_continuous ?_ ?_
      · apply continuous_subtype_val.comp
        exact continuous_fst.comp (cubesretract_continuous n)
      · intro x
        exact Subtype.coe_prop (cubesretract n x).1
    · exact continuous_snd.comp (cubesretract_continuous n)

-- nicht benutzt:
lemma r_rw (m : ℕ) :
  sumMap m = fun q ↦ r m (SkeletonProjection X (m +1) q.1, q.2) := by
  apply funext_iff.2
  intro x
  rw [← Function.FactorsThrough.extend_apply (factors m) id x]
  rfl

lemma continuousRetract (m : ℕ) : Continuous (r (X := X) m) := by
  refine (SkeletonProjectionIsQuotientMap (m +1) X).continuous_lift_prod_left ?_
  have cts_sumMap : Continuous (sumMap (X := X) m) :=
    (Homeomorph.comp_continuous_iff' (homeoProd m).symm).1 (cts_sumMap_prehomeo m)
  apply cts_sumMap.congr ?_
  intro x
  rw [← Function.FactorsThrough.extend_apply (factors m) id x]
  rfl

/-
r ist now almost the retraction, we need for the retraction criterion. Only we have to extend the
second coordinate onto all of ℝ and then proof, it satisfies all conditions of a retraction:
-/

def retr_skeleton (m : ℕ) : (skeletonLT X (m + 1)) × ℝ → (skeletonLT X (m + 1)) × ℝ := fun p ↦
  ((Function.comp (r (X := X) m) (Prod.map id R_I) p).1,
  Subtype.val (Function.comp (r (X := X) m) (Prod.map id R_I) p).2)

lemma skel_ctsOn (m : ℕ) : ContinuousOn (retr_skeleton (X := X) m) {p | p.2 ∈ unitInterval} := by
  unfold retr_skeleton
  have : ContinuousOn (fun p ↦ (Function.comp (r (X := X) m) (Prod.map id R_I) p))
    {p | p.2 ∈ unitInterval} := by
    apply (continuousRetract m).comp_continuousOn  ?_
    have : ContinuousOn (@id (skeletonLT X (↑m + 1))) Set.univ := continuousOn_id
    apply (this.prodMap cts_R_I).mono
    intro x hx
    exact Set.mem_prod.mpr ⟨by tauto, Set.mem_setOf.mp hx⟩
  refine ContinuousOn.prodMk ?_ ?_
  · exact continuous_fst.comp_continuousOn this
  · apply continuous_subtype_val.comp_continuousOn  ?_
    exact continuous_snd.comp_continuousOn this

lemma sumMap_mapsTo (m : ℕ) (x : (↑C ⊕ (n : Fin (m + 1)) × (_ : cell X ↑n) × ↑(closedBall 0 1)) × ↑unitInterval) :
  (sumMap m x).2 = 0 ∨ ↑(sumMap m x).1 ∈ skeletonLT X ↑m ∧ ↑(sumMap m x).2 ∈ unitInterval := by
  obtain ⟨x1, t⟩ := x
  obtain c |⟨n, i, x'⟩ := x1
  · simp only [sumMap, baseMap, Sum.elim_inl, Subtype.coe_prop, and_true]
    exact Or.inr (mem_skeletonLT_iff.mpr (Or.inl c.prop))
  · simp only [sumMap, cubeMap, Sum.elim_inr, Subtype.coe_prop, and_true]
    by_cases hn : n = m
    · exact cubesretract_mapsto_top n i (x',t) hn
    · exact Or.inr (cubesretract_mapsto_lt n i (x',t) (lt_of_le_of_ne (Fin.is_le n) hn))

lemma skel_mapsTo (m : ℕ) : Set.MapsTo (retr_skeleton m) {p | p.2 ∈ unitInterval}
  {p | p.2 = 0 ∨ p.1 ∈ (skeletonLT X (m + 1)).carrier ↓∩ ↑(skeletonLT X m) ∧ p.2 ∈ unitInterval} := by
  intro s hs
  unfold retr_skeleton
  obtain ⟨x, hxproj1, _ , hxsum⟩ := r_apply (X := X) m (s.1, ⟨s.2, hs⟩)
  simp only [Set.mem_preimage, SetLike.mem_coe, Function.comp_apply, Set.mem_setOf_eq,
    Set.Icc.coe_eq_zero]
  have : (Prod.map id R_I s) = (s.1, ⟨s.2, hs⟩) := by
    refine Prod.snd_eq_iff.mp ?_
    simp only [Prod.map_snd, R_I, Set.mem_setOf.mp hs, ↓reduceDIte]
  rw[this, hxsum]
  exact sumMap_mapsTo m x

/- dieses Lemma ist sehr kurz und daher nicht nötig, aber änliche formulierungen könnten den
  darauf folgenden Beweis deutlich verkürzen

lemma fixed_C (m : ℕ) (c : C) (t : unitInterval) (ht : t = 0):
    sumMap m (Sum.inl c, t) = (SkeletonProjection X (m + 1) (Sum.inl c), t) := by
  simp[sumMap, baseMap, SkeletonProjection]
  rfl
-/

lemma skel_fixedOn (m : ℕ) : ∀ a ∈ {p | p.2 = 0 ∨ p.1 ∈ (skeletonLT X (↑m + 1)).carrier ↓∩
  ↑(skeletonLT X ↑m) ∧ p.2 ∈ unitInterval}, retr_skeleton m a = a := by
  intro s hs
  unfold retr_skeleton
  have hs2 : s.2 ∈ unitInterval := by
    rcases hs with h0 | hI
    · rw[h0]
      exact unitInterval.zero_mem
    · exact hI.2
  obtain ⟨x, hxproj1, hproj2, hxsum⟩ := r_apply (X := X) m (s.1, ⟨s.2, hs2⟩)
  have simpProd : (Prod.map id R_I s) = (s.1, ⟨s.2, hs2⟩) := by
    refine Prod.snd_eq_iff.mp ?_
    simp only [Prod.map_snd, R_I, hs2, ↓reduceDIte]
  simp only [Function.comp_apply, simpProd, hxsum]
  obtain ⟨x1, t⟩ := x
  obtain c |⟨n, i, x'⟩ := x1
  · rcases hs with h0 | h1
    · have ht : t = 0 := by simp only [h0, Set.Icc.mk_zero] at hproj2; exact hproj2
      refine Prod.ext hxproj1 ?_
      rw[ht]
      exact h0.symm
    · simp only [sumMap, baseMap, Sum.elim_inl]
      refine Prod.ext hxproj1 ?_
      apply SetCoe.ext_iff.2 hproj2
  · rcases hs with h0 | h1
    · have ht : t = 0 := by simp only [h0, Set.Icc.mk_zero] at hproj2; exact hproj2
      unfold sumMap cubeMap cubesretract
      by_cases hn : n = m
      · simp only [id_eq, Sum.elim_inr, hn, ↓reduceIte]
        have : (r_cube n (x', t)) = (x', t.1) := by
          apply (r_cube_IsretractionOn n).fixesOn (x', ↑t) ?_
          exact Or.inl (Set.Icc.coe_eq_zero.mpr ht)
        simp only [this, id_R_I]
        refine Prod.ext hxproj1 ?_
        simp only [ht, Set.Icc.coe_zero]
        exact h0.symm
      · simp only [id_eq, Sum.elim_inr, hn, ↓reduceIte]
        refine Prod.ext hxproj1 ?_
        rw [ht]
        exact h0.symm
    · unfold sumMap cubeMap cubesretract
      by_cases hn : n = m
      · simp only [id_eq, Sum.elim_inr, hn, ↓reduceIte]
        suffices h : r_cube ↑n (x', ↑t) = (x', ↑t) by
          simp only [h, id_R_I]
          simp only [SkeletonProjection, Sum.elim_inr] at hxproj1
          refine Prod.ext hxproj1 ?_
          rw [← SetCoe.ext_iff] at hproj2
          exact hproj2
        apply (r_cube_IsretractionOn n).fixesOn (x',t)
        refine Or.inr ⟨?_ ,Subtype.coe_prop t⟩
        by_contra x'notsphere
        have x'ball : x'.1 ∈ ball (0 : Fin n → ℝ ) 1 := by
          rw [← Metric.closedBall_sdiff_sphere]
          refine ⟨x'.prop , x'notsphere⟩
        have notmem: (SkeletonProjection X (m + 1) (Sum.inr ⟨n, ⟨i, x'⟩⟩)).1 ∉ (skeletonLT X m) := by
          intro h
          have disjoint : Disjoint (openCell n i) (skeletonLT X n) :=
            (Topology.RelCWComplex.disjoint_skeletonLT_openCell (by rfl)).symm
          have nottmem: ((SkeletonProjection X (m + 1) (Sum.inr ⟨n, ⟨i, x'⟩⟩))).1 ∉ skeletonLT X n := by
            apply Disjoint.notMem_of_mem_left disjoint ?_
            simp only [SkeletonProjection, Sum.elim_inr]
            apply Set.mem_image_of_mem
            exact x'ball
          have subset : (skeletonLT X m).carrier ⊆ skeletonLT X n := by
            apply skeletonLT_mono (Std.le_of_eq (congrArg Nat.cast (id (Eq.symm hn))))
          exact nottmem (subset h)
        rw[hxproj1] at notmem
        exact notmem h1.1
      · simp only [id_eq, Sum.elim_inr, hn, ↓reduceIte]
        simp only [SkeletonProjection, Sum.elim_inr] at hxproj1
        refine Prod.ext hxproj1 ?_
        rw [← SetCoe.ext_iff] at hproj2
        exact hproj2


lemma HEP_skeleton (m : ℕ) : HEP' (skeletonLT X (m + 1)).carrier (skeletonLT X m).carrier := by
/-
  apply (retraction_criterion_closed' (skeletonLT X m).carrier (skeletonLT X (m + 1))
  (Topology.RelCWComplex.skeletonLT_mono le_self_add) (skeletonLT X m).closed').mpr
  use retr_skeleton m
-/
  apply (retraction_criterion_closed (IsClosed.preimage_val (skeletonLT X ↑m).closed') ).2
  use retr_skeleton m
  constructor
  · simp only [Set.mem_preimage, Set.mem_Icc, Set.setOf_subset_setOf, Prod.forall,
    forall_eq_or_imp, Std.le_refl, zero_le_one, and_self, and_imp, imp_self, implies_true]
  · exact skel_ctsOn m
  · exact skel_mapsTo m
  · exact skel_fixedOn m


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

/-
  -- have h1 : (C ⊕ (Σ (n : Fin (m + 1)) (_ : cell X n), (closedBall (0 : Fin n → ℝ) 1)))
  --   × unitInterval ≃ₜ C × ↑unitInterval ⊕ (Σ (n : Fin (m + 1)) (_ : cell X n),
  --   (closedBall (0 : Fin n → ℝ) 1)) × ↑unitInterval := Homeomorph.sumProdDistrib
  -- have h2 : (Σ (n : Fin (m + 1)) (_ : cell X n), (closedBall (0 : Fin n → ℝ) 1)) × ↑unitInterval ≃ₜ
  --   (Σ (n : Fin (m + 1)), (Σ (_ : cell X n), (closedBall (0 : Fin n → ℝ) 1))) × ↑unitInterval := by
  --   exact Homeomorph.refl (((n : Fin (m + 1)) × (_ : cell X n) × (closedBall 0 1)) × unitInterval)
  -- have h3 : (Σ (n : Fin (m + 1)), (Σ (_ : cell X n), (closedBall (0 : Fin n → ℝ) 1)))
  --   × ↑unitInterval ≃ₜ Σ (n : Fin (m + 1)), (Σ (_ : cell X n), (closedBall (0 : Fin n → ℝ) 1))
  --   × ↑unitInterval := Homeomorph.sigmaProdDistrib
  -- have h4 : (C ⊕ (Σ (n : Fin (m + 1)) (_: cell X n), (closedBall (0 : Fin n → ℝ) 1))) × unitInterval ≃ₜ
  --   C × ↑unitInterval ⊕ (Σ (n : Fin (m + 1)), (Σ (_ : cell X n), (closedBall (0 : Fin n → ℝ) 1))) × ↑unitInterval := by
  --   apply Homeomorph.sumProdDistrib
  have h5 : (C ⊕ (Σ (n : Fin (m + 1)) (_: cell X n), (closedBall (0 : Fin n → ℝ) 1))) × unitInterval ≃ₜ
     C × ↑unitInterval ⊕ (Σ (n : Fin (m + 1)), (Σ (_ : cell X n), (closedBall (0 : Fin n → ℝ) 1))
    × ↑unitInterval ) := by
    apply Homeomorph.trans Homeomorph.sumProdDistrib ?_
    apply Homeomorph.sumCongr (Homeomorph.refl _ ) Homeomorph.sigmaProdDistrib
  have h6 (n : Fin (m+1)) : (Σ (_ : cell X n), (closedBall (0 : Fin n → ℝ) 1)) × unitInterval ≃ₜ
    Σ (_ : cell X n), (closedBall (0 : Fin n → ℝ) 1) × unitInterval := Homeomorph.sigmaProdDistrib
  have h7 : (C ⊕ (Σ (n : Fin (m + 1)) (_: cell X n), (closedBall (0 : Fin n → ℝ) 1))) × unitInterval ≃ₜ
    C × ↑unitInterval ⊕ (Σ (n : Fin (m + 1)), Σ (_ : cell X n), ((closedBall (0 : Fin n → ℝ) 1) × unitInterval)) := by
    apply Homeomorph.trans h5 ?_
    apply Homeomorph.sumCongr (Homeomorph.refl _) ?_

    sorry

-/
