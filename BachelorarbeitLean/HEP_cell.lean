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


open Metric
open Set.Notation
open Topology
open RelCWComplex

noncomputable section

variable {Y : Type*} [TopologicalSpace Y] {X C : Set Y} [RelCWComplex X C]
  (A : Subcomplex X)

def r_cube (m : ℕ) : (closedBall (0 : Fin m → ℝ) 1) × ℝ → (closedBall (0 : Fin m → ℝ) 1) × ℝ :=
  Exists.choose ((retraction_criterion_closed isClosed_sphere).1
  (HEP_cube_boundary m ))

lemma r_cube_IsretractionOn (m : ℕ) : RetractionOn (r_cube m) {p | p.2 ∈ unitInterval}
    {p | p.2 = 0 ∨ p.1.1 ∈ sphere 0 1 ∧ p.2 ∈ unitInterval} :=
  Exists.choose_spec ((retraction_criterion_closed isClosed_sphere).1
  (HEP_cube_boundary m))

-- universal property of the quotient:
#check Topology.IsQuotientMap.lift
-- wann ist etwas im CW complex closed:
#check RelCWComplex.closed


def QuotMap {m : ℕ} (i : cell X m) : closedBall (0 : Fin m → ℝ) 1 →
  closedCell m i :=
  Set.MapsTo.restrict (map m i) (closedBall 0 1)
    (closedCell m i) (Set.mapsTo_image (map m i) (closedBall 0 1))

lemma QuotMap_isClosedMap {m : ℕ} [T2Space Y] (i : cell X m) : IsClosedMap (QuotMap i) :=
  Continuous.isClosedMap (ContinuousOn.mapsToRestrict (continuousOn m i) _ )

--lemma RestrictMap_Continuous (i : cell X m) : Continuous (RestrictMap X C i) :=
  --ContinuousOn.mapsToRestrict (continuousOn m i) _

lemma QuotMap_isQuotient {m : ℕ} (i : cell X m) [T2Space Y] : IsQuotientMap (QuotMap i) := by
  have Restrict_Surj : Function.Surjective (QuotMap i) :=
            (Set.MapsTo.restrict_surjective_iff (QuotMap._proof_1 i)).mpr (fun a a_1 ↦ a_1)
  constructor
  · sorry --exact Restrict_Surj
  · sorry -- seit Mathlib update
    /-
    refine Eq.symm ((fun {X} {t₁ t₂} ↦ TopologicalSpace.ext_iff_isClosed.mpr) ?_)
    intro S
    constructor
    · intro hs_map
      rw[isClosed_coinduced] at hs_map
      rw [isClosed_induced_iff]
      use Subtype.val ∘ (QuotMap i) '' (QuotMap  i ⁻¹' S)
      constructor
      · rw[RelCWComplex.closed X _ ?_ ]
        · constructor
          · intro n j
            refine IsClosed.inter ?_ (isClosed_closedCell)
            have : IsClosedMap (Subtype.val ∘ QuotMap i) := by
              refine IsClosedMap.comp ?_ (by exact QuotMap_isClosedMap i)
              exact IsClosed.isClosedMap_subtype_val isClosed_closedCell
            exact this (QuotMap i ⁻¹' S) hs_map
          · refine IsClosed.inter ?_ (by exact isClosedBase X)
            have : IsClosedMap (Subtype.val ∘ QuotMap i) := by
              refine IsClosedMap.comp ?_ (QuotMap_isClosedMap i)
              exact IsClosed.isClosedMap_subtype_val isClosed_closedCell
            exact isClosed_coinduced.mpr (this (QuotMap i ⁻¹' S) hs_map)
        · refine Set.MapsTo.image_subset (Set.MapsTo.comp_right ?_ (QuotMap i))
          rw [Set.mapsTo_iff_subset_preimage,
            Set.preimage_val_eq_univ_of_subset (closedCell_subset_complex m i)]
          tauto
      · ext s
        constructor
        · intro hs
          rw [Set.image_comp Subtype.val (QuotMap i) (QuotMap i ⁻¹' S),
            Set.image_preimage_eq_range_inter, Set.image_val_inter] at hs
          have := hs.2
          simp only [Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
            Subtype.coe_eta, Subtype.coe_prop, exists_const] at this
          exact this
        · intro hs
          simp only [Set.mem_preimage, Set.mem_image]
          use Function.surjInv Restrict_Surj s
          simp only [Function.surjInv_eq Restrict_Surj, Function.comp_apply, and_true]
          exact hs
    · -- wenn im CW-complex closed, dann auch in der coinduced topology
      intro hs
      refine isClosed_coinduced.mpr ?_
      refine IsClosed.preimage ?_ hs
      exact (ContinuousOn.mapsToRestrict (continuousOn m i) _ )
-/
def RetractBall {m : ℕ} (i : cell X m):
    C(closedBall (0 : Fin m → ℝ) 1 × unitInterval , closedCell m i × ℝ ) where
  toFun := fun (p,t) ↦
    (⟨map m i (r_cube m (p,t)).1, Set.mem_image_of_mem (map m i)
    (Subtype.coe_prop (r_cube m (p, t)).1)⟩,
    (r_cube m (p,t)).2)
  continuous_toFun := by
    rw [continuous_prodMk]
    constructor
    · apply Continuous.subtype_mk
      apply ContinuousOn.comp_continuous (RelCWComplex.continuousOn m i)
      · apply continuous_subtype_val.comp
        apply continuous_fst.comp ((r_cube_IsretractionOn m).continuousOn.comp_continuous
          (by fun_prop) (fun x ↦ x.2.2))
      · intro (x,t)
        simp only [Subtype.coe_prop]
    · exact continuous_snd.comp ((r_cube_IsretractionOn m).continuousOn.comp_continuous
        (by fun_prop) (fun x ↦ x.2.2))

/- Beweis irgendwann später: -/
-- Stetigkeit - gibt es schon :
#check Topology.IsQuotientMap.continuous_lift_prod_left

lemma QuotientProductIdentityOnLocallyCompact {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {f : X → Y} (hf : IsQuotientMap f) (hZ : LocallyCompactSpace Z) :
    IsQuotientMap (Prod.map f (@id Z)) := by
  sorry





def C_QuotMapProd {m : ℕ} (i : cell X m) :
  C(closedBall (0 : Fin m → ℝ) 1 × unitInterval , closedCell m i × unitInterval) where
    toFun := (Prod.map (QuotMap i) id)
    continuous_toFun := (ContinuousOn.mapsToRestrict (continuousOn m i) _).prodMap continuous_id

lemma quotient_QuotMapProd {m : ℕ} (i : cell X m) [T2Space Y] :
    IsQuotientMap (C_QuotMapProd i) :=
  QuotientProductIdentityOnLocallyCompact (QuotMap_isQuotient i)
    (WeaklyLocallyCompactSpace.locallyCompactSpace)

-- für Mathlib interessant?
#check Topology.RelCWComplex.cellFrontier_subset_finite_openCell
#check Topology.RelCWComplex.disjoint_openCell_of_ne
#check Topology.RelCWComplex.disjointBase

lemma DisjointCellFrontierOpenCell [T2Space Y] (n : ℕ) (i : cell X n) :
    Disjoint (cellFrontier n i)  (openCell n i) := by
  obtain ⟨I, hI⟩ := cellFrontier_subset_finite_openCell n i
  suffices h : Disjoint ( C ∪ ⋃ m, ⋃ (_ : m < n), ⋃ j ∈ I m, openCell m j) (openCell n i) by
    exact Set.disjoint_of_subset_left hI h
  refine Set.disjoint_union_left.mpr ⟨Disjoint.symm (disjointBase n i), ?_⟩
  rw [Set.disjoint_iUnion₂_left]
  intro m hm
  refine Set.disjoint_iUnion₂_left.mpr ?_
  intro j hj
  refine Topology.RelCWComplex.disjoint_openCell_of_ne ?_
  rw [ne_eq, Sigma.mk.injEq, not_and_or]
  left
  exact Nat.ne_of_lt hm

lemma CellFrontierEqClosedWithoutOpen [T2Space Y] (n : ℕ) (i : cell X n) :
    cellFrontier n i = (closedCell n i \ openCell n i) := by
  refine Eq.symm (Set.eq_of_subset_of_subset ?_ ?_)
  · apply Set.sdiff_subset_iff.2
    rw [Set.union_comm (openCell n i) (cellFrontier n i)]
    exact subset_of_eq (Topology.RelCWComplex.cellFrontier_union_openCell_eq_closedCell n i).symm
  · exact Set.subset_sdiff.mpr
      ⟨ cellFrontier_subset_closedCell n i , DisjointCellFrontierOpenCell n i ⟩

lemma RetractBallFactors {m : ℕ} [T2Space Y] (i : cell X m) :
    Function.FactorsThrough (RetractBall i) (C_QuotMapProd i):= by
  intro x y heq
  simp only [Prod.ext_iff] at heq
  obtain ⟨heq1, heq2⟩ := heq
  simp only [C_QuotMapProd, ContinuousMap.coe_mk, Prod.map_fst, Prod.map_snd, id_eq] at heq2 heq1
  have heq1: map m i x.1 = map m i y.1 := by
    unfold QuotMap at heq1
    have : Set.MapsTo (map m i) (closedBall 0 1) (closedCell m i) := by
     exact Set.mapsTo_iff_image_subset.mpr fun ⦃a⦄ a_1 ↦ a_1
    have := Set.MapsTo.val_restrict_apply (this)
    rw[← this x.1, ← this y.1]
    exact Subtype.ext_iff.mp heq1
  by_cases h1 : x.1.1 ∈ ball 0 1
  · suffices x.1 = y.1 by simp[Prod.ext this heq2]
    have mapInj :=  PartialEquiv.injOn (map m i)
    have xx: x.1.1 ∈ (map m i).source := by
      rw [source_eq m i]
      exact h1
    have yy: y.1.1 ∈ (map m i).source := by
      rw [source_eq m i, ← closedBall_sdiff_sphere]
      refine ⟨y.1.2, ?_ ⟩
      by_contra
      suffices yball : (map m i) y.1.1 ∈ openCell m i by
        have yfront : map m i y.1.1 ∈ cellFrontier m i := by use y.1.1
        exact Disjoint.notMem_of_mem_left (DisjointCellFrontierOpenCell m i) yfront yball
      rw[← heq1]
      use x.1.1
    exact SetCoe.ext (mapInj xx yy heq1)
  · have x1sphere: x.1.1 ∈ sphere 0 1 := by
      rw[← Metric.closedBall_sdiff_ball]
      exact ⟨x.1.2, h1⟩
    simp only [RetractBall, ContinuousMap.coe_mk, Prod.mk.injEq, Subtype.mk.injEq]
    suffices r_id : r_cube m (x.1, x.2.1) = (x.1, x.2.1) ∧ r_cube m (y.1, y.2.1) = (y.1, y.2.1) by
      simp only [r_id]
      exact ⟨heq1, congrArg Subtype.val heq2⟩
    have r_idx := (r_cube_IsretractionOn m).fixesOn (x.1,x.2) (by
      rw[ Set.mem_setOf_eq]
      right
      exact ⟨mem_sphere.mpr x1sphere , Subtype.coe_prop x.2 ⟩)
    have r_idy := (r_cube_IsretractionOn m).fixesOn (y.1,y.2) (by
      rw[ Set.mem_setOf_eq]
      right
      refine ⟨ ?_ , Subtype.coe_prop y.2 ⟩
      by_contra
      suffices yfront : (map m i) y.1.1 ∈ cellFrontier m i by
        have yopen: map m i y.1.1 ∈ openCell m i := by
          have yball : y.1.1 ∈ ball 0 1 := by
            rw[← Metric.closedBall_sdiff_sphere]
            refine ⟨y.1.2,?_ ⟩
            intro h
            exact Ne.elim this h
          use y.1
        exact Disjoint.notMem_of_mem_left (DisjointCellFrontierOpenCell m i) yfront yopen
      rw[← heq1]
      use x.1.1)
    rw[r_idx, r_idy]
    exact Prod.mk_inj.mp rfl

def RetractCellInt_Fun {m : ℕ} [T2Space Y] (i : cell X m) (hm : 0 < m) :
  C(closedCell m i × unitInterval, closedCell m i × ℝ) :=
  (quotient_QuotMapProd i).lift (RetractBall i ) (RetractBallFactors i )

lemma RetractCellInt_range {m : ℕ} [T2Space Y] (i : cell X m) (hm : 0 < m) :
    Set.range (RetractCellInt_Fun i hm) ⊆
    {(p,t) : closedCell m i × ℝ | t = 0 ∨ (p : Y) ∈ cellFrontier m i ∧
      t ∈ unitInterval} := by
  unfold RetractCellInt_Fun
  rw [CellFrontierEqClosedWithoutOpen m i]
  intro x hx
  obtain ⟨y, hy⟩ := hx
  have := (Topology.IsQuotientMap.lift_apply (quotient_QuotMapProd i) (RetractBall i )
    (RetractBallFactors i )) y
  rw[hy] at this
  simp only [Function.comp_apply, IsQuotientMap.homeomorph_symm_apply, Quotient.liftOn'_mk'',
    IsQuotientMap.lift_apply] at this hy
  suffices Mapsto_gprod : Set.MapsTo (RetractBall i ) ⊤ {(p,t) : closedCell m i × ℝ | t = 0 ∨
      (p : Y) ∈ (closedCell m i \ openCell m i) ∧ t ∈ unitInterval} by
    exact Set.mem_of_eq_of_mem this (Mapsto_gprod trivial)
  intro z hz
  unfold RetractBall
  simp only [Set.mem_sdiff, Subtype.coe_prop, true_and, ContinuousMap.coe_mk,
    Set.mem_setOf_eq]
  by_cases h : ((r_cube m) (z.1, z.2)).2 = 0
  · simp [h]
  · have : (r_cube m) (z.1, z.2) ∈ {p | p.1 ∈ (sphere ⟨ 0, by simp⟩  1) ∧ p.2 ∈ unitInterval} := by
      have mem : (z.1, z.2.1) ∈ {p : (closedBall 0 1) × ℝ | p.2 ∈ unitInterval } := by
        rw [Set.mem_setOf_eq]
        exact Subtype.coe_prop z.2
      have := (r_cube_IsretractionOn m).mapsTo mem
      simp only [mem_sphere, Set.mem_Icc, Set.mem_setOf_eq, h, false_or] at this
      exact this
    right
    constructor
    · suffices h : (map m i) (r_cube m (z.1, ↑z.2)).1 ∈ cellFrontier m i  by
        exact Disjoint.notMem_of_mem_left (DisjointCellFrontierOpenCell m i) h
      rw [Set.mem_setOf] at this
      apply Set.mem_image_of_mem
      exact mem_sphere.mpr this.1
    · rw [Set.mem_setOf_eq] at this
      exact this.2

lemma RetractCellInt_fixesOn {m : ℕ} [T2Space Y] (i : cell X m) (hm : 0 < m) :
    ∀ x : closedCell m i × unitInterval, x ∈ {p | p.2 = 0 ∨ p.1 ∈ cellFrontier m i} →
    (RetractCellInt_Fun i hm) x = (x.1, x.2.1) := by
  intro x hx
  have C_ProdSurj := IsQuotientMap.homeomorph._proof_1 (quotient_QuotMapProd i)
  have QuotientApply := (Topology.IsQuotientMap.lift_apply (quotient_QuotMapProd i)
    (RetractBall i ) (RetractBallFactors i )) x
  unfold RetractCellInt_Fun
  rw[QuotientApply]
  simp only [Function.comp_apply, IsQuotientMap.homeomorph_symm_apply, Quotient.liftOn'_mk'']
  have mapeqC_Prod : ∀ (y : (closedBall 0 1) × unitInterval ), (map m i ) y.1 =
        ((C_QuotMapProd i) y).1 := by
      intro y
      simp [C_QuotMapProd, QuotMap]
  have id2 : (Function.surjInv C_ProdSurj x).2 = x.2 := by
      have : ∀ (y : (closedBall 0 1) × unitInterval), ((C_QuotMapProd i) y ).2 = y.2 := by
        simp [C_QuotMapProd]
      have := this (Function.surjInv C_ProdSurj x)
      rw[← this, Function.surjInv_eq C_ProdSurj x]
  by_cases h : x.2 = 0
  · rw [Prod.ext_iff, h, Set.Icc.coe_zero]
    rw [h] at id2
    constructor
    · simp only [RetractBall, ContinuousMap.coe_mk, id2, Set.Icc.coe_zero,
        (r_cube_IsretractionOn m).fixesOn ((Function.surjInv C_ProdSurj x).1, 0) (by simp),
        mapeqC_Prod, Subtype.coe_eta]
      specialize mapeqC_Prod (Function.surjInv C_ProdSurj x)
      exact SetCoe.ext (congrArg Subtype.val (congrArg Prod.fst (Function.surjInv_eq
        C_ProdSurj x)))
    · suffices h1 :(Function.surjInv C_ProdSurj x).2 = 0 by
        simp only [RetractBall, ContinuousMap.coe_mk, h1]
        have r_id := (r_cube_IsretractionOn m).fixesOn ((Function.surjInv
          (IsQuotientMap.homeomorph._proof_1 (quotient_QuotMapProd i)) x).1, 0) (by simp)
        rw [Prod.ext_iff] at r_id
        exact r_id.2
      exact id2
  · have hx1 : x.1.1 ∈ cellFrontier m i := by
      simp [h] at hx
      simp [hx]
    have : (Function.surjInv C_ProdSurj x).1.1 ∈ sphere (0 : Fin m → ℝ) 1 := by
      by_contra notsphere
      have xball : (Function.surjInv C_ProdSurj x).1 ∈ ball ⟨0, by simp⟩  1 := by
        rw[← Metric.closedBall_sdiff_sphere]
        refine ⟨mem_closedBall.mpr (Function.surjInv (IsQuotientMap.homeomorph._proof_1
          (quotient_QuotMapProd i)) x).1.2, ?_ ⟩
        intro hs
        exact Ne.elim notsphere hs
      have xopenCell := Set.mem_image_of_mem (QuotMap i) xball
      have surjInv : QuotMap i (Function.surjInv C_ProdSurj x).1 = x.1 := by
        have := Function.surjInv_eq C_ProdSurj x
        rw [Prod.ext_iff] at this
        exact this.1
      rw[surjInv] at xopenCell
      have xopenCell := Set.mem_image_of_mem (Subtype.val) xopenCell
      have : QuotMap i '' (ball ⟨(0 : (Fin m → ℝ)), by simp⟩ 1) ≤ openCell m i := by
        refine Set.le_iff_subset.mpr ?_
        rw [Set.image_subset_iff, Set.image_subset_iff]
        intro y hy
        rw [Set.mem_preimage]
        exact Set.mem_image_of_mem (map m i) hy
      exact Disjoint.notMem_of_mem_left (DisjointCellFrontierOpenCell m i) hx1
        (Set.mem_of_mem_of_subset xopenCell this )
    have r_id := (r_cube_IsretractionOn m).fixesOn
      ((Function.surjInv (IsQuotientMap.homeomorph._proof_1 (quotient_QuotMapProd i)) x).1,
      (Function.surjInv (IsQuotientMap.homeomorph._proof_1 (quotient_QuotMapProd i)) x).2) (by
      simp only [Set.mem_setOf, Set.Icc.coe_eq_zero, Subtype.coe_prop, and_true]
      right
      exact mem_sphere.mpr this)
    refine Prod.ext_iff.mpr ?_
    constructor
    · specialize mapeqC_Prod (Function.surjInv (IsQuotientMap.homeomorph._proof_1
        (quotient_QuotMapProd i)) x)
      simp only [RetractBall, ContinuousMap.coe_mk, r_id, mapeqC_Prod, Subtype.coe_eta]
      exact SetCoe.ext (congrArg Subtype.val (congrArg Prod.fst (Function.surjInv_eq
        (IsQuotientMap.homeomorph._proof_1 (quotient_QuotMapProd i)) x)))
    · simp only [RetractBall, ContinuousMap.coe_mk, r_id, mapeqC_Prod, Subtype.coe_eta]
      exact Subtype.ext_iff.mp id2

lemma nonemptyFront {m : ℕ} (hm : 0 < m) (j : cell X m) :  Nonempty ↑(closedCell m j ↓∩
    cellFrontier m j) := by
  have := (@NormedSpace.sphere_nonempty (Fin m → ℝ) _ _ ?_ 0 1).2 zero_le_one
  · simp only [nonempty_subtype, Set.mem_preimage, Subtype.exists, exists_prop]
    rw [show cellFrontier m j = ↑(map m j) '' sphere 0 1 from rfl]
    obtain ⟨a, ha⟩ := this
    refine exists_exists_and_eq_and.mp ?_
    use ((map m j) a)
    refine ⟨?_ , Set.mem_image_of_mem (↑(map m j)) ha ⟩
    simp only [↓existsAndEq, and_true]
    rw [show closedCell m j = ↑(map m j) '' closedBall 0 1 from rfl]
    refine Set.mem_image_of_mem ↑(map m j) ?_
    exact Metric.sphere_subset_closedBall ha
  · refine nontrivialTopology_iff_exists_norm_ne_zero.mpr ?_
    simp only [ne_eq, norm_eq_zero]
    use Pi.single ⟨0, hm⟩ 1
    exact Function.ne_iff.mpr ⟨⟨0, hm⟩, by simp⟩


lemma HEP_Cell [T2Space Y] {m : ℕ} (hm : 0 < m) (j : cell X m) :
    HEP' (closedCell m j) (cellFrontier m j) := by
  apply (retraction_criterion_closed (IsClosed.preimage_val isClosed_cellFrontier)).2
  let r : (closedCell m j) × ℝ → (closedCell m j) × ℝ := fun (x,t) ↦
    if ht : t ∈ unitInterval then RetractCellInt_Fun j hm (x, ⟨t, ht⟩)
    else (x,0)
  use r
  refine ⟨?_, ?_ , ?_ , ?_⟩
  · sorry
  · simp only [r]
    apply ContinuousOn.congr (f := fun x ↦ (RetractCellInt_Fun j hm) (x.1, Set.projIcc 0 1
      zero_le_one x.2))
    · apply Continuous.continuousOn
      fun_prop
    · intro x hx
      simp only [Set.mem_setOf_eq] at hx
      dsimp only
      rw [dif_pos hx, Set.projIcc_of_mem _ hx]
  · simp only [Set.mem_preimage]
    intro ⟨x,t⟩ ht
    simp only [Set.mem_setOf_eq] at ht
    have : (RetractCellInt_Fun j hm) (x, ⟨t, ht⟩)  = r (x, t) := by
      simp only [ r, ht, dite_true]
    rw[← this]
    have range := RetractCellInt_range j hm
    rw [Set.range_subset_iff] at range
    exact range (x, ⟨t,ht⟩)
  · intro a ha
    have ha2 : a.2 ∈ unitInterval := by
      rcases ha with h0 | hi
      · rw[h0]
        exact unitInterval.zero_mem
      · exact hi.2
    have : (RetractCellInt_Fun j hm) (a.1, ⟨a.2, ha2⟩)  = r a := by
      simp only [ r, ha2, dite_true]
    rw[← this]
    apply RetractCellInt_fixesOn j hm (a.1, ⟨a.2, ha2⟩)
    rcases ha with h0 | hi
    · left
      exact Eq.symm (SetCoe.ext (id (Eq.symm h0)))
    · right
      rw [Set.mem_preimage] at hi
      exact hi.1

def r_cell [T2Space Y] {m : ℕ} (hm : 0 < m) (j : cell X m) :=
  Exists.choose ((retraction_criterion_closed (IsClosed.preimage_val isClosed_cellFrontier)).1
  (HEP_Cell hm j))

lemma r_cell_IsretractionOn [T2Space Y] {m : ℕ} (hm : 0 < m) (j : cell X m) :
    RetractionOn (r_cell hm j) {p | p.2 ∈ unitInterval}
    {p | p.2 = 0 ∨ p.1.1 ∈ cellFrontier m j ∧ p.2 ∈ unitInterval} :=
  Exists.choose_spec ((retraction_criterion_closed (IsClosed.preimage_val isClosed_cellFrontier)).1
  (HEP_Cell hm j))


lemma uniqueOpenCell {m : ℕ} (p : Y) (hi : ∃ (i : cell X m), p ∈ openCell m i) :
  ∃! (i : cell X m), p ∈ openCell m i := by
  refine existsUnique_of_exists_of_unique hi ?_
  intro y1 y2 hp1 hp2
  by_contra
  have notDisj: ¬ Disjoint (openCell m y1) (openCell m y2) := by
    refine Set.not_disjoint_iff.mpr (by use p)
  refine notDisj (Topology.RelCWComplex.disjoint_openCell_of_ne ?_)
  simp [this]



/-
für den Versuch es über Function.extend zu machen, aber ich glaube das ist umständlicher -/

def f {m : ℕ} (hm : 0 < m) : ⋃ (j : cell X m), openCell m j × ℝ → X × ℝ := fun p ↦
  ( ⟨ p.1.1, by sorry ⟩ , p.2)

def gg {m : ℕ} (hm : 0 < m) : ⋃ (j : cell X m), openCell m j × ℝ → X × ℝ := by
  intro ⟨⟨ x , hx⟩ ,t⟩
  rw [Set.mem_iUnion] at hx
  let i := hx.choose
  sorry

def j : X × ℝ → X × ℝ := id



open Classical in
def r_dimCW' {m : ℕ} [T2Space Y] (hm : 0 < m) : X × ℝ → X × ℝ := fun (p,t) ↦
  if hi : (∃ i : cell X m, (p : Y) ∈ openCell m i) ∧ t ∈ unitInterval then
    let i : cell X m := hi.1.choose
    let hi_i : (p : Y) ∈ openCell m i := hi.1.choose_spec
    let p_mem := ⟨p, Set.mem_of_mem_of_subset hi_i (openCell_subset_closedCell m i)⟩
    let val := RetractCellInt_Fun i hm (p_mem, ⟨t, hi.2⟩)
    (⟨val.1, closedCell_subset_complex m i (Subtype.coe_prop val.1)⟩, val.2)
  else (p, t)

open Classical in
def r_dimCW {m : ℕ} [T2Space Y] (hm : 0 < m) : X × ℝ → X × ℝ := fun (p,t) ↦
  if hi : (∃ i : cell X m, (p : Y) ∈ openCell m i)  then
    let i : cell X m := hi.choose
    let hi_i : (p : Y) ∈ openCell m i := hi.choose_spec
    let p_mem := ⟨p, Set.mem_of_mem_of_subset hi_i (openCell_subset_closedCell m i)⟩
    let val := r_cell hm i (p_mem, t)
    (⟨val.1, closedCell_subset_complex m i (Subtype.coe_prop val.1)⟩, val.2)
  else (p, t)

lemma r_dimCW_applyCell {m : ℕ} [T2Space Y] (hm : 0 < m) (i : cell X m)
    (p : X) (hp : (p : Y) ∈ closedCell m i) (t : ℝ) (ht : t ∈ unitInterval) :
    r_dimCW hm (p, t) = (⟨ (r_cell hm i (⟨p, hp ⟩, t)).1.1 , by
      suffices h : ((r_cell hm i (⟨p, hp ⟩, t)).1 : Y ) ∈ closedCell m i by
        exact Topology.RelCWComplex.closedCell_subset_complex m i h
      exact Subtype.coe_prop (r_cell hm i (⟨↑p, hp⟩, t)).1
      ⟩ , (r_cell hm i (⟨p, hp ⟩, t)).2) := by
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
        rw [CellFrontierEqClosedWithoutOpen m i] --!
        exact Set.mem_sdiff_of_mem hp h
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
      rw [CellFrontierEqClosedWithoutOpen m i]
      exact Set.mem_sdiff_of_mem hp h
    exact (r_cell_IsretractionOn hm i ).4 _ fixmem

lemma r_dimCW_applyA {m : ℕ} [T2Space Y] (hm : 0 < m) (p : X) (hp : (p : Y) ∈ A) (t : ℝ) :
    r_dimCW hm (p, t) = (p,t) := by
  unfold r_dimCW

  sorry








--def r_dimCW' {m : ℕ} [T2Space Y] (hm : 0 < m) : X × ℝ → X × ℝ := Function.extend


#check Function.extend
#check ContinuousOn.union_of_isClosed

lemma r_dimCW_ContOn {m : ℕ} [T2Space Y] (hm : 0 < m) (hX : X = ↑A ∪ ⋃ (j : cell X m), openCell m j)
    (hA : Nonempty (X ↓∩ ↑A)) : ContinuousOn (r_dimCW hm) {p : X × ℝ | p.2 ∈ unitInterval} := by
  --apply ContinuousOn.if
  have union : {p : X × ℝ | p.2 ∈ unitInterval} = {p | p.1 ∈ A ∧ p.2 ∈ unitInterval} ∪
      closure {p | p.1 ∈ (⋃ (j : cell X m), openCell m j) ∧ p.2 ∈ unitInterval} := by
    sorry
  rw[union]
  apply ContinuousOn.union_of_isClosed ?_ ?_ ?_ isClosed_closure
  · sorry
  · sorry
  · have : {p : X × ℝ | p.1.1 ∈ A ∧ p.2 ∈ unitInterval} = {p : X | p.1 ∈ A } ×ˢ
        {p : ℝ | p ∈ unitInterval} := by
      ext x
      simp
    rw[this]
    refine IsClosed.prod ?_ isClosed_Icc
    rw [isClosed_induced_iff]
    use A.carrier
    exact ⟨A.closed' , Set.image_val_inj.mp rfl ⟩

    /-
    -- ohne IsClosed.and geht es deutlich schneller
    · have : {x : X × ℝ | ↑x.1 ∈ ⋃ (j : cell X m), closedCell m j} =
          {x : X | (x : Y) ∈ ⋃ (j : cell X m), closedCell m j} ×ˢ {x : ℝ | x ∈ Set.univ } := by
        have : {x : X × ℝ | ↑x.1 ∈ ⋃ (j : cell X m), closedCell m j} = {x : X × ℝ | ↑x.1 ∈ ⋃
            (j : cell X m), closedCell m j ∧ x.2 ∈ Set.univ} := by simp
        rw [this]
        ext x
        simp
      rw[this]
      refine IsClosed.prod ?_ (by simp)
      have : {x | ↑x ∈ ⋃ (j : cell X m), closedCell m j} ⊆ X := by sorry
      --apply Topology.RelCWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell
      apply (IsClosed.inter_preimage_val_iff isClosed).2
      --apply RelCWComplex.isClosed
      sorry
/-
      refine LocallyFinite.isClosed_iUnion ?_ ?_
      · sorry
      · intro i
        exact isClosed_closedCell-/
    · have : {x : X × ℝ | x.2 ∈ unitInterval} = {x : X | x ∈ Set.univ } ×ˢ
          {x : ℝ | x ∈ unitInterval} := by
        rw [show {x : X × ℝ | x.2 ∈ unitInterval} = {x | x.1 ∈ Set.univ ∧ x.2 ∈ unitInterval} from
          Eq.symm Set.sep_univ]
        ext x
        simp
      rw[this]
      refine IsClosed.prod (by simp) isClosed_Icc -/






lemma HEP_Dim {m : ℕ} [T2Space Y] (hm : 0 < m) (hX : X = ↑A ∪ ⋃ (j : cell X m), openCell m j)
    (hA : Nonempty (X ↓∩ ↑A)) : HEP' X A := by
  apply (retraction_criterion_closed  ((Subcomplex.closed A).preimage_val)).2
  use r_dimCW hm
  refine ⟨?_, ?_ , ?_ , ?_⟩
  · intro x hx
    simp only [Set.mem_setOf_eq]
    obtain h1 | h2 := hx
    · rw[h1]
      exact unitInterval.zero_mem
    · exact h2.2
  · exact r_dimCW_ContOn ↑A hm hX hA
  · intro (x,t) ht
    simp only [Set.mem_setOf_eq] at ht
    by_cases hcell : (∃ i : cell X m, (x : Y) ∈ openCell m i)
    · simp only [Set.mem_preimage, SetLike.mem_coe, r_dimCW, hcell, ↓reduceDIte]
      obtain ⟨i, hi⟩ := hcell
      have : {(p, t) : X × ℝ | t = 0 ∨ ↑p ∈ cellFrontier m i ∧ t ∈ unitInterval} ⊆
        {p | p.2 = 0 ∨ p.1.1 ∈ A ∧ p.2 ∈ unitInterval} := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ⊢ ha
        rcases ha with  ha | ha
        · (expose_names; exact Or.symm (Or.inr ha))
        · right
          refine ⟨?_ , ha.2⟩
          have a_memUnion :  ↑a.1 ∈ ↑A ∪ ⋃ (j : cell X m), openCell m j := by
            rw[← hX]
            exact Set.mem_preimage.mp ((cellFrontier_subset_complex m i) ha.1)
          suffices h:  ↑a.1 ∉ ⋃ (j : cell X m), openCell m j by
            simp only [Set.mem_union, SetLike.mem_coe, h, or_false] at a_memUnion
            exact a_memUnion
          intro hopen
          rw [Set.mem_iUnion] at hopen
          obtain ⟨j, hj⟩ := hopen
          have front_in_skel := cellFrontier_subset_skeletonLT m i
          have : (m : ℕ∞ ) ≤ m := by simp
          exact (Disjoint.notMem_of_mem_right (disjoint_skeletonLT_openCell this) hj)
            (front_in_skel ha.1)
      refine Set.mem_of_subset_of_mem this ?_
      have xmem: (x : Y) ∈ closedCell m i := (openCell_subset_closedCell m i) hi
      have r_range := RetractCellInt_range i hm
      rw [← Set.mapsTo_univ_iff_range_subset, Set.mapsTo_univ_iff] at r_range
      specialize r_range (⟨x, xmem ⟩,⟨t, ht⟩)
      simp only [ Set.mem_setOf_eq] at ⊢ r_range
      rcases r_range with hr | hr
      · left
        --let z := (r_dimCW._proof_1 x t (of_eq_true (Eq.trans (congr (congrArg And (eq_true (Exists.intro i hi))) (eq_true ht)) (and_self True))))
        --have : i  = z.choose := by
          --have: ⟨i, hi⟩ = z := by rfl
         -- rw[← this]
         -- have := uniqueOpenCell (x : Y) i z.choose hi sz

        sorry

      sorry
    · simp only [Set.mem_preimage, SetLike.mem_coe, r_dimCW, hcell, false_and, ↓reduceDIte,
      Set.mem_setOf_eq]
      right
      refine ⟨?_, ht⟩
      have xmem := x.2
      simp only [hX, Set.mem_union, SetLike.mem_coe, Set.mem_iUnion, hcell, or_false] at xmem
      exact xmem

  · sorry
