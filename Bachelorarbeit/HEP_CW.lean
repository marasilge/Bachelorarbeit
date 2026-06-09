import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.GaugeRescale
import Bachelorarbeit.HEP_definition
import Mathlib.Data.Set.Subset
import Mathlib.Topology.Defs.Filter

noncomputable section


  --(f : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) → Y)

/-
Prop 2.28
∀ m ≥ 0, the pair (D^m , ∂D^m) has the homotopy extension property

Proof:
Construction of an auxilliar function aux_fun, which is defined on the Disc with radius 2 and
contains the information of f and H.
We use aux_fun to define the extended homotopy
-/


open Metric

variable {m : ℕ} {X Y : Type} [TopologicalSpace X] (C : Set Y)
  (f : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) → Y)
  (H : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) × ℝ → Y)

lemma domain_union : Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 2 =
    Metric.closedBall 0 1 ∪ {p : EuclideanSpace ℝ (Fin m) | 1 ≤ dist 0 p ∧ dist 0 p ≤ 2} := by
  ext x
  simp only [Set.mem_union, mem_closedBall, dist_zero_right, dist_zero, Set.mem_setOf_eq]
  grind

def aux_fun : EuclideanSpace ℝ (Fin m) → Y := fun p =>
  if hp : norm p ≤ 1 then f ⟨p, by simp[hp]⟩
  else H (⟨(‖p‖⁻¹ : ℝ) • p, inv_norm_smul_mem_unitClosedBall p⟩, norm p - 1)

lemma aux_contOn_ring [TopologicalSpace Y]
    (hH_cont : ContinuousOn H {p | p.1 ∈ sphere ⟨0, by simp⟩ 1 ∧ p.2 ∈ Set.Icc 0 1})
    (hAgree : agreeOn_A f H (sphere ⟨0, by simp⟩ 1)) :
    ContinuousOn (aux_fun f H) {p | 1 ≤ dist 0 p ∧ dist 0 p ≤ 2} := by
  rw [continuousOn_iff_continuous_restrict]
  apply Continuous.congr ?_ ?_
  · use (fun p => H (⟨(‖p.val‖⁻¹ : ℝ) • p, inv_norm_smul_mem_unitClosedBall p.1⟩, norm p.val - 1))
  · apply ContinuousOn.comp_continuous hH_cont ?_ ?_
    · refine continuous_prodMk.mpr ⟨(Continuous.subtype_mk ?_ _ ), by fun_prop ⟩
      refine (continuous_subtype_val.norm.inv₀ ?_ ).smul continuous_subtype_val
      intro a
      grind [a.prop.1, dist_zero_left]
    · intro x
      rw [Set.mem_setOf_eq]
      constructor
      · simp only [Set.mem_setOf_eq, mem_sphere, Subtype.dist_eq, dist_zero_right, inv_nonneg,
          norm_nonneg, norm_smul_of_nonneg]
        refine inv_mul_cancel₀ ?_
        grind [x.prop.1, dist_zero_left]
      · simp only [Set.mem_setOf_eq, Set.mem_Icc, sub_nonneg, tsub_le_iff_right, one_add_one_eq_two]
        have h1 := x.prop.1
        have h2 := x.prop.2
        rw [dist_zero_left] at h1 h2
        exact ⟨h1, h2⟩
  · intro x
    by_cases hx : norm x.val = 1
    · specialize hAgree ⟨⟨x.val, by simp[hx]⟩, mem_sphere.mpr (mem_sphere_zero_iff_norm.2 hx)⟩
      simp only [Set.mem_setOf_eq, hx, inv_one, one_smul, sub_self, Set.restrict_apply, aux_fun,
        Std.le_refl, reduceDIte]
      exact hAgree.symm
    · suffices hh : (¬ (norm x.val) ≤ 1) by simp [hh, aux_fun]
      have := x.prop
      rw [Set.mem_setOf_eq, dist_zero_left] at this
      exact not_le.2 (Std.lt_of_le_of_ne this.1 (Ne.intro hx).symm)

lemma aux_contOn [TopologicalSpace Y] (hf_cont : Continuous f)
    (hH_cont : ContinuousOn H {p | p.1 ∈ sphere ⟨0, by simp⟩ 1 ∧ p.2 ∈ Set.Icc 0 1})
    (hAgree : agreeOn_A f H (Metric.sphere ⟨0, mem_closedBall_self zero_le_one⟩ 1)) :
    ContinuousOn (aux_fun f H) (closedBall 0 2) := by
  rw[domain_union]
  apply ContinuousOn.union_of_isClosed ?_ (aux_contOn_ring f H hH_cont hAgree)
    (isClosed_closedBall ) ?_
  · rw [continuousOn_iff_continuous_restrict, Set.restrict_eq]
    apply Continuous.congr hf_cont
    intro x
    simp [aux_fun, mem_closedBall_zero_iff.1 x.prop]
  · rw [Set.setOf_and]
    apply IsClosed.inter ?_ ?_
    · rw [dist_zero, ← closure_le_eq continuous_const continuous_norm]
      exact isClosed_closure
    · rw [dist_zero, ← closure_le_eq continuous_norm continuous_const]
      exact isClosed_closure

def H' : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) × ℝ → Y :=
    fun p => (aux_fun f H ) ((1 + p.2) • p.1)

lemma H'_ContinuousOn [TopologicalSpace Y] (hf_cont : Continuous f)
    (hH_cont : ContinuousOn H {p | p.1 ∈ sphere ⟨0, by simp⟩ 1 ∧ p.2 ∈ Set.Icc 0 1})
    (hAgree : agreeOn_A f H (Metric.sphere ⟨0, by simp⟩ 1)) :
    ContinuousOn (H' f H) {p | p.2 ∈ unitInterval} := by
  unfold H'
  refine ContinuousOn.comp (aux_contOn f H hf_cont hH_cont hAgree) (by fun_prop ) ?_
  intro x hx
  simp only [Metric.mem_closedBall, dist_zero_right]
    -- (ab hier eigentlich nur noch Ungleichung lösen)
  have : ‖1 + x.2‖ ≤ 2 := by
      rw [show ‖1 + x.2‖ = |1 + x.2| from rfl]
      grw[abs_add_le, hx.2]
      · rw[abs_one, le_iff_eq_or_lt]
        left
        norm_num
      · exact hx.1
  grw [norm_smul, this]
  simp only [Nat.ofNat_pos, mul_le_iff_le_one_right, ge_iff_le]
  apply mem_closedBall_zero_iff.1 (Subtype.coe_prop x.1)

lemma H'_MapsTo (hf_range : Set.range f ⊆ C)
    (hH_mapsto : Set.MapsTo H {p | p.1 ∈ sphere ⟨0, by simp⟩ 1 ∧ p.2 ∈ unitInterval} C) :
    {p | p.2 ∈ unitInterval}.MapsTo (H' f H) C := by
  unfold H' aux_fun
  intro x hx
  by_cases hp : ‖(1 + x.2) • x.1.val‖ ≤ 1
  · simp only [hp, reduceDIte]
    apply Set.range_subset_iff.1 hf_range
  · simp only [hp, reduceDIte]
    apply hH_mapsto
    constructor
    · simp only [mem_sphere, Subtype.dist_eq, dist_zero_right]
      refine norm_smul_inv_norm (smul_ne_zero_iff.2 ?_)
      constructor
      · intro h_neg
        simp [h_neg] at hp
      · intro h_neg
        simp [h_neg] at hp
    · refine ⟨by grind, ?_ ⟩
      grw [tsub_le_iff_right, norm_smul_of_nonneg (by grind) x.1.1, hx.2]
      simp only [ pos_add_self_iff, zero_lt_one, mul_le_iff_le_one_right]
      exact mem_closedBall_zero_iff.1 (Subtype.coe_prop x.1)


lemma H'_agreeH
    (hAgree : agreeOn_A f H (Metric.sphere ⟨0, by simp⟩ 1)) :
    ∀ (a : (sphere ⟨0, by simp⟩ 1)) (t : unitInterval), H (a, t) = (H' f H) (a.1, t.1) := by
  unfold H' aux_fun
  intro a t
  have norm_a: ‖a.1.1‖ = 1 := by grind [mem_sphere, Subtype.dist_eq, dist_zero_right a.1.1]
  by_cases ht : ‖(1 + t.1) • a.1.val‖ = 1
  · simp [ht]
    have Hf := (hAgree ⟨a.1, by rw [mem_sphere, Subtype.dist_eq, dist_zero_right, norm_a]⟩).symm
    have : t = 0 := by
      simp only [norm_smul_of_nonneg (add_nonneg zero_le_one t.2.1), norm_a, mul_one, add_eq_left,
        Set.Icc.coe_eq_zero] at ht
      exact ht
    simp [this, Hf]
  · have : ¬ ‖(1 + t.val) • a.val.1‖ ≤ 1 := by
      rw [not_le]
      rw [← ne_eq, ne_comm] at ht
      refine lt_of_le_of_ne ?_ ht
      rw [norm_smul_of_nonneg ?_ a.1.1]
      · grw[← t.prop.1]
        simp only [add_zero, one_mul]
        apply Eq.ge
        exact norm_a
      · grw[← t.prop.1]
        norm_num
    simp only [this, reduceDIte]
    congrm H ( ?_ , ?_)
    · refine SetCoe.ext ?_
      simp only [Real.norm_eq_abs, mul_one, smul_smul, norm_smul, norm_a]
      rw [abs_of_pos (by grind), inv_mul_cancel₀ (by grind)]
      norm_num
    · rw [norm_smul, norm_a, Real.norm_eq_abs, mul_one, abs_of_pos (by grind)]
      norm_num

lemma HEP_disc_boundary : ∀ (m : ℕ),
    HEP (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) (Metric.sphere ⟨0, by simp⟩ 1):= by
  intro m Y hY C f H hf_cont hf_range hH_cont hH_mapsto hAgree
  use H'  f H
  refine ⟨?_ , ?_ , ?_, ?_ ⟩
  · exact H'_ContinuousOn f H hf_cont hH_cont hAgree
  · exact H'_MapsTo C f H hf_range hH_mapsto
  · intro x
    simp [H', aux_fun, mem_closedBall_zero_iff.mp x.prop]
  · exact H'_agreeH  f H hAgree

#check zero_le
/-
HEP for Cubes and boundary
-/

lemma HEP_cube_boundary : ∀ (m : ℕ),
    HEP (closedBall (0 : (Fin m → ℝ)) 1) (Metric.sphere ⟨0, by simp⟩ 1) := by sorry
  -- Beweis noch nicht final fertig... (nur in der 'Basic.lean' Datei)


/-
HEP for the pair (X,A), if X is obtained from A by attaching m-cells
-/
--set_option trace.Meta.synthInstance true
/-

open Set.Notation
open Topology
open RelCWComplex

variable {Y : Type*} [TopologicalSpace Y] (X C : Set Y) [RelCWComplex X C] {m : ℕ}
  (A : Subcomplex X)


def r_cube (hm : 0 < m) : (closedBall (0 : Fin m → ℝ) 1) × ℝ → (closedBall (0 : Fin m → ℝ) 1) × ℝ :=
  Exists.choose ((retraction_criterion_closed isClosed_sphere (by
    have := (@NormedSpace.sphere_nonempty (Fin m → ℝ) _ _ ?_ 0 1).2 zero_le_one
    · use ⟨this.choose, Metric.sphere_subset_closedBall this.choose_spec⟩
      exact mem_sphere.mpr this.choose_spec
    · refine nontrivialTopology_iff_exists_norm_ne_zero.mpr ?_
      simp only [ne_eq, norm_eq_zero]
      use Pi.single ⟨0, hm⟩ 1
      exact Function.ne_iff.mpr ⟨ ⟨0, hm⟩, by simp⟩)).1
    (HEP_cube_boundary m (Nat.zero_le m)))

lemma r_cube1 (hm : 0 < m) : ContinuousOn (r_cube hm) {p | p.2 ∈ unitInterval}:=
  (Exists.choose_spec ((retraction_criterion_closed isClosed_sphere (by
    have := (@NormedSpace.sphere_nonempty (Fin m → ℝ) _ _ ?_ 0 1).2 zero_le_one
    · use ⟨this.choose, Metric.sphere_subset_closedBall this.choose_spec⟩
      exact mem_sphere.mpr this.choose_spec
    · refine nontrivialTopology_iff_exists_norm_ne_zero.mpr ?_
      simp only [ne_eq, norm_eq_zero]
      use Pi.single ⟨0, hm⟩ 1
      exact Function.ne_iff.mpr ⟨ ⟨0, hm⟩, by simp⟩)).1
  (HEP_cube_boundary m (Nat.zero_le m)))).1

lemma r_cube2 (hm : 0 < m) : {p | p.2 ∈ unitInterval}.MapsTo (r_cube hm)
  {p | p.2 = 0 ∨ p.1 ∈ (sphere ⟨ 0, by simp⟩  1) ∧ p.2 ∈ unitInterval} :=
  (Exists.choose_spec ((retraction_criterion_closed isClosed_sphere (by
    have := (@NormedSpace.sphere_nonempty (Fin m → ℝ) _ _ ?_ 0 1).2 zero_le_one
    · use ⟨this.choose, Metric.sphere_subset_closedBall this.choose_spec⟩
      exact mem_sphere.mpr this.choose_spec
    · refine nontrivialTopology_iff_exists_norm_ne_zero.mpr ?_
      simp only [ne_eq, norm_eq_zero]
      use Pi.single ⟨0, hm⟩ 1
      exact Function.ne_iff.mpr ⟨ ⟨0, hm⟩, by simp⟩)).1
  (HEP_cube_boundary m (Nat.zero_le m)))).2.1


lemma r_cube3 (hm : 0 < m) :
  ∀ (a : {(p : (closedBall (0 : Fin m → ℝ) 1) × ℝ ) | p.2 = 0 ∨
    p.1 ∈ (sphere (⟨0, by simp⟩ : (closedBall (0 : Fin m → ℝ) 1)) 1) ∧ p.2 ∈ unitInterval}),
    (r_cube hm) a = a :=
  (Exists.choose_spec ((retraction_criterion_closed isClosed_sphere (by
    have := (@NormedSpace.sphere_nonempty (Fin m → ℝ) _ _ ?_ 0 1).2 zero_le_one
    · use ⟨this.choose, Metric.sphere_subset_closedBall this.choose_spec⟩
      exact mem_sphere.mpr this.choose_spec
    · refine nontrivialTopology_iff_exists_norm_ne_zero.mpr ?_
      simp only [ne_eq, norm_eq_zero]
      use Pi.single ⟨0, hm⟩ 1
      exact Function.ne_iff.mpr ⟨ ⟨0, hm⟩, by simp⟩)).1
  (HEP_cube_boundary m (Nat.zero_le m)))).2.2


-- universal property of the quotient:
#check Topology.IsQuotientMap.lift
-- iff für quotientmap
#check Topology.isQuotientMap_iff'
-- wann ist etwas im CW complex closed:
#check RelCWComplex.closed


def RestrictMap (i : cell X m) : closedBall (0 : Fin m → ℝ) 1 →
  closedCell m i :=
  Set.MapsTo.restrict (map m i) ( closedBall 0 1)
    (closedCell m i) (Set.mapsTo_image (map m i) (closedBall 0 1))

lemma RestrictMap_isClosedMap [T2Space Y] (i : cell X m) : IsClosedMap (RestrictMap X C i) :=
  Continuous.isClosedMap (ContinuousOn.mapsToRestrict (continuousOn m i) _ )

lemma RestrictMap_Continuous (i : cell X m) : Continuous (RestrictMap X C i) :=
  ContinuousOn.mapsToRestrict (continuousOn m i) _

lemma quotient_Restrict (i : cell X m) [T2Space Y] : IsQuotientMap (RestrictMap X C i) := by
  have Restrict_Surj : Function.Surjective (RestrictMap X C i) :=
            (Set.MapsTo.restrict_surjective_iff (RestrictMap._proof_1 X C i)).mpr (fun a a_1 ↦ a_1)
  constructor
  · exact Restrict_Surj
  · refine Eq.symm ((fun {X} {t₁ t₂} ↦ TopologicalSpace.ext_iff_isClosed.mpr) ?_)
    intro S
    constructor
    · intro hs_map
      rw[isClosed_coinduced] at hs_map
      rw [isClosed_induced_iff]
      use Subtype.val ∘ (RestrictMap X C i) '' (RestrictMap X C i ⁻¹' S)
      constructor
      · rw[RelCWComplex.closed X _ ?_ ]
        · constructor
          · intro n j
            refine IsClosed.inter ?_ (isClosed_closedCell)
            have : IsClosedMap (Subtype.val ∘ RestrictMap X C i) := by
              refine IsClosedMap.comp ?_ (by exact RestrictMap_isClosedMap X C i)
              exact IsClosed.isClosedMap_subtype_val isClosed_closedCell
            exact this (RestrictMap X C i ⁻¹' S) hs_map
          · refine IsClosed.inter ?_ (by exact isClosedBase X)
            have : IsClosedMap (Subtype.val ∘ RestrictMap X C i) := by
              refine IsClosedMap.comp ?_ (by exact RestrictMap_isClosedMap X C i)
              exact IsClosed.isClosedMap_subtype_val isClosed_closedCell
            exact isClosed_coinduced.mpr (this (RestrictMap X C i ⁻¹' S) hs_map)
        · refine Set.MapsTo.image_subset (Set.MapsTo.comp_right ?_ (RestrictMap X C i))
          rw [Set.mapsTo_iff_subset_preimage,
            Set.preimage_val_eq_univ_of_subset (closedCell_subset_complex m i)]
          tauto
      · ext s
        constructor
        · intro hs
          rw [Set.image_comp Subtype.val (RestrictMap X C i) (RestrictMap X C i ⁻¹' S),
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
      exact (ContinuousOn.mapsToRestrict (continuousOn m i) _)
/-
Claime das folgende, ohne es jetzt beweisen zu wollen: -/

lemma QuotientProductIdentityOnLocallyCompact {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {f : X → Y} (hf : IsQuotientMap f) (hZ : LocallyCompactSpace Z) :
    IsQuotientMap (Prod.map f (@id Z)) := by
  sorry -- erstmal nicht



def C_Prod (i : cell X m) :
  C(closedBall (0 : Fin m → ℝ) 1 × unitInterval , closedCell m i × unitInterval) where
    toFun := (Prod.map (RestrictMap X C i) id)
    continuous_toFun := Continuous.prodMap (RestrictMap_Continuous X C i) continuous_id

lemma quotient_RestrictIdentity (i : cell X m) [T2Space Y] :
    IsQuotientMap (C_Prod X C i) :=
  QuotientProductIdentityOnLocallyCompact (quotient_Restrict X C i)
    (WeaklyLocallyCompactSpace.locallyCompactSpace)

def gprod (i : cell X m) (hm : 0 < m) :
  C(closedBall (0 : Fin m → ℝ) 1 × unitInterval , closedCell m i × ℝ ) where
    toFun := fun (p,t) ↦
      (⟨map m i (r_cube hm (p,t)).1, Set.mem_image_of_mem (map m i) (Subtype.coe_prop (r_cube hm (p, t)).1)⟩,
      (r_cube hm (p,t)).2)
    continuous_toFun := by
      rw [continuous_prodMk]
      constructor
      ·
        --apply ContinuousOn.comp_continuous ?_ ?_ `_
        sorry
      · exact continuous_snd.comp ((r_cube1 hm).comp_continuous (by fun_prop) (fun x ↦ x.2.2))



lemma RestrictFactors (i : cell X m) (hm : 0 < m) :  Function.FactorsThrough (gprod X C i hm) (C_Prod X C i):= by
  intro x y heq
  simp only [C_Prod, ContinuousMap.coe_mk, Prod.ext_iff] at heq
  obtain ⟨heq1, heq2⟩ := heq
  simp only [Prod.map_fst, Prod.map_snd, id_eq] at heq2 heq1
  simp only [gprod, Prod.mk.eta, ContinuousMap.coe_mk, Prod.mk.injEq, Subtype.mk.injEq]
  constructor
  · sorry
  · sorry

def retractionCell_toFun [T2Space Y] (i : cell X m) (hm : 0 < m) : C(closedCell m i × unitInterval, closedCell m i × ℝ) :=
  (quotient_RestrictIdentity X C i).lift (gprod X C i hm) (RestrictFactors X C i hm)




/-
def gfun ( i : cell X m) (t : ℝ ) (hm : 0 ≤ m): Metric.closedBall (0 : Fin m → ℝ) 1 →
  (map m i).toFun '' (Metric.closedBall 0 1) := fun p ↦
  ⟨(map m i).toFun ∘ (r_cube hm (p,t)).1, by sorry⟩

variable (p : closedBall (0 : Fin 4 → ℝ) 1) (i : cell X 4)
#check (map 4 i).toFun (r_cube zero_le_four).1 (p,0.4)
#check r_cube zero_le_four (p,0.4)
-/






/-
neuer Start: Ich fange von hinten an und schaue welche Funktionen ich genau brauche, um piecewise
  continuous für CW complexe anzuwenden
· f ist die Familie aller cellularen retractions
· fD und fX sind die Identität

PROBLEM: Ich muss meine Funktion auf (CW) × ℝ definieren und das ist anstrengend
-/

/- explizite Definition des retracts:
-/

open Classical in
def r : X × ℝ → X × ℝ := fun (p,t) ↦
  if hi : ∃ (i : cell X m), (p : Y) ∈ openCell m i then
    (⟨(map m (Exists.choose hi)).toFun 0, by sorry⟩ , 0)
    --((map m (Exists.choose hi)).toFun ∘ (map m (Exists.choose hi)).symm p,t)

  else (p,t)


lemma HEP_Dim (hX : X = ↑A ∪ ⋃ (j : cell X m), (map m j) '' (Metric.closedBall 0 1))
    (hA : Nonempty (X ↓∩ ↑A)) (hm : m ≥ 0)
     :
    HEP' X A := by
  apply (retraction_criterion_closed (by sorry) hA).2
  have := (retraction_criterion_closed (by sorry) (by sorry)).1 (HEP_cube_boundary m hm)
  sorry

#check  ⋃ m, ⋃ (j : cell X m), openCell m j
-/
