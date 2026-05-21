import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.GaugeRescale
import Bachelorarbeit.HEP_definition

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

lemma HEP_disc_boundary : ∀ (m : ℕ), m ≥ 0 →
    HEP (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) (Metric.sphere ⟨0, by simp⟩ 1):= by
  intro m hm Y hY C f H hf_cont hf_range hH_cont hH_mapsto hAgree
  use H'  f H
  refine ⟨?_ , ?_ , ?_, ?_ ⟩
  · exact H'_ContinuousOn f H hf_cont hH_cont hAgree
  · exact H'_MapsTo C f H hf_range hH_mapsto
  · intro x
    simp [H', aux_fun, mem_closedBall_zero_iff.mp x.prop]
  · exact H'_agreeH  f H hAgree


/-
HEP for Cubes and boundary
-/

lemma HEP_cube_boundary : ∀ (m : ℕ), m ≥ 0 →
    HEP (closedBall (0 : (Fin m → ℝ)) 1) (Metric.sphere ⟨0, by simp⟩ 1) := by sorry
  -- Beweis noch nicht final fertig... (nur in der 'Basic.lean' Datei)




variable {m : ℕ} {A : Set (EuclideanSpace ℝ (Fin m))} {ι : Type*}

def J : (i : ι) → Set (EuclideanSpace ℝ (Fin m)) :=
  Function.const _ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)

#check Set.iUnion J

def setoid_CW : Setoid (Set (EuclideanSpace ℝ (Fin m))) where
  r := -- attaching map von dem cube an A
    sorry
  iseqv := sorry

-- def X_quotien := Quotient.mk setoid_CW ( A ∪ (Set.iUnion H) )



open Topology

lemma X_quotient (A : Set X) (hA1 : IsClosed A) (hA2 : Nonempty A) [RelCWComplex (Set.univ : Set X) A]
    (m : ℕ) (h : ∀ n, n ≠ m → IsEmpty (RelCWComplex.cell (Set.univ : Set X) n)) :
  true  := by sorry


-- GOAL :
lemma HEP_rel_dimn (A : Set X) (hA1 : IsClosed A) (hA2 : Nonempty A) [RelCWComplex (Set.univ : Set X) A]
    (n : ℕ) (h : ∀ m, m ≠ n → IsEmpty (RelCWComplex.cell (Set.univ : Set X) m)) :
    HEP X A := by
  apply (retraction_criterion_closed hA1 hA2).2
  sorry
