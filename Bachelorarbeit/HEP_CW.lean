import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.GaugeRescale
import Bachelorarbeit.HEP_definition

noncomputable section

open Topology
universe u
variable {m : ℕ} {X Y : Set (EuclideanSpace ℝ (Fin m))}
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

lemma domain_union : Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 2
    = Metric.closedBall 0 1 ∪ {p : EuclideanSpace ℝ (Fin m) | 1 ≤ dist 0 p ∧ dist 0 p ≤ 2} := by
  ext x
  simp only [Set.mem_union, mem_closedBall, dist_zero_right, dist_zero, Set.mem_setOf_eq]
  grind

def aux_fun {Y : Type u} (f : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) → Y)
    (H : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) × ℝ → Y)
    : EuclideanSpace ℝ (Fin m) → Y := fun p =>
  if hp : norm p ≤ 1 then f ⟨p, by simp[hp]⟩
  else H (⟨(‖p‖⁻¹ : ℝ) • p, inv_norm_smul_mem_unitClosedBall p⟩, norm p - 1)

lemma aux_contOn_ring (f : (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) → Y)
    (H : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) × ℝ → Y) (hf_cont : Continuous f)
    (hH_cont : ContinuousOn H {p | p.1 ∈ sphere ⟨0, by simp⟩ 1 ∧ p.2 ∈ Set.Icc 0 1})
    (hAgree : agreeOn_A f H (Metric.sphere ⟨0, mem_closedBall_self zero_le_one⟩ 1)) :
    ContinuousOn (aux_fun f H) {p | 1 ≤ dist 0 p ∧ dist 0 p ≤ 2} := by
  rw [continuousOn_iff_continuous_restrict]
  apply Continuous.congr ?_ ?_
  · use (fun p => H (⟨(‖p.val‖⁻¹ : ℝ) • p, inv_norm_smul_mem_unitClosedBall p.1⟩, norm p.val - 1))
  · apply ContinuousOn.comp_continuous hH_cont ?_ ?_
    · refine continuous_prodMk.mpr ⟨ (Continuous.subtype_mk ?_ _ ), by fun_prop ⟩
      sorry
    · intro x
      rw [Set.mem_setOf_eq]
      constructor
      · simp only [Set.mem_setOf_eq, mem_sphere, Subtype.dist_eq, dist_zero_right, inv_nonneg,
          norm_nonneg, norm_smul_of_nonneg]
        refine inv_mul_cancel₀ ?_
        have := x.2.1
        rw  [← dist_ne_zero]
        sorry
      · sorry
  sorry

lemma aux_contOn (f : (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) → Y)
    (H : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) × ℝ → Y) (hf_cont : Continuous f)
    (hH_cont : ContinuousOn H {p | p.1 ∈ sphere ⟨0, by simp⟩ 1 ∧ p.2 ∈ Set.Icc 0 1})
    (hAgree : agreeOn_A f H (Metric.sphere ⟨0, mem_closedBall_self zero_le_one⟩ 1)) :
    ContinuousOn (aux_fun f H) (closedBall 0 2) := by
  rw[domain_union]
  apply ContinuousOn.union_of_isClosed ?_ (aux_contOn_ring f H hf_cont hH_cont hAgree)
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

def H'' (f : (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) → Y)
  (H : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) × ℝ → Y) :
  (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) × ℝ → Y :=
    fun p => (aux_fun f H ) ((1 + p.2) • p.1)

lemma HEP_Disc_boundary : ∀ (m : ℕ), m ≥ 0 →
    HEP (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) (Metric.sphere ⟨0, by simp⟩ 1):= by
  intro m hm Y hY C f H hf_cont hf_mapsto hH_cont hH_mapsto hfH_agree
  let H' : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) × ℝ → Y := fun p => (aux_fun f H)
    ((1 + p.2) • p.1)
  use H'
  refine ⟨?_, ?_, ?_, ?_⟩
  · sorry
  · sorry
  · -- agree f H'
    intro x
    simp [H', aux_fun, mem_closedBall_zero_iff.mp x.prop]
  · sorry







lemma X_quotient (A : Set X) (hA1 : IsClosed A) (hA2 : Nonempty A) (m : ℕ) [RelCWComplex (Set.univ : Set X) A]
    (h : ∀ n, n ≠ m → IsEmpty (RelCWComplex.cell (Set.univ : Set X) n)) :
  true  := by sorry


-- GOAL :
lemma HEP_rel (A : Set X) (hA1 : IsClosed A) (hA2 : Nonempty A) (n : ℕ) [RelCWComplex (Set.univ : Set X) A]
    (h : ∀ m, m ≠ n → IsEmpty (RelCWComplex.cell (Set.univ : Set X) m)) :
    HEP X A := by
  apply (retraction_criterion_closed hA1 hA2).2
  sorry
