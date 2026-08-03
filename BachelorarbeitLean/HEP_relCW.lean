import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Data.Set.Subset
import Mathlib.Topology.Defs.Filter
import Mathlib.Data.PEquiv
import BachelorarbeitLean.HEP_definition
import BachelorarbeitLean.HEP_ball_cube
import BachelorarbeitLean.HEP_cell
import BachelorarbeitLean.HEP_skeleton


open Metric
open Set.Notation
open Topology
open RelCWComplex

noncomputable section

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] (X : Set Y) {C : Set Y} [RelCWComplex X C]

lemma ex_r_skel' (m : ℕ) : ∃ r,
    RetractionOn r {p : Y × ℝ | p.1 ∈ (skeletonLT X (↑m + 1)).carrier ∧ p.2 ∈ unitInterval}
      {p | p.1 ∈ (skeletonLT X (↑m + 1)) ∧ p.2 = 0 ∨ p.1 ∈ (skeletonLT X ↑m) ∧ p.2 ∈ unitInterval} :=
  (retraction_criterion_closed' (skeletonLT X m).carrier (skeletonLT X (m+1)).carrier
    (skeletonLT_mono le_self_add) ((skeletonLT X ↑m).closed')).1 (HEP'_skeleton (X := X) m)

def r_skel' (m : ℕ) : Y × ℝ → Y × ℝ := (ex_r_skel' X m).choose

lemma r_skel'_IsRetactionOn (m : ℕ) : RetractionOn (r_skel' X m)
  {p : Y × ℝ | p.1 ∈ (skeletonLT X (↑m + 1)).carrier ∧ p.2 ∈ unitInterval}
  {p | p.1 ∈ (skeletonLT X (↑m + 1)) ∧ p.2 = 0 ∨ p.1 ∈ (skeletonLT X ↑m) ∧ p.2 ∈ unitInterval} :=
  (ex_r_skel' X m).choose_spec

lemma induction_start_0 : HEP' (skeletonLT X 0) C := by
  rw[skeletonLT_zero_eq_base, HEP', Subtype.coe_preimage_self]
  exact HEP_self

lemma induction_start_1 : HEP' (skeletonLT X 1) C := by
  simp only [← skeletonLT_zero_eq_base (C := X) (D := C)]
  exact HEP'_skeleton 0

lemma HEP'_finite_relCW (m : ℕ) : HEP' (skeletonLT X m) C := by
  induction m with
  | zero => exact induction_start_0 X
  | succ n n_ih =>
    apply HEP_trans' (skeletonLT X (n + 1)).carrier  (skeletonLT X n) C (skeletonLT_mono
      le_self_add) (Subcomplex.closed (skeletonLT X n)) ?_ (Subcomplex.base_subset (skeletonLT X ↑n))
      (isClosedBase X) n_ih
    exact HEP'_skeleton n

    /-
    have := (retraction_criterion_closed' C (skeletonLT X n) (skeletonLT X n).base_subset
      (isClosedBase X)).mp n_ih
    have hr_n := this.choose_spec
    set r_n := this.choose -/
