import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Data.Set.Subset
import Mathlib.Topology.Defs.Filter
import BachelorarbeitLean.HEP_definition
import BachelorarbeitLean.HEP_ball_cube
import BachelorarbeitLean.HEP_cell
import BachelorarbeitLean.HEP_skeleton

open Topology
open RelCWComplex

noncomputable section

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] (X : Set Y) {C : Set Y} [RelCWComplex X C]

lemma ex_r_skel' (m : ℕ) : ∃ r,
    RetractionOn r (smalcyl (skeletonLT X (↑m + 1)).carrier)
      (anchor' ↑(skeletonLT X (↑m + 1)) ↑(skeletonLT X ↑m)) :=
  (retraction_criterion_closed' (skeletonLT X m).carrier (skeletonLT X (m+1)).carrier
    (skeletonLT_mono le_self_add) ((skeletonLT X ↑m).closed')).1 (HEP'_skeleton (X := X) m)

def r_skel' (m : ℕ) : Y × ℝ → Y × ℝ := (ex_r_skel' X m).choose

lemma r_skel'_IsRetactionOn (m : ℕ) : RetractionOn (r_skel' X m)
  (smalcyl (skeletonLT X (↑m + 1)).carrier)
  (anchor' ↑(skeletonLT X (↑m + 1)) ↑(skeletonLT X ↑m)) :=
  (ex_r_skel' X m).choose_spec

lemma induction_start_0 : HEP' (skeletonLT X 0) C := by
  rw[skeletonLT_zero_eq_base, HEP', Subtype.coe_preimage_self]
  exact HEP_self

lemma induction_start_1 : HEP' (skeletonLT X 1) C := by
  simp only [← skeletonLT_zero_eq_base (C := X) (D := C)]
  exact HEP'_skeleton 0

lemma HEP'_finite_skel_base (m : ℕ) : HEP' (skeletonLT X m) C := by
  induction m with
  | zero => exact induction_start_0 X
  | succ n n_ih =>
    apply HEP_trans (skeletonLT X (n + 1)).carrier  (skeletonLT X n) C (skeletonLT_mono
      le_self_add)  ?_ (Subcomplex.base_subset (skeletonLT X ↑n)) n_ih
    exact HEP'_skeleton n

lemma RelCW_eq_UnionSkelCell (m : ℕ∞) : X = (skeletonLT X m).carrier ∪ ⋃ (n : ℕ) (m ≤ n)
    (j : cell X n), openCell n j := by
  simp only [← union_iUnion_openCell_eq_complex (C := X) (D := C)]
  rw [← (skeletonLT X m).union']
  rw [Set.union_assoc]
  congr
   --[← iUnion_openCell_eq_skeletonLT (C := X) (D := C) m ]
  sorry

lemma HEP'_finite_relCW (m : ℕ) (hX : FiniteDimensional X) : ∃ (m : ℕ), X = skeletonLT X m := by
  have := hX.eventually_isEmpty_cell
  rw[Filter.eventually_atTop] at this
  obtain ⟨m , hm⟩ := this
  use m
  refine Set.Subset.antisymm_iff.mpr ?_
  refine ⟨ ?_ , (skeletonLT X m).subset_complex ⟩
  simp only [← union_iUnion_openCell_eq_complex, Set.union_subset_iff, Set.iUnion_subset_iff]
  refine ⟨ Set.subset_union_left, ?_ ⟩
  intro m_x i


  sorry
