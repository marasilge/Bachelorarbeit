import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Constructions.SumProd
import BachelorarbeitLean.HEP_skeleton

open Topology
open RelCWComplex

noncomputable section

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] (X : Set Y) {C : Set Y} [RelCWComplex X C]

-- Every skeleton relative to its base has the `HEP'`:
lemma HEP_skelLT_base (m : ℕ) : HEP' (skeletonLT X m) C := by
  induction m with
  | zero =>
    rw [ENat.coe_zero, skeletonLT_zero_eq_base, HEP', Subtype.coe_preimage_self]
    exact HEP_self
  | succ n n_ih =>
    apply HEP_trans (skeletonLT X (n + 1)).carrier  (skeletonLT X n) C (skeletonLT_mono
      le_self_add)  ?_ (Subcomplex.base_subset (skeletonLT X ↑n)) n_ih
    exact HEP'_skeleton X n

-- Transfered the result from `skeletonLT` to `skeleton
lemma HEP_skel_base (m : ℕ) : HEP' (skeleton X m) C := by
  rw [skeleton.congr_simp X m m rfl]
  exact HEP_skelLT_base X (m + 1)

/- We can split the union over all open cells in the union over all open cells up to dimension
  m and a second onion over all remaining higher dimensional cells.
-/
omit [T2Space Y] in
lemma splitUnionAtLt (m : ℕ) : ⋃ (n : ℕ), ⋃ (j : cell X n), openCell n j =
    (⋃ n ∈ {x | x < m}, ⋃ (j : cell X n), openCell n j) ∪
    (⋃ n ∈ {x | m ≤ x}, ⋃ (j : cell X n), openCell n j) := by
  suffices h :  {x | x < m} ∪ {x | m ≤ x} = Set.univ by
    rw [← Set.biUnion_univ, ← h, Set.biUnion_union]
  ext n
  refine ⟨by tauto, ?_ ⟩
  intro _
  by_cases hnm : n < m
  · exact Set.mem_union_left _ hnm
  · apply Set.mem_union_right _ (Std.not_lt.mp hnm)

/- We can write a relatice CW-complex as the union of an (m-1)-skeleton and all open cells
  of dimension m or higher -/
lemma RelCW_eq_UnionSkelLtCell (m : ℕ) : X = ↑(skeletonLT X m) ∪ (⋃ n ≥ m, ⋃ (j : cell X n),
    openCell n j) := by
  simp only [← union_iUnion_openCell_eq_complex (C := X) (D := C)]
  rw [splitUnionAtLt X m, ← Set.union_assoc]
  congr
  simp only [Set.mem_setOf_eq]
  convert iUnion_openCell_eq_skeletonLT (C := X) (D := C) m
  rw [Nat.cast_lt]

/-
For a finite dimensional relative CW-complex (X,C) we can find a natural number m, such that
X equals the (m-1)-skeleton
-/
lemma RelCWFinite_eq_SkelLT (hX : FiniteDimensional X) : ∃ (m : ℕ), X = skeletonLT X m := by
  obtain ⟨m, hm⟩ := Filter.eventually_atTop.1 hX.eventually_isEmpty_cell
  use m
  convert RelCW_eq_UnionSkelLtCell X m
  convert (Set.union_empty _ ).symm
  apply Set.iUnion_eq_empty.mpr
  intro b
  apply Set.iUnion_eq_empty.mpr
  intro hb
  specialize hm b hb
  simp only [Set.iUnion_of_empty]

-- every finite dimensional CW complex has the `HEP'`
lemma HEP_RelCWFinite (hX : FiniteDimensional X) : HEP' X C := by
  obtain ⟨m, hm⟩ := RelCWFinite_eq_SkelLT X hX
  rw[hm]
  exact HEP_skelLT_base X m



-- für die zukunft
lemma ex_r_skel' (m : ℕ) : ∃ r,
    RetractionOn r (smalcyl (skeletonLT X (↑m + 1)).carrier)
    (smalanchor ↑(skeletonLT X (↑m + 1)) ↑(skeletonLT X ↑m)) :=
  (retraction_criterion_closed' (skeletonLT X m).carrier (skeletonLT X (m+1)).carrier
    (skeletonLT_mono le_self_add) ((skeletonLT X ↑m).closed')).1 (HEP'_skeleton (X := X) m)

def r_skel' (m : ℕ) : Y × ℝ → Y × ℝ := (ex_r_skel' X m).choose

lemma r_skel'_IsRetactionOn (m : ℕ) : RetractionOn (r_skel' X m)
  (smalcyl (skeletonLT X (m + 1))) (smalanchor (skeletonLT X (m + 1)) (skeletonLT X m)) :=
  (ex_r_skel' X m).choose_spec
