/-
Copyright (c) 2026 Mara Silge. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mara Silge
-/

import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Constructions.SumProd
import Formalisation.HEP_skeleton

/-!
# HEP for finite dimensional relative CW-complexes

This file proves that a finite dimensional relative CW-complex `(X, C)` has the HEP relative to
its base. This is the final result of the formalisation. The general case, in which the complex
need not be finite dimensional, is not covered here.

The proof has two steps. First an induction over the skeleta, whose base case is the HEP of a
space relative to itself and whose inductive step combines the HEP for two consecutive skeleta
with the transitivity of the HEP. Second, the observation that a finite dimensional complex is
one of its own skeleta.

## Main results

* `HEP_skelLT_base` and `HEP_skel_base`: every skeleton has the HEP relative to the base, stated
  for both notions of skeleton that Mathlib provides.
* `RelCWFinite_eq_SkelLT`: a finite dimensional complex equals one of its skeleta.
* `HEP_RelCWFinite`: a finite dimensional relative CW-complex has the HEP relative to its base.
-/

open Topology
open RelCWComplex

noncomputable section

/- The notation follows the convention fixed in `HEP_definition`: `Y` is the ambient type,
`X : Set Y` the relative CW-complex and `C : Set Y` its base. The dimensions `m` and `n` are
bound in each declaration separately. -/

universe u

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] (X : Set Y) {C : Set Y} [RelCWComplex X C]

-- Every skeleton relative to its base has the `HEP'`. The proof is an induction over `m`.
lemma HEP_skelLT_base (m : ℕ) : HEP' (skeletonLT X m) C := by
  induction m with
  | zero =>
    rw [ENat.coe_zero, skeletonLT_zero_eq_base, HEP', Subtype.coe_preimage_self]
    exact HEP_self
  | succ n n_ih =>
    apply HEP_trans (skeletonLT X (n + 1)).carrier  (skeletonLT X n) C (skeletonLT_mono
      le_self_add)  ?_ (Subcomplex.base_subset (skeletonLT X ↑n)) n_ih
    exact HEP'_skeleton X n

-- The same result transferred from `skeletonLT` to `skeleton`, using that `skeleton X m` is by
-- definition `skeletonLT X (m + 1)`.
lemma HEP_skel_base (m : ℕ) : HEP' (skeleton X m) C := by
  rw [skeleton.congr_simp X m m rfl]
  exact HEP_skelLT_base X (m + 1)

/- We can split the union over all open cells into the union over all open cells of dimension
  less than `m` and a second union over all remaining cells of higher dimension.-/
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

/- We can write a relative CW-complex as the union of an (m-1)-skeleton and all open cells
  of dimension `m` or higher. -/
lemma RelCW_eq_UnionSkelLtCell (m : ℕ) : X = ↑(skeletonLT X m) ∪ (⋃ n ≥ m, ⋃ (j : cell X n),
    openCell n j) := by
  simp only [← union_iUnion_openCell_eq_complex (C := X) (D := C)]
  rw [splitUnionAtLt X m, ← Set.union_assoc]
  congr
  simp only [Set.mem_setOf_eq]
  convert iUnion_openCell_eq_skeletonLT (C := X) (D := C) m
  rw [Nat.cast_lt]

/-
For a finite dimensional relative CW-complex (X,C) we can find a natural number `m` such that
X equals the (m-1)-skeleton.
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

-- The final result: every finite dimensional relative CW-complex has the `HEP'` relative to its
-- base.
lemma HEP_RelCWFinite (hX : FiniteDimensional X) : HEP' X C := by
  obtain ⟨m, hm⟩ := RelCWFinite_eq_SkelLT X hX
  rw[hm]
  exact HEP_skelLT_base X m
