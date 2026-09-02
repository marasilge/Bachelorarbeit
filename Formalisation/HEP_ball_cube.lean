/-
Copyright (c) 2026 Mara Silge. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mara Silge
-/

import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Data.Set.Subset
import Mathlib.Topology.Defs.Filter
import Formalisation.HEP_definition

/-!
# HEP for balls and cubes

We prove the HEP for the ball relative to its boundary (D^m, ∂(D^m)) and for the cube relative
to its boundary ([-1,1]^m, ∂([-1,1]^m)). These are the first pairs of spaces for which we
establish the property, and they are the first step in the proof for relative CW-complexes.

For the ball we do not use the retraction criterion but check the definition directly. From the
given map `f` and homotopy `H` we build an auxiliary function on the ball of radius two and
obtain the extended homotopy by rescaling.

The cube is then reached by transport along a homeomorphism. What makes the cube appear is that
in `Fin m → ℝ` with the maximum norm the closed unit ball is a cube, so we first move the ball
into that space and then apply a Mathlib lemma that carries a convex bounded set with nonempty
interior onto the closed unit ball. This is the shape in which the characteristic maps of a
CW-complex have their domain.

## Main definitions

* `aux_fun` and `H'`: the auxiliary function assembled from `f` and `H`, and the extended
  homotopy defined from it by rescaling the first coordinate.
* `homeo_euclid_max`: the identity map that changes the norm of the ambient space from the
  Euclidean to the maximum norm.
* `comp_homeo` and `comp_partialhomeo`: the homeomorphism from the ball to the cube and its
  upgrade to a partial homeomorphism with source the ball and target the cube.

## Main results

* `HEP_ball_boundary` and `HEP_ball_boundary'`: the ball has the HEP relative to its boundary,
  stated for both definitions of the property.
* `HEP_cube_boundary'` and `HEP_cube_boundary`: the same for the cube, obtained from the ball
  through `PartialHomeomorph_HEP'`.
-/

noncomputable section
open Metric


/- The notation follows the convention fixed in `HEP_definition`: `Z` is the target type of the
maps `f`, `H`, `H'` and `rangeH' ⊆ Z` constrains their range. Here `Z` has to live in `Type 0`,
since the pair of this section is a pair of types in `Type 0`. -/

variable {m : ℕ} {Z : Type} [TopologicalSpace Z] (rangeH' : Set Z)
  (f : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) → Z)
  (H : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) × ℝ → Z)

/-
HEP for a ball relative to its boundary:
∀ m ≥ 0, the pair (D^m , ∂D^m) has the homotopy extension property.

Proof:
Construction of an auxiliary function aux_fun that is defined on the ball of radius 2 and
contains the information of f and H.
We then use aux_fun to define the extended homotopy.
-/

-- Definition of the auxiliary function:
def aux_fun : EuclideanSpace ℝ (Fin m) → Z := fun p =>
  if hp : norm p ≤ 1 then f ⟨p, by simp[hp]⟩
  else H (⟨((norm p)⁻¹ : ℝ) • p, inv_norm_smul_mem_unitClosedBall p⟩, norm p - 1)

/- First of the three steps towards continuity of `aux_fun`: continuity on the annulus
{p | 1 ≤ ‖p‖ ≤ 2}. -/
lemma aux_contOn_annulus
    (hH_cont : ContinuousOn H (smallcyl (sphere ⟨0, by simp⟩ 1)))
    (hAgree : agreeOn f H (sphere ⟨0, by simp⟩ 1)) :
    ContinuousOn (aux_fun f H) {p | 1 ≤ dist 0 p ∧ dist 0 p ≤ 2} := by
  rw [continuousOn_iff_continuous_restrict]
  apply Continuous.congr ?_ ?_
  · use (fun p => H (⟨(‖p.val‖⁻¹ : ℝ) • p, inv_norm_smul_mem_unitClosedBall p.1⟩, norm p.val - 1))
  · apply hH_cont.comp_continuous ?_ ?_
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
      · simp only [Set.mem_setOf_eq, Set.mem_Icc, sub_nonneg, tsub_le_iff_right, one_add_one_eq_two,
          ← dist_zero_left]
        exact ⟨x.prop.1, x.prop.2⟩
  · intro x
    by_cases hx : norm x.val = 1
    · simp only [Set.mem_setOf_eq, hx, inv_one, one_smul, sub_self, Set.restrict_apply, aux_fun,
        Std.le_refl, reduceDIte]
      exact (hAgree  ⟨x.val, by simp[hx]⟩ (mem_sphere.mpr (mem_sphere_zero_iff_norm.2 hx))).symm
    · suffices h : (¬ (norm x.val) ≤ 1) by simp [h, aux_fun]
      refine not_le.2 (Std.lt_of_le_of_ne ?_ (Ne.intro hx).symm)
      have := x.prop
      rw [Set.mem_setOf_eq, dist_zero_left] at this
      exact this.1

-- Continuity of the auxiliary function on the ball of radius 2:
lemma aux_contOn (hf_cont : Continuous f)
    (hH_cont : ContinuousOn H (smallcyl (sphere ⟨0, by simp⟩ 1)))
    (hAgree : agreeOn f H (Metric.sphere ⟨0, mem_closedBall_self zero_le_one⟩ 1)) :
    ContinuousOn (aux_fun f H) (closedBall 0 2) := by
  have domain_union : Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 2 =
    Metric.closedBall 0 1 ∪ {p : EuclideanSpace ℝ (Fin m) | 1 ≤ dist 0 p ∧ dist 0 p ≤ 2} := by
    ext x
    simp only [Set.mem_union, mem_closedBall, dist_zero_right, dist_zero, Set.mem_setOf_eq]
    grind
  rw[domain_union]
  apply ContinuousOn.union_of_isClosed ?_ (aux_contOn_annulus f H hH_cont hAgree)
    (isClosed_closedBall) ?_
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

-- Defining the extended homotopy via the auxiliary function:
def H' : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) × ℝ → Z :=
  fun p => (aux_fun f H ) ((1 + p.2) • p.1)

-- Checking that this homotopy H' satisfies all required properties. We start with continuity.
lemma H'_ContinuousOn (hf_cont : Continuous f)
    (hH_cont : ContinuousOn H (smallcyl (sphere ⟨0, by simp⟩ 1)))
    (hAgree : agreeOn f H (Metric.sphere ⟨0, by simp⟩ 1)) :
    ContinuousOn (H' f H) (cyl (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)) := by
  refine ContinuousOn.comp (aux_contOn f H hf_cont hH_cont hAgree) (by fun_prop ) ?_
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  have : ‖1 + x.2‖ ≤ 2 := by
      rw [show ‖1 + x.2‖ = |1 + x.2| from rfl]
      grw [abs_add_le, hx.2]
      · rw[abs_one, le_iff_eq_or_lt]
        left
        norm_num
      · exact hx.1
  grw [norm_smul, this]
  simp only [Nat.ofNat_pos, mul_le_iff_le_one_right]
  apply mem_closedBall_zero_iff.1 (Subtype.coe_prop x.1)

-- The `range` field of `HomotopyExtension`: the values of `H'` stay inside `rangeH'`.
omit [TopologicalSpace Z] in
lemma H'_MapsTo (hf_range : Set.range f ⊆ rangeH')
    (hH_mapsto : Set.MapsTo H (smallcyl (sphere ⟨0, by simp⟩ 1)) rangeH') :
    (cyl (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)).MapsTo (H' f H) rangeH' := by
  unfold H' aux_fun
  intro x hx
  by_cases hp : ‖(1 + x.2) • x.1.val‖ ≤ 1
  · simp only [hp]
    apply Set.range_subset_iff.1 hf_range
  · simp only [hp]
    apply hH_mapsto
    constructor
    · simp only [mem_sphere, Subtype.dist_eq, dist_zero_right]
      refine norm_smul_inv_norm (smul_ne_zero_iff.2 ?_)
      constructor <;>
      · intro h_neg
        simp [h_neg] at hp
    · rw [not_le, ← sub_pos] at hp
      refine ⟨Std.le_of_lt hp , ?_ ⟩
      have le_two : (1 + x.2) ≤ 2 := by
        rw [add_comm, ← le_sub_iff_add_le]
        linarith [hx.2]
      simp only
      rw [norm_smul_of_nonneg (by positivity [hx.1])] at ⊢ hp
      grw[ tsub_le_iff_left, one_add_one_eq_two, le_two]
      exact mul_le_of_le_one_right zero_le_two (mem_closedBall_zero_iff.1 x.1.2)

-- The `agreeH` field of `HomotopyExtension`: on the boundary `H'` reproduces `H`.
omit [TopologicalSpace Z] in
lemma H'_agreeH
    (hAgree : agreeOn f H (sphere ⟨0, by simp⟩ 1)) :
    ∀ (a : (sphere ⟨0, by simp⟩ 1)) (t : unitInterval), H (a, t) = (H' f H) (a.1, t.1) := by
  unfold H' aux_fun
  intro a t
  have norm_a: ‖a.1.1‖ = 1 := mem_sphere_zero_iff_norm.mp (mem_sphere.1 a.2)
  by_cases ht : ‖(1 + t.1) • a.1.val‖ = 1
  · have Hf := (hAgree a.1 (by rw [mem_sphere, Subtype.dist_eq, dist_zero_right, norm_a])).symm
    have ht0 : t = 0 := by
      simp only [norm_smul_of_nonneg (add_nonneg zero_le_one t.2.1), norm_a, mul_one, add_eq_left,
        Set.Icc.coe_eq_zero] at ht
      exact ht
    simp [ht, Std.le_refl]
    simp [ht0, Set.Icc.coe_zero, Hf, add_zero, one_smul, Subtype.coe_eta]
  · have : ¬ ‖(1 + t.val) • a.val.1‖ ≤ 1 := by
      rw [not_le]
      rw [← ne_eq, ne_comm] at ht
      refine lt_of_le_of_ne ?_ ht
      grw [norm_smul_of_nonneg (by grw[← t.prop.1]; norm_num) a.1.1, ← t.prop.1, add_zero, one_mul]
      exact Eq.ge norm_a
    simp only [this, reduceDIte]
    congrm H ( ?_ , ?_)
    · refine SetCoe.ext ?_
      simp only [Real.norm_eq_abs, mul_one, smul_smul, norm_smul, norm_a]
      rw [abs_of_pos (by grind), inv_mul_cancel₀ (by grind)]
      norm_num
    · rw [norm_smul, norm_a, Real.norm_eq_abs, mul_one, abs_of_pos (by grind)]
      norm_num

-- Combining the above results to get the main result, that the ball relative boundary has the HEP.
lemma HEP_ball_boundary : ∀ (m : ℕ),
    HEP (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) (sphere ⟨0, by simp⟩ 1) := by
  intro m Z hZ rangeH' f H hf_cont hf_range hH_cont hH_range hAgree
  refine ⟨H' f H, H'_ContinuousOn f H hf_cont hH_cont hAgree, ?_ , ?_ , H'_agreeH f H hAgree ⟩
  · exact fun _ hx => H'_MapsTo rangeH' f H hf_range hH_range hx
  · exact fun x => by simp [H', aux_fun, mem_closedBall_zero_iff.mp x.prop]

-- Transferred to the version with `HEP'` by an `exact` statement, since the two definitions
-- are definitionally equal:
lemma HEP_ball_boundary' : ∀ (m : ℕ),
  HEP' (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) (sphere 0 1) := HEP_ball_boundary

/-
HEP for a cube relative to its boundary:
∀ m ≥ 0, the pair ([-1,1]^m , ∂([-1,1]^m)) has the homotopy extension property.
Proof:
Construct a homeomorphism from the `m`-dimensional ball to the cube.
-/

/- Identity map that changes the norm of the ambient space from the Euclidean to the maximum
norm. We use that the ball in maximum norm is a cube to transfer the result to the pair of it.
-/
def homeo_euclid_max : EuclideanSpace ℝ (Fin m)  ≃ₜ (Fin m → ℝ) where
  toFun := fun p ↦ p
  invFun := fun p ↦ {ofLp := p }
  left_inv := congrFun rfl
  right_inv := congrFun rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

-- `homeo_euclid_max` is a closed embedding, which is what lets us identify the closure of the
-- image of the closed ball in `closure_hG_closed` below.
lemma closed_embedding_euclid_max : Topology.IsClosedEmbedding (@homeo_euclid_max m) := by
  refine ⟨homeo_euclid_max.isEmbedding, ?_ ⟩
  suffices h : Set.range (@homeo_euclid_max m) = ⊤ by
    rw[h]
    exact closure_subset_iff_isClosed.mp fun ⦃a⦄ a_1 ↦ trivial
  refine Eq.symm (Set.Subset.antisymm ?_ fun ⦃a⦄ a_1 ↦ trivial)
  intro x hx
  use WithLp.toLp 2 x
  simp[homeo_euclid_max]

/- The image of the closed ball under `homeo_euclid_max` is convex, has nonempty interior and is
bounded. These three lemmas are exactly the hypotheses `hc`, `hne` and `hb` of the Mathlib
lemma `exists_homeomorph_image_interior_closure_frontier_eq_unitBall`, which we apply below. -/

lemma convex_euclid_to_max_ball : Convex ℝ (homeo_euclid_max '' (closedBall
  (0 : EuclideanSpace ℝ (Fin m)) 1)) := by
  refine Convex.is_linear_image (convex_closedBall 0 1) ?_
  exact { map_add := fun x ↦ congrFun rfl, map_smul := fun c ↦ congrFun rfl }

lemma nonempty_euclid_to_max_ball : (interior (homeo_euclid_max '' (closedBall
    (0 : EuclideanSpace ℝ (Fin m)) 1))).Nonempty := by
  use 0
  rw [mem_interior]
  use homeo_euclid_max '' ball 0 1
  refine ⟨Set.image_mono ball_subset_closedBall, homeo_euclid_max.isOpenMap
    (ball 0 1) isOpen_ball , ?_ ⟩
  use 0
  refine ⟨mem_ball_self zero_lt_one, by rfl ⟩

lemma bounded_euclid_to_max_ball : Bornology.IsBounded (homeo_euclid_max '' (closedBall
    (0 : EuclideanSpace ℝ (Fin m)) 1)) :=
  Bornology.isBounded_induced.mp isBounded_closedBall

/- Homeomorphism from the image of the closed ball under `homeo_euclid_max` to [-1,1]^m. Since
 the Mathlib lemma only asserts that such a map exists, we use `.choose` to fix one of them.
 Its two defining properties are `hG_closed` and `hG_front` below, obtained by `.choose_spec`. -/
def G : (Fin m → ℝ) ≃ₜ (Fin m → ℝ):= (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
  convex_euclid_to_max_ball
  nonempty_euclid_to_max_ball bounded_euclid_to_max_ball).choose

lemma hG_closed : G '' closure (homeo_euclid_max '' closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)
    = closedBall 0 1  :=
  (exists_homeomorph_image_interior_closure_frontier_eq_unitBall convex_euclid_to_max_ball
  nonempty_euclid_to_max_ball bounded_euclid_to_max_ball).choose_spec.2.1

lemma hG_front : G '' frontier (homeo_euclid_max '' closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)
    = sphere 0 1 :=
  (exists_homeomorph_image_interior_closure_frontier_eq_unitBall convex_euclid_to_max_ball
  nonempty_euclid_to_max_ball bounded_euclid_to_max_ball).choose_spec.2.2

-- The image of the closed ball is already closed, so taking the closure changes nothing. We use
-- this in the proof of `comp_partialhomeo` below.
lemma closure_hG_closed : closure (@homeo_euclid_max m '' closedBall 0 1) =
  ((fun (p : EuclideanSpace ℝ (Fin m)) ↦ p.ofLp) '' closedBall 0 1) := by
  refine closure_eq_iff_isClosed.mpr ?_
  exact (closed_embedding_euclid_max.isClosed_iff_image_isClosed).mp
    isClosed_closedBall

/- The desired homeomorphism is the composite of the two above. It is in particular a partial
  homeomorphism from the ball to the cube, which is the shape `PartialHomeomorph_HEP'` expects.-/
def comp_homeo : EuclideanSpace ℝ (Fin m) ≃ₜ (Fin m → ℝ) := homeo_euclid_max.trans G

def comp_partialhomeo : PartialHomeomorph (EuclideanSpace ℝ (Fin m)) (Fin m → ℝ) :=
  comp_homeo.toPartialHomeomorphOfImageEq (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)
  (closedBall (0 : (Fin m → ℝ)) 1) (by
    rw [Set.BijOn.image_eq]
    have trans_eq_comp : ⇑(homeo_euclid_max.trans (@G m)) = ⇑G ∘ ⇑homeo_euclid_max := rfl
    refine Set.BijOn.mk ?_ ?_ ?_
    · rw [comp_homeo, trans_eq_comp]
      simp only [homeo_euclid_max, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk]
      refine Set.mapsTo_image_iff.mp ?_
      rw [Set.mapsTo_iff_image_subset, ← closure_hG_closed]
      exact (Eq.subset (@hG_closed m))
    · exact comp_homeo.injective.injOn
    · rw [ comp_homeo, trans_eq_comp, Set.surjOn_comp_iff]
      simp only [homeo_euclid_max, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk]
      rw[← closure_hG_closed]
      apply (Set.image_eq_iff_surjOn_mapsTo.1 hG_closed).1 )

/- `PartialHomeomorph_HEP'` yields the final result that cubes relative boundary have the HEP.-/
lemma HEP_cube_boundary' (m : ℕ) :
    HEP' (closedBall (0 : (Fin m → ℝ)) 1) (sphere 0 1) := by
  refine PartialHomeomorph_HEP' sphere_subset_closedBall sphere_subset_closedBall
    (HEP_ball_boundary' m) comp_partialhomeo (by rfl) (by rfl) ?_ isClosed_sphere
  simp only [comp_partialhomeo, comp_homeo, homeo_euclid_max,
    Homeomorph.toPartialHomeomorphOfImageEq_apply, Homeomorph.trans_apply,
    Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk]
  rw[← hG_front, ← Set.image_image]
  refine (Set.image_eq_image G.injective).mpr ?_
  have := (@homeo_euclid_max m).image_frontier (closedBall 0 1)
  simp only [homeo_euclid_max, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk] at this ⊢
  rw[← this, frontier_closedBall 0 one_ne_zero]

-- The analogous statement for `HEP`:
lemma HEP_cube_boundary (m : ℕ) :
    HEP (closedBall (0 : (Fin m → ℝ)) 1) (sphere ⟨0, by simp⟩ 1) :=
  HEP_cube_boundary' m
