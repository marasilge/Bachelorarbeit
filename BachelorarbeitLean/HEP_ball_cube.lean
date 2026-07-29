import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Data.Set.Subset
import Mathlib.Topology.Defs.Filter
import BachelorarbeitLean.HEP_definition

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


def aux_fun : EuclideanSpace ℝ (Fin m) → Y := fun p =>
  if hp : norm p ≤ 1 then f ⟨p, by simp[hp]⟩
  else H (⟨(‖p‖⁻¹ : ℝ) • p, inv_norm_smul_mem_unitClosedBall p⟩, norm p - 1)

lemma aux_contOn_ring [TopologicalSpace Y]
    (hH_cont : ContinuousOn H {p | p.1 ∈ sphere ⟨0, by simp⟩ 1 ∧ p.2 ∈ Set.Icc 0 1})
    (hAgree : agreeOn f H (sphere ⟨0, by simp⟩ 1)) :
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
    (hAgree : agreeOn f H (Metric.sphere ⟨0, mem_closedBall_self zero_le_one⟩ 1)) :
    ContinuousOn (aux_fun f H) (closedBall 0 2) := by
  have domain_union : Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 2 =
    Metric.closedBall 0 1 ∪ {p : EuclideanSpace ℝ (Fin m) | 1 ≤ dist 0 p ∧ dist 0 p ≤ 2} := by
    ext x
    simp only [Set.mem_union, mem_closedBall, dist_zero_right, dist_zero, Set.mem_setOf_eq]
    grind
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
    (hAgree : agreeOn f H (Metric.sphere ⟨0, by simp⟩ 1)) :
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
  simp only [Nat.ofNat_pos, mul_le_iff_le_one_right]
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
      constructor <;>
      · intro h_neg
        simp [h_neg] at hp
    · simp only
      rw [not_le, ← sub_pos] at hp
      refine ⟨Std.le_of_lt hp , ?_ ⟩
      rw [norm_smul_of_nonneg (by positivity [hx.1])] at ⊢ hp
      have le_two : (1 + x.2) ≤ 2 := by
        rw [add_comm, ← le_sub_iff_add_le]
        linarith [hx.2]
      grw[ tsub_le_iff_left, one_add_one_eq_two, le_two]
      apply mul_le_of_le_one_right zero_le_two (mem_closedBall_zero_iff.1 x.1.2)


lemma H'_agreeH
    (hAgree : agreeOn f H (Metric.sphere ⟨0, by simp⟩ 1)) :
    ∀ (a : (sphere ⟨0, by simp⟩ 1)) (t : unitInterval), H (a, t) = (H' f H) (a.1, t.1) := by
  unfold H' aux_fun
  intro a t
  have norm_a: ‖a.1.1‖ = 1 := mem_sphere_zero_iff_norm.mp (mem_sphere.1 a.2)
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
  intro m Y hY f H hf_cont hH_cont hAgree
  refine ⟨H' f H, H'_ContinuousOn f H hf_cont hH_cont hAgree , ?_ , H'_agreeH f H hAgree ⟩
  intro x
  simp [H', aux_fun, mem_closedBall_zero_iff.mp x.prop]

lemma HEP_disc_boundary' : ∀ (m : ℕ),
    HEP' (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) (Metric.sphere 0 1):= by
  exact HEP_disc_boundary

/-
HEP for Cubes and boundary:
-/

variable {m : ℕ}
def fun_euclid_max : EuclideanSpace ℝ (Fin m) → (Fin m → ℝ) := fun p ↦ p

def homeomorphic_euclid_max : EuclideanSpace ℝ (Fin m)  ≃ₜ (Fin m → ℝ) where
  toFun := @fun_euclid_max m
  invFun := fun p ↦ { ofLp := p }
  left_inv := congrFun rfl
  right_inv := congrFun rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

lemma closed_embedding_euclid_max : Topology.IsClosedEmbedding (@fun_euclid_max m) := by
  refine ⟨homeomorphic_euclid_max.isEmbedding, ?_ ⟩
  suffices h : Set.range (@fun_euclid_max m) = ⊤ by
    rw[h]
    exact closure_subset_iff_isClosed.mp fun ⦃a⦄ a_1 ↦ trivial
  refine Eq.symm (Set.Subset.antisymm ?_ fun ⦃a⦄ a_1 ↦ trivial)
  intro x hx
  use WithLp.toLp 2 x
  simp[fun_euclid_max]

lemma convex_euclid_to_max_ball : Convex ℝ (fun_euclid_max '' (closedBall
  (0 :EuclideanSpace ℝ (Fin m)) 1)) := by
  refine Convex.is_linear_image (convex_closedBall 0 1) ?_
  exact { map_add := fun x ↦ congrFun rfl, map_smul := fun c ↦ congrFun rfl }

lemma nonempty_euclid_to_max_ball : (interior (fun_euclid_max '' (closedBall
    (0 :EuclideanSpace ℝ (Fin m)) 1))).Nonempty := by
  use 0
  rw [mem_interior]
  use fun_euclid_max '' ball 0 1
  refine ⟨ Set.image_mono  ball_subset_closedBall ,  homeomorphic_euclid_max.isOpenMap
    (ball 0 1) isOpen_ball , ?_ ⟩
  use 0
  refine ⟨mem_ball_self zero_lt_one, by rfl ⟩

lemma bounded_euclid_to_max_ball : Bornology.IsBounded (fun_euclid_max '' (closedBall
    (0 :EuclideanSpace ℝ (Fin m)) 1)) :=
  Bornology.isBounded_induced.mp isBounded_closedBall

def G : (Fin m → ℝ) ≃ₜ (Fin m → ℝ):= (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
  convex_euclid_to_max_ball
  nonempty_euclid_to_max_ball bounded_euclid_to_max_ball).choose

lemma hG_closed : G '' closure (fun_euclid_max '' closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)
    = closedBall 0 1  :=
  (exists_homeomorph_image_interior_closure_frontier_eq_unitBall convex_euclid_to_max_ball
  nonempty_euclid_to_max_ball bounded_euclid_to_max_ball).choose_spec.2.1

lemma hG_front : G '' frontier (fun_euclid_max '' closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)
    = sphere 0 1 :=
  (exists_homeomorph_image_interior_closure_frontier_eq_unitBall convex_euclid_to_max_ball
  nonempty_euclid_to_max_ball bounded_euclid_to_max_ball).choose_spec.2.2

lemma closure_hG_cosed : closure (@fun_euclid_max m '' closedBall 0 1) = (fun_euclid_max ''
    closedBall 0 1) := by
  refine closure_eq_iff_isClosed.mpr ?_
  exact (Topology.IsClosedEmbedding.isClosed_iff_image_isClosed closed_embedding_euclid_max).mp
    isClosed_closedBall

def comp_homeomorphic : EuclideanSpace ℝ (Fin m) ≃ₜ (Fin m → ℝ) :=
  Homeomorph.trans homeomorphic_euclid_max G

def comp_partialhomeomorphic : PartialHomeomorph (EuclideanSpace ℝ (Fin m)) (Fin m → ℝ) :=
  comp_homeomorphic.toPartialHomeomorphOfImageEq (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)
  (closedBall (0 : (Fin m → ℝ)) 1) (by
    apply Set.BijOn.image_eq
    have trans_eq_comp: (homeomorphic_euclid_max.trans G : EuclideanSpace ℝ (Fin m) → Fin m → ℝ )
      = G.toFun.comp homeomorphic_euclid_max := List.map_inj.mp rfl
    refine Set.BijOn.mk ?_ ?_ ?_
    · rw [comp_homeomorphic, trans_eq_comp]
      simp only [Equiv.toFun_as_coe, Homeomorph.coe_toEquiv, homeomorphic_euclid_max,
        Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk]
      refine Set.mapsTo_image_iff.mp ?_
      rw [Set.mapsTo_iff_image_subset, ← closure_hG_cosed]
      exact (Eq.subset (@hG_closed m))
    · exact Function.Injective.injOn comp_homeomorphic.injective
    · rw [ comp_homeomorphic, trans_eq_comp, Set.surjOn_comp_iff]
      simp only [Equiv.toFun_as_coe, Homeomorph.coe_toEquiv, homeomorphic_euclid_max,
        Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk]
      rw[← closure_hG_cosed]
      apply (Set.image_eq_iff_surjOn_mapsTo.1 hG_closed).1 )

lemma HEP_cube_boundary' : ∀ (m : ℕ),
    HEP' (closedBall (0 : (Fin m → ℝ)) 1) (sphere 0 1) := by
  -- exact HEP_cube_boundary
  intro m
  refine PartialHomeomorph_HEP' sphere_subset_closedBall sphere_subset_closedBall
    (HEP_disc_boundary' m) comp_partialhomeomorphic (by rfl) (by rfl) ?_
    isClosed_sphere isClosed_sphere
  simp only [comp_partialhomeomorphic, comp_homeomorphic, homeomorphic_euclid_max,
    Homeomorph.toPartialHomeomorphOfImageEq_apply, Homeomorph.trans_apply,
    Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk]
  rw[← hG_front, ← Set.image_image]
  refine (Set.image_eq_image G.injective).mpr ?_
  have := (@homeomorphic_euclid_max m).image_frontier (closedBall 0 1)
  simp only [homeomorphic_euclid_max, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk] at this
  rw[← this, frontier_closedBall 0 one_ne_zero]

lemma HEP_cube_boundary : ∀ (m : ℕ),
    HEP (closedBall (0 : (Fin m → ℝ)) 1) (sphere ⟨0, by simp⟩ 1) := by
  --exact HEP_cube_boundary'
  intro m
  refine partialHomeomorph_HEP (HEP_disc_boundary m) comp_partialhomeomorphic (by rfl) (by rfl) ?_
    (IsClosed.trans isClosed_sphere isClosed_closedBall)
    (IsClosed.trans isClosed_sphere isClosed_closedBall)
  simp only [comp_partialhomeomorphic, comp_homeomorphic, homeomorphic_euclid_max,
    Homeomorph.toPartialHomeomorphOfImageEq_apply, Homeomorph.trans_apply,
    Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk]
  have s_finm: Subtype.val '' (sphere ⟨0, mem_closedBall_self zero_le_one⟩ 1 :
      Set (closedBall (0 : Fin m → ℝ) 1)) = sphere 0 1 := by
    refine Set.SurjOn.image_eq_of_mapsTo ?_ fun ⦃x⦄ a ↦ a
    intro f hf
    simp only [Set.mem_image, mem_sphere, Subtype.exists, mem_closedBall, dist_zero_right,
      exists_and_right, exists_eq_right]
    use mem_closedBall_zero_iff.mp (sphere_subset_closedBall hf)
    exact mem_sphere.mp hf
  have s_eucl : Subtype.val '' (sphere ⟨0, mem_closedBall_self zero_le_one⟩ 1 :
      Set (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)) = sphere 0 1 := by
    refine Set.SurjOn.image_eq_of_mapsTo ?_ fun ⦃x⦄ a ↦ a
    intro f hf
    simp only [Set.mem_image, mem_sphere, Subtype.exists, mem_closedBall, dist_zero_right,
      exists_and_right, exists_eq_right]
    use mem_closedBall_zero_iff.mp (sphere_subset_closedBall hf)
    exact mem_sphere.mp hf
  rw[s_finm, s_eucl, ← hG_front, ← Set.image_image]
  refine (Set.image_eq_image G.injective).mpr ?_
  have := (@homeomorphic_euclid_max m).image_frontier (closedBall 0 1)
  simp only [homeomorphic_euclid_max, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk] at this
  rw[← this, frontier_closedBall 0 one_ne_zero]
