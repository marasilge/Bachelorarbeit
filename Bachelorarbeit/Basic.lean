import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.GaugeRescale

noncomputable section
set_option linter.style.longLine false
universe u

def fH_agreeOn_A {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (H : X × ℝ → Y) (A : Set X) : Prop := ∀ (a : A), f a = H (a,0)

def HEP_neu (X : Type u) [TopologicalSpace X] (A : Set X) : Prop :=
  ∀ (Y : Type u) [TopologicalSpace Y] (C : Set Y), ∀ (f : X → Y), ∀ (H : X × ℝ → Y),
  ContinuousOn f (@Set.univ X) → (@Set.univ X).MapsTo f C →
  ContinuousOn H {p : X × ℝ | (p.1 ∈ A) ∧ (p.2 ∈ (Set.Icc (0 : ℝ) 1))} →
  {p : X × ℝ | (p.1 ∈ A) ∧ (p.2 ∈ (Set.Icc (0 : ℝ) 1))}.MapsTo H C  → (fH_agreeOn_A f H A)
  → ∃ (H' : X × ℝ → Y), ContinuousOn H' { p : X × ℝ | p.2 ∈ Set.Icc (0 : ℝ) 1} ∧
  { p : X × ℝ | p.2 ∈ Set.Icc (0 : ℝ) 1}.MapsTo H' C ∧
  (∀ (x : X), f x = H' (x, 0)) ∧ (∀ (a : A) (t : Set.Icc (0 : ℝ) 1), H (a,t) = H' (a, t))

-- The pair (X,X) has the HEP:
example {X : Type u} [TopologicalSpace X] : HEP_neu X (@Set.univ X) := by
  intro Y hY C f H hf_cont hf_mapstp hH_cont hH_mapsto hfHA
  use H
  refine ⟨?_, ?_ ,?_ ⟩
  · rw [← Set.sep_univ]
    exact hH_cont
  · intro x hx
    apply hH_mapsto
    simp [hx.2, hx.1]
  · simp only [implies_true, and_true]
    intro x
    exact hfHA ⟨x, by tauto⟩

/-
  "Corollary 2.25" for closed:  Let A be a closed subset of a topological space X.
  Then A ⊆ X has the HEP ↔
  for every topological space Y and every continuous map g: (X × {0}) ∪ (A × [0,1]) → Y there
  exists an extension of g to a map G : X × [0,1] → Y:
-/
-- (Hinrichtung geht auch ohne A closed)
lemma zweizweifuenf_hin {X : Type u} [TopologicalSpace X] {A : Set X} :
    HEP_neu X A →  ∀ (Y : Type u) [TopologicalSpace Y] (C : Set Y),
    ∀ (g :  X × ℝ → Y ), ContinuousOn g {p : X × ℝ | p.2 = 0 ∨ (p.1 ∈ A) ∧ p.2 ∈ (Set.Icc (0 : ℝ) 1)} →
    {p : X × ℝ | p.2 = 0 ∨ (p.1 ∈ A) ∧ p.2 ∈ (Set.Icc (0 : ℝ) 1)}.MapsTo g C →
    ∃ (G :  X × ℝ → Y), ContinuousOn G {p : X × ℝ | p.2 ∈ Set.Icc 0 1} ∧ {p : X × ℝ | p.2 ∈ Set.Icc 0 1}.MapsTo G C
    ∧ ∀ (q : {p : X × ℝ | p.2 = 0 ∨ (p.1 ∈ A) ∧ p.2 ∈ (Set.Icc (0 : ℝ) 1)}), g q = G q.val := by
  intro h_HEP Y hY C g hg_cont hg_mapsto
  let f : X → Y := fun x ↦ g (x,0)
  let H : X × ℝ → Y := fun p ↦ g p
  have hf : ContinuousOn f Set.univ := ContinuousOn.comp hg_cont (by fun_prop) (by simp)
  have hH : ContinuousOn H {p | p.1 ∈ A ∧ p.2 ∈ Set.Icc 0 1} := by
    unfold H
    exact ContinuousOn.congr_mono  hg_cont (by simp [Set.EqOn]) (by grind)
  have h_agree : fH_agreeOn_A f H A := by
    intro a
    simp [f, H]
  have hf_mapsto : Set.MapsTo f Set.univ C := by
    intro x hx
    simp only [f]
    exact hg_mapsto (by simp)
  have hH_mapsto : Set.MapsTo H {p | p.1 ∈ A ∧ p.2 ∈ Set.Icc 0 1} C := by
    intro x hx
    simp only [H]
    exact hg_mapsto (by grind)
  obtain ⟨G, ⟨hG_cont, hG⟩⟩ := h_HEP Y C f H hf hf_mapsto hH hH_mapsto h_agree
  use G
  refine ⟨hG_cont , hG.1 , ?_ ⟩
  · intro q
    cases q.prop with
    | inl h0 => grind
    | inr hA => exact hG.2.2 ⟨q.val.1, hA.1⟩ ⟨ q.val.2, hA.2⟩

lemma zweizweifuenf_rueck {X : Type u} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    (∀ (Y : Type u) [TopologicalSpace Y] (C : Set Y),
    ∀ (g :  X × ℝ → Y ), ContinuousOn g {p : X × ℝ | p.2 = 0 ∨ (p.1 ∈ A) ∧ p.2 ∈ (Set.Icc (0 : ℝ) 1)} →
    {p : X × ℝ | p.2 = 0 ∨ (p.1 ∈ A) ∧ p.2 ∈ (Set.Icc (0 : ℝ) 1)}.MapsTo g C →
    ∃ (G :  X × ℝ → Y), ContinuousOn G {p : X × ℝ | p.2 ∈ Set.Icc 0 1} ∧ {p : X × ℝ | p.2 ∈ Set.Icc 0 1}.MapsTo G C
    ∧ ∀ (q : {p : X × ℝ | p.2 = 0 ∨ (p.1 ∈ A) ∧ p.2 ∈ (Set.Icc (0 : ℝ) 1)}), g q = G q.val)  →  HEP_neu X A  := by
  intro h_extend Y hY C f H hf_cont hf_mapsto hH_cont hH_mapsto h_agree
  let g : X × ℝ → Y := fun q =>
    if h : q.2 = 0 then f q.1
    else H q
  have hg: ContinuousOn g {p | p.2 = 0 ∨ (p.1 ∈ A ∧ p.2 ∈ Set.Icc 0 1)} := by
    refine ContinuousOn.union_of_isClosed ?_ ?_ ?_ ?_
    · have h1: ContinuousOn (fun q ↦ if q.2 = 0 then f q.1 else H q) fun p ↦ p.2 = 0 =
        ContinuousOn (fun q ↦ if q.2 = 0 then f q.1 else H q) {p : X × ℝ | p.2 = 0} := rfl
      have h2: ContinuousOn (fun q ↦ if q.2 = 0 then f q.1 else H q) {p | p.2 = 0} =
          ContinuousOn (fun (q : X × ℝ ) ↦ f q.1)  {p | p.2 = 0} := by
        simp only [eq_iff_iff]
        refine continuousOn_congr ?_
        intro p hp
        grind -- grind weg ?!
      simp only [g, dite_eq_ite, h1, h2]
      exact ContinuousOn.comp hf_cont (by fun_prop) (Set.mapsTo_univ Prod.fst {p | p.2 = 0})
    · unfold g
      simp only [dite_eq_ite]
      have : ContinuousOn (fun q ↦ if q.2 = 0 then f q.1 else H q) (fun p ↦ p.1 ∈ A ∧ p.2 ∈ Set.Icc 0 1)
        = ContinuousOn (fun q ↦ if q.2 = 0 then f q.1 else H q) { p : X × ℝ | p.1 ∈ A ∧ p.2 ∈ Set.Icc 0 1} := rfl
      rw [this]
      have : ContinuousOn (fun q ↦ if q.2 = 0 then f q.1 else H q) {p | p.1 ∈ A ∧ p.2 ∈ Set.Icc 0 1} =
        ContinuousOn (fun (q : X × ℝ ) ↦ H q) {p | p.1 ∈ A ∧ p.2 ∈ Set.Icc 0 1} := by
        simp only [eq_iff_iff]
        refine continuousOn_congr ?_
        intro p hp
        by_cases h : p.2 = 0
        · simp only [ite_eq_right_iff]
          intro h'
          specialize h_agree ⟨p.1, by grind⟩
          simp only [h_agree]
          exact (congrArg H ∘ congrArg (Prod.mk p.1)) (id (Eq.symm h))
        · exact if_neg h
      rw[this]
      exact ContinuousOn.comp hH_cont (by fun_prop) (Set.mapsTo_iff_subset_preimage.mpr fun a a_1 ↦ a_1)
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · refine IsClosed.and ?_ ?_
      · have : { x : X × ℝ | x.1 ∈ A} = {x : X | x ∈ A } ×ˢ { a : ℝ | true} := by grind
        rw[this]
        exact IsClosed.prod (isClosed_coinduced.mpr hA_closed) (isClosed_const)
      · refine IsClosed.and ?_ ?_
        · exact isClosed_le (by fun_prop) (by fun_prop)
        · exact isClosed_le (by fun_prop) (by fun_prop)
  obtain ⟨G, hG⟩ := h_extend Y C g hg (by
    simp only [dite_eq_ite, g]
    intro x hx
    by_cases hx_case : x.2 = 0
    · simp only [hx_case, ↓reduceIte]
      exact hf_mapsto (by simp)
    · simp only [hx_case, ↓reduceIte]
      simp only [Set.mem_Icc, Set.mem_setOf_eq, hx_case, false_or] at hx
      exact hH_mapsto (Set.mem_sep_iff.mpr hx))
  use G
  refine ⟨hG.1, hG.2.1, ?_ ⟩
  · constructor
    · intro x
      unfold g at hG
      grind [hG.2.2 ⟨(x,0), by simp⟩]
    · intro a t
      unfold g at hG
      by_cases h : t.1 = 0
      · obtain ⟨hG_cont , ⟨hG1, hG2⟩⟩  := hG
        specialize hG2 ⟨(a,t), by grind⟩
        have : G (a, t) = f a := by grind
        specialize h_agree ⟨a, by grind⟩
        rw [this, h]
        exact h_agree.symm
      · obtain ⟨hG_cont , ⟨hG1, hG2⟩⟩ := hG
        specialize hG2 ⟨(a,t), by grind⟩ -- grind weg ?
        grind


/-
  "Lemma 2.26": A ⊆ X subspace, then TFAE:
  (i): ∀ g : A → Y, there exists an extension G : X → Y
  (ii): A is a retract of X, i.e. ∃ r: X → A s.th. r is the indentity on A
-/

lemma zweizweisechs {X : Type u} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) (hX : Nonempty X) :
    (∀ (Y : Type u) [TopologicalSpace Y] (C : Set Y) (g : X → Y),
    ContinuousOn g A → A.MapsTo g C → ∃ G : X → Y , ContinuousOn G B ∧ B.MapsTo G C ∧ ∀ a : A, g a = G a ) ↔
    ∃ r : X → X, ContinuousOn r B ∧ B.MapsTo r A ∧ ∀ a : A, r a = a := by
  classical
  constructor
  · intro h
    let g : X → X := fun p =>
      if hp : p ∈ A then p
      else Classical.choice hX
    have hg_cont: ContinuousOn g A := by
      simp only [dite_eq_ite, continuousOn_iff_continuous_restrict, Set.restrict_ite, g]
      fun_prop
    have hg_mapsAA : Set.MapsTo g A A := by
      intro a ha
      simp only [dite_eq_ite, g, ha, ↓reduceIte]
    obtain ⟨G, hG1, hG2⟩ := h X A g hg_cont hg_mapsAA
    use G
    refine ⟨hG1, hG2.1, (by intro a; grind)⟩
  · intro h Y hY C g hg hgAC
    obtain ⟨r, hr_cont, ⟨hrBA, hr_id⟩⟩ := h
    let G : X → Y := fun p =>
      if hp : p ∈ B then g (r p)
      else Classical.choice (Nonempty.map2 (fun a ↦ g) hX hX)
    use G
    refine ⟨?_ , ?_, ?_ ⟩
    · unfold G
      simp only [dite_eq_ite, continuousOn_iff_continuous_restrict, Set.restrict_ite]
      rw [← continuousOn_iff_continuous_restrict]
      refine ContinuousOn.comp hg hr_cont hrBA
    · intro b hb
      simp only [dite_eq_ite, hb, ↓reduceIte, G]
      exact hgAC (hrBA hb)
    · intro a
      simp [G, Set.mem_of_mem_of_subset a.prop hAB, hr_id]

-- A closed wieder nur für die Rückrichtung notwendig

/-
  "Corollary 2.27": **Retraction criterion:** A ⊆ X closed.
  (X,A) has the HEP ↔ (X × {0}) ∪ (A × [0,1]) is a retract of X×[0,1]
-/

lemma retraction_criterion {X : Type u} [TopologicalSpace X] {A : Set X} (hA1 : IsClosed A) (hA2 : Nonempty A) :
    HEP_neu X A ↔
    (∃ (r : X × ℝ → X × ℝ),
    ContinuousOn r {p : X × ℝ | p.2 ∈ (Set.Icc 0 1)} ∧
    {p : X × ℝ | p.2 ∈ (Set.Icc 0 1)}.MapsTo r ({p : X × ℝ | p.2 = 0 ∨ (p.1 ∈ A) ∧ p.2 ∈ (Set.Icc 0 1)}) ∧
    ∀ a : {p : X × ℝ | p.2 = 0 ∨ (p.1 ∈ A) ∧ p.2 ∈ (Set.Icc 0 1)}, r a = a ):= by
  have : Nonempty (X × ℝ) := by -- geht bestimmt schöner und Namen geben
    rw [nonempty_prod]
    refine ⟨?_ , instNonemptyOfInhabited ⟩
    obtain ⟨a , ha⟩ := hA2
    use a
  constructor
  · intro h_HEP
    apply (zweizweisechs (by simp) this).1
    intro Y hY C g hg_cont hg_mapsto
    obtain ⟨G, hG⟩ := zweizweifuenf_hin h_HEP Y C g hg_cont hg_mapsto
    use G
  · intro h
    refine zweizweifuenf_rueck hA1 ?_
    intro Y hY C g hg_cont hg_mapsto
    -- B = {p | p.2 ∈ Set.Icc 0 1}
    -- A = {p | p.2 = 0 ∨ p.1 ∈ A ∧ p.2 ∈ Set.Icc 0 1}
    obtain ⟨G, hG_cont, hG_mapsto, hG_agree⟩ := (zweizweisechs (by simp) this).2 h Y C g hg_cont hg_mapsto
    use G


/-
Prop 2.28
∀ m ≥ 0, the pair (D^m , ∂D^m) has the homotopy extension property
-/
open Metric
--> variablen anlegen???
variable {m : ℕ} {Y : Set (EuclideanSpace ℝ (Fin m))} (f : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) → Y)

lemma domain_union : Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 2
    = Metric.closedBall 0 1 ∪ {p : EuclideanSpace ℝ (Fin m) | 1 ≤ dist 0 p ∧ dist 0 p ≤ 2} := by
  ext x
  simp only [Set.mem_union, mem_closedBall, dist_zero_right, dist_zero, Set.mem_setOf_eq]
  grind

def aux_fun (m : ℕ) {Y : Type u} (f : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) → Y)
    (H : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) × ℝ → Y)
    : EuclideanSpace ℝ (Fin m) → Y := fun p =>
  if hp : norm p ≤ 1 then f ⟨p, by simp[hp]⟩
  else H (⟨(‖p‖⁻¹ : ℝ) • p, by apply inv_norm_smul_mem_unitClosedBall⟩, norm p - 1)

lemma aux_contOn {m : ℕ} {Y : Set (EuclideanSpace ℝ (Fin m))} (f : (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) → Y)
    (H : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) × ℝ → Y) (hf_cont : Continuous f) (hH_cont : Continuous H) --> ToDo: haben garnicht wirklich dass H Überall cts ist :(
    (hfH_agree : fH_agreeOn_A f H (Metric.sphere ⟨0, mem_closedBall_self zero_le_one⟩ 1)) :
    ContinuousOn (aux_fun m f H) (closedBall 0 2) :=  by
  rw[domain_union]
  refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_closedBall ?_
  · rw [continuousOn_iff_continuous_restrict, Set.restrict_eq]
    apply Continuous.congr hf_cont
    intro x
    simp [aux_fun, Function.comp_apply, Subtype.coe_eta, mem_closedBall_zero_iff.1 x.prop ]
  · rw [continuousOn_iff_continuous_restrict, Set.restrict_eq, ← continuousOn_univ]
    let G : {(p : EuclideanSpace ℝ (Fin m))| 1 ≤ dist 0 p ∧ dist 0 p ≤ 2} → Y := fun p =>
      H (⟨(‖p.val‖⁻¹ : ℝ) • p, by apply inv_norm_smul_mem_unitClosedBall⟩, norm p.val - 1)
    have hG_cont : ContinuousOn G (@Set.univ {(p : EuclideanSpace ℝ (Fin m))| 1 ≤ dist 0 p ∧ dist 0 p ≤ 2}) := by
      rw [continuousOn_univ]
      unfold G
      refine hH_cont.comp'  ?_
      simp only [Set.coe_setOf, Set.mem_setOf_eq, continuous_prodMk]
      refine ⟨?_, Continuous.fun_add (by fun_prop) (by fun_prop) ⟩
      refine Continuous.subtype_mk ?_ _
      refine (continuous_subtype_val.norm.inv₀ ?_).smul continuous_subtype_val
      intro a
      grind[dist_zero_left, a.prop.1]
    apply hG_cont.congr
    rw[Set.eqOn_univ]
    ext x
    unfold aux_fun
    by_cases hx : norm x.val = 1
    · specialize hfH_agree ⟨⟨ x.val, mem_closedBall_zero_iff.2 (le_of_eq hx)⟩, by
        rw [← mem_sphere_zero_iff_norm] at hx; exact mem_sphere.mpr hx⟩
      simp only [G, Set.mem_setOf_eq, Function.comp_apply, hx, Std.le_refl, ↓reduceDIte, inv_one,
        one_smul, sub_self, hfH_agree]
    · have : ¬ ( norm x.val ≤ 1) := by
        rw [le_iff_eq_or_lt]
        simp only [Set.mem_setOf_eq, hx, false_or, not_lt]
        have := x.prop.1
        simp only [Set.mem_setOf_eq, dist_eq_norm_vsub, vsub_eq_sub, zero_sub, norm_neg] at this
        exact this
      simp[this, G]
  · simp only [dist_zero, Set.setOf_and]
    refine IsClosed.inter ?_ ?_
    · rw [← closure_le_eq (by fun_prop) (by fun_prop)]
      exact isClosed_closure
    · rw [← closure_le_eq (by fun_prop) (by fun_prop)]
      exact isClosed_closure

def H' {m : ℕ} {Y : Type u} (f : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) → Y)
    (H : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) × ℝ → Y) : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) × ℝ → Y :=
  fun p => aux_fun m f H ((1 + p.2) • p.1)

lemma cont_H' {m : ℕ} {Y : Set (EuclideanSpace ℝ (Fin m))} (f : (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) → Y)
    (H : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) × ℝ → Y) (hf_cont : Continuous f) (hH_cont : Continuous H)
    (hfH_agree : fH_agreeOn_A f H (Metric.sphere ⟨0, mem_closedBall_self zero_le_one⟩ 1)) :
    ContinuousOn (H' f H) {p | p.2 ∈ Set.Icc 0 1} := by
  unfold H'
  sorry

lemma zweizweiacht' : ∀ (m : ℕ), m ≥ 0 →
    HEP_neu (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) (Metric.sphere ⟨0, by simp⟩ 1):= by
  intro m hm Y hY C f H hf_cont hf_mapsto hH_cont hH_mapsto hfH_agree
  let h : EuclideanSpace ℝ (Fin m) → Y := fun p =>
    if hp : norm p ≤ 1 then f ⟨p, by simp[hp]⟩
    else H (⟨(‖p‖⁻¹ : ℝ) • p, by apply inv_norm_smul_mem_unitClosedBall⟩, norm p - 1)
  have h_cont : ContinuousOn h (closedBall 0 2) := by
    rw[domain_union]
    unfold h
    apply ContinuousOn.union_of_isClosed ?_ ?_ (isClosed_closedBall ) ?_
    · rw [continuousOn_iff_continuous_restrict, Set.restrict_eq, ← continuousOn_univ]
      apply ContinuousOn.congr hf_cont
      rw[Set.eqOn_univ]
      ext x
      simp [Function.comp_apply, Subtype.coe_eta, mem_closedBall_zero_iff.1 x.prop ]
    · rw [continuousOn_iff_continuous_restrict, Set.restrict_eq, ← continuousOn_univ]
      let G : {(p : EuclideanSpace ℝ (Fin m))| 1 ≤ dist 0 p ∧ dist 0 p ≤ 2} → Y := fun p =>
        H (⟨(‖p.val‖⁻¹ : ℝ) • p, by apply inv_norm_smul_mem_unitClosedBall⟩, norm p.val - 1)
      have hG_cont : ContinuousOn G Set.univ := by
        unfold G
        apply hH_cont.comp'  ?_ ?_
        · simp only [Set.coe_setOf, Set.mem_setOf_eq, continuousOn_univ, continuous_prodMk]
          refine ⟨?_, Continuous.fun_add (by fun_prop) (by fun_prop) ⟩
          refine Continuous.subtype_mk ?_ _
          refine (continuous_subtype_val.norm.inv₀ ?_).smul continuous_subtype_val
          intro a
          have := a.prop.1
          rw [← dist_zero_left]
          grind
        · intro a ha
          constructor
          · simp only [Set.mem_setOf_eq, mem_sphere, Subtype.dist_eq, dist_zero_right]
            rw [norm_smul_of_nonneg (inv_nonneg.2 (norm_nonneg _ ))]
            refine inv_mul_cancel₀ ?_
            intro h0
            have := a.prop.1
            rw [dist_zero_left, h0, ← not_lt] at this
            exact this zero_lt_one
          · have := a.prop
            simp only [dist_eq_norm, zero_sub, norm_neg, Set.mem_setOf_eq] at this
            simp only [Set.mem_Icc, sub_nonneg, this.1, tsub_le_iff_right, one_add_one_eq_two,
              true_and, ge_iff_le]
            exact this.2
      apply ContinuousOn.congr hG_cont
      rw[Set.eqOn_univ]
      ext x
      by_cases hx : norm x.val = 1
      · simp only [G, Set.mem_setOf_eq, Function.comp_apply, hx, Std.le_refl, ↓reduceDIte, inv_one,
          one_smul, sub_self]
        specialize hfH_agree ⟨⟨ x.val, mem_closedBall_zero_iff.2 (le_of_eq hx)⟩, by
          rw [← mem_sphere_zero_iff_norm] at hx; exact mem_sphere.mpr hx⟩
        exact hfH_agree
      · have : ¬ ( norm x.val ≤ 1) := by
          rw [le_iff_eq_or_lt]
          simp only [Set.mem_setOf_eq, hx, false_or, not_lt]
          have := x.prop.1
          simp only [Set.mem_setOf_eq, dist_eq_norm_vsub, vsub_eq_sub, zero_sub, norm_neg] at this
          exact this
        simp[this, G]
    · simp only [dist_zero]
      rw [Set.setOf_and]
      refine IsClosed.inter ?_ ?_
      · rw [← closure_le_eq (by fun_prop) (by fun_prop)]
        exact isClosed_closure
      · rw [← closure_le_eq (by fun_prop) (by fun_prop)]
        exact isClosed_closure
  -----
  let H' : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) × ℝ → Y := fun p => h ((1 + p.2) • p.1)
  use H'
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- H' continuous
    refine ContinuousOn.comp h_cont (by fun_prop) ?_
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
  ·-- H' MapsTo
    unfold H' h
    intro x hx
    by_cases hp : ‖(1 + x.2) • x.1.val‖ ≤ 1
    · simp only [hp, reduceDIte]
      exact Set.mem_preimage.mp (hf_mapsto trivial)
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
  · -- agree f H'
    intro x
    simp [H', h, mem_closedBall_zero_iff.mp x.prop]
  · -- agree H H'
    intro a t
    unfold H' h
    have norm_a: ‖a.1.1‖ = 1 := by
        grind [mem_sphere, Subtype.dist_eq, dist_zero_right a.1.1]
    by_cases hp : ‖(1 + t.1) • a.1.val‖ = 1
    · simp [hp]
      have Hf := (hfH_agree ⟨a.1, by rw [mem_sphere, Subtype.dist_eq, dist_zero_right, norm_a]⟩).symm
      have : t = 0 := by
        simp only [norm_smul_of_nonneg (add_nonneg zero_le_one t.2.1), norm_a, mul_one, add_eq_left,
          Set.Icc.coe_eq_zero] at hp
        exact hp
      simp[this, Hf]
    · have : ¬ ‖(1 + t.val) • a.val.1‖ ≤ 1 := by
        rw [not_le]
        rw [← ne_eq, ne_comm] at hp
        refine lt_of_le_of_ne ?_ hp
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


lemma homeomorph_HEP {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (A : Set X) (hA_closed : IsClosed A) (hA_nonempty : Nonempty A) :
    HEP_neu X A → IsHomeomorph f → HEP_neu Y (f '' A) := by
  intro h_hep1 hf
  rw[retraction_criterion hA_closed hA_nonempty ] at h_hep1
  obtain ⟨r, hr⟩ := h_hep1
  obtain ⟨hf_cont, ⟨f_inv, hf1, hf2, hf_inv_cont⟩ ⟩ := isHomeomorph_iff_exists_inverse.1 hf
  let r' : Y × ℝ → Y × ℝ := fun p ↦ ( f (r ((f_inv p.1), p.2 )).1, (r ((f_inv p.1), p.2 )).2)
  rw [retraction_criterion (by
    exact (@Homeomorph.isClosed_image X Y _ _  (IsHomeomorph.homeomorph f hf) A).2 hA_closed) (Set.instNonemptyElemImage f A)]
  use r'
  refine ⟨?_ , ?_ , ?_ ⟩
  · refine ContinuousOn.prodMk ?_ ?_
    · refine Continuous.comp_continuousOn hf_cont ?_
      refine Continuous.comp_continuousOn' (by fun_prop) ?_
      refine ContinuousOn.comp hr.1 (by fun_prop) ?_
      intro x hx
      simp only [Set.mem_setOf_eq]
      rw [Set.mem_setOf] at hx
      exact hx
    · refine Continuous.comp_continuousOn' (by fun_prop) ?_
      refine ContinuousOn.comp hr.1 (by fun_prop) ?_
      intro x hx
      simp only [Set.mem_setOf_eq]
      exact unitInterval.mem_unitIntervalSubmonoid.mp hx
  · unfold r'
    have maps2 : Set.MapsTo (fun (p : X × ℝ) ↦ (f p.1, p.2)) {p | p.2 = 0 ∨ p.1 ∈ A ∧ p.2 ∈ Set.Icc 0 1} {p | p.2 = 0 ∨ p.1 ∈ f '' A ∧ p.2 ∈ Set.Icc 0 1} := by
      intro x hx
      simp only [Set.mem_image, Set.mem_setOf_eq]
      obtain h1 | h2 := Set.mem_setOf.1 hx
      · exact Or.symm (Or.inr h1)
      · right
        refine ⟨?_, h2.2 ⟩
        use x.1
        exact ⟨h2.1, rfl⟩
    have maps1 : Set.MapsTo (fun (p: Y × ℝ) ↦ r (f_inv p.1, p.2)) {y | y.2 ∈ Set.Icc 0 1} {x | x.2 = 0 ∨ x.1 ∈ A ∧ x.2 ∈ Set.Icc 0 1} := by
      refine Set.MapsTo.comp hr.2.1 ?_
      intro y hy
      simp only [ Set.mem_setOf_eq, Set.mem_setOf.1 hy]
    have := Set.MapsTo.comp maps2 maps1
    rw [Function.comp_def] at this
    exact this
  · intro b
    unfold r'
    have :(f_inv b.1.1, b.1.2) ∈  {p | p.2 = 0 ∨ p.1 ∈ A ∧ p.2 ∈ Set.Icc 0 1} := by
      simp only [Set.mem_setOf_eq]
      by_cases h : b.1.2 = 0
      · exact Or.inl h
      · right
        have := b.prop
        simp only [Set.mem_setOf, Set.mem_setOf_eq, h, false_or] at this
        simp only [this.2, and_true]
        exact (Set.mem_image_iff_of_inverse hf1 hf2).mp this.1
    have := hr.2.2 ⟨(f_inv b.1.1, b.1.2), this⟩
    rw[this]
    grind

-- partial homeomorph -> Hannah

variable {m : ℕ}

def fun_euclid_max : EuclideanSpace ℝ (Fin m) → (Fin m → ℝ) := fun p ↦ p
def fun_max_euclid : (Fin m → ℝ) → EuclideanSpace ℝ (Fin m) := fun p ↦ { ofLp := p }

lemma left_inverse_euclid_max : Function.LeftInverse (@ fun_euclid_max m) (@ fun_max_euclid m )  := by
  intro x
  simp[fun_euclid_max, fun_max_euclid]

lemma right_inverse_euclid_max : Function.RightInverse (@ fun_euclid_max m) (@ fun_max_euclid m )  := by
  intro x
  simp[fun_euclid_max, fun_max_euclid]

lemma bij_euclid_max : Function.Bijective (@fun_euclid_max m) := by
  refine Function.bijective_iff_has_inverse.mpr ?_
  use fun_max_euclid
  refine ⟨right_inverse_euclid_max , left_inverse_euclid_max⟩

lemma IsOpen_euclid_max : IsOpenMap (@fun_euclid_max m) := by
  refine IsOpenMap.of_inverse ?_ left_inverse_euclid_max right_inverse_euclid_max
  unfold fun_max_euclid
  fun_prop

lemma Continuous_euclid_max : Continuous (@fun_euclid_max m) := by
  fun_prop

lemma homeo_euclid_max : IsHomeomorph (@fun_euclid_max m) := by
  refine ⟨ Continuous_euclid_max, IsOpen_euclid_max , bij_euclid_max ⟩

lemma closed_embedding_euclid_max : Topology.IsClosedEmbedding (@fun_euclid_max m) := by
  refine ⟨?_, ?_ ⟩
  · refine ⟨ { eq_induced := rfl }, ?_⟩
    refine Function.HasLeftInverse.injective ?_
    use fun_max_euclid
    exact right_inverse_euclid_max
  · have : Set.range (@fun_euclid_max m) = ⊤ := by
      ext x
      constructor
      · tauto
      · intro hx
        use WithLp.toLp 2 x
        simp[fun_euclid_max]
    rw[this]
    exact closure_subset_iff_isClosed.mp fun ⦃a⦄ a_1 ↦ trivial

lemma closure_hG_cosed : closure (@fun_euclid_max m '' closedBall 0 1) = (fun_euclid_max '' closedBall 0 1) := by
    refine closure_eq_iff_isClosed.mpr ?_
    exact  (Topology.IsClosedEmbedding.isClosed_iff_image_isClosed closed_embedding_euclid_max).mp isClosed_closedBall

lemma interior_hG : interior (@fun_euclid_max m '' closedBall 0 1) = fun_euclid_max '' (interior (closedBall 0 1)) := by
  obtain ⟨a, ha⟩  := isHomeomorph_iff_exists_homeomorph.1 (@homeo_euclid_max m)
  rw[← ha]
  exact (Homeomorph.image_interior a (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)).symm

lemma boundary_hG : frontier (@fun_euclid_max m '' closedBall 0 1) = fun_euclid_max '' (frontier (closedBall 0 1)) := by
  rw [show
      frontier (fun_euclid_max '' closedBall 0 1) =
        closure (fun_euclid_max '' closedBall 0 1) \ interior (fun_euclid_max '' closedBall 0 1)
      from rfl]
  rw[closure_hG_cosed, interior_hG, ← Set.image_diff bij_euclid_max.injective (closedBall 0 1) (interior (closedBall 0 1)),
    ← IsClosed.frontier_eq isClosed_closedBall]


lemma euclid_max_MapsTo_ball : (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1).MapsTo  fun_euclid_max (closedBall 0 1) := by
  intro x hx
  refine mem_closedBall_zero_iff.mpr ?_
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs]
  simp only [zero_le_one, EuclideanSpace.closedBall_zero_eq, one_pow] at hx
  rw [← sq_le_one_iff_abs_le_one, show fun_euclid_max x i = x.ofLp i from rfl]
  rw [Set.mem_setOf] at hx
  refine le_trans ?_ hx
  rw [← Finset.sum_attach Finset.univ fun x_1 ↦ x.ofLp x_1 ^ 2]
  have hf : ∀ j ∈ Finset.univ.attach, 0 ≤ x.ofLp j.1  ^ 2 := by
    intro j  hj
    positivity
  let ij : Finset.univ.attach := {
    val := ⟨ i, by simp⟩
    property := by simp }
  have : i = ij.1 := by
    simp[ij]
  rw[this]
  apply Finset.single_le_sum hf
  simp


lemma convex_euclid_to_max_ball : Convex ℝ (fun_euclid_max '' (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)) := by
  refine Convex.is_linear_image (convex_closedBall 0 1) ?_
  exact { map_add := fun x ↦ congrFun rfl, map_smul := fun c ↦ congrFun rfl }

lemma nonempty_euclid_to_max_ball : (interior (fun_euclid_max '' (closedBall (0 :EuclideanSpace ℝ (Fin m)) 1))).Nonempty := by
  use 0
  rw [mem_interior]
  use fun_euclid_max '' ball 0 1
  refine ⟨ Set.image_mono  ball_subset_closedBall , IsOpen_euclid_max (ball 0 1) isOpen_ball , ?_ ⟩
  use 0
  refine ⟨mem_ball_self zero_lt_one, by rfl ⟩

lemma bounded_euclid_to_max_ball : Bornology.IsBounded (fun_euclid_max '' (closedBall (0 :EuclideanSpace ℝ (Fin m)) 1)) :=
  Bornology.isBounded_induced.mp isBounded_closedBall



lemma HEP_cube : ∀ (m : ℕ), m ≥ 0 →
    HEP_neu (closedBall (0 : (Fin m → ℝ)) 1) (Metric.sphere ⟨0, by simp⟩ 1) := by
  intro m hm
  obtain ⟨G, hG_int, hG_closed, hG_frontier⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall convex_euclid_to_max_ball
    nonempty_euclid_to_max_ball bounded_euclid_to_max_ball
  let f : (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) → (closedBall (0 : (Fin m → ℝ)) 1) := fun p ↦ ⟨G (fun_euclid_max p.1), by
    rw[← hG_closed]
    simp only [Set.mem_image, EmbeddingLike.apply_eq_iff_eq, exists_eq_right]
    refine closure_induced.mp ?_
    rw [IsClosed.closure_eq]
    · exact p.2
    · exact isClosed_closedBall
    ⟩
  rw [closure_hG_cosed ] at hG_closed
  rw [interior_hG] at hG_int

  have bij_comp : Function.Bijective (G ∘ fun_euclid_max) :=
    (EquivLike.comp_bijective fun_euclid_max G).mpr bij_euclid_max
  have bijOn_com : Set.BijOn (G ∘ fun_euclid_max) (closedBall 0 1) (closedBall 0 1) := by
    refine Set.BijOn.mk ?_ ?_ ?_
    · rw [Set.mapsTo_iff_image_subset]
      have := (Eq.subset hG_closed)
      grind
    · exact Function.Injective.injOn (Function.Bijective.injective bij_comp)
    · rw[Set.surjOn_comp_iff]
      exact (Set.image_eq_iff_surjOn_mapsTo.1 hG_closed).1
  have bij_f : f.Bijective := by
    refine ⟨?_ , ?_ ⟩
    · intro a1 a2 heq
      simp only [Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq, f] at heq
      exact SetCoe.ext ((@homeo_euclid_max m).injective heq)
    · rintro ⟨b, hb⟩
      obtain ⟨a, ha, ha_map⟩ := bijOn_com.2.2 hb
      use ⟨a, ha⟩
      simp only [Subtype.mk.injEq, f]
      exact List.ofFn_inj.mp (congrArg List.ofFn ha_map)
  have f_sphere : f '' (sphere ⟨0, mem_closedBall_self zero_le_one⟩ 1) = sphere ⟨0, by simp⟩ 1 := by
    refine Set.SurjOn.image_eq_of_mapsTo ?_ ?_
    · intro b hb
      rw [boundary_hG, frontier_closedBall 0 one_ne_zero, Set.image_image] at hG_frontier
      rw[mem_sphere, Subtype.dist_eq,dist_zero_right, ← mem_sphere_zero_iff_norm, ← hG_frontier] at hb
      obtain ⟨a, ha_mem, ha_maps⟩ := hb
      use ⟨a, Metric.sphere_subset_closedBall ha_mem⟩
      exact ⟨mem_sphere.mpr ha_mem , SetCoe.ext ha_maps⟩
    · intro a ha
      have f_a : fun_euclid_max a.1 ∈ frontier (fun_euclid_max '' closedBall 0 1) := by
        refine (mem_frontier_iff_notMem_interior ?_).mpr ?_
        · simp only [Set.mem_image, mem_closedBall, dist_zero_right]
          use a
          refine ⟨?_, by rfl ⟩
          rw [← mem_closedBall_zero_iff]
          exact mem_closedBall.mpr (Metric.sphere_subset_closedBall ha)
        · rw[interior_hG]
          intro a_mem
          rw [Function.Injective.mem_set_image bij_euclid_max.injective, interior_closedBall 0 one_ne_zero, mem_ball] at a_mem
          rw [mem_sphere, Subtype.dist_eq] at ha
          exact (lt_self_iff_false 1).mp (Eq.trans_lt ha.symm a_mem)
      have G_f_a : G (fun_euclid_max a.1) ∈ sphere 0 1 := by
        rw[← hG_frontier]
        simp [f_a]
      exact mem_sphere.mpr G_f_a
  rw[← f_sphere]
  apply homeomorph_HEP _ _ (isClosed_sphere) (by sorry)  (zweizweiacht' m hm)
  constructor
  · fun_prop
  · obtain ⟨ f_inv , hf1, hf2 ⟩ := (Function.bijective_iff_has_inverse).1 bij_f
    refine IsOpenMap.of_inverse ?_ hf2 hf1
    let comp' : (Fin m → ℝ) → EuclideanSpace ℝ (Fin m) := fun_max_euclid ∘ G.invFun
    have cont_comp' : Continuous comp' := by
      refine Continuous.comp ?_ G.continuous_invFun
      unfold fun_max_euclid
      fun_prop
    have contOn_comp' : ContinuousOn comp' (closedBall 0 1) := Continuous.continuousOn cont_comp'
    have : ∀ (x :  Fin m → ℝ ), (hx : x ∈ closedBall 0 1) →  comp' x =  f_inv  ⟨x, hx⟩  := by
      intro x hx
      unfold comp'
      rw [← exists_subtype_mk_eq_iff]
      have : (fun_max_euclid ∘ G.invFun) x ∈ closedBall 0 1 := by sorry
      use this
      simp only [Equiv.invFun_as_coe, Homeomorph.coe_symm_toEquiv, Function.comp_apply]
      apply bij_f.injective
      rw [Subtype.mk_eq_mk]
      sorry
    sorry
    /-
    intro U hU
    apply isOpen_induced_iff.2
    rw[isOpen_induced_iff] at hU
    obtain ⟨ U_euc, ⟨U_euc_open, U_euc2_preim⟩ ⟩ := hU
    use (G ∘ fun_euclid_max) '' U_euc
    refine ⟨?_ , ?_ ⟩
    · exact IsOpenMap.comp (Homeomorph.isOpenMap G) IsOpen_euclid_max U_euc U_euc_open
    · simp only [Function.comp_apply]
      ext x
      constructor
      · intro hx
        --refine (Set.mem_image Subtype.val (f '' U) x).mpr ?_
        --use ⟨ x, hx.1⟩
        --refine ⟨?_, by simp⟩
        --simp only [Set.mem_image, Subtype.mk.injEq, Subtype.exists, f]
        sorry
      · sorry
      /-
      ext x
      constructor
      · intro hx
        simp only [Set.mem_preimage, Set.mem_image] at hx
        obtain ⟨y, hy⟩ := hx
        simp only [Set.mem_image, Subtype.exists]
        use y
        refine ⟨ ?_, ?_, ?_⟩
        · sorry
        · have x_im := Set.mem_of_mem_of_subset (Subtype.coe_prop x) (Eq.subset hG_closed.symm)
          rw[closure_hG_cosed, hy.2.symm, Set.mem_image] at x_im
          obtain ⟨v, hv⟩ := x_im
          --have : Function.Bijective G := Homeomorph.bijective G



          sorry
        · unfold f
          simp [hy.2]
        -/

    /-
    refine IsOpenMap.subtype_mk ?_ ?_  -- dabei geht der Ball im codomain verlohren und es ist nocht mehr open
    -- das ist de Weg über die composition, aber dann ist die zweite map nicht auf dem closed ball open ...
    refine IsOpenMap.comp ?_ ?_
    · sorry
    · have := @IsOpen_euclid_max m
      sorry-/ -/
  · exact bij_f






  -- apply (homeomorph_HEP f (Metric.sphere ⟨0, by simp⟩ 1) (zweizweiacht' m hm))



/-


  let f : (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) → (closedBall (0 : (Fin m → ℝ)) 1) := fun p ↦ ⟨p, by
    refine mem_closedBall_zero_iff.mpr ?_
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_eq_abs]
    have p_prop := p.prop
    simp only [zero_le_one, EuclideanSpace.closedBall_zero_eq, one_pow, Set.mem_setOf_eq] at p_prop
    rw [← sq_le_one_iff_abs_le_one]
    rw [ ← Finsupp.univ_sum_single_apply' i ((p.1).ofLp i ^ 2)]
    have :  ∑ a ∈ {x | x = i }.toFinset, ((p.1).ofLp a ^ 2) = ∑ j, (Finsupp.single j ((p.1).ofLp i ^ 2)) i := by
      sorry
    rw[← this]
    have : ∑ a ∈ {x | x = i }.toFinset, ((p.1).ofLp a ^ 2) ≤ ∑ x, (p.1).ofLp x ^ 2 :=
      Finset.sum_le_univ_sum_of_nonneg (by simp [sq_nonneg])
    --by_contra h
    --simp only [Real.norm_eq_abs, ge_iff_le, not_le] at h
    --rw [← one_lt_sq_iff_one_lt_abs] at h
    sorry
    ⟩
  -- have Im_f_: Convex ℝ (f '' (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)) := by sorry
  have Im_f_non : Nonempty (interior (f '' (Metric.closedBall ⟨0, by sorry⟩  1))) := by sorry
  have f_sphere : f '' (Metric.sphere ⟨0, by simp⟩ 1) = (Metric.sphere ⟨0, by simp⟩ 1) := by sorry
  rw[← f_sphere]
  apply (homeomorph_HEP f (Metric.sphere ⟨0, by simp⟩ 1) (zweizweiacht' m hm)) -- nicht f
  constructor
  · fun_prop
  · unfold f
    sorry
  · sorry -/



#check exists_homeomorph_image_interior_closure_frontier_eq_unitBall
  -- wenn es einfacher ist eine andere kompakte bounded Menge zu bekommen,
  -- dann kann ich innerhalb eines Raum homeomorph zum unit Ball werden



/-
 have h_interior : (interior (Metric.closedBall (0 : (Fin m → ℝ)) 1)).Nonempty := by
    sorry
  obtain ⟨w, hw_int, hw_clos, hw_front⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall (convex_closedBall 0 1) h_interior isBounded_closedBall

-/
-- (Metric.sphere ⟨0, by simp⟩ 1)
