import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
set_option linter.style.longLine false
open Classical  -- muss hier was hin?
universe u

def fH_agreeOn_A {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (H : X × ℝ → Y) (A : Set X) : Prop := ∀ (a : A), f a = H (a,0)

def HEP (X : Type u) [TopologicalSpace X] (A : Set X) : Prop :=
  ∀ (Y : Type u) [TopologicalSpace Y], ∀ (f : X → Y), ∀ (H : X × ℝ → Y),
  ContinuousOn f (@Set.univ X) → ContinuousOn H {p : X × ℝ | (p.1 ∈ A) ∧ (p.2 ∈ (Set.Icc (0 : ℝ) 1))} →
  (fH_agreeOn_A f H A)
  → ∃ (H' : X × ℝ → Y), ContinuousOn H' { p : X × ℝ | p.2 ∈ Set.Icc (0 : ℝ) 1} ∧
  ∀ (x : X), f x = H' (x, 0) ∧ ∀ (a : A) (t : Set.Icc (0 : ℝ) 1), H (a,t) = H' (a, t)


lemma Zweizweiacht: ∀ (m : ℕ), m ≥ 0 → HEP (Metric.closedBall (0 : (Fin m → ℝ)) 1) (Metric.sphere ⟨0, by simp⟩ 1):= by
  intro m hm Y hY f H hf hH h_agree
  -- hilfsfunktion h definieren
  let h : (Fin m → ℝ) → Y := fun p =>
    if hp : norm p ≤ 1 then f ⟨p, by simp[hp]⟩
    else H (⟨(‖p‖⁻¹ : ℝ) • p, by
      simp only [Metric.mem_closedBall, dist_zero_right]
      rw [norm_smul_of_nonneg (by rw [Right.inv_nonneg]; exact norm_nonneg p) p]
      exact inv_mul_le_one⟩, norm p - 1)
  -- die ist auf der disc with radius 2 continuous
  have h_cont : ContinuousOn h (Metric.closedBall 0 2) := by
    --apply ContinuousOn.if
    have : Metric.closedBall (0 : Fin m → ℝ) 2 = Metric.closedBall (0 : Fin m → ℝ) 1 ∪ {p : Fin m → ℝ | 1 ≤ dist 0 p ∧ dist 0 p ≤ 2} := by
      ext p
      simp only [Metric.mem_closedBall, dist_zero_right, dist_zero, Set.mem_union, Set.mem_setOf_eq]
      constructor
      · intro hp
        by_cases hp_case : ‖p‖ ≤ 1
        · left
          exact hp_case
        · right
          exact ⟨ Std.le_of_not_ge hp_case,  le_of_eq_of_le rfl hp⟩
      · intro hp
        obtain hp1 | hp2 := hp
        · exact le_trans hp1 (by norm_num)
        · exact hp2.2
    rw[this]
    refine ContinuousOn.union_of_isClosed ?_ ?_ Metric.isClosed_closedBall ?_
    · --unfold h
      have : ContinuousOn (fun (p : Fin m → ℝ) => f ⟨p, by sorry⟩) (Metric.closedBall 0 1) := sorry -- erstes sorry ist nicht lösbar
      refine ContinuousOn.congr_mono this ?_ ?_
      · sorry
      · sorry
    · sorry
    · exact IsClosed.and (isClosed_le (by fun_prop) (by fun_prop)) (isClosed_le (by fun_prop) (by fun_prop))
  -- use h to define the extended homotopy
  let H' : (Metric.closedBall (0 : (Fin m → ℝ)) 1) × ℝ → Y := fun p => h ((1 + p.2) • p.1)
  use H'
  constructor --  H' is continuous and agrees with f or H, where defined
  · refine ContinuousOn.comp h_cont (by fun_prop) ?_
    intro x hx
    simp only [Metric.mem_closedBall, dist_zero_right]
    -- (ab hier eigentlich nur noch kleine Ungleichungen)
    rw [norm_smul (1 + x.2) x.1.val, Eq.symm (mul_one 2)]
    refine mul_le_mul_of_nonneg ?_ (mem_closedBall_zero_iff.mp x.1.prop) (norm_nonneg (1 + x.2)) (by positivity)
    rw [← one_add_one_eq_two]
    refine norm_add_le_of_le (by norm_num) ?_
    simp only [Real.norm_eq_abs, abs_le]
    exact ⟨le_trans (by norm_num) hx.1, hx.2 ⟩
  · intro x
    constructor
    · simp [H', h, mem_closedBall_zero_iff.mp x.prop] -- agrees with f
    · intro a t -- agrees with H
      unfold H' h
      by_cases h : t.val = 0 -- cases : H' defined via f and  H' defined via H
      · have : ‖(1 + t.val) • a.val.1‖ ≤ 1 := by
          simp only [h, add_zero, one_smul]
          rw [← mem_closedBall_zero_iff]
          exact Set.mem_of_mem_of_subset a.prop (@Metric.sphere_subset_closedBall _ _ (0 : (Fin m → ℝ)) 1)
        specialize h_agree ⟨a, a.prop⟩
        simp [this]
        simp [h, h_agree] ----> simps können nicht zusammen geschrieben werden ?!
      · simp only
        have norm_auu: norm a.val.1 = 1 := by
          -- is that true --> max-norm
          sorry
        have h_if : ¬ (‖(1 + t.val) • a.val.1‖ ≤  1) := by
          simp only [norm_smul, norm_auu, Real.norm_eq_abs, mul_one, not_le]
          grind
        -----> tactic, which compares the left and the right argument of H ?
        have h_t : ‖(1 + t.val) • ↑a.val.1‖ - 1 = t.val := by
          rw [norm_smul_of_nonneg (add_nonneg (by positivity) t.prop.1) a.val.1, one_add_mul t.val ‖a.val.1‖]
          have := a.prop
          rw [Metric.mem_sphere'] at this
          simp [norm_auu]
        have h_a : ‖(1 + t.val) • a.val.1‖⁻¹ • (1 + t.val) • a.val.1 = a.val.1 := by
          have : |1 + t.val|⁻¹ * (1 + t) = 1 := (inv_mul_eq_one₀ (by grind)).mpr (by grind)
          simp [norm_smul, Real.norm_eq_abs, norm_auu, smul_smul, this]
        simp [h_if, h_t, h_a]



/-
Prop 2.29
If X is a space, which is obtained from A ⊆ X by attaching m-cells, then the pair (X,A) has the HEP
-/


/-- The source of every characteristic map of dimension `n` is
  `(ball 0 1 : Set (Fin n → ℝ))`. -/
  --sphere 0 1
  --closedBall 0 1
lemma Zweizweisechs' {X : Type u} [TopologicalSpace X] {A : Set X} (hA : Nonempty A) :
    (∀ (Y : Type u) [TopologicalSpace Y] ( _ : Nonempty Y) (g : X → Y) , ContinuousOn g A → ∃ G : X → Y ,
    Continuous G ∧ ∀ a : A, g a = G a ) ↔ ∃ r : X → A, Continuous r ∧ ∀ a : A, r a = a := by
  constructor
  · intro h
    let g : X → A := fun p =>
      if hp : p ∈ A then ⟨p, hp⟩
      else Classical.choice hA
    have : ContinuousOn g A := by
      simp [g, continuousOn_iff_continuous_restrict, continuous_inclusion]
    obtain ⟨G, hG⟩ := h A hA g this
    use G
    constructor
    · exact hG.1
    · intro a
      grind
  · intro h Y hY1 hY2 g hg
    obtain ⟨r, hr ⟩ := h
    let G : X → Y := fun p => g (r p)
    use G
    constructor
    · unfold G
      apply ContinuousOn.comp_continuous ?_ ?_ ?_ -- komisch
      · use A
      · exact hg
      · exact Continuous.comp (by fun_prop) hr.1
      simp
    · intro a
      grind




/-
def homotopy_extension_probleme' {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X}
    (f : C(X, Y)) (H : C({p: A × ℝ // p.2 ∈ (Set.Icc (0 : ℝ) 1)}, Y)) : Prop :=
    ∀ (a : A), f a = H ⟨(a, 0), by simp⟩

def HEP' (X : Type u) [TopologicalSpace X] (A : Set X) : Prop :=
  ∀ (Y : Type u) [TopologicalSpace Y], ∀ (f : C(X, Y)),
  ∀ (H : C({p: A × ℝ // p.2 ∈ (Set.Icc (0 : ℝ) 1)}, Y)),
  homotopy_extension_probleme' f H
  → ∃ (H' : C({p: X × ℝ // p.2 ∈ (Set.Icc (0 : ℝ) 1)}, Y)),
  (∀ (x : X), f x = H' ⟨(x, 0), by simp⟩) ∧
  (∀ (a : A) (t : Set.Icc (0 : ℝ) 1), H ⟨(a, t), by simp⟩ = H' ⟨(a, t), by simp⟩)


lemma zweizweisechs' {X : Type u} [TopologicalSpace X] {A : Set X} :
  (∀ (Y : Type u) [TopologicalSpace Y] (g : C(A,Y)), ∃ (G : C(X,Y)), ∀ (a : A), G a = g a)
  ↔ ( ∃ (r : C(X, A)), ∀ (a : A), r a = a ) := by
  constructor
  · intro h
    obtain ⟨G, hG⟩ :=  h A (ContinuousMap.id A) -- universe u wird hier gebraucht
    use G
    apply hG
  · intro h Y hY g
    obtain ⟨r, hr⟩ := h
    use (⟨ g ∘ r, by refine Continuous.comp g.2 r.2⟩)
    intro a
    exact ContinuousMap.congr_arg g (hr a)


lemma zweizweisechs {X : Type u} [TopologicalSpace X] {A : Set X} :
  (∀ (Y : Type u) [TopologicalSpace Y] (g : X → Y) , ContinuousOn g A → ∃ G : X → Y ,
  ContinuousOn G (@Set.univ X)∧ ∀ a : A, g a = G a ) ↔ retract A := by
  constructor
  · intro h hAB
    have := h A (fun (a : A)  ↦ a)
    sorry
  · intro hr
    sorry


lemma zweizweisieben {X : Type u} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    HEP X A ↔ retract  { p : X × ℝ | p.2 ∈ (Set.Icc 0 1)} { p : X × ℝ | p.2 = 0 ∨ (p.1 ∈ A) ∧ p.2 ∈ (Set.Icc 0 1)} := by
  constructor
  · intro h_HEP
    apply zweizweisechs.1
    intro Y hY g hg
    obtain ⟨G, hG⟩ := zweizweifuenf_hin h_HEP Y g hg
    use G
  · intro hr
    refine zweizweifuenf_rueck hA ?_
    intro Y hY g hg
    obtain ⟨G, hG⟩ := zweizweisechs.2 hr Y g hg
    use G

-/


/-
  "Corollary 2.25" for closed:  Let A be a closed subset of a topological space X.
  Then A ⊆ X has the HEP ↔
  for every topological space Y and every continuous map g: (X × {0}) ∪ (A × [0,1]) → Y there
  exists an extension of g to a map G : X × [0,1] → Y:
-/
-- (Hinrichtung geht auch ohne A closed)
lemma Zweizweifuenf_hin {X : Type u} [TopologicalSpace X] {A : Set X} :
    HEP X A →  ∀ (Y : Type u) [TopologicalSpace Y],
    ∀ (g :  X × ℝ → Y ), ContinuousOn g {p : X × ℝ | p.2 = 0 ∨ (p.1 ∈ A) ∧ p.2 ∈ (Set.Icc (0 : ℝ) 1)} →
    ∃ (G :  X × ℝ → Y), ContinuousOn G {p : X × ℝ | p.2 ∈ Set.Icc 0 1}
    ∧ ∀ (q : {p : X × ℝ | p.2 = 0 ∨ (p.1 ∈ A) ∧ p.2 ∈ (Set.Icc (0 : ℝ) 1)}), g q = G q.1 := by
  intro h_HEP Y hY g hg
  let f : X → Y := fun x ↦ g (x,0)
  let H : X × ℝ → Y := fun p ↦ g p
  have hf : ContinuousOn f Set.univ := ContinuousOn.comp hg (by fun_prop) (by simp)
  have hH : ContinuousOn H {p | p.1 ∈ A ∧ p.2 ∈ Set.Icc 0 1} := by
    unfold H
    exact ContinuousOn.congr_mono  hg (by simp [Set.EqOn]) (by grind)
  have h_agree : fH_agreeOn_A f H A := by
    intro a
    unfold f H
    rfl
  obtain ⟨G, ⟨ hG_cont, hG⟩⟩ := h_HEP Y f H hf hH h_agree
  use G
  constructor
  · exact hG_cont
  · intro q
    cases q.prop with
    | inl h0 => grind
    | inr hA => apply (hG q.val.1).2 ⟨q.val.1 , hA.1⟩ ⟨q.val.2 , hA.2⟩

lemma Zweizweifuenf_rueck {X : Type u} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
   (∀ (Y : Type u) [TopologicalSpace Y], ∀ (g :  X × ℝ → Y ),
    ContinuousOn g {p : X × ℝ | p.2 = 0 ∨ (p.1 ∈ A) ∧ p.2 ∈ (Set.Icc (0 : ℝ) 1)} →
   (∃ (G :  X × ℝ → Y), ContinuousOn G {p : X × ℝ | p.2 ∈ Set.Icc 0 1}
    ∧ ∀ (q : {p : X × ℝ | p.2 = 0 ∨ (p.1 ∈ A) ∧ p.2 ∈ (Set.Icc (0 : ℝ) 1)}), g q = G q.1)) →  HEP X A  := by
  intro h_extend Y hY f H hf hH h_agree
  let g : X × ℝ → Y := fun q =>
    if h : q.2 = 0 then f q.1
    else H q
  have hg: ContinuousOn g {p | p.2 = 0 ∨ (p.1 ∈ A ∧ p.2 ∈ Set.Icc 0 1)} := by
    refine ContinuousOn.union_of_isClosed ?_ ?_ ?_ ?_
    · unfold g
      simp only [dite_eq_ite]
      have : ContinuousOn (fun q ↦ if q.2 = 0 then f q.1 else H q) fun p ↦ p.2 = 0 =
        ContinuousOn (fun q ↦ if q.2 = 0 then f q.1 else H q) {p : X × ℝ | p.2 = 0} := rfl
      rw[this]
      have : ContinuousOn (fun q ↦ if q.2 = 0 then f q.1 else H q) {p | p.2 = 0} =
          ContinuousOn (fun (q : X × ℝ ) ↦ f q.1)  {p | p.2 = 0} := by
        simp only [eq_iff_iff]
        refine continuousOn_congr ?_
        intro p hp
        grind -- grind weg ?!
      rw[this]
      exact ContinuousOn.comp hf (by fun_prop) (Set.mapsTo_univ Prod.fst {p | p.2 = 0})
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
          specialize h_agree ⟨p.1, by grind⟩ -- grind weg
          rw[h_agree ]
          exact (congrArg H ∘ congrArg (Prod.mk p.1)) (id (Eq.symm h))
        · exact if_neg h
      rw[this]
      refine ContinuousOn.comp hH (by fun_prop) ?_
      exact Set.mapsTo_iff_subset_preimage.mpr fun ⦃a⦄ a_1 ↦ a_1
    · refine isClosed_eq (by fun_prop) (by fun_prop)
    · have : IsClosed (fun (p : X × ℝ ) ↦ p.1 ∈ A ∧ p.2 ∈ Set.Icc 0 1) ↔ IsClosed { p : X × ℝ | p.1 ∈ A ∧ p.2 ∈ Set.Icc 0 1} := Eq.to_iff rfl
      rw[this]
      refine IsClosed.and ?_ ?_
      · have : { x : X × ℝ | x.1 ∈ A} = {x : X | x ∈ A } ×ˢ { a : ℝ | true} := by grind
        rw[this]
        exact IsClosed.prod (isClosed_coinduced.mpr hA_closed) (isClosed_const)
      · refine IsClosed.and ?_ ?_
        · refine isClosed_le (by fun_prop) (by fun_prop)
        · refine isClosed_le (by fun_prop) (by fun_prop)
  obtain ⟨G, hG⟩ := h_extend Y g hg
  use G
  refine ⟨hG.1, ?_ ⟩
  intro x
  constructor
  · unfold g at hG
    have := hG.2 ⟨(x,0), by simp⟩
    -- hier grind macht es auch schon fertig.
    rw [dif_pos (EReal.coe_eq_zero.mp rfl)] at this
    exact this
  · intro a t
    unfold g at hG
    by_cases h : t.1 = 0
    · obtain ⟨hG_cont , hG1⟩ := hG
      specialize hG1 ⟨(a,t), by grind⟩
      have : G (a, t) = f a := by grind
      specialize h_agree ⟨a, by grind⟩
      rw [this, h]
      exact h_agree.symm
    · obtain ⟨hG_cont , hG1⟩ := hG
      specialize hG1 ⟨ (a,t), by grind⟩ -- grind weg ?
      grind



lemma Zweizweisechs {X : Type u} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) (hA : Nonempty A) :
    (∀ (Y : Type u) [TopologicalSpace Y] ( _ : Nonempty Y) (g : X → Y) , ContinuousOn g A → ∃ G : X → Y ,
    ContinuousOn G B ∧ ∀ a : A, g a = G a ) ↔ ∃ r : B → A, Continuous r ∧ ∀ a : A, r ⟨a, hAB a.prop⟩ = a := by
  constructor
  · intro h
    let g : X → A := fun p =>
      if hp : p ∈ A then ⟨p, hp⟩
      else Classical.choice hA
    have : ContinuousOn g A := by
      simp [g, continuousOn_iff_continuous_restrict, continuous_inclusion]
    obtain ⟨G, hG⟩ := h A hA g this
    use B.restrict G
    rw [← continuousOn_iff_continuous_restrict]
    refine ⟨hG.1 , (by grind) ⟩
  · intro h Y hY_Top hY_choose g hg
    obtain ⟨r , hr⟩ := h
    let G : X → Y := fun p =>
      if hp : p ∈ B then g (r ⟨p, hp⟩)
      else Classical.choice hY_choose
    use G
    constructor
    · unfold G
      simp only [continuousOn_iff_continuous_restrict, Set.restrict_dite, Subtype.coe_eta]
      refine ContinuousOn.comp_continuous hg ?_ ?_
      · exact Continuous.comp continuous_subtype_val hr.1
      · simp
    · intro a
      grind

/-
lemma zweizweisieben {X : Type u} [TopologicalSpace X] {A : Set X} (hA1 : IsClosed A) (hA2 : Nonempty A) :
    HEP X A ↔
    (∃ (r : { p : X × ℝ | p.2 ∈ (Set.Icc 0 1)} → ({p : X × ℝ | p.2 = 0 ∨ (p.1 ∈ A) ∧ p.2 ∈ (Set.Icc 0 1)})),
    Continuous r ∧ ∀ a : ({p : X × ℝ | p.2 = 0 ∨ (p.1 ∈ A) ∧ p.2 ∈ (Set.Icc 0 1)}), r ⟨a, by grind⟩ = a ) := by  -- grind
  have hAB : {p : X × ℝ | p.2 = 0 ∨ p.1 ∈ A ∧ p.2 ∈ Set.Icc 0 1} ⊆ {p | p.2 ∈ Set.Icc 0 1} := by simp
  have h_choose : Nonempty {p : X × ℝ | p.2 = 0 ∨ p.1 ∈ A ∧ p.2 ∈ Set.Icc 0 1} := by
      refine nonempty_subtype.mpr ⟨((Classical.choice hA2).val, (0: ℝ)), by simp⟩
  constructor
  · intro h_HEP
    apply (zweizweisechs hAB h_choose).1
    intro Y hY1 hY2 g hg
    obtain ⟨G, hG ⟩ := zweizweifuenf_hin h_HEP Y g hg
    use G
  · intro h
    refine zweizweifuenf_rueck hA1 ?_
    intro Y hY g hg
    obtain ⟨G, hG⟩ := (zweizweisechs hAB h_choose).2 h Y (by sorry) g hg --> Y in zweizweifuenf_ruek muss nonempty sein
    use G -/

lemma zweizweiacht : ∀ (m : ℕ), m ≥ 0 → HEP_neu (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) (Metric.sphere ⟨0, by simp⟩ 1):= by
  intro m hm Y hY C f H hf_cont hf_mapsto hH_cont hH_mapsto hfH_agree
  let h : EuclideanSpace ℝ (Fin m) → Y := fun p =>
    if hp : norm p ≤ 1 then f ⟨p, by simp[hp]⟩
    else H (⟨(‖p‖⁻¹ : ℝ) • p, by apply inv_norm_smul_mem_unitClosedBall⟩, norm p - 1)
  let H' : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) × ℝ → Y := fun p => h ((1 + p.2) • p.1)
  use H'
  have domain_union : Metric.closedBall (0 :  EuclideanSpace ℝ (Fin m)) 2 = Metric.closedBall 0 1 ∪ {p : EuclideanSpace ℝ (Fin m) | 1 ≤ dist 0 p ∧ dist 0 p ≤ 2} := by
    ext x
    simp only [Set.mem_union, mem_closedBall, dist_zero_right, dist_zero, Set.mem_setOf_eq]
    grind
  have sphere_H' : ∀ (a : (Metric.sphere ⟨(0 : EuclideanSpace ℝ (Fin m)), Metric.mem_closedBall_self zero_le_one⟩ 1)) (t : (Set.Icc 0 1)), H (a, t) = H' (a.val, t.val) := by
    sorry
  --have sphere_h : ∀ (a : EuclideanSpace ℝ (Fin m)) (t : (Set.Icc 0 1)), (ha : norm ((1+t) • a) = 1 ) → h (a, by simp[ha] ) = f

  refine ⟨?_, ?_, ?_, ?_⟩
  · sorry
  · unfold H' h
    intro x hx
    by_cases hp : ‖(1 + x.2) • x.1.val‖ ≤ 1
    · simp only [hp, reduceDIte]
      exact Set.mem_preimage.mp (hf_mapsto trivial)
    · simp[hp]


      sorry
  · intro x
    simp [H', h, mem_closedBall_zero_iff.mp x.prop]
  · exact sphere_H'
