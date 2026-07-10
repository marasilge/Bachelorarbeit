import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Data.Set.Subset
import Mathlib.Topology.Basic


noncomputable section

universe u
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X}

/-
Definitions :
· f and H agree on the Set A × {0}, i.e. it makes sence to search for a function H' which agrees
  with f and H
· IsHomotopyExtension combines all the properties, which the extended Homotopy on X × [0,1] should
  have.
· Definition of the homotopy extension property.
-/

def agreeOn (f : X → Y) (H : X × ℝ → Y) (A : Set X) : Prop := ∀ (a : A), f a = H (a,0)

def HomotopyExtension (H' : X × ℝ → Y) (f : X → Y) (H : X × ℝ → Y) (A : Set X) (rangeH' : Set Y) :
    Prop :=
  ContinuousOn H' { p : X × ℝ | p.2 ∈ unitInterval} ∧
  { p : X × ℝ | p.2 ∈ unitInterval}.MapsTo H' rangeH'  ∧
  (∀ (x : X), f x = H' (x, 0)) ∧ (∀ (a : A) (t :unitInterval), H (a,t) = H' (a, t))

def HEPY (X : Type u) [TopologicalSpace X] (A : Set X) : Prop :=
  ∀ (Y : Type u) [TopologicalSpace Y] (rangeH' : Set Y), ∀ (f : X → Y), ∀ (H : X × ℝ → Y),
  Continuous f → Set.range f ⊆ rangeH' →
  ContinuousOn H {p : X × ℝ | (p.1 ∈ A) ∧ (p.2 ∈ (unitInterval))} →
  {p : X × ℝ | (p.1 ∈ A) ∧ (p.2 ∈ unitInterval)}.MapsTo H rangeH' → agreeOn f H A
  → ∃ (H' : X × ℝ → Y), HomotopyExtension H' f H A rangeH'

def HomotopyExtensionY (H' : X × ℝ → Y) (f : X → Y) (H : X × ℝ → Y) (A : Set X) :
    Prop :=
  ContinuousOn H' { p : X × ℝ | p.2 ∈ unitInterval} ∧
  (∀ (x : X), f x = H' (x, 0)) ∧ (∀ (a : A) (t :unitInterval), H (a,t) = H' (a, t))

def HEP (X : Type u) [TopologicalSpace X] (A : Set X) : Prop :=
  ∀ (Y : Type u) [TopologicalSpace Y], ∀ (f : X → Y), ∀ (H : X × ℝ → Y), Continuous f →
  ContinuousOn H {p : X × ℝ | (p.1 ∈ A) ∧ (p.2 ∈ (unitInterval))} → agreeOn f H A
  → ∃ (H' : X × ℝ → Y), HomotopyExtensionY H' f H A

open Classical in
lemma HEP_iff_HEPY (X : Type u) [TopologicalSpace X] (A : Set X) : HEPY X A ↔ HEP X A := by
  constructor
  · intro h Y hY f H hf hH hfH
    obtain ⟨H', hH' ⟩ := h Y (@Set.univ Y) f H hf (by simp) hH (by simp) hfH
    use H'
    exact ⟨hH'.1, hH'.2.2.1 , hH'.2.2.2 ⟩
  · intro h Y hY rangeH' f H hf1 hf2 hH1 hH2 hfH
    let fr : X → rangeH' := fun p ↦ ⟨f p, hf2 (Set.mem_range_self p)⟩
    by_cases hX : Nonempty X
    · have hrange : Nonempty rangeH' := by
        let x := Classical.choice hX
        use f x
        exact hf2 (Set.mem_range_self x)
      let Hr : X × ℝ → rangeH' := fun p ↦
        if hp : p ∈ {x | x.1 ∈ A ∧ x.2 ∈ unitInterval} then ⟨H p, hH2 hp⟩
        else Classical.choice hrange
      have Hr_continuousOn : ContinuousOn Hr {x | x.1 ∈ A ∧ x.2 ∈ unitInterval} := by
        rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
        refine hH1.congr ?_
        intro p hp
        have hval : Hr p = ⟨H p, hH2 hp⟩ := dif_pos hp
        rw [Function.comp_apply, hval]
      have agree_r : agreeOn fr Hr A := by
        intro a
        simp only [Set.mem_Icc, Set.mem_setOf_eq, a.prop, Std.le_refl, zero_le_one, and_self,
          ↓reduceDIte, Subtype.mk.injEq, fr, Hr]
        exact hfH a
      obtain ⟨H', hH1', hH2', hH3'⟩  := h rangeH' fr Hr (by fun_prop) Hr_continuousOn agree_r
      let H'Y : X × ℝ → Y := fun p ↦ H' p
      use H'Y
      refine ⟨by fun_prop, ?_ , ?_ , ?_ ⟩
      · intro x hx
        exact Subtype.coe_prop (H' x)
      · intro x
        have := hH2' x
        rw [← SetCoe.ext_iff] at this
        exact this
      · intro a t
        have := hH3' a t
        rw [← SetCoe.ext_iff] at this
        simp only [Hr, Set.mem_setOf_eq, a.prop, true_and, t.prop, ↓reduceDIte] at this
        exact this
    · rw [not_nonempty_iff] at hX
      obtain ⟨H', hH1', hH2', hH3'⟩ := h Y f H hf1 hH1 hfH
      use H'
      refine ⟨hH1', ?_ , hH2' , hH3'⟩
      have : {p : X × ℝ | p.2 ∈ unitInterval} = ∅ := by
        have := @Prod.isEmpty_left X ℝ hX
        rw [← Set.univ_eq_empty_iff] at this
        exact  Set.subset_eq_empty (Set.setOf_subset.mpr fun x a ↦ trivial) this
      rw[this]
      exact (Set.mapsTo_empty H' rangeH')

open Set.Notation
def HEP' {Y : Type*} [TopologicalSpace Y] (X C : Set Y) : Prop := HEP X (X ↓∩ C)

lemma HEP_HEP' {Y : Type*} [TopologicalSpace Y] (X : Set Y) (A : Set X) :
    HEP (Set.Elem X) A ↔ HEP' X (Subtype.val '' A) := by
  unfold HEP'
  rw [Set.preimage_val_image_val_eq_self]

-- The pair (X,X) has the HEP :

example : HEP X (@Set.univ X) := by
  intro Y hY f H hf hH hAgree
  use H
  refine ⟨?_, ?_ ,?_ ⟩
  · rw [← Set.sep_univ]
    exact hH
  · intro x
    exact hAgree ⟨x, by tauto⟩
  · intro a t
    rfl

-- The pair (X, ∅ ) has the HEP:

lemma HEP_empty : HEP X ∅ := by
  intro Y hY f H hf hH hAgree
  let H' : X × ℝ → Y := fun (x,t) ↦ f x
  use H'
  refine ⟨?_, ?_ ,?_ ⟩
  · exact Continuous.continuousOn (Continuous.fst' hf)
  · intro x
    rfl
  · simp only [H', Subtype.forall, IsEmpty.forall_iff,]


/-
  "Corollary 2.25" for closed:  Let A be a closed subset of a topological space X.
  Then A ⊆ X has the HEP ↔
  for every topological space Y and every continuous map g: (X × {0}) ∪ (A × [0,1]) → Y there
  exists an extension of g to a map G : X × [0,1] → Y:
-/

-- (Hinrichtung, die geht auch ohne A closed)

lemma if_HEP_then_extension :
    HEP X A →  ∀ (Y : Type u) [TopologicalSpace Y] (rangeH' : Set Y), ∀ (g :  X × ℝ → Y ),
    ContinuousOn g {p : X × ℝ | p.2 = 0 ∨ (p.1 ∈ A) ∧ p.2 ∈ unitInterval} →
    {p : X × ℝ | p.2 = 0 ∨ (p.1 ∈ A) ∧ p.2 ∈ unitInterval}.MapsTo g rangeH' →
    ∃ (G :  X × ℝ → Y), ContinuousOn G {p : X × ℝ | p.2 ∈ unitInterval} ∧
    {p : X × ℝ | p.2 ∈ unitInterval}.MapsTo G rangeH' ∧
    ∀ (q : {p : X × ℝ | p.2 = 0 ∨ (p.1 ∈ A) ∧ p.2 ∈ unitInterval}), g q = G q.val := by
  intro hHEP Y hY rangeH' g hg1 hg2
  let f : X → Y := fun x ↦ g (x,0)
  let H : X × ℝ → Y := fun p ↦ g p
  have hf : Continuous f := ContinuousOn.comp_continuous hg1 (Continuous.prodMk_left 0) (by simp)
  have hH : ContinuousOn H {p | p.1 ∈ A ∧ p.2 ∈ unitInterval} := by
    unfold H
    exact ContinuousOn.congr_mono hg1 (by simp [Set.EqOn]) (by grind)
  have h_agree : agreeOn f H A := by
    intro a
    simp [f, H]
  have hf_range : Set.range f ⊆ rangeH'  := by
    refine Set.mapsTo_univ_iff_range_subset.mp ?_
    intro x hx
    exact hg2 (by simp)
  have hH_mapsto : Set.MapsTo H {p | p.1 ∈ A ∧ p.2 ∈ unitInterval} rangeH' := by
    intro x hx
    simp only [H]
    exact hg2 (by grind)
  obtain ⟨G, ⟨hG_cont, hG⟩⟩ := hHEP Y rangeH' f H hf hf_range hH hH_mapsto h_agree
  refine ⟨G, hG_cont , hG.1 , ?_ ⟩
  intro q
  cases q.prop with
  | inl h0 => grind
  | inr hA => exact hG.2.2 ⟨q.val.1, hA.1⟩ ⟨ q.val.2, hA.2⟩

-- Rückrichtung:

def g (f : X → Y) (H : X × ℝ → Y) : X × ℝ → Y := fun q =>
  if q.2 = 0 then f q.1
  else H q

lemma continuousOn_g (A : Set X) (hA : IsClosed A) (f : X → Y) (H : X × ℝ → Y) (hf1 : Continuous f)
  (hH1 : ContinuousOn H {p | p.1 ∈ A ∧ p.2 ∈ unitInterval}) (hAgree : agreeOn f H A) :
    ContinuousOn (@g X Y f H)  { p : X × ℝ | p.2 = 0 ∨ (p.1 ∈ A ∧ p.2 ∈ unitInterval) } := by
  refine ContinuousOn.union_of_isClosed ?_ ?_ (isClosed_eq continuous_snd continuous_const) ?_
  · have h: ContinuousOn (fun q ↦ if q.2 = 0 then f q.1 else H q) {p | p.2 = 0} =
        ContinuousOn (fun (q : X × ℝ ) ↦ f q.1) {p | p.2 = 0} := by
      rw [eq_iff_iff]
      refine continuousOn_congr ?_
      intro p hp
      exact if_pos hp
    unfold g
    rw [show ContinuousOn (fun q ↦ if q.2 = 0 then f q.1 else H q) fun p ↦ p.2 = 0 =
      ContinuousOn (fun q ↦ if q.2 = 0 then f q.1 else H q) {p : X × ℝ | p.2 = 0} by rfl, h]
    exact Continuous.comp_continuousOn' hf1 continuousOn_fst
  · have : ContinuousOn (g f H) (fun p ↦ p.1 ∈ A ∧ p.2 ∈ unitInterval)
      = ContinuousOn (g f H) { p : X × ℝ | p.1 ∈ A ∧ p.2 ∈ unitInterval} := rfl
    rw [this]
    have : ContinuousOn (g f H) {p | p.1 ∈ A ∧ p.2 ∈ unitInterval} =
        ContinuousOn (fun (q : X × ℝ ) ↦ H q) {p | p.1 ∈ A ∧ p.2 ∈ unitInterval} := by
      unfold g
      rw [eq_iff_iff]
      refine continuousOn_congr ?_
      intro p hp
      by_cases h : p.2 = 0
      · specialize hAgree ⟨p.1, hp.1⟩
        rw [ite_eq_right_iff, hAgree]
        intro h'
        exact (congrArg H ∘ congrArg (Prod.mk p.1)) (id (Eq.symm h))
      · exact if_neg h
    rw[this]
    exact ContinuousOn.comp hH1 (by fun_prop) (Set.mapsTo_iff_subset_preimage.mpr fun a a_1 ↦ a_1)
  · refine IsClosed.and ?_ ?_
    · have : { x : X × ℝ | x.1 ∈ A} = {x : X | x ∈ A } ×ˢ { a : ℝ | true} :=  by
        ext
        grind
      rw[this]
      exact IsClosed.prod (isClosed_coinduced.mpr hA) (isClosed_const)
    · exact IsClosed.and
        (isClosed_le continuous_const continuous_snd) (isClosed_le continuous_snd continuous_const)

lemma if_extension_then_HEP (hA : IsClosed A) :
    ( ∀ (Y : Type u) [TopologicalSpace Y] (rangeH' : Set Y),
    ∀ (g :  X × ℝ → Y ), ContinuousOn g {p : X × ℝ | p.2 = 0 ∨ (p.1 ∈ A) ∧ p.2 ∈ unitInterval} →
    {p : X × ℝ | p.2 = 0 ∨ (p.1 ∈ A) ∧ p.2 ∈ unitInterval}.MapsTo g rangeH' →
    ∃ (G :  X × ℝ → Y), ContinuousOn G {p : X × ℝ | p.2 ∈ unitInterval} ∧
    {p : X × ℝ | p.2 ∈ unitInterval}.MapsTo G rangeH' ∧
    ∀ (q : {p : X × ℝ | p.2 = 0 ∨ (p.1 ∈ A) ∧ p.2 ∈ unitInterval}), g q = G q.val )
    → HEP X A  := by
  intro h_extend Y hY rangeH' f H hf1 hf2 hH1 hH2 hAgree
  let g : X × ℝ → Y := fun q =>
    if q.2 = 0 then f q.1
    else H q
  obtain ⟨G, hG⟩ := h_extend Y rangeH' g (continuousOn_g A hA f H hf1 hH1 hAgree) (by
    intro x hx
    by_cases hx_case : x.2 = 0
    · simp only [hx_case, reduceIte, g]
      exact hf2 (by simp)
    · simp only [hx_case, reduceIte, g]
      simp only [Set.mem_Icc, Set.mem_setOf_eq, hx_case, false_or] at hx
      exact hH2 (Set.mem_sep_iff.mpr hx))
  refine ⟨G, hG.1, hG.2.1, ⟨ ?_, ?_ ⟩  ⟩
  · intro x
    grind [hG.2.2 ⟨(x,0), by simp⟩]
  · intro a t
    by_cases h : t.1 = 0
    · obtain ⟨hG_cont, ⟨hG1, hG2⟩⟩ := hG
      specialize hG2 ⟨(a,t), by simp [h]⟩
      specialize hAgree ⟨a, by grind⟩
      rw [show G (a, t) = f a by grind, h]
      exact hAgree.symm
    · obtain ⟨hG_cont , ⟨hG1, hG2⟩⟩ := hG
      specialize hG2 ⟨(a,t), Set.mem_setOf.mpr (Or.inr ⟨Subtype.coe_prop a, Subtype.coe_prop t⟩)⟩
      grind

structure RetractionOn {X : Type*} [TopologicalSpace X] (r : X → X) (B A : Set X) : Prop where
  subset : A ⊆ B
  continuousOn : ContinuousOn r B
  mapsTo : B.MapsTo r A
  fixesOn : ∀ a ∈ A, r a = a

  /-
  "Lemma 2.26": A ⊆ X subspace, then TFAE:
  (i): ∀ g : A → Y, there exists an extension G : X → Y
  (ii): A is a retract of X, i.e. ∃ r: X → A s.th. r is the indentity on A
-/

lemma extension_then_retract {A B : Set X} (hAB : A ⊆ B) (hX : Nonempty X) :
    (∀ (Y : Type u) [TopologicalSpace Y] (rangeG : Set Y) (g : X → Y),
    ContinuousOn g A → A.MapsTo g rangeG →
    ∃ G : X → Y , ContinuousOn G B ∧ B.MapsTo G rangeG ∧ ∀ a : A, g a = G a ) →
    ∃ r : X → X, RetractionOn r B A  := by
  classical
  intro h
  let g : X → X := fun p =>
    if p ∈ A then p
    else Classical.choice hX
  have hg_cont: ContinuousOn g A := by
    simp only [continuousOn_iff_continuous_restrict, Set.restrict_ite, g]
    fun_prop
  have hg_mapsAA : Set.MapsTo g A A := by
    intro a ha
    simp only [g, ha, ↓reduceIte]
  obtain ⟨G, hG1, hG2, hG3⟩ := h X A g hg_cont hg_mapsAA
  refine ⟨G, hAB,  hG1, hG2, ?_ ⟩
  intro a ha
  rw[← hG3 ⟨a, ha⟩]
  exact (Ne.dite_eq_left_iff fun h a ↦ h ha).mpr ha


lemma retract_then_extension {B : Set X} (hAB : A ⊆ B) (hX : Nonempty X)
    (r : X → X) (hr : RetractionOn r B A) :
    ∀ (Y : Type u) [TopologicalSpace Y] (C : Set Y) (g : X → Y), ContinuousOn g A → A.MapsTo g C →
    ∃ G : X → Y , ContinuousOn G B ∧ B.MapsTo G C ∧ ∀ a : A, g a = G a := by
  classical
  intro Y hY C g hg hgAC
  let G : X → Y := fun p =>
    if hp : p ∈ B then g (r p)
    else Classical.choice (Nonempty.map2 (fun a ↦ g) hX hX)
  refine ⟨G, ?_ , ?_ , ?_ ⟩
  · unfold G
    simp only [dite_eq_ite, continuousOn_iff_continuous_restrict, Set.restrict_ite]
    rw [← continuousOn_iff_continuous_restrict]
    exact ContinuousOn.comp hg hr.continuousOn hr.mapsTo
  · intro b hb
    simp only [dite_eq_ite, hb, ↓reduceIte, G]
    exact hgAC (hr.mapsTo hb)
  · intro a
    simp [G, Set.mem_of_mem_of_subset a.prop hAB, hr.fixesOn]


/-
retraction criterion :
  "Corollary 2.27": **Retraction criterion:** A ⊆ X closed.
  (X,A) has the HEP ↔ (X × {0}) ∪ (A × [0,1]) is a retract of X×[0,1]

The condition A ⊆ X closed is only needed for "→".
-/

lemma if_HEP_then_retraction {X : Type u} [TopologicalSpace X] {A : Set X} (hA : Nonempty A)
    (h_HEP : HEP X A) : ∃ r : X × ℝ → X × ℝ, RetractionOn r {p : X × ℝ | p.2 ∈ unitInterval}
    {p : X × ℝ | p.2 = 0 ∨ (p.1 ∈ A) ∧ p.2 ∈ unitInterval}
    := by
  apply extension_then_retract (by simp)
    (nonempty_prod.2 ⟨Set.Nonempty.to_type (Set.nonempty_coe_sort.mp hA), instNonemptyOfInhabited⟩)
  intro Y hY C g hg_cont hg_mapsto
  obtain ⟨G, hG⟩ := if_HEP_then_extension h_HEP Y C g hg_cont hg_mapsto
  use G

lemma retraction_criterion_closed (hA1 : IsClosed A) :
    HEP X A ↔ ∃ r : X × ℝ → X × ℝ, RetractionOn r {p : X × ℝ | p.2 ∈ unitInterval}
    {p : X × ℝ | p.2 = 0 ∨ (p.1 ∈ A) ∧ p.2 ∈ unitInterval} := by
  by_cases hA2 : Nonempty A
  · have hX : Nonempty (X × ℝ ):=
      (nonempty_prod.2 ⟨Set.Nonempty.to_type (Set.nonempty_coe_sort.mp hA2),
      instNonemptyOfInhabited⟩)
    refine ⟨if_HEP_then_retraction hA2 , ?_ ⟩
    intro h
    apply if_extension_then_HEP hA1
    intro Y hY C g hg1 hg2
    obtain ⟨r, hr⟩ := h
    obtain ⟨G, hG1, hG2, hG3⟩ := (retract_then_extension (by simp) hX) r hr Y C g hg1 hg2
    use G
  · have : A = ∅ := by exact Set.not_nonempty_iff_eq_empty'.mp hA2
    rw[this]
    refine (iff_true_right ?_).mpr (HEP_empty)
    use (fun x ↦ (x.1,0))
    refine ⟨by simp, by fun_prop, ?_ , ?_  ⟩
    · intro x hx
      simp
    · intro x hx
      simp at hx
      rw [Prod.ext_iff]
      refine ⟨by rfl, hx.symm ⟩


lemma ContinuousOn_dite {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {p : β → Prop} [DecidablePred p] {f : { a // p a } → α} {f' : { a // ¬p a } → α}
    (hg : ContinuousOn f {a | p a}) {s : Set β} (hs : s ⊆ {b |p b}) :
    ContinuousOn (fun (x : β) => if h : x ∈ {b | p b} then f ⟨x, h⟩ else f' ⟨x, h⟩) s := by
  set s' := {b |p b} ↓∩ s
  refine continuousOn_iff_continuous_restrict.mpr ?_
  --have g (b : β) := b ∈ s → f ⟨ b ,by sorry ⟩
  -- Set.restrict_dite


  --have := ContinuousOn.mono hg

  /-
  have := ContinuousOn.mono hg hs
  apply (ContinuousOn.mono hg hs).congr
  intro b hb
  have : p b := Set.mem_setOf.1 hs hb
  simp only [this, ↓reduceIte] -/

  sorry


open Classical in
lemma retraction_criterion_closed' {Y : Type u} [TopologicalSpace Y] (A X : Set Y) (hAX : A ⊆ X)
    (hA1 : IsClosed A) : HEP' X A ↔ ∃ r : Y × ℝ → Y × ℝ, RetractionOn r
    {p : Y × ℝ | p.1 ∈ X ∧ p.2 ∈ unitInterval}
    {p : Y × ℝ | p.1 ∈ X ∧ p.2 = 0 ∨ (p.1 ∈ A) ∧ p.2 ∈ unitInterval} := by
  constructor
  · intro h
    unfold HEP' at h
    obtain ⟨r, hr⟩ := (retraction_criterion_closed hA1.preimage_val).mp h
    let incl : X × ℝ → Y × ℝ := fun p ↦ (Subtype.val p.1,p.2)
    let rY : X × ℝ → Y × ℝ := fun p ↦ ((r p).1, (r p).2)
    let s : Y × ℝ → Y × ℝ  := Function.extend incl rY id
    have incl_inj : incl.Injective := by
      intro x y hxy
      rw [Prod.mk_inj] at hxy
      refine Prod.ext_iff.mpr ⟨ SetCoe.ext hxy.1 , hxy.2⟩
    let proj (p : Y × ℝ ) (hp: p.1 ∈ X) : X × ℝ := (⟨ p.1, hp⟩ , p.2)
    have sapply (p : Y × ℝ) (hp : p.1 ∈ X ) : s p = rY (proj p hp) := by
      set p' : X × ℝ := (⟨p.1, hp⟩, p.2 )
      have h : ∃ a, incl a = p := by use p'
      simp only [s, Function.extend_def, h, ↓reduceDIte]
      grind
    have hrY : ContinuousOn rY {p | p.2 ∈ unitInterval} := by
      have := hr.2
      fun_prop
    have hrY_mapsTo : {p | p.2 ∈ unitInterval}.MapsTo rY {p | p.1 ∈ X ∧ p.2 = 0 ∨
      p.1 ∈ A ∧ p.2 ∈ unitInterval} := by
      intro y hy
      have := hr.3 hy
      grind
      /-
      obtain h1 | h2 := this
      · left
        simp only [Subtype.coe_prop, true_and, rY]
        exact h1
      · right
        simp only [rY]
        exact ⟨ Set.mem_preimage.mp h2.1 , h2.2 ⟩
        -/
    have hrY_fixed : ∀ a ∈ {p | p.2 = 0 ∨ p.1 ∈ X ↓∩ A ∧ p.2 ∈ unitInterval}, rY a = incl a := by
      intro a ha
      simp only [ rY, incl, hr.4 a ha]
    use s
    constructor
    · grind
    · have := hr.2
      unfold s
      rw[← Function.extend_comp incl_inj rY id] at hrY

      sorry
    · intro y hy
      set y' : X × ℝ := proj y hy.1
      have : y' ∈ {p : X × ℝ  | p.2 ∈ unitInterval} := by
        simp only [Set.mem_setOf_eq, y']
        exact hy.2
      convert hrY_mapsTo this
      exact sapply y hy.1
    · intro y hy
      grind
      /-
      have : y.1 ∈ X := by
        rw [Set.mem_setOf] at hy
        obtain h1 | h2 := hy
        · exact h1.1
        · exact hAX h2.1
      rw[sapply y this]
      apply hrY_fixed
      obtain h1 | h2 := hy
      · left
        unfold proj
        exact h1.2
      · right
        simp only [proj, Set.mem_preimage]
        exact h2 -/
  · intro h
    unfold HEP'
    obtain ⟨r, hr⟩ :=  h
    have Maps_r' (p : X × ℝ) (hp : p.2 ∈ unitInterval): (r (p.1,p.2)).1 ∈ X := by
      have : ((p.1 : Y), p.2) ∈ {p | p.1 ∈ X ∧ p.2 ∈ unitInterval} := ⟨Subtype.coe_prop p.1 , hp⟩
      have := hr.3 this
      obtain h1 | h2 := this
      · exact h1.1
      · exact hAX h2.1
    let r' : X × ℝ → X × ℝ := fun p ↦
      if hp : p.2 ∈ unitInterval then (⟨(r (p.1,p.2)).1 , by exact Maps_r' p hp⟩, (r (p.1,p.2)).2 )
      else Classical.choice (by sorry) -- WLOG X Nonempty
    apply (retraction_criterion_closed hA1.preimage_val).2
    use r'
    constructor
    · simp
    · unfold r'
      have : {p : X × ℝ | p.2 ∈ unitInterval} ⊆ {p | p.2 ∈ unitInterval} := by rfl
      nth_rw 1 [continuousOn_iff_continuous_restrict]
      --rw[Set.restrict_dite _ _]
      -- have : ContinuousOn (Y := X × ℝ) (fun (p : X × ℝ) ↦ (⟨(r (p.1,p.2)).1 , by exact Maps_r' p hp⟩, (r (p.1,p.2)).2 )) {p : X × ℝ | p.2 ∈ unitInterval} := by
        --sorry
      sorry
    · unfold r'
      intro x hx
      rw [Set.mem_setOf] at hx
      simp only [Set.mem_preimage, hx, ↓reduceDIte, Set.mem_setOf_eq]
      set x' : Y × ℝ := (x.1,x.2)
      have : x' ∈ {p | p.1 ∈ X ∧ p.2 ∈ unitInterval} := ⟨Subtype.coe_prop x.1, hx⟩
      have := hr.3 this
      grind only [usr Set.mem_setOf_eq]
    · intro x hx
      set x' : Y × ℝ := (x.1,x.2) with defx'
      have : x' ∈ {p | p.1 ∈ X ∧ p.2 = 0 ∨ p.1 ∈ A ∧ p.2 ∈ unitInterval} := by
        obtain h1 | h2 := hx
        ·
          left
          exact ⟨ Subtype.coe_prop x.1, h1⟩
        · right
          exact ⟨ Set.mem_preimage.mp h2.1 , unitInterval.mem_unitIntervalSubmonoid.mp h2.2⟩
      have := hr.4 x' this
      unfold r'
      simp[defx'] at this
      simp[this, show x.2 ∈ unitInterval by grind only [usr Set.mem_setOf_eq, = Set.mem_Icc]]


-- corollary:
--lemma HEP_Discrete {X J : Type u} [TopologicalSpace X] [TopologicalSpace J] [DiscreteTopology J]
   -- {A : Set X} (h_HEP : HEP X A) : HEP (J × X) (J × A) := by sorry

-- if f : X → Y is a homeomorphism and (X,A) has the HEP, then also (Y, f(A)) has the HEP


-- ToDo :
-- partial homeomorph

lemma homeomorph_HEP {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (A : Set X) (hA_closed : IsClosed A) :
    HEP X A → IsHomeomorph f → HEP Y (f '' A) := by
  intro h_hep1 hf
  rw[retraction_criterion_closed hA_closed] at h_hep1
  obtain ⟨r, hr⟩ := h_hep1
  obtain ⟨hf_cont, ⟨f_inv, hf1, hf2, hf_inv_cont⟩ ⟩ := isHomeomorph_iff_exists_inverse.1 hf
  let r' : Y × ℝ → Y × ℝ := fun p ↦ (f (r ((f_inv p.1), p.2 )).1, (r ((f_inv p.1), p.2 )).2)
  rw [retraction_criterion_closed (by
    exact (Homeomorph.isClosed_image (IsHomeomorph.homeomorph f hf)).2 hA_closed)]
  use r'
  refine ⟨?_, ?_ , ?_ , ?_ ⟩
  · grind
  · refine ContinuousOn.prodMk ?_ ?_
    · refine Continuous.comp_continuousOn hf_cont ?_
      refine Continuous.comp_continuousOn' continuous_fst ?_
      exact ContinuousOn.comp hr.2 (by fun_prop) (Set.mapsTo_iff_subset_preimage.mpr fun a b ↦ b)
    · refine Continuous.comp_continuousOn' continuous_snd ?_
      refine ContinuousOn.comp hr.2 (by fun_prop) ?_
      exact Set.mapsTo_iff_subset_preimage.mpr fun a b ↦ b
  · have maps : {p | p.2 = 0 ∨ p.1 ∈ A ∧ p.2 ∈ unitInterval}.MapsTo
        (fun (p : X × ℝ) ↦ (f p.1, p.2))
        {p | p.2 = 0 ∨ p.1 ∈ f '' A ∧ p.2 ∈ unitInterval} := by
      intro x hx
      simp only [Set.mem_image, Set.mem_setOf_eq]
      obtain h1 | h2 := Set.mem_setOf.1 hx
      · exact Or.inl h1
      · exact Or.inr ⟨⟨x.1, h2.1, rfl⟩, h2.2⟩
    exact Set.MapsTo.comp maps (Set.MapsTo.comp hr.mapsTo
      (Set.mapsTo_iff_subset_preimage.mpr fun a b ↦ b))
  · intro b hb
    unfold r'
    rw [ hr.fixesOn (f_inv b.1, b.2) ?_]
    · grind
    · simp only [Set.mem_setOf_eq]
      by_cases h : b.2 = 0
      · exact Or.symm (Or.inr h)
      · right
        simp only [Set.mem_image, Set.mem_Icc, Set.mem_setOf_eq, h, false_or] at hb
        simp only [Set.mem_Icc, hb.2, and_self, and_true]
        exact (Set.mem_image_iff_of_inverse hf1 hf2).mp hb.1

lemma PartialHomeomorph_HEP' {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {X1 X2 : Set X} (hX : X2 ⊆ X1) {Y1 Y2 : Set Y} (hY : Y2 ⊆ Y1) (hHEP : HEP' X1 X2)
    (f : PartialHomeomorph X Y) (hf_source : f.source = X1) (hf_target : f.target = Y1)
    (h2 : f '' X2 = Y2) (hX2closed : IsClosed (X2 : Set X)) (hY2closed : IsClosed (Y2 : Set Y)) :
    HEP' Y1 Y2 := by
  apply (retraction_criterion_closed' X2 X1 hX hX2closed).mp at hHEP
  obtain ⟨r, hr⟩ := hHEP
  have finv_mem: ∀ (p : Y1), f.invFun p ∈ X1 := by
    rw [PartialHomeomorph.invFun_eq_coe, ← hf_source, ← hf_target]
    intro p
    exact PartialHomeomorph.mapsTo_symm f p.2
  let r_comp_fsymm : Y × ℝ → X × ℝ := fun p ↦ (r (f.invFun p.1 , p.2))
  let r' : Y × ℝ → Y × ℝ := fun p ↦ (f (r_comp_fsymm p).1, (r_comp_fsymm p).2 )
  apply (retraction_criterion_closed' Y2 Y1 hY hY2closed ).2
  use r'
  constructor
  · grind
  · have hr_comp_fsymm : ContinuousOn r_comp_fsymm {p | p.1 ∈ Y1 ∧ p.2 ∈ unitInterval} := by
      unfold r_comp_fsymm
      apply ContinuousOn.comp' hr.2 ?_ ?_
      · have : ContinuousOn f.symm Y1 := by
          rw[← hf_target]
          exact f.continuousOn_symm
        simp only [PartialEquiv.invFun_as_coe, PartialHomeomorph.coe_toPartialEquiv_symm]
        refine ContinuousOn.prodMk ?_ (by fun_prop)
        apply ContinuousOn.comp' this ?_ ?_
        · fun_prop
        · intro x hx
          exact hx.1
      · intro x hx
        refine ⟨ ?_ , hx.2⟩
        simp only [PartialEquiv.invFun_as_coe, PartialHomeomorph.coe_toPartialEquiv_symm]
        rw[← hf_source]
        refine PartialHomeomorph.map_target f ?_
        rw[hf_target]
        exact hx.1
    unfold r'
    refine ContinuousOn.prodMk ?_ ?_
    · have : ContinuousOn f X1 := by
        rw[← hf_source]
        exact f.continuousOn
      apply ContinuousOn.comp' this ?_ ?_
      · exact Continuous.comp_continuousOn' continuous_fst hr_comp_fsymm
      · rw[← hf_target]
        simp only [PartialEquiv.invFun_as_coe, PartialHomeomorph.coe_toPartialEquiv_symm,
          r_comp_fsymm]
        intro x hx
        have : (f.symm x.1, x.2) ∈ {p | p.1 ∈ X1 ∧ p.2 ∈ unitInterval} := by
          refine ⟨ ?_, hx.2⟩
          rw[← hf_source]
          exact PartialHomeomorph.map_target f hx.1
        obtain h0 | h1 := hr.3 this
        · exact h0.1
        · exact hX h1.1
    exact ContinuousOn.snd hr_comp_fsymm
  · have : {y | y.1 ∈ Y1 ∧ y.2 ∈ unitInterval}.MapsTo r_comp_fsymm
        { x | x.1 ∈ X1 ∧ x.2 = 0 ∨ x.1 ∈ X2 ∧ x.2 ∈ unitInterval}:= by
      unfold r_comp_fsymm
      intro y hy
      apply hr.3
      refine ⟨?_ , hy.2⟩
      rw[← hf_source]
      rw[← hf_target] at hy
      simp only [PartialEquiv.invFun_as_coe, PartialHomeomorph.coe_toPartialEquiv_symm]
      apply f.mapsTo_symm hy.1
    intro y hy
    simp only [Set.mem_setOf_eq, r']
    have := this hy
    obtain h0 | h1 := this
    · refine Or.inl ⟨ ?_ , h0.2⟩
      rw[← hf_source] at h0
      rw[← hf_target]
      exact f.mapsTo h0.1
    · right
      refine ⟨ ?_ , h1.2⟩
      rw[← h2]
      exact Set.mem_image_of_mem f h1.1
  · intro y hy
    have : r_comp_fsymm y = (f.symm y.1, y.2) := by
      apply hr.4 (f.symm y.1 ,y.2)
      obtain h0 | h1 := hy
      · left
        refine ⟨ ?_, h0.2 ⟩
        rw[← hf_target] at h0
        rw[← hf_source]
        apply f.mapsTo_symm h0.1
      · right
        refine ⟨ ?_, h1.2⟩
        rw[← h2] at h1
        have := Set.mem_image_of_mem f.symm h1.1
        refine Set.mem_of_mem_of_subset this ?_
        intro _ hx
        obtain ⟨ _ , ⟨⟨ _, hx'⟩, hy1 ⟩⟩ := hx
        rw[← hy1, ← hx'.2, PartialHomeomorph.left_inv f (by rw[hf_source]; exact hX hx'.1)]
        · exact hx'.1
    unfold r'
    rw [this]
    refine Prod.ext (f.right_inv ?_ ) rfl
    rw[ hf_target]
    obtain h0 | h1 := hy
    · exact h0.1
    · exact hY h1.1

-- Partial Equiv, ... should be replaced by paritalHomeomorph
lemma partialHomeomorph_HEP {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {X1 : Set X} {X2 : Set X1} {Y1 : Set Y} {Y2 : Set Y1} (hHEP : HEP X1 X2)
    (f : PartialHomeomorph X Y)
    (hf_source : f.source = X1) (hf_target : f.target = Y1)
    (h2 : f '' X2 = Y2) (hX2closed : IsClosed (X2 : Set X)) (hY2closed : IsClosed (Y2 : Set Y)) :
    HEP Y1 Y2 := by
  -- ENTWEDER Subtype '' X2 closed, ODER X1 closed und X2 closed, was stärker als notwendig wäre.
  rw[HEP_HEP'] at hHEP ⊢
  refine PartialHomeomorph_HEP' (Subtype.coe_image_subset X1 X2) (Subtype.coe_image_subset Y1 Y2)
    hHEP f hf_source hf_target h2 hX2closed hY2closed





/- ohne partialHomeomorph_HEP'

  apply (retraction_criterion_closed (by sorry)).mp at hHEP
  obtain ⟨r, hr⟩ := hHEP
  have finv_mem: ∀ (p : Y1), f.invFun p ∈ X1 := by sorry
  let r_comp_fsymm : ↑Y1 × ℝ → X1 × ℝ := fun p ↦ (r (⟨ f.invFun p.1,
    Set.mem_preimage.mp (finv_mem p.1)⟩, p.2))
  have Continuous_r_comp_fsymm : ContinuousOn r_comp_fsymm {p | p.2 ∈ unitInterval} := by
    sorry
  let r' : Y1 × ℝ → Y1 × ℝ := fun p ↦ (⟨f (r_comp_fsymm p).1, by sorry⟩, (r_comp_fsymm p).2 )
  apply (retraction_criterion_closed ?_ ).2
  · use r'
    constructor -- RetractionOn
    · refine ContinuousOn.prodMk ?_ ?_
      · have int := Continuous.comp_continuousOn' continuous_fst  Continuous_r_comp_fsymm
        have ext := f.continuousOn
        have : ContinuousOn (fun p ↦ f ↑(r_comp_fsymm p).1) {p | p.2 ∈ unitInterval} := by
          refine ContinuousOn.comp ext ?_ ?_
          · exact Continuous.comp_continuousOn' continuous_subtype_val int
          · sorry
        rw [continuousOn_iff_continuous_restrict] at this ⊢
        apply Continuous.subtype_mk (h := this)
      · exact Continuous.comp_continuousOn' continuous_snd Continuous_r_comp_fsymm
    · intro y hy
      sorry
    · intro a ha
      unfold r' r_comp_fsymm
      have := hr.3
      sorry
  sorry
    /-
  · have : IsClosed (Subtype.val '' X2) := by
      refine IsClosed.trans h2closed ?_
      sorry
    sorry

    rw[← h2]
    have := f.continuousOn
    rw [continuousOn_iff_continuous_restrict] at this
    refine IsClosed.preimage_val ?_
    sorry -/

-/
