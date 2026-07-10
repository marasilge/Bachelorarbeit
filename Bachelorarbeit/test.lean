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

def IsHomotopyExtension (H' : X × ℝ → Y) (f : X → Y) (H : X × ℝ → Y) (A : Set X)
  (rangeH' : Set Y := Set.univ) : Prop :=
  ContinuousOn H' { p : X × ℝ | p.2 ∈ unitInterval} ∧
  { p : X × ℝ | p.2 ∈ unitInterval}.MapsTo H' rangeH'  ∧
  (∀ (x : X), f x = H' (x, 0)) ∧ (∀ (a : A) (t :unitInterval), H (a,t) = H' (a, t))

def HEP (X : Type u) [TopologicalSpace X] (A : Set X) : Prop :=
  ∀ (Y : Type u) [TopologicalSpace Y] (rangeH' : Set Y ), ∀ (f : X → Y), ∀ (H : X × ℝ → Y),
  Continuous f → Set.range f ⊆ rangeH' →
  ContinuousOn H {p : X × ℝ | (p.1 ∈ A) ∧ (p.2 ∈ (unitInterval))} →
  {p : X × ℝ | (p.1 ∈ A) ∧ (p.2 ∈ unitInterval)}.MapsTo H rangeH'  → agreeOn f H A
  → ∃ (H' : X × ℝ → Y), IsHomotopyExtension H' f H A rangeH'
open Set.Notation

/-
  "Corollary 2.25" for closed:  Let A be a closed subset of a topological space X.
  Then A ⊆ X has the HEP ↔
  for every topological space Y and every continuous map g: (X × {0}) ∪ (A × [0,1]) → Y there
  exists an extension of g to a map G : X × [0,1] → Y:
-/

-- (Hinrichtung, die geht auch ohne A closed)


-- The pair (X,X) has the HEP :

example : HEP X (@Set.univ X) := by
  intro Y hY rangeH' f H hf1 hf2 hH1 hH2 hAgree
  use H
  refine ⟨?_, ?_ ,?_ ⟩
  · rw [← Set.sep_univ]
    exact hH1
  · intro x hx
    apply hH2
    simp [hx.2, hx.1]
  · simp only [implies_true, and_true]
    intro x
    exact hAgree ⟨x, by tauto⟩

-- The pair (X, ∅ ) has the HEP:

lemma HEP_empty : HEP X ∅ := by
  intro Y hY rangeH' f H hf1 hf2 hH1 hH2 hAgree
  let H' : X × ℝ → Y := fun (x,t) ↦ f x
  use H'
  refine ⟨?_, ?_ ,?_ ⟩
  · exact Continuous.continuousOn (Continuous.fst' hf1)
  · rw [← Set.mapsTo_univ_iff_range_subset] at hf2
    apply Set.MapsTo.comp hf2 (by tauto)
  · simp only [H', Subtype.forall, Set.mem_Icc, and_imp, IsEmpty.forall_iff, and_true]
    intro x
    tauto

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

structure IsRetractionOn (r : X → X) (B A : Set X) : Prop where
  continuousOn : ContinuousOn r B
  mapsTo : B.MapsTo r A
  fixesOn : ∀ a ∈ A, r a = a

  /-
  "Lemma 2.26": A ⊆ X subspace, then TFAE:
  (i): ∀ g : A → Y, there exists an extension G : X → Y
  (ii): A is a retract of X, i.e. ∃ r: X → A s.th. r is the indentity on A
-/

lemma extension_then_retract {B : Set X} (hX : Nonempty X) :
    (∀ (Y : Type u) [TopologicalSpace Y] (C : Set Y) (g : X → Y), ContinuousOn g A → A.MapsTo g C →
    ∃ G : X → Y , ContinuousOn G B ∧ B.MapsTo G C ∧ ∀ a : A, g a = G a ) →
    ∃ r : X → X, IsRetractionOn r B A  := by
  classical
  intro h
  let g : X → X := fun p =>
    if hp : p ∈ A then p
    else Classical.choice hX
  have hg_cont: ContinuousOn g A := by
    simp only [dite_eq_ite, continuousOn_iff_continuous_restrict, Set.restrict_ite, g]
    fun_prop
  have hg_mapsAA : Set.MapsTo g A A := by
    intro a ha
    simp only [dite_eq_ite, g, ha, ↓reduceIte]
  obtain ⟨G, hG1, hG2, hG3⟩ := h X A g hg_cont hg_mapsAA
  exact ⟨G, hG1, hG2, by
    intro a ha
    rw[← hG3 ⟨a, ha⟩]
    exact (Ne.dite_eq_left_iff fun h a ↦ h ha).mpr ha⟩

lemma retract_then_extension {B : Set X} (hAB : A ⊆ B) (hX : Nonempty X)
    (r : X → X) (hr : IsRetractionOn r B A) :
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
    (h_HEP : HEP X A) : ∃ r : X × ℝ → X × ℝ, IsRetractionOn r {p : X × ℝ | p.2 ∈ unitInterval}
    {p : X × ℝ | p.2 = 0 ∨ (p.1 ∈ A) ∧ p.2 ∈ unitInterval}
    := by
  apply extension_then_retract
    (nonempty_prod.2 ⟨Set.Nonempty.to_type (Set.nonempty_coe_sort.mp hA), instNonemptyOfInhabited⟩)
  intro Y hY C g hg_cont hg_mapsto
  obtain ⟨G, hG⟩ := if_HEP_then_extension h_HEP Y C g hg_cont hg_mapsto
  use G

lemma retraction_criterion_closed (hA1 : IsClosed A) :
    HEP X A ↔ ∃ r : X × ℝ → X × ℝ, IsRetractionOn r {p : X × ℝ | p.2 ∈ unitInterval}
    {p : X × ℝ | p.2 = 0 ∨ (p.1 ∈ A) ∧ p.2 ∈ unitInterval}:= by
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
    constructor
    · fun_prop
    · intro x hx
      simp
    · intro x hx
      simp at hx
      rw [Prod.ext_iff]
      refine ⟨by rfl, hx.symm ⟩
