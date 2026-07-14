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

def HomotopyExtension (H' : X × ℝ → Y) (f : X → Y) (H : X × ℝ → Y) (A : Set X) :
    Prop :=
  ContinuousOn H' { p : X × ℝ | p.2 ∈ unitInterval} ∧
  (∀ (x : X), f x = H' (x, 0)) ∧ (∀ (a : A) (t : unitInterval), H (a,t) = H' (a, t))

def HEP (X : Type u) [TopologicalSpace X] (A : Set X) : Prop :=
  ∀ (Y : Type u) [TopologicalSpace Y], ∀ (f : X → Y), ∀ (H : X × ℝ → Y), Continuous f →
  ContinuousOn H {p : X × ℝ | (p.1 ∈ A) ∧ (p.2 ∈ (unitInterval))} → agreeOn f H A
  → ∃ (H' : X × ℝ → Y), HomotopyExtension H' f H A


open Set.Notation
def HEP' {Y : Type*} [TopologicalSpace Y] (X A : Set Y) : Prop := HEP X (X ↓∩ A)

lemma HEP_HEP' {Y : Type*} [TopologicalSpace Y] (X : Set Y) (A : Set (Set.Elem X)) :
    HEP (Set.Elem X) A ↔ HEP' X (Subtype.val '' A) := by
  unfold HEP'
  rw [Set.preimage_val_image_val_eq_self]


def HomotopyExtension'' {Z : Type u} [TopologicalSpace Z] (f : Z → Y) (H : Z × ℝ → Y) (X A : Set Z)
(H' : Z × ℝ → Y) : Prop :=
ContinuousOn H' { p : Z × ℝ | p.1 ∈ X ∧ p.2 ∈ unitInterval} ∧
(∀ (x : Z), x ∈ X →  f x = H' (x, 0)) ∧
(∀ (a : Z × ℝ ), a.1 ∈ A → a.2 ∈ unitInterval → H a = H' a)

def HEP'' {Z : Type u} [TopologicalSpace Z] (X A : Set Z) : Prop :=
  ∀ (Y : Type u) [TopologicalSpace Y], ∀ (f : Z → Y), ∀ (H : Z × ℝ → Y), ContinuousOn f X →
  ContinuousOn H {p : Z × ℝ | (p.1 ∈ A) ∧ (p.2 ∈ (unitInterval))} → agreeOn f H A
  → ∃ (H' : Z × ℝ → Y), HomotopyExtension'' f H X A H'

/-
  "Corollary 2.25" for closed:  Let A be a closed subset of a topological space X.
  Then A ⊆ X has the HEP ↔
  for every topological space Y and every continuous map g: (X × {0}) ∪ (A × [0,1]) → Y there
  exists an extension of g to a map G : X × [0,1] → Y:
-/

-- (Hinrichtung, die geht auch ohne A closed)


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

variable {Z : Type u} [TopologicalSpace Z] {X A : Set Z}

lemma if_HEP''_then_extension :
    HEP'' X A →  ∀ (Y : Type u) [TopologicalSpace Y] , ∀ (g : Z × ℝ → Y ),
    ContinuousOn g {p : Z × ℝ | (p.1 ∈ X) ∧ p.2 = 0 ∨ (p.1 ∈ A) ∧ p.2 ∈ unitInterval} →
    ∃ (G : Z × ℝ → Y), ContinuousOn G {p : Z × ℝ | p.1 ∈ X ∧ p.2 ∈ unitInterval} ∧
    ∀ (q : {p : Z × ℝ | p.1 ∈ X ∧ p.2 = 0 ∨ (p.1 ∈ A) ∧ p.2 ∈ unitInterval}), g q = G q.val := by
  intro hHEP Y hY g hg
  let f : Z → Y := fun x ↦ g (x,0)
  let H : Z × ℝ → Y := fun p ↦ g p
  have hf : ContinuousOn f X := by
    unfold f
    apply ContinuousOn.comp hg (by fun_prop) ?_
    intro x hx
    simp only [Set.mem_setOf_eq, and_true]
    exact Or.inl hx
  have hH : ContinuousOn H {p | p.1 ∈ A ∧ p.2 ∈ unitInterval} := by
    unfold H
    exact ContinuousOn.congr_mono hg (by simp [Set.EqOn]) (by grind)
  have h_agree : agreeOn f H A := by
    intro a
    simp [f, H]
  obtain ⟨G, ⟨hG_cont, hG⟩⟩ := hHEP Y f H hf hH h_agree
  refine ⟨G, hG_cont , ?_ ⟩
  intro q
  cases q.prop with
  | inl h0 => grind
  | inr hA => exact hG.2 q.val hA.1 hA.2

def g (f : Z → Y) (H : Z × ℝ → Y) : Z × ℝ → Y := fun q =>
  if q.2 = 0 then f q.1
  else H q

lemma continuousOn_g (A : Set Z) (hA : IsClosed A) (hX : IsClosed X)(f : Z → Y) (H : Z × ℝ → Y) (hf1 : ContinuousOn f X)
  (hH1 : ContinuousOn H {p | p.1 ∈ A ∧ p.2 ∈ unitInterval}) (hAgree : agreeOn f H A) :
    ContinuousOn (g f H)  { p : Z × ℝ | p.1 ∈ X ∧ p.2 = 0 ∨ (p.1 ∈ A ∧ p.2 ∈ unitInterval) } := by
  refine ContinuousOn.union_of_isClosed ?_ ?_ ?_ ?_
  · have h: ContinuousOn (fun q ↦ if q.2 = 0 then f q.1 else H q) {p : Z × ℝ | p.1 ∈ X ∧ p.2 = 0} =
        ContinuousOn (fun (q : Z × ℝ ) ↦ f q.1) { p | p.1 ∈ X ∧ p.2 = 0} := by
      rw [eq_iff_iff]
      refine continuousOn_congr ?_
      intro p hp
      exact if_pos hp.2
    unfold g
    rw [show ContinuousOn (fun q ↦ if q.2 = 0 then f q.1 else H q) fun p ↦ p.1 ∈ X ∧ p.2 = 0 =
      ContinuousOn (fun q ↦ if q.2 = 0 then f q.1 else H q) {p : Z × ℝ | p.1 ∈ X ∧ p.2 = 0} by rfl, h]
    refine ContinuousOn.comp hf1 continuousOn_fst ?_
    intro x hx
    exact hx.1
  · have : ContinuousOn (g f H) {p | p.1 ∈ A ∧ p.2 ∈ unitInterval} =
      ContinuousOn (fun (q : Z × ℝ ) ↦ H q) {p | p.1 ∈ A ∧ p.2 ∈ unitInterval} := by
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
    rw[show ContinuousOn (g f H) (fun p ↦ p.1 ∈ A ∧ p.2 ∈ unitInterval)
      = ContinuousOn (g f H) { p : Z × ℝ | p.1 ∈ A ∧ p.2 ∈ unitInterval} by rfl, this]
    exact ContinuousOn.comp hH1 (by fun_prop) (Set.mapsTo_iff_subset_preimage.mpr fun a a_1 ↦ a_1)
  · rw [show IsClosed fun (p : Z × ℝ ) ↦ p.1 ∈ X ∧ p.2 = 0 = IsClosed {p : Z × ℝ | p.1 ∈ X ∧ p.2 = 0 } by rfl]
    refine IsClosed.and ?_ ?_
    · sorry
    sorry
  · refine IsClosed.and ?_ ?_
    · have : { x : Z × ℝ | x.1 ∈ A} = {x : Z | x ∈ A } ×ˢ { a : ℝ | true} :=  by
        ext
        grind
      rw[this]
      exact IsClosed.prod (isClosed_coinduced.mpr hA) (isClosed_const)
    · exact IsClosed.and
        (isClosed_le continuous_const continuous_snd) (isClosed_le continuous_snd continuous_const)

lemma if_extension_then_HEP (hA : IsClosed A) :
    ( ∀ (Y : Type u) [TopologicalSpace Y],
    ∀ (g :  Z × ℝ → Y ), ContinuousOn g {p : Z × ℝ | p.1 ∈ X ∧ p.2 = 0 ∨ (p.1 ∈ A) ∧ p.2 ∈ unitInterval} →
    ∃ (G :  Z × ℝ → Y), ContinuousOn G {p : Z × ℝ | p.1 ∈ X ∧ p.2 ∈ unitInterval} ∧
    ∀ (q : {p : Z × ℝ | p.2 = 0 ∨ (p.1 ∈ A) ∧ p.2 ∈ unitInterval}), g q = G q.val )
    → HEP'' X A  := by
  intro h_extend Y hY f H hf hH hAgree
  let g : Z × ℝ → Y := fun q =>
    if q.2 = 0 then f q.1
    else H q
  obtain ⟨G, hG⟩ := h_extend Y g (continuousOn_g A hA (by sorry) f H hf hH hAgree)
  refine ⟨G, hG.1, ?_, ?_ ⟩
  · intro x
    grind [hG.2 ⟨(x,0), by simp⟩]
  · intro a
    by_cases h : (a.1 ∈ A ∧ a.2 = 0)
    · obtain ⟨hG_cont, hG1 ⟩ := hG
      specialize hG1 ⟨a, by simp [h]⟩
      specialize hAgree ⟨a.1, h.1⟩
      rw [show G a = f a.1 by grind, h.2]
      intro x t
      grind
    · obtain ⟨hG_cont , hG1 ⟩ := hG
      specialize hG1 ⟨a, by sorry⟩
      grind
  /-
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
      -/

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
    HEP'' X A ↔ ∃ r : X × ℝ → X × ℝ, IsRetractionOn r {p : X × ℝ | p.2 ∈ unitInterval}
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
