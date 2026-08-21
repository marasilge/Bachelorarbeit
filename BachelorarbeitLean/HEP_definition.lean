import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Data.Set.Subset
import Mathlib.Topology.Basic

open Set.Notation

noncomputable section

universe u
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

--## abbreviations for the relevant subsets of `X × ℝ`

--`X × I ⊆ X × ℝ`.
abbrev cyl (X : Type*) : Set (X × ℝ) := {p | p.2 ∈ unitInterval}

-- `A × I ⊆ X × ℝ` is the cylinder over a subset `A ⊆ X`.
abbrev smalcyl {X : Type*} (A : Set X) : Set (X × ℝ) := {p | p.1 ∈ A ∧ p.2 ∈ unitInterval}

-- `X × {0} ∪ A × I ⊆ X × ℝ`
abbrev anchor {X : Type*} (A : Set X) : Set (X × ℝ) :=
  {p | p.2 = 0 ∨ p.1 ∈ A ∧ p.2 ∈ unitInterval}

--`X × {0} ∪ A × I ⊆ Y × ℝ` in an ambient space `Y`.
abbrev smalanchor {Y : Type*} (X A : Set Y) : Set (Y × ℝ) :=
  {p | p.1 ∈ X ∧ p.2 = 0 ∨ p.1 ∈ A ∧ p.2 ∈ unitInterval}


/-
Definitions :
· agreeOn: f and H are compatible in a sense, that they agree on the Set A × {0}.
  We need this to ensure, it makes sence to search for a function H' which extends f and H
· HomotopyExtension combines all the properties, which the extended Homotopy on X × [0,1] should
  have.
· Definition of the homotopy extension property.
-/
def agreeOn (f : X → Y) (H : X × ℝ → Y) (A : Set X) : Prop := ∀ (a : X), a ∈ A → f a = H (a,0)

structure HomotopyExtension (H' : X × ℝ → Y) (f : X → Y) (H : X × ℝ → Y) (A : Set X)
    (rangeH' : Set Y) : Prop  where
  ContinuousOn : ContinuousOn H' (cyl X)
  range : (cyl X).MapsTo H' rangeH'
  agreef : (∀ (x : X), f x = H' (x, 0))
  agreeH : (∀ (a : A) (t : unitInterval), H (a,t) = H' (a, t))

def HEP (X : Type u) [TopologicalSpace X] (A : Set X) : Prop :=
  ∀ (Y : Type u) [TopologicalSpace Y] (rangeH' : Set Y), ∀ (f : X → Y), ∀ (H : X × ℝ → Y),
  Continuous f → Set.range f ⊆ rangeH' → ContinuousOn H (smalcyl A) →
  (smalcyl A).MapsTo H rangeH' → agreeOn f H A → ∃ H' : X × ℝ → Y,
  HomotopyExtension H' f H A rangeH'

-- This is the version, without rangeH':
structure HomotopyExtensionY (H' : X × ℝ → Y) (f : X → Y) (H : X × ℝ → Y) (A : Set X) : Prop where
  ContinuousOn : ContinuousOn H' (cyl X)
  agreef : ∀ (x : X), f x = H' (x, 0)
  agreeH : ∀ (a : A) (t : unitInterval), H (a,t) = H' (a, t)

def HEPY (X : Type u) [TopologicalSpace X] (A : Set X) : Prop :=
  ∀ (Y : Type u) [TopologicalSpace Y], ∀ (f : X → Y), ∀ (H : X × ℝ → Y), Continuous f →
  ContinuousOn H (smalcyl A) → agreeOn f H A
  → ∃ (H' : X × ℝ → Y), HomotopyExtensionY H' f H A

--Third version, where both X and A are sets of the same Type:
def HEP' {Y : Type*} [TopologicalSpace Y] (X A : Set Y) : Prop := HEP X (X ↓∩ A)

@[simp]
lemma HEP_HEP' {Y : Type*} [TopologicalSpace Y] (X : Set Y) (A : Set (Set.Elem X)) :
    HEP (X.Elem) A ↔ HEP' X (Subtype.val '' A) := by
  unfold HEP'
  rw [Set.preimage_val_image_val_eq_self]

-- The pair (X,X) has the HEP :
lemma HEP_self : HEP X (@Set.univ X) := by
  intro Y hY rangeH' f H hf1 hf2 hH1 hH2 hAgree
  use H
  refine ⟨?_, ?_ ,?_, ?_⟩
  · exact hH1.mono fun p hp => ⟨trivial, hp⟩
  · tauto
  · intro x
    exact hAgree x (by tauto)
  · intro a t
    rfl

-- The pair (X, ∅ ) has the HEP:
lemma HEP_empty : HEP X ∅ := by
  intro Y hY rangeH' f H hf1 hf2 hH1 hH2 hAgree
  let H' : X × ℝ → Y := fun (x,t) ↦ f x
  use H'
  refine ⟨?_, ?_ ,?_, ?_ ⟩
  · exact (Continuous.fst' hf1).continuousOn
  · intro x hx
    unfold H'
    apply hf2
    simp only [Set.mem_range, exists_apply_eq_apply]
  · intro x
    rfl
  · simp only [H', Subtype.forall, IsEmpty.forall_iff,]

-- Proof, that it is equivalent to define the HEP with rangeH' or without:
open Classical in
lemma HEP_iff_HEPY (X : Type u) [TopologicalSpace X] (A : Set X) : HEP X A ↔ HEPY X A := by
  constructor
  · intro h Y _ f H hf hH hfH
    obtain ⟨H', hH'⟩ := h Y (@Set.univ Y) f H hf (by simp) hH (by simp) hfH
    use H'
    exact ⟨hH'.ContinuousOn, hH'.agreef , hH'.agreeH⟩
  · intro h Y hY rangeH' f H hf1 hf2 hH1 hH2 hfH
    let fr : X → rangeH' := fun p ↦ ⟨f p, hf2 (Set.mem_range_self p)⟩
    by_cases hX : Nonempty X
    · have hrange : Nonempty rangeH' := by
        let x := Classical.choice hX
        use f x
        exact hf2 (Set.mem_range_self x)
      let Hr : X × ℝ → rangeH' := fun p ↦
        if hp : p ∈ (smalcyl A) then ⟨H p, hH2 hp⟩
        else Classical.choice hrange
      have Hr_continuousOn : ContinuousOn Hr (smalcyl A) := by
        rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
        refine hH1.congr ?_
        intro p hp
        have hval : Hr p = ⟨H p, hH2 hp⟩ := dif_pos hp
        rw [Function.comp_apply, hval]
      have agree_r : agreeOn fr Hr A := by
        intro a ha
        simp only [Set.mem_Icc, Set.mem_setOf_eq, ha, Std.le_refl, zero_le_one, and_self,
          ↓reduceDIte, Subtype.mk.injEq, fr, Hr]
        exact hfH a ha
      obtain ⟨H', hH1', hH2', hH3'⟩  := h rangeH' fr Hr (by fun_prop) Hr_continuousOn agree_r
      use (fun p ↦ H' p)
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
      have : (cyl X) = ∅ := by
        have := @Prod.isEmpty_left X ℝ hX
        rw [← Set.univ_eq_empty_iff] at this
        exact  Set.subset_eq_empty (Set.setOf_subset.mpr fun x a ↦ trivial) this
      rw[this]
      exact (Set.mapsTo_empty H' rangeH')

/-
  **Corollary 2.25** for closed: Let A be a closed subset of a topological space X.
  Then A ⊆ X has the HEP ↔
  for every topological space Y and every continuous map g: (X × {0}) ∪ (A × [0,1]) → Y there
  exists an extension of g to a map G : X × [0,1] → Y:
  The following lemma `if_HEP_then_extension` is the forward direction of the proof, which does not
  require the closedness condition on A.
-/

def ExtensionProperty (X : Type u) [TopologicalSpace X] (A : Set X) : Prop :=
  ∀ (Y : Type u) [TopologicalSpace Y] (rangeG : Set Y) (g : X × ℝ → Y),
  ContinuousOn g (anchor A) → (anchor A).MapsTo g rangeG →
  ∃ G : X × ℝ → Y, ContinuousOn G (cyl X) ∧ (cyl X).MapsTo G rangeG ∧
  ∀ q ∈ anchor A, g q = G q

lemma if_HEP_then_extension :
    HEP X A → ExtensionProperty X A := by
  intro hHEP Y hY rangeH' g hg1 hg2
  obtain ⟨G, ⟨hG_cont, hG, hGf, hGH⟩⟩ := hHEP Y rangeH' (fun x ↦ g (x,0)) (fun p ↦ g p)
    (hg1.comp_continuous (Continuous.prodMk_left 0) (by simp))
    (Set.mapsTo_univ_iff_range_subset.mp (fun x hx => hg2 (by simp)))
    (hg1.congr_mono  (by simp [Set.EqOn]) (by grind))
    (fun _ _ => hg2 (by grind)) (fun a x => rfl)
  refine ⟨G, hG_cont , hG, ?_ ⟩
  intro q hq
  cases hq with
  | inl _ => grind
  | inr hA => exact hGH ⟨q.1, hA.1⟩ ⟨q.2, hA.2⟩

-- reverse direction:

def g (f : X → Y) (H : X × ℝ → Y) : X × ℝ → Y := fun q =>
  if q.2 = 0 then f q.1
  else H q

omit [TopologicalSpace X] [TopologicalSpace Y] in
@[simp]
lemma g_apply_zero (f : X → Y) (H : X × ℝ → Y) (x : X) : g f H (x, 0) = f x := if_pos rfl

omit [TopologicalSpace X] [TopologicalSpace Y] in
@[simp]
lemma g_apply_of_ne_zero (f : X → Y) (H : X × ℝ → Y) {q : X × ℝ} (h : q.2 ≠ 0) :
    g f H q = H q := if_neg h

lemma continuousOn_g {A : Set X} (hA : IsClosed A) (f : X → Y) (H : X × ℝ → Y) (hf1 : Continuous f)
  (hH1 : ContinuousOn H (smalcyl A)) (hAgree : agreeOn f H A) :
    ContinuousOn (@g X Y f H) (anchor A) := by
  refine ContinuousOn.union_of_isClosed ?_ ?_ (isClosed_eq continuous_snd continuous_const) ?_
  · have congrcts : ContinuousOn (fun (p : X × ℝ) ↦ f p.1) {p | p.2 = 0} := by fun_prop
    refine ContinuousOn.congr congrcts ?_
    intro x hx
    rw [show x = (x.1, 0) from Prod.ext rfl hx, g_apply_zero]
  · apply ContinuousOn.congr hH1 ?_
    intro x hx
    by_cases h : x.2 = 0
    · rw [show x = (x.1, 0) from Prod.ext rfl h, g_apply_zero]
      exact hAgree x.1 hx.1
    · exact g_apply_of_ne_zero f H h
  · refine IsClosed.and ?_ ?_
    · rw [← @Set.preimage_setOf_eq]
      refine IsClosed.preimage continuous_fst hA
    · exact (isClosed_le continuous_const continuous_snd).and
        (isClosed_le continuous_snd continuous_const)

omit [TopologicalSpace X] [TopologicalSpace Y] in
/-- If `H'` agrees with the glued map `g f H` on the anchor, then it agrees with `H` on `A × I`.
This is the `agreeH` field of `HomotopyExtension`, extracted from an extension of `g f H`. -/
lemma agreeH_of_eq_g (f : X → Y) (H : X × ℝ → Y) (H' : X × ℝ → Y)
  (hAgree : agreeOn f H A) (hgH' : ∀ q ∈ (anchor A), g f H q = H' q)
  (a : X) (ha : a ∈ A) (t : ℝ) (ht : t ∈ unitInterval) :
  H (↑a, ↑t) = H' (↑a, ↑t) := by
  by_cases h : t = 0
  · rw [h, ← hgH' (a, 0) (Or.inl rfl), g_apply_zero]
    exact (hAgree a ha).symm
  · rw [← hgH' (a, t) (Or.inr ⟨ha, ht⟩), g_apply_of_ne_zero _ _ h]

lemma if_extension_then_HEP {A : Set X} (hA : IsClosed A) :
    ExtensionProperty X A
    → HEP X A := by
  intro h_extend Y hY rangeH' f H hf1 hf2 hH1 hH2 hAgree
  obtain ⟨G, hGcts, hGrange, hGg⟩ := h_extend Y rangeH' (g f H)
    (continuousOn_g hA f H hf1 hH1 hAgree)
    (fun x hx => by
      by_cases hx_case : x.2 = 0
      · rw [show x = (x.1, 0) from Prod.ext rfl hx_case, g_apply_zero]
        exact hf2 (Set.mem_range_self _)
      · rw [g_apply_of_ne_zero f H hx_case]
        exact hH2 (hx.resolve_left hx_case))
  refine ⟨G, hGcts, hGrange, fun x => ?_,
    fun a t => agreeH_of_eq_g f H G hAgree hGg a a.2 t t.2⟩
  rw [← g_apply_zero f H x]
  exact hGg (x, 0) (Or.inl rfl)

-- Definition of a `retraction`:
structure RetractionOn (r : X → X) (B A : Set X) : Prop where
  subset : A ⊆ B
  continuousOn : ContinuousOn r B
  mapsTo : B.MapsTo r A
  fixesOn : ∀ a ∈ A, r a = a

/-
  **Lemma 2.26**: A ⊆ X subspace, then TFAE:
  (i): ∀ g : A → Y, there exists an extension G : X → Y
  (ii): A is a retract of X, i.e. ∃ r: X → A s.th. r is the indentity on A
-/

lemma extension_iff_retract {A B : Set X} (hAB : A ⊆ B) :
    (∀ (Y : Type u) [TopologicalSpace Y] (rangeG : Set Y) (g : X → Y),
    ContinuousOn g A → A.MapsTo g rangeG →
    ∃ G : X → Y , ContinuousOn G B ∧ B.MapsTo G rangeG ∧ ∀ a ∈ A, g a = G a) ↔
    ∃ r : X → X, RetractionOn r B A := by
  classical
  constructor
  · intro h_extend
    obtain ⟨G, hG1, hG2, hG3⟩ := h_extend X A id (by fun_prop) A.mapsTo_id
    refine ⟨G, hAB,  hG1, hG2, ?_ ⟩
    intro a ha
    rw [← hG3 a ha]
    exact id_eq a
  · intro ⟨r, hr⟩ Y _ _ g hg hgAC
    exact ⟨g ∘ r, hg.comp hr.continuousOn hr.mapsTo, fun _ hb => hgAC (hr.mapsTo hb),
      fun a ha => by simp [hr.fixesOn a ha]⟩

/-
retraction criterion :
  "Corollary 2.27": **Retraction criterion:** A ⊆ X closed.
  (X,A) has the HEP ↔ (X × {0}) ∪ (A × [0,1]) is a retract of X×[0,1]

The condition A ⊆ X closed is only needed for "→".
-/

lemma if_HEP_then_retraction {X : Type u} [TopologicalSpace X] {A : Set X}
    (h_HEP : HEP X A) : ∃ r : X × ℝ → X × ℝ, RetractionOn r (cyl X)
    (anchor A) := by
  apply (extension_iff_retract (by simp)).1
  intro Y hY C g hg_cont hg_mapsto
  obtain ⟨G, hG⟩ := if_HEP_then_extension h_HEP Y C g hg_cont hg_mapsto
  use G

lemma retraction_criterion_closed (hA1 : IsClosed A) :
    HEP X A ↔ ∃ r : X × ℝ → X × ℝ, RetractionOn r (cyl X)
    (anchor A) := by
  refine ⟨if_HEP_then_retraction, ?_ ⟩
  intro ⟨r, hr⟩
  apply if_extension_then_HEP hA1
  intro Y _ C g hg1 hg2
  obtain ⟨G, hG1, hG2, hG3⟩ := (extension_iff_retract hr.subset).2 ⟨r, hr⟩ Y C g hg1 hg2
  exact ⟨G, hG1, hG2, fun a ha => hG3 a ha⟩

-- nützlich?
lemma zeroOrI_subset_I : (anchor A) ⊆ (cyl X) := by
  intro y hy
  obtain h0 | hA := hy
  · rw [Set.mem_setOf, h0]
    exact unitInterval.zero_mem
  · exact hA.2

/-
The next step is to prove the **retraction_criterion_closed'**. This is a version of the retraction
criterion, which corresponds to the definition of HEP' instead of HEP.
The (co-)domain of the retraction map is the ambient space Y × ℝ.

The forward implication is called **if_HEP_then_retraction'** and does not require closedness.
We obtain a retraction from the previous lemma `if_HEP_then_retraction` and then
extend it onto the ambient space. This extension is realised by precomposition with
the map `mapYX`.
-/
/- We need the two maps `mapYX` and `ProjIcc` for the proof.-/
open Classical in
def mapYX {Y : Type u} [TopologicalSpace Y] {X : Set Y} (hX : Nonempty X) : Y → X := fun y ↦
  if hy : y ∈ X then ⟨y, hy⟩
  else Classical.choice hX

lemma ctsOn_mapYX {Y : Type u} [TopologicalSpace Y] {X : Set Y} (hX : Nonempty X) :
    ContinuousOn (mapYX hX) X := by
  refine continuousOn_iff_continuous_restrict.mpr ?_
  unfold mapYX
  simp only [Set.restrict_dite _ _]
  exact continuous_id

def ProjIcc : ℝ → ℝ := fun t ↦ (Set.projIcc (0 : ℝ) 1 zero_le_one t)

lemma proj_mem (t : ℝ) : ProjIcc t ∈ unitInterval :=
  Subtype.coe_prop (Set.projIcc 0 1  zero_le_one t)

@[grind =]
lemma proj_id {t : ℝ} (ht : t ∈ unitInterval) : ProjIcc t = t :=
  congrArg Subtype.val (Set.projIcc_of_mem _ ht)

@[fun_prop]
lemma proj_cont : Continuous ProjIcc := continuous_subtype_val.comp continuous_projIcc

lemma if_HEP_then_retraction' (A X : Set Y) (hAX : A ⊆ X) :
    HEP' X A → ∃ r : Y × ℝ → Y × ℝ, RetractionOn r (smalcyl X) (smalanchor X A) := by
  intro h_hep
  obtain ⟨r, hr⟩ := if_HEP_then_retraction h_hep
  wlog hX : Nonempty X
  · rw [Set.not_nonempty_iff_eq_empty'] at hX
    have hA : A = ∅ := Set.subset_eq_empty hAX hX
    exact ⟨id, by simp [smalcyl, smalanchor, hX, hA], continuous_id.continuousOn,
      by simp [smalcyl, smalanchor, hX, hA], by simp [smalanchor, hX, hA]⟩
  let s : Y × ℝ → Y × ℝ :=
    fun p ↦ (Subtype.val (r ((mapYX hX) p.1, p.2)).1, (r ((mapYX hX) p.1, p.2)).2)
  refine ⟨s, by grind, ?_, ?_ , ?_ ⟩
  · have cts_mapYX : ContinuousOn (fun (p : Y × ℝ) ↦ r ((mapYX hX) p.1, p.2))
      (smalcyl X) := by
      refine hr.continuousOn.comp ?_ (fun _ hy => hy.2)
      refine ContinuousOn.prodMk ?_ continuousOn_snd
      exact (ctsOn_mapYX hX).comp continuousOn_fst (fun _ hy => hy.1)
    refine ContinuousOn.prodMk ?_ cts_mapYX.snd
    exact continuous_subtype_val.comp_continuousOn cts_mapYX.fst
  · intro _ hy
    simp only [hy.1, Set.mem_setOf_eq, Subtype.coe_prop, true_and, s, mapYX]
    exact hr.mapsTo hy.2
  · intro y hy
    have hX : y.1 ∈ X := by
      obtain h0 | hA := hy
      · exact h0.1
      · exact hAX hA.1
    have y_mem : (⟨y.1, hX⟩, y.2) ∈ (anchor (X ↓∩ A)) := by
      obtain h0 | hA := hy
      · exact Or.inl h0.2
      · exact Or.inr hA
    simp only [hX, ↓reduceDIte, s, mapYX,  hr.fixesOn (⟨y.1, hX⟩, y.2) y_mem, Prod.mk.eta]

lemma retraction_criterion_closed' (A X : Set Y) (hAX : A ⊆ X)
    (hA1 : IsClosed A) : HEP' X A ↔ ∃ s : Y × ℝ → Y × ℝ, RetractionOn s (smalcyl X) (smalanchor X A)
    := by
  refine ⟨fun h_HEP' ↦ if_HEP_then_retraction' A X hAX h_HEP', ?_ ⟩
  intro h_retract
  obtain ⟨s, hs⟩ := h_retract
  have mem_source (p : X × ℝ) : ((p.1 : Y), ProjIcc p.2) ∈ (smalcyl X) :=
    ⟨Subtype.coe_prop p.1, proj_mem p.2⟩
  have MapsTo1_s (p : X × ℝ) : (s ((p.1 : Y), ProjIcc p.2)).1 ∈ X := by
    obtain h1 | h2 := hs.mapsTo (mem_source p)
    exacts [h1.1, hAX h2.1]
  let r : X × ℝ → X × ℝ := fun p ↦ (⟨(s (p.1, ProjIcc p.2)).1, MapsTo1_s p⟩,
    (s (p.1, ProjIcc p.2)).2)
  apply (retraction_criterion_closed  hA1.preimage_val).2
  use r
  constructor
  · simp
  · unfold r
    have hr_comp : ContinuousOn (fun p : X × ℝ ↦ s ((p.1 : Y), ProjIcc p.2)) Set.univ :=
      ContinuousOn.comp hs.continuousOn (by fun_prop) (by tauto)
    refine ContinuousOn.prodMk ?_ ?_
    · rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
      exact hr_comp.fst.mono (Set.subset_univ _)
    · exact continuous_snd.comp_continuousOn (hr_comp.mono (by tauto))
  · intro x hx
    simp [Set.mem_setOf_eq, Set.mem_preimage, r, proj_id hx]
    grind [hs.mapsTo (mem_source x)]
  · intro x hx
    have : (x.1.1,x.2) ∈ (smalanchor X A) := by
      simp only [Set.mem_setOf_eq, Subtype.coe_prop, true_and]
      obtain h0 | hA := hx
      · exact Or.inl h0
      · refine Or.inr ⟨by exact Set.mem_preimage.mp hA.1, hA.2 ⟩
    have := hs.fixesOn (x.1.1,x.2) this
    simp[r, proj_id (zeroOrI_subset_I hx), this]

/-
HEP is `preserved under homeomorphisms`:
Let (X,A) and (Y,B) be pairs of topological spaces with A and B closed, and let f : X → Y be a
homeomorphism with f(A) = B. If (X,A) has the HEP, then so does (Y,B).-/

lemma PartialHomeomorph_HEP' {X1 X2 : Set X} (hX : X2 ⊆ X1) {Y1 Y2 : Set Y} (hY : Y2 ⊆ Y1)
    (hHEP : HEP' X1 X2) (f : PartialHomeomorph X Y) (source : X1 = f.source)
    (target : Y1 = f.target) (h2 : f '' X2 = Y2) (hY2closed : IsClosed Y2) :
    HEP' Y1 Y2 := by
  have := h2.symm
  subst target source this
  obtain ⟨r, hr⟩ := if_HEP_then_retraction' X2 f.source hX hHEP
  let r_comp_fsymm : Y × ℝ → X × ℝ := fun p ↦ (r (f.invFun p.1 , p.2))
  let r' : Y × ℝ → Y × ℝ := fun p ↦ (f (r_comp_fsymm p).1, (r_comp_fsymm p).2 )
  apply (retraction_criterion_closed' (f '' X2) f.target hY hY2closed).2
  use r'
  constructor
  · grind
  · have hr_comp_fsymm : ContinuousOn r_comp_fsymm (smalcyl f.target) := by
      apply hr.2.comp ?_ (fun _ hx => ⟨f.map_target hx.1 , hx.2⟩)
      refine ContinuousOn.prodMk ?_ continuousOn_snd
      exact f.continuousOn_symm.comp continuousOn_fst (fun _ hx => hx.1)
    refine ContinuousOn.prodMk ?_ ?_
    · apply f.continuousOn.comp (continuous_fst.comp_continuousOn' hr_comp_fsymm) ?_
      intro x hx
      have : (f.symm x.1, x.2) ∈ (smalcyl f.source) := ⟨f.map_target hx.1, hx.2⟩
      obtain h0 | h1 := hr.3 this
      exacts [h0.1, hX h1.1]
    exact hr_comp_fsymm.snd
  · intro _ hy
    have : (smalcyl f.target).MapsTo r_comp_fsymm (smalanchor f.source X2) :=
      fun _ h => hr.3 ⟨f.mapsTo_symm h.1, h.2⟩
    obtain h0 | h1 := this hy
    exacts [Or.inl ⟨f.mapsTo h0.1 , h0.2⟩, Or.inr ⟨ Set.mem_image_of_mem f h1.1 , h1.2⟩]
  · intro y hy
    have : r_comp_fsymm y = (f.symm y.1, y.2) := by
      apply hr.4 (f.symm y.1 ,y.2)
      obtain h0 | h1 := hy
      · exact Or.inl ⟨ f.mapsTo_symm h0.1, h0.2 ⟩
      · refine Or.inr ⟨ ?_, h1.2⟩
        refine Set.mem_of_mem_of_subset (Set.mem_image_of_mem f.symm h1.1) ?_
        intro _ ⟨ _ , ⟨⟨ _, hx'⟩, hy1 ⟩⟩
        rw[← hy1, ← hx'.2, f.left_inv (hX hx'.1)]
        exact hx'.1
    unfold r'
    rw [this]
    refine Prod.ext (f.right_inv ?_ ) rfl
    obtain h0 | h1 := hy
    exacts [h0.1, hY h1.1]


/-
HEP is `transitive`:
Prop: If (A1,A2) and (A2,A3) are pairs of topological spaces and both of them satisfy the HEP,
   then also the pair (A1,A3) has the HEP.
   The prove is checking the definition of HEP'. We construct the extended homotopy in two steps,
   first using the HEP for (A2,A3) and afterward for (A1,A2).
 -/

open Classical in
lemma HEP_trans (A1 A2 A3 : Set X) (h21_sub : A2 ⊆ A1) (h12_hep : HEP' A1 A2) (h32_sub : A3 ⊆ A2)
    (h23_hep : HEP' A2 A3) : HEP' A1 A3 := by
  intro Y hY rangeH' f H hf1 hf2 hH1 hH2 hagree
  let f2 : A2 → Y := fun p ↦ f ⟨p.val, h21_sub p.prop⟩
  let H2 : A2 × ℝ → Y := fun p ↦ H (⟨p.1.val, h21_sub p.1.prop⟩, p.2)
  obtain ⟨H2', hH2'⟩ := (h23_hep Y rangeH' f2 H2 (by fun_prop) (by grind)
    (hH1.comp (by fun_prop) (fun _ hx => Set.mem_preimage.1 hx))
    (fun x hx => hH2 hx)
    (fun x hx => hagree ⟨x.1, h21_sub x.prop⟩ hx))
  let H2'extend : A1 × ℝ → Y := fun p ↦
    if h : p.1.1 ∈ A2 then H2' (⟨p.1.1,h⟩, p.2)
    else H p
  have H2'extend_apply : ∀ (p : A1 ↓∩ A2) (t : ℝ),  H2'extend (⟨p, h21_sub p.prop⟩,t ) =
    H2' (⟨p.1, Set.mem_preimage.2 p.prop⟩, t) := by
    intro p
    simp [H2'extend, show p.1.1 ∈ A2 by apply Set.mem_preimage.2 p.prop]
  obtain ⟨H1', hH1'⟩ := h12_hep Y rangeH' f H2'extend hf1 hf2
    (by
      rw [continuousOn_iff_continuous_restrict]
      let projfun : (A1 ↓∩ A2) → A2 := fun p ↦ ⟨p, Set.mem_preimage.2 p.prop⟩
      let congrfun: (smalcyl (A1 ↓∩ A2)) → Y :=
        fun p ↦ H2' (projfun ⟨p.1.1, p.prop.1⟩, p.1.2 )
      have ctscongr: Continuous congrfun := by
        unfold congrfun projfun
        exact hH2'.ContinuousOn.comp_continuous (by fun_prop) fun x => x.prop.2
      exact ctscongr.congr fun x => by simp[H2'extend, congrfun, projfun,
        Set.mem_preimage.mp x.prop.1])
    (by
      intro x hx
      rw [H2'extend_apply ⟨x.1, hx.1⟩ x.2]
      exact hH2'.range hx.2)
    (by
      intro x hx
      rw [H2'extend_apply ⟨x, hx⟩ 0]
      exact hH2'.agreef ⟨x.1, Set.mem_preimage.mp hx⟩)
  refine ⟨H1', hH1'.ContinuousOn, hH1'.range, hH1'.agreef, ?_ ⟩
  intro a t
  rw[← hH1'.agreeH ⟨a.1, h32_sub a.prop⟩ t,
    H2'extend_apply ⟨a.1, h32_sub a.prop⟩ t.1,
    ← hH2'.agreeH ⟨⟨ a.1.1, h32_sub a.prop⟩, a.prop⟩ t]

-- Partail homeomorph ohne retraction criterion

-- lemma PartialHomeomorph_HEP'' {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
--     {X1 X2 : Set X} (hX : X2 ⊆ X1) {Y1 Y2 : Set Y} (hY : Y2 ⊆ Y1) (hHEP : HEP' X1 X2)
--     (homeo : PartialHomeomorph X Y) (source : X1 = homeo.source) (target : Y1 = homeo.target)
--     (h2 : homeo '' X2 = Y2) (hX2closed : IsClosed (X2 : Set X)) (hY2closed : IsClosed (Y2 : Set Y)):
--     HEP' Y1 Y2 := by
--   intro Z _ rangeH' f H hf1 hf2 hH1 hH2 hagree
--   subst target source
--   let fX : homeo.source → Z := fun p ↦ f ⟨(homeo.toFun p), homeo.mapsTo p.prop⟩
--   let HX : homeo.source × ℝ → Z := fun p ↦ H (⟨(homeo.toFun p.1), homeo.mapsTo p.1.prop⟩, p.2)
--   have := hHEP Z rangeH' fX HX ?_ ?_ ?_ ?_ ?_
--   · obtain ⟨HX', hHX'⟩ := this
--     let homeo_prod : ↑homeo.target × ℝ → ↑homeo.source × ℝ  :=
--       (fun p ↦ (⟨(homeo.symm p.1), homeo.map_target p.1.2⟩, p.2))
--     use HX' ∘ homeo_prod
--     constructor
--     · have := hHX'.ContinuousOn
--       apply hHX'.ContinuousOn.comp (by
--         refine Continuous.continuousOn ?_
--         simp only [continuous_prodMk, homeo_prod]
--         refine ⟨?_, continuous_snd⟩
--         sorry)
--       intro x
--       simp [homeo_prod]
--     · sorry
--     · sorry
--     · sorry
--   · refine hf1.comp ?_
--     have cts_homeo := homeo.continuousOn
--     apply continuousOn_iff_continuous_restrict.1 at cts_homeo
--     exact (cts_homeo).subtype_mk  fun x ↦ homeo.mapsTo (Subtype.prop x)
--   · apply Set.Subset.trans ?_ hf2
--     exact Set.range_comp_subset_range _ _
--   · unfold HX
--     have : ContinuousOn (fun (p : homeo.source × ℝ) ↦
--       ((⟨ homeo.toPartialEquiv p.1.1, homeo.mapsTo p.1.prop⟩ : { x // x ∈ homeo.target }), p.2))
--       (smalcyl (homeo.source ↓∩ X2)) := by
--       refine ContinuousOn.prodMk ?_ continuousOn_snd
--       simp only [PartialHomeomorph.toFun_eq_coe]
--       sorry
--     apply hH1.comp this ?_
--     intro _ hz
--     simp only [Set.mem_preimage, PartialHomeomorph.toFun_eq_coe, Set.mem_setOf_eq]
--     refine ⟨?_, hz.2⟩
--     rw[← h2]; exact Set.mem_image_of_mem (↑homeo) hz.1
--   · apply Set.MapsTo.comp hH2 ?_
--     intro _ hz
--     refine ⟨ ?_, hz.2⟩
--     rw[← h2]
--     exact Set.mem_image_of_mem (↑homeo) hz.1
--   · sorry
