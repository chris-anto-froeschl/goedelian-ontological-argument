import RequestProject.VacuityTriSupport
/-!
# Exclusion Results: N=1, N=2, N≥4

Formalizes **Sections 27–30** of *Axiom-Free Ontological Trinity* (Kim, 2026).
-/
set_option linter.unusedSectionVars false

namespace OntologicalTrinity
variable [OntPrim]
open OntPrim

/-! ## Epistemic refutation primitives -/

/-- Refutation-domain primitives (Isabelle §27.1, §29.1: `consts Ref`, `typedecl P`, etc.). -/
class EpPrim where
  /-- Refutation predicate (Isabelle §27.1: `consts Ref`). -/
  Ref : Prop → Prop
  /-- Person type (Isabelle §29.1: `typedecl P`). -/
  P : Type
  /-- Conjunction on P (Isabelle §29.1: `consts AndP`). -/
  AndP : P → P → P
  /-- Arg for P (Isabelle §29.1: `consts ArgP`). -/
  ArgP : P → OntPrim.U
  /-- Head predicate on P (Isabelle §29.1: `consts HeadP`). -/
  HeadP : P → Prop

variable [EpPrim]
open EpPrim

/-- EDia_ep (Isabelle §27.1). -/
def EDia_ep (z : Prop) : Prop := ¬Ref z

/-- PDom_ep (Isabelle §27.1). -/
def PDom_ep : Set Prop := {z | TrueNow z ∨ EDia_ep z}

/-- H_negU_strict_ep (Isabelle §27.1). -/
def H_negU_strict_ep (q : Prop) : Prop :=
  ∀ z : Prop, z ∈ PDom_ep → z ≠ q → ¬LtU (Arg q) (Arg z)

/-- Head_ep (Isabelle §27.1). -/
def Head_ep (q : Prop) : Prop := EDia_ep q ∧ H_negU_strict_ep q

/-- NT_pair_support_ep (Isabelle §27.1). -/
def NT_pair_support_ep (A B C : Prop) : Prop :=
  A ≠ B ∧ A ≠ C ∧ B ≠ C ∧ LeU (Arg (A ∧ B)) (Arg C)

/-- NT_in_edges_ep (Isabelle §27.1). -/
def NT_in_edges_ep (C : Prop) : Set (Prop × Prop) :=
  {p | Head_ep p.1 ∧ Head_ep p.2 ∧ Head_ep C ∧ NT_pair_support_ep p.1 p.2 C}

/-- MaxNT_ep (Isabelle §27.1). -/
def MaxNT_ep (q : Prop) : Prop :=
  Head_ep q ∧ (∀ r : Prop, EDia_ep r → le_card (NT_in_edges_ep r) (NT_in_edges_ep q))

/-- H_opt_ep (Isabelle §27.1). -/
def H_opt_ep (q : Prop) : Prop := MaxNT_ep q

/-- EqNT_ep (Isabelle §27.1). -/
def EqNT_ep (X Y : Prop) : Prop := NT_in_edges_ep X = NT_in_edges_ep Y

/-- EH_ep (Isabelle §27.1). -/
def EH_ep (u : U) : Prop := ∀ z : Prop, EDia_ep z → LeU (Arg z) u

/-! ## Section 27.3: Hopt3 ⇒ N3 -/

/-- Hopt3 (Isabelle §27.3). -/
def Hopt3 (a b c : Prop) : Prop :=
  H_opt a ∧ H_opt b ∧ H_opt c ∧ EDia a ∧ EDia b ∧ EDia c ∧ TriSupport_Joint a b c

/-- N3 (Isabelle §27.3). -/
def N3 : Prop :=
  ∃ a b c : Prop, H_opt a ∧ H_opt b ∧ H_opt c ∧ TriSupport_Joint a b c ∧
    (∀ e, Supports e b ∧ Supports e c → Supports e a) ∧
    (∀ e, Supports e c ∧ Supports e a → Supports e b) ∧
    (∀ e, Supports e a ∧ Supports e b → Supports e c)

/-- **Hopt3 ⇒ N3** (Isabelle §27.3: `OnlyN3_from_Hopt3_unboxed`). -/
theorem OnlyN3_from_Hopt3_unboxed {a b c : Prop} (h3 : Hopt3 a b c)
    (MCI : ∀ (e : U) (X Y : Prop), Supports e X → Supports e Y → Supports e (X ∧ Y))
    : N3 := by
  obtain ⟨ha, hb, hc, _, _, _, hTS⟩ := h3
  have ⟨s1, s2, s3⟩ := TriSupport_Joint_semantics hTS MCI
  exact ⟨a, b, c, ha, hb, hc, hTS,
    fun e ⟨hb', hc'⟩ => s1 e hb' hc', fun e ⟨hc', ha'⟩ => s2 e hc' ha',
    fun e ⟨ha', hb'⟩ => s3 e ha' hb'⟩

/-! ## Section 28: N≥4 exclusion -/

/-- Band_Collapse_Superfluous (Isabelle §28.4). -/
structure BandCollapseSuperfluous (ΩΨ Φ : Prop) : Prop where
  ES : EDia_ep ΩΨ
  Cov : LeU (Arg ΩΨ) (Arg Φ)
  NS : LeU (Arg ΩΨ) (Arg Φ) → ∀ Y, H_opt_ep Y → EDia_ep Y →
    LeU (Arg (ΩΨ ∧ Y)) (Arg Φ) → EqU (Arg (ΩΨ ∧ Y)) (Arg ΩΨ)
  MCL : ∀ (e : U) (A B : Prop), Makes e (A ∧ B) → Makes e A
  MCR : ∀ (e : U) (A B : Prop), Makes e (A ∧ B) → Makes e B

/-- Band collapse (Isabelle §28.4). -/
theorem pulled_pair_collapse_in_band (bc : BandCollapseSuperfluous ΩΨ Φ)
    {Y₁ Y₂ : Prop} (hY1 : H_opt_ep Y₁) (eY1 : EDia_ep Y₁)
    (hY2 : H_opt_ep Y₂) (eY2 : EDia_ep Y₂)
    : EqU (Arg (ΩΨ ∧ Y₁)) (Arg (ΩΨ ∧ Y₂)) := by
  have h1 := bc.NS bc.Cov Y₁ hY1 eY1 (LeU_trans (fun e he => bc.MCL e ΩΨ Y₁ he) bc.Cov)
  have h2 := bc.NS bc.Cov Y₂ hY2 eY2 (LeU_trans (fun e he => bc.MCL e ΩΨ Y₂ he) bc.Cov)
  exact EqU_trans h1 (EqU_sym h2)

/-- **N≥4 exclusion** (Isabelle §28.6). -/
theorem no_four_distinct_classes_in_band (bc : BandCollapseSuperfluous ΩΨ Φ)
    {Y₁ Y₂ Y₃ Y₄ : Prop}
    (hY1 : H_opt_ep Y₁) (eY1 : EDia_ep Y₁)
    (hY2 : H_opt_ep Y₂) (eY2 : EDia_ep Y₂)
    (_hY3 : H_opt_ep Y₃) (_eY3 : EDia_ep Y₃)
    (_hY4 : H_opt_ep Y₄) (_eY4 : EDia_ep Y₄)
    : ¬(¬EqU (Arg (ΩΨ ∧ Y₁)) (Arg (ΩΨ ∧ Y₂)) ∧
        ¬EqU (Arg (ΩΨ ∧ Y₁)) (Arg (ΩΨ ∧ Y₃)) ∧
        ¬EqU (Arg (ΩΨ ∧ Y₁)) (Arg (ΩΨ ∧ Y₄)) ∧
        ¬EqU (Arg (ΩΨ ∧ Y₂)) (Arg (ΩΨ ∧ Y₃)) ∧
        ¬EqU (Arg (ΩΨ ∧ Y₂)) (Arg (ΩΨ ∧ Y₄)) ∧
        ¬EqU (Arg (ΩΨ ∧ Y₃)) (Arg (ΩΨ ∧ Y₄))) := by
  intro ⟨h12, _⟩; exact h12 (pulled_pair_collapse_in_band bc hY1 eY1 hY2 eY2)

/-- **NS discharge** (Isabelle §28.8: `core_conj_equiv_basic`). -/
theorem core_conj_equiv_basic {ΩΨ Y : Prop}
    (Core_to_Y : LeU (Arg ΩΨ) (Arg Y))
    (MCL : ∀ (e : U) (A B : Prop), Makes e (A ∧ B) → Makes e A)
    (MCI : ∀ (e : U) (A B : Prop), Makes e A → Makes e B → Makes e (A ∧ B))
    : EqU (Arg (ΩΨ ∧ Y)) (Arg ΩΨ) := by
  apply LeU_antisym_eq
  · intro e he; exact MCL e ΩΨ Y he
  · intro e he; exact MCI e ΩΨ Y he (le_pointwise Core_to_Y he)

/-! ## Section 29–30: N=1 and N=2 exclusion -/

/-- NT_pair_supportP (Isabelle §29.1). -/
def NT_pair_supportP (A B C : EpPrim.P) : Prop :=
  A ≠ B ∧ A ≠ C ∧ B ≠ C ∧ LeU (ArgP (AndP A B)) (ArgP C)

/-- NT_in_edgesP (Isabelle §29.1). -/
def NT_in_edgesP (C : EpPrim.P) : Set (EpPrim.P × EpPrim.P) :=
  {p | HeadP p.1 ∧ HeadP p.2 ∧ HeadP C ∧ NT_pair_supportP p.1 p.2 C}

/-- EdgeExist (Isabelle §29.2). -/
def EdgeExist : Prop := ∃ r : EpPrim.P, HeadP r ∧ NT_in_edgesP r ≠ ∅

/-- ExactlyOneHeadP (Isabelle §29.2). -/
def ExactlyOneHeadP : Prop :=
  ∃ A₀ : EpPrim.P, HeadP A₀ ∧ (∀ C, HeadP C → C = A₀)

/-- **Edge ⇒ ¬OneHead** (Isabelle §29.2). -/
theorem Edge_implies_notOneHead : EdgeExist → ¬ExactlyOneHeadP := by
  intro ⟨r, _, hNE⟩ ⟨A₀, _, hRange⟩
  have hNE' := Set.nonempty_iff_ne_empty.mpr hNE
  obtain ⟨⟨A, B⟩, hA, hB, _, ⟨hAB, _, _, _⟩⟩ := hNE'
  simp at hA hB hAB; exact hAB (by rw [hRange A hA, hRange B hB])

/-- stronger_edge (Isabelle §29.2). -/
def stronger_edge (Q P₀ : Prop) : Prop :=
  EDia_ep (Q ∧ EdgeExist) ∧ ¬EDia_ep (P₀ ∧ EdgeExist)

/-- MaxNT_candidate (Isabelle §29.2). -/
def MaxNT_candidate (P₀ : Prop) : Prop :=
  EDia_ep P₀ ∧ (∀ Q : Prop, EDia_ep Q → ¬stronger_edge Q P₀)

/-- EDia_ep forward propagation (Isabelle §29.2). -/
theorem EDia_ep_forward0
    (notEdia_back : ∀ (P Q : Prop), (P → Q) → ¬EDia_ep Q → ¬EDia_ep P)
    {P₀ Q : Prop} (imp : P₀ → Q) (possP : EDia_ep P₀) : EDia_ep Q := by
  by_contra h; exact notEdia_back P₀ Q imp h possP

/-- **N=1 exclusion** (Isabelle §29.2: `N1_fails_MaxNT_final`). -/
theorem N1_fails_MaxNT_final
    (poss_edge : EDia_ep EdgeExist)
    (notEdia_back : ∀ (P Q : Prop), (P → Q) → ¬EDia_ep Q → ¬EDia_ep P)
    (notEdia_False : ¬EDia_ep False) : ¬MaxNT_candidate ExactlyOneHeadP := by
  intro ⟨_, hno⟩
  have imp_conj : EdgeExist → (¬ExactlyOneHeadP ∧ EdgeExist) :=
    fun h => ⟨Edge_implies_notOneHead h, h⟩
  have p1 := EDia_ep_forward0 notEdia_back imp_conj poss_edge
  have p2 : ¬EDia_ep (ExactlyOneHeadP ∧ EdgeExist) :=
    notEdia_back _ _ (fun ⟨h1, h2⟩ => Edge_implies_notOneHead h2 h1) notEdia_False
  exact hno _ (EDia_ep_forward0 notEdia_back (fun h => h.1) p1) ⟨p1, p2⟩

/-- ExactlyTwoHeadsP (Isabelle §30.6). -/
def ExactlyTwoHeadsP : Prop :=
  ∃ A₀ B₀ : EpPrim.P, A₀ ≠ B₀ ∧ HeadP A₀ ∧ HeadP B₀ ∧
    (∀ C, HeadP C → (C = A₀ ∨ C = B₀))

/-- Edge ⇒ ¬TwoHeads (Isabelle §30.6). -/
theorem Edge_blocks_N2 : EdgeExist → ¬ExactlyTwoHeadsP := by
  intro ⟨r, _, hNE⟩ ⟨A₀, B₀, _, _, _, hRange⟩
  have hNE' := Set.nonempty_iff_ne_empty.mpr hNE
  obtain ⟨⟨A, B⟩, hA, hB, hR', ⟨hAB, hAr, hBr, _⟩⟩ := hNE'
  simp at hA hB hAB hAr hBr
  rcases hRange A hA with rfl | rfl <;> rcases hRange B hB with rfl | rfl <;>
    rcases hRange r hR' with rfl | rfl <;> simp_all

/-- MaxNT_candidate_N2 (Isabelle §30.6). -/
def MaxNT_candidate_N2 (P₀ : Prop) : Prop :=
  EDia_ep P₀ ∧ (∀ Q : Prop, EDia_ep Q → ¬stronger_edge Q P₀)

/-- **N=2 exclusion** (Isabelle §30.6: `N2_fails_MaxNT_final`). -/
theorem N2_fails_MaxNT_final
    (poss_edge : EDia_ep EdgeExist)
    (notEdia_back : ∀ (P Q : Prop), (P → Q) → ¬EDia_ep Q → ¬EDia_ep P)
    (notEdia_False : ¬EDia_ep False) : ¬MaxNT_candidate_N2 ExactlyTwoHeadsP := by
  intro ⟨_, hno⟩
  have imp_conj : EdgeExist → (¬ExactlyTwoHeadsP ∧ EdgeExist) :=
    fun h => ⟨Edge_blocks_N2 h, h⟩
  have p1 := EDia_ep_forward0 notEdia_back imp_conj poss_edge
  have p2 : ¬EDia_ep (ExactlyTwoHeadsP ∧ EdgeExist) :=
    notEdia_back _ _ (fun ⟨h1, h2⟩ => Edge_blocks_N2 h2 h1) notEdia_False
  exact hno _ (EDia_ep_forward0 notEdia_back (fun h => h.1) p1) ⟨p1, p2⟩

end OntologicalTrinity
