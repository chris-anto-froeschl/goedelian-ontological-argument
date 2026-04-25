import RequestProject.Exclusions
/-!
# Trinity Forcing, Actuality, and Final Results

Formalizes **Sections 31–42** of *Axiom-Free Ontological Trinity* (Kim, 2026).
-/
set_option linter.unusedSectionVars false

namespace OntologicalTrinity
variable [OntPrim] [EpPrim]
open OntPrim EpPrim

/-! ## Section 31.1: Case labels and forcing -/

/-- N1_exact (Isabelle §31.1). -/
def N1_exact : Prop := MaxNT_candidate ExactlyOneHeadP
/-- N2_exact (Isabelle §31.1). -/
def N2_exact : Prop := MaxNT_candidate_N2 ExactlyTwoHeadsP
/-- N4plus (Isabelle §31.1). -/
def N4plus : Prop :=
  ∃ a b c d : Prop, H_opt_ep a ∧ H_opt_ep b ∧ H_opt_ep c ∧ H_opt_ep d ∧
    EDia_ep a ∧ EDia_ep b ∧ EDia_ep c ∧ EDia_ep d ∧
    ¬EqNT_ep a b ∧ ¬EqNT_ep a c ∧ ¬EqNT_ep a d ∧
    ¬EqNT_ep b c ∧ ¬EqNT_ep b d ∧ ¬EqNT_ep c d

/-- **Forcing lemma** (Isabelle §31.1). -/
theorem force_N3_from_exhaust_and_exclusions
    (hExhaust : N1_exact ∨ N2_exact ∨ N3 ∨ N4plus)
    (hNoN1 : ¬N1_exact) (hNoN2 : ¬N2_exact) (hNoN4 : ¬N4plus) : N3 := by tauto

/-- **Clean forced-N3** (Isabelle §31.1: `N3_forced_clean`). -/
theorem N3_forced_clean
    (DN : ¬¬∃ x : Prop, H_opt x)
    (Exhaust : (∃ x, H_opt x) → N1_exact ∨ N2_exact ∨ N3 ∨ N4plus)
    (hNoN1 : ¬N1_exact) (hNoN2 : ¬N2_exact) (hNoN4 : ¬N4plus) : N3 :=
  force_N3_from_exhaust_and_exclusions
    (Exhaust (Classical.byContradiction fun h => DN fun hx => h hx)) hNoN1 hNoN2 hNoN4

/-! ## Section 31.2: Actuality at e0 -/

/-- TriuneGod_e0 (Isabelle §31.2). -/
def TriuneGod_e0 : Prop :=
  ∃ a b c : Prop, H_opt a ∧ H_opt b ∧ H_opt c ∧
    ((Supports e0 b ∧ Supports e0 c) → Supports e0 a) ∧
    ((Supports e0 c ∧ Supports e0 a) → Supports e0 b) ∧
    ((Supports e0 a ∧ Supports e0 b) → Supports e0 c)

/-- **TriuneGod_e0 from N3** (Isabelle §31.2). -/
theorem TriuneGod_e0_holds_from_N3 (hN3 : N3) : TriuneGod_e0 := by
  obtain ⟨a, b, c, ha, hb, hc, _, sbc, sca, sab⟩ := hN3
  exact ⟨a, b, c, ha, hb, hc,
    fun ⟨hb', hc'⟩ => sbc e0 ⟨hb', hc'⟩,
    fun ⟨hc', ha'⟩ => sca e0 ⟨hc', ha'⟩,
    fun ⟨ha', hb'⟩ => sab e0 ⟨ha', hb'⟩⟩

/-! ## Section 31.3: God existence -/

/-- GodExists_U (Isabelle §31.3). -/
def GodExists_U : Prop := ∃ x : Prop, H_opt x
/-- GodExists_U_from_DN (Isabelle §31.3). -/
theorem GodExists_U_from_DN (DN : ¬¬∃ x : Prop, H_opt x) : GodExists_U :=
  Classical.byContradiction fun h => DN fun ⟨x, hx⟩ => h ⟨x, hx⟩
/-- GodExists_world (Isabelle §31.3). -/
def GodExists_world : Prop := GodExists_U

/-! ## Section 32: Disjunctive-causal collapse -/

/-- **Disjunctive causation collapse** (Isabelle §32). -/
theorem disjunctive_causation_collapse {A B C : Prop}
    (h1 : (A ∨ B) → C) (h2 : (A ∨ C) → B) (h3 : (B ∨ C) → A) :
    (A ↔ C) ∧ (B ↔ C) ∧ (A ↔ B) :=
  ⟨⟨fun ha => h1 (.inl ha), fun hc => h3 (.inr hc)⟩,
   ⟨fun hb => h1 (.inr hb), fun hc => h2 (.inr hc)⟩,
   ⟨fun ha => h2 (.inl ha), fun hb => h3 (.inl hb)⟩⟩

/-- Isabelle §32: `no_disjunctive_trinity`. -/
theorem no_disjunctive_trinity {A B C : Prop}
    (h1 : (A ∨ B) → C) (h2 : (A ∨ C) → B) (h3 : (B ∨ C) → A)
    (hne : ¬(A ↔ B) ∨ ¬(B ↔ C) ∨ ¬(A ↔ C)) : False := by
  have ⟨hAC, hBC, hAB⟩ := disjunctive_causation_collapse h1 h2 h3; tauto

/-! ## Section 33–34: Trinity and truthmaking -/

/-- Trinity (Isabelle §33). -/
def Trinity (Φ Ω ψ : Prop) : Prop := Φ ∧ Ω ∧ ψ

/-- Isabelle §33: `Trinity_equiv_from_T_and_S_strong`. -/
theorem Trinity_equiv_from_T_and_S_strong {Φ Ω ψ R : Prop}
    (hT : Trinity Φ Ω ψ → R) (hS : ¬Trinity Φ Ω ψ → ¬R) :
    (Trinity Φ Ω ψ ↔ R) ∧ (R → Φ) ∧ (R → Ω) ∧ (R → ψ) := by
  have hR : R → Trinity Φ Ω ψ := by tauto
  exact ⟨⟨hT, hR⟩, fun hr => (hR hr).1, fun hr => (hR hr).2.1, fun hr => (hR hr).2.2⟩

/-! ## Section 35: Relative Certainty -/

/-- Isabelle §35.2: `RelCert_pointwise`. -/
theorem RelCert_pointwise {R S : Prop} (hRC : RelCert R S)
    {e : U} (hR : Supports e R) : Supports e S := le_pointwise hRC.1 hR

/-- Ontological grounding (Isabelle §35.4). -/
def Ground (S R : Prop) : Prop := RelCert R S

/-! ## Section 36: Ontological Origin Truth -/

/-- Ontological_Origin_Truth (Isabelle §36). -/
def Ontological_Origin_Truth (q : Prop) : Prop :=
  (∀ ζ ∈ PDom, LeU (Arg ζ) (Arg q)) ∧ (∀ ζ ∈ PDom, ¬LtU (Arg q) (Arg ζ))

/-- Isabelle §36: `Hopt_is_Ontological_Origin_Truth`. -/
theorem Hopt_is_Ontological_Origin_Truth {q : Prop}
    (hq : H_opt q) (hPH : PH (Arg q)) : Ontological_Origin_Truth q :=
  ⟨fun ζ hζ => hPH ζ hζ, argument_finality_PDom hq⟩

/-! ## Section 39: Ordinal/Cardinal Transcendence -/

/-- Ord3 (Isabelle §39). -/
inductive Ord3 where | O1 | O2 | O3 deriving DecidableEq, Fintype

/-- cap on ord3 (Isabelle §39). -/
def capO : Ord3 → Ord3 → Ord3
  | .O1, _ => .O1 | .O2, .O1 => .O1 | .O2, .O2 => .O2 | .O2, .O3 => .O2 | .O3, y => y

/-- ltO on ord3 (Isabelle §39). -/
def ltO : Ord3 → Ord3 → Bool
  | .O1, .O2 => true | .O1, .O3 => true | .O2, .O3 => true | _, _ => false

/-- Person (Isabelle §39). -/
inductive Person where | F | S | G deriving DecidableEq, Fintype

/-- preserves_trinity_on_ord3 (Isabelle §39). -/
def preserves_trinity_on_ord3 (f : Person → Ord3) : Prop :=
  Function.Bijective f ∧
  ltO (capO (f .F) (f .S)) (f .G) = true ∧
  ltO (capO (f .F) (f .G)) (f .S) = true ∧
  ltO (capO (f .S) (f .G)) (f .F) = true

/-- **No ordinal embedding** (Isabelle §39). -/
theorem no_ordinal_embedding_for_trinity :
    ¬∃ f : Person → Ord3, preserves_trinity_on_ord3 f := by
  intro ⟨f, hbij, hFSG, hFGS, hSGF⟩
  have hF : f .F ≠ .O1 := by
    intro h; rw [h] at hSGF; cases f .S <;> cases f .G <;> simp_all [capO, ltO]
  have hS : f .S ≠ .O1 := by
    intro h; rw [h] at hFGS; cases f .F <;> cases f .G <;> simp_all [capO, ltO]
  have hG : f .G ≠ .O1 := by
    intro h; rw [h] at hFSG; cases f .F <;> cases f .S <;> simp_all [capO, ltO]
  obtain ⟨p, hp⟩ := hbij.surjective .O1; cases p <;> simp_all

/-- **Oneness** (Isabelle §39). -/
theorem oneness_global {E : Type*} [DecidableEq E]
    (essence : Person → E)
    (hFS : essence .F = essence .S) (hSG : essence .S = essence .G) :
    (Finset.image essence Finset.univ).card = 1 := by
  have : Finset.image essence Finset.univ = {essence .F} := by
    ext x; simp [Finset.mem_image]; constructor
    · rintro ⟨p, _, rfl⟩; cases p <;> simp_all
    · intro h; exact ⟨.F, h.symm⟩
  rw [this]; simp

/-! ## Section 40: Uniqueness of the Trinity -/

/-- Trinity_Uniqueness_MaxCov locale (Isabelle §40). -/
structure TrinityUniquenessMaxCov (MaxCov : U → Prop) : Prop where
  sym : ∀ p q : U, EqU p q → EqU q p
  trans : ∀ p q r : U, EqU p q → EqU q r → EqU p r
  excl4 : ∀ a b c d : U, MaxCov a → MaxCov b → MaxCov c → MaxCov d →
    ¬EqU a b → ¬EqU a c → ¬EqU b c → ¬EqU a d → ¬EqU b d → ¬EqU c d → False

/-- TrinityTop3_mc (Isabelle §40). -/
def TrinityTop3_mc (MaxCov : U → Prop) (A B C : U) : Prop :=
  MaxCov A ∧ MaxCov B ∧ MaxCov C ∧ ¬EqU A B ∧ ¬EqU A C ∧ ¬EqU B C

/-- Top3Classes (Isabelle §40). -/
def Top3Classes (A B C : U) : Set U := {x | EqU x A ∨ EqU x B ∨ EqU x C}

/-- Every MaxCov falls into one of three classes (Isabelle §40). -/
theorem MaxCov_must_fall_into_Top3Classes {MaxCov : U → Prop}
    (h : TrinityUniquenessMaxCov MaxCov) {A B C : U}
    (hT : TrinityTop3_mc MaxCov A B C) {X : U} (hX : MaxCov X) :
    EqU X A ∨ EqU X B ∨ EqU X C := by
  by_contra hne; push_neg at hne
  exact h.excl4 A B C X hT.1 hT.2.1 hT.2.2.1 hX
    hT.2.2.2.1 hT.2.2.2.2.1 hT.2.2.2.2.2
    (fun h' => hne.1 (h.sym A X h'))
    (fun h' => hne.2.1 (h.sym B X h'))
    (fun h' => hne.2.2 (h.sym C X h'))

/-- **Top3Classes unique** (Isabelle §40). -/
theorem Top3Classes_unique {MaxCov : U → Prop}
    (h : TrinityUniquenessMaxCov MaxCov) {A B C A' B' C' : U}
    (hT1 : TrinityTop3_mc MaxCov A B C) (hT2 : TrinityTop3_mc MaxCov A' B' C') :
    Top3Classes A B C = Top3Classes A' B' C' := by
  ext x; simp only [Top3Classes, Set.mem_setOf_eq]; constructor
  · intro hx
    have lift : ∀ {Y : U}, MaxCov Y → EqU x Y →
        EqU x A' ∨ EqU x B' ∨ EqU x C' := by
      intro Y hMY hxY
      rcases MaxCov_must_fall_into_Top3Classes h hT2 hMY with h'|h'|h'
      · exact .inl (h.trans x Y A' hxY h')
      · exact .inr (.inl (h.trans x Y B' hxY h'))
      · exact .inr (.inr (h.trans x Y C' hxY h'))
    rcases hx with hxA|hxB|hxC
    · exact lift hT1.1 hxA
    · exact lift hT1.2.1 hxB
    · exact lift hT1.2.2.1 hxC
  · intro hx
    have lift : ∀ {Y : U}, MaxCov Y → EqU x Y →
        EqU x A ∨ EqU x B ∨ EqU x C := by
      intro Y hMY hxY
      rcases MaxCov_must_fall_into_Top3Classes h hT1 hMY with h'|h'|h'
      · exact .inl (h.trans x Y A hxY h')
      · exact .inr (.inl (h.trans x Y B hxY h'))
      · exact .inr (.inr (h.trans x Y C hxY h'))
    rcases hx with hxA'|hxB'|hxC'
    · exact lift hT2.1 hxA'
    · exact lift hT2.2.1 hxB'
    · exact lift hT2.2.2.1 hxC'

/-! ## Section 41: Wrappers -/

/-- **God finality** (Isabelle §41). -/
theorem God_finality {q : Prop} (hq : H_opt q) :
    ∀ ζ ∈ PDom, ¬LtU (Arg q) (Arg ζ) := argument_finality_PDom hq

/-- **Trinity actuality** (Isabelle §41). -/
theorem Trinity_actuality {a b c : Prop} (h3 : Hopt3 a b c)
    (MCI : ∀ (e : U) (X Y : Prop), Supports e X → Supports e Y → Supports e (X ∧ Y))
    : N3 := OnlyN3_from_Hopt3_unboxed h3 MCI

/-- Contingency Preserved (Isabelle §37). -/
theorem Contingency_Preserved [ModalPrim] (Φ Ω ψ R : Prop)
    (_ : Trinity Φ Ω ψ → ModalPrim.MDia R) :
    (Trinity Φ Ω ψ → R) ∨ ¬(Trinity Φ Ω ψ → R) := Classical.em _

end OntologicalTrinity
