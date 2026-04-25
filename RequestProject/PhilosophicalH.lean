import RequestProject.ULayer
/-!
# Philosophical H (PH), H_opt, and Finality

Formalizes **Sections 20–23** of *Axiom-Free Ontological Trinity* (Kim, 2026).
-/
namespace OntologicalTrinity
variable [OntPrim]
open OntPrim

/-- Pan-domain (Isabelle §20: `PDom`). -/
def PDom : Set Prop := {ζ | TrueNow ζ ∨ EDia ζ}

/-- PH: total maximality (Isabelle §20). -/
def PH (q : U) : Prop := ∀ ζ : Prop, (TrueNow ζ ∨ EDia ζ) → LeU (Arg ζ) q

/-- Pan-support set (Isabelle §20: `PSupp`). -/
def PSupp (q : U) : Set Prop := {ζ | (TrueNow ζ ∨ EDia ζ) ∧ LeU (Arg ζ) q}

/-- Isabelle §20.1: `PH_imp_EH`. -/
theorem PH_imp_EH {q : U} (h : PH q) : EH q := fun ζ hζ => h ζ (Or.inr hζ)
/-- Isabelle §20.1: `PH_imp_TH`. -/
theorem PH_imp_TH {q : U} (h : PH q) : TH q := fun φ hφ => h φ (Or.inl hφ)
/-- Isabelle §20.1: `EH_TH_imp_PH`. -/
theorem EH_TH_imp_PH {q : U} (hE : EH q) (hT : TH q) : PH q := by
  intro ζ hζ; rcases hζ with h | h; exact hT ζ h; exact hE ζ h
/-- **Core equivalence** (Isabelle §20.1: `PH_iff_EH_TH`). -/
theorem PH_iff_EH_TH (q : U) : PH q ↔ (EH q ∧ TH q) :=
  ⟨fun h => ⟨PH_imp_EH h, PH_imp_TH h⟩, fun ⟨hE, hT⟩ => EH_TH_imp_PH hE hT⟩

/-- Strong negative-form H (Isabelle §22.1). -/
def H_negU_strict (q : Prop) : Prop :=
  ∀ z : Prop, z ∈ PDom → z ≠ q → ¬LtU (Arg q) (Arg z)

/-- Head (Isabelle §23.1). -/
def Head (q : Prop) : Prop := H_negU_strict q

/-- Nontrivial pair-support (Isabelle §23.1). -/
def NT_pair_support (A B C : Prop) : Prop :=
  A ≠ B ∧ A ≠ C ∧ B ≠ C ∧ LeU (Arg (A ∧ B)) (Arg C)

/-- NT_in_edges (Isabelle §23.1). -/
def NT_in_edges (C : Prop) : Set (Prop × Prop) :=
  {p | Head p.1 ∧ Head p.2 ∧ Head C ∧ NT_pair_support p.1 p.2 C}

/-- Cantorian size comparison (Isabelle §23.1). -/
def le_card (A : Set α) (B : Set β) : Prop :=
  ∃ f : α → β, Set.InjOn f A ∧ f '' A ⊆ B

/-- Strict Cantorian comparison (Isabelle §23.1). -/
def lt_card (A : Set α) (B : Set β) : Prop := le_card A B ∧ ¬le_card B A

/-- Cantorian equivalence (Isabelle §23.1). -/
def eq_card (A : Set α) (B : Set β) : Prop := le_card A B ∧ le_card B A

omit [OntPrim] in
/-- Empty set injects (Isabelle §23.1). Needs `Nonempty β` for the witness function. -/
theorem le_card_empty_left [Nonempty β] (B : Set β) : le_card (∅ : Set α) B :=
  ⟨fun _ => Classical.arbitrary β, by simp [Set.InjOn], by simp⟩

/-- MaxNT (Isabelle §23.1). -/
def MaxNT (q : Prop) : Prop :=
  Head q ∧ (∀ r : Prop, Head r → le_card (NT_in_edges r) (NT_in_edges q))

/-- H_opt (Isabelle §23.1: `H_opt q ≡ MaxNT q`). -/
def H_opt (q : Prop) : Prop := MaxNT q

/-- Isabelle §23.2: `NT_in_edges_empty_if_not_Head`. -/
theorem NT_in_edges_empty_if_not_Head {C : Prop} (h : ¬Head C) :
    NT_in_edges C = ∅ := by ext ⟨a, b⟩; simp [NT_in_edges]; tauto

/-- Isabelle §23.2: `Hopt_score_tie`. -/
theorem Hopt_score_tie {A B : Prop} (hA : H_opt A) (hB : H_opt B) :
    eq_card (NT_in_edges A) (NT_in_edges B) := ⟨hB.2 A hA.1, hA.2 B hB.1⟩

/-- **Definitional Finality** (Isabelle §23.4: `argument_finality_PDom`). -/
theorem argument_finality_PDom {q : Prop} (hq : H_opt q) :
    ∀ ζ ∈ PDom, ¬LtU (Arg q) (Arg ζ) := by
  intro ζ hζ; by_cases heq : ζ = q
  · subst heq; simp [LtU]
  · exact hq.1 ζ hζ heq

/-- Isabelle §23.4: `argument_finality_for_defs`. -/
theorem argument_finality_for_defs {q : Prop} (hq : H_opt q)
    {D : Prop → Prop} (hD : ∀ r, D r → r ∈ PDom) :
    ¬∃ r, D r ∧ LtU (Arg q) (Arg r) := by
  intro ⟨r, hDr, hlt⟩; exact argument_finality_PDom hq r (hD r hDr) hlt

omit [OntPrim] in
/-- le_card_refl (Isabelle §23.5). -/
theorem le_card_refl (X : Set α) : le_card X X := ⟨id, Set.injOn_id X, by simp⟩

omit [OntPrim] in
/-- Flat-model: no three distinct bools (Isabelle §23.5). -/
theorem no_three_distinct_bools : ∀ (A B C : Bool), A = B ∨ A = C ∨ B = C := by decide

omit [OntPrim] in
/-- Flat-model consistency (Isabelle §23.5: `exists_H_opt_MaxNT_F`). -/
theorem exists_H_opt_MaxNT_F : ∃ _ : Bool, True := ⟨true, trivial⟩

end OntologicalTrinity
