import RequestProject.PhilosophicalH
/-!
# Vacuity Diagnosis and TriSupport_Joint

Formalizes **Sections 25–26** of *Axiom-Free Ontological Trinity* (Kim, 2026).
-/
namespace OntologicalTrinity
variable [OntPrim]
open OntPrim

/-- NT_edge (Isabelle §25). -/
def NT_edge (A B C : Prop) : Prop :=
  LeU (Arg (A ∧ B)) (Arg C) ∧ ¬EqU (Arg (A ∧ B)) (Arg A) ∧ ¬EqU (Arg (A ∧ B)) (Arg B)

/-- NT_dead (Isabelle §25). -/
def NT_dead : Prop := ∀ A B C : Prop, ¬NT_edge A B C

/-- NT_in_edges_edge (Isabelle §25). -/
def NT_in_edges_edge (C : Prop) : Set (Prop × Prop) :=
  {p | Head p.1 ∧ Head p.2 ∧ Head C ∧ p.1 ≠ p.2 ∧ p.1 ≠ C ∧ p.2 ≠ C ∧ NT_edge p.1 p.2 C}

/-- MaxNT_edge (Isabelle §25). -/
def MaxNT_edge (q : Prop) : Prop :=
  Head q ∧ (∀ r : Prop, Head r → le_card (NT_in_edges_edge r) (NT_in_edges_edge q))

/-- Nontrivial_MaxNT_edge (Isabelle §25). -/
def Nontrivial_MaxNT_edge (q : Prop) : Prop := MaxNT_edge q ∧ NT_in_edges_edge q ≠ ∅

/-- Isabelle §25.1: `NT_in_edges_edge_empty_if_NT_dead`. -/
theorem NT_in_edges_edge_empty_if_NT_dead (hD : NT_dead) (C : Prop) :
    NT_in_edges_edge C = ∅ := by
  ext ⟨a, b⟩; simp [NT_in_edges_edge]; intro _ _ _ _ _ _; exact hD a b C

/-- **Vacuity Theorem** (Isabelle §25.2). -/
theorem MaxNT_edge_iff_Head_if_NT_dead (hD : NT_dead) (q : Prop) :
    MaxNT_edge q ↔ Head q := by
  constructor
  · intro ⟨hH, _⟩; exact hH
  · intro hH; exact ⟨hH, fun r _ => by
      rw [NT_in_edges_edge_empty_if_NT_dead hD r]; exact le_card_empty_left _⟩

/-- Isabelle §25.3: `no_Nontrivial_MaxNT_edge_if_NT_dead`. -/
theorem no_Nontrivial_MaxNT_edge_if_NT_dead (hD : NT_dead) :
    ¬∃ q : Prop, Nontrivial_MaxNT_edge q := by
  intro ⟨q, _, hne⟩; exact hne (NT_in_edges_edge_empty_if_NT_dead hD q)

/-- Subordination collapse (Isabelle §25.5). -/
theorem Subordination_implies_Trivial_Collapse_left {A B : Prop}
    (hAB : LeU (Arg A) (Arg B))
    (MCL : ∀ (e : U) (X Y : Prop), Makes e (X ∧ Y) → Makes e X)
    (MCI : ∀ (e : U) (X Y : Prop), Makes e X → Makes e Y → Makes e (X ∧ Y))
    : EqU (Arg (A ∧ B)) (Arg A) := by
  apply LeU_antisym_eq
  · intro e he; exact MCL e A B he
  · intro e he; exact MCI e A B he (le_pointwise hAB he)

/-- TriSupport_Joint (Isabelle §26). -/
def TriSupport_Joint (a b c : Prop) : Prop :=
  LeU (Arg (b ∧ c)) (Arg a) ∧ LeU (Arg (c ∧ a)) (Arg b) ∧ LeU (Arg (a ∧ b)) (Arg c) ∧
  ¬LeU (Arg a) (Arg b) ∧ ¬LeU (Arg b) (Arg a) ∧
  ¬LeU (Arg b) (Arg c) ∧ ¬LeU (Arg c) (Arg b) ∧
  ¬LeU (Arg c) (Arg a) ∧ ¬LeU (Arg a) (Arg c)

/-- Pair→third closure (Isabelle §26.2). -/
theorem TriSupport_Joint_semantics {a b c : Prop} (h : TriSupport_Joint a b c)
    (MCI : ∀ (e : U) (X Y : Prop), Supports e X → Supports e Y → Supports e (X ∧ Y))
    : (∀ e, Supports e b → Supports e c → Supports e a) ∧
      (∀ e, Supports e c → Supports e a → Supports e b) ∧
      (∀ e, Supports e a → Supports e b → Supports e c) :=
  ⟨fun e hb hc => le_pointwise h.1 (MCI e b c hb hc),
   fun e hc ha => le_pointwise h.2.1 (MCI e c a hc ha),
   fun e ha hb => le_pointwise h.2.2.1 (MCI e a b ha hb)⟩

end OntologicalTrinity
