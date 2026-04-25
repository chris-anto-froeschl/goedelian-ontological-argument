import Mathlib
/-!
# U-Layer: Universe, Entailment, and Foundational Definitions

This file formalizes **Sections 14–19** of *Axiom-Free Ontological Trinity* (Kim, 2026).

All primitive types and constants are packaged in the `OntPrim` class (corresponding
to Isabelle's `typedecl U`, `consts Entails`, `consts Arg`, `consts e0`).
The modal operators `MBox`/`MDia` are in `ModalPrim`.
-/

namespace OntologicalTrinity

/-! ## Section 14–16: Primitive types and constants -/

/-- Core primitives of the ontological theory (Isabelle: `typedecl U`, `consts Entails`,
    `consts Arg`, `consts e0`). -/
class OntPrim where
  /-- The abstract universe type (Isabelle: `typedecl U`). -/
  U : Type
  /-- Primitive entailment (Isabelle: `consts Entails :: "U ⇒ U ⇒ bool"`). -/
  Entails : U → U → Prop
  /-- Argument map (Isabelle §17.1: `consts Arg :: "bool ⇒ U"`). -/
  Arg : Prop → U
  /-- Distinguished actuality ground (Isabelle §19: `consts e0 :: U`). -/
  e0 : U

/-- Modal operators (Isabelle §16: `consts Box, Dia`). -/
class ModalPrim where
  /-- Necessity (Isabelle §16: `Box`). -/
  MBox : Prop → Prop
  /-- Possibility (Isabelle §16: `Dia`). -/
  MDia : Prop → Prop

variable [OntPrim]
open OntPrim

/-! ## Section 15: Support sets, preorder and equivalence on U -/

/-- Support set (Isabelle §15: `SuppU u = {e. Entails e u}`). -/
def SuppU (u : U) : Set U := {e | Entails e u}

/-- Preorder on U (Isabelle §15: `p ⪯ q ⟷ SuppU p ⊆ SuppU q`). -/
def LeU (p q : U) : Prop := SuppU p ⊆ SuppU q

/-- Equivalence on U (Isabelle §15: `p ≈ q ⟷ SuppU p = SuppU q`). -/
def EqU (p q : U) : Prop := SuppU p = SuppU q

/-- Strict order (Isabelle §15.2: `p ≺ q ⟷ (p ⪯ q ∧ ¬(q ⪯ p))`). -/
def LtU (p q : U) : Prop := LeU p q ∧ ¬LeU q p

/-! ### Section 15.1: Basic calculus -/

/-- Isabelle §15.1: `LeU_refl`. -/
theorem LeU_refl (p : U) : LeU p p := Set.Subset.refl _

/-- Isabelle §15.1: `LeU_trans`. -/
theorem LeU_trans {p q r : U} (h1 : LeU p q) (h2 : LeU q r) : LeU p r :=
  Set.Subset.trans h1 h2

/-- Isabelle §15.1: `EqU_refl`. -/
theorem EqU_refl (p : U) : EqU p p := rfl

/-- Isabelle §15.1: `EqU_sym`. -/
theorem EqU_sym {p q : U} (h : EqU p q) : EqU q p := h.symm

/-- Isabelle §15.1: `EqU_trans`. -/
theorem EqU_trans {p q r : U} (h1 : EqU p q) (h2 : EqU q r) : EqU p r := h1.trans h2

/-- Isabelle §15.1: `LeU_antisym_eq`. -/
theorem LeU_antisym_eq {p q : U} (h1 : LeU p q) (h2 : LeU q p) : EqU p q :=
  Set.Subset.antisymm h1 h2

/-- Isabelle §15.1: `EqU_iff_LeU_both`. -/
theorem EqU_iff_LeU_both (p q : U) : EqU p q ↔ (LeU p q ∧ LeU q p) := by
  simp [EqU, LeU, Set.Subset.antisymm_iff]

/-- Isabelle §15.1: `le_pointwise`. -/
theorem le_pointwise {p q : U} (h : LeU p q) {e : U} (he : Entails e p) : Entails e q :=
  h he

/-! ### Section 15.2: Extensionality -/

/-- Isabelle §15.2: `EqU_mono_right`. -/
theorem EqU_mono_right {p q r : U} (h : EqU p q) : LeU r p ↔ LeU r q := by
  simp [LeU, EqU] at *; rw [h]

/-! ## Section 17: Relative Certainty – Bridge -/

/-- Support relation (Isabelle §17.1: `Supports e φ ≡ (e ⊢ Arg φ)`). -/
def Supports (e : U) (φ : Prop) : Prop := Entails e (Arg φ)

/-- Epistemic possibility (Isabelle §17.1: `EDia ζ ≡ (∃e. Supports e ζ)`). -/
def EDia (ζ : Prop) : Prop := ∃ e, Supports e ζ

/-- Truthmaking alias (Isabelle §17.1: `Makes e X ≡ Supports e X`). -/
abbrev Makes (e : U) (X : Prop) : Prop := Supports e X

/-- Isabelle §17.1: `LeU_iff_all`. -/
theorem LeU_iff_all (S T : Prop) :
    LeU (Arg S) (Arg T) ↔ (∀ e, Makes e S → Makes e T) := by
  simp [LeU, SuppU, Makes, Supports, Set.subset_def]

/-- Isabelle §17.1: `not_LeU_iff_exists_witness`. -/
theorem not_LeU_iff_exists_witness (S T : Prop) :
    ¬LeU (Arg S) (Arg T) ↔ (∃ a, Makes a S ∧ ¬Makes a T) := by
  rw [LeU_iff_all]; push_neg; rfl

/-- Relative certainty (Isabelle §17.1: `RelCert`). -/
def RelCert (R S : Prop) : Prop := LtU (Arg R) (Arg S)

/-- More certain predicate (Isabelle §17.1). -/
def MoreCertain_pred (Φ' Φ : Prop) : Prop :=
  (∀ e, Makes e Φ' → Makes e Φ) ∧ ¬(∀ e, Makes e Φ → Makes e Φ')

/-! ## Section 17.2: EH -/

/-- EH: maximality over epistemic possibility (Isabelle §17.2). -/
def EH (q : U) : Prop := ∀ ζ : Prop, EDia ζ → LeU (Arg ζ) q

/-- Isabelle §17.2: `EH_inclusion`. -/
theorem EH_inclusion {q : U} (hq : EH q) {ζ : Prop} (hζ : EDia ζ) :
    LeU (Arg ζ) q := hq ζ hζ

/-- Isabelle §17.2: `EH_pointwise`. -/
theorem EH_pointwise {q : U} (hq : EH q) {ζ : Prop} (hζ : EDia ζ)
    {e : U} (he : Supports e ζ) : Entails e q := le_pointwise (EH_inclusion hq hζ) he

/-! ## Section 18: Witness from failure of EH -/

/-- Isabelle §18: `not_EH_witnessE`. -/
theorem not_EH_witnessE {q' : U} (h : ¬EH q') :
    ∃ ζ : Prop, EDia ζ ∧ ¬LeU (Arg ζ) q' := by simp [EH] at h; exact h

/-- Isabelle §18: `witness_from_failure_of_EH`. -/
theorem witness_from_failure_of_EH {a' : Prop} {b c : Prop}
    (hb : EDia b) (hc : EDia c)
    (hdisj : ¬LeU (Arg b) (Arg a') ∨ ¬LeU (Arg c) (Arg a')) : ¬EH (Arg a') := by
  intro hEH; rcases hdisj with h | h
  · exact h (EH_inclusion hEH hb)
  · exact h (EH_inclusion hEH hc)

/-! ## Section 19: TrueNow and TH -/

/-- TrueNow (Isabelle §19: `TrueNow φ ≡ Supports e0 φ`). -/
def TrueNow (φ : Prop) : Prop := Supports e0 φ

/-- TH: maximality over actuality (Isabelle §19). -/
def TH (q : U) : Prop := ∀ φ : Prop, TrueNow φ → LeU (Arg φ) q

/-- TrueNow-support set (Isabelle §19: `TSupp`). -/
def TSupp (q : U) : Set Prop := {φ | TrueNow φ ∧ LeU (Arg φ) q}

/-- Isabelle §19.1: `TSupp_mono`. -/
theorem TSupp_mono {q r : U} (h : LeU q r) : TSupp q ⊆ TSupp r := by
  intro φ ⟨hT, hA⟩; exact ⟨hT, LeU_trans hA h⟩

/-- Isabelle §23: `TrueNow_implies_EDia`. -/
theorem TrueNow_implies_EDia {φ : Prop} (h : TrueNow φ) : EDia φ := ⟨e0, h⟩

/-- Isabelle §23: `EH_implies_TH`. -/
theorem EH_implies_TH {q : U} (h : EH q) : TH q :=
  fun φ hφ => h φ (TrueNow_implies_EDia hφ)

end OntologicalTrinity
