module

public import Mathlib.Computability.DFA
public import Mathlib.Computability.NFA
public import Mathlib.Computability.EpsilonNFA

@[expose] public section

/-!
# Finite automata

Finite automata aliases, conversions, and regular-language characterizations.
-/

namespace Mathling.Automata

/-- Mathlib's deterministic finite automata, re-exported in the Mathling namespace. -/
abbrev DFA (α σ : Type*) := _root_.DFA α σ

/-- Mathlib's nondeterministic finite automata, re-exported in the Mathling namespace. -/
abbrev NFA (α σ : Type*) := _root_.NFA α σ

/-- Mathlib's epsilon-NFAs, re-exported in the Mathling namespace. -/
abbrev εNFA (α σ : Type*) := _root_.εNFA α σ

/-- Converting a DFA to an NFA preserves its language. -/
@[simp] theorem DFA.toNFA_language {α σ : Type*} (M : DFA α σ) :
    M.toNFA.accepts = M.accepts := _root_.DFA.toNFA_correct M

/-- Determinizing an NFA preserves its language. -/
@[simp] theorem NFA.toDFA_language {α σ : Type*} (M : NFA α σ) :
    M.toDFA.accepts = M.accepts := _root_.NFA.toDFA_correct

/-- Removing epsilon transitions preserves an epsilon-NFA's language. -/
@[simp] theorem εNFA.toNFA_language {α σ : Type*} (M : εNFA α σ) :
    M.toNFA.accepts = M.accepts := _root_.εNFA.toNFA_correct M

/-- A language is regular exactly when some finite-state NFA accepts it. -/
theorem Language.isRegular_iff_nfa {α : Type*} {L : Language α} :
    L.IsRegular ↔ ∃ σ : Type*, ∃ _ : Fintype σ, ∃ M : NFA α σ, M.accepts = L := by
  constructor
  · rintro h
    obtain ⟨σ, _, M, rfl⟩ := Language.isRegular_iff.mp h
    exact ⟨σ, inferInstance, M.toNFA, _root_.DFA.toNFA_correct M⟩
  · rintro ⟨σ, _, M, rfl⟩
    apply Language.isRegular_iff.mpr
    exact ⟨Set σ, inferInstance, M.toDFA, _root_.NFA.toDFA_correct⟩

end Mathling.Automata
