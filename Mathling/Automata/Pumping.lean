module

public import Mathling.Automata.Finite

@[expose] public section

/-!
# Pumping lemma for regular languages

This module transfers Mathlib's DFA pumping lemma to `Language.IsRegular`.
-/

namespace Mathling.Automata

open Computability

/-- Every regular language satisfies the pumping lemma. -/
theorem Language.IsRegular.pumping_lemma {α : Type*} {L : Language α} (h : L.IsRegular) :
    ∃ p ≥ 1, ∀ x ∈ L, p ≤ x.length →
      ∃ a b c, x = a ++ b ++ c ∧ a.length + b.length ≤ p ∧ b ≠ [] ∧
        ({a} : Language α) * ({b} : Language α)∗ * ({c} : Language α) ≤ L := by
  rcases h with ⟨σ, _, M, rfl⟩
  refine ⟨Fintype.card σ, Fintype.card_pos_iff.mpr ⟨M.start⟩, ?_⟩
  intro x hx hlen
  exact M.pumping_lemma hx hlen

end Mathling.Automata
