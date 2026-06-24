import Mathling.CCG.Search

/-!
# Soundness of the bounded recognizer

Every successful recognizer run yields an inductive `⇒ccg` derivation.  The
per-step lemmas reuse the characterization lemmas from `Search`, so the boolean
search structure is unpacked once rather than re-analyzed in each proof.
-/

namespace Mathling.CCG

open Tp

/-- Soundness of the unary backtracking component. -/
@[grind =>]
theorem unaryBack_sound {rec : List Tp → Tp → Bool}
    (hrec : ∀ Γ A, rec Γ A = true → Γ ⇒ccg A)
    {Γ : List Tp} {A : Tp} (h : unaryBack rec Γ A = true) : Γ ⇒ccg A := by
  grind

/-- Soundness of the binary backtracking component. -/
@[grind =>]
theorem binaryBack_sound {K : List Tp} {rec : List Tp → Tp → Bool}
    (hrec : ∀ Γ A, rec Γ A = true → Γ ⇒ccg A)
    {Γ : List Tp} {A : Tp} (h : binaryBack K rec Γ A = true) : Γ ⇒ccg A := by
  rcases (binaryBack_eq_true_iff K rec Γ A).mp h with ⟨p, hp_mem, r, _hr_mem, hleft, hright⟩
  grind

/-- The bounded recognizer is sound for the inductive eight-rule derivability relation. -/
@[grind =>]
theorem recognizes_sound (K : List Tp) :
    ∀ fuel Γ A, recognizes K fuel Γ A = true → Γ ⇒ccg A := by
  intro fuel
  induction fuel with grind

/-- The bounded decision procedure is sound for the inductive derivability relation. -/
@[grind =>]
theorem decideBounded_sound {K : List Tp} {fuel : Nat} {Γ : List Tp} {A : Tp}
    (h : decideBounded K fuel Γ A = true) : Γ ⇒ccg A :=
  recognizes_sound K fuel Γ A h

end Mathling.CCG
