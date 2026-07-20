module

public import Mathling.CCG.Search

@[expose] public section

/-!
# Soundness of the bounded recognizer

Every successful recognizer run yields an inductive `⇒ccg` derivation.  The
per-step lemmas reuse the characterization lemmas from `Search`, so the boolean
search structure is unpacked once rather than re-analyzed in each proof.
-/

namespace Mathling.CCG

open Category

/-- Soundness of the unary backtracking component. -/
@[grind =>]
theorem unaryBack_sound {rec : List Category → Category → Bool}
    (hrec : ∀ Γ A, rec Γ A = true → Γ ⇒ccg A)
    {Γ : List Category} {A : Category} (h : tryUnaryStep rec Γ A = true) : Γ ⇒ccg A := by
  grind

/-- Soundness of the binary backtracking component. -/
@[grind =>]
theorem binaryBack_sound {K : List Category} {rec : List Category → Category → Bool}
    (hrec : ∀ Γ A, rec Γ A = true → Γ ⇒ccg A)
    {Γ : List Category} {A : Category} (h : tryBinaryStep K rec Γ A = true) : Γ ⇒ccg A := by
  rcases (tryBinaryStep_eq_true_iff K rec Γ A).mp h with ⟨p, hp_mem, r, _hr_mem, hleft, hright⟩
  grind

/-- The bounded recognizer is sound for the inductive eight-rule derivability relation. -/
@[grind =>]
theorem recognize_sound (K : List Category) :
    ∀ fuel Γ A, recognize K fuel Γ A = true → Γ ⇒ccg A := by
  intro fuel
  induction fuel with grind

/-- The bounded decision procedure is sound for the inductive derivability relation. -/
@[grind =>]
theorem decideWithFuel_sound {K : List Category} {fuel : Nat} {Γ : List Category} {A : Category}
    (h : decideWithFuel K fuel Γ A = true) : Γ ⇒ccg A :=
  recognize_sound K fuel Γ A h

end Mathling.CCG
