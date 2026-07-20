module

public import Mathling.CCG.Search

@[expose] public section

/-!
# Relative completeness of the bounded recognizer

If the finite candidate list `K` contains every category needed as a hidden
binary-rule choice, then every inductive derivation is found by the recognizer
with some finite fuel.  The development proceeds through fuel monotonicity and a
one-step binary completeness lemma, reusing the characterization lemmas from
`Search`.
-/

set_option linter.style.longLine false

namespace Mathling.CCG

open Category

/-! ## Fuel monotonicity -/

/-- If a recursive recognizer grows pointwise, unary backtracking successes are preserved. -/
@[grind =>]
theorem unaryBack_mono {rec rec' : List Category → Category → Bool}
    (hrec : ∀ Γ A, rec Γ A = true → rec' Γ A = true)
    {Γ : List Category} {A : Category} (h : tryUnaryStep rec Γ A = true) :
    tryUnaryStep rec' Γ A = true := by
  grind

/-- If a recursive recognizer grows pointwise, binary backtracking successes are preserved. -/
@[grind =>]
theorem binaryBack_mono {K : List Category} {rec rec' : List Category → Category → Bool}
    (hrec : ∀ Γ A, rec Γ A = true → rec' Γ A = true)
    {Γ : List Category} {A : Category} (h : tryBinaryStep K rec Γ A = true) :
    tryBinaryStep K rec' Γ A = true := by
  grind

/-- Increasing the fuel by one preserves successful recognition. -/
@[grind =>]
theorem recognize_mono_succ (K : List Category) :
    ∀ fuel Γ A, recognize K fuel Γ A = true → recognize K (fuel + 1) Γ A = true := by
  intro fuel
  induction fuel with grind

/-- Increasing fuel preserves successful recognition. -/
@[grind =>]
theorem recognize_mono_le (K : List Category) {fuel₁ fuel₂ : Nat} (hle : fuel₁ ≤ fuel₂)
    {Γ : List Category} {A : Category} (h : recognize K fuel₁ Γ A = true) :
    recognize K fuel₂ Γ A = true := by
  induction hle <;> grind

/-! ## One-step binary completeness -/

/-- One binary derivation step is complete for `tryBinaryStep` when `K` contains all hidden choices. -/
@[grind =>]
theorem binaryBack_complete {K : List Category} {rec : List Category → Category → Bool}
    (hK : ∀ A : Category, A ∈ K)
    {Γ Δ : List Category} {A B C : Category}
    (hΓ : isNonemptyList Γ = true) (hΔ : isNonemptyList Δ = true)
    (h₁ : rec Γ A = true) (h₂ : rec Δ B = true)
    (rule : Rule A B C) :
    tryBinaryStep K rec (Γ ++ Δ) C = true := by
  grind

/-- One binary derivation step is complete for `tryBinaryStep` from the exact
finite-candidate bookkeeping carried by `ChartRule`.  This is the version
used for real finite charts, where `K` is finite and cannot contain every
category. -/
@[grind =>]
theorem binaryBack_complete_of_ruleIn {K : List Category} {rec : List Category → Category → Bool}
    {Γ Δ : List Category} {A B C : Category}
    (hΓ : isNonemptyList Γ = true) (hΔ : isNonemptyList Δ = true)
    (h₁ : rec Γ A = true) (h₂ : rec Δ B = true)
    (rule : ChartRule K A B C) :
    tryBinaryStep K rec (Γ ++ Δ) C = true := by
  rw [tryBinaryStep_eq_true_iff]
  obtain ⟨r, hrmem, hleft, hright⟩ := reverseRules_complete_of_ruleIn rule
  refine ⟨(Γ, Δ), nonemptySplits_mem hΓ hΔ, r, hrmem, ?_, ?_⟩
  · simpa [hleft] using h₁
  · simpa [hright] using h₂

/-! ## Completeness -/

/-- Relative completeness: if the finite candidate list `K` contains every
category needed as a hidden binary-rule choice, then every inductive derivation
is found by the recognizer with some finite fuel.  The assumption is stated here
in the simple strong form `∀ A, A ∈ K`; later bounded-normal-form work can
replace it by membership in a concrete finite `K_{Γ,y}` for a fixed derivation. -/
theorem recognize_complete_exists (K : List Category) (hK : ∀ A : Category, A ∈ K)
    {Γ : List Category} {A : Category} (h : Γ ⇒ccg A) :
    ∃ fuel, recognize K fuel Γ A = true := by
  induction h with
  | leaf => exact ⟨0, by grind [recognize]⟩
  | typeRaiseRight h ih =>
      rcases ih with ⟨fuel, hfuel⟩
      refine ⟨fuel + 1, ?_⟩
      grind
  | typeRaiseLeft h ih =>
      rcases ih with ⟨fuel, hfuel⟩
      refine ⟨fuel + 1, ?_⟩
      grind
  | binary h₁ h₂ rule ih₁ ih₂ =>
      rcases ih₁ with ⟨fuel₁, hfuel₁⟩
      rcases ih₂ with ⟨fuel₂, hfuel₂⟩
      have hfuel₁' := recognize_mono_le K (Nat.le_max_left fuel₁ fuel₂) hfuel₁
      have hfuel₂' := recognize_mono_le K (Nat.le_max_right fuel₁ fuel₂) hfuel₂
      have hbinary :=
        binaryBack_complete hK (derives_isNonemptyList h₁) (derives_isNonemptyList h₂)
          hfuel₁' hfuel₂' rule
      refine ⟨max fuel₁ fuel₂ + 1, ?_⟩
      grind

/-- Completeness for the bounded decision wrapper, with enough fuel chosen
existentially. -/
theorem decideWithFuel_complete_exists (K : List Category) (hK : ∀ A : Category, A ∈ K)
    {Γ : List Category} {A : Category} (h : Γ ⇒ccg A) :
    ∃ fuel, decideWithFuel K fuel Γ A = true :=
  recognize_complete_exists K hK h

/-! ## Finite-candidate relative completeness

The previous theorem is convenient for small metatheoretic arguments, but its
assumption `∀ A, A ∈ K` cannot hold for the actual finite candidate list.
`ChartDerivable` gives the paper-facing finite version: once the normal-form/depth
argument has transformed a derivation into one whose categories and rule
metavariables lie in `K`, the executable recognizer finds it with finite fuel.
-/

/-- Bounded derivations have nonempty antecedents. -/
@[grind =>]
theorem chartDerivable_isNonemptyList {K : List Category} {Γ : List Category} {A : Category}
    (h : ChartDerivable K Γ A) :
    isNonemptyList Γ = true :=
  derives_isNonemptyList h.toDerivable

/-- Relative completeness for derivations whose finite-rule bookkeeping is
already in `K`. -/
theorem recognize_complete_exists_of_chartDerivable (K : List Category)
    {Γ : List Category} {A : Category} (h : ChartDerivable K Γ A) :
    ∃ fuel, recognize K fuel Γ A = true := by
  induction h with
  | leaf hA => exact ⟨0, by grind [recognize]⟩
  | typeRaiseRight hC hOut h ih =>
      rcases ih with ⟨fuel, hfuel⟩
      refine ⟨fuel + 1, ?_⟩
      grind
  | typeRaiseLeft hC hOut h ih =>
      rcases ih with ⟨fuel, hfuel⟩
      refine ⟨fuel + 1, ?_⟩
      grind
  | binary h₁ h₂ rule ih₁ ih₂ =>
      rcases ih₁ with ⟨fuel₁, hfuel₁⟩
      rcases ih₂ with ⟨fuel₂, hfuel₂⟩
      have hfuel₁' := recognize_mono_le K (Nat.le_max_left fuel₁ fuel₂) hfuel₁
      have hfuel₂' := recognize_mono_le K (Nat.le_max_right fuel₁ fuel₂) hfuel₂
      have hbinary :=
        binaryBack_complete_of_ruleIn (chartDerivable_isNonemptyList h₁) (chartDerivable_isNonemptyList h₂)
          hfuel₁' hfuel₂' rule
      refine ⟨max fuel₁ fuel₂ + 1, ?_⟩
      grind

/-- Completeness for the bounded decision wrapper from a `ChartDerivable` witness,
with sufficiently large fuel chosen existentially. -/
theorem decideWithFuel_complete_exists_of_chartDerivable (K : List Category)
    {Γ : List Category} {A : Category} (h : ChartDerivable K Γ A) :
    ∃ fuel, decideWithFuel K fuel Γ A = true :=
  recognize_complete_exists_of_chartDerivable K h

end Mathling.CCG
