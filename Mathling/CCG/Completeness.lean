import Mathling.CCG.Search

/-!
# Relative completeness of the bounded recognizer

If the finite candidate list `K` contains every category needed as a hidden
binary-rule choice, then every inductive derivation is found by the recognizer
with some finite fuel.  The development proceeds through fuel monotonicity and a
one-step binary completeness lemma, reusing the characterization lemmas from
`Search`.
-/

namespace Mathling.CCG

open Tp

/-! ## Fuel monotonicity -/

/-- If a recursive recognizer grows pointwise, unary backtracking successes are preserved. -/
@[grind =>]
theorem unaryBack_mono {rec rec' : List Tp → Tp → Bool}
    (hrec : ∀ Γ A, rec Γ A = true → rec' Γ A = true)
    {Γ : List Tp} {A : Tp} (h : unaryBack rec Γ A = true) :
    unaryBack rec' Γ A = true := by
  grind

/-- If a recursive recognizer grows pointwise, binary backtracking successes are preserved. -/
@[grind =>]
theorem binaryBack_mono {K : List Tp} {rec rec' : List Tp → Tp → Bool}
    (hrec : ∀ Γ A, rec Γ A = true → rec' Γ A = true)
    {Γ : List Tp} {A : Tp} (h : binaryBack K rec Γ A = true) :
    binaryBack K rec' Γ A = true := by
  grind

/-- Increasing the fuel by one preserves successful recognition. -/
@[grind =>]
theorem recognizes_mono_succ (K : List Tp) :
    ∀ fuel Γ A, recognizes K fuel Γ A = true → recognizes K (fuel + 1) Γ A = true := by
  intro fuel
  induction fuel with grind

/-- Increasing fuel preserves successful recognition. -/
@[grind =>]
theorem recognizes_mono_le (K : List Tp) {fuel₁ fuel₂ : Nat} (hle : fuel₁ ≤ fuel₂)
    {Γ : List Tp} {A : Tp} (h : recognizes K fuel₁ Γ A = true) :
    recognizes K fuel₂ Γ A = true := by
  induction hle <;> grind

/-! ## One-step binary completeness -/

/-- One binary derivation step is complete for `binaryBack` when `K` contains all hidden choices. -/
@[grind =>]
theorem binaryBack_complete {K : List Tp} {rec : List Tp → Tp → Bool}
    (hK : ∀ A : Tp, A ∈ K)
    {Γ Δ : List Tp} {A B C : Tp}
    (hΓ : nonemptyList Γ = true) (hΔ : nonemptyList Δ = true)
    (h₁ : rec Γ A = true) (h₂ : rec Δ B = true)
    (rule : BinaryRule A B C) :
    binaryBack K rec (Γ ++ Δ) C = true := by
  grind

/-! ## Completeness -/

/-- Relative completeness: if the finite candidate list `K` contains every
category needed as a hidden binary-rule choice, then every inductive derivation
is found by the recognizer with some finite fuel.  The assumption is stated here
in the simple strong form `∀ A, A ∈ K`; later bounded-normal-form work can
replace it by membership in a concrete finite `K_{Γ,y}` for a fixed derivation. -/
theorem recognizes_complete_exists (K : List Tp) (hK : ∀ A : Tp, A ∈ K)
    {Γ : List Tp} {A : Tp} (h : Γ ⇒ccg A) :
    ∃ fuel, recognizes K fuel Γ A = true := by
  induction h with
  | leaf => exact ⟨0, by grind [recognizes]⟩
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
      have hfuel₁' := recognizes_mono_le K (Nat.le_max_left fuel₁ fuel₂) hfuel₁
      have hfuel₂' := recognizes_mono_le K (Nat.le_max_right fuel₁ fuel₂) hfuel₂
      have hbinary :=
        binaryBack_complete hK (derives_nonemptyList h₁) (derives_nonemptyList h₂)
          hfuel₁' hfuel₂' rule
      refine ⟨max fuel₁ fuel₂ + 1, ?_⟩
      grind

/-- Completeness for the bounded decision wrapper, with enough fuel chosen
existentially. -/
theorem decideBounded_complete_exists (K : List Tp) (hK : ∀ A : Tp, A ∈ K)
    {Γ : List Tp} {A : Tp} (h : Γ ⇒ccg A) :
    ∃ fuel, decideBounded K fuel Γ A = true :=
  recognizes_complete_exists K hK h

end Mathling.CCG
