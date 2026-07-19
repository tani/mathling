import Mathling.Grammar.Core
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.Sublists

/-!
# Context-free grammar support

Shared finite-support and derivation utilities used by normal-form conversions.
The semantic notions of rewriting, derivation, and language remain Mathlib's
`ContextFreeGrammar` notions.
-/

namespace Mathling.Grammar

/-- Nonterminals occurring in a sentential form, in their original order. -/
def rhsNonterminals {T N : Type*} : List (Symbol T N) → List N
  | [] => []
  | Symbol.terminal _ :: xs => rhsNonterminals xs
  | Symbol.nonterminal A :: xs => A :: rhsNonterminals xs

namespace ContextFreeRule

/-- The input and all right-hand-side nonterminals of a rule. -/
def nonterminals {T N : Type*} (r : ContextFreeRule T N) : List N :=
  r.input :: rhsNonterminals r.output


/-- Renaming nonterminals preserves a one-rule rewrite. -/
theorem Rewrites.mapNonterminal {T N M : Type*}
    {r : ContextFreeRule T N} {u v : List (Symbol T N)}
    (h : r.Rewrites u v) (f : N → M) :
    (ContextFreeRule.mapNonterminal f r).Rewrites
      (u.map (Symbol.mapNonterminal f))
      (v.map (Symbol.mapNonterminal f)) := by
  induction h with
  | head s =>
      simpa [ContextFreeRule.mapNonterminal, List.map_append] using
        (ContextFreeRule.Rewrites.head
          (r := ContextFreeRule.mapNonterminal f r)
          (s.map (Symbol.mapNonterminal f)))
  | cons x h ih =>
      exact ContextFreeRule.Rewrites.cons (Symbol.mapNonterminal f x) ih
end ContextFreeRule

namespace ContextFreeGrammar

variable {T N : Type*}

/-- The finite support explicitly mentioned by a grammar. -/
noncomputable def activeNonterminals (g : ContextFreeGrammar T) : Finset g.NT := by
  classical
  exact {g.initial} ∪ g.rules.biUnion fun r =>
    (ContextFreeRule.nonterminals r).toFinset

@[simp] theorem initial_mem_activeNonterminals (g : ContextFreeGrammar T) :
    g.initial ∈ activeNonterminals g := by
  classical
  simp [activeNonterminals]

theorem rule_input_mem_activeNonterminals (g : ContextFreeGrammar T)
    {r : ContextFreeRule T g.NT} (hr : r ∈ g.rules) :
    r.input ∈ activeNonterminals g := by
  classical
  simp only [activeNonterminals, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_biUnion]
  right
  exact ⟨r, hr, by simp [ContextFreeRule.nonterminals]⟩

private theorem mem_rhsNonterminals_of_nonterminal_mem
    {xs : List (Symbol T N)} {A : N}
    (hA : Symbol.nonterminal A ∈ xs) : A ∈ rhsNonterminals xs := by
  induction xs with
  | nil => simp at hA
  | cons x xs ih =>
      cases x with
      | terminal a =>
          rcases List.mem_cons.mp hA with hEq | htail
          · cases hEq
          · exact ih htail
      | nonterminal B =>
          rcases List.mem_cons.mp hA with hEq | htail
          · exact List.mem_cons.mpr (Or.inl (Symbol.nonterminal.inj hEq))
          · exact List.mem_cons.mpr (Or.inr (ih htail))

theorem rule_rhs_mem_activeNonterminals (g : ContextFreeGrammar T)
    {r : ContextFreeRule T g.NT} {A : g.NT} (hr : r ∈ g.rules)
    (hA : Symbol.nonterminal A ∈ r.output) :
    A ∈ activeNonterminals g := by
  classical
  simp only [activeNonterminals, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_biUnion]
  right
  refine ⟨r, hr, ?_⟩
  change A ∈ (ContextFreeRule.nonterminals r).toFinset
  simp only [List.mem_toFinset, ContextFreeRule.nonterminals, List.mem_cons]
  exact Or.inr (mem_rhsNonterminals_of_nonterminal_mem hA)

/-- Terminal embedding is injective. -/
theorem terminalSymbols_injective {u v : List T} :
    (terminalSymbols (N := N) u) = terminalSymbols v → u = v := by
  intro h
  induction u generalizing v with
  | nil => simpa using h
  | cons a u ih =>
      cases v with
      | nil => simp at h
      | cons b v =>
          change Symbol.terminal a :: terminalSymbols u =
            Symbol.terminal b :: terminalSymbols v at h
          obtain ⟨hsym, htail⟩ := List.cons.inj h
          cases hsym
          exact congrArg (a :: ·) (ih htail)

/-- A context-free rule cannot rewrite a terminal-only sentential form. -/
theorem no_rewrites_terminals (r : ContextFreeRule T N) {w : List T}
    {v : List (Symbol T N)} :
    r.Rewrites (terminalSymbols w) v → False := by
  intro h
  induction w generalizing v with
  | nil => cases h
  | cons a w ih =>
      cases h with
      | cons _ htail => exact ih htail

/-- A derivation between terminal-only forms does not change the word. -/
theorem derives_terminals_eq (g : ContextFreeGrammar T) {u v : List T} :
    g.Derives (terminalSymbols u) (terminalSymbols v) → u = v := by
  intro h
  rcases h.eq_or_head with heq | ⟨_, ⟨r, _, hr⟩, _⟩
  · exact terminalSymbols_injective heq
  · exact (no_rewrites_terminals r hr).elim

/-- Lift a simulation of source production steps to complete derivations. -/
theorem derives_lift_of_produces
    {g₁ : ContextFreeGrammar T} {g₂ : ContextFreeGrammar T}
    {mapSym : Symbol T g₁.NT → Symbol T g₂.NT}
    (hstep : ∀ {u v}, g₁.Produces u v →
      g₂.Derives (u.map mapSym) (v.map mapSym)) :
    ∀ {u v}, g₁.Derives u v →
      g₂.Derives (u.map mapSym) (v.map mapSym) := by
  intro u v h
  induction h with
  | refl => exact ContextFreeGrammar.Derives.refl _
  | tail hxy hyz ih => exact ih.trans (hstep hyz)

end ContextFreeGrammar
end Mathling.Grammar
