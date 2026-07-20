    module

    public import Mathling.Grammar.Core
    public import Mathlib.Data.Finset.Union
    public import Mathlib.Data.List.Sublists

    public import LiterateLean
    open scoped LiterateLean

    @[expose] public section

# Mathling / Grammar / ContextFree モジュール

このモジュールは Mathling のこの領域に属する定義、変換、および証明を提供する。公開される契約と依存関係は import 境界で明示し、実装は以下の Lean ブロックに限定する。

```lean
@[expose] public section

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
def activeNonterminals (g : ContextFreeGrammar T) [DecidableEq g.NT] : Finset g.NT :=
  {g.initial} ∪ g.rules.biUnion fun r =>
    (ContextFreeRule.nonterminals r).toFinset

@[simp] theorem initial_mem_activeNonterminals (g : ContextFreeGrammar T)
    [DecidableEq g.NT] :
    g.initial ∈ activeNonterminals g := by
  classical
  simp [activeNonterminals]

theorem rule_input_mem_activeNonterminals (g : ContextFreeGrammar T)
    [DecidableEq g.NT]
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
    [DecidableEq g.NT]
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
```

## 実装の継続

次の定義群は前節で確立した型・不変条件・補題を利用して、このモジュールの契約を段階的に拡張する。

```lean
theorem derives_terminals_eq (g : ContextFreeGrammar T) {u v : List T} :
    g.Derives (terminalSymbols u) (terminalSymbols v) → u = v := by
  intro h
  rcases h.eq_or_head with heq | ⟨_, ⟨r, _, hr⟩, _⟩
  · exact terminalSymbols_injective heq
  · exact (no_rewrites_terminals r hr).elim

mutual
  inductive DerivationSymbolTree (g : ContextFreeGrammar T) :
      Symbol T g.NT → List T → Prop
    | terminal (a : T) : DerivationSymbolTree g (.terminal a) [a]
    | nonterminal (r : ContextFreeRule T g.NT) (hr : r ∈ g.rules)
        {w : List T} (children : DerivationFormTree g r.output w) :
        DerivationSymbolTree g (.nonterminal r.input) w

  inductive DerivationFormTree (g : ContextFreeGrammar T) :
      List (Symbol T g.NT) → List T → Prop
    | nil : DerivationFormTree g [] []
    | cons {x : Symbol T g.NT} {u : List T}
        {xs : List (Symbol T g.NT)} {v : List T}
        (head : DerivationSymbolTree g x u)
        (tail : DerivationFormTree g xs v) :
        DerivationFormTree g (x :: xs) (u ++ v)
end

private theorem derivationFormTree_append (g : ContextFreeGrammar T)
    {xs ys : List (Symbol T g.NT)} {u v : List T}
    (hx : DerivationFormTree g xs u) (hy : DerivationFormTree g ys v) :
    DerivationFormTree g (xs ++ ys) (u ++ v) := by
  cases hx with
  | nil => simpa using hy
  | cons head tail =>
      simpa [List.append_assoc] using
        DerivationFormTree.cons head (derivationFormTree_append g tail hy)
termination_by xs.length

private theorem derivationFormTree_split_append (g : ContextFreeGrammar T)
    {xs ys : List (Symbol T g.NT)} {w : List T}
    (h : DerivationFormTree g (xs ++ ys) w) :
    ∃ u v, w = u ++ v ∧
      DerivationFormTree g xs u ∧ DerivationFormTree g ys v := by
  cases xs with
  | nil => exact ⟨[], w, by simp, DerivationFormTree.nil, by simpa using h⟩
  | cons x xs =>
      cases h with
      | cons head tail =>
          obtain ⟨u, v, rfl, hu, hv⟩ :=
            derivationFormTree_split_append g (xs := xs) (ys := ys) tail
          exact ⟨_, v, by simp [List.append_assoc],
            DerivationFormTree.cons head hu, hv⟩
termination_by xs

private theorem derivationFormTree_terminals (g : ContextFreeGrammar T)
    (w : List T) : DerivationFormTree g (terminalSymbols w) w := by
  induction w with
  | nil => exact DerivationFormTree.nil
  | cons a w ih =>
      simpa [terminalSymbols] using
        DerivationFormTree.cons (DerivationSymbolTree.terminal a) ih

private theorem derivationFormTree_of_produces
    (g : ContextFreeGrammar T)
    {u v : List (Symbol T g.NT)} {w : List T}
    (hstep : g.Produces u v) (hv : DerivationFormTree g v w) :
    DerivationFormTree g u w := by
  rcases hstep with ⟨r, hr, hrewrite⟩
  obtain ⟨p, q, rfl, rfl⟩ := hrewrite.exists_parts
  have hv' : DerivationFormTree g (p ++ (r.output ++ q)) w := by
    simpa [List.append_assoc] using hv
  obtain ⟨wp, wrest, hw, hp, hrest⟩ :=
    derivationFormTree_split_append g (xs := p) (ys := r.output ++ q) hv'
  subst w
  obtain ⟨wout, wq, rfl, hout, hq⟩ :=
    derivationFormTree_split_append g (xs := r.output) (ys := q) hrest
  simpa [List.append_assoc] using
    derivationFormTree_append g hp
      (DerivationFormTree.cons (DerivationSymbolTree.nonterminal r hr hout) hq)

theorem derivationFormTree_of_derives
    (g : ContextFreeGrammar T) {xs : List (Symbol T g.NT)} {w : List T}
    (h : g.Derives xs (terminalSymbols w)) :
    DerivationFormTree g xs w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact derivationFormTree_terminals g w
  | head hstep hrest ih => exact derivationFormTree_of_produces g hstep ih

private theorem derives_cons_of
    (g : ContextFreeGrammar T)
    {x : Symbol T g.NT} {u : List T}
    {xs : List (Symbol T g.NT)} {v : List T}
    (hx : g.Derives [x] (terminalSymbols u))
    (ht : g.Derives xs (terminalSymbols v)) :
    g.Derives (x :: xs) (terminalSymbols (u ++ v)) := by
  have h₁ := hx.append_right xs
  have h₂ := ht.append_left (terminalSymbols u)
  simpa [terminalSymbols, List.map_append, List.append_assoc] using h₁.trans h₂

private theorem derives_of_derivationFormTree
    (g : ContextFreeGrammar T)
    {xs : List (Symbol T g.NT)} {w : List T}
    (h : DerivationFormTree g xs w) :
    g.Derives xs (terminalSymbols w) := by
  exact DerivationFormTree.rec
    (motive_1 := fun x w _ => g.Derives [x] (terminalSymbols w))
    (motive_2 := fun xs w _ => g.Derives xs (terminalSymbols w))
    (fun _ => ContextFreeGrammar.Derives.refl _)
    (fun r hr _ children ih =>
      (ContextFreeGrammar.Produces.single
        ⟨r, hr, ContextFreeRule.Rewrites.input_output⟩).trans ih)
    (ContextFreeGrammar.Derives.refl _)
    (fun _ _ ihHead ihTail => derives_cons_of g ihHead ihTail)
    h

/-- A terminal derivation from a concatenated sentential form splits into terminal
derivations from its two parts. -/
theorem derives_append_split (g : ContextFreeGrammar T)
    {u v : List (Symbol T g.NT)} {w : List T}
    (h : g.Derives (u ++ v) (terminalSymbols w)) :
    ∃ w₁ w₂, w = w₁ ++ w₂ ∧
      g.Derives u (terminalSymbols w₁) ∧
      g.Derives v (terminalSymbols w₂) := by
  obtain ⟨w₁, w₂, hw, hu, hv⟩ :=
    derivationFormTree_split_append g (derivationFormTree_of_derives g h)
  exact ⟨w₁, w₂, hw, derives_of_derivationFormTree g hu,
    derives_of_derivationFormTree g hv⟩

/-- Lift a simulation of source production steps to complete derivations. -/
```

## 実装の継続

次の定義群は前節で確立した型・不変条件・補題を利用して、このモジュールの契約を段階的に拡張する。

```lean
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

```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
