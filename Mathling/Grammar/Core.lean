    module

    public import Mathlib.Computability.ContextFreeGrammar

    public import LiterateLean
    open scoped LiterateLean

    @[expose] public section

# Mathling / Grammar / Core モジュール

このモジュールは Mathling のこの領域に属する定義、変換、および証明を提供する。公開される契約と依存関係は import 境界で明示し、実装は以下の Lean ブロックに限定する。

```lean
@[expose] public section

/-!
# Grammar hierarchy

Shared context-free grammar utilities, rule-shape predicates, and bundles for
linear, right-linear, left-linear, Chomsky-normal, and Greibach-normal grammars.
-/

namespace Mathling.Grammar

/-- Embed a terminal word into a context-free sentential form. -/
abbrev terminalSymbols {T N : Type*} (w : List T) : List (Symbol T N) :=
  w.map Symbol.terminal

@[simp] theorem terminalSymbols_nil {T N : Type*} :
    terminalSymbols (T := T) (N := N) [] = [] := rfl

@[simp] theorem terminalSymbols_cons {T N : Type*} (a : T) (w : List T) :
    terminalSymbols (N := N) (a :: w) =
      Symbol.terminal a :: terminalSymbols w := rfl

/-- Rename the nonterminal carried by a symbol, preserving terminals. -/
def Symbol.mapNonterminal {T N M : Type*} (f : N → M) :
    Symbol T N → Symbol T M
  | .terminal a => .terminal a
  | .nonterminal A => .nonterminal (f A)

@[simp] theorem Symbol.mapNonterminal_terminal {T N M : Type*}
    (f : N → M) (a : T) :
    Symbol.mapNonterminal f (.terminal a) = .terminal a := rfl

@[simp] theorem Symbol.mapNonterminal_nonterminal {T N M : Type*}
    (f : N → M) (A : N) :
    Symbol.mapNonterminal f (.nonterminal A : Symbol T N) =
      (.nonterminal (f A) : Symbol T M) := rfl

/-- Rename every nonterminal in a context-free rule. -/
def ContextFreeRule.mapNonterminal {T N M : Type*} (f : N → M)
    (r : ContextFreeRule T N) : ContextFreeRule T M :=
  { input := f r.input, output := r.output.map (Symbol.mapNonterminal f) }

@[simp] theorem ContextFreeRule.mapNonterminal_input {T N M : Type*}
    (f : N → M) (r : ContextFreeRule T N) :
    (ContextFreeRule.mapNonterminal f r).input = f r.input := rfl

@[simp] theorem ContextFreeRule.mapNonterminal_output {T N M : Type*}
    (f : N → M) (r : ContextFreeRule T N) :
    (ContextFreeRule.mapNonterminal f r).output =
      r.output.map (Symbol.mapNonterminal f) := rfl

/-- Whether a symbol is structurally a nonterminal. -/
def Symbol.IsNonterminal {T N : Type*} : Symbol T N → Prop
  | .terminal _ => False
  | .nonterminal _ => True

@[simp] theorem Symbol.isNonterminal_terminal {T N : Type*} (a : T) :
    Symbol.IsNonterminal (.terminal a : Symbol T N) = False := rfl

@[simp] theorem Symbol.isNonterminal_nonterminal {T N : Type*} (A : N) :
    Symbol.IsNonterminal (.nonterminal A : Symbol T N) = True := rfl

/-- Every symbol in the sentential form is a nonterminal. -/
def allNonterminals {T N : Type*} (xs : List (Symbol T N)) : Prop :=
  ∀ x ∈ xs, Symbol.IsNonterminal x

def symbolIsNonterminal {T N : Type*} : Symbol T N → Bool
  | .terminal _ => false
  | .nonterminal _ => true


namespace ContextFreeRule

variable {T N : Type*}

/-- The number of nonterminal symbols on the right-hand side of a rule. -/
def nonterminalCount (r : ContextFreeRule T N) : Nat :=
  r.output.countP symbolIsNonterminal

/-- A rule is linear when its output contains at most one nonterminal. -/
def IsLinear (r : ContextFreeRule T N) : Prop :=
  Mathling.Grammar.ContextFreeRule.nonterminalCount r ≤ 1

/-- The one-symbol right-linear normal form. -/
def IsRightLinear (r : ContextFreeRule T N) : Prop :=
  r.output = [] ∨
  (∃ a, r.output = [Symbol.terminal a]) ∨
  (∃ a B, r.output = [Symbol.terminal a, Symbol.nonterminal B])

/-- The one-symbol left-linear normal form. -/
def IsLeftLinear (r : ContextFreeRule T N) : Prop :=
  r.output = [] ∨
  (∃ a, r.output = [Symbol.terminal a]) ∨
  (∃ A a, r.output = [Symbol.nonterminal A, Symbol.terminal a])


/-- Chomsky rule shape, including the standard initial-symbol ε exception. -/
def IsChomskyNormal (S : N) (r : ContextFreeRule T N) : Prop :=
  (r.input = S ∧ r.output = []) ∨
  (∃ a : T, r.output = [Symbol.terminal a]) ∨
  (∃ B C : N, r.output = [Symbol.nonterminal B, Symbol.nonterminal C])

/-- Greibach rule shape, including the standard initial-symbol ε exception. -/
def IsGreibachNormal (S : N) (r : ContextFreeRule T N) : Prop :=
  (r.input = S ∧ r.output = []) ∨
  ∃ a : T, ∃ tail : List N,
    r.output = Symbol.terminal a :: tail.map Symbol.nonterminal
end ContextFreeRule

/-- A context-free grammar all of whose rules are linear. -/
structure LinearGrammar (T : Type*) where
  cfg : ContextFreeGrammar T
  linear : ∀ r ∈ cfg.rules, Mathling.Grammar.ContextFreeRule.IsLinear r

/-- A context-free grammar in one-symbol right-linear normal form. -/
structure RightLinearGrammar (T : Type*) where
  cfg : ContextFreeGrammar T
  rightLinear : ∀ r ∈ cfg.rules, Mathling.Grammar.ContextFreeRule.IsRightLinear r

/-- A context-free grammar in one-symbol left-linear normal form. -/
```

## 実装の継続

次の定義群は前節で確立した型・不変条件・補題を利用して、このモジュールの契約を段階的に拡張する。

```lean
structure LeftLinearGrammar (T : Type*) where
  cfg : ContextFreeGrammar T
  leftLinear : ∀ r ∈ cfg.rules, Mathling.Grammar.ContextFreeRule.IsLeftLinear r


/-- A context-free grammar in Chomsky normal form. -/
structure ChomskyNormalGrammar (T : Type*) where
  cfg : ContextFreeGrammar T
  chomskyNormal : ∀ r ∈ cfg.rules,
    Mathling.Grammar.ContextFreeRule.IsChomskyNormal cfg.initial r
  initial_not_output : ∀ r ∈ cfg.rules,
    Symbol.nonterminal cfg.initial ∉ r.output

/-- A context-free grammar in Greibach normal form. -/
structure GreibachNormalGrammar (T : Type*) where
  cfg : ContextFreeGrammar T
  greibachNormal : ∀ r ∈ cfg.rules,
    Mathling.Grammar.ContextFreeRule.IsGreibachNormal cfg.initial r
  initial_not_output : ∀ r ∈ cfg.rules,
    Symbol.nonterminal cfg.initial ∉ r.output
end Mathling.Grammar

```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
