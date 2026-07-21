    module

    public import Mathling.Automata.Regular.Kleene
    public import Mathling.Grammar.Regular.Right

    public import Mathling.Grammar.Pushdown
    import LiterateLean
    open scoped LiterateLean


# Mathling / Grammar / Regular / Regex モジュール

正規表現の表示言語を正則文法・文脈自由文法の階層へ接続する。正規表現から有限状態機械
への構文帰納的な存在証明と、右線形文法による正則言語の特徴付けを合成するため、この層は
具体的な DFA や文法の内部状態を公開しない。

```mermaid
flowchart LR
    Regex["正規表現"] <-->|isRegular_iff_hasRegularExpression| Regular["正則言語"]
    Regular -->|isRegular_iff_exists_rightLinearGrammar| Right["右線形文法"]
    Right -->|forget shape| CFG["文脈自由文法"]
    Regular -->|isRegular_isContextFree| CFL["文脈自由言語"]
```

alphabet の `Nonempty` 仮定は、連接・Kleene star の有限オートマトン構成で dummy symbol を
選ぶためにだけ使われる。`Finite` は正則言語から右線形文法へ戻す際、終端記号を有限列挙
する境界で必要になる。

```lean
namespace Language

```

```lean
open Mathling.Automata

/-- A language has a regular-expression presentation when it is the denotation
of some expression. -/


@[expose] public def HasRegularExpression {T : Type} (L : Language T) : Prop :=
  ∃ r : Mathling.Automata.RegularExpression T,
    Mathling.Automata.RegularExpression.language r = L

/-- A regular-expression presentation yields a finite-state presentation. -/
@[important, grind →] public theorem HasRegularExpression.isRegular
    {T : Type} [Nonempty T] {L : Language T}
    (h : L.HasRegularExpression) : L.IsRegular := by
  rcases h with ⟨r, rfl⟩
  exact Mathling.Automata.RegularExpression.language_isRegular r

/-- Over a finite alphabet, state elimination gives every regular language a
regular-expression presentation. -/


@[important, grind →] public theorem IsRegular.hasRegularExpression
    {T : Type} [Finite T] {L : Language T} (h : L.IsRegular) :
    L.HasRegularExpression := by
  letI := Fintype.ofFinite T
  have presentation : ∃ State : Type, ∃ _ : Fintype State,
      ∃ M : Mathling.Automata.NFA T State, M.accepts = L :=
    Mathling.Automata.Language.isRegular_iff_nfa.mp h
  obtain ⟨State, inst, M, hM⟩ := presentation
  exact ⟨@Mathling.Automata.NFA.toRegex T State inferInstance inst M,
    by rw [@Mathling.Automata.NFA.toRegex_language T State inferInstance inst M, hM]⟩

/-- Kleene's theorem: over a finite nonempty alphabet, finite automata and
regular expressions present exactly the same languages. -/


@[important, grind =] public theorem isRegular_iff_hasRegularExpression
    {T : Type} [Finite T] [Nonempty T] {L : Language T} :
    L.IsRegular ↔ L.HasRegularExpression :=
  ⟨IsRegular.hasRegularExpression, HasRegularExpression.isRegular⟩

/-- Over a finite nonempty alphabet, every regex-presented language is
context-free through the regular-language inclusion. -/


@[important, grind →] public theorem HasRegularExpression.isContextFree
    {T : Type} [Finite T] [Nonempty T] {L : Language T}
    (h : L.HasRegularExpression) : L.IsContextFree :=
  Mathling.Grammar.Language.isRegular_isContextFree h.isRegular

/-- A regex presentation can be replaced by a finite-state NFA presentation. -/
@[important, grind →] public theorem HasRegularExpression.exists_nfa
    {T : Type} [Nonempty T] {L : Language T}
    (h : L.HasRegularExpression) :
    ∃ State : Type, ∃ _ : Fintype State,
      ∃ M : Mathling.Automata.NFA T State, M.accepts = L :=
  Mathling.Automata.Language.isRegular_iff_nfa.mp h.isRegular

/-- Over a finite alphabet, a regex presentation can be replaced by a
right-linear grammar presentation. -/


@[important, grind →] public theorem HasRegularExpression.exists_rightLinearGrammar
    {T : Type} [Finite T] [Nonempty T] {L : Language T}
    (h : L.HasRegularExpression) :
    ∃ g : Mathling.Grammar.RightLinearGrammar T,
      Nonempty (Fintype g.cfg.NT) ∧ g.language = L :=
  Mathling.Grammar.Language.isRegular_iff_exists_rightLinearGrammar.mp h.isRegular

/-- A regex presentation also has a finite-local NPDA presentation, obtained
through its context-free grammar presentation. -/


@[important, grind →] public theorem HasRegularExpression.exists_npda
    {T : Type} [Finite T] [Nonempty T] {L : Language T}
    (h : L.HasRegularExpression) :
    ∃ State Stack : Type, ∃ M : Mathling.Automata.NPDA T State Stack,
      M.language = L :=
  Language.isContextFree_iff_exists_npda.mp h.isContextFree

end Language
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
