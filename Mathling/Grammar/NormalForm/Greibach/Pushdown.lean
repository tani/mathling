    module

    public import Mathling.Grammar.NormalForm.Greibach.Classical
    public import Mathling.Grammar.Conversion.Pushdown
    public import Mathling.Meta.Important

    import LiterateLean
    open scoped LiterateLean


# Mathling / Grammar / NormalForm / Greibach / Pushdown モジュール

このモジュールは Greibach 標準形文法と有限局所 NPDA の等価性を、既存の二つの結果を
合成するだけで導く。一つは任意の文脈自由文法が言語を保ったまま Greibach 標準形へ
変換できるという事実、もう一つは文脈自由文法と有限局所 NPDA が言語として一致すると
いう一般の等価性である。新しい機械や文法の構成は不要で、既存の変換を橋渡しする。

```lean

namespace Language

open Mathling.Automata Mathling.Grammar

/-- A language is context-free exactly when some grammar in Greibach normal form
generates it. Forward: every context-free grammar has a language-preserving
Greibach-normal presentation (`ContextFreeGrammar.Classical.toGreibachNormalGrammar`).
Backward: forgetting Greibach-normality evidence returns a plain context-free
grammar for the same language. -/
@[important, grind =] public theorem isContextFree_iff_exists_greibachNormalGrammar
    {T : Type} {L : Language T} :
    L.IsContextFree ↔ ∃ g : GreibachNormalGrammar T, g.language = L := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨ContextFreeGrammar.Classical.toGreibachNormalGrammar g,
      ContextFreeGrammar.Classical.toGreibachNormalGrammar_language g⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g.toContextFreeGrammar, g.toContextFreeGrammar_language⟩

```

## Greibach 文法と NPDA の存在同値

前節の特徴付けを中間命題として消去し、一般の CFG–NPDA 等価性へ接続する。
状態型とスタック型は機械 witness とともに存在量化されるため、この層は具体的な符号化を
公開 API に漏らさない。

```lean
/-- Greibach-normal grammars generate exactly the languages accepted by some
finite local NPDA, both state and stack alphabets being existential witnesses.
This composes `isContextFree_iff_exists_greibachNormalGrammar` with the general
context-free/pushdown equivalence `isContextFree_iff_exists_npda`. -/
@[important] public theorem exists_greibachNormalGrammar_iff_exists_npda
    {T : Type} {L : Language T} :
    (∃ g : GreibachNormalGrammar T, g.language = L) ↔
      ∃ State Stack : Type, ∃ M : NPDA T State Stack, M.language = L := by
  rw [← isContextFree_iff_exists_greibachNormalGrammar]
  exact isContextFree_iff_exists_npda

grind_pattern exists_greibachNormalGrammar_iff_exists_npda =>
  Language.IsContextFree L

end Language

```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
