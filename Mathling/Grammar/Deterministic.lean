    module

    public import Mathling.Automata.Regular.Finite
    public import Mathling.Grammar.Pushdown

    import LiterateLean
    open scoped LiterateLean


# 決定性文脈自由言語

有限 DFA を、スタック上の唯一の印を保存する DPDA として実行することで、正則言語から
決定性文脈自由言語への包含を与える。変換は入力を一文字ずつ決定的に読み、スタック高を
変えないため、PDA 側に追加の失敗経路は生じない。

```lean
namespace Language

open Mathling.Automata

/-- Every regular language is deterministic context-free. -/
@[important, grind .] public theorem IsRegular.isDeterministicContextFree
    {T : Type} [Finite T] {L : Language T} (h : L.IsRegular) :
    L.IsDeterministicContextFree := by
  letI := Fintype.ofFinite T
  obtain ⟨State, inst, M, hM⟩ := Language.isRegular_iff.mp h
  exact ⟨State, PUnit, M.toDPDA, M.toDPDA_language.trans hM⟩

end Language
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
