    module

    public import Mathling.Grammar.NormalForm.Greibach.Conversion
    public import Mathling.Meta.Important

    public import LiterateLean
    open scoped LiterateLean

    @[expose] public section

# Mathling / Grammar / NormalForm / Greibach / Classical モジュール

計算可能な Greibach 標準形変換が要求する線形順序を古典的に供給するラッパである。変換本体の構成と証明は再実装せず、任意の小さい型上で標準形文法とその言語保存等式だけを公開する。

```lean
@[expose] public section

namespace Mathling.Grammar
namespace ContextFreeGrammar
namespace Classical

/-- Convert a context-free grammar over a small terminal type to Greibach normal
form, choosing classical orders. Use `ContextFreeGrammar.toGreibachNormalGrammar`
when executable code is required. -/
noncomputable def toGreibachNormalGrammar {T : Type}
    (g : ContextFreeGrammar T) : GreibachNormalGrammar T := by
  classical
  letI : LinearOrder T := linearOrderOfSTO WellOrderingRel
  letI : LinearOrder g.NT := linearOrderOfSTO WellOrderingRel
  exact _root_.Mathling.Grammar.ContextFreeGrammar.toGreibachNormalGrammar g

```

## 言語保存契約

古典的に選んだ順序は変換の実行に必要な補助データであり、生成言語には現れない。
したがって公開等式は計算可能な変換本体の保存定理へそのまま簡約される。

```lean
@[important, grind =, simp] theorem toGreibachNormalGrammar_language {T : Type}
    (g : ContextFreeGrammar T) :
    (Classical.toGreibachNormalGrammar g).language = g.language := by
  classical
  simp [Classical.toGreibachNormalGrammar,
    _root_.Mathling.Grammar.ContextFreeGrammar.toGreibachNormalGrammar_language]

end Classical
end ContextFreeGrammar
end Mathling.Grammar

```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
