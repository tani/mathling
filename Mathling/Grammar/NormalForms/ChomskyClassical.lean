    module

    public import Mathling.Grammar.NormalForms.Chomsky
    public import Mathling.Meta.Important

    import LiterateLean
    open scoped LiterateLean


# Mathling / Grammar / NormalForms / ChomskyClassical モジュール

計算可能な Chomsky 標準形変換に必要な終端記号・非終端記号の順序を古典論理で選ぶ薄いラッパである。実行可能性を要求しない利用者向けに型クラス引数を隠しつつ、基礎変換の言語保存定理をそのまま公開する。

```lean

namespace Mathling.Grammar
namespace ContextFreeGrammar
namespace Classical

/-- Convert a context-free grammar over a small terminal type to Chomsky normal
form, choosing classical orders. Use `ContextFreeGrammar.toChomskyNormalGrammar`
when executable code is required. -/
public noncomputable def toChomskyNormalGrammar {T : Type}
    (g : ContextFreeGrammar T) : ChomskyNormalGrammar T := by
  classical
  letI : LinearOrder T := linearOrderOfSTO WellOrderingRel
  letI : LinearOrder g.NT := linearOrderOfSTO WellOrderingRel
  exact _root_.Mathling.Grammar.ContextFreeGrammar.toChomskyNormalGrammar g

```

## 言語保存契約

古典ラッパは順序 instance の選択だけを隠すため、生成言語の証明は計算可能な変換の
言語保存定理へ簡約できる。選ばれた順序の具体的な値は等式の両辺に観測されない。

```lean
@[important, grind =, simp] public theorem toChomskyNormalGrammar_language {T : Type}
    (g : ContextFreeGrammar T) :
    (Classical.toChomskyNormalGrammar g).language = g.language := by
  classical
  simp [Classical.toChomskyNormalGrammar,
    _root_.Mathling.Grammar.ContextFreeGrammar.toChomskyNormalGrammar_language]

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
