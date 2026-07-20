    module

    public import Mathling.Grammar.NormalForm.Chomsky.Conversion

    public import LiterateLean
    open scoped LiterateLean

    @[expose] public section

# Mathling / Grammar / NormalForm / Chomsky / Classical モジュール

このモジュールは Mathling のこの領域に属する定義、変換、および証明を提供する。公開される契約と依存関係は import 境界で明示し、実装は以下の Lean ブロックに限定する。

```lean
@[expose] public section

namespace Mathling.Grammar
namespace ContextFreeGrammar
namespace Classical

/-- Convert a context-free grammar over a small terminal type to Chomsky normal
form, choosing classical orders. Use `ContextFreeGrammar.toChomskyNormalGrammar`
when executable code is required. -/
noncomputable def toChomskyNormalGrammar {T : Type}
    (g : ContextFreeGrammar T) : ChomskyNormalGrammar T := by
  classical
  letI : LinearOrder T := linearOrderOfSTO WellOrderingRel
  letI : LinearOrder g.NT := linearOrderOfSTO WellOrderingRel
  exact _root_.Mathling.Grammar.ContextFreeGrammar.toChomskyNormalGrammar g

@[simp] theorem toChomskyNormalGrammar_language {T : Type}
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
