    module

    public import Mathling.Grammar.NormalForm.Greibach.Conversion

    public import LiterateLean
    open scoped LiterateLean

    @[expose] public section

# Mathling / Grammar / NormalForm / Greibach / Classical モジュール

このモジュールは Mathling のこの領域に属する定義、変換、および証明を提供する。公開される契約と依存関係は import 境界で明示し、実装は以下の Lean ブロックに限定する。

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

@[simp] theorem toGreibachNormalGrammar_language {T : Type}
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
