    module

    public import Mathling.Grammar.Regular.RightLinear
    public import Mathling.Grammar.Regular.LeftLinear
    public import Mathling.Grammar.Regular.Linear
    public import Mathling.Grammar.NormalForm.Chomsky.Conversion
    public import Mathling.Grammar.NormalForm.Chomsky.Classical
    public import Mathling.Grammar.NormalForm.Greibach.Conversion
    public import Mathling.Grammar.NormalForm.Greibach.Classical
    public import Mathling.Grammar.NormalForm.Greibach.Pushdown
    public import Mathling.Grammar.Conversion.Pushdown

    public import Mathling.Grammar.Theory.Pumping
    public import LiterateLean
    open scoped LiterateLean

    @[expose] public section

# Mathling / Grammar / All モジュール

このモジュールは Mathling のこの領域に属する定義、変換、および証明を提供する。公開される契約と依存関係は import 境界で明示し、実装は以下の Lean ブロックに限定する。

```lean
/-!
# Grammar

The public entry point for Mathling's grammar library.
-/

```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
