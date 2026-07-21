    module

    public import Mathling.Grammar.Core
    public import Mathling.Grammar.ContextFree
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
    import LiterateLean
    open scoped LiterateLean


# Mathling / Grammar / All モジュール

文法の基礎、正則・文脈自由文法、オートマトンとの変換、標準形、および pumping lemma を一括公開する façade である。宣言を再定義せず、利用者に対して文法サブシステム全体の安定した import 境界を与える。

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
