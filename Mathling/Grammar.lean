    module

    public import Mathling.Grammar.Core
    public import Mathling.Grammar.ContextFree
    public import Mathling.Grammar.Deterministic
    public import Mathling.Grammar.Regular
    public import Mathling.Grammar.NormalForms
    public import Mathling.Grammar.Pushdown
    public import Mathling.Grammar.Theory

    import LiterateLean
    open scoped LiterateLean


# Mathling Grammar

正則・文脈自由文法、正規形、オートマトンとの変換、および主要定理の領域入口である。公開下位モジュールは `Core`、`ContextFree`、`Regular`、`Pushdown`、`NormalForms`、`Theory` であり、個別の構成アルゴリズムではなくこの公開境界を介して文法理論を利用する。

```lean
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
