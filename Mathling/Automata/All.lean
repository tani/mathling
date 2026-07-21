    module

    public import Mathling.Automata.Core
    public import Mathling.Automata.Conversion.Pushdown
    public import Mathling.Automata.Conversion.Finite
    public import Mathling.Automata.Conversion.Regex
    public import Mathling.Automata.Theory.Minimization
    public import Mathling.Automata.Theory.Pumping

    import LiterateLean
    open scoped LiterateLean


# Mathling / Automata / All モジュール

有限オートマトン、正規表現、プッシュダウン・オートマトン、およびそれらの変換・理論を一括して公開する façade である。実装は各下位モジュールに属し、このファイルは利用者が安定した一つの import 境界を選べるよう依存関係だけを集約する。

```lean
/-!
# Automata

The public entry point for finite automata, conversions, and related theory.
-/

```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
