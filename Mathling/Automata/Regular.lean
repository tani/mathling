    module

    public import Mathling.Automata.Regular.Finite
    public import Mathling.Automata.Regular.Minimization
    public import Mathling.Automata.Regular.Pumping

    import LiterateLean
    open scoped LiterateLean


# Mathling Automata Regular

正規言語の構成的な API を集約する。有限オートマトンの PDA への埋め込み、最小 DFA、
および pumping lemma を提供する。各構成の補助計算は下位モジュールに閉じ、ここでは
正規言語を扱う利用者向けの安定した import 境界だけを定める。

```lean
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
