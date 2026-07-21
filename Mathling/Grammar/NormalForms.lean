    module

    public import Mathling.Grammar.NormalForms.Chomsky
    public import Mathling.Grammar.NormalForms.ChomskyClassical
    public import Mathling.Grammar.NormalForms.Greibach
    public import Mathling.Grammar.NormalForms.GreibachClassical
    public import Mathling.Grammar.NormalForms.GreibachPushdown

    import LiterateLean
    open scoped LiterateLean


# Mathling Grammar NormalForms

Chomsky 標準形と Greibach 標準形への変換を集約する公開境界である。変換は元の言語を
保存し、その事実は各変換の主要定理として公開する。有限 support、fresh 記号、作業文法、
導出木などの構成途中の詳細は利用者の契約に含めない。

```lean
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
