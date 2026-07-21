    module

    import LiterateLean
    open scoped LiterateLean

    public import Mathling.Meta.Important

    public import Mathling.Lambek.ProductFree.Core
    public import Mathling.Lambek.ProductFree.Decision
    public import Mathling.Lambek.ProductFree.Right.Core
    public import Mathling.Lambek.ProductFree.Right.Decision
    public import Mathling.Lambek.ProductFree.Right.Shallow.Core
    public import Mathling.Lambek.ProductFree.Right.Shallow.Decision
    public import Mathling.Lambek.ProductFree.Left.Core
    public import Mathling.Lambek.ProductFree.Left.Decision
    public import Mathling.Lambek.ProductFree.Left.Shallow.Core
    public import Mathling.Lambek.ProductFree.Left.Shallow.Decision
    public import Mathling.Lambek.ProductFree.Shallow.Core
    public import Mathling.Lambek.ProductFree.Shallow.Decision

    public import Mathling.Automata.Core
    public import Mathling.Automata.Conversion.Pushdown
    public import Mathling.Automata.Conversion.Finite
    public import Mathling.Automata.Conversion.Regex
    public import Mathling.Automata.Theory.Minimization
    public import Mathling.Automata.Theory.Pumping

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


# Mathling ライブラリの公開入口

このモジュールは Lambek 計算、オートマトン、文法理論の公開 API を一つに集約する。
個別の領域だけを利用する場合は、それぞれの `All` モジュールを直接 import する。

依存方向はメタデータ属性から論理・オートマトン・文法の各 façade へ一方向に流れる。
この入口自身は実行時状態も新しい定理も持たず、下位モジュールの名前空間と instance を
そのまま再輸出する。失敗は下位モジュールの型検査時に表面化し、fallback は挟まない。

```lean
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
