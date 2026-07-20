    module

    public import LiterateLean
    open scoped LiterateLean

    public import Mathling.Meta.Important

    public import Mathling.Lambek.ProductFree.All

    public import Mathling.Automata.All
    public import Mathling.Grammar.All

    @[expose] public section

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
