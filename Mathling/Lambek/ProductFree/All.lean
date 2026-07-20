    module

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

    public import LiterateLean
    open scoped LiterateLean

    @[expose] public section

# Mathling / Lambek / ProductFree / All モジュール

一般の product-free 系、左右片側断片、および shallow 断片の core と決定手続きを
一つの import に集約する。各断片は一般系への翻訳で意味論を共有するため、この façade は
翻訳元と翻訳先を同時に利用できる依存順序を保証するが、新しい探索器は定義しない。

```lean
/-!
# Product-free Lambek calculus

The public entry point for the product-free Lambek developments.
-/

```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
