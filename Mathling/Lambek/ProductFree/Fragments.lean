    module

    public import Mathling.Lambek.ProductFree.Fragments.Right.Core
    public import Mathling.Lambek.ProductFree.Fragments.Right.Decision
    public import Mathling.Lambek.ProductFree.Fragments.Right.Shallow.Core
    public import Mathling.Lambek.ProductFree.Fragments.Right.Shallow.Decision
    public import Mathling.Lambek.ProductFree.Fragments.Left.Core
    public import Mathling.Lambek.ProductFree.Fragments.Left.Decision
    public import Mathling.Lambek.ProductFree.Fragments.Left.Shallow.Core
    public import Mathling.Lambek.ProductFree.Fragments.Left.Shallow.Decision
    public import Mathling.Lambek.ProductFree.Fragments.Shallow.Core
    public import Mathling.Lambek.ProductFree.Fragments.Shallow.Decision

    import LiterateLean
    open scoped LiterateLean


# Product-free Lambek calculus fragments

片側除法と shallow 制限を持つ product-free Lambek calculus の公開境界である。各断片は
一般系への翻訳と共通の決定手続きを利用するが、利用者にはそれぞれの `Tp`、`Sequent`、
cut admissibility、および `prove2` の完全性だけを契約として提供する。

```lean
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
