    module

    public import Mathlib.Data.Bool.Basic
    public import Mathlib.Data.List.Basic
    public import Mathling.Lambek.ProductFree.Left.Shallow.Core
    public import Mathling.Lambek.ProductFree.Decision
    public import Mathling.Meta.Important
    public import LiterateLean
    open scoped LiterateLean

    @[expose] public section

# Decidability for the Left-Shallow Fragment

このファイルでは、left-shallow 断片の決定可能性を
`Mathling.Lambek.ProductFree.Decision` への翻訳で与える。

```lean
namespace Mathling.Lambek.ProductFree.Left.Shallow
```

この literate ファイルでは、style と heartbeat に関する設定を独立した Lean コードブロックに分けて置く。

```lean
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.maxHeartbeats false
```

`prove2` は決定手続きとして使う最終版である。

```lean
@[grind .]
def prove2 (Γ : List Tp) (A : Tp) : Bool :=
  Mathling.Lambek.ProductFree.translatedProve2 Tp.toProductFree Γ A
```

```lean
@[important, grind .]
theorem prove2_iff_sequent {Γ : List Tp} {A : Tp} : prove2 Γ A ↔ Γ ⇒ A := by
  simpa [prove2, Sequent, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.translatedProve2_iff_Sequent
      Tp.toProductFree (Γ := Γ) (A := A))
```

したがって shallow シーケントには `Decidable` instance が入る。

```lean
instance {Γ : List Tp} {A : Tp} : Decidable (Γ ⇒ A) :=
  decidable_of_iff (prove2 Γ A) prove2_iff_sequent
```

記法が期待通りに展開される例を置く。

```lean
example : [Tp.atom "p", Tp.ldiv "p" "q"] = [Tp.atom "p", Tp.ldiv "p" "q"] := rfl
```

最後に名前空間を閉じる。

```lean
end Mathling.Lambek.ProductFree.Left.Shallow
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
