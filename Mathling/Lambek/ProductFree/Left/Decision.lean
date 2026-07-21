    module

    public import Mathlib.Data.Bool.Basic
    public import Mathlib.Data.List.Basic
    public import Mathling.Lambek.ProductFree.Left.Core
    public import Mathling.Lambek.ProductFree.Decision
    public import Mathling.Meta.Important
    import LiterateLean
    open scoped LiterateLean


# Decidability for the Left Fragment

このファイルでは、left 断片の決定可能性を
`Mathling.Lambek.ProductFree.Decision` への翻訳で与える。

探索関数は left 構文を一般構文へ写してから共通探索器を呼ぶ。主要契約は
`prove2 Γ A = true` と $`\Gamma \Rightarrow A`$ の同値であり、ここから `Decidable`
public instance を構成する。探索失敗は例外ではなく Boolean の `false` として返る。

まず left 決定手続きの名前空間を開く。

```lean
namespace Mathling.Lambek.ProductFree.Left
```

この literate ファイルでは、style と heartbeat に関する設定を独立した Lean コードブロックに分けて置く。

```lean
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.maxHeartbeats false
```

`prove1` は一般断片側の主探索を left 側へ持ち上げたものである。

```lean
@[grind .]
public def prove1 (Γ : List Tp) (A : Tp) : Bool :=
  Mathling.Lambek.ProductFree.translatedProve1 Tp.toProductFree Γ A
```

`proveAux` は深さ付き探索を表す。

```lean
@[grind .]
public def proveAux (n : Nat) (Γ : List Tp) (A : Tp) : Bool :=
  Mathling.Lambek.ProductFree.translatedProveAux Tp.toProductFree n Γ A
```

`prove2` は決定手続きとして使う最終版である。

```lean
@[grind .]
public def prove2 (Γ : List Tp) (A : Tp) : Bool :=
  Mathling.Lambek.ProductFree.translatedProve2 Tp.toProductFree Γ A
```

1 ステップだけ探索深さを増やしても成功は保たれる。

```lean
@[grind =>]
lemma proveAux_mono {n : Nat} {Γ : List Tp} {A : Tp} (h : proveAux n Γ A) :
  proveAux (n + 1) Γ A := by
  grind only [proveAux, translatedProveAux_mono]
```

より大きい深さへの単調性も同様に従う。

```lean
@[grind =>]
lemma proveAux_mono_le {n m : Nat} {Γ : List Tp} {A : Tp} (h : n ≤ m) (hp : proveAux n Γ A) :
    proveAux m Γ A := by
  grind only [proveAux, translatedProveAux_mono_le]
```

深さ付き探索が成功すれば主探索も成功する。

```lean
@[grind =>]
lemma proveAux_sound {n : Nat} {Γ : List Tp} {A : Tp} (h : proveAux n Γ A) : prove1 Γ A := by
  grind only [prove1, proveAux, translatedProveAux_sound]
```

逆に、主探索の成功から十分大きい深さ付き探索が得られる。

```lean
@[grind =>]
lemma proveAux_complete {Γ : List Tp} {A : Tp} (h : prove1 Γ A) : prove2 Γ A := by
  grind only [prove1, prove2, translatedProveAux_complete]
```

したがって `prove1` と `prove2` は同値である。

```lean
@[grind .] lemma prove1_iff_prove2 {Γ : List Tp} {A : Tp} : prove1 Γ A ↔ prove2 Γ A := by
  grind only [prove1, prove2, translatedProve1_iff_Prove2]
```

探索の成功はシーケント導出を与える。

```lean
@[grind .]
lemma prove1_sound {Γ : List Tp} {A : Tp} (h : prove1 Γ A) : Γ ⇒ A := by
  simpa [prove1, Sequent, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.translatedProve1_sound Tp.toProductFree h)
```

シーケント導出から探索の成功も従う。

```lean
@[grind .]
lemma prove1_complete {Γ : List Tp} {A : Tp} (h : Γ ⇒ A) : prove1 Γ A := by
  simpa [prove1, Sequent, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.translatedProve1_complete Tp.toProductFree h)
```

これで探索と導出の同値が得られる。

```lean
@[grind .]
lemma prove1_iff_sequent {Γ : List Tp} {A : Tp} : prove1 Γ A ↔ Γ ⇒ A := by
  grind only [prove1_sound, prove1_complete]
```

`prove2` についても同じ同値を使える。

```lean
@[important, grind .]
public theorem prove2_iff_sequent {Γ : List Tp} {A : Tp} : prove2 Γ A ↔ Γ ⇒ A := by
  simpa [prove2, Sequent, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.translatedProve2_iff_Sequent Tp.toProductFree
      (Γ := Γ) (A := A))
```

したがって left シーケントには `Decidable` instance が入る。

```lean
public instance {Γ : List Tp} {A : Tp} : Decidable (Γ ⇒ A) :=
  decidable_of_iff (prove2 Γ A) prove2_iff_sequent
```

最後に `decide` が動く具体例を置く。

```lean
example : [Tp.atom "p", Tp.ldiv (Tp.atom "p") (Tp.atom "q")] ⇒ Tp.atom "q" := by decide
```

最後に名前空間を閉じる。

```lean
end Mathling.Lambek.ProductFree.Left
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
