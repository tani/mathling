    module

    public import Mathlib.Data.Bool.Basic
    public import Mathlib.Data.List.Basic
    public import Mathling.Lambek.ProductFree.Right.Core
    public import Mathling.Lambek.ProductFree.Decision
    public import Mathling.Meta.Important
    public import LiterateLean
    open scoped LiterateLean

    public section

# Decidability for the Right Fragment

このファイルでは、right 断片の決定可能性を
`Mathling.Lambek.ProductFree.Decision` への翻訳で与える。

まず right 決定手続きの名前空間を開く。

```lean
namespace Mathling.Lambek.ProductFree.Right
```

この literate ファイルでは、style と heartbeat に関する設定を独立した Lean コードブロックに分けて置く。

```lean
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.maxHeartbeats false
```

翻訳に使う一般断片側の型写像を短い名前に束縛しておく。以下、`prove1`・`proveAux`・`prove2` の
定義や単調性・健全性・完全性の証明のたびに `Tp.toProductFree` と書く代わりにこの `toProductFree`
という略称を用いることで、right 断片専用のコードとして読みやすくする。

```lean
private abbrev toProductFree : Tp → Mathling.Lambek.ProductFree.Tp := Tp.toProductFree
```

`prove1` は健全性・完全性を re-prove するのではなく、base file の `translatedProve1` を
`toProductFree`（right 断片の型を一般断片へ埋め込む写像）で特殊化するだけで得られる。
right 断片は右除法 `⧸` のみを持つ部分体系であり、埋め込み先の一般断片における
証明探索ロジックをそのまま再利用できる。

```lean
@[grind .]
def prove1 (Γ : List Tp) (A : Tp) : Bool :=
  Mathling.Lambek.ProductFree.translatedProve1 toProductFree Γ A
```

`proveAux` も同様に `translatedProveAux` を `toProductFree` で特殊化したものであり、
探索の深さを明示的な引数として持つことで自明に停止する。停止性の根拠自体は
base file 側で証明済みであるため、ここで再証明する必要はない。

```lean
@[grind .]
def proveAux (n : Nat) (Γ : List Tp) (A : Tp) : Bool :=
  Mathling.Lambek.ProductFree.translatedProveAux toProductFree n Γ A
```

`prove2` は `translatedProve2` の特殊化であり、シーケントの次数に基づく十分なステップ数を
`proveAux` に与えることで `prove1` と同値になる版である。以降の `Decidable` instance は
この `prove2` を用いて構成する。

```lean
@[grind .]
def prove2 (Γ : List Tp) (A : Tp) : Bool :=
  Mathling.Lambek.ProductFree.translatedProve2 toProductFree Γ A
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
  simpa [prove1, Sequent, ctxToProductFree, toProductFree] using
    (Mathling.Lambek.ProductFree.translatedProve1_sound toProductFree h)
```

シーケント導出から探索の成功も従う。

```lean
@[grind .]
lemma prove1_complete {Γ : List Tp} {A : Tp} (h : Γ ⇒ A) : prove1 Γ A := by
  simpa [prove1, Sequent, ctxToProductFree, toProductFree] using
    (Mathling.Lambek.ProductFree.translatedProve1_complete toProductFree h)
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
theorem prove2_iff_sequent {Γ : List Tp} {A : Tp} : prove2 Γ A ↔ Γ ⇒ A := by
  simpa [prove2, Sequent, ctxToProductFree, toProductFree] using
    (Mathling.Lambek.ProductFree.translatedProve2_iff_Sequent toProductFree
      (Γ := Γ) (A := A))
```

したがって right シーケントには `Decidable` instance が入る。

```lean
instance {Γ : List Tp} {A : Tp} : Decidable (Γ ⇒ A) :=
  decidable_of_iff (prove2 Γ A) prove2_iff_sequent
```

最後に `decide` が動く具体例を置く。

```lean
example : [Tp.rdiv (Tp.atom "q") (Tp.atom "p"), Tp.atom "p"] ⇒ Tp.atom "q" := by decide
```

最後に名前空間を閉じる。

```lean
end Mathling.Lambek.ProductFree.Right
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
