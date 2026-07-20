    module

    public import Mathlib.Data.Bool.Basic
    public import Mathlib.Data.List.Basic
    public import Mathling.Lambek.ProductFree.Right.Shallow.Core
    public import Mathling.Lambek.ProductFree.Decision
    public import Mathling.Meta.Important
    public import LiterateLean
    open scoped LiterateLean

    @[expose] public section

# Decidability for the Right-Shallow Fragment

このファイルでは、right-shallow 断片の決定可能性を
`Mathling.Lambek.ProductFree.Decision` への翻訳で与える。

実行時のデータフローは構文翻訳、共通 Boolean 探索、結果の解釈の三段階である。
`false` は探索資源切れではなく非導出可能性を表し、`prove2_iff_sequent` の完全性が
その読み方を保証する。

```lean
namespace Mathling.Lambek.ProductFree.Right.Shallow
```

この literate ファイルでは、style と heartbeat に関する設定を独立した Lean コードブロックに分けて置く。

```lean
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.maxHeartbeats false
```

`prove1` は健全性・完全性を独自に証明し直すのではなく、`Mathling.Lambek.ProductFree.translatedProve1` を
`Tp.toProductFree`（right-shallow の型を一般断片の型へ埋め込む写像）で特殊化するだけで得られる。
right-shallow は right 断片よりもさらに引数の形を原子式に制限した部分体系だが、
`toProductFree` による埋め込み先は同じ一般断片であるため、証明探索の核となるロジックはすべて
base file 側の `prove1`／`prove2` に委ねられる。

```lean
@[grind .]
def prove1 (Γ : List Tp) (A : Tp) : Bool :=
  Mathling.Lambek.ProductFree.translatedProve1 Tp.toProductFree Γ A
```

`proveAux` も同様に、`translatedProveAux` を `Tp.toProductFree` で特殊化したものであり、
探索の深さ（ステップ数）を明示的な引数として持つことで、Lean の関数として自明に停止する。
この深さ引数の意味や停止性の根拠は base file 側で既に証明済みであるため、ここでは再証明しない。

```lean
@[grind .]
def proveAux (n : Nat) (Γ : List Tp) (A : Tp) : Bool :=
  Mathling.Lambek.ProductFree.translatedProveAux
    Tp.toProductFree n Γ A
```

`prove2` は `translatedProve2` の特殊化であり、シーケントの次数から計算される
十分なステップ数を `proveAux` に与えることで、`prove1` と同値になる（停止性が保証された）版である。
以降の決定可能性インスタンスは、この `prove2` を用いて構成される。

```lean
@[grind .]
def prove2 (Γ : List Tp) (A : Tp) : Bool :=
  Mathling.Lambek.ProductFree.translatedProve2 Tp.toProductFree Γ A
```

## 単調性と補助補題

1 ステップだけ探索深さを増やしても成功は保たれる。この性質も base file の
`translatedProveAux_mono` をそのまま呼び出すだけで得られ、shallow 側で個別に帰納法を回す必要はない。

```lean
@[grind =>]
lemma proveAux_mono {n : Nat} {Γ : List Tp} {A : Tp} (h : proveAux n Γ A) :
  proveAux (n + 1) Γ A := by
  grind only [proveAux, translatedProveAux_mono]
```

より大きい任意の深さへの単調性も、base file の `translatedProveAux_mono_le` をそのまま利用して得られる。

```lean
@[grind =>]
lemma proveAux_mono_le {n m : Nat} {Γ : List Tp} {A : Tp} (h : n ≤ m) (hp : proveAux n Γ A) :
    proveAux m Γ A := by
  grind only [proveAux, translatedProveAux_mono_le]
```

深さ付き探索 `proveAux` が成功すれば、深さ引数を持たない主探索 `prove1` も成功する
（健全性）。この事実も base file の `translatedProveAux_sound` を呼び出すだけで従う。

```lean
@[grind =>]
lemma proveAux_sound {n : Nat} {Γ : List Tp} {A : Tp} (h : proveAux n Γ A) : prove1 Γ A := by
  grind only [prove1, proveAux, translatedProveAux_sound]
```

逆に、`prove1` が成功するならば、シーケントの次数から計算される十分なステップ数を
与えた `prove2` でも成功する（完全性）。これも base file の `translatedProveAux_complete` を
呼び出すだけで得られる。

```lean
@[grind =>]
lemma proveAux_complete {Γ : List Tp} {A : Tp} (h : prove1 Γ A) : prove2 Γ A := by
  grind only [prove1, prove2, translatedProveAux_complete]
```

したがって `prove1` と `prove2` は同値である。この同値も base file の
`translatedProve1_iff_Prove2` から従う、shallow 側固有の議論を要しない事実である。

```lean
lemma prove1_iff_prove2 {Γ : List Tp} {A : Tp} : prove1 Γ A ↔ prove2 Γ A := by
  grind only [prove1, prove2, translatedProve1_iff_Prove2]
```

## シーケント体系との一致

探索の成功 `prove1 Γ A` からシーケント導出 `Γ ⇒ A` を導く。right-shallow の `Sequent` は
定義上 `ctxToProductFree`／`Tp.toProductFree` による埋め込みを介して一般断片の `Sequent` に
一致するため、base file の `translatedProve1_sound` の結論をこれらの定義に沿って
`simpa` で書き換えるだけで証明が完了する。

```lean
@[grind .]
lemma prove1_sound {Γ : List Tp} {A : Tp} (h : prove1 Γ A) : Γ ⇒ A := by
  simpa [prove1, Sequent, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.translatedProve1_sound
      Tp.toProductFree h)
```

逆にシーケント導出 `Γ ⇒ A` から探索の成功 `prove1 Γ A` も従う。同様に `Sequent` の定義を
展開したうえで、base file の `translatedProve1_complete` を適用すればよい。

```lean
@[grind .]
lemma prove1_complete {Γ : List Tp} {A : Tp} (h : Γ ⇒ A) : prove1 Γ A := by
  have h_pf :
      Mathling.Lambek.ProductFree.Sequent
        (List.map Tp.toProductFree Γ) A.toProductFree := by
    simpa [Sequent, ctxToProductFree, Tp.toProductFree] using h
  simpa [prove1] using
    (Mathling.Lambek.ProductFree.translatedProve1_complete
      Tp.toProductFree h_pf)
```

これで探索と導出の同値が得られる。

```lean
@[grind .]
lemma prove1_iff_sequent {Γ : List Tp} {A : Tp} : prove1 Γ A ↔ Γ ⇒ A := by
  grind only [prove1_sound, prove1_complete]
```

`prove2` についても同じ同値を使える。ここでは `prove1_iff_prove2` と `prove1_iff_sequent` を
経由する代わりに、base file の中心定理 `translatedProve2_iff_Sequent` を直接呼び出し、
`simpa` で `Sequent`／`ctxToProductFree`／`Tp.toProductFree` を展開して right-shallow 側の
言明に書き換えている。この定理には `@[important]` 属性が付き、この決定手続きファイル全体の
結論として扱われる。

```lean
@[important, grind .]
theorem prove2_iff_sequent {Γ : List Tp} {A : Tp} : prove2 Γ A ↔ Γ ⇒ A := by
  simpa [prove2, Sequent, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.translatedProve2_iff_Sequent
      Tp.toProductFree (Γ := Γ) (A := A))
```

したがって shallow シーケントの導出可能性には `Decidable` instance が入る。これにより
`Γ ⇒ A` という命題に対して、Lean の `decide` タクティクを用いた自動的な証明・判定が可能になる。

```lean
instance {Γ : List Tp} {A : Tp} : Decidable (Γ ⇒ A) :=
  decidable_of_iff (prove2 Γ A) prove2_iff_sequent
```

最後に、記法が期待通りに展開されることを確認する例を置く。この例は決定手続きが実際に走ることを
確かめる `decide` のスモークテストではなく、文字列リテラル `"p"`／`"q"` から `Tp.atom` への
coercion や `⧸` などの記法が構文的に期待通りの項へ展開されることを `rfl` で確認するものである。

```lean
example : [Tp.rdiv "q" "p", Tp.atom "p"] = [Tp.rdiv "q" "p", Tp.atom "p"] := rfl
```

最後に名前空間を閉じる。

```lean
end Mathling.Lambek.ProductFree.Right.Shallow
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
