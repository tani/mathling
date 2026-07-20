    module

    public import Mathlib.Data.Bool.Basic
    public import Mathlib.Data.List.Basic
    public import Mathling.Lambek.ProductFree.Decision
    public import Mathling.Lambek.ProductFree.Shallow.Core
    public import Mathling.Meta.Important
    public import LiterateLean
    open scoped LiterateLean

    @[expose] public section

# Decidability for the Shallow Fragment

このファイルでは、shallow 断片の決定可能性を
`Mathling.Lambek.ProductFree.Decision` への翻訳で与える。

```lean
namespace Mathling.Lambek.ProductFree.Shallow
```

この literate ファイルでは、style と heartbeat に関する設定を独立した Lean コードブロックに分けて置く。

```lean
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.maxHeartbeats false
```

`prove1` は right・left 断片側のファイルのように `translatedProve1` ラッパーを経由するのではなく、
`ctxToProductFree Γ` と `A.toProductFree` で shallow 断片を一般断片へ埋め込んだうえで、
base file の `Mathling.Lambek.ProductFree.prove1` を直接呼び出す。
shallow 断片は左除法 `⧹` と右除法 `⧸` の両方を許すが引数を原子式に限定した部分体系であり、
単一の型埋め込み写像 `Tp.toProductFree` を経由すれば、そのまま一般断片の探索アルゴリズムを再利用できる。

```lean
@[grind .]
def prove1 (Γ : List Tp) (A : Tp) : Bool :=
  Mathling.Lambek.ProductFree.prove1 (ctxToProductFree Γ) A.toProductFree
```

`proveAux` も同様に、`ctxToProductFree`／`A.toProductFree` によって一般断片へ変換したシーケントに
対して、base file の `Mathling.Lambek.ProductFree.proveAux` を直接呼び出す。
深さ引数 `n` の意味・停止性は base file 側で既に確立されているため、ここで再証明する必要はない。

```lean
@[grind .]
def proveAux (n : Nat) (Γ : List Tp) (A : Tp) : Bool :=
  Mathling.Lambek.ProductFree.proveAux n (ctxToProductFree Γ) A.toProductFree
```

`prove2` も同様に、base file の `Mathling.Lambek.ProductFree.prove2` を翻訳したシーケントに
対して直接呼び出したものである。次数から計算される十分なステップ数を与える具体的な計算式は
base file 側にすでに定義されているため、ここでは呼び出すだけでよい。

```lean
@[grind .]
def prove2 (Γ : List Tp) (A : Tp) : Bool :=
  Mathling.Lambek.ProductFree.prove2 (ctxToProductFree Γ) A.toProductFree
```

## 単調性と補助補題

以下の一連の補題は、shallow 側で独自に帰納法を回すのではなく、`ctxToProductFree`／`Tp.toProductFree`
による埋め込みを `grind` で展開したうえで、base file 側の対応する補題
（`proveAux_mono`・`proveAux_mono_le`・`proveAux_sound`・`proveAux_complete`・`prove1_iff_prove2`）を
そのまま呼び出すことで得られる。まず、探索深さを 1 ステップ増やしても成功が保たれることを示す。

```lean
@[grind =>]
lemma proveAux_mono {n : Nat} {Γ : List Tp} {A : Tp} (h : proveAux n Γ A) :
  proveAux (n + 1) Γ A := by
  grind only [proveAux, ctxToProductFree, Tp.toProductFree, proveAux_mono]
```

より大きい任意の深さへの単調性も、base file の `proveAux_mono_le` から同様に得られる。

```lean
@[grind =>]
lemma proveAux_mono_le {n m : Nat} {Γ : List Tp} {A : Tp} (h : n ≤ m) (hp : proveAux n Γ A) :
    proveAux m Γ A := by
  grind only [proveAux, ctxToProductFree, Tp.toProductFree, proveAux_mono_le]
```

深さ付き探索 `proveAux` が成功すれば主探索 `prove1` も成功する（健全性）。
これも base file の `proveAux_sound` を、翻訳の定義を展開したうえで呼び出すだけで従う。

```lean
@[grind =>]
lemma proveAux_sound {n : Nat} {Γ : List Tp} {A : Tp} (h : proveAux n Γ A) : prove1 Γ A := by
  grind only [prove1, proveAux, ctxToProductFree, Tp.toProductFree, proveAux_sound]
```

逆向きには、`prove1` の成功から、次数に基づく十分なステップ数を与えた `prove2` の成功が
従う（完全性）。これも base file の `proveAux_complete` を呼び出すだけで得られる。

```lean
@[grind =>]
lemma proveAux_complete {Γ : List Tp} {A : Tp} (h : prove1 Γ A) : prove2 Γ A := by
  grind only [prove1, prove2, ctxToProductFree, Tp.toProductFree, proveAux_complete]
```

したがって、base file の `prove1_iff_prove2` を経由して、shallow 側でも `prove1` と `prove2` は
同値であることが分かる。

```lean
lemma prove1_iff_prove2 {Γ : List Tp} {A : Tp} : prove1 Γ A ↔ prove2 Γ A := by
  grind only [prove1, prove2, ctxToProductFree, Tp.toProductFree, prove1_iff_prove2]
```

## シーケント体系との一致

ここからは、翻訳先（一般断片）での健全性・完全性を shallow 断片の `Sequent` へ移す。
shallow 側の `Sequent` は定義上 `ctxToProductFree`／`Tp.toProductFree` による埋め込みを介して
一般断片の `Sequent` と一致するため、base file 側の `prove1_sound`／`prove1_complete` の結論を
`simpa` でこれらの定義に沿って書き換えるだけで、shallow 側の健全性・完全性が得られる。
まず、探索が成功すれば shallow シーケントが導出可能であることを示す。

```lean
@[grind .]
lemma prove1_sound {Γ : List Tp} {A : Tp} (h : prove1 Γ A) : Γ ⇒ A := by
  simpa [prove1, Sequent, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.prove1_sound
      (Γ := ctxToProductFree Γ)
      (A := A.toProductFree)
      h)
```

逆に、shallow シーケントの導出可能性から探索の成功も従う。

```lean
@[grind .]
lemma prove1_complete {Γ : List Tp} {A : Tp} (h : Γ ⇒ A) : prove1 Γ A := by
  simpa [prove1, Sequent, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.prove1_complete
      (Γ := ctxToProductFree Γ)
      (A := A.toProductFree)
      h)
```

これで探索と導出の同値が得られる。

```lean
@[grind .]
lemma prove1_iff_sequent {Γ : List Tp} {A : Tp} : prove1 Γ A ↔ Γ ⇒ A := by
  grind only [prove1_sound, prove1_complete]
```

`prove2` についても同じ同値が成り立つ。ここでは right・left 側のファイルのように base file の
`translatedProve2_iff_Sequent` を直接呼び出すのではなく、既に示した `prove1_iff_prove2` と
`prove1_iff_sequent` を単純に合成するだけで証明できる（`prove2 ↔ prove1 ↔ Γ ⇒ A`）。

```lean
@[important, grind .]
theorem prove2_iff_sequent {Γ : List Tp} {A : Tp} : prove2 Γ A ↔ Γ ⇒ A := by
  rw [← prove1_iff_prove2, prove1_iff_sequent]
```

したがって shallow シーケントの導出可能性には `Decidable` instance が入る。これにより
具体的なシーケントに対して Lean の `decide` タクティクによる自動的な証明・判定が可能になる。

```lean
instance {Γ : List Tp} {A : Tp} : Decidable (Γ ⇒ A) :=
  decidable_of_iff (prove2 Γ A) prove2_iff_sequent
```

最初の例は、`decide` が実際に走ることを確認するスモークテストであり、
shallow 断片のうち左除法 `⧹`（`Tp.ldiv`）を含む典型的なシーケントの導出可能性を判定する。

```lean
example : [Tp.atom "p", Tp.ldiv "p" "q"] ⇒ Tp.atom "q" := by decide
```

続く例は、右除法 `⧸`（`Tp.rdiv`）を含むシーケントについて同様に `decide` が動くことを確認する。

```lean
example : [Tp.rdiv "q" "p", Tp.atom "p"] ⇒ Tp.atom "q" := by decide
```

最後に名前空間を閉じる。

```lean
end Mathling.Lambek.ProductFree.Shallow
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
