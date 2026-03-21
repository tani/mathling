    import Mathlib.Data.Bool.Basic
    import Mathlib.Data.List.Basic
    import Mathling.Lambek.ProductFree.Right.Decidable
    import Mathling.Lambek.ProductFree.Right.Shallow.Basic
    import LiterateLean

# Decidability for the Right-Shallow Fragment

このファイルでは、right-shallow 断片の決定可能性を
`Mathling.Lambek.ProductFree.Right.Decidable` への翻訳で与える。

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

`prove1` は right 断片側の主探索を shallow 側へ持ち上げたものである。

```lean
@[grind .]
def prove1 (Γ : List Tp) (A : Tp) : Bool :=
  Mathling.Lambek.ProductFree.Right.prove1 (ctxToRight Γ) A.toRight
```

`proveAux` は深さ付き探索を表す。

```lean
@[grind .]
def proveAux (n : Nat) (Γ : List Tp) (A : Tp) : Bool :=
  Mathling.Lambek.ProductFree.Right.proveAux n (ctxToRight Γ) A.toRight
```

`prove2` は決定手続きとして使う最終版である。

```lean
@[grind .]
def prove2 (Γ : List Tp) (A : Tp) : Bool :=
  Mathling.Lambek.ProductFree.Right.prove2 (ctxToRight Γ) A.toRight
```

## 単調性と補助補題

1 ステップだけ探索深さを増やしても成功は保たれる。

```lean
@[grind =>]
lemma proveAux_mono {n : Nat} {Γ : List Tp} {A : Tp} (h : proveAux n Γ A) :
  proveAux (n + 1) Γ A := by
  simpa [proveAux, ctxToRight, Tp.toRight] using
    (Mathling.Lambek.ProductFree.Right.proveAux_mono
      (Γ := ctxToRight Γ)
      (A := A.toRight)
      h)
```

より大きい深さへの単調性も同様に従う。

```lean
@[grind =>]
lemma proveAux_mono_le {n m : Nat} {Γ : List Tp} {A : Tp} (h : n ≤ m) (hp : proveAux n Γ A) :
    proveAux m Γ A := by
  simpa [proveAux, ctxToRight, Tp.toRight] using
    (Mathling.Lambek.ProductFree.Right.proveAux_mono_le
      (Γ := ctxToRight Γ)
      (A := A.toRight)
      h hp)
```

深さ付き探索が成功すれば主探索も成功する。

```lean
@[grind =>]
lemma proveAux_sound {n : Nat} {Γ : List Tp} {A : Tp} (h : proveAux n Γ A) : prove1 Γ A := by
  simpa [prove1, proveAux, ctxToRight, Tp.toRight] using
    (Mathling.Lambek.ProductFree.Right.proveAux_sound
      (Γ := ctxToRight Γ)
      (A := A.toRight)
      h)
```

逆に、主探索の成功から十分大きい深さ付き探索が得られる。

```lean
@[grind =>]
lemma proveAux_complete {Γ : List Tp} {A : Tp} (h : prove1 Γ A) : prove2 Γ A := by
  simpa [prove1, prove2, ctxToRight, Tp.toRight] using
    (Mathling.Lambek.ProductFree.Right.proveAux_complete
      (Γ := ctxToRight Γ)
      (A := A.toRight)
      h)
```

したがって `prove1` と `prove2` は同値である。

```lean
lemma prove1_iff_prove2 {Γ : List Tp} {A : Tp} : prove1 Γ A ↔ prove2 Γ A := by
  simpa [prove1, prove2, ctxToRight, Tp.toRight] using
    (Mathling.Lambek.ProductFree.Right.prove1_iff_prove2
      (Γ := ctxToRight Γ)
      (A := A.toRight))
```

## シーケント体系との一致

探索の成功はシーケント導出を与える。

```lean
@[grind .]
lemma prove1_sound {Γ : List Tp} {A : Tp} (h : prove1 Γ A) : Γ ⇒ A := by
  simpa [prove1, Sequent, ctxToRight, Tp.toRight] using
    (Mathling.Lambek.ProductFree.Right.prove1_sound
      (Γ := ctxToRight Γ)
      (A := A.toRight)
      h)
```

シーケント導出から探索の成功も従う。

```lean
@[grind .]
lemma prove1_complete {Γ : List Tp} {A : Tp} (h : Γ ⇒ A) : prove1 Γ A := by
  simpa [prove1, Sequent, ctxToRight, Tp.toRight] using
    (Mathling.Lambek.ProductFree.Right.prove1_complete
      (Γ := ctxToRight Γ)
      (A := A.toRight)
      h)
```

これで探索と導出の同値が得られる。

```lean
@[grind .]
lemma prove1_iff_sequent {Γ : List Tp} {A : Tp} : prove1 Γ A ↔ Γ ⇒ A := by
  constructor <;> [apply prove1_sound; apply prove1_complete]
```

`prove2` についても同じ同値を使える。

```lean
@[grind .]
theorem prove2_iff_sequent {Γ : List Tp} {A : Tp} : prove2 Γ A ↔ Γ ⇒ A := by
  rw [← prove1_iff_prove2, prove1_iff_sequent]
```

したがって shallow シーケントには `Decidable` instance が入る。

```lean
instance {Γ : List Tp} {A : Tp} : Decidable (Γ ⇒ A) :=
  decidable_of_iff (prove2 Γ A) prove2_iff_sequent
```

記法が期待通りに展開される例を置く。

```lean
example : [Tp.rdiv "q" "p", Tp.atom "p"] = [Tp.rdiv "q" "p", Tp.atom "p"] := rfl
```

最後に名前空間を閉じる。

```lean
end Mathling.Lambek.ProductFree.Right.Shallow
```

<!-- vim: set filetype=markdown : -->
