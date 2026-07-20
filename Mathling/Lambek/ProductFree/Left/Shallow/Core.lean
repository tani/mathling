    module

    public import Mathlib.Data.List.Basic
    public import Mathlib.Data.Nat.Basic
    public import Mathling.Lambek.ProductFree.Core
    public import LiterateLean
    open scoped LiterateLean

    @[expose] public section

# Left-Shallow Fragment of Product-Free Lambek Calculus

このファイルでは、積を持たない Lambek 計算の left-shallow 断片を定義する。
left-shallow 断片では、左除法の分母は原子式に限定される。

基本的なメタ理論は `Mathling.Lambek.ProductFree.Core` に翻訳して再利用する。

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

まず、left-shallow 断片の論理式を定義する。

```lean
@[grind cases]
inductive Tp where
  | atom (name : String) : Tp
  | ldiv (A : String) (B : String) : Tp
  deriving Repr, DecidableEq
```

原子式の記法を導入する。

```lean
prefix:65 "#" => Tp.atom
```

左除法の記法を導入する。

```lean
infixr:60 " ⧹ " => Tp.ldiv
```

各 shallow 論理式を一般の product-free 論理式へ直接写す。

```lean
def Tp.toProductFree : Tp → Mathling.Lambek.ProductFree.Tp
  | .atom name => Mathling.Lambek.ProductFree.Tp.atom name
  | .ldiv A B =>
      Mathling.Lambek.ProductFree.Tp.ldiv
        (Mathling.Lambek.ProductFree.Tp.atom A)
        (Mathling.Lambek.ProductFree.Tp.atom B)
```

## 一般断片への翻訳

left-shallow の定理は一般の product-free 断片への翻訳から得る。

文脈も同じ写像で翻訳する。

```lean
def ctxToProductFree : List Tp → List Mathling.Lambek.ProductFree.Tp :=
  List.map Tp.toProductFree
```

空文脈の翻訳は自明である。

```lean
@[simp] lemma ctxToProductFree_nil : ctxToProductFree [] = [] := rfl
```

先頭要素を付けた文脈の翻訳も簡約できる。

```lean
@[simp] lemma ctxToProductFree_cons :
    ctxToProductFree (A :: Γ) = A.toProductFree :: ctxToProductFree Γ := rfl
```

連結についても翻訳が分配される。

```lean
@[simp] lemma ctxToProductFree_append :
    ctxToProductFree (Γ ++ Δ) = ctxToProductFree Γ ++ ctxToProductFree Δ := by
  simp [ctxToProductFree]
```

shallow シーケントは一般断片のシーケントとして実装する。

```lean
def Sequent (Γ : List Tp) (A : Tp) : Prop :=
  Mathling.Lambek.ProductFree.Sequent (ctxToProductFree Γ) A.toProductFree
```

## shallow 規則

以下では shallow 規則をまとめる名前空間を開く。

```lean
namespace Sequent
```

公理規則は翻訳先の公理そのものである。

```lean
theorem ax : Sequent [A] A := by
  simpa [Sequent, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.Sequent.ax :
      Mathling.Lambek.ProductFree.Sequent [A.toProductFree] A.toProductFree)
```

右導入規則は left 断片側の定理を持ち上げる。

```lean
theorem ldiv_r
  (h_ne : Γ ≠ [])
  (h : Sequent ([Tp.atom A] ++ Γ) (Tp.atom B)) :
  Sequent Γ (Tp.ldiv A B) := by
  simpa [Sequent, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.Sequent.ldiv_r
      (by simpa using h_ne) h)
```

左導入規則も翻訳先からそのまま再利用する。

```lean
theorem ldiv_l
  (h_arg : Sequent Δ (Tp.atom A))
  (h_main : Sequent (Γ ++ [Tp.atom B] ++ Λ) C) :
  Sequent (Γ ++ Δ ++ [Tp.ldiv A B] ++ Λ) C := by
  have h_main_pf :
      Mathling.Lambek.ProductFree.Sequent
        (ctxToProductFree Γ ++ [Mathling.Lambek.ProductFree.Tp.atom B] ++ ctxToProductFree Λ)
        C.toProductFree := by
    simpa [Sequent, ctxToProductFree, Tp.toProductFree, List.append_assoc] using h_main
  simpa [Sequent, ctxToProductFree, Tp.toProductFree, List.append_assoc] using
    (Mathling.Lambek.ProductFree.Sequent.ldiv_l
      (Δ := ctxToProductFree Δ)
      (A := Mathling.Lambek.ProductFree.Tp.atom A)
      (Γ := ctxToProductFree Γ)
      (B := Mathling.Lambek.ProductFree.Tp.atom B)
      (Λ := ctxToProductFree Λ)
      (C := C.toProductFree)
      h_arg h_main_pf)
```

規則定義の名前空間をここで閉じる。

```lean
end Sequent
```

読みやすさのため shallow 断片側の記法を与える。

```lean
infixl:50 " ⇒ " => Sequent
```

## 基本補題と主要定理

カット許容性は left 断片での結果を翻訳して得る。

```lean
theorem cut_admissible
  {Γ Δ Λ : List Tp} {A B : Tp}
  (d_left : Sequent Γ A)
  (d_right : Sequent (Δ ++ [A] ++ Λ) B) :
  Sequent (Δ ++ Γ ++ Λ) B := by
  have d_left_pf :
      Mathling.Lambek.ProductFree.Sequent (ctxToProductFree Γ) A.toProductFree := by
    simpa [Sequent, ctxToProductFree, Tp.toProductFree] using d_left
  have d_right_pf :
      Mathling.Lambek.ProductFree.Sequent
        (ctxToProductFree Δ ++ [A.toProductFree] ++ ctxToProductFree Λ) B.toProductFree := by
    simpa [Sequent, ctxToProductFree, Tp.toProductFree, List.append_assoc] using d_right
  simpa [Sequent, ctxToProductFree, Tp.toProductFree, List.append_assoc] using
    (Mathling.Lambek.ProductFree.cut_admissible d_left_pf d_right_pf)
```

左除法の右規則の逆転可能性も再輸出する。

```lean
theorem ldiv_invertible {Γ : List Tp} {A B : String}
  (h : Sequent Γ (Tp.ldiv A B)) :
  Sequent ([Tp.atom A] ++ Γ) (Tp.atom B) := by
  simpa [Sequent, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.ldiv_invertible
      (Γ := ctxToProductFree Γ)
      (A := Mathling.Lambek.ProductFree.Tp.atom A)
      (B := Mathling.Lambek.ProductFree.Tp.atom B)
      h)
```

原子式だけを見分ける述語を定義する。

```lean
@[grind]
def is_atom (A : Tp) : Prop :=
  Mathling.Lambek.ProductFree.translatedIsAtom Tp.toProductFree A
```

原子式のみの文脈から導出できる原子式は公理の場合に限られる。

```lean
theorem atom_generation {Γ : List Tp} {s : String}
  (h_ctx : ∀ x ∈ Γ, is_atom x)
  (h_der : Sequent Γ (Tp.atom s)) :
  Γ = [Tp.atom s] := by
  have h_ctx_pf :
      ∀ x ∈ ctxToProductFree Γ, Mathling.Lambek.ProductFree.is_atom x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
    simpa [is_atom, Tp.toProductFree, Mathling.Lambek.ProductFree.is_atom,
      Mathling.Lambek.ProductFree.translatedIsAtom] using h_ctx y hy
  have h_pf :
      ctxToProductFree Γ = [Mathling.Lambek.ProductFree.Tp.atom s] := by
    simpa [Sequent, ctxToProductFree, Tp.toProductFree] using
      (Mathling.Lambek.ProductFree.atom_generation h_ctx_pf h_der)
  cases Γ with
  | nil =>
      simp [ctxToProductFree] at h_pf
  | cons x xs =>
      cases x with
      | atom name =>
          cases xs with
          | nil =>
              simpa [ctxToProductFree, Tp.toProductFree] using h_pf
          | cons y ys =>
              simp [ctxToProductFree] at h_pf
      | ldiv A B =>
          simp [ctxToProductFree, Tp.toProductFree] at h_pf
```

最後に名前空間を閉じる。

```lean
end Mathling.Lambek.ProductFree.Left.Shallow
```

<!-- vim: set filetype=markdown : -->
