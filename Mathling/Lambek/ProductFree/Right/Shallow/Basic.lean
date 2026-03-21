    import Mathlib.Data.List.Basic
    import Mathlib.Data.Nat.Basic
    import Mathling.Lambek.ProductFree.Right.Basic
    import LiterateLean

# Right-Shallow Fragment of Product-Free Lambek Calculus

このファイルでは、積を持たない Lambek 計算の right-shallow 断片を定義する。
right-shallow 断片では、右除法の分母は原子式に限定される。

基本的なメタ理論は `Mathling.Lambek.ProductFree.Right.Basic` に翻訳して再利用する。

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

まず、right-shallow 断片の論理式を定義する。

```lean
@[grind cases]
inductive Tp where
  | atom (name : String) : Tp
  | rdiv (B : String) (A : String) : Tp
  deriving Repr, DecidableEq
```

原子式の記法を導入する。

```lean
prefix:65 "#" => Tp.atom
```

右除法の記法を導入する。

```lean
infixl:60 " ⧸ " => Tp.rdiv
```

次数は shallow な構文に合わせて定義する。

```lean
@[grind =]
def tp_degree : Tp → Nat
  | Tp.atom _ => 1
  | Tp.rdiv _ _ => 3
```

文脈の次数は要素ごとの次数の和である。

```lean
@[grind =]
def list_degree : List Tp → Nat
  | [] => 0
  | A :: Γ => tp_degree A + list_degree Γ
```

連結に対する加法性も先に示す。

```lean
@[grind =]
lemma list_degree_traversible : list_degree (Γ ++ Δ) = list_degree Γ + list_degree Δ := by
  induction Γ <;> grind
```

## 一般 right 断片への翻訳

right-shallow の定理は right 断片への翻訳から得る。

各 shallow 論理式を right 断片へ写す。

```lean
def Tp.toRight : Tp → Mathling.Lambek.ProductFree.Right.Tp
  | .atom name => Mathling.Lambek.ProductFree.Right.Tp.atom name
  | .rdiv B A =>
      Mathling.Lambek.ProductFree.Right.Tp.rdiv
        (Mathling.Lambek.ProductFree.Right.Tp.atom B)
        (Mathling.Lambek.ProductFree.Right.Tp.atom A)
```

文脈も同じ写像で翻訳する。

```lean
def ctxToRight : List Tp → List Mathling.Lambek.ProductFree.Right.Tp :=
  List.map Tp.toRight
```

空文脈の翻訳は自明である。

```lean
@[simp] lemma ctxToRight_nil : ctxToRight [] = [] := rfl
```

先頭要素を付けた文脈の翻訳も簡約できる。

```lean
@[simp] lemma ctxToRight_cons :
    ctxToRight (A :: Γ) = A.toRight :: ctxToRight Γ := rfl
```

連結についても翻訳が分配される。

```lean
@[simp] lemma ctxToRight_append :
    ctxToRight (Γ ++ Δ) = ctxToRight Γ ++ ctxToRight Δ := by
  simp [ctxToRight]
```

shallow シーケントは right 断片のシーケントとして実装する。

```lean
def Sequent (Γ : List Tp) (A : Tp) : Prop :=
  Mathling.Lambek.ProductFree.Right.Sequent (ctxToRight Γ) A.toRight
```

## shallow 規則

以下では shallow 規則をまとめる名前空間を開く。

```lean
namespace Sequent
```

公理規則は翻訳先の公理そのものである。

```lean
theorem ax : Sequent [A] A := by
  simpa [Sequent, ctxToRight, Tp.toRight] using
    (Mathling.Lambek.ProductFree.Right.Sequent.ax :
      Mathling.Lambek.ProductFree.Right.Sequent [A.toRight] A.toRight)
```

右導入規則は right 断片側の定理を持ち上げる。

```lean
theorem rdiv_r
  (h_ne : Γ ≠ [])
  (h : Sequent (Γ ++ [Tp.atom A]) (Tp.atom B)) :
  Sequent Γ (Tp.rdiv B A) := by
  have h_ne_right : ctxToRight Γ ≠ [] := by
    cases Γ <;> simp at h_ne ⊢
  have h_right :
      Mathling.Lambek.ProductFree.Right.Sequent
        (ctxToRight Γ ++ [Mathling.Lambek.ProductFree.Right.Tp.atom A])
        (Mathling.Lambek.ProductFree.Right.Tp.atom B) := by
    simpa [Sequent, ctxToRight, Tp.toRight] using h
  simpa [Sequent, ctxToRight, Tp.toRight] using
    (Mathling.Lambek.ProductFree.Right.Sequent.rdiv_r
      (Γ := ctxToRight Γ)
      (A := Mathling.Lambek.ProductFree.Right.Tp.atom A)
      (B := Mathling.Lambek.ProductFree.Right.Tp.atom B)
      h_ne_right h_right)
```

左導入規則も翻訳先からそのまま再利用する。

```lean
theorem rdiv_l
  (h_arg : Sequent Δ (Tp.atom A))
  (h_main : Sequent (Γ ++ [Tp.atom B] ++ Λ) C) :
  Sequent (Γ ++ [Tp.rdiv B A] ++ Δ ++ Λ) C := by
  have h_main_right :
      Mathling.Lambek.ProductFree.Right.Sequent
        (ctxToRight Γ ++ [Mathling.Lambek.ProductFree.Right.Tp.atom B] ++ ctxToRight Λ)
        C.toRight := by
    simpa [Sequent, ctxToRight, Tp.toRight, List.append_assoc] using h_main
  simpa [Sequent, ctxToRight, Tp.toRight, List.append_assoc] using
    (Mathling.Lambek.ProductFree.Right.Sequent.rdiv_l
      (Δ := ctxToRight Δ)
      (A := Mathling.Lambek.ProductFree.Right.Tp.atom A)
      (Γ := ctxToRight Γ)
      (B := Mathling.Lambek.ProductFree.Right.Tp.atom B)
      (Λ := ctxToRight Λ)
      (C := C.toRight)
      h_arg h_main_right)
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

導出可能なシーケントは空文脈を持たない。

```lean
@[grind =>]
lemma nonempty_premises
  (h : Mathling.Lambek.ProductFree.Right.Shallow.Sequent Γ A) : Γ ≠ [] := by
  cases Γ with
  | nil =>
      simpa [Sequent, ctxToRight] using
        (Mathling.Lambek.ProductFree.Right.nonempty_premises h)
  | cons => simp
```

非空文脈を含む連結もやはり非空である。

```lean
@[grind =>]
lemma nonempty_append (h : Γ ≠ []) : Δ ++ Γ ++ Λ ≠ [] := by
  cases Γ <;> simp at h ⊢
```

カット許容性は right 断片での結果を翻訳して得る。

```lean
theorem cut_admissible
  {Γ Δ Λ : List Tp} {A B : Tp}
  (d_left : Mathling.Lambek.ProductFree.Right.Shallow.Sequent Γ A)
  (d_right : Mathling.Lambek.ProductFree.Right.Shallow.Sequent (Δ ++ [A] ++ Λ) B) :
  Mathling.Lambek.ProductFree.Right.Shallow.Sequent (Δ ++ Γ ++ Λ) B := by
  have d_left_right :
      Mathling.Lambek.ProductFree.Right.Sequent (ctxToRight Γ) A.toRight := by
    simpa [Sequent, ctxToRight, Tp.toRight] using d_left
  have d_right_right :
      Mathling.Lambek.ProductFree.Right.Sequent
        (ctxToRight Δ ++ [A.toRight] ++ ctxToRight Λ) B.toRight := by
    simpa [Sequent, ctxToRight, Tp.toRight, List.append_assoc] using d_right
  have h_cut :
      Mathling.Lambek.ProductFree.Right.Sequent
        (ctxToRight Δ ++ ctxToRight Γ ++ ctxToRight Λ) B.toRight := by
    exact Mathling.Lambek.ProductFree.Right.cut_admissible d_left_right d_right_right
  simpa [Sequent, ctxToRight, Tp.toRight, List.append_assoc] using h_cut
```

右除法の右規則の逆転可能性も再輸出する。

```lean
theorem rdiv_invertible {Γ : List Tp} {B A : String}
  (h : Mathling.Lambek.ProductFree.Right.Shallow.Sequent Γ (Tp.rdiv B A)) :
  Mathling.Lambek.ProductFree.Right.Shallow.Sequent (Γ ++ [Tp.atom A]) (Tp.atom B) := by
  simpa [Sequent, ctxToRight, Tp.toRight] using
    (Mathling.Lambek.ProductFree.Right.rdiv_invertible
      (Γ := ctxToRight Γ)
      (A := Mathling.Lambek.ProductFree.Right.Tp.atom A)
      (B := Mathling.Lambek.ProductFree.Right.Tp.atom B)
      h)
```

原子式だけを見分ける述語を定義する。

```lean
@[grind]
def is_atom : Tp → Prop
  | Tp.atom _ => True
  | _ => False
```

原子式のみの文脈から導出できる原子式は公理の場合に限られる。

```lean
theorem atom_generation {Γ : List Tp} {s : String}
  (h_ctx : ∀ x ∈ Γ, is_atom x)
  (h_der : Mathling.Lambek.ProductFree.Right.Shallow.Sequent Γ (Tp.atom s)) :
  Γ = [Tp.atom s] := by
  have h_ctx_right :
      ∀ x ∈ ctxToRight Γ, Mathling.Lambek.ProductFree.Right.is_atom x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
    cases y with
    | atom name =>
        simp [Tp.toRight, Mathling.Lambek.ProductFree.Right.is_atom]
    | rdiv B A =>
        have : False := by simpa [is_atom] using h_ctx _ hy
        contradiction
  have h_right :
      ctxToRight Γ = [Mathling.Lambek.ProductFree.Right.Tp.atom s] := by
    have h_der_right :
        Mathling.Lambek.ProductFree.Right.Sequent (ctxToRight Γ)
          (Mathling.Lambek.ProductFree.Right.Tp.atom s) := by
      simpa [Sequent, ctxToRight, Tp.toRight] using h_der
    simpa [Sequent, ctxToRight, Tp.toRight] using
      (Mathling.Lambek.ProductFree.Right.atom_generation h_ctx_right h_der_right)
  cases Γ with
  | nil =>
      simp [ctxToRight] at h_right
  | cons x xs =>
      cases x with
      | atom name =>
          cases xs with
          | nil =>
              simpa [ctxToRight, Tp.toRight] using h_right
          | cons y ys =>
              simp [ctxToRight] at h_right
      | rdiv B A =>
          simp [ctxToRight, Tp.toRight] at h_right
```

最後に名前空間を閉じる。

```lean
end Mathling.Lambek.ProductFree.Right.Shallow
```

<!-- vim: set filetype=markdown : -->
