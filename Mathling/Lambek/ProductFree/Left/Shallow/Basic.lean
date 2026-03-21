    import Mathlib.Data.List.Basic
    import Mathlib.Data.Nat.Basic
    import Mathling.Lambek.ProductFree.Left.Basic
    import LiterateLean

# Left-Shallow Fragment of Product-Free Lambek Calculus

このファイルでは、積を持たない Lambek 計算の left-shallow 断片を定義する。
left-shallow 断片では、左除法の分母は原子式に限定される。

基本的なメタ理論は `Mathling.Lambek.ProductFree.Left.Basic` に翻訳して再利用する。

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

次数は shallow な構文に合わせて定義する。

```lean
@[grind =]
def tp_degree : Tp → Nat
  | Tp.atom _ => 1
  | Tp.ldiv _ _ => 3
```

文脈の次数は要素ごとの次数の和である。

```lean
@[grind =]
def list_degree : List Tp → Nat
  | [] => 0
  | A :: Γ => tp_degree A + list_degree Γ
```

連結に対する加法性も記録しておく。

```lean
@[grind =]
lemma list_degree_traversible : list_degree (Γ ++ Δ) = list_degree Γ + list_degree Δ := by
  induction Γ <;> grind
```

## 一般 left 断片への翻訳

left-shallow の定理は left 断片への翻訳から得る。

各 shallow 論理式を left 断片へ写す。

```lean
def Tp.toLeft : Tp → Mathling.Lambek.ProductFree.Left.Tp
  | .atom name => Mathling.Lambek.ProductFree.Left.Tp.atom name
  | .ldiv A B =>
      Mathling.Lambek.ProductFree.Left.Tp.ldiv
        (Mathling.Lambek.ProductFree.Left.Tp.atom A)
        (Mathling.Lambek.ProductFree.Left.Tp.atom B)
```

文脈も同じ写像で翻訳する。

```lean
def ctxToLeft : List Tp → List Mathling.Lambek.ProductFree.Left.Tp :=
  List.map Tp.toLeft
```

空文脈の翻訳は自明である。

```lean
@[simp] lemma ctxToLeft_nil : ctxToLeft [] = [] := rfl
```

先頭要素を付けた文脈の翻訳も簡約できる。

```lean
@[simp] lemma ctxToLeft_cons :
    ctxToLeft (A :: Γ) = A.toLeft :: ctxToLeft Γ := rfl
```

連結についても翻訳が分配される。

```lean
@[simp] lemma ctxToLeft_append :
    ctxToLeft (Γ ++ Δ) = ctxToLeft Γ ++ ctxToLeft Δ := by
  simp [ctxToLeft]
```

shallow シーケントは left 断片のシーケントとして実装する。

```lean
def Sequent (Γ : List Tp) (A : Tp) : Prop :=
  Mathling.Lambek.ProductFree.Left.Sequent (ctxToLeft Γ) A.toLeft
```

## shallow 規則

以下では shallow 規則をまとめる名前空間を開く。

```lean
namespace Sequent
```

公理規則は翻訳先の公理そのものである。

```lean
theorem ax : Sequent [A] A := by
  simpa [Sequent, ctxToLeft, Tp.toLeft] using
    (Mathling.Lambek.ProductFree.Left.Sequent.ax :
      Mathling.Lambek.ProductFree.Left.Sequent [A.toLeft] A.toLeft)
```

右導入規則は left 断片側の定理を持ち上げる。

```lean
theorem ldiv_r
  (h_ne : Γ ≠ [])
  (h : Sequent ([Tp.atom A] ++ Γ) (Tp.atom B)) :
  Sequent Γ (Tp.ldiv A B) := by
  have h_ne_left : ctxToLeft Γ ≠ [] := by
    cases Γ <;> simp at h_ne ⊢
  have h_left :
      Mathling.Lambek.ProductFree.Left.Sequent
        ([Mathling.Lambek.ProductFree.Left.Tp.atom A] ++ ctxToLeft Γ)
        (Mathling.Lambek.ProductFree.Left.Tp.atom B) := by
    simpa [Sequent, ctxToLeft, Tp.toLeft] using h
  simpa [Sequent, ctxToLeft, Tp.toLeft] using
    (Mathling.Lambek.ProductFree.Left.Sequent.ldiv_r
      (Γ := ctxToLeft Γ)
      (A := Mathling.Lambek.ProductFree.Left.Tp.atom A)
      (B := Mathling.Lambek.ProductFree.Left.Tp.atom B)
      h_ne_left h_left)
```

左導入規則も翻訳先からそのまま再利用する。

```lean
theorem ldiv_l
  (h_arg : Sequent Δ (Tp.atom A))
  (h_main : Sequent (Γ ++ [Tp.atom B] ++ Λ) C) :
  Sequent (Γ ++ Δ ++ [Tp.ldiv A B] ++ Λ) C := by
  have h_main_left :
      Mathling.Lambek.ProductFree.Left.Sequent
        (ctxToLeft Γ ++ [Mathling.Lambek.ProductFree.Left.Tp.atom B] ++ ctxToLeft Λ)
        C.toLeft := by
    simpa [Sequent, ctxToLeft, Tp.toLeft, List.append_assoc] using h_main
  simpa [Sequent, ctxToLeft, Tp.toLeft, List.append_assoc] using
    (Mathling.Lambek.ProductFree.Left.Sequent.ldiv_l
      (Δ := ctxToLeft Δ)
      (A := Mathling.Lambek.ProductFree.Left.Tp.atom A)
      (Γ := ctxToLeft Γ)
      (B := Mathling.Lambek.ProductFree.Left.Tp.atom B)
      (Λ := ctxToLeft Λ)
      (C := C.toLeft)
      h_arg h_main_left)
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
  (h : Mathling.Lambek.ProductFree.Left.Shallow.Sequent Γ A) : Γ ≠ [] := by
  cases Γ with
  | nil =>
      simpa [Sequent, ctxToLeft] using
        (Mathling.Lambek.ProductFree.Left.nonempty_premises h)
  | cons => simp
```

非空文脈を含む連結もやはり非空である。

```lean
@[grind =>]
lemma nonempty_append (h : Γ ≠ []) : Δ ++ Γ ++ Λ ≠ [] := by
  cases Γ <;> simp at h ⊢
```

カット許容性は left 断片での結果を翻訳して得る。

```lean
theorem cut_admissible
  {Γ Δ Λ : List Tp} {A B : Tp}
  (d_left : Mathling.Lambek.ProductFree.Left.Shallow.Sequent Γ A)
  (d_right : Mathling.Lambek.ProductFree.Left.Shallow.Sequent (Δ ++ [A] ++ Λ) B) :
  Mathling.Lambek.ProductFree.Left.Shallow.Sequent (Δ ++ Γ ++ Λ) B := by
  have d_left_left :
      Mathling.Lambek.ProductFree.Left.Sequent (ctxToLeft Γ) A.toLeft := by
    simpa [Sequent, ctxToLeft, Tp.toLeft] using d_left
  have d_right_left :
      Mathling.Lambek.ProductFree.Left.Sequent
        (ctxToLeft Δ ++ [A.toLeft] ++ ctxToLeft Λ) B.toLeft := by
    simpa [Sequent, ctxToLeft, Tp.toLeft, List.append_assoc] using d_right
  have h_cut :
      Mathling.Lambek.ProductFree.Left.Sequent
        (ctxToLeft Δ ++ ctxToLeft Γ ++ ctxToLeft Λ) B.toLeft := by
    exact Mathling.Lambek.ProductFree.Left.cut_admissible d_left_left d_right_left
  simpa [Sequent, ctxToLeft, Tp.toLeft, List.append_assoc] using h_cut
```

左除法の右規則の逆転可能性も再輸出する。

```lean
theorem ldiv_invertible {Γ : List Tp} {A B : String}
  (h : Mathling.Lambek.ProductFree.Left.Shallow.Sequent Γ (Tp.ldiv A B)) :
  Mathling.Lambek.ProductFree.Left.Shallow.Sequent ([Tp.atom A] ++ Γ) (Tp.atom B) := by
  simpa [Sequent, ctxToLeft, Tp.toLeft] using
    (Mathling.Lambek.ProductFree.Left.ldiv_invertible
      (Γ := ctxToLeft Γ)
      (A := Mathling.Lambek.ProductFree.Left.Tp.atom A)
      (B := Mathling.Lambek.ProductFree.Left.Tp.atom B)
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
  (h_der : Mathling.Lambek.ProductFree.Left.Shallow.Sequent Γ (Tp.atom s)) :
  Γ = [Tp.atom s] := by
  have h_ctx_left :
      ∀ x ∈ ctxToLeft Γ, Mathling.Lambek.ProductFree.Left.is_atom x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
    cases y with
    | atom name =>
        simp [Tp.toLeft, Mathling.Lambek.ProductFree.Left.is_atom]
    | ldiv A B =>
        have : False := by simpa [is_atom] using h_ctx _ hy
        contradiction
  have h_left :
      ctxToLeft Γ = [Mathling.Lambek.ProductFree.Left.Tp.atom s] := by
    have h_der_left :
        Mathling.Lambek.ProductFree.Left.Sequent (ctxToLeft Γ)
          (Mathling.Lambek.ProductFree.Left.Tp.atom s) := by
      simpa [Sequent, ctxToLeft, Tp.toLeft] using h_der
    simpa [Sequent, ctxToLeft, Tp.toLeft] using
      (Mathling.Lambek.ProductFree.Left.atom_generation h_ctx_left h_der_left)
  cases Γ with
  | nil =>
      simp [ctxToLeft] at h_left
  | cons x xs =>
      cases x with
      | atom name =>
          cases xs with
          | nil =>
              simpa [ctxToLeft, Tp.toLeft] using h_left
          | cons y ys =>
              simp [ctxToLeft] at h_left
      | ldiv A B =>
          simp [ctxToLeft, Tp.toLeft] at h_left
```

最後に名前空間を閉じる。

```lean
end Mathling.Lambek.ProductFree.Left.Shallow
```

<!-- vim: set filetype=markdown : -->
