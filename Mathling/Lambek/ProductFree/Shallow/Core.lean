    module

    public import Mathlib.Data.List.Basic
    public import Mathlib.Data.Nat.Basic
    public import Mathling.Lambek.ProductFree.Core
    public import Mathling.Meta.Important
    import LiterateLean
    open scoped LiterateLean


# Shallow Fragment of Product-Free Lambek Calculus

このファイルでは、積を持たない Lambek 計算の shallow 断片を定義する。
shallow 断片では、除法の引数は原子式に限定される。

基本的なメタ理論は `Mathling.Lambek.ProductFree.Core` に翻訳して再利用する。
これにより、shallow 断片の定義は独立に保ちつつ、重い証明を重複させずに済む。

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

まず、shallow 断片で扱う論理式を定義する。

```lean
@[grind cases]
public inductive Tp where
  | atom (name : String) : Tp
  | ldiv (A B : String)  : Tp
  | rdiv (B A : String)  : Tp
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

右除法の記法を導入する。

```lean
infixl:60 " ⧸ " => Tp.rdiv
```

次数は shallow の構文に合わせて単純に数える。

```lean
@[grind =]
public def tp_degree : Tp → Nat
  | Tp.atom _ => 1
  | Tp.ldiv _ _ => 3
  | Tp.rdiv _ _ => 3
```

文脈全体の次数は要素ごとの次数の和で定義する。

```lean
@[grind =]
public def list_degree : List Tp → Nat
  | [] => 0
  | A :: Γ => tp_degree A + list_degree Γ
```

連結に対する加法性もここで押さえる。

```lean
@[grind =]
lemma list_degree_traversible : list_degree (Γ ++ Δ) = list_degree Γ + list_degree Δ := by
  induction Γ <;> grind
```

次数関数 `tp_degree`／`list_degree` は、この shallow 断片ではケース分析により直接定義されており
（原子式は 1、`ldiv`・`rdiv` はいずれも 3）、`Left.Shallow`・`Right.Shallow` のように
`Mathling.Lambek.ProductFree.translatedTpDegree` を経由して一般断片側から借用してはいない。
もっとも、この値は一般断片の次数公式 `tp_degree A + tp_degree B + 1` に原子式の次数 1 を代入した場合と一致しており、
後述するようにこの断片の `cut_admissible` 自体は一般断片への翻訳のみで証明されるため、
実のところこのファイル内で `tp_degree`／`list_degree` を利用する箇所はない。
次数計算をあえて独立に持たせているのは、他の shallow 系統のファイルが将来的に探索の停止性などを
独自に議論する際の土台として温存されている、と理解しておくとよい。

## 一般断片への翻訳

shallow 断片の証明は、一般の product-free 断片へ翻訳して再利用する。

各 shallow 論理式を一般断片の論理式へ写す。

```lean
public def Tp.toProductFree : Tp → Mathling.Lambek.ProductFree.Tp
  | .atom name => Mathling.Lambek.ProductFree.Tp.atom name
  | .ldiv A B =>
      Mathling.Lambek.ProductFree.Tp.ldiv
        (Mathling.Lambek.ProductFree.Tp.atom A)
        (Mathling.Lambek.ProductFree.Tp.atom B)
  | .rdiv B A =>
      Mathling.Lambek.ProductFree.Tp.rdiv
        (Mathling.Lambek.ProductFree.Tp.atom B)
        (Mathling.Lambek.ProductFree.Tp.atom A)
```

文脈も要素ごとに翻訳する。

```lean
public def ctxToProductFree : List Tp → List Mathling.Lambek.ProductFree.Tp :=
  List.map Tp.toProductFree
```

空文脈の翻訳は自明である。

```lean
@[grind =, simp] lemma ctxToProductFree_nil :
    ctxToProductFree [] = [] := rfl
```

先頭要素を付けた文脈の翻訳も簡約できる。

```lean
@[grind =, simp] lemma ctxToProductFree_cons :
    ctxToProductFree (A :: Γ) = A.toProductFree :: ctxToProductFree Γ := rfl
```

連結に対して翻訳が分配されることを記録する。

```lean
@[grind =, simp] lemma ctxToProductFree_append :
    ctxToProductFree (Γ ++ Δ) = ctxToProductFree Γ ++ ctxToProductFree Δ := by
  simp [ctxToProductFree]
```

shallow シーケントは翻訳先のシーケントとして実装する。

```lean
public def Sequent (Γ : List Tp) (A : Tp) : Prop :=
  Mathling.Lambek.ProductFree.Sequent (ctxToProductFree Γ) A.toProductFree
```

## shallow シーケント規則

基本規則は翻訳先の定理をそのまま持ち上げる。

以下では shallow 規則をまとめるための名前空間を開く。

```lean
namespace Sequent
```

公理規則は翻訳先の公理からそのまま従う。

```lean
@[grind .] theorem ax : Sequent [A] A := by
  simpa [Sequent, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.Sequent.ax :
      Mathling.Lambek.ProductFree.Sequent [A.toProductFree] A.toProductFree)
```

左除法の右規則も翻訳先から持ち上げる。

```lean
@[grind =>] theorem ldiv_r
  (h_ne : Γ ≠ [])
  (h : Sequent ([Tp.atom A] ++ Γ) (Tp.atom B)) :
  Sequent Γ (Tp.ldiv A B) := by
  simpa [Sequent, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.Sequent.ldiv_r
      (by simpa using h_ne) h)
```

右除法の右規則では非空性と前提の翻訳を明示する。

```lean
@[grind =>] theorem rdiv_r
  (h_ne : Γ ≠ [])
  (h : Sequent (Γ ++ [Tp.atom A]) (Tp.atom B)) :
  Sequent Γ (Tp.rdiv B A) := by
  have h_ne_pf : ctxToProductFree Γ ≠ [] := by
    cases Γ <;> simp at h_ne ⊢
  have h_pf :
      Mathling.Lambek.ProductFree.Sequent
        (ctxToProductFree Γ ++ [Mathling.Lambek.ProductFree.Tp.atom A])
        (Mathling.Lambek.ProductFree.Tp.atom B) := by
    simpa [Sequent, ctxToProductFree, Tp.toProductFree] using h
  simpa [Sequent, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.Sequent.rdiv_r
      (Γ := ctxToProductFree Γ)
      (A := Mathling.Lambek.ProductFree.Tp.atom A)
      (B := Mathling.Lambek.ProductFree.Tp.atom B)
      h_ne_pf
      h_pf)
```

左除法の左規則も翻訳先の規則から再利用する。

```lean
@[grind =>] theorem ldiv_l
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

右除法の左規則も同様に翻訳から得る。

```lean
@[grind =>] theorem rdiv_l
  (h_arg : Sequent Δ (Tp.atom A))
  (h_main : Sequent (Γ ++ [Tp.atom B] ++ Λ) C) :
  Sequent (Γ ++ [Tp.rdiv B A] ++ Δ ++ Λ) C := by
  have h_main_pf :
      Mathling.Lambek.ProductFree.Sequent
        (ctxToProductFree Γ ++ [Mathling.Lambek.ProductFree.Tp.atom B] ++ ctxToProductFree Λ)
        C.toProductFree := by
    simpa [Sequent, ctxToProductFree, Tp.toProductFree, List.append_assoc] using h_main
  simpa [Sequent, ctxToProductFree, Tp.toProductFree, List.append_assoc] using
    (Mathling.Lambek.ProductFree.Sequent.rdiv_l
      (Δ := ctxToProductFree Δ)
      (A := Mathling.Lambek.ProductFree.Tp.atom A)
      (Γ := ctxToProductFree Γ)
      (B := Mathling.Lambek.ProductFree.Tp.atom B)
      (Λ := ctxToProductFree Λ)
      (C := C.toProductFree)
      h_arg h_main_pf)
```

規則定義をここで閉じる。

```lean
end Sequent
```

読みやすさのため shallow シーケントの記法を与える。

```lean
infixl:50 " ⇒ " => Sequent
```

## 基本補題と主要定理

カット許容性、逆転可能性、原子式生成は一般断片の結果から従う。

導出可能なシーケントは必ず非空の文脈を持つ。

```lean
@[grind =>]
lemma nonempty_premises
  (h : Mathling.Lambek.ProductFree.Shallow.Sequent Γ A) : Γ ≠ [] := by
  cases Γ with
  | nil =>
      simpa [Sequent, ctxToProductFree] using
        (Mathling.Lambek.ProductFree.nonempty_premises h)
  | cons => simp
```

非空文脈を含む連結もやはり非空である。

```lean
@[grind =>]
lemma nonempty_append (h : Γ ≠ []) : Δ ++ Γ ++ Λ ≠ [] := by
  cases Γ <;> simp at h ⊢
```

カット許容性は一般断片での定理を翻訳して得る。

```lean
@[important, grind =>]
public theorem cut_admissible
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

左除法の右規則の逆転可能性を再輸出する。

```lean
@[grind =>] theorem ldiv_invertible {Γ : List Tp} {A B : String}
  (h : Sequent Γ (Tp.ldiv A B)) :
  Sequent ([Tp.atom A] ++ Γ) (Tp.atom B) := by
  simpa [Sequent, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.ldiv_invertible
      (Γ := ctxToProductFree Γ)
      (A := Mathling.Lambek.ProductFree.Tp.atom A)
      (B := Mathling.Lambek.ProductFree.Tp.atom B)
      h)
```

右除法についても同じく逆転可能性を得る。

```lean
@[grind =>] theorem rdiv_invertible {Γ : List Tp} {A B : String}
  (h : Sequent Γ (Tp.rdiv B A)) :
  Sequent (Γ ++ [Tp.atom A]) (Tp.atom B) := by
  simpa [Sequent, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.rdiv_invertible
      (Γ := ctxToProductFree Γ)
      (A := Mathling.Lambek.ProductFree.Tp.atom A)
      (B := Mathling.Lambek.ProductFree.Tp.atom B)
      h)
```

原子式かどうかを判定する述語を定義する。

```lean
@[grind]
public def is_atom : Tp → Prop
  | Tp.atom _ => True
  | _ => False
```

原子式だけからなる文脈では、導出できる原子式は公理の場合に限られる。

```lean
@[grind =>] theorem atom_generation
  (h_ctx : ∀ x ∈ Γ, is_atom x)
  (h_der : Sequent Γ (Tp.atom s)) :
  Γ = [Tp.atom s] := by
  have h_ctx_pf :
      ∀ x ∈ ctxToProductFree Γ, Mathling.Lambek.ProductFree.is_atom x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
    cases y <;> grind only [is_atom, Tp.toProductFree,
      Mathling.Lambek.ProductFree.is_atom]
  have h_pf :
      ctxToProductFree Γ = [Mathling.Lambek.ProductFree.Tp.atom s] := by
    grind only [Sequent, ctxToProductFree, Tp.toProductFree,
      Mathling.Lambek.ProductFree.atom_generation]
  cases Γ with
  | nil => simp_all [ctxToProductFree]
  | cons x xs =>
      cases x <;> cases xs <;> simp_all [ctxToProductFree, Tp.toProductFree]
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
