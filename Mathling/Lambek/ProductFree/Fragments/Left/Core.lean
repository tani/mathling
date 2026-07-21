    module

    public import Mathlib.Data.List.Basic
    public import Mathlib.Data.Nat.Basic
    public import Mathling.Lambek.ProductFree.Calculus
    public import Mathling.Meta.Important
    import LiterateLean
    open scoped LiterateLean


# Left Fragment of Product-Free Lambek Calculus

このファイルでは、積を持たない Lambek 計算の left 断片を定義する。
left 断片では左除法だけを許し、基本的なメタ理論は
`Mathling.Lambek.ProductFree.Calculus` への翻訳で再利用する。

まず left 断片の名前空間を開く。

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

まず、left 断片の論理式を定義する。

```lean
@[grind cases]
public inductive Tp where
  | atom (name : String) : Tp
  | ldiv (A B : Tp) : Tp
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

各 left 論理式を一般の product-free 論理式へ写す。

```lean
public def Tp.toProductFree : Tp → Mathling.Lambek.ProductFree.Tp
  | .atom name => Mathling.Lambek.ProductFree.Tp.atom name
  | .ldiv A B => Mathling.Lambek.ProductFree.Tp.ldiv A.toProductFree B.toProductFree
```

論理式ひとつの次数は一般断片の次数を通じて定義する。

```lean
@[grind =]
public def tp_degree (A : Tp) : Nat :=
  Mathling.Lambek.ProductFree.translatedTpDegree Tp.toProductFree A
```

文脈全体の次数も一般断片側の定義を再利用する。

```lean
@[grind =]
public def list_degree (Γ : List Tp) : Nat :=
  Mathling.Lambek.ProductFree.translatedListDegree Tp.toProductFree Γ
```

連結に対する加法性も一般断片側から従う。

```lean
@[grind =]
```

```lean
lemma list_degree_traversible : list_degree (Γ ++ Δ) = list_degree Γ + list_degree Δ := by
  grind only [list_degree, Mathling.Lambek.ProductFree.translatedListDegree_traversible]
```

文脈も同じ写像で翻訳する。

```lean
public def ctxToProductFree : List Tp → List Mathling.Lambek.ProductFree.Tp :=
  List.map Tp.toProductFree
```

`ctxToProductFree` は `List.map Tp.toProductFree` そのものであり、要素ごとの変換
`Tp.toProductFree` をリスト全体へ持ち上げただけである。しかし、この写像を通じて
`Sequent` の翻訳が意味を持つためには、リストの構成的な操作——空リスト、先頭への
追加、連結——のいずれについても「まず操作してから写す」のと「まず写してから操作
する」のとで結果が一致しなければならない。次の3つの補題は、`ctxToProductFree` が
リストの単位元 `[]` と結合演算 `++` を保つ***準同型***（list homomorphism）である
ことを述べている。

空文脈の場合はその両者が定義上そのまま一致する。

```lean
@[grind =, simp] lemma ctxToProductFree_nil : ctxToProductFree [] = [] := rfl
```

先頭要素を切り出した場合も `List.map` の定義から直ちに従う。

```lean
@[grind =, simp] lemma ctxToProductFree_cons :
    ctxToProductFree (A :: Γ) = A.toProductFree :: ctxToProductFree Γ := rfl
```

連結の場合は `List.map_append` へ単純に還元されるだけだが、この事実は
以後の証明で頻繁に暗黙のうちに利用される。とりわけ姉妹ファイル
`Left/Decision.lean` の `prove2_iff_sequent` は、一般断片側の
`translatedProve2_iff_Sequent Tp.toProductFree` を呼び出す際に、
left 側の表記 `ctxToProductFree Γ` と一般側の表記 `Γ.map Tp.toProductFree` が
同じ項へ書き換わることに依存しており、この3つの `@[simp]` 補題による
自動正規化がまさにその橋渡しを担っている。

```lean
@[grind =, simp] lemma ctxToProductFree_append :
    ctxToProductFree (Γ ++ Δ) = ctxToProductFree Γ ++ ctxToProductFree Δ := by
  simp [ctxToProductFree]
```

left シーケントは一般断片のシーケントとして実装する。

```lean
public def Sequent (Γ : List Tp) (A : Tp) : Prop :=
  Mathling.Lambek.ProductFree.Sequent (ctxToProductFree Γ) A.toProductFree
```

以下では left 規則をまとめる名前空間を開く。

```lean
namespace Sequent
```

公理規則は翻訳先の公理そのものである。

```lean
@[grind .] theorem ax : Sequent [A] A := by
  simpa [Sequent, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.Sequent.ax :
      Mathling.Lambek.ProductFree.Sequent [A.toProductFree] A.toProductFree)
```

推論規則そのものは `Sequent` 型に固有の帰納子として現れるのではなく
（`Sequent` は一般断片の `Sequent` への定義による還元にすぎない）、ここでは
`Sequent.ax` に加えて `ldiv_r`・`ldiv_l` の2つの構成子だけを個別の定理として
提供する。base 断片の `Sequent` 帰納型は `ldiv_r`・`rdiv_r`・`ldiv_l`・`rdiv_l`
の4本の導入規則を持つが、left 断片の論理式 `Tp` にはそもそも `rdiv` という
構成子が存在しないため、`rdiv_r`・`rdiv_l` に対応する規則は端から不要になる。

左除法の右規則は一般断片側の定理を持ち上げる。`ldiv_r` は、文脈 `Γ` が空でない
という副条件（`h_ne`）のもとで `[A] ++ Γ ⇒ B` から `Γ ⇒ A ⧹ B` を導く。証明の
大半は、この非空条件と前提のシーケントを `ctxToProductFree` で書き換えて一般
断片側の同名の定理へ横流しするだけの配管作業であり、非空性の伝達（`h_ne_pf`）
だけが「`List.map` は要素の有無を保つ」という事実（`cases Γ <;> simp`）に
わずかに依存している。

```lean
@[grind =>] theorem ldiv_r
  (h_ne : Γ ≠ [])
  (h : Sequent ([A] ++ Γ) B) :
  Sequent Γ (A ⧹ B) := by
  have h_ne_pf : ctxToProductFree Γ ≠ [] := by
    cases Γ <;> simp at h_ne ⊢
  have h_pf :
      Mathling.Lambek.ProductFree.Sequent
        ([A.toProductFree] ++ ctxToProductFree Γ)
        B.toProductFree := by
    simpa [Sequent, ctxToProductFree, Tp.toProductFree] using h
  simpa [Sequent, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.Sequent.ldiv_r
      (Γ := ctxToProductFree Γ)
      (A := A.toProductFree)
      (B := B.toProductFree)
      h_ne_pf h_pf)
```

左除法の左規則も翻訳先からそのまま再利用する。`ldiv_l` は、副次シーケント
`Δ ⇒ A` と主シーケント `Γ ++ [B] ++ Λ ⇒ C` とから、新たな複合論理式 `A ⧹ B` を
文脈へ挿入した `Γ ++ Δ ++ [A ⧹ B] ++ Λ ⇒ C` を導く。ここでの持ち上げが `ldiv_r`
よりわずかに込み入っているのは、`Γ ++ Δ ++ [A ⧹ B] ++ Λ` のように4つのリストが
連結された文脈を翻訳するには `List.append_assoc` による結合律の調整が必要に
なるためである。`simpa [..., List.append_assoc]` はこの右結合・左結合の違いを
吸収してから一般断片側の `Sequent.ldiv_l` を適用する。

```lean
@[grind =>] theorem ldiv_l
  (h_arg : Sequent Δ A)
  (h_main : Sequent (Γ ++ [B] ++ Λ) C) :
  Sequent (Γ ++ Δ ++ [A ⧹ B] ++ Λ) C := by
  have h_main_pf :
      Mathling.Lambek.ProductFree.Sequent
        (ctxToProductFree Γ ++ [B.toProductFree] ++ ctxToProductFree Λ)
        C.toProductFree := by
    simpa [Sequent, ctxToProductFree, Tp.toProductFree, List.append_assoc] using h_main
  simpa [Sequent, ctxToProductFree, Tp.toProductFree, List.append_assoc] using
    (Mathling.Lambek.ProductFree.Sequent.ldiv_l
      (Δ := ctxToProductFree Δ)
      (A := A.toProductFree)
      (Γ := ctxToProductFree Γ)
      (B := B.toProductFree)
      (Λ := ctxToProductFree Λ)
      (C := C.toProductFree)
      h_arg h_main_pf)
```

規則定義の名前空間をここで閉じる。

```lean
end Sequent
```

読みやすさのため left 断片側の記法を与える。

```lean
infixl:50 " ⇒ " => Sequent
```

導出可能なシーケントは空文脈を持たない。

```lean
@[grind =>]
```

```lean
lemma nonempty_premises (h : Mathling.Lambek.ProductFree.Left.Sequent Γ A) : Γ ≠ [] := by
  cases Γ with
  | nil =>
      simpa [Sequent, ctxToProductFree] using
        (Mathling.Lambek.ProductFree.nonempty_premises h)
  | cons => simp
```

非空文脈を含む連結もやはり非空である。

```lean
@[grind =>]
```

```lean
lemma nonempty_append (h : Γ ≠ []) : Δ ++ Γ ++ Λ ≠ [] := by
  exact Mathling.Lambek.ProductFree.translatedNonemptyAppend h
```

カット除去定理（`cut_admissible`）の実質的な証明内容——カット論理式の次数と
導出の深さに関する二重帰納法、公理・交換・主要ケースへの場合分け——は
`Mathling.Lambek.ProductFree.Calculus` に一度だけ記述されている。left 断片における
`cut_admissible` は、その膨大な場合分けを繰り返す必要が一切ない。`Sequent` が
定義上すでに一般断片の `Sequent` の特殊化であるため、ここで行う仕事は前提・
結論のシーケントを `ctxToProductFree` で書き換えて型を合わせるだけの配管作業に
尽きる。この「翻訳による再利用」こそが、Left のような断片モジュールを
Core.lean 本体から独立させつつ軽量に保てる理由である。

```lean
@[important, grind =>] public theorem cut_admissible
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

base 断片の `Core.lean` は `ldiv_invertible` と `rdiv_invertible` の両方を
証明している。これは base の論理式 `Tp` が `ldiv` と `rdiv` の両方の構成子を
持つためであり、それぞれの右導入規則の逆転可能性が独立した意味を持つからで
ある。しかし left 断片の `Tp` には `rdiv` という構成子自体が存在しない。
したがって `Γ ⇒ (A ⧸ B)` という形のシーケントはそもそも left 側では書き
下すことすらできず、`rdiv_invertible` に対応する定理を left 側へ輸出する
必要はない。left 断片が必要とするのは `ldiv_invertible` 一本だけであり、
これは `Γ ⇒ A ⧹ B` が導出可能ならば `[A] ++ Γ ⇒ B` も導出可能である——
すなわち右導入規則 `ldiv_r` を「逆向きに」適用できる、という決定手続きの
探索上重要な性質を述べている。

```lean
@[grind =>] theorem ldiv_invertible {Γ : List Tp} {A B : Tp}
  (h : Sequent Γ (A ⧹ B)) :
  Sequent ([A] ++ Γ) B := by
  simpa [Sequent, ctxToProductFree, Tp.toProductFree] using
    (Mathling.Lambek.ProductFree.ldiv_invertible
      (Γ := ctxToProductFree Γ)
      (A := A.toProductFree)
      (B := B.toProductFree)
      h)
```

原子式だけを見分ける述語を定義する。

```lean
@[grind]
public def is_atom (A : Tp) : Prop :=
  Mathling.Lambek.ProductFree.translatedIsAtom Tp.toProductFree A
```

原子式だけの文脈では導出は公理の形に限られる。この事実は決定手続きの停止性
（証明探索の葉をいつ確定させるか）を支える補題だが、left 断片ではこれも
base 断片の `atom_generation` を経由して得る。証明でやや手間がかかるのは、
`is_atom` が `Tp.toProductFree` を経由した間接的な述語であるため、
「`ctxToProductFree Γ` の要素が原子式である」という事実から、逆に
「元の `Γ` の要素も原子式である（`ldiv` ではあり得ない）」ことを
`cases y` によって遡らねばならない点である。最終的に `ctxToProductFree Γ`
が単一の翻訳済み原子式に一致することから、`Γ` 自体も単一の原子式のリスト
であることを、文脈の場合分け（`nil`／`cons x xs` でさらに `xs` も分解）に
よって復元する。

```lean
@[grind =>] theorem atom_generation {Γ : List Tp} {s : String}
  (h_ctx : ∀ x ∈ Γ, is_atom x)
  (h_der : Sequent Γ (Tp.atom s)) :
  Γ = [Tp.atom s] := by
  have h_ctx_pf :
      ∀ x ∈ ctxToProductFree Γ, Mathling.Lambek.ProductFree.is_atom x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
    cases y <;> grind only [is_atom, Mathling.Lambek.ProductFree.translatedIsAtom,
      Tp.toProductFree, Mathling.Lambek.ProductFree.is_atom]
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
end Mathling.Lambek.ProductFree.Left
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
