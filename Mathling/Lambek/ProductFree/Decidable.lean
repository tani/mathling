    import Mathlib.Data.Bool.Basic
    import Mathlib.Data.List.Basic
    import Mathling.Lambek.ProductFree.Basic
    import Lean.LibrarySuggestions.Default
    import LiterateLean

# Lambek 計算の決定可能性の証明

このファイルでは、Lambek計算において与えられたシーケントに対して証明が存在するか
どうかを判定する手続きが決定可能であることを証明する。
まず手続き的に証明探索アルゴリズムを定義する。
そして、証明探索アルゴリズムが `Mathling.Lambek.ProductFree.Basic` で帰納的に定義された
シーケントの導出と一致することを示す。

```lean
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
namespace Mathling.Lambek.ProductFree
```

## 非決定的なリスト操作

### 分割

リストに対する２分割する仕方は、複数ある。その総数を `splits` で定義する。
$Γ = Δ, Λ$ となるような $(Δ, Λ)$ の総数を返す。

```lean
@[grind]
def splits {α} : List α → List (List α × List α)
  | [] => [([], [])]
  | x :: xs => ([], x :: xs) :: (splits xs).map (fun (l, r) => (x :: l, r))
```

この分割ついて補助的な性質を以下に示す。
まず、分割したリストの要素を結合すると元のリストに戻る。

```lean
@[grind .]
lemma splits_list_degree (h : X ∈ splits Γ) :
  X.1 ++ X.2 = Γ := by
  induction Γ generalizing X <;> grind

```

２つのリストを結合したリストの分割を考える。
この時、分割の候補のうち自明なものの一つは、基となった２つのリストの対である。

```lean
@[grind .]
lemma splits_mem {α} (Γ Δ : List α) : (Γ, Δ) ∈ splits (Γ ++ Δ) := by
  induction Γ with
  | nil =>
      cases Δ <;> simp [splits]
  | cons x xs ih =>
      apply List.mem_cons_of_mem
      refine List.mem_map.mpr ?_
      refine ⟨(xs, Δ), ih, ?_⟩
      simp
```

### 選択

リストにおける非決定的な要素選択を定義する。
これは、リスト中の要素を一つ選択し、その前後のリストとの３つ組みからなるリストを生成する。

```lean
@[grind]
def picks {α} : List α → List (List α × α × List α)
  | [] => []
  | x :: xs => ([], x, xs) :: (picks xs).map (fun (l, a, r) => (x :: l, a, r))
```

選択した要素とその前後の結果のリストを結合すると、元のリストに等しくなることを示す。

```lean
@[grind =>]
lemma picks_list_degree (h : X ∈ picks Γ) :
   X.1 ++ [X.2.1] ++ X.2.2 = Γ := by
  induction Γ generalizing X <;> grind
```

リストの結合の中からの選択として、元のリストそれぞれの要素を選ぶ候補が正しく生成されることを示す。

```lean
@[grind .]
lemma picks_mem {α} (Γ Δ : List α) (a : α) :
    (Γ, a, Δ) ∈ picks (Γ ++ [a] ++ Δ) := by
  induction Γ with
  | nil => simp [picks]
  | cons x xs ih =>
      apply List.mem_cons_of_mem
      refine List.mem_map.mpr ?_
      refine ⟨(xs, a, Δ), ?_, ?_⟩
      · simpa [List.append_assoc] using ih
      · simp
```

## 証明探索の候補

もし体系においてカットフリーな証明が存在するならば、証明探索の過程で、
シーケントの左辺から選択と分割を組み合わせて得られる候補の中に、
証明の構造を反映したものが存在するはずである。この候補を `Cand` として定義する。

```lean
@[grind]
inductive Cand where
  | rdiv (L : List Tp) (B A : Tp) (Δ Λ : List Tp)
  | ldiv (Γ Δ : List Tp) (A B : Tp) (Λ : List Tp)
```

証明探索において、探索するべき規則の適用候補は、常に左導出規則のみを考慮する。

これは、右除法や左除法の右導入規則が **反転可能（Invertible）** であるという性質に基づいている。
右導入規則は、結論が導出可能であればその前提も必ず導出可能であるため、
非決定的な選択（バックトラッキング）を伴わずに優先的に適用することができる。
したがって、目的のシーケントの右辺が複合式である限りは右導入規則を適用して分解し、
右辺が原子式となった段階で、はじめて左辺のどの論理式を分解すべきかという「左辺の探索候補」を検討すればよい。
この「左辺の探索候補」を `Cand` として定義する。

```lean
@[grind]
def candidates (Γ : List Tp) : List Cand :=
  (picks Γ).flatMap (fun (L, f, R) =>
    match f with
    | B ⧸ A =>
        (splits R).map (fun (Δ, Λ) => .rdiv L B A Δ Λ)
    | A ⧹ B =>
        (splits L).map (fun (Γ, Δ) => .ldiv Γ Δ A B R)
    | # _ => [])
```

証明探索の候補 `candidates` が、元のリストを正しく分割・選択して得られた構造であることを示す補助定理。

```lean
@[grind =>]
lemma candidates_list_degree (h : c ∈ candidates Γ) :
  match c with
    | .rdiv L B A Δ Λ => L ++ [B ⧸ A] ++ Δ ++ Λ = Γ
    | .ldiv Γ₁ Δ A B R => Γ₁ ++ Δ ++ [A ⧹ B] ++ R = Γ := by
  simp only [candidates, List.mem_flatMap, Prod.exists] at h
  rcases h with ⟨L, f, R, h_pick, h_cand⟩
  cases f with
  | atom s =>
      grind
  | rdiv B A =>
      simp only [List.mem_map, Prod.exists] at h_cand
      rcases h_cand with ⟨X, Y, hX, rfl⟩
      have h_split : X ++ Y = R := splits_list_degree hX
      grind
  | ldiv A B =>
      simp only [List.mem_map, Prod.exists] at h_cand
      rcases h_cand with ⟨X, Y, hX, rfl⟩
      have h_split : X ++ Y = L := splits_list_degree hX
      grind
```

右除法 `/` を含むシーケントの左辺から生成される候補が、正しく `candidates` に含まれることを示す。

```lean
@[grind .]
lemma candidates_rdiv_mem (Γ Δ Λ : List Tp) (A B : Tp) :
  Cand.rdiv Γ B A Δ Λ ∈ candidates (Γ ++ [B ⧸ A] ++ Δ ++ Λ) := by
  unfold candidates
  refine List.mem_flatMap.mpr ?_
  refine ⟨(Γ, B ⧸ A, Δ ++ Λ), ?_, ?_⟩
  · grind
  · refine List.mem_map.mpr ?_
    refine ⟨(Δ, Λ), ?_, ?_⟩ <;> grind
```

左除法 `\` を含むシーケントの左辺から生成される候補が、正しく `candidates` に含まれることを示す。

```lean
@[grind .]
lemma candidates_ldiv_mem (Γ₁ Δ R : List Tp) (A B : Tp) :
  Cand.ldiv Γ₁ Δ A B R ∈ candidates (Γ₁ ++ Δ ++ [A ⧹ B] ++ R) := by
  unfold candidates
  refine List.mem_flatMap.mpr ?_
  refine ⟨(Γ₁ ++ Δ, A ⧹ B, R), ?_, ?_⟩
  · grind
  · refine List.mem_map.mpr ?_
    refine ⟨(Γ₁, Δ), ?_, ?_⟩ <;> grind
```

## 決定可能手続きの定義

シーケントの証明が存在するかどうかを判定する再帰関数 `prove1` を定義する。
右辺の論理式の形に応じて、証明規則を後ろ向きに適用していく。
右辺がアトムの場合は、左辺の要素から候補を選んで再帰的に証明可能かを判定する。
以降に幾つかの証明探索アルゴリズムのバリエーションを導入するkが `prove1` が
このファイルにおける証明探索の主役的アルゴリズムである。

```lean
@[grind .]
def prove1 (Γ : List Tp) (A : Tp) : Bool :=
  match A with
  | Tp.atom s =>
    (Γ = [Tp.atom s]) ||
    (candidates Γ).attach.any (fun ⟨c, _hc⟩ =>
      match c with
      | .rdiv L B A' Δ Λ =>
        prove1 Δ A' && prove1 (L ++ [B] ++ Λ) (# s)
      | .ldiv Λ Δ A' B R =>
        prove1 Δ A' && prove1 (Λ ++ [B] ++ R) (# s))
  | Tp.ldiv A' B =>
    Γ ≠ [] && prove1 ([A'] ++ Γ) B
  | Tp.rdiv B A' =>
    Γ ≠ [] && prove1 (Γ ++ [A']) B
termination_by
  list_degree Γ + tp_degree A
decreasing_by
  all_goals grind
```

上の `prove1` 関数は自身の停止性を証明しながら定義されているが、
停止性を特別に証明する必要がある関数はLeanの *計算* に使用することができないため、
探索の深さ（ステップ数）を明示的に引数に取ることで、自明に停止する補助関数 `proveAux` を定義する。

```lean
@[grind .]
def proveAux : Nat → List Tp → Tp → Bool
  | 0, _,  _ => false
  | n + 1, Γ,  A =>
    match A with
    | Tp.atom s =>
        (Γ = [Tp.atom s]) ||
        (candidates Γ).any (fun c =>
          match c with
          | .rdiv L B A' Δ Λ =>
              proveAux n Δ A' &&
              proveAux n (L ++ [B] ++ Λ) (# s)
          | .ldiv Γ₁ Δ A' B R =>
              proveAux n Δ A' &&
              proveAux n (Γ₁ ++ [B] ++ R) (# s))
    | Tp.ldiv A' B =>
        (Γ ≠ []) && proveAux n ([A'] ++ Γ) B
    | Tp.rdiv B A' =>
        (Γ ≠ []) && proveAux n (Γ ++ [A']) B
```

`proveAux` を用い、探索の深さとしてシーケントのサイズから計算される十分な上限ステップ数を与えることで、
`prove1` と等価な判定関数 `prove2` を定義する。ここでは、$シーケント全体の次数 + 1$ を上限に設定している。
なぜなら、カットの許容可能性から規則の適用をするごとに次数は単調増加することが保証されているからである。
この事実は明示的に証明されていないが、後続の証明が成立することが間接的にこの性質の証明になっている。

```lean
@[grind .]
def prove2 (Γ : List Tp) (A : Tp) : Bool :=
  proveAux (list_degree Γ + tp_degree A + 1) Γ A
```

ここから、これらの関数の性質を証明していく。
まず `proveAux` について、あるステップ数で証明可能ならば、
それより1大きいステップ数でも証明可能であることを示す。

```lean
@[grind =>]
lemma proveAux_mono (h : proveAux n Γ A) :
  proveAux (n + 1) Γ A := by
  induction n generalizing Γ A <;> grind
```

さらに、任意の大きいステップ数に対しても帰納法から単調に証明可能であることが言える。

```lean
@[grind =>]
lemma proveAux_mono_le {n m : Nat} (h : n ≤ m) (hp : proveAux n Γ A) :
    proveAux m Γ A := by
  induction h <;> grind
```

`proveAux` で証明可能ならば、元の `prove1` でも証明可能であること（健全性）を示す。

```lean
@[grind =>]
lemma proveAux_sound (h : proveAux n Γ A) : prove1 Γ A := by
  induction n generalizing Γ A with
  | zero => grind
  | succ n ih =>
      cases A with
      | atom s =>
        simp only [proveAux, Bool.or_eq_true, List.any_eq_true] at h
        unfold prove1
        simp only [Bool.or_eq_true]
        rcases h with h_base | h_cand
        · grind
        · right
          rcases h_cand with ⟨c, hc_mem, hc_val⟩
          simp only [List.any_eq_true]
          refine ⟨⟨c, hc_mem⟩, by simp, ?_⟩
          grind
      | ldiv A' B => grind
      | rdiv B A' => grind
```

逆に、`prove1` で証明可能ならば、十分なステップ数を持たせた `prove2` でも証明可能であること（完全性）を示す。
規則の適用をするごとに次数は単調増加することの証明になっている。

```lean
@[grind =>]
lemma proveAux_complete (h : prove1 Γ A) : prove2 Γ A := by
  unfold prove2
  induction Γ, A using prove1.induct
  case case1 Γ s h_rdiv_left h_rdiv_right h_ldiv_left h_ldiv_right =>
    unfold prove1 at h
    unfold proveAux
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at h ⊢
    rcases h with h_ax | h_left
    · grind
    · right
      rcases h_left with ⟨⟨c, hc_mem⟩, -, hc_val⟩
      refine ⟨c, hc_mem, ?_⟩
      cases c with
      | rdiv L B A' Δ Λ =>
        simp only [Bool.and_eq_true] at hc_val ⊢
        constructor
        · have h_le :
            list_degree Δ + tp_degree A' + 1 ≤
              list_degree Γ + tp_degree (# s) := by
            grind
          exact proveAux_mono_le h_le (by grind)
        · have h_le :
            list_degree (L ++ [B] ++ Λ) + tp_degree (# s) + 1 ≤
              list_degree Γ + tp_degree (# s) := by
            grind
          exact proveAux_mono_le h_le (by grind)
      | ldiv Γ₁ Δ A' B R =>
        simp only [Bool.and_eq_true] at hc_val ⊢
        constructor
        · have h_le :
            list_degree Δ + tp_degree A' + 1 ≤
              list_degree Γ + tp_degree (# s) := by
            grind
          exact proveAux_mono_le h_le (by grind)
        · have h_le :
            list_degree (Γ₁ ++ [B] ++ R) + tp_degree (# s) + 1 ≤
              list_degree Γ + tp_degree (# s) := by
            grind
          exact proveAux_mono_le h_le (by grind)
  case case2 Γ A' B h_rec =>
    unfold prove1 at h
    unfold proveAux
    simp only [Bool.and_eq_true] at h ⊢
    rcases h with ⟨h_ne, h_inner⟩
    constructor
    · grind
    · have h_eq :
        list_degree (A' :: Γ) + tp_degree B + 1 =
          list_degree Γ + tp_degree (A' ⧹ B) := by
        grind
      grind
  case case3 Γ B A' h_rec =>
    unfold prove1 at h
    unfold proveAux
    simp only [Bool.and_eq_true] at h ⊢
    rcases h with ⟨h_ne, h_inner⟩
    constructor
    · grind
    · have h_eq :
        list_degree (Γ ++ [A']) + tp_degree B + 1 =
          list_degree Γ + tp_degree (B ⧸ A') := by
        grind
      grind
```

上記２つの補題から、`prove1` と `prove2` は同値であることがわかる。

```lean
lemma prove1_iff_prove2 : prove1 Γ A ↔ prove2 Γ A := by grind
```

## 論理体系との一致

アルゴリズム `prove1` が真を返すならば、実際にシーケントの導出 $Γ ⇒ A$ が
論理体系において存在すること（健全性）を証明する。

```lean
@[grind =>]
lemma prove1_sound (h : prove1 Γ A) : Γ ⇒ A := by
  induction Γ, A using prove1.induct with
  | case1 Γ s h_rdiv_left h_rdiv_right h_ldiv_left h_ldiv_right =>
      grind only [prove1, List.any_eq, List.any_eq_false, Sequent.ax, candidates_list_degree,
        Sequent.rdiv_l, Sequent.ldiv_l]
  | case2 Γ A' B h_rec => grind
  | case3 Γ B A' h_rec => grind
```

逆に、論理体系においてシーケントの導出 $Γ ⇒ A$ が存在するならば、
アルゴリズム `prove1` は真を返すこと（完全性）を証明する。
prove1 は存在証明だけをすれば良いので `classical` (古典論理ベース)の証明を行なっている。

```lean
@[grind =>]
lemma prove1_complete (h : Γ ⇒ A) : prove1 Γ A := by
  revert h
  classical
  have hp :
      ∀ n Γ A, list_degree Γ + tp_degree A = n → Γ ⇒ A → prove1 Γ A := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih Γ A h_deg h
    unfold prove1
    cases A with
    | atom s =>
        cases h with
        | ax => grind
        | rdiv_l d_arg d_main =>
            rename_i Δ A Γ₁ B Λ
            simp only [Bool.or_eq_true, List.any_eq_true]
            right
            refine ⟨⟨Cand.rdiv Γ₁ B A Δ Λ, by grind⟩, by simp, ?_⟩
            grind
        | ldiv_l d_arg d_main =>
            rename_i Δ A Γ₁ B Λ
            simp only [Bool.or_eq_true, List.any_eq_true]
            right
            refine ⟨⟨Cand.ldiv Γ₁ Δ A B Λ, by grind⟩, by simp, ?_⟩
            grind
    | ldiv A' B => grind
    | rdiv B A' => grind
  grind
```

健全性と完全性をまとめることで、`prove1` がシーケントの導出可能性と同値であることが示される。

```lean
@[grind .]
lemma prove1_iff_sequent : prove1 Γ A ↔ Γ ⇒ A := by grind
```

先ほど示した `prove1` と `prove2` の同値性により、
最終的に自明に停止する証明探索アルゴリズムである
 `prove2` もシーケントの導出可能性と同値であることがわかる。

```lean
@[grind .]
theorem prove2_iff_sequent : prove2 Γ A ↔ Γ ⇒ A := by grind
```

`prove2` は停止性が保証されたアルゴリズムであり、
それが対象とする論理体系の導出可能性と同値であるため、
Lambek計算の証明可能性が決定可能（Decidable）であることが結論づけられる。

```lean
instance : Decidable (Γ ⇒ A) :=
  decidable_of_iff (prove2 Γ A) (by grind)
```

この決定可能性のインスタンスにより、具体的なシーケントに対して Lean の `decide` タクティクを用いて
自動的に証明探索・判定を行わせることが可能になる。

```lean
example : [Tp.atom "p", Tp.ldiv (Tp.atom "p") (Tp.atom "q")] ⇒ Tp.atom "q" :=
  by decide
```

```lean
end Mathling.Lambek.ProductFree
```

<!-- vim: set filetype=markdown : -->
