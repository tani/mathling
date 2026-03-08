    import Mathlib.Data.Nat.Basic
    import Mathlib.Data.List.Basic
    import LiterateLean

# Lambek 計算（積なし）の基本定義と性質

このファイルでは、Lambek 計算（Lambek Calculus）の積（Product）を持たない断片について、
その論理式の定義、シーケント体系、および基本的な性質（カット除去定理など）を定義する。

証明に際して、大量の記号計算が必要になることから `maxHeartbeats`を上げることがある。
したがって、あまりに貧弱なコンピュータでは計算回数が足りずにタイムアウトする可能性がある。

```lean
namespace Mathling.Lambek.ProductFree
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.maxHeartbeats false
```

## 論理式の定義

Lambek 計算の論理式（Type）は、原子式のほかに、左除法 `\` と右除法 `/` を用いて構成される。
`atom` は文字列として定義しており、その論理式を再帰的に合成していくことで、論理式全体を定義する。

```lean
@[grind cases]
inductive Tp where
  | atom (name : String) : Tp
  | ldiv (A B : Tp)      : Tp
  | rdiv (A B : Tp)      : Tp
  deriving Repr, DecidableEq
```

利便性のために、原子式、左除法、右除法の記法を導入する。

```lean
prefix:65 "#" => Tp.atom
infixr:60 " ⧹ " => Tp.ldiv
infixl:60 " ⧸ " => Tp.rdiv
```

例えば、以下のように複合型 $a / b$ を定義することができる。

```lean
#check (# "a" ⧸ # "b")
```

## シーケント体系の定義

Lambek 計算のシーケント $Γ ⇒ A$ は、自然演繹において
論理式の空でないリスト $Γ$ から単一の論理式 $A$ を導出可能であることに対応する。
ここではカット規則を含まない、カットフリーな導出規則を帰納的に定義する。

- $Γ, A ⇒ B$ が導出可能であるとき $Γ ⇒ B / A$ が導出可能
- $A, Γ ⇒ B$ が導出可能であるとき $Γ ⇒ A \backslash B$ が導出可能
- $Δ ⇒ A$ と $Γ, B, Λ ⇒ C$ が導出可能であるとき $Γ, B / A, Δ, Λ ⇒ C$ が導出可能
- $Δ ⇒ A$ と $Γ, B, Λ ⇒ C$ が導出可能であるとき $Γ, Δ, A \backslash B, Λ ⇒ C$ が導出可能

```lean
@[grind intro]
inductive Sequent : List Tp → Tp → Prop where
  | ax : Sequent [A] A
  | rdiv_r :
      Γ ≠ [] →
      Sequent (Γ ++ [A]) B →
      Sequent Γ (B ⧸ A)
  | ldiv_r :
      Γ ≠ [] →
      Sequent ([A] ++ Γ) B →
      Sequent Γ (A ⧹ B)
  | rdiv_l :
      Sequent Δ A →
      Sequent (Γ ++ [B] ++ Λ) C →
      Sequent (Γ ++ [B ⧸ A] ++ Δ ++ Λ) C
  | ldiv_l :
      Sequent Δ A →
      Sequent (Γ ++ [B] ++ Λ) C →
      Sequent (Γ ++ Δ ++ [A ⧹ B] ++ Λ) C

infixl:50 " ⇒ " => Sequent
```

シーケント計算とは、`ax` から始めて、`rdiv_r`, `ldiv_r`, `rdiv_l`, `ldiv_l` を繰り返し適用して
新しいシーケントを生成していく操作である。

## 次数（Degree）の定義

証明の停止性や帰納法のために、論理式およびリストの「次数（サイズ）」を定義する。
ここでは、原子式の次数を 1 とし、演算子の次数を 1 と定義する。これらの総和を次数と呼ぶ。


```lean
@[grind =]
def tp_degree : Tp → Nat
  | # _     => 1
  | A ⧹ B   => tp_degree A + tp_degree B + 1
  | A ⧸ B   => tp_degree A + tp_degree B + 1

@[grind =]
def list_degree : List Tp → Nat
  | []        => 0
  | A :: Γ    => tp_degree A + list_degree Γ
```

リストが連結された場合の次数についての補助定理。
当然であるが、リストの次数は、そのリストの要素の次数を足し合わせたものに等しい。

```lean
@[grind =]
lemma list_degree_traversible : list_degree (Γ ++ Δ) = list_degree Γ + list_degree Δ := by
  induction Γ <;> grind
```

## シーケントの基本的な性質

シーケント計算の定義から、導出可能なシーケントの左辺は必ず空ではない。

```lean
@[grind =>]
lemma nonempty_premises (h : Γ ⇒ A) : Γ ≠ [] := by
  induction h <;> grind [List.append_eq_nil_iff]
```

シーケントの左辺に関する導入規則について特に、
空でないリストを含む連結リストもまた空ではない。

```lean
@[grind =>]
lemma nonempty_append (h : Γ ≠ []) : Δ ++ Γ ++ Λ ≠ [] := by
  grind only [List.append_eq_nil_iff]
```

## リスト分割に関する補題

カット除去定理の証明において、リストの中に特定の論理式が含まれている場合の分割パターンを
網羅的に扱うための補題が必要となる。

基本的に鳩の巣原理を適用することで証明できる。リストの最中に論理式 $α$ が含まれている
場合、このリストを $n$ 分割したとき、$α$ は、$n$ 個の分割のうちのどれかに含まれる。
ここでは $n = 4$ までの分割を考える。

例えば、$Γ₁, α, Γ₂ = Δ₁, Δ₂$ である時、$α$ が $Δ₁$ に含まれるか $Δ₂$ に含まれるか
の２通りが考えられる。

```lean
lemma list_split_2_cases
  (h : Γ₁ ++ [α] ++ Γ₂ = Δ₁ ++ Δ₂) :
  (∃ R, Δ₁ = Γ₁ ++ [α] ++ R ∧ Γ₂ = R ++ Δ₂) ∨
  (∃ L R, Δ₂ = L ++ [α] ++ R ∧ Γ₁ = Δ₁ ++ L ∧ Γ₂ = R) := by
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h
  rcases List.append_eq_append_iff.mp h with ⟨m, rfl, hm⟩ | ⟨m, rfl, hm⟩
  · simp [List.cons_eq_append_iff] at hm
    grind
  · grind

lemma list_split_3_cases
  (h : Γ₁ ++ [α] ++ Γ₂ = Δ₁ ++ Δ₂ ++ Δ₃) :
  (∃ R, Δ₁ = Γ₁ ++ [α] ++ R ∧ Γ₂ = R ++ Δ₂ ++ Δ₃) ∨
  (∃ L R, Δ₂ = L ++ [α] ++ R ∧ Γ₁ = Δ₁ ++ L ∧ Γ₂ = R ++ Δ₃) ∨
  (∃ L R, Δ₃ = L ++ [α] ++ R ∧ Γ₁ = Δ₁ ++ Δ₂ ++ L ∧ Γ₂ = R) := by
  rcases list_split_2_cases (by simpa using h)
    with ⟨R, h1, h2⟩ | ⟨L, R, h1, h2, h3⟩
  · grind
  · rcases list_split_2_cases h1.symm with ⟨R', h4, h5⟩ | ⟨L', R', h4, h5, h6⟩ <;> grind

lemma list_split_4_cases
  (h : Γ₁ ++ [α] ++ Γ₂ = Δ₁ ++ Δ₂ ++ Δ₃ ++ Δ₄) :
  (∃ R, Δ₁ = Γ₁ ++ [α] ++ R ∧ Γ₂ = R ++ Δ₂ ++ Δ₃ ++ Δ₄)
  ∨ (∃ L R, Δ₂ = L ++ [α] ++ R ∧ Γ₁ = Δ₁ ++ L ∧ Γ₂ = R ++ Δ₃ ++ Δ₄)
  ∨ (∃ L R, Δ₃ = L ++ [α] ++ R ∧ Γ₁ = Δ₁ ++ Δ₂ ++ L ∧ Γ₂ = R ++ Δ₄)
  ∨ (∃ L R, Δ₄ = L ++ [α] ++ R ∧ Γ₁ = Δ₁ ++ Δ₂ ++ Δ₃ ++ L ∧ Γ₂ = R) := by
  rcases list_split_2_cases (by simpa using h)
    with ⟨R, h1, h2⟩ | ⟨L, R, h1, h2, h3⟩
  · grind
  · rcases list_split_3_cases (by simpa using h1.symm)
    with ⟨R', h4, h5⟩ | ⟨L', R', h4, h5, h6⟩ | ⟨L', R', h4, h5, h6⟩ <;> grind
```

## カット除去定理（演繹の許容性）

Lambek 計算において、カット規則は **許容的（Admissible）** である。
すなわち、カット規則を用いて導出可能なシーケントは、
カット規則を使用しない体系（カットなしの体系）においても導出できる。

### カット規則の意義と課題

シーケント計算におけるカット規則は、
利用者の視点と体系を研究する側の視点とで、対照的な性質を持つ。
カット規則とは、$\Gamma, A, \Delta \Rightarrow B$ および
 $\Sigma \Rightarrow A$ から $\Gamma, \Sigma, \Delta \Rightarrow B$ を導く規則である。
ここで注目すべきは、前提に含まれる論理式 $A$（カット論理式）が、結論のシーケントからは消失している点である。

-  **利用者の視点**: 既知の定理（$\Sigma \Rightarrow A$）を補題として利用し、
   中間の論理式 $A$ を消去できるため、証明を構成する上で極めて強力な道具となる。
-   **体系を研究する側の視点**: 結論から前提を探索する（後退推論）際、
    消失した $A$ が何であったかを特定しなければならない。
    これは **部分論理式特性（Subformula Property）** を損なうことを意味し、
    自動証明の困難さや体系の無矛盾性の証明において大きな障壁となる。

### カット除去という解決策

この非対称性に対する根源的な回答が「カット除去定理」である。
これは、カット規則を用いて導出できるシーケントは、
実はカットなしでも導出可能であるというメタ定理である。

この定理は「ゲンツェンの基本定理」とも称され、
証明論における最も重要な柱の一つである。本項では、
導出木を直接変形してカットを段階的に除去していく
**構文的カット除去（Syntactic Cut Elimination）** を採用する。
これは、推論規則の組み合わせによって生じる膨大なパターンに対して、
地道に変形操作を定義していく手法である。

### Lean による形式化の利点

構文的カット除去は、考慮すべきケースが極めて多く、
人間による手作業ではパターンの漏れが生じやすい。
しかし、Lean で形式化を行うことで、パターンマッチの網羅性がコンパイラによって保証される。
このような膨大なケース分析を伴う古典的な証明手法こそ、定理証明支援系による恩恵を最も享受できる対象であると言える。

### 証明の構造（ケース分析）

`cut_admissible` の証明は、カット論理式 $A$ の次数および導出の深さに関する二重帰納法に基づく。
膨大な条件分岐を整理すると、大きく分けて「公理 axiom」「交換ケース」「主要ケース」の3つの戦略に集約される。

```mermaid
graph TD
    Start["カット除去定理の証明戦略"] --> CaseL{左側の証明の形}

    CaseL -- "公理 axiom" --> DoneAx["<b>公理 axiom のケース</b><br>Γ = [A] となり自明"]

    CaseL -- "導入規則" --> CaseR{右側の証明の形}

    CaseR -- "公理 axiom" --> DoneAx

    CaseR -- "導入規則" --> IsPrincipal{カット論理式 A は<br>主要か？}

    IsPrincipal -- "片方で主要でない<br>(交換ケース)" --> Commutative["<b>交換ケース (Commutative)</b><br>推論を入れ替えてカットを<br>導出木の「上（前提）」へ移動"]
    Commutative --> IH_Depth["導出の深さに関する帰納法で解決"]

    IsPrincipal -- "両方で主要<br>(主要ケース)" --> Principal["<b>主要ケース (Principal)</b><br>除法を分解してより単純な<br>論理式へのカットに還元"]
    Principal --> IH_Degree["論理式の次数に関する帰納法で解決"]
```

この構造を Lean の `cases` と `induction` を用いて網羅的に書き下すことで、証明が完成する。
特に「主要ケース」では、カット論理式の次数が確実に減少することを利用している。

```lean
set_option maxHeartbeats 1000000 in
@[grind =>]
theorem cut_admissible
  (d_left : Γ ⇒ A)
  (d_right : Δ ++ [A] ++ Λ ⇒ B) :
  Δ ++ Γ ++ Λ ⇒ B := by
    let deg := list_degree (Δ ++ Γ ++ Λ) + tp_degree A + tp_degree B
    generalize h_n : deg = n
    induction n using Nat.strong_induction_on generalizing Γ Δ Λ A B
    next n ih =>
      subst h_n
      cases d_left with
      | ax => grind
      | ldiv_r h_ne_L d_inner_L =>
        rename_i A₁ A₂
        have h_der_A : Γ ⇒ A₁ ⧹ A₂ := by grind
        generalize d_right_eq_x : Δ ++ [A₁ ⧹ A₂] ++ Λ = ContextRight at d_right
        cases d_right with
        | ax =>
          grind only [List.cons_eq_cons, List.append_assoc, List.append_cons,
          List.append_eq_nil_iff, List.append_eq_singleton_iff, Sequent.ldiv_r]
        | ldiv_r h_ne_R d_inner_R =>
          rename_i C D
          let m := list_degree ([C] ++ Δ ++ Γ ++ Λ) + tp_degree (A₁ ⧹ A₂) + tp_degree D
          have h_deg_lt : m < deg := by grind
          have d_permuted_inner : [C] ++ Δ ++ [ A₁ ⧹ A₂ ] ++ Λ ⇒ D := by grind
          have d_cut_result : [C] ++ Δ ++ Γ ++ Λ ⇒ D := by grind
          grind
        | rdiv_r h_ne_R d_inner_R =>
          rename_i C D
          let m := list_degree (Δ ++ Γ ++ Λ ++ [C]) + tp_degree (A₁ ⧹ A₂) + tp_degree D
          have h_deg_lt : m < deg := by grind
          have d_permuted_inner : Δ ++ [ A₁ ⧹ A₂ ] ++ Λ ++ [C] ⇒ D := by grind
          have d_cut_result : Δ ++ Γ ++ Λ ++ [C] ⇒ D := by grind
          grind
        | ldiv_l d_arg d_main =>
          rename_i Δ_arg A_arg Γ_L B_res Γ_R
          rcases list_split_4_cases d_right_eq_x
            with ⟨R, rfl, rfl⟩
               | ⟨L, R, rfl, rfl, rfl⟩
               | ⟨L, R, h_princ, rfl, rfl⟩
               | ⟨L, R, rfl, rfl, rfl⟩
          · let m := list_degree (Δ ++ Γ ++ (R ++ [B_res] ++ Γ_R))
                   + tp_degree (A₁ ⧹ A₂) + tp_degree B
            have h_deg_lt : m < deg := by grind
            have d_cut_main : Δ ++ Γ ++ R ++ [B_res] ++ Γ_R ⇒ B := by grind
            have d_reconstructed : Δ ++ Γ ++ R ++ Δ_arg ++ [A_arg ⧹ B_res] ++ Γ_R ⇒ B := by grind
            grind
          · let m := list_degree (L ++ Γ ++ R) + tp_degree A_arg + tp_degree B
            have h_deg_lt : m < deg := by
              grind only [list_degree, tp_degree, list_degree_traversible]
            have d_cut_arg : L ++ Γ ++ R ⇒ A_arg := by grind
            have d_reconstructed : Γ_L ++ (L ++ Γ ++ R) ++ [A_arg ⧹ B_res] ++ Γ_R ⇒ B := by grind
            grind
          · have h_eq_decomp: [A_arg ⧹ B_res] = L ++ [A₁ ⧹ A₂] ++ R
                              → L = [] ∧ R = [] ∧ A_arg = A₁ ∧ B_res = A₂ := by
              grind [List.singleton_eq_append_iff]
            have h_decomp: L = [] ∧ R = [] ∧ A_arg = A₁ ∧ B_res = A₂ := by grind
            let m1 := list_degree (Γ_L ++ ([A₁] ++ Γ) ++ Γ_R) + tp_degree A₂ + tp_degree B
            have h_deg_lt_princ : m1 < deg := by
              grind only [list_degree, tp_degree, list_degree_traversible]
            have d_reduced : Γ_L ++ Δ_arg ++ Γ ++ Γ_R ⇒ B := by grind
            grind
          · let m := list_degree (Γ_L ++ [B_res] ++ L ++ Γ ++ Λ) + tp_degree (A₁ ⧹ A₂) + tp_degree B
            have h_deg_lt : m < deg := by
              grind only [list_degree, tp_degree, list_degree_traversible]
            have d_cut_main : Γ_L ++ [B_res] ++ L ++ Γ ++ Λ ⇒ B := by grind
            have d_reconstructed : Γ_L ++ Δ_arg ++ [A_arg ⧹ B_res] ++ (L ++ Γ ++ Λ) ⇒ B := by grind
            grind
        | rdiv_l d_arg d_main =>
          rename_i Δ_arg A_arg Γ_L B_res Γ_R
          rcases list_split_4_cases d_right_eq_x
            with ⟨R, rfl, rfl⟩
               | ⟨L, R, h, rfl, rfl⟩
               | ⟨L, R, rfl, rfl, rfl⟩
               | ⟨L, R, rfl, rfl, rfl⟩
          · let m := list_degree (Δ ++ Γ ++ R ++ [B_res] ++ Γ_R) + tp_degree (A₁ ⧹ A₂) + tp_degree B
            have h_deg_lt : m < deg := by
              grind only [list_degree, tp_degree, list_degree_traversible]
            have d_cut_main : Δ ++ Γ ++ (R ++ [B_res] ++ Γ_R) ⇒ B := by grind
            have d_reconstructed : (Δ ++ Γ ++ R) ++ [B_res ⧸ A_arg] ++ Δ_arg ++ Γ_R ⇒ B := by grind
            grind
          · grind [List.singleton_eq_append_iff]
          · let m := list_degree (L ++ Γ ++ R) + tp_degree (A₁ ⧹ A₂) + tp_degree A_arg
            have h_deg_lt : m < deg := by
              grind only [list_degree_traversible, list_degree, tp_degree]
            have d_cut_arg : L ++ Γ ++ R ⇒ A_arg := by grind
            have d_reconstructed : Γ_L ++ [B_res ⧸ A_arg] ++ (L ++ Γ ++ R) ++ Γ_R ⇒ B := by grind
            grind
          · let m := list_degree (Γ_L ++ [B_res] ++ L ++ Γ ++ Λ) + tp_degree (A₁ ⧹ A₂) + tp_degree B
            have h_deg_lt : m < deg := by
              grind only [list_degree_traversible, list_degree, tp_degree]
            have d_cut_main : Γ_L ++ [B_res] ++ L ++ [A₁ ⧹ A₂] ++ Λ ⇒ B := by grind
            have d_reconstructed : Γ_L ++ [B_res] ++ L ++ Γ ++ Λ ⇒ B := by grind
            grind
      | rdiv_r h_ne_L d_inner_L =>
        rename_i A₁ A₂
        have h_der_A : Γ ⇒ A₂ ⧸ A₁ := by grind
        generalize d_right_eq_x : Δ ++ [A₂ ⧸ A₁] ++ Λ = ContextRight at d_right
        cases d_right with
        | ax => grind only [nonempty_append, List.cons_eq_cons, List.append_assoc, List.append_cons,
          List.append_eq_nil_iff, List.append_eq_singleton_iff, Sequent.rdiv_r]
        | ldiv_r h_ne_R d_inner_R =>
          rename_i C D
          let m := list_degree ([C] ++ Δ ++ Γ ++ Λ) + tp_degree (A₂ ⧸ A₁) + tp_degree D
          have h_deg_lt : m < deg := by
            grind only [list_degree, tp_degree, list_degree_traversible]
          have d_permuted_inner : [C] ++ Δ ++ [ A₂ ⧸ A₁ ] ++ Λ ⇒ D := by grind
          have d_cut_result : [C] ++ Δ ++ Γ ++ Λ ⇒ D := by grind
          grind
        | rdiv_r h_ne_R d_inner_R =>
          rename_i C D
          let m := list_degree (Δ ++ Γ ++ Λ ++ [C]) + tp_degree ( A₂ ⧸ A₁ ) + tp_degree D
          have h_deg_lt : m < deg := by
            grind only [list_degree, tp_degree, list_degree_traversible]
          have d_permuted_inner : Δ ++ [ A₂ ⧸ A₁ ] ++ Λ ++ [C] ⇒ D := by grind
          have d_cut_result : Δ ++ Γ ++ Λ ++ [C] ⇒ D := by grind
          grind
        | ldiv_l d_arg d_main =>
          rename_i Δ_arg A_arg Γ_L B_res Γ_R
          rcases list_split_4_cases d_right_eq_x
            with ⟨R, rfl, rfl⟩
               | ⟨L, R, rfl, rfl, rfl⟩
               | ⟨L, R, h_contra, rfl, rfl⟩
               | ⟨L, R, rfl, rfl, rfl⟩
          · let m := list_degree (Δ ++ Γ ++ (R ++ [B_res] ++ Γ_R))
                   + tp_degree (A₂ ⧸ A₁) + tp_degree B
            have h_deg_lt : m < deg := by
              grind only [list_degree, tp_degree, list_degree_traversible]
            have d_cut_main : Δ ++ Γ ++ R ++ [B_res] ++ Γ_R ⇒ B := by grind
            have d_reconstructed : Δ ++ Γ ++ R ++ Δ_arg ++ [A_arg ⧹ B_res] ++ Γ_R ⇒ B := by grind
            grind
          · let m := list_degree (L ++ Γ ++ R) + tp_degree A_arg + tp_degree B
            have h_deg_lt : m < deg := by
              grind only [list_degree, tp_degree, list_degree_traversible]
            have d_cut_arg : L ++ Γ ++ R ⇒ A_arg := by grind
            have d_reconstructed : Γ_L ++ (L ++ Γ ++ R) ++ [A_arg ⧹ B_res] ++ Γ_R ⇒ B := by grind
            grind
          · grind [List.singleton_eq_append_iff]
          · let m := list_degree (Γ_L ++ [B_res] ++ L ++ Γ ++ Λ) + tp_degree (A₂ ⧸ A₁) + tp_degree B
            have h_deg_lt : m < deg := by
              grind only [list_degree, tp_degree, list_degree_traversible]
            have d_cut_main : Γ_L ++ [B_res] ++ L ++ Γ ++ Λ ⇒ B := by grind
            have d_reconstructed : Γ_L ++ Δ_arg ++ [A_arg ⧹ B_res] ++ (L ++ Γ ++ Λ) ⇒ B := by grind
            grind
        | rdiv_l d_arg d_main =>
          rename_i Δ_arg A_arg Γ_L B_res Γ_R
          rcases list_split_4_cases d_right_eq_x
            with ⟨R, rfl, rfl⟩
               | ⟨L, R, h, rfl, rfl⟩
               | ⟨L, R, rfl, rfl, rfl⟩
               | ⟨L, R, rfl, rfl, rfl⟩
          · let m := list_degree (Δ ++ Γ ++ R ++ [B_res] ++ Γ_R) + tp_degree (A₂ ⧸ A₁) + tp_degree B
            have h_deg_lt : m < deg := by
              grind only [list_degree, tp_degree, list_degree_traversible]
            have d_cut_main : Δ ++ Γ ++ (R ++ [B_res] ++ Γ_R) ⇒ B := by grind
            have d_reconstructed : (Δ ++ Γ ++ R) ++ [B_res ⧸ A_arg] ++ Δ_arg ++ Γ_R ⇒ B := by grind
            grind
          · have h_eq_decomp: [B_res ⧸ A_arg] = L ++ [A₂ ⧸ A₁] ++ R
                              → L = [] ∧ R = [] ∧ B_res = A₂ ∧ A_arg = A₁ := by
              grind [List.singleton_eq_append_iff]
            have h_decomp: L = [] ∧ R = [] ∧ B_res = A₂ ∧ A_arg = A₁ := by grind
            let m1 := list_degree (Γ_L ++ (Γ ++ [A₁]) ++ Γ_R) + tp_degree A₂ + tp_degree B
            have h_deg_lt_princ : m1 < deg := by
              grind only [list_degree, tp_degree, list_degree_traversible]
            have d_reduced : (Γ_L ++ Γ) ++ Δ_arg ++ Γ_R ⇒ B := by grind
            grind
          · let m := list_degree (L ++ Γ ++ R) + tp_degree (A₂ ⧸ A₁) + tp_degree A_arg
            have h_deg_lt : m < deg := by
              grind only [list_degree_traversible, list_degree, tp_degree]
            have d_cut_arg : L ++ Γ ++ R ⇒ A_arg := by grind
            have d_reconstructed : Γ_L ++ [B_res ⧸ A_arg] ++ (L ++ Γ ++ R) ++ Γ_R ⇒ B := by grind
            grind
          · let m := list_degree (Γ_L ++ [B_res] ++ L ++ Γ ++ Λ) + tp_degree (A₂ ⧸ A₁) + tp_degree B
            have h_deg_lt : m < deg := by
              grind only [list_degree_traversible, list_degree, tp_degree]
            have d_cut_main : Γ_L ++ [B_res] ++ L ++ [A₂ ⧸ A₁] ++ Λ ⇒ B := by grind
            have d_reconstructed : Γ_L ++ [B_res] ++ L ++ Γ ++ Λ ⇒ B := by grind
            grind
      | rdiv_l d_arg d_main =>
        rename_i Γ_L Γ_R  Δ_arg A_arg B_res
        let m := list_degree (Δ ++ (Δ_arg ++ [A_arg] ++ B_res) ++ Λ) + tp_degree A + tp_degree B
        have h_deg_lt : m < deg := by grind
        have d_restored_context : Δ ++ Δ_arg ++ [A_arg] ++ B_res ++ Λ ⇒ B := by grind
        have d_final : Δ ++ Δ_arg ++ [A_arg ⧸ Γ_R] ++ Γ_L ++ B_res ++ Λ ⇒ B := by grind
        grind
      | ldiv_l d_arg d_main =>
        rename_i Γ_L Γ_R Δ_arg A_arg B_res
        let m := list_degree (Δ ++ (Δ_arg ++ [A_arg] ++ B_res) ++ Λ) + tp_degree A + tp_degree B
        have h_deg_lt : m < deg := by grind
        have d_restored_context : Δ ++ Δ_arg ++ [A_arg] ++ B_res ++ Λ ⇒ B := by grind
        have d_final : Δ ++ Δ_arg ++ Γ_L ++ [Γ_R ⧹ A_arg] ++ B_res ++ Λ ⇒ B := by grind
        grind
```

## 除法の逆転可能性（Invertibility）

さて、カットの許容性が証明できると、とても興味深い性質が見えてくる。その一つが逆転可能性である。
つまり、右導入規則の逆方向もまた成立する。

- 通常版の定義は $A, Γ ⇒ B$ が導出できるとき $Γ ⇒ A \backslash B$ もまた導出可能である。
- 逆転版の定義は $Γ ⇒ A \backslash B$ が導出できるとき $A, Γ ⇒ B$ もまた導出可能である。


```lean
@[grind =>]
theorem ldiv_invertible {Γ : List Tp} {A B : Tp} (h : Γ ⇒ (A ⧹ B)) :
 [A] ++ Γ ⇒ B := by
    have a: [A] ⇒ A := by grind
    have b: [B] ⇒ B := by grind
    have c: [] ++ [A] ++ [A ⧹ B] ++ [] ⇒ B := by grind
    grind

@[grind =>]
theorem rdiv_invertible {Γ : List Tp} {A B : Tp} (h : Γ ⇒ (B ⧸ A)) :
  Γ ++ [A] ⇒ B := by
    have a: [A] ⇒ A := by grind
    have b: [B] ⇒ B := by grind
    have c: [] ++ [B ⧸ A] ++ ([A] ++ []) ⇒ B := by grind
    grind
```

## 原子式に関する性質

証明探索において、これ以上探索を深める必要のない「探索の葉」を特定することは極めて重要である。
具体的には、シーケントの右辺が原子式であり、
かつ左辺のすべての論理式も原子式である場合、そのシーケントが導出可能であるためには、
それが公理 axiom そのものである他に道はない。

この性質を証明する上でも、カット許容性が決定的な役割を果たす。
もし体系にカット規則が不可欠であれば、未知の複雑な論理式を仲介させることで
「実は証明できるかもしれない」という可能性（探索の余地）が常に残ってしまう。
しかし、カット許容性が示されていれば、カットなしの体系で証明できないものは、
いかなる論理式を導入しても証明できないことが保証される。
したがって、原子式のみからなるシーケントについては、
余計な疑念を挟むことなく、公理 axiom の適用可能性のみを確認すればよいのである。

```lean
@[grind]
def is_atom : Tp → Prop
  | Tp.atom _ => True
  | _   => False

@[grind =>]
theorem atom_generation
  (h_ctx : ∀ x ∈ Γ, is_atom x)
  (h_der : Γ ⇒ Tp.atom s) :
    Γ = [Tp.atom s] := by
  cases h_der with
  | ax =>
      grind
  | rdiv_l d_arg d_main =>
      rename_i Δ A Γ₁ B Λ
      have hbad : is_atom (B ⧸ A) := by grind
      grind
  | ldiv_l d_arg d_main =>
      rename_i Δ A Γ₁ B Λ
      have hbad : is_atom (A ⧹ B) := by grind
      grind
```

```lean
end Mathling.Lambek.ProductFree
```

<!-- vim: set filetype=markdown : -->
