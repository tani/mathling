    import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import LiterateLean

まず right 断片の名前空間を開く。

```lean
namespace Mathling.Lambek.ProductFree.Right
```

この literate ファイルでは、コードブロック単位で style 抑止を管理する。

```lean
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.maxHeartbeats false
```

## 論理式の定義

原子式（atom）は文字列（String）を用いて識別され、右除法演算子を再帰的に適用することで、任意の論理式を構成する。

```lean
@[grind cases]
inductive Tp where
  | atom (name : String) : Tp
  | rdiv (A B : Tp)      : Tp
  deriving Repr, DecidableEq
```

## シーケント体系

利便性のために、原子式、右除法の記法を導入する。

原子式と右除法の記法をここで導入する。

```lean
prefix:65 "#" => Tp.atom
infixl:60 " ⧸ " => Tp.rdiv
```

## シーケント体系の定義

Lambek 計算のシーケント $Γ ⇒ A$ は、前提となる論理式の空でないリスト $Γ$ から、単一の結論 $A$ が導出可能であることを表す。
ここでは、カット規則を含まない、カットフリーなシーケント体系を帰納的に定義する。

- $Γ, A ⇒ B$ が導出可能であるとき $Γ ⇒ B / A$ が導出可能
- $Δ ⇒ A$ と $Γ, B, Λ ⇒ C$ が導出可能であるとき $Γ, B / A, Δ, Λ ⇒ C$ が導出可能

```lean
@[grind intro]
inductive Sequent : List Tp → Tp → Prop where
  | ax : Sequent [A] A
  | rdiv_r :
      Γ ≠ [] →
      Sequent (Γ ++ [A]) B →
      Sequent Γ (B ⧸ A)
  | rdiv_l :
      Sequent Δ A →
      Sequent (Γ ++ [B] ++ Λ) C →
      Sequent (Γ ++ [B ⧸ A] ++ Δ ++ Λ) C

infixl:50 " ⇒ " => Sequent
```

## 次数（Degree）の定義

証明の停止性や帰納法のために、論理式およびリストの「次数（サイズ）」を定義する。
ここでは、原子式の次数を 1 とし、演算子の次数を 1 と定義する。これらの総和を次数と呼ぶ。


論理式ひとつの次数を定義する。

```lean
@[grind =]
def tp_degree : Tp → Nat
  | # _     => 1
  | A ⧸ B   => tp_degree A + tp_degree B + 1
```

文脈全体の次数は要素ごとの和とする。

```lean
@[grind =]
def list_degree : List Tp → Nat
  | []        => 0
  | A :: Γ    => tp_degree A + list_degree Γ
```

## 証明の停止性
リストの次数は、そのリストに含まれる各論理式の次数の総和に等しい。

連結に対する加法性を示す。

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

リストの途中に特定の論理式 $α$ が含まれている場合、このリストを複数に分割した際、
$α$ はいずれかの断片に必ず含まれることになる。
ここでは $n = 4$ までの分割を考える。

例えば、$Γ₁, α, Γ₂ = Δ₁, Δ₂$ である時、$α$ が $Δ₁$ に含まれるか $Δ₂$ に含まれるか
の２通りが考えられる。

2 分割の場合分けをまず示す。

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
```

3 分割の場合分けは 2 分割補題を使って導く。

```lean
lemma list_split_3_cases
  (h : Γ₁ ++ [α] ++ Γ₂ = Δ₁ ++ Δ₂ ++ Δ₃) :
  (∃ R, Δ₁ = Γ₁ ++ [α] ++ R ∧ Γ₂ = R ++ Δ₂ ++ Δ₃) ∨
  (∃ L R, Δ₂ = L ++ [α] ++ R ∧ Γ₁ = Δ₁ ++ L ∧ Γ₂ = R ++ Δ₃) ∨
  (∃ L R, Δ₃ = L ++ [α] ++ R ∧ Γ₁ = Δ₁ ++ Δ₂ ++ L ∧ Γ₂ = R) := by
  rcases list_split_2_cases (by simpa using h)
    with ⟨R, h1, h2⟩ | ⟨L, R, h1, h2, h3⟩
  · grind
  · rcases list_split_2_cases h1.symm with ⟨R', h4, h5⟩ | ⟨L', R', h4, h5, h6⟩ <;> grind
```

4 分割の場合分けも同様に段階的に導く。

```lean
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

### カット除去の証明戦略

この定理の証明は、カット論理式の次数と導出の深さに関する二重帰納法に基づいている。

```mermaid
graph TD
    Start["カット除去の証明戦略 (Right)"] --> CaseL{左側の証明}
    CaseL -- "公理 ax" --> DoneAx["Γ = [A] より自明"]
    CaseL -- "導入規則" --> CaseR{右側の証明}
    CaseR -- "導入規則" --> IsPrincipal{カット論理式は主要か？}
    IsPrincipal -- "主要ケース" --> Principal["除法を分解して還元"]
```

## カット除去定理（演繹の許容性）

Lambek 計算において、カット規則は **許容的（Admissible）** である。
すなわち、カット規則を用いて導出可能なシーケントは、
カット規則を使用しない体系（カットなしの体系）においても導出できる。

重い証明なので heartbeat 上限だけ局所的に緩める。

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
      | rdiv_r h_ne_L d_inner_L =>
        rename_i A₁ A₂
        have h_der_A : Γ ⇒ A₂ ⧸ A₁ := by grind
        generalize d_right_eq_x : Δ ++ [A₂ ⧸ A₁] ++ Λ = ContextRight at d_right
        cases d_right with
        | ax => grind only [nonempty_append, List.cons_eq_cons, List.append_assoc, List.append_cons,
          List.append_eq_nil_iff, List.append_eq_singleton_iff, Sequent.rdiv_r]
        | rdiv_r h_ne_R d_inner_R =>
          rename_i C D
          let m := list_degree (Δ ++ Γ ++ Λ ++ [C]) + tp_degree ( A₂ ⧸ A₁ ) + tp_degree D
          have h_deg_lt : m < deg := by
            grind only [list_degree, tp_degree, list_degree_traversible]
          have d_permuted_inner : Δ ++ [ A₂ ⧸ A₁ ] ++ Λ ++ [C] ⇒ D := by grind
          have d_cut_result : Δ ++ Γ ++ Λ ++ [C] ⇒ D := by grind
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
```

## 除法の逆転可能性（Invertibility）

さて、カットの許容性が証明できると、とても興味深い性質が見えてくる。その一つが逆転可能性である。
つまり、右導入規則の逆方向もまた成立する。

- 通常の推論規則（右導入規則）は、$Γ, A ⇒ B$ が導出できるとき $Γ ⇒ B / A$ が導出可能であるというものである。
- 逆転可能とは、逆に $Γ ⇒ B / A$ が導出できるとき $Γ, A ⇒ B$ もまた導出可能であるという性質である。

右除法右導入の逆転可能性を示す。

```lean
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

カット許容性が示されていれば、「カットなしの体系で証明できないものは、いかなる補題を導入しても証明できない」ことが保証される。
したがって、原子式のみからなるシーケントについては、単に公理 `ax` の適用可能性のみを確認すればよい。

原子式だけを見分ける述語を定義する。

```lean
@[grind]
def is_atom : Tp → Prop
  | Tp.atom _ => True
  | _   => False
```

原子式だけの文脈では導出は公理の形に限られる。

```lean
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
```

最後に名前空間を閉じる。

```lean
end Mathling.Lambek.ProductFree.Right
```

<!-- vim: set filetype=markdown : -->
