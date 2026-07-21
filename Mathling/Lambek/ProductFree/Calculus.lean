    module

    public import Mathlib.Data.Nat.Basic
    public import Mathlib.Data.List.Basic
    public import Mathling.Meta.Important
    import LiterateLean
    open scoped LiterateLean


# Product-free Lambek calculus

このファイルでは、Lambek 計算（Lambek Calculus）の積（Product）を持たない断片について、
その論理式の定義、シーケント体系、および基本的な性質（カット除去定理など）を定義する。

証明に際して、複雑な論理式では膨大な記号計算が必要になるため、`maxHeartbeats` の設定値を引き上げている。
実行環境の計算資源によっては、タイムアウトが発生する可能性があることに注意されたい。

```lean
namespace Mathling.Lambek.ProductFree
```

以下の style 抑止は、この literate ファイル内でコードブロックを細かく分ける都合上、
Lean コードブロックに対してだけ適用する。

```lean
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.maxHeartbeats false
```

## 論理式の定義

原子式（atom）は文字列（String）を用いて識別され、除法演算子を再帰的に適用することで、任意の論理式を構成する。

```lean
@[grind cases]
public inductive Tp where
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

例えば、以下のように原子式 `a`, `b` から複合的な論理式 $a / b$ を定義することができる。

```lean
example : Tp := # "a" ⧸ # "b"
```

Lambek 計算のシーケント $Γ ⇒ A$ は、前提となる論理式の空でないリスト $Γ$ から、単一の結論 $A$ が導出可能であることを表す。
ここでは、カット規則を含まない、カットフリーなシーケント体系（Ghentzen-style sequent calculus）を帰納的に定義する。

- $Γ, A ⇒ B$ が導出可能であるとき $Γ ⇒ B / A$ が導出可能
- $A, Γ ⇒ B$ が導出可能であるとき $Γ ⇒ A \backslash B$ が導出可能
- $Δ ⇒ A$ と $Γ, B, Λ ⇒ C$ が導出可能であるとき $Γ, B / A, Δ, Λ ⇒ C$ が導出可能
- $Δ ⇒ A$ と $Γ, B, Λ ⇒ C$ が導出可能であるとき $Γ, Δ, A \backslash B, Λ ⇒ C$ が導出可能

```lean
@[grind intro]
public inductive Sequent : List Tp → Tp → Prop where
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

シーケント計算による導出は、公理 `ax` を起点として、各種の推論規則をボトムアップまたはトップダウンに適用し、
目的のシーケントに到達するまでのプロセスを記述するものである。

## 次数（Degree）の定義

証明の停止性や帰納法のために、論理式およびリストの「次数（サイズ）」を定義する。
ここでは、原子式の次数を 1 とし、演算子の次数を 1 と定義する。これらの総和を次数と呼ぶ。


```lean
@[grind =]
public def tp_degree : Tp → Nat
  | # _     => 1
  | A ⧹ B   => tp_degree A + tp_degree B + 1
  | A ⧸ B   => tp_degree A + tp_degree B + 1
```

```lean
@[grind =]
public def list_degree : List Tp → Nat
  | []        => 0
  | A :: Γ    => tp_degree A + list_degree Γ
```

リストの次数は、そのリストに含まれる各論理式の次数の総和に等しい。

```lean
@[grind =]
lemma list_degree_traversible : list_degree (Γ ++ Δ) = list_degree Γ + list_degree Δ := by
  induction Γ <;> grind
```

## シーケントの基本的な性質

シーケント計算の定義から、導出可能なシーケントの左辺は必ず空ではない。

```lean
@[grind =>]
public lemma nonempty_premises (h : Γ ⇒ A) : Γ ≠ [] := by
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
$α$ はいずれかの断片に必ず含まれることになる。ここでは 4 分割までのパターンを網羅する。

例えば、$Γ₁, α, Γ₂ = Δ₁, Δ₂$ である時、$α$ が $Δ₁$ に含まれるか $Δ₂$ に含まれるか
の２通りが考えられる。

なお「区別された要素がどの断片に落ちるか」を数え上げるという発想自体は、
姉妹ファイル `Mathling.Lambek.ProductFree.Decision` の証明探索アルゴリズムが用いる
`splits`・`picks` という非決定的なリスト操作とも通じるところがある。
ただし両者は独立に実装されており、本節の一連の補題は専ら、
カット除去定理の証明の中で「除去規則が生成する文脈」と
「カット規則が持ち込む文脈」がどのように重なり合うかを網羅的に場合分けするためだけに用いる。

```lean
@[grind .] lemma list_split_2_cases
  (h : Γ₁ ++ [α] ++ Γ₂ = Δ₁ ++ Δ₂) :
  (∃ R, Δ₁ = Γ₁ ++ [α] ++ R ∧ Γ₂ = R ++ Δ₂) ∨
  (∃ L R, Δ₂ = L ++ [α] ++ R ∧ Γ₁ = Δ₁ ++ L ∧ Γ₂ = R) := by
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h
  rcases List.append_eq_append_iff.mp h with ⟨m, rfl, hm⟩ | ⟨m, rfl, hm⟩
  · simp [List.cons_eq_append_iff] at hm
    grind
  · grind
```

3 分割の場合は、上記の 2 分割の結果に対してもう一度 2 分割の補題を適用することで得られる。
$Δ₁$ 側に落ちた場合はそのまま最初のケースとなり、$Δ₂ ++ Δ₃$ 側に落ちた場合は
その断片をさらに 2 分割することで、$α$ が $Δ₂$ に含まれるか $Δ₃$ に含まれるかを決定する。

```lean
@[grind .] lemma list_split_3_cases
  (h : Γ₁ ++ [α] ++ Γ₂ = Δ₁ ++ Δ₂ ++ Δ₃) :
  (∃ R, Δ₁ = Γ₁ ++ [α] ++ R ∧ Γ₂ = R ++ Δ₂ ++ Δ₃) ∨
  (∃ L R, Δ₂ = L ++ [α] ++ R ∧ Γ₁ = Δ₁ ++ L ∧ Γ₂ = R ++ Δ₃) ∨
  (∃ L R, Δ₃ = L ++ [α] ++ R ∧ Γ₁ = Δ₁ ++ Δ₂ ++ L ∧ Γ₂ = R) := by
  rcases list_split_2_cases (by simpa using h)
    with ⟨R, h1, h2⟩ | ⟨L, R, h1, h2, h3⟩
  · grind
  · rcases list_split_2_cases h1.symm with ⟨R', h4, h5⟩ | ⟨L', R', h4, h5, h6⟩ <;> grind
```

同様に 4 分割は、3 分割の結果へさらに 2 分割を適用することで構成される。
`cut_admissible` の証明では、除去規則側の文脈 $Γ, B, Λ$ とカット規則側の文脈 $Δ₁, Δ₂, Δ₃, Δ₄$
（あるいはこれらの入れ替え）が衝突する箇所を特定するために、ちょうどこの 4 分割が必要になる。
入れ子の適用によって構成しているため、任意有限個への分割への一般化も同じ手法で可能である。

```lean
@[grind .] lemma list_split_4_cases
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

シーケント計算におけるカット規則は、ユーザー（証明を構成する側）と
メタ理論（体系の性質を研究する側）の双方から見て、極めて対照的な意義を持つ。
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
このような膨大なケース分析を伴うメタ理論の証明こそ、Lean のような定理証明支援系の恩恵を最も享受できる分野である。

### 証明の構造（ケース分析）

`cut_admissible` の証明は、カット論理式 $A$ の次数および導出の深さに関する二重帰納法に基づく。
膨大な条件分岐を整理すると、大きく分けて「公理 axiom」「交換ケース」「主要ケース」の3つの戦略に集約される。

```mermaid
graph TD
    Start["カット除去定理の証明戦略"] --> CaseL{左側の証明の形}

    CaseL -- "公理 ax" --> DoneAx["<b>公理 ax のケース</b><br>Γ = [A] となり自明"]

    CaseL -- "導入規則" --> CaseR{右側の証明の形}

    CaseR -- "公理 ax" --> DoneAx

    CaseR -- "導入規則" --> IsPrincipal{カット論理式 A は<br>主要か？}

    IsPrincipal -- "片方で主要でない<br>(交換ケース)" --> Commutative["<b>交換ケース (Commutative)</b><br>推論を入れ替えてカットを<br>導出木の「上（前提）」へ移動"]
    Commutative --> IH_Depth["導出の深さに関する帰納法で解決"]

    IsPrincipal -- "両方で主要<br>(主要ケース)" --> Principal["<b>主要ケース (Principal)</b><br>除法を分解してより単純な<br>論理式へのカットに還元"]
    Principal --> IH_Degree["論理式の次数に関する帰納法で解決"]
```

この構造を Lean の `cases` と `induction` を用いて網羅的に書き下すことで、証明が完成する。
特に「主要ケース」では、カット論理式の次数が確実に減少することを利用している。

### 形式的主張と単一の帰納法の尺度

`cut_admissible` が主張するのは、$Γ ⇒ A$ かつ $Δ, A, Λ ⇒ B$ が
（カットフリー体系において）導出可能ならば、$Δ, Γ, Λ ⇒ B$ もまた
（同じくカットフリー体系において）導出可能である、という事実である。
これは体系にカット規則を新たに追加できるという主張ではなく、
カットフリーな規則だけを使って、カット規則を使った場合と同じ結論に
実際に到達できることを示す構成的な定理である。

前掲の図が示す通り、証明中では 2 種類の帰納法が現れる——
交換ケースでは導出の深さに関する帰納法、主要ケースでは論理式の次数に関する帰納法である。
この 2 つを Lean の項再帰性チェッカーが受理できる単一の帰納法にまとめるため、
証明の冒頭では

```math
\mathit{deg} := \mathrm{list\_degree}(Δ ++ Γ ++ Λ) + \mathrm{tp\_degree}(A) + \mathrm{tp\_degree}(B)
```

という 1 つの自然数を定義し、この `deg` に関する強い帰納法（`Nat.strong_induction_on`）を回す。
交換ケースでは推論の入れ替えによって `deg` 自体は変化しないが、
入れ替え後に再帰呼び出しする対象の導出がより浅くなるように議論を組み立て、
主要ケースでは除法が分解されてカット論理式が真に小さな部分論理式に置き換わるため
`deg` が真に減少する。両者を単一の尺度 `deg` の減少として統一的に扱うことで、
場合分けの数が多いにもかかわらず、全体を 1 つの `induction ... using Nat.strong_induction_on`
で処理できるようになっている。

### なぜ「許容性」を証明しなければならないのか

カットが許容的であるという性質は、体系の定義に最初からカット規則を
含めてしまえば得られるようなものではない。それでは「カットを使わずに済む」
という主張そのものが空虚になってしまう。したがって、カットフリーな規則だけを
公理として出発し、任意の $Γ ⇒ A$ と $Δ, A, Λ ⇒ B$ の組に対して
$Δ, Γ, Λ ⇒ B$ の証明をカットフリー体系の規則のみで具体的に構成できることを、
上記の帰納法によって実際に示さねばならない。カット規則を単に体系に追加するのとは異なり、
この構成的な証明を経て初めて、カットフリー体系がカットを含む体系と同じ導出能力を
持つことが保証される。

### 決定手続きとの関係

この事実は、姉妹ファイル `Mathling.Lambek.ProductFree.Decision` で定義される
証明探索アルゴリズム `prove1`／`prove2` にとって死活的に重要である。
決定手続きは、結論のシーケントの右辺の形や左辺に現れる論理式だけを手掛かりに、
規則をボトムアップに逆算することで証明を探索する。しかしカット規則は、
結論には一切現れない論理式 $A$ を経由することを要求するため、
もしカット規則を排除できないままであれば、探索アルゴリズムは
「どのような $A$ を補題として経由すればよいか」を有限の情報だけから
決定できず、探索が停止する保証を失ってしまう。
`cut_admissible` によってカットフリー体系だけで（カットを許す体系と）
同じ導出能力を持つことが保証されるため、`Decision.lean` の探索アルゴリズムは
カット規則を一切考慮する必要がなく、`candidates`（`splits`・`picks` を用いて
構成される）が列挙する有限個の分解パターンのみを調べれば健全性・完全性の
双方が成り立つ。

```lean
set_option maxHeartbeats 1000000 in
@[important, grind =>]
public theorem cut_admissible
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

こうして `cut_admissible` が確立されたことで、カットフリー体系はカットを含む体系と
全く同じ導出能力を持つことが保証された。以下では、この事実を土台として、
シーケント計算のいくつかの派生的な性質を導いていく。

## 除法の逆転可能性（Invertibility）

さて、カットの許容性が証明できると、とても興味深い性質が見えてくる。その一つが逆転可能性である。
つまり、右導入規則の逆方向もまた成立する。

- 通常版の定義は $A, Γ ⇒ B$ が導出できるとき $Γ ⇒ A \backslash B$ もまた導出可能である。
- 逆転版の定義は $Γ ⇒ A \backslash B$ が導出できるとき $A, Γ ⇒ B$ もまた導出可能である。


```lean
@[grind =>]
public theorem ldiv_invertible {Γ : List Tp} {A B : Tp} (h : Γ ⇒ (A ⧹ B)) :
  [A] ++ Γ ⇒ B := by
    have a: [A] ⇒ A := by grind
    have b: [B] ⇒ B := by grind
    have c: [] ++ [A] ++ [A ⧹ B] ++ [] ⇒ B := by grind
    grind
```

```lean
@[grind =>]
public theorem rdiv_invertible {Γ : List Tp} {A B : Tp} (h : Γ ⇒ (B ⧸ A)) :
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
カット許容性が示されていれば、「カットなしの体系で証明できないものは、いかなる補題を導入しても証明できない」ことが保証される。
したがって、原子式のみからなるシーケントについては、単に公理 `ax` の適用可能性（すなわち一致判定）のみを確認すればよい。

```lean
/-- Recognize atoms in the public product-free syntax.

Its body is exposed because public fragment translations normalize this
predicate inside their `grind` proofs. -/
@[grind, expose] public def is_atom : Tp → Prop
  | Tp.atom _ => True
  | _   => False
```

```lean
@[grind =>]
public theorem atom_generation
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

## 翻訳ラッパ用の共通 utility

他の断片では、各論理式をこの一般断片へ翻訳して基本補題を再利用する。
そのための薄い helper をここにまとめて置く。

```lean
public def translatedTpDegree (toProductFree : α → Tp) (A : α) : Nat :=
  tp_degree (toProductFree A)
```

```lean
public def translatedListDegree (toProductFree : α → Tp) (Γ : List α) : Nat :=
  list_degree (Γ.map toProductFree)
```

```lean
@[grind .] public lemma translatedListDegree_traversible (toProductFree : α → Tp) :
    translatedListDegree toProductFree (Γ ++ Δ) =
      translatedListDegree toProductFree Γ + translatedListDegree toProductFree Δ := by
  simp [translatedListDegree, list_degree_traversible]
```

```lean
/-- Transport atomicity through a public translation.

Its body is exposed because public fragment proofs reduce it after a case
split on the translated formula. -/
@[expose] public def translatedIsAtom (toProductFree : α → Tp) (A : α) : Prop :=
  is_atom (toProductFree A)
```

```lean
@[grind .] public lemma translatedNonemptyAppend (h : Γ ≠ []) : Δ ++ Γ ++ Λ ≠ [] := by
  exact nonempty_append h
```

```lean
end Mathling.Lambek.ProductFree
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
