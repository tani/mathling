    module

    public import Mathling.Lambek.Lexicon
    public import Mathling.Lambek.ProductFree.Fragments.Shallow.Core
    public import Mathling.Lambek.ProductFree.Fragments.Left.Shallow.Core
    public import Mathling.Lambek.ProductFree.Fragments.Right.Shallow.Core
    public import Mathling.Grammar.Regular.Linear
    public import Mathling.Grammar.Regular.Left
    public import Mathling.Grammar.Regular.Right

    import LiterateLean
    open scoped LiterateLean


# Shallow Lambek 文法と具体的な文法変換

このモジュールは、実際の語彙を持つ Lambek 文法を定義する。語が文法言語に属するとは、
各終端記号へ語彙範疇を割り当て、その範疇列から既存の shallow シーケント計算で
指定された開始原子を導出できることを意味する。

順方向変換は意味論的なラッパーではなく、各語彙項目から生成規則を組み立てる具体的な関数である。

```mermaid
flowchart LR
    Word --> Lexicon
    Lexicon --> Categories
    Categories --> Sequent
    Lexicon --> Rules
    Rules --> LinearGrammar
```

## 一般 shallow 文法

```lean
namespace Mathling.Lambek.ProductFree.Shallow

public structure Grammar (T : Type*) where
  lexicon : Mathling.Lambek.Lexicon T Tp
  start : String
```

以降の操作と定理は `Grammar` 名前空間にまとめ、文法値を受け取る API として公開する。

```lean
namespace Grammar

variable {T : Type*}
```

受理判定では各終端記号に範疇を一つずつ選び、その範疇列を既存の shallow Sequent へ渡す。

```lean
/- Exposed because public language and decision theorems reduce lexical acceptance. -/
@[expose] public def Accepts (g : Grammar T) (w : List T) : Prop :=
  ∃ Γ, g.lexicon.Categorizes w Γ ∧ Sequent Γ (.atom g.start)
```

```lean
/- Exposed because public class and conversion theorems compare this set extensionally. -/
@[expose] public def language (g : Grammar T) : Language T :=
  {w | g.Accepts w}
```

空語からは Lambek 計算が要求する非空の前提列を構成できない。

```lean
@[important, grind .] public theorem empty_not_mem (g : Grammar T) :
    [] ∉ g.language := by
  rintro ⟨Γ, hcat, hseq⟩
  cases hcat
  exact Mathling.Lambek.ProductFree.nonempty_premises hseq rfl
```

原子語彙は終端規則へ、右除法語彙は右線形規則へ、左除法語彙は左線形規則へ変換する。

```lean
public abbrev lexicalRule (entry : T × Tp) : ContextFreeRule T String :=
  match entry with
  | (a, .atom A) =>
      { input := A, output := [Symbol.terminal a] }
  | (a, .rdiv B A) =>
      { input := B, output := [Symbol.terminal a, Symbol.nonterminal A] }
  | (a, .ldiv A B) =>
      { input := B, output := [Symbol.nonterminal A, Symbol.terminal a] }
```

```lean
/-- 各 shallow 語彙項目を対応する具体的な線形生成規則へ変換する。 -/
public noncomputable abbrev toLinearGrammar (g : Grammar T) :
    Mathling.Grammar.LinearGrammar T := by
  classical
  exact
    { cfg :=
        { NT := String
          initial := g.start
          rules := (g.lexicon.entries.map lexicalRule).toFinset }
      linear := by
        intro r hr
        rw [List.mem_toFinset] at hr
        obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hr
        rcases entry with ⟨a, A⟩
        cases A <;>
          simp [lexicalRule, Mathling.Grammar.ContextFreeRule.IsLinear,
            Mathling.Grammar.ContextFreeRule.nonterminalCount,
            Mathling.Grammar.symbolIsNonterminal] }
```

```lean
end Grammar
end Mathling.Lambek.ProductFree.Shallow
```

一般 shallow の語彙規則が表す生成 spine を明示する。基底規則は原子語彙を一語生成し、右除法は左端へ、左除法は右端へ一語を追加する。

```math
\begin{aligned}
a:A &\mapsto A \to a,\\
a:B/A &\mapsto B \to aA,\\
a:A\backslash B &\mapsto B \to Aa.
\end{aligned}
```

```lean
namespace Mathling.Lambek.ProductFree.Shallow
namespace Grammar

@[grind cases] public inductive Generates (g : Grammar T) : String → List T → Prop
  | atom {a A} (entry : (a, Tp.atom A) ∈ g.lexicon.entries) :
      Generates g A [a]
  | rdiv {a A B w}
      (entry : (a, Tp.rdiv B A) ∈ g.lexicon.entries)
      (child : Generates g A w) :
      Generates g B (a :: w)
  | ldiv {a A B w}
      (entry : (a, Tp.ldiv A B) ∈ g.lexicon.entries)
      (child : Generates g A w) :
      Generates g B (w ++ [a])
```

spine から Lambek 導出を作る向きは、各 constructor を対応する左規則へ写す。ここでは語列と型列を同時に組み立てるため、語彙割当も証人として返す。

```lean
@[grind .] private theorem categorizes_append_singleton
    {g : Grammar T} {w : List T} {Γ : List Tp} {a : T} {A : Tp}
    (h : g.lexicon.Categorizes w Γ)
    (entry : (a, A) ∈ g.lexicon.entries) :
    g.lexicon.Categorizes (w ++ [a]) (Γ ++ [A]) := by
  induction h with
  | nil =>
      simpa using
        (Mathling.Lambek.Lexicon.Categorizes.cons entry
          Mathling.Lambek.Lexicon.Categorizes.nil)
  | @cons a' A' w' Γ' head tail ih =>
      simpa [List.append_assoc] using
        (Mathling.Lambek.Lexicon.Categorizes.cons head ih)

```

生成 spine の各 constructor を対応する Lambek 左規則へ写し、語彙割当とシーケント導出を同時に構成する。

```lean
@[grind .] public theorem accepts_of_generates
    {g : Grammar T} {A : String} {w : List T}
    (h : g.Generates A w) :
    ∃ Γ, g.lexicon.Categorizes w Γ ∧ Sequent Γ (.atom A) := by
  induction h with
  | atom entry =>
      exact ⟨[.atom _],
        Mathling.Lambek.Lexicon.Categorizes.cons entry
          Mathling.Lambek.Lexicon.Categorizes.nil,
        Sequent.ax⟩
  | @rdiv a A B w entry child ih =>
      obtain ⟨Γ, hcat, hseq⟩ := ih
      refine ⟨.rdiv B A :: Γ,
        Mathling.Lambek.Lexicon.Categorizes.cons entry hcat, ?_⟩
      simpa using
        (_root_.Mathling.Lambek.ProductFree.Shallow.Sequent.rdiv_l (Γ := []) (Λ := []) hseq
          (Sequent.ax : Sequent [.atom B] (.atom B)))
  | @ldiv a A B w entry child ih =>
      obtain ⟨Γ, hcat, hseq⟩ := ih
      refine ⟨Γ ++ [.ldiv A B],
        categorizes_append_singleton hcat entry, ?_⟩
      simpa using
        (_root_.Mathling.Lambek.ProductFree.Shallow.Sequent.ldiv_l (Γ := []) (Λ := []) hseq
          (Sequent.ax : Sequent [.atom B] (.atom B)))
```

逆向きでは、各前提を一つの終端語断片として解釈する。語彙由来の前提は一語を担い、既に導出済みの原子前提は一つの生成 spine 全体を担う。左規則は引数側の断片を主辞へ吸収して原子資源へ置換するため、導出木に関する帰納法がそのまま生成 spine を復元する。

```lean
private def Item (g : Grammar T)
    (w : List T) (A : Mathling.Lambek.ProductFree.Tp) : Prop :=
  (∃ a shallow, w = [a] ∧ A = shallow.toProductFree ∧
    (a, shallow) ∈ g.lexicon.entries) ∨
  (∃ name, A = Mathling.Lambek.ProductFree.Tp.atom name ∧
    g.Generates name w)

```

各前提が担当する語列を並べる `Resources` を導入する。型文脈と語順を同時に保存するため、非可換な Lambek 導出の左右を失わずに扱える。

```lean
private inductive Resources (g : Grammar T) :
    List Mathling.Lambek.ProductFree.Tp → List T → Prop
  | nil : Resources g [] []
  | cons {A Γ u v}
      (head : Item g u A)
      (tail : Resources g Γ v) :
      Resources g (A :: Γ) (u ++ v)

```

文脈を連結すると、対応する語列も同じ順序で連結される。この合成則は、部分導出を主導出へ戻すときに使う。

```lean
@[grind .] private theorem Resources.append
    {g : Grammar T} {Γ Δ : List Mathling.Lambek.ProductFree.Tp}
    {u v : List T}
    (left : Resources g Γ u) (right : Resources g Δ v) :
    Resources g (Γ ++ Δ) (u ++ v) := by
  induction left with
  | nil => simpa using right
  | @cons A Γ x y head tail ih =>
      simpa [List.append_assoc] using Resources.cons head ih

```

逆に、連結された文脈の資源証明は境界位置で二分できる。規則反転ではこの補題を使い、主式と左右の文脈を順番どおりに取り出す。

```lean
@[grind .] private theorem Resources.split
    {g : Grammar T} {Γ Δ : List Mathling.Lambek.ProductFree.Tp}
    {w : List T}
    (h : Resources g (Γ ++ Δ) w) :
    ∃ u v, w = u ++ v ∧ Resources g Γ u ∧ Resources g Δ v := by
  induction Γ generalizing w with
  | nil =>
      exact ⟨[], w, by simp, Resources.nil, by simpa using h⟩
  | cons A Γ ih =>
      cases h with
      | @cons _ _ x y head tail =>
          obtain ⟨u, v, rfl, hΓ, hΔ⟩ := ih tail
          exact ⟨x ++ u, v, by simp [List.append_assoc],
            Resources.cons head hΓ, hΔ⟩

```

一要素の文脈からは対応する `Item` を直接回収できる。これにより、主式が語彙項目か、構成済みの生成 spine かを判別する。

```lean
@[grind .] private theorem Resources.singleton
    {g : Grammar T} {A : Mathling.Lambek.ProductFree.Tp} {w : List T}
    (h : Resources g [A] w) :
    Item g w A := by
  cases h with
  | @cons _ _ u v head tail =>
      cases tail
      simpa using head

```

通常の語彙割当は、各語を一語の `Item` とみなすことで `Resources` へ持ち上がる。ここが受理意味論から規則反転用表現への入口である。

```lean
@[grind .] private theorem Resources.ofCategorizes
    {g : Grammar T} {w : List T} {Γ : List Tp}
    (h : g.lexicon.Categorizes w Γ) :
    Resources g (ctxToProductFree Γ) w := by
  induction h with
  | nil => exact Resources.nil
  | @cons a A w Γ entry tail ih =>
      simpa [ctxToProductFree] using
        (Resources.cons (Or.inl ⟨a, A, rfl, rfl, entry⟩) ih)

```

準備した資源分解を使い、product-free Lambek 導出を帰納的に反転する。除法の左規則では引数側の生成を主式へ吸収し、対応する spine constructor を復元する。

```lean
@[grind .] private theorem generates_of_resources
    {g : Grammar T}
    {Γ : List Mathling.Lambek.ProductFree.Tp}
    {C : Mathling.Lambek.ProductFree.Tp}
    (derivation : Mathling.Lambek.ProductFree.Sequent Γ C) :
    ∀ {A w}, C = Mathling.Lambek.ProductFree.Tp.atom A →
      Resources g Γ w → g.Generates A w := by
  induction derivation with
  | @ax C =>
      intro A w hC resources
      subst C
      have item := Resources.singleton resources
      rcases item with
        ⟨a, shallow, rfl, htype, entry⟩ |
        ⟨name, htype, generation⟩
      · cases shallow <;> simp_all [Tp.toProductFree]
        exact Generates.atom entry
      · simp only [Mathling.Lambek.ProductFree.Tp.atom.injEq] at htype
        subst name
        exact generation
  | @rdiv_r Γ X Y hne premise ih =>
      intro A w hC
      cases hC
  | @ldiv_r Γ X Y hne premise ih =>
      intro A w hC
      cases hC
  | @rdiv_l Δ X Γ B Λ C argument main ihArgument ihMain =>
      intro A w hC resources
      have resources' :
          Resources g (Γ ++ ([B ⧸ X] ++ Δ ++ Λ)) w := by
        simpa [List.append_assoc] using resources
      obtain ⟨wΓ, wrest, rfl, resourcesΓ, resourcesRest⟩ :=
        Resources.split resources'
      obtain ⟨wPrincipal, wrest', rfl, resourcesPrincipal, resourcesRest'⟩ :=
        Resources.split (Γ := [B ⧸ X]) (Δ := Δ ++ Λ) resourcesRest
      obtain ⟨wΔ, wΛ, rfl, resourcesΔ, resourcesΛ⟩ :=
        Resources.split (Γ := Δ) (Δ := Λ) resourcesRest'
      have principal := Resources.singleton resourcesPrincipal
      rcases principal with
        ⟨a, shallow, rfl, htype, entry⟩ |
        ⟨name, htype, generation⟩
      · cases shallow with
        | atom name =>
            simp [Tp.toProductFree] at htype
        | ldiv left result =>
            simp [Tp.toProductFree] at htype
        | rdiv result arg =>
            simp only [Tp.toProductFree,
              Mathling.Lambek.ProductFree.Tp.rdiv.injEq] at htype
            obtain ⟨rfl, rfl⟩ := htype
            have child := ihArgument rfl resourcesΔ
            have combined : Item g ([a] ++ wΔ)
                (Mathling.Lambek.ProductFree.Tp.atom result) :=
              Or.inr ⟨result, rfl, Generates.rdiv entry child⟩
            have singleton :
                Resources g [Mathling.Lambek.ProductFree.Tp.atom result]
                  ([a] ++ wΔ) := by
              simpa using (Resources.cons
                (u := [a] ++ wΔ) (v := []) combined Resources.nil)
            have replaced :
                Resources g
                  (Γ ++ [Mathling.Lambek.ProductFree.Tp.atom result] ++ Λ)
                  (wΓ ++ ([a] ++ wΔ) ++ wΛ) :=
              Resources.append
                (Resources.append resourcesΓ singleton) resourcesΛ
            simpa [List.append_assoc] using ihMain hC replaced
      · cases htype
  | @ldiv_l Δ X Γ B Λ C argument main ihArgument ihMain =>
      intro A w hC resources
      have resources' :
          Resources g (Γ ++ (Δ ++ [X ⧹ B] ++ Λ)) w := by
        simpa [List.append_assoc] using resources
      obtain ⟨wΓ, wrest, rfl, resourcesΓ, resourcesRest⟩ :=
        Resources.split resources'
      have resourcesRest'' :
          Resources g (Δ ++ ([X ⧹ B] ++ Λ)) wrest := by
        simpa [List.append_assoc] using resourcesRest
      obtain ⟨wΔ, wrest', rfl, resourcesΔ, resourcesRest'⟩ :=
        Resources.split resourcesRest''
      obtain ⟨wPrincipal, wΛ, rfl, resourcesPrincipal, resourcesΛ⟩ :=
        Resources.split (Γ := [X ⧹ B]) (Δ := Λ) resourcesRest'
      have principal := Resources.singleton resourcesPrincipal
      rcases principal with
        ⟨a, shallow, rfl, htype, entry⟩ |
        ⟨name, htype, generation⟩
      · cases shallow with
        | atom name =>
            simp [Tp.toProductFree] at htype
        | rdiv result arg =>
            simp [Tp.toProductFree] at htype
        | ldiv arg result =>
            simp only [Tp.toProductFree,
              Mathling.Lambek.ProductFree.Tp.ldiv.injEq] at htype
            obtain ⟨rfl, rfl⟩ := htype
            have child := ihArgument rfl resourcesΔ
            have combined : Item g (wΔ ++ [a])
                (Mathling.Lambek.ProductFree.Tp.atom result) :=
              Or.inr ⟨result, rfl, Generates.ldiv entry child⟩
            have singleton :
                Resources g [Mathling.Lambek.ProductFree.Tp.atom result]
                  (wΔ ++ [a]) := by
              simpa using (Resources.cons
                (u := wΔ ++ [a]) (v := []) combined Resources.nil)
            have replaced :
                Resources g
                  (Γ ++ [Mathling.Lambek.ProductFree.Tp.atom result] ++ Λ)
                  (wΓ ++ (wΔ ++ [a]) ++ wΛ) :=
              Resources.append
                (Resources.append resourcesΓ singleton) resourcesΛ
            simpa [List.append_assoc] using ihMain hC replaced
      · cases htype

```

逆向きでは受理証明から開始原子の生成 spine を復元する。一般版は資源反転を直接使い、片側版は一般 shallow の完全性を経由する。

```lean
@[important, grind .] public theorem generates_of_accepts
    {g : Grammar T} {w : List T} (h : g.Accepts w) :
    g.Generates g.start w := by
  obtain ⟨Γ, hcat, hseq⟩ := h
  exact generates_of_resources hseq rfl (Resources.ofCategorizes hcat)

```

往路と復路を合わせると、Lambek 導出による受理と生成 spine が同値になる。この中間契約を次の文法変換で利用する。

```lean
@[important, grind =] public theorem accepts_iff_generates
    {g : Grammar T} {w : List T} :
    g.Accepts w ↔ g.Generates g.start w := by
  constructor
  · exact generates_of_accepts
  · exact accepts_of_generates
```

最後に、生成 spine と実際に構成した LinearGrammar の生成木を規則ごとに対応させる。規則集合の所属証明から元の語彙項目を復元するため、逆向きも定義上の投影ではなく規則形の反転になっている。

```lean
/-- A terminal-only word cannot contain an embedded nonterminal. -/
@[grind .] public theorem terminalSymbols_ne_terminalContext
    (word pre suffix : List T) (B : N) :
    Mathling.Grammar.terminalSymbols word ≠
      Mathling.Grammar.terminalSymbols pre ++
        [Symbol.nonterminal B] ++
        Mathling.Grammar.terminalSymbols suffix := by
  intro h
  induction pre generalizing word with
  | nil =>
      cases word <;> simp [Mathling.Grammar.terminalSymbols] at h
  | cons p pre ih =>
      cases word with
      | nil =>
          simp [Mathling.Grammar.terminalSymbols] at h
      | cons x word =>
          simp only [Mathling.Grammar.terminalSymbols_cons,
            List.cons_append, List.cons.injEq] at h
          exact ih word h.2

```

branch 規則同士の出力が等しい場合、唯一の非終端記号の位置も一致する。前置語、非終端記号、後置語を一意に回収する。

```lean
/-- The unique nonterminal splits two equal linear-rule outputs at the same point. -/
@[grind .] public theorem terminalContext_injective
    {pre₁ pre₂ suffix₁ suffix₂ : List T} {A B : N}
    (h : Mathling.Grammar.terminalSymbols pre₁ ++
          [Symbol.nonterminal A] ++
          Mathling.Grammar.terminalSymbols suffix₁ =
        Mathling.Grammar.terminalSymbols pre₂ ++
          [Symbol.nonterminal B] ++
          Mathling.Grammar.terminalSymbols suffix₂) :
    pre₁ = pre₂ ∧ A = B ∧ suffix₁ = suffix₂ := by
  induction pre₁ generalizing pre₂ with
  | nil =>
      cases pre₂ with
      | nil =>
          simp only [Mathling.Grammar.terminalSymbols_nil,
            List.nil_append, List.cons_append, List.cons.injEq] at h
          have hA : A = B := Symbol.nonterminal.inj h.1
          exact ⟨rfl, hA,
            Mathling.Grammar.ContextFreeGrammar.terminalSymbols_injective h.2⟩
      | cons b pre₂ =>
          simp [Mathling.Grammar.terminalSymbols] at h
  | cons a pre₁ ih =>
      cases pre₂ with
      | nil =>
          simp [Mathling.Grammar.terminalSymbols] at h
      | cons b pre₂ =>
          simp only [Mathling.Grammar.terminalSymbols_cons,
            List.cons_append, List.cons.injEq] at h
          obtain ⟨hhead, htail⟩ := h
          have hab : a = b := Symbol.terminal.inj hhead
          subst b
          obtain ⟨rfl, hA, hsuffix⟩ := ih htail
          exact ⟨rfl, hA, hsuffix⟩

```

規則出力の形を反転し、生成 spine と具体的な線形生成木を双方向に変換する。leaf は原子語彙に、branch は対応する除法語彙に一致する。

```lean
@[important, grind =] public theorem generates_iff_linearGenerates
    {g : Grammar T} {A : String} {w : List T} :
    g.Generates A w ↔
      Mathling.Grammar.LinearGrammar.LinearGenerates g.toLinearGrammar A w := by
  classical
  constructor
  · intro h
    induction h with
    | @atom a A entry =>
        apply Mathling.Grammar.LinearGrammar.LinearGenerates.leaf
          (g := g.toLinearGrammar)
          (r := lexicalRule (a, .atom A))
          (word := [a])
        · rw [List.mem_toFinset]
          exact List.mem_map_of_mem (f := lexicalRule) entry
        · rfl
    | @rdiv a A B w entry child ih =>
        simpa [Mathling.Grammar.terminalSymbols] using
          (Mathling.Grammar.LinearGrammar.LinearGenerates.branch
            (g := g.toLinearGrammar)
            (r := lexicalRule (a, .rdiv B A))
            (pre := [a]) (suffix := []) (middle := w) (B := A)
            (by
              rw [List.mem_toFinset]
              exact List.mem_map_of_mem (f := lexicalRule) entry)
            (by rfl)
            ih)
    | @ldiv a A B w entry child ih =>
        simpa [Mathling.Grammar.terminalSymbols] using
          (Mathling.Grammar.LinearGrammar.LinearGenerates.branch
            (g := g.toLinearGrammar)
            (r := lexicalRule (a, .ldiv A B))
            (pre := []) (suffix := [a]) (middle := w) (B := A)
            (by
              rw [List.mem_toFinset]
              exact List.mem_map_of_mem (f := lexicalRule) entry)
            (by rfl)
            ih)
  · intro h
    refine Mathling.Grammar.LinearGrammar.LinearGenerates.rec
      (motive := fun A word _ => g.Generates A word) ?_ ?_ h
    · intro r word hr hout
      rw [show g.toLinearGrammar.cfg.rules =
        (g.lexicon.entries.map lexicalRule).toFinset by rfl] at hr
      rw [List.mem_toFinset] at hr
      obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hr
      rcases entry with ⟨a, category⟩
      cases category with
      | atom A =>
          change g.Generates A word
          change Mathling.Grammar.terminalSymbols [a] =
            Mathling.Grammar.terminalSymbols word at hout
          have hword := Mathling.Grammar.ContextFreeGrammar.terminalSymbols_injective hout
          subst word
          exact Generates.atom hentry
      | ldiv A B =>
          exfalso
          apply terminalSymbols_ne_terminalContext word [] [a] A
          simpa [Mathling.Grammar.terminalSymbols] using hout.symm
      | rdiv B A =>
          exfalso
          apply terminalSymbols_ne_terminalContext word [a] [] A
          simpa [Mathling.Grammar.terminalSymbols] using hout.symm
    · intro r pre suffix middle B hr hout child ih
      rw [show g.toLinearGrammar.cfg.rules =
        (g.lexicon.entries.map lexicalRule).toFinset by rfl] at hr
      rw [List.mem_toFinset] at hr
      obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hr
      rcases entry with ⟨a, category⟩
      cases category with
      | atom A =>
          exfalso
          apply terminalSymbols_ne_terminalContext [a] pre suffix B
          simpa [Mathling.Grammar.terminalSymbols] using hout
      | ldiv A C =>
          change Mathling.Grammar.terminalSymbols [] ++
              [Symbol.nonterminal A] ++
              Mathling.Grammar.terminalSymbols [a] =
            Mathling.Grammar.terminalSymbols pre ++
              [Symbol.nonterminal B] ++
              Mathling.Grammar.terminalSymbols suffix at hout
          obtain ⟨rfl, rfl, rfl⟩ := terminalContext_injective hout
          simpa using Generates.ldiv hentry ih
      | rdiv C A =>
          change Mathling.Grammar.terminalSymbols [a] ++
              [Symbol.nonterminal A] ++
              Mathling.Grammar.terminalSymbols [] =
            Mathling.Grammar.terminalSymbols pre ++
              [Symbol.nonterminal B] ++
              Mathling.Grammar.terminalSymbols suffix at hout
          obtain ⟨rfl, rfl, rfl⟩ := terminalContext_injective hout
          simpa using Generates.rdiv hentry ih

```

開始原子で生成同値を使い、線形文法の生成判定と `Accepts` を接続する。公開変換の最終契約はこの言語等式である。

```lean
@[important, grind =, simp] public theorem toLinearGrammar_language
    (g : Grammar T) :
    g.toLinearGrammar.language = g.language := by
  ext w
  rw [← Mathling.Grammar.LinearGrammar.linearGenerates_iff]
  exact g.generates_iff_linearGenerates.symm.trans
    g.accepts_iff_generates.symm

end Grammar
end Mathling.Lambek.ProductFree.Shallow
```

## Left.Shallow 文法

```lean
namespace Mathling.Lambek.ProductFree.Left.Shallow

public structure Grammar (T : Type*) where
  lexicon : Mathling.Lambek.Lexicon T Tp
  start : String
```

以降の操作と定理は `Grammar` 名前空間にまとめ、文法値を受け取る API として公開する。

```lean
namespace Grammar

variable {T : Type*}
```

```lean
/- Exposed because public language theorems reduce lexical acceptance. -/
@[expose] public def Accepts (g : Grammar T) (w : List T) : Prop :=
  ∃ Γ, g.lexicon.Categorizes w Γ ∧ Sequent Γ (.atom g.start)
```

```lean
/- Exposed because public conversion theorems compare this set extensionally. -/
@[expose] public def language (g : Grammar T) : Language T :=
  {w | g.Accepts w}
```

```lean
@[important, grind .] public theorem empty_not_mem (g : Grammar T) :
    [] ∉ g.language := by
  rintro ⟨Γ, hcat, hseq⟩
  cases hcat
  exact Mathling.Lambek.ProductFree.nonempty_premises hseq rfl
```

```lean
public abbrev lexicalRule (entry : T × Tp) : ContextFreeRule T String :=
  match entry with
  | (a, .atom A) =>
      { input := A, output := [Symbol.terminal a] }
  | (a, .ldiv A B) =>
      { input := B, output := [Symbol.nonterminal A, Symbol.terminal a] }
```

```lean
/-- 各 left-shallow 語彙項目を対応する具体的な左線形生成規則へ変換する。 -/
public noncomputable abbrev toLeftLinearGrammar (g : Grammar T) :
    Mathling.Grammar.LeftLinearGrammar T := by
  classical
  exact
    { cfg :=
        { NT := String
          initial := g.start
          rules := (g.lexicon.entries.map lexicalRule).toFinset }
      leftLinear := by
        intro r hr
        rw [List.mem_toFinset] at hr
        obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hr
        rcases entry with ⟨a, A⟩
        cases A <;>
          simp [lexicalRule, Mathling.Grammar.ContextFreeRule.IsLeftLinear] }
```

```lean
end Grammar
end Mathling.Lambek.ProductFree.Left.Shallow
```

## Right.Shallow 文法

```lean
namespace Mathling.Lambek.ProductFree.Right.Shallow

public structure Grammar (T : Type*) where
  lexicon : Mathling.Lambek.Lexicon T Tp
  start : String
```

以降の操作と定理は `Grammar` 名前空間にまとめ、文法値を受け取る API として公開する。

```lean
namespace Grammar

variable {T : Type*}
```

```lean
/- Exposed because public language theorems reduce lexical acceptance. -/
@[expose] public def Accepts (g : Grammar T) (w : List T) : Prop :=
  ∃ Γ, g.lexicon.Categorizes w Γ ∧ Sequent Γ (.atom g.start)
```

```lean
/- Exposed because public conversion theorems compare this set extensionally. -/
@[expose] public def language (g : Grammar T) : Language T :=
  {w | g.Accepts w}
```

```lean
@[important, grind .] public theorem empty_not_mem (g : Grammar T) :
    [] ∉ g.language := by
  rintro ⟨Γ, hcat, hseq⟩
  cases hcat
  exact Mathling.Lambek.ProductFree.nonempty_premises hseq rfl
```

```lean
public abbrev lexicalRule (entry : T × Tp) : ContextFreeRule T String :=
  match entry with
  | (a, .atom A) =>
      { input := A, output := [Symbol.terminal a] }
  | (a, .rdiv B A) =>
      { input := B, output := [Symbol.terminal a, Symbol.nonterminal A] }
```

```lean
/-- 各 right-shallow 語彙項目を対応する具体的な右線形生成規則へ変換する。 -/
public noncomputable abbrev toRightLinearGrammar (g : Grammar T) :
    Mathling.Grammar.RightLinearGrammar T := by
  classical
  exact
    { cfg :=
        { NT := String
          initial := g.start
          rules := (g.lexicon.entries.map lexicalRule).toFinset }
      rightLinear := by
        intro r hr
        rw [List.mem_toFinset] at hr
        obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hr
        rcases entry with ⟨a, A⟩
        cases A <;>
          simp [lexicalRule, Mathling.Grammar.ContextFreeRule.IsRightLinear] }
```

```lean
end Grammar
end Mathling.Lambek.ProductFree.Right.Shallow
```

## 左右 shallow の対応

片側 fragment は一般 shallow へ忠実に埋め込める。左 fragment は左除法だけを、右 fragment は右除法だけを語彙に許すため、対応する spine も一方向へしか伸びない。

### Left.Shallow と左線形生成

```lean
namespace Mathling.Lambek.ProductFree.Left.Shallow
namespace Grammar

@[grind cases] public inductive Generates (g : Grammar T) : String → List T → Prop
  | atom {a A} (entry : (a, Tp.atom A) ∈ g.lexicon.entries) :
      Generates g A [a]
  | ldiv {a A B w}
      (entry : (a, Tp.ldiv A B) ∈ g.lexicon.entries)
      (child : Generates g A w) :
      Generates g B (w ++ [a])

```

片側 fragment の型を一般 shallow 型へ埋め込む。許可された原子と一方向の除法だけを、その構造を変えずに移す。

```lean
private def Tp.toGeneral : Tp →
    Mathling.Lambek.ProductFree.Shallow.Tp
  | .atom A => .atom A
  | .ldiv A B => .ldiv A B

```

型の埋め込みを語彙全体へ写し、同じ開始原子を持つ一般 shallow 文法を作る。この内部文法を一般版の完全性の再利用に使う。

```lean
private def toGeneral (g : Grammar T) :
    Mathling.Lambek.ProductFree.Shallow.Grammar T :=
  { lexicon :=
      { entries := g.lexicon.entries.map fun entry =>
          (entry.1, Tp.toGeneral entry.2) }
    start := g.start }

```

個々の語彙割当は型列への `map` と整合するため、元の分類証明を一般文法の分類証明へ構造的に移せる。

```lean
@[grind .] private theorem categorizes_toGeneral
    {g : Grammar T} {w : List T} {Γ : List Tp}
    (h : g.lexicon.Categorizes w Γ) :
    g.toGeneral.lexicon.Categorizes w (Γ.map Tp.toGeneral) := by
  induction h with
  | nil => exact Mathling.Lambek.Lexicon.Categorizes.nil
  | @cons a A w Γ entry tail ih =>
      apply Mathling.Lambek.Lexicon.Categorizes.cons
        (tail := ih)
      simpa [toGeneral] using
        List.mem_map_of_mem (f := fun entry => (entry.1, Tp.toGeneral entry.2)) entry

```

型埋め込みは product-free 表現を変えない。したがって、分類済みの型列に対する同じ Lambek 導出を一般文法側でも利用できる。

```lean
@[grind .] private theorem toGeneral_accepts
    {g : Grammar T} {w : List T} (h : g.Accepts w) :
    g.toGeneral.Accepts w := by
  obtain ⟨Γ, hcat, hseq⟩ := h
  refine ⟨Γ.map Tp.toGeneral, categorizes_toGeneral hcat, ?_⟩
  have htype (A : Tp) :
      Mathling.Lambek.ProductFree.Shallow.Tp.toProductFree
          (Tp.toGeneral A) = Tp.toProductFree A := by
    cases A <;> rfl
  have hctx_all : ∀ Δ : List Tp,
      List.map
          (Mathling.Lambek.ProductFree.Shallow.Tp.toProductFree ∘
            Tp.toGeneral) Δ =
        List.map Tp.toProductFree Δ := by
    intro Δ
    induction Δ with
    | nil => rfl
    | cons A Δ ih =>
        simp only [List.map_cons, Function.comp_apply]
        rw [htype, ih]
  have hctx := hctx_all Γ
  simp only [toGeneral,
    Mathling.Lambek.ProductFree.Shallow.Sequent,
    Mathling.Lambek.ProductFree.Shallow.ctxToProductFree,
    List.map_map]
  rw [hctx]
  simp only [Mathling.Lambek.ProductFree.Shallow.Tp.toProductFree]
  simpa only [Sequent, ctxToProductFree, Tp.toProductFree] using hseq

```

片側の生成 spine は constructor ごとに一般版へ埋め込める。この往路は、片側規則が一般規則の制限になっていることを明示する。

```lean
@[grind .] private theorem generates_toGeneral
    {g : Grammar T} {A : String} {w : List T}
    (h : g.Generates A w) :
    g.toGeneral.Generates A w := by
  induction h with
  | atom entry =>
      apply Mathling.Lambek.ProductFree.Shallow.Grammar.Generates.atom
      simpa [toGeneral, Tp.toGeneral] using
        List.mem_map_of_mem (f := fun entry => (entry.1, Tp.toGeneral entry.2)) entry
  | ldiv entry child ih =>
      apply Mathling.Lambek.ProductFree.Shallow.Grammar.Generates.ldiv
        (child := ih)
      simpa [toGeneral, Tp.toGeneral] using
        List.mem_map_of_mem (f := fun entry => (entry.1, Tp.toGeneral entry.2)) entry

```

一般版から戻すときは、埋め込み語彙に反対向きの除法項目が存在しないことを規則形から判定する。残る constructor だけを片側 fragment へ戻す。

```lean
@[grind .] private theorem generates_ofGeneral
    {g : Grammar T} {A : String} {w : List T}
    (h : g.toGeneral.Generates A w) :
    g.Generates A w := by
  induction h with
  | @atom a A entry =>
      change (a, Mathling.Lambek.ProductFree.Shallow.Tp.atom A) ∈
        g.lexicon.entries.map (fun entry =>
          (entry.1, Tp.toGeneral entry.2)) at entry
      obtain ⟨source, hsource, heq⟩ := List.mem_map.mp entry
      rcases source with ⟨a', category⟩
      cases category <;> simp_all [Tp.toGeneral]
      exact Generates.atom hsource
  | @rdiv a A B w entry child ih =>
      change (a, Mathling.Lambek.ProductFree.Shallow.Tp.rdiv B A) ∈
        g.lexicon.entries.map (fun entry =>
          (entry.1, Tp.toGeneral entry.2)) at entry
      obtain ⟨source, hsource, heq⟩ := List.mem_map.mp entry
      rcases source with ⟨a', category⟩
      cases category <;> simp_all [Tp.toGeneral]
  | @ldiv a A B w entry child ih =>
      change (a, Mathling.Lambek.ProductFree.Shallow.Tp.ldiv A B) ∈
        g.lexicon.entries.map (fun entry =>
          (entry.1, Tp.toGeneral entry.2)) at entry
      obtain ⟨source, hsource, heq⟩ := List.mem_map.mp entry
      rcases source with ⟨a', category⟩
      cases category <;> simp_all [Tp.toGeneral]
      simpa using Generates.ldiv hsource ih

```

左除法は語を spine の右端へ追加するため、語彙割当にも同じ右端追加を反映する。

```lean
@[grind .] private theorem categorizes_append_singleton
    {g : Grammar T} {w : List T} {Γ : List Tp} {a : T} {A : Tp}
    (h : g.lexicon.Categorizes w Γ)
    (entry : (a, A) ∈ g.lexicon.entries) :
    g.lexicon.Categorizes (w ++ [a]) (Γ ++ [A]) := by
  induction h with
  | nil =>
      simpa using
        (Mathling.Lambek.Lexicon.Categorizes.cons entry
          Mathling.Lambek.Lexicon.Categorizes.nil)
  | @cons a' A' w' Γ' head tail ih =>
      simpa [List.append_assoc] using
        (Mathling.Lambek.Lexicon.Categorizes.cons head ih)

@[important, grind .] public theorem accepts_of_generates
    {g : Grammar T} {A : String} {w : List T}
    (h : g.Generates A w) :
    ∃ Γ, g.lexicon.Categorizes w Γ ∧ Sequent Γ (.atom A) := by
  induction h with
  | atom entry =>
      exact ⟨[.atom _],
        Mathling.Lambek.Lexicon.Categorizes.cons entry
          Mathling.Lambek.Lexicon.Categorizes.nil,
        Sequent.ax⟩
  | @ldiv a A B w entry child ih =>
      obtain ⟨Γ, hcat, hseq⟩ := ih
      have hcat' :
          g.lexicon.Categorizes (w ++ [a]) (Γ ++ [.ldiv A B]) :=
        categorizes_append_singleton hcat entry
      refine ⟨Γ ++ [.ldiv A B], hcat', ?_⟩
      simpa using
        (_root_.Mathling.Lambek.ProductFree.Left.Shallow.Sequent.ldiv_l (Γ := []) (Λ := []) hseq
          (Sequent.ax : Sequent [.atom B] (.atom B)))

```

逆向きでは受理証明から開始原子の生成 spine を復元する。一般版は資源反転を直接使い、片側版は一般 shallow の完全性を経由する。

```lean
@[important, grind .] public theorem generates_of_accepts
    {g : Grammar T} {w : List T} (h : g.Accepts w) :
    g.Generates g.start w :=
  generates_ofGeneral
    (Mathling.Lambek.ProductFree.Shallow.Grammar.generates_of_accepts
      (toGeneral_accepts h))

```

往路と復路を合わせると、Lambek 導出による受理と生成 spine が同値になる。この中間契約を次の文法変換で利用する。

```lean
@[important, grind =] public theorem accepts_iff_generates
    {g : Grammar T} {w : List T} :
    g.Accepts w ↔ g.Generates g.start w := by
  constructor
  · exact generates_of_accepts
  · exact accepts_of_generates
```

左向き spine と、実際の左線形規則集合からなる生成木を規則ごとに往復する。

```lean
@[important, grind =] public theorem generates_iff_linearGenerates
    {g : Grammar T} {A : String} {w : List T} :
    g.Generates A w ↔
      Mathling.Grammar.LinearGrammar.LinearGenerates
        g.toLeftLinearGrammar.toLinear A w := by
  classical
  constructor
  · intro h
    induction h with
    | @atom a A entry =>
        apply Mathling.Grammar.LinearGrammar.LinearGenerates.leaf
          (g := g.toLeftLinearGrammar.toLinear)
          (r := lexicalRule (a, .atom A))
          (word := [a])
        · rw [List.mem_toFinset]
          exact List.mem_map_of_mem (f := lexicalRule) entry
        · rfl
    | @ldiv a A B w entry child ih =>
        simpa [Mathling.Grammar.terminalSymbols] using
          (Mathling.Grammar.LinearGrammar.LinearGenerates.branch
            (g := g.toLeftLinearGrammar.toLinear)
            (r := lexicalRule (a, .ldiv A B))
            (pre := []) (suffix := [a]) (middle := w) (B := A)
            (by
              rw [List.mem_toFinset]
              exact List.mem_map_of_mem (f := lexicalRule) entry)
            (by rfl)
            ih)
  · intro h
    refine Mathling.Grammar.LinearGrammar.LinearGenerates.rec
      (motive := fun A word _ => g.Generates A word) ?_ ?_ h
    · intro r word hr hout
      rw [show g.toLeftLinearGrammar.toLinear.cfg.rules =
        (g.lexicon.entries.map lexicalRule).toFinset by rfl] at hr
      rw [List.mem_toFinset] at hr
      obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hr
      rcases entry with ⟨a, category⟩
      cases category with
      | atom A =>
          change g.Generates A word
          change Mathling.Grammar.terminalSymbols [a] =
            Mathling.Grammar.terminalSymbols word at hout
          have hword := Mathling.Grammar.ContextFreeGrammar.terminalSymbols_injective hout
          subst word
          exact Generates.atom hentry
      | ldiv A B =>
          exfalso
          apply Mathling.Lambek.ProductFree.Shallow.Grammar.terminalSymbols_ne_terminalContext word [] [a] A
          simpa [Mathling.Grammar.terminalSymbols] using hout.symm
    · intro r pre suffix middle B hr hout child ih
      rw [show g.toLeftLinearGrammar.toLinear.cfg.rules =
        (g.lexicon.entries.map lexicalRule).toFinset by rfl] at hr
      rw [List.mem_toFinset] at hr
      obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hr
      rcases entry with ⟨a, category⟩
      cases category with
      | atom A =>
          exfalso
          apply Mathling.Lambek.ProductFree.Shallow.Grammar.terminalSymbols_ne_terminalContext [a] pre suffix B
          simpa [Mathling.Grammar.terminalSymbols] using hout
      | ldiv A C =>
          change Mathling.Grammar.terminalSymbols [] ++
              [Symbol.nonterminal A] ++
              Mathling.Grammar.terminalSymbols [a] =
            Mathling.Grammar.terminalSymbols pre ++
              [Symbol.nonterminal B] ++
              Mathling.Grammar.terminalSymbols suffix at hout
          obtain ⟨rfl, rfl, rfl⟩ :=
            Mathling.Lambek.ProductFree.Shallow.Grammar.terminalContext_injective hout
          simpa using Generates.ldiv hentry ih

```

開始原子における生成同値を左線形文法の言語へ持ち上げ、変換前後の言語が一致することを得る。

```lean
@[important, grind =, simp] public theorem toLeftLinearGrammar_language
    (g : Grammar T) :
    g.toLeftLinearGrammar.language = g.language := by
  ext w
  rw [← Mathling.Grammar.LeftLinearGrammar.toLinear_language,
    ← Mathling.Grammar.LinearGrammar.linearGenerates_iff]
  exact g.generates_iff_linearGenerates.symm.trans
    g.accepts_iff_generates.symm

end Grammar
end Mathling.Lambek.ProductFree.Left.Shallow
```

### Right.Shallow と右線形生成

右 fragment は上の構成を左右反転したものである。右除法語彙だけが許されるため、各 branch は子が生成する語の左端へ一語を追加する。

```lean
namespace Mathling.Lambek.ProductFree.Right.Shallow
namespace Grammar

@[grind cases] public inductive Generates (g : Grammar T) : String → List T → Prop
  | atom {a A} (entry : (a, Tp.atom A) ∈ g.lexicon.entries) :
      Generates g A [a]
  | rdiv {a A B w}
      (entry : (a, Tp.rdiv B A) ∈ g.lexicon.entries)
      (child : Generates g A w) :
      Generates g B (a :: w)

```

片側 fragment の型を一般 shallow 型へ埋め込む。許可された原子と一方向の除法だけを、その構造を変えずに移す。

```lean
private def Tp.toGeneral : Tp →
    Mathling.Lambek.ProductFree.Shallow.Tp
  | .atom A => .atom A
  | .rdiv B A => .rdiv B A

```

型の埋め込みを語彙全体へ写し、同じ開始原子を持つ一般 shallow 文法を作る。この内部文法を一般版の完全性の再利用に使う。

```lean
private def toGeneral (g : Grammar T) :
    Mathling.Lambek.ProductFree.Shallow.Grammar T :=
  { lexicon :=
      { entries := g.lexicon.entries.map fun entry =>
          (entry.1, Tp.toGeneral entry.2) }
    start := g.start }

```

個々の語彙割当は型列への `map` と整合するため、元の分類証明を一般文法の分類証明へ構造的に移せる。

```lean
@[grind .] private theorem categorizes_toGeneral
    {g : Grammar T} {w : List T} {Γ : List Tp}
    (h : g.lexicon.Categorizes w Γ) :
    g.toGeneral.lexicon.Categorizes w (Γ.map Tp.toGeneral) := by
  induction h with
  | nil => exact Mathling.Lambek.Lexicon.Categorizes.nil
  | @cons a A w Γ entry tail ih =>
      apply Mathling.Lambek.Lexicon.Categorizes.cons
        (tail := ih)
      simpa [toGeneral] using
        List.mem_map_of_mem (f := fun entry => (entry.1, Tp.toGeneral entry.2)) entry

```

型埋め込みは product-free 表現を変えない。したがって、分類済みの型列に対する同じ Lambek 導出を一般文法側でも利用できる。

```lean
@[grind .] private theorem toGeneral_accepts
    {g : Grammar T} {w : List T} (h : g.Accepts w) :
    g.toGeneral.Accepts w := by
  obtain ⟨Γ, hcat, hseq⟩ := h
  refine ⟨Γ.map Tp.toGeneral, categorizes_toGeneral hcat, ?_⟩
  have htype (A : Tp) :
      Mathling.Lambek.ProductFree.Shallow.Tp.toProductFree
          (Tp.toGeneral A) = Tp.toProductFree A := by
    cases A <;> rfl
  have hctx_all : ∀ Δ : List Tp,
      List.map
          (Mathling.Lambek.ProductFree.Shallow.Tp.toProductFree ∘
            Tp.toGeneral) Δ =
        List.map Tp.toProductFree Δ := by
    intro Δ
    induction Δ with
    | nil => rfl
    | cons A Δ ih =>
        simp only [List.map_cons, Function.comp_apply]
        rw [htype, ih]
  have hctx := hctx_all Γ
  simp only [toGeneral,
    Mathling.Lambek.ProductFree.Shallow.Sequent,
    Mathling.Lambek.ProductFree.Shallow.ctxToProductFree,
    List.map_map]
  rw [hctx]
  simp only [Mathling.Lambek.ProductFree.Shallow.Tp.toProductFree]
  simpa only [Sequent, ctxToProductFree, Tp.toProductFree] using hseq

```

一般版から戻すときは、埋め込み語彙に反対向きの除法項目が存在しないことを規則形から判定する。残る constructor だけを片側 fragment へ戻す。

```lean
@[grind .] private theorem generates_ofGeneral
    {g : Grammar T} {A : String} {w : List T}
    (h : g.toGeneral.Generates A w) :
    g.Generates A w := by
  induction h with
  | @atom a A entry =>
      change (a, Mathling.Lambek.ProductFree.Shallow.Tp.atom A) ∈
        g.lexicon.entries.map (fun entry =>
          (entry.1, Tp.toGeneral entry.2)) at entry
      obtain ⟨source, hsource, heq⟩ := List.mem_map.mp entry
      rcases source with ⟨a', category⟩
      cases category <;> simp_all [Tp.toGeneral]
      exact Generates.atom hsource
  | @ldiv a A B w entry child ih =>
      change (a, Mathling.Lambek.ProductFree.Shallow.Tp.ldiv A B) ∈
        g.lexicon.entries.map (fun entry =>
          (entry.1, Tp.toGeneral entry.2)) at entry
      obtain ⟨source, hsource, heq⟩ := List.mem_map.mp entry
      rcases source with ⟨a', category⟩
      cases category <;> simp_all [Tp.toGeneral]
  | @rdiv a A B w entry child ih =>
      change (a, Mathling.Lambek.ProductFree.Shallow.Tp.rdiv B A) ∈
        g.lexicon.entries.map (fun entry =>
          (entry.1, Tp.toGeneral entry.2)) at entry
      obtain ⟨source, hsource, heq⟩ := List.mem_map.mp entry
      rcases source with ⟨a', category⟩
      cases category <;> simp_all [Tp.toGeneral]
      simpa using Generates.rdiv hsource ih

@[important, grind .] public theorem accepts_of_generates
    {g : Grammar T} {A : String} {w : List T}
    (h : g.Generates A w) :
    ∃ Γ, g.lexicon.Categorizes w Γ ∧ Sequent Γ (.atom A) := by
  induction h with
  | atom entry =>
      exact ⟨[.atom _],
        Mathling.Lambek.Lexicon.Categorizes.cons entry
          Mathling.Lambek.Lexicon.Categorizes.nil,
        Sequent.ax⟩
  | @rdiv a A B w entry child ih =>
      obtain ⟨Γ, hcat, hseq⟩ := ih
      refine ⟨.rdiv B A :: Γ,
        Mathling.Lambek.Lexicon.Categorizes.cons entry hcat, ?_⟩
      simpa using
        (_root_.Mathling.Lambek.ProductFree.Right.Shallow.Sequent.rdiv_l (Γ := []) (Λ := []) hseq
          (Sequent.ax : Sequent [.atom B] (.atom B)))

```

逆向きでは受理証明から開始原子の生成 spine を復元する。一般版は資源反転を直接使い、片側版は一般 shallow の完全性を経由する。

```lean
@[important, grind .] public theorem generates_of_accepts
    {g : Grammar T} {w : List T} (h : g.Accepts w) :
    g.Generates g.start w :=
  generates_ofGeneral
    (Mathling.Lambek.ProductFree.Shallow.Grammar.generates_of_accepts
      (toGeneral_accepts h))

```

往路と復路を合わせると、Lambek 導出による受理と生成 spine が同値になる。この中間契約を次の文法変換で利用する。

```lean
@[important, grind =] public theorem accepts_iff_generates
    {g : Grammar T} {w : List T} :
    g.Accepts w ↔ g.Generates g.start w := by
  constructor
  · exact generates_of_accepts
  · exact accepts_of_generates
```

右向き spine と右線形生成木も同じ規則反転で一致する。

```lean
@[important, grind =] public theorem generates_iff_linearGenerates
    {g : Grammar T} {A : String} {w : List T} :
    g.Generates A w ↔
      Mathling.Grammar.LinearGrammar.LinearGenerates
        g.toRightLinearGrammar.toLinear A w := by
  classical
  constructor
  · intro h
    induction h with
    | @atom a A entry =>
        apply Mathling.Grammar.LinearGrammar.LinearGenerates.leaf
          (g := g.toRightLinearGrammar.toLinear)
          (r := lexicalRule (a, .atom A))
          (word := [a])
        · rw [List.mem_toFinset]
          exact List.mem_map_of_mem (f := lexicalRule) entry
        · rfl
    | @rdiv a A B w entry child ih =>
        simpa [Mathling.Grammar.terminalSymbols] using
          (Mathling.Grammar.LinearGrammar.LinearGenerates.branch
            (g := g.toRightLinearGrammar.toLinear)
            (r := lexicalRule (a, .rdiv B A))
            (pre := [a]) (suffix := []) (middle := w) (B := A)
            (by
              rw [List.mem_toFinset]
              exact List.mem_map_of_mem (f := lexicalRule) entry)
            (by rfl)
            ih)
  · intro h
    refine Mathling.Grammar.LinearGrammar.LinearGenerates.rec
      (motive := fun A word _ => g.Generates A word) ?_ ?_ h
    · intro r word hr hout
      rw [show g.toRightLinearGrammar.toLinear.cfg.rules =
        (g.lexicon.entries.map lexicalRule).toFinset by rfl] at hr
      rw [List.mem_toFinset] at hr
      obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hr
      rcases entry with ⟨a, category⟩
      cases category with
      | atom A =>
          change g.Generates A word
          change Mathling.Grammar.terminalSymbols [a] =
            Mathling.Grammar.terminalSymbols word at hout
          have hword := Mathling.Grammar.ContextFreeGrammar.terminalSymbols_injective hout
          subst word
          exact Generates.atom hentry
      | rdiv B A =>
          exfalso
          apply Mathling.Lambek.ProductFree.Shallow.Grammar.terminalSymbols_ne_terminalContext word [a] [] A
          simpa [Mathling.Grammar.terminalSymbols] using hout.symm
    · intro r pre suffix middle B hr hout child ih
      rw [show g.toRightLinearGrammar.toLinear.cfg.rules =
        (g.lexicon.entries.map lexicalRule).toFinset by rfl] at hr
      rw [List.mem_toFinset] at hr
      obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hr
      rcases entry with ⟨a, category⟩
      cases category with
      | atom A =>
          exfalso
          apply Mathling.Lambek.ProductFree.Shallow.Grammar.terminalSymbols_ne_terminalContext [a] pre suffix B
          simpa [Mathling.Grammar.terminalSymbols] using hout
      | rdiv C A =>
          change Mathling.Grammar.terminalSymbols [a] ++
              [Symbol.nonterminal A] ++
              Mathling.Grammar.terminalSymbols [] =
            Mathling.Grammar.terminalSymbols pre ++
              [Symbol.nonterminal B] ++
              Mathling.Grammar.terminalSymbols suffix at hout
          obtain ⟨rfl, rfl, rfl⟩ :=
            Mathling.Lambek.ProductFree.Shallow.Grammar.terminalContext_injective hout
          simpa using Generates.rdiv hentry ih

```

開始原子における生成同値を右線形文法の言語へ持ち上げ、変換前後の言語が一致することを得る。

```lean
@[important, grind =, simp] public theorem toRightLinearGrammar_language
    (g : Grammar T) :
    g.toRightLinearGrammar.language = g.language := by
  ext w
  rw [← Mathling.Grammar.RightLinearGrammar.toLinear_language,
    ← Mathling.Grammar.LinearGrammar.linearGenerates_iff]
  exact g.generates_iff_linearGenerates.symm.trans
    g.accepts_iff_generates.symm

end Grammar
end Mathling.Lambek.ProductFree.Right.Shallow
```

## 一般 shallow 言語の線形性

一般 shallow では有限状態性を要求しないため、公開した具体的線形文法と言語等式をそのまま線形言語の witness として使える。

```lean
namespace Mathling.Lambek.ProductFree.Shallow
namespace Grammar

```

具体的な線形文法との言語等式を witness として使い、一般 shallow の言語が線形言語であることを公開する。

```lean
@[important, grind .] public theorem language_isLinear
    (g : Grammar T) : g.language.IsLinear := by
  rw [← g.toLinearGrammar_language]
  exact g.toLinearGrammar.language_isLinear

end Grammar
end Mathling.Lambek.ProductFree.Shallow
```

## 片側 shallow 言語の正規性

公開変換の非終端記号型は原子名をそのまま使うため String だが、実際の語彙が参照する原子は有限個しかない。正規性の証明では開始原子と語彙中の原子から有限台を作り、その subtype を非終端記号とする内部文法へ同じ規則を生成する。

### Right.Shallow の有限台

```lean
namespace Mathling.Lambek.ProductFree.Right.Shallow
namespace Grammar

```

まず各片側型に現れる原子名を列挙する。有限台の構成はこの局所的な走査だけに依存する。

```lean
private def Tp.atoms : Tp → List String
  | .atom A => [A]
  | .rdiv B A => [B, A]

```

開始原子と全語彙項目に現れる原子を集め、有限な非終端記号台を作る。その subtype が内部文法の非終端記号型になる。

```lean
private def atomSupport (g : Grammar T) : Finset String :=
  (g.start :: g.lexicon.entries.flatMap fun entry => Tp.atoms entry.2).toFinset

private abbrev FiniteNT (g : Grammar T) :=
  ↥(atomSupport g)

```

任意の片側生成 spine の結果原子は有限台に必ず含まれる。この事実が生成途中の非終端記号を subtype 化する根拠になる。

```lean
@[grind .] private theorem Generates.result_mem_atomSupport
    {g : Grammar T} {A : String} {w : List T}
    (h : g.Generates A w) :
    A ∈ atomSupport g := by
  cases h with
  | atom entry =>
      simp only [atomSupport, List.mem_toFinset, List.mem_cons,
        List.mem_flatMap]
      right
      exact ⟨_, entry, by simp [Tp.atoms]⟩
  | rdiv entry child =>
      simp only [atomSupport, List.mem_toFinset, List.mem_cons,
        List.mem_flatMap]
      right
      exact ⟨_, entry, by simp [Tp.atoms]⟩

```

各語彙規則の入出力原子へ有限台の所属証明を付け、有限非終端記号上の線形規則へ変換する。

```lean
private noncomputable abbrev finiteLexicalRule
    (g : Grammar T) (entry : {e // e ∈ g.lexicon.entries}) :
    ContextFreeRule T (FiniteNT g) := by
  classical
  rcases entry with ⟨⟨a, category⟩, hentry⟩
  cases category with
  | atom A =>
      exact
        { input := ⟨A, by
              simp only [atomSupport, List.mem_toFinset, List.mem_cons,
                List.mem_flatMap]
              exact Or.inr ⟨_, hentry, by simp [Tp.atoms]⟩⟩
          output := [Symbol.terminal a] }
  | rdiv B A =>
      exact
        { input := ⟨B, by
              simp only [atomSupport, List.mem_toFinset, List.mem_cons,
                List.mem_flatMap]
              exact Or.inr ⟨_, hentry, by simp [Tp.atoms]⟩⟩
          output :=
            [Symbol.terminal a,
              Symbol.nonterminal ⟨A, by
                simp only [atomSupport, List.mem_toFinset, List.mem_cons,
                  List.mem_flatMap]
                exact Or.inr ⟨_, hentry, by simp [Tp.atoms]⟩⟩] }

```

有限化した右向き規則をまとめ、開始原子にも所属証明を付けて内部右線形文法を構成する。

```lean
private noncomputable abbrev toFiniteRightLinearGrammar
    (g : Grammar T) : Mathling.Grammar.RightLinearGrammar T := by
  classical
  exact
    { cfg :=
        { NT := FiniteNT g
          initial := ⟨g.start, by simp [atomSupport]⟩
          rules :=
            (g.lexicon.entries.attach.map
              (finiteLexicalRule g)).toFinset }
      rightLinear := by
        intro r hr
        rw [List.mem_toFinset] at hr
        obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hr
        rcases entry with ⟨⟨a, category⟩, hentry⟩
        cases category <;>
          simp [finiteLexicalRule,
            Mathling.Grammar.ContextFreeRule.IsRightLinear] }
```

有限台版の生成木は、既に証明した right-shallow spine と規則単位で一致する。subtype の所属証明は命題の証拠なので、非終端記号の実体は元の原子名から変わらない。

```lean
@[grind .] private theorem generates_toFinite
    {g : Grammar T} {A : String} {w : List T}
    (h : g.Generates A w) :
    Mathling.Grammar.LinearGrammar.LinearGenerates
      g.toFiniteRightLinearGrammar.toLinear
      ⟨A, h.result_mem_atomSupport⟩ w := by
  classical
  induction h with
  | @atom a A entry =>
      apply Mathling.Grammar.LinearGrammar.LinearGenerates.leaf
        (g := g.toFiniteRightLinearGrammar.toLinear)
        (r := finiteLexicalRule g ⟨(a, .atom A), entry⟩)
        (word := [a])
      · change finiteLexicalRule g ⟨(a, .atom A), entry⟩ ∈
          (g.lexicon.entries.attach.map (finiteLexicalRule g)).toFinset
        rw [List.mem_toFinset]
        exact List.mem_map_of_mem (f := finiteLexicalRule g) (by simp)
      · rfl
  | @rdiv a A B w entry child ih =>
      simpa [finiteLexicalRule, Mathling.Grammar.terminalSymbols] using
        (Mathling.Grammar.LinearGrammar.LinearGenerates.branch
          (g := g.toFiniteRightLinearGrammar.toLinear)
          (r := finiteLexicalRule g ⟨(a, .rdiv B A), entry⟩)
          (pre := [a]) (suffix := []) (middle := w)
          (B := (⟨A, child.result_mem_atomSupport⟩ : FiniteNT g))
          (by
            change finiteLexicalRule g ⟨(a, .rdiv B A), entry⟩ ∈
              (g.lexicon.entries.attach.map
                (finiteLexicalRule g)).toFinset
            rw [List.mem_toFinset]
            exact List.mem_map_of_mem
              (f := finiteLexicalRule g) (by simp))
          (by rfl)
          ih)

```

有限文法の生成木から subtype の値を消去し、元の片側生成 spine を復元する。

```lean
@[grind .] private theorem generates_ofFinite
    {g : Grammar T} {A : FiniteNT g} {w : List T}
    (h : Mathling.Grammar.LinearGrammar.LinearGenerates
      g.toFiniteRightLinearGrammar.toLinear A w) :
    g.Generates A.1 w := by
  classical
  refine Mathling.Grammar.LinearGrammar.LinearGenerates.rec
    (motive := fun (A : FiniteNT g) word _ => g.Generates A.1 word) ?_ ?_ h
  · intro r word hr hout
    rw [show g.toFiniteRightLinearGrammar.toLinear.cfg.rules =
      (g.lexicon.entries.attach.map
        (finiteLexicalRule g)).toFinset by rfl] at hr
    rw [List.mem_toFinset] at hr
    obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hr
    rcases entry with ⟨⟨a, category⟩, hentry⟩
    cases category with
    | atom name =>
        change g.Generates name word
        change Mathling.Grammar.terminalSymbols [a] =
          Mathling.Grammar.terminalSymbols word at hout
        have hword :=
          Mathling.Grammar.ContextFreeGrammar.terminalSymbols_injective hout
        subst word
        exact Generates.atom hentry
    | rdiv result arg =>
        let argNT : FiniteNT g :=
          ⟨arg, by
            simp only [atomSupport, List.mem_toFinset, List.mem_cons,
              List.mem_flatMap]
            exact Or.inr ⟨_, hentry, by simp [Tp.atoms]⟩⟩
        exfalso
        apply Mathling.Lambek.ProductFree.Shallow.Grammar.terminalSymbols_ne_terminalContext word [a] [] argNT
        simpa [argNT, finiteLexicalRule,
          Mathling.Grammar.terminalSymbols] using hout.symm
  · intro r pre suffix middle B hr hout child ih
    rw [show g.toFiniteRightLinearGrammar.toLinear.cfg.rules =
      (g.lexicon.entries.attach.map
        (finiteLexicalRule g)).toFinset by rfl] at hr
    rw [List.mem_toFinset] at hr
    obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hr
    rcases entry with ⟨⟨a, category⟩, hentry⟩
    cases category with
    | atom name =>
        exfalso
        apply Mathling.Lambek.ProductFree.Shallow.Grammar.terminalSymbols_ne_terminalContext [a] pre suffix B
        simpa [finiteLexicalRule,
          Mathling.Grammar.terminalSymbols] using hout
    | rdiv result arg =>
        let argNT : FiniteNT g :=
          ⟨arg, by
            simp only [atomSupport, List.mem_toFinset, List.mem_cons,
              List.mem_flatMap]
            exact Or.inr ⟨_, hentry, by simp [Tp.atoms]⟩⟩
        have hout' :
            Mathling.Grammar.terminalSymbols [a] ++
                [Symbol.nonterminal argNT] ++
                Mathling.Grammar.terminalSymbols [] =
              Mathling.Grammar.terminalSymbols pre ++
                [Symbol.nonterminal B] ++
                Mathling.Grammar.terminalSymbols suffix := by
          simpa [argNT, finiteLexicalRule,
            Mathling.Grammar.terminalSymbols] using hout
        obtain ⟨hpre, hB, hsuffix⟩ :=
          Mathling.Lambek.ProductFree.Shallow.Grammar.terminalContext_injective hout'
        subst pre
        subst B
        subst suffix
        simpa [argNT] using Generates.rdiv hentry ih

```

二つの変換をまとめ、開始原子を含む任意の台上の非終端記号について生成関係が一致することを示す。

```lean
@[important, grind =] private theorem
    toFiniteRightLinearGrammar_language (g : Grammar T) :
    g.toFiniteRightLinearGrammar.language = g.language := by
  ext w
  calc
    w ∈ g.toFiniteRightLinearGrammar.language ↔
        Mathling.Grammar.LinearGrammar.LinearGenerates
          g.toFiniteRightLinearGrammar.toLinear
          g.toFiniteRightLinearGrammar.toLinear.cfg.initial w := by
      rw [← Mathling.Grammar.RightLinearGrammar.toLinear_language]
      exact (Mathling.Grammar.LinearGrammar.linearGenerates_iff
        g.toFiniteRightLinearGrammar.toLinear w).symm
    _ ↔ g.Generates g.start w := by
      constructor
      · exact generates_ofFinite
      · intro h
        simpa [toFiniteRightLinearGrammar] using generates_toFinite h
    _ ↔ g.Accepts w := g.accepts_iff_generates.symm
    _ ↔ w ∈ g.language := Iff.rfl

```

有限非終端記号を持つ内部片側線形文法と言語が一致するため、元の shallow 言語は正規言語である。

```lean
@[important, grind .] public theorem language_isRegular
    (g : Grammar T) : g.language.IsRegular := by
  rw [← g.toFiniteRightLinearGrammar_language]
  exact g.toFiniteRightLinearGrammar.language_isRegular

end Grammar
end Mathling.Lambek.ProductFree.Right.Shallow
```

### Left.Shallow の有限台

左側も同じ有限台を使い、左除法語彙を A → B a 型の生成規則へ移す。これにより語反転を API に露出させず、左線形文法の既存正規性定理を直接利用できる。

```lean
namespace Mathling.Lambek.ProductFree.Left.Shallow
namespace Grammar

```

まず各片側型に現れる原子名を列挙する。有限台の構成はこの局所的な走査だけに依存する。

```lean
private def Tp.atoms : Tp → List String
  | .atom A => [A]
  | .ldiv A B => [A, B]

```

開始原子と全語彙項目に現れる原子を集め、有限な非終端記号台を作る。その subtype が内部文法の非終端記号型になる。

```lean
private def atomSupport (g : Grammar T) : Finset String :=
  (g.start :: g.lexicon.entries.flatMap fun entry => Tp.atoms entry.2).toFinset

private abbrev FiniteNT (g : Grammar T) :=
  ↥(atomSupport g)

```

任意の片側生成 spine の結果原子は有限台に必ず含まれる。この事実が生成途中の非終端記号を subtype 化する根拠になる。

```lean
@[grind .] private theorem Generates.result_mem_atomSupport
    {g : Grammar T} {A : String} {w : List T}
    (h : g.Generates A w) :
    A ∈ atomSupport g := by
  cases h with
  | atom entry =>
      simp only [atomSupport, List.mem_toFinset, List.mem_cons,
        List.mem_flatMap]
      right
      exact ⟨_, entry, by simp [Tp.atoms]⟩
  | ldiv entry child =>
      simp only [atomSupport, List.mem_toFinset, List.mem_cons,
        List.mem_flatMap]
      right
      exact ⟨_, entry, by simp [Tp.atoms]⟩

```

各語彙規則の入出力原子へ有限台の所属証明を付け、有限非終端記号上の線形規則へ変換する。

```lean
private noncomputable abbrev finiteLexicalRule
    (g : Grammar T) (entry : {e // e ∈ g.lexicon.entries}) :
    ContextFreeRule T (FiniteNT g) := by
  classical
  rcases entry with ⟨⟨a, category⟩, hentry⟩
  cases category with
  | atom A =>
      exact
        { input := ⟨A, by
              simp only [atomSupport, List.mem_toFinset, List.mem_cons,
                List.mem_flatMap]
              exact Or.inr ⟨_, hentry, by simp [Tp.atoms]⟩⟩
          output := [Symbol.terminal a] }
  | ldiv A B =>
      exact
        { input := ⟨B, by
              simp only [atomSupport, List.mem_toFinset, List.mem_cons,
                List.mem_flatMap]
              exact Or.inr ⟨_, hentry, by simp [Tp.atoms]⟩⟩
          output :=
            [Symbol.nonterminal ⟨A, by
                simp only [atomSupport, List.mem_toFinset, List.mem_cons,
                  List.mem_flatMap]
                exact Or.inr ⟨_, hentry, by simp [Tp.atoms]⟩⟩,
              Symbol.terminal a] }

```

有限化した左向き規則をまとめ、開始原子にも所属証明を付けて内部左線形文法を構成する。

```lean
private noncomputable abbrev toFiniteLeftLinearGrammar
    (g : Grammar T) : Mathling.Grammar.LeftLinearGrammar T := by
  classical
  exact
    { cfg :=
        { NT := FiniteNT g
          initial := ⟨g.start, by simp [atomSupport]⟩
          rules :=
            (g.lexicon.entries.attach.map
              (finiteLexicalRule g)).toFinset }
      leftLinear := by
        intro r hr
        rw [List.mem_toFinset] at hr
        obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hr
        rcases entry with ⟨⟨a, category⟩, hentry⟩
        cases category <;>
          simp [finiteLexicalRule,
            Mathling.Grammar.ContextFreeRule.IsLeftLinear] }

```

元の生成 spine に台への所属証明を補い、有限文法の生成木へ写す。

```lean
@[grind .] private theorem generates_toFinite
    {g : Grammar T} {A : String} {w : List T}
    (h : g.Generates A w) :
    Mathling.Grammar.LinearGrammar.LinearGenerates
      g.toFiniteLeftLinearGrammar.toLinear
      ⟨A, h.result_mem_atomSupport⟩ w := by
  classical
  induction h with
  | @atom a A entry =>
      apply Mathling.Grammar.LinearGrammar.LinearGenerates.leaf
        (g := g.toFiniteLeftLinearGrammar.toLinear)
        (r := finiteLexicalRule g ⟨(a, .atom A), entry⟩)
        (word := [a])
      · change finiteLexicalRule g ⟨(a, .atom A), entry⟩ ∈
          (g.lexicon.entries.attach.map (finiteLexicalRule g)).toFinset
        rw [List.mem_toFinset]
        exact List.mem_map_of_mem (f := finiteLexicalRule g) (by simp)
      · rfl
  | @ldiv a A B w entry child ih =>
      simpa [finiteLexicalRule, Mathling.Grammar.terminalSymbols] using
        (Mathling.Grammar.LinearGrammar.LinearGenerates.branch
          (g := g.toFiniteLeftLinearGrammar.toLinear)
          (r := finiteLexicalRule g ⟨(a, .ldiv A B), entry⟩)
          (pre := []) (suffix := [a]) (middle := w)
          (B := (⟨A, child.result_mem_atomSupport⟩ : FiniteNT g))
          (by
            change finiteLexicalRule g ⟨(a, .ldiv A B), entry⟩ ∈
              (g.lexicon.entries.attach.map
                (finiteLexicalRule g)).toFinset
            rw [List.mem_toFinset]
            exact List.mem_map_of_mem
              (f := finiteLexicalRule g) (by simp))
          (by rfl)
          ih)

```

有限文法の生成木から subtype の値を消去し、元の片側生成 spine を復元する。

```lean
@[grind .] private theorem generates_ofFinite
    {g : Grammar T} {A : FiniteNT g} {w : List T}
    (h : Mathling.Grammar.LinearGrammar.LinearGenerates
      g.toFiniteLeftLinearGrammar.toLinear A w) :
    g.Generates A.1 w := by
  classical
  refine Mathling.Grammar.LinearGrammar.LinearGenerates.rec
    (motive := fun (A : FiniteNT g) word _ => g.Generates A.1 word) ?_ ?_ h
  · intro r word hr hout
    rw [show g.toFiniteLeftLinearGrammar.toLinear.cfg.rules =
      (g.lexicon.entries.attach.map
        (finiteLexicalRule g)).toFinset by rfl] at hr
    rw [List.mem_toFinset] at hr
    obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hr
    rcases entry with ⟨⟨a, category⟩, hentry⟩
    cases category with
    | atom name =>
        change g.Generates name word
        change Mathling.Grammar.terminalSymbols [a] =
          Mathling.Grammar.terminalSymbols word at hout
        have hword :=
          Mathling.Grammar.ContextFreeGrammar.terminalSymbols_injective hout
        subst word
        exact Generates.atom hentry
    | ldiv arg result =>
        let argNT : FiniteNT g :=
          ⟨arg, by
            simp only [atomSupport, List.mem_toFinset, List.mem_cons,
              List.mem_flatMap]
            exact Or.inr ⟨_, hentry, by simp [Tp.atoms]⟩⟩
        exfalso
        apply Mathling.Lambek.ProductFree.Shallow.Grammar.terminalSymbols_ne_terminalContext word [] [a] argNT
        simpa [argNT, finiteLexicalRule,
          Mathling.Grammar.terminalSymbols] using hout.symm
  · intro r pre suffix middle B hr hout child ih
    rw [show g.toFiniteLeftLinearGrammar.toLinear.cfg.rules =
      (g.lexicon.entries.attach.map
        (finiteLexicalRule g)).toFinset by rfl] at hr
    rw [List.mem_toFinset] at hr
    obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hr
    rcases entry with ⟨⟨a, category⟩, hentry⟩
    cases category with
    | atom name =>
        exfalso
        apply Mathling.Lambek.ProductFree.Shallow.Grammar.terminalSymbols_ne_terminalContext [a] pre suffix B
        simpa [finiteLexicalRule,
          Mathling.Grammar.terminalSymbols] using hout
    | ldiv arg result =>
        let argNT : FiniteNT g :=
          ⟨arg, by
            simp only [atomSupport, List.mem_toFinset, List.mem_cons,
              List.mem_flatMap]
            exact Or.inr ⟨_, hentry, by simp [Tp.atoms]⟩⟩
        have hout' :
            Mathling.Grammar.terminalSymbols [] ++
                [Symbol.nonterminal argNT] ++
                Mathling.Grammar.terminalSymbols [a] =
              Mathling.Grammar.terminalSymbols pre ++
                [Symbol.nonterminal B] ++
                Mathling.Grammar.terminalSymbols suffix := by
          simpa [argNT, finiteLexicalRule,
            Mathling.Grammar.terminalSymbols] using hout
        obtain ⟨hpre, hB, hsuffix⟩ :=
          Mathling.Lambek.ProductFree.Shallow.Grammar.terminalContext_injective hout'
        subst pre
        subst B
        subst suffix
        simpa [argNT] using Generates.ldiv hentry ih

```

二つの変換をまとめ、開始原子を含む任意の台上の非終端記号について生成関係が一致することを示す。

```lean
@[important, grind =] private theorem
    toFiniteLeftLinearGrammar_language (g : Grammar T) :
    g.toFiniteLeftLinearGrammar.language = g.language := by
  ext w
  calc
    w ∈ g.toFiniteLeftLinearGrammar.language ↔
        Mathling.Grammar.LinearGrammar.LinearGenerates
          g.toFiniteLeftLinearGrammar.toLinear
          g.toFiniteLeftLinearGrammar.toLinear.cfg.initial w := by
      rw [← Mathling.Grammar.LeftLinearGrammar.toLinear_language]
      exact (Mathling.Grammar.LinearGrammar.linearGenerates_iff
        g.toFiniteLeftLinearGrammar.toLinear w).symm
    _ ↔ g.Generates g.start w := by
      constructor
      · exact generates_ofFinite
      · intro h
        simpa [toFiniteLeftLinearGrammar] using generates_toFinite h
    _ ↔ g.Accepts w := g.accepts_iff_generates.symm
    _ ↔ w ∈ g.language := Iff.rfl

```

有限非終端記号を持つ内部片側線形文法と言語が一致するため、元の shallow 言語は正規言語である。

```lean
@[important, grind .] public theorem language_isRegular
    (g : Grammar T) : g.language.IsRegular := by
  rw [← g.toFiniteLeftLinearGrammar_language]
  exact g.toFiniteLeftLinearGrammar.language_isRegular

end Grammar
end Mathling.Lambek.ProductFree.Left.Shallow
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
