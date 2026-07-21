    module

    public import Mathling.Grammar.ContextFree
    public import Mathling.Automata.Pushdown
    public import Mathling.Meta.Important

    import LiterateLean
    open scoped LiterateLean


# Mathling / Grammar / Regular / Linear モジュール

線形文法の生成木と一回転 NPDA を対応付ける。生成規則から機械を構成し、木から受理実行を作る順方向と、受理実行から木を復元する逆方向を証明して、両者の言語が一致することを導く。

```lean

/-!
# Linear grammars

Production-tree semantics and the one-turn NPDA construction for linear grammars.
-/

namespace Mathling.Grammar

namespace LinearGrammar

variable {T : Type*}

/-- Every linear grammar is, by forgetting its linearity certificate, a
context-free grammar for the same language. -/
@[important, grind .] public theorem language_isContextFree (g : LinearGrammar T) :
    g.language.IsContextFree :=
  ⟨g.cfg, rfl⟩

end LinearGrammar

namespace LinearGrammar

variable {T : Type*}



@[grind .] private theorem terminals_of_count_eq_zero {N : Type}
    (s : List (Symbol T N))
    (h : s.countP (symbolIsNonterminal (T := T)) = 0) :
    ∃ w : List T, s = terminalSymbols w := by
  induction s with
  | nil => exact ⟨[], rfl⟩
  | cons symbol s ih =>
      cases symbol with
      | terminal a =>
          have hs : s.countP (symbolIsNonterminal (T := T)) = 0 := by
            simpa only [List.countP_cons, symbolIsNonterminal, Bool.false_eq_true, if_false,
              zero_add, Nat.add_zero] using h
          obtain ⟨w, rfl⟩ := ih hs
          exact ⟨a :: w, rfl⟩
      | nonterminal A =>
          simp only [List.countP_cons, symbolIsNonterminal, if_true] at h
          omega

@[grind .] private theorem split_linear_output {N : Type}
    (s : List (Symbol T N))
    (h : s.countP (symbolIsNonterminal (T := T)) ≤ 1) :
    (∃ word : List T, s = terminalSymbols word) ∨
      ∃ pre : List T, ∃ B : N, ∃ suffix : List T,
        s = terminalSymbols pre ++ [Symbol.nonterminal B] ++ terminalSymbols suffix := by
  induction s with
  | nil => exact Or.inl ⟨[], rfl⟩
  | cons symbol s ih =>
      cases symbol with
      | terminal a =>
          have hs : s.countP (symbolIsNonterminal (T := T)) ≤ 1 := by
            simpa only [List.countP_cons, symbolIsNonterminal, Bool.false_eq_true, if_false,
              zero_add, Nat.add_zero] using h
          rcases ih hs with ⟨word, rfl⟩ | ⟨pre, B, suffix, rfl⟩
          · exact Or.inl ⟨a :: word, rfl⟩
          · exact Or.inr ⟨a :: pre, B, suffix, by simp [terminalSymbols]⟩
      | nonterminal A =>
          have hc : s.countP (symbolIsNonterminal (T := T)) + 1 ≤ 1 := by
            simpa only [List.countP_cons, symbolIsNonterminal, if_true] using h
          have hz : s.countP (symbolIsNonterminal (T := T)) = 0 := by omega
          obtain ⟨suffix, rfl⟩ := terminals_of_count_eq_zero s hz
          exact Or.inr ⟨[], A, suffix, by simp [terminalSymbols]⟩

/-- The production-tree semantics of a linear grammar. -/
@[grind cases] public inductive LinearGenerates (g : LinearGrammar T) : g.cfg.NT → List T → Prop
  | leaf {r : ContextFreeRule T g.cfg.NT} {word : List T}
      (hr : r ∈ g.cfg.rules) (hout : r.output = terminalSymbols word) :
      LinearGenerates g r.input word
  | branch {r : ContextFreeRule T g.cfg.NT} {pre suffix middle : List T}
      {B : g.cfg.NT}
      (hr : r ∈ g.cfg.rules)
      (hout : r.output =
        terminalSymbols pre ++ [Symbol.nonterminal B] ++ terminalSymbols suffix)
      (child : LinearGenerates g B middle) :
      LinearGenerates g r.input (pre ++ middle ++ suffix)

@[grind .] private theorem generates_derives (g : LinearGrammar T)
    {A : g.cfg.NT} {w : List T} (h : LinearGenerates g A w) :
    g.cfg.Derives [Symbol.nonterminal A] (terminalSymbols w) := by
  induction h with
  | leaf hr hout =>
      have hp : g.cfg.Produces [Symbol.nonterminal _] _ :=
        ⟨_, hr, ContextFreeRule.Rewrites.input_output⟩
      simpa [hout] using hp.single
  | @branch r pre suffix middle B hr hout child ih =>
      have hp : g.cfg.Produces [Symbol.nonterminal _] _ :=
        ⟨_, hr, ContextFreeRule.Rewrites.input_output⟩
      apply hp.single.trans
      have hctx := (ih.append_left (terminalSymbols pre)).append_right
        (terminalSymbols suffix)
      simpa [hout, terminalSymbols, List.map_append, List.append_assoc] using hctx


@[grind .] private theorem rewrites_terminal_context (r : ContextFreeRule T N)
    (left right : List T) (A : N) {v : List (Symbol T N)}
    (h : r.Rewrites
      (terminalSymbols left ++ [Symbol.nonterminal A] ++ terminalSymbols right) v) :
    r.input = A ∧
      v = terminalSymbols left ++ r.output ++ terminalSymbols right := by
  induction left generalizing v with
  | nil =>
      simp only [terminalSymbols, List.map_nil, List.nil_append] at h ⊢
      cases h with
      | head s => exact ⟨rfl, rfl⟩
      | cons _ htail =>
          exact (ContextFreeGrammar.no_rewrites_terminals r htail).elim
  | cons a left ih =>
      simp only [terminalSymbols, List.map_cons, List.cons_append] at h ⊢
      cases h with
      | cons _ htail =>
          obtain ⟨hin, hout⟩ := ih htail
          exact ⟨hin, congrArg (Symbol.terminal a :: ·) hout⟩


@[grind .] private theorem derives_linear_context (g : LinearGrammar T)
    {form : List (Symbol T g.cfg.NT)} {target : List T}
    (h : g.cfg.Derives form (terminalSymbols target)) :
    ∀ (left right : List T) (A : g.cfg.NT),
      form = terminalSymbols left ++ [Symbol.nonterminal A] ++ terminalSymbols right →
      ∃ middle : List T,
        target = left ++ middle ++ right ∧ LinearGenerates g A middle := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro left right A hform
      have hmem : Symbol.nonterminal A ∈ terminalSymbols target := by
        rw [hform]
        simp
      simp [terminalSymbols] at hmem
  | head hprod hrest ih =>
      intro left right A hform
      rcases hprod with ⟨r, hr, hw⟩
      rw [hform] at hw
      obtain ⟨hin, hc⟩ := rewrites_terminal_context r left right A hw
      cases hin
      have hcount : r.output.countP (symbolIsNonterminal (T := T)) ≤ 1 :=
        g.linear r hr
      rcases split_linear_output r.output hcount with
        ⟨word, hout⟩ | ⟨pre, B, suffix, hout⟩
      · have hrest' :
            g.cfg.Derives
              (terminalSymbols left ++ r.output ++ terminalSymbols right)
              (terminalSymbols target) := by
          rw [← hc]
          exact hrest
        have hterminal :
            g.cfg.Derives (terminalSymbols (left ++ word ++ right))
              (terminalSymbols target) := by
          rw [hout] at hrest'
          simpa [terminalSymbols, List.map_append, List.append_assoc] using hrest'
        refine ⟨word,
          (ContextFreeGrammar.derives_terminals_eq g.cfg hterminal).symm, ?_⟩
        exact LinearGenerates.leaf hr hout
      · obtain ⟨middle, heq, hmiddle⟩ :=
          ih (left ++ pre) (suffix ++ right) B (by
            rw [hc, hout]
            simp [terminalSymbols, List.map_append, List.append_assoc])
        refine ⟨pre ++ middle ++ suffix, ?_, ?_⟩
        · simpa [List.append_assoc] using heq
        · exact LinearGenerates.branch hr hout hmiddle

```

## 木構造意味論と通常の導出の一致

前節で定義した `LinearGenerates` は、生成規則の適用を明示的な木として表現した帰納的述語である。`generates_derives` と `derives_linear_context` はそれぞれ、この木構造意味論から Mathlib の `Derives` 関係への含意と、その逆方向の含意を与える。`linearGenerates_iff` はこの両者を組み合わせ、文法の初期記号から導出できる言語 `g.language` の要素と、`LinearGenerates` によって生成される終端列とが過不足なく一致することを確立する。以降では、この同値性を唯一の橋渡しとして、木構造上の議論とオートマトンの実行列に関する議論とを行き来する。

```lean
/-- Production trees and context-free derivations agree for linear grammars. -/
@[grind .] theorem linearGenerates_iff (g : LinearGrammar T) (w : List T) :
    LinearGenerates g g.cfg.initial w ↔ w ∈ g.language := by
  constructor
  · exact generates_derives g
  · intro h
    obtain ⟨middle, heq, hmiddle⟩ :=
      derives_linear_context g h [] [] g.cfg.initial rfl
    simp only [List.nil_append, List.append_nil] at heq
    subst middle
    exact hmiddle

```

## 生成規則駆動の一回転 NPDA

`LinearGenerates` の各生成木を、実行時に１本のスタック操作列としてシミュレートするのが `toOneTurnNPDA` である。線形文法の規則は「終端列のみ」（leaf）か「前後を終端列で挟んだ単一の非終端記号」（branch）のいずれかの形しか取り得ない（`g.linear` と `split_linear_output` が保証する）。したがって PDA は、規則を１つ選んだあと、その出力を左から右へなぞりながら push フェーズで入力を消費し、非終端記号に達したら子の導出へ、終端記号のみになったら pop フェーズへの折り返しへ進む、という単純な制御構造で足りる。

制御状態 `LinearPDAState` は「選んだ規則のどこまで処理し終えたか」を型として直接表現する。

- `derive A`：非終端記号 `A` をこれから導出しようとしている状態。
- `prefixLeaf r hr word todo hout`：leaf 規則 `r` を選び、その出力全体 `word` のうち残り `todo` をまだ消費し終えていない状態。
- `prefixBranch r hr pre todo B suffix hout`：branch 規則 `r` を選び、前置終端列の残り `todo` を消費している最中の状態（消費し終えれば非終端記号 `B` と後置終端列 `suffix` が控えている）。
- `pushBranch B suffix todo`：`prefixBranch` の消費が終わり、後置終端列 `suffix` を１文字ずつスタックへ積んでいく途中の状態（`todo` は積み残し）。
- `matchStack`：入力の残りとスタックの中身を pop フェーズで突き合わせる状態。
- `finished`：受理状態。

`LinearRawStep` はこれらの状態間の局所遷移を１個ずつ与える。

```mermaid
stateDiagram-v2
    [*] --> derive
    derive --> prefixLeaf: chooseLeaf（規則が leaf 形）
    derive --> prefixBranch: chooseBranch（規則が branch 形）
    prefixLeaf --> prefixLeaf: consumeLeaf（終端を1つ消費）
    prefixLeaf --> matchStack: finishLeaf（push→pop へ折り返し）
    prefixBranch --> prefixBranch: consumeBranch（前置終端を1つ消費）
    prefixBranch --> pushBranch: beginPush
    pushBranch --> pushBranch: push（後置終端を1つスタックへ）
    pushBranch --> derive: continue（子の非終端へ再帰）
    matchStack --> matchStack: matchStack（スタックと入力を1つずつ照合）
    matchStack --> finished: finish
    finished --> [*]
```

構成子をこのように細かく分けているのは、後段の `LinearGood` 不変条件がちょうど１ステップごとに保存されることを個別に確認できるようにするためであり、`toOneTurnNPDA` 自体はこれらの局所遷移を非決定的に合併しただけの定義になっている。`pop_stays_pop`／`push_phase_nonshrinking`／`pop_phase_nongrowing` は、この構成が push フェーズで積んだ分だけ pop フェーズで消費して終わるという `OneTurnNPDA`（一回転 PDA）の形状要件を満たすことを保証する。

```lean
/-- Control states for the production-driven linear-grammar PDA. -/
@[grind cases] public inductive LinearPDAState (g : LinearGrammar T) where
  | derive (A : g.cfg.NT)
  | prefixLeaf (r : ContextFreeRule T g.cfg.NT) (hr : r ∈ g.cfg.rules)
      (word todo : List T) (hout : r.output = terminalSymbols word)
  | prefixBranch (r : ContextFreeRule T g.cfg.NT) (hr : r ∈ g.cfg.rules)
      (pre todo : List T) (B : g.cfg.NT) (suffix : List T)
      (hout : r.output =
        terminalSymbols pre ++ [Symbol.nonterminal B] ++ terminalSymbols suffix)
  | pushBranch (B : g.cfg.NT) (suffix todo : List T)
  | matchStack
  | finished

namespace Internal

/-- Local micro-transitions for the linear-grammar PDA. -/
@[grind cases] inductive LinearRawStep (g : LinearGrammar T) :
    LinearPDAState g → Mathling.Automata.TurnPhase → Option T → List T →
      LinearPDAState g → Mathling.Automata.TurnPhase → List T → Prop
  | chooseLeaf {r word stack}
      (hr : r ∈ g.cfg.rules) (hout : r.output = terminalSymbols word) :
      LinearRawStep g (.derive r.input) .push none stack
        (.prefixLeaf r hr word word hout) .push stack
  | chooseBranch {r pre B suffix stack}
      (hr : r ∈ g.cfg.rules)
      (hout : r.output =
        terminalSymbols pre ++ [Symbol.nonterminal B] ++ terminalSymbols suffix) :
      LinearRawStep g (.derive r.input) .push none stack
        (.prefixBranch r hr pre pre B suffix hout) .push stack
  | consumeLeaf {r hr word a todo hout stack} :
      LinearRawStep g (.prefixLeaf r hr word (a :: todo) hout) .push
        (some a) stack (.prefixLeaf r hr word todo hout) .push stack
  | consumeBranch {r hr pre a todo B suffix hout stack} :
      LinearRawStep g (.prefixBranch r hr pre (a :: todo) B suffix hout) .push
        (some a) stack (.prefixBranch r hr pre todo B suffix hout) .push stack
  | finishLeaf {r hr word hout stack} :
      LinearRawStep g (.prefixLeaf r hr word [] hout) .push none stack
        .matchStack .pop stack
  | beginPush {r hr pre B suffix hout stack} :
      LinearRawStep g (.prefixBranch r hr pre [] B suffix hout) .push none stack
        (.pushBranch B suffix suffix.reverse) .push stack
  | push {B suffix a todo stack} :
      LinearRawStep g (.pushBranch B suffix (a :: todo)) .push none stack
        (.pushBranch B suffix todo) .push (a :: stack)
  | continue {B suffix stack} :
      LinearRawStep g (.pushBranch B suffix []) .push none stack
        (.derive B) .push stack
  | matchStack {a stack} :
      LinearRawStep g .matchStack .pop (some a) (a :: stack)
        .matchStack .pop stack
  | finish :
      LinearRawStep g .matchStack .pop none [] .finished .pop []

end Internal

open Internal

/-- Convert a linear grammar to a local, production-driven one-turn NPDA. -/
public def toOneTurnNPDA (g : LinearGrammar T) :
    Mathling.Automata.OneTurnNPDA T (LinearPDAState g) T where
  step q phase sym stack :=
    {next | Internal.LinearRawStep g q phase sym stack next.1 next.2.1 next.2.2}
  start := {.derive g.cfg.initial}
  accept := {.finished}
  initialStack := []
  pop_stays_pop := by
    intro q p sym stack q' p' stack' h hp
    cases h <;> simp_all
  push_phase_nonshrinking := by
    intro q sym stack q' stack' h
    cases h <;> simp
  pop_phase_nongrowing := by
    intro q p sym stack q' stack' h
    cases h <;> simp

```

## 順方向：生成木から実行列を構成する

以降の `_reaches` 系の補題は、`LinearRawStep` の１ステップ遷移を繰り返し適用して、`toOneTurnNPDA` が意図した通りの複数ステップ実行列（`Reaches`）を持つことを示す部品である。それぞれが `LinearPDAState` の１つの構成子に対応するミクロな振る舞いを切り出しており、続く `generates_reaches` はこれらを規則の形（leaf／branch）に応じて組み合わせるだけで済む。

- `consumeLeaf_reaches`：`prefixLeaf` 状態で残りの終端列 `todo` を１文字ずつ消費し尽くすまでの実行列。
- `consumeBranch_reaches`：同様に `prefixBranch` 状態で前置終端列の残りを消費し尽くすまでの実行列。
- `pushBranch_reaches`：`pushBranch` 状態で後置終端列 `todo` を先頭から１文字ずつスタックへ積み、`todo.reverse` がスタックの上に乗った状態で `derive B` へ遷移するまでの実行列。push は入力側の消費と逆向きの操作であるため、積み終えた結果が `todo.reverse ++ stack` という反転した順序になる点に注意されたい。
- `matchStack_reaches`：`matchStack` 状態で入力の残りとスタックの中身を１文字ずつ突き合わせ、両者を使い切ったところで `finished` 状態へ折り返すまでの実行列。

```lean
@[grind .] private theorem consumeLeaf_reaches (g : LinearGrammar T)
    {r : ContextFreeRule T g.cfg.NT} {hr : r ∈ g.cfg.rules}
    {word : List T} {hout : r.output = terminalSymbols word}
    (todo rest stack : List T) :
    g.toOneTurnNPDA.Reaches
      (todo ++ rest, (.prefixLeaf r hr word todo hout, .push), stack)
      (rest, (.prefixLeaf r hr word [] hout, .push), stack) := by
  induction todo with
  | nil => exact Relation.ReflTransGen.refl
  | cons a todo ih =>
      have hstep : g.toOneTurnNPDA.Step
          (a :: todo ++ rest, (.prefixLeaf r hr word (a :: todo) hout, .push), stack)
          (todo ++ rest, (.prefixLeaf r hr word todo hout, .push), stack) := by
        apply Mathling.Automata.OneTurnNPDA.Step.consume
        change LinearRawStep g _ _ _ _ _ _ _
        exact LinearRawStep.consumeLeaf
      exact ih.head hstep

@[grind .] private theorem consumeBranch_reaches (g : LinearGrammar T)
    {r : ContextFreeRule T g.cfg.NT} {hr : r ∈ g.cfg.rules}
    {pre : List T} {B : g.cfg.NT} {suffix : List T}
    {hout : r.output =
      terminalSymbols pre ++ [Symbol.nonterminal B] ++ terminalSymbols suffix}
    (todo rest stack : List T) :
    g.toOneTurnNPDA.Reaches
      (todo ++ rest, (.prefixBranch r hr pre todo B suffix hout, .push), stack)
      (rest, (.prefixBranch r hr pre [] B suffix hout, .push), stack) := by
  induction todo with
  | nil => exact Relation.ReflTransGen.refl
  | cons a todo ih =>
      have hstep : g.toOneTurnNPDA.Step
          (a :: todo ++ rest,
            (.prefixBranch r hr pre (a :: todo) B suffix hout, .push), stack)
          (todo ++ rest, (.prefixBranch r hr pre todo B suffix hout, .push), stack) := by
        apply Mathling.Automata.OneTurnNPDA.Step.consume
        change LinearRawStep g _ _ _ _ _ _ _
        exact LinearRawStep.consumeBranch
      exact ih.head hstep

@[grind .] private theorem pushBranch_reaches (g : LinearGrammar T) (B : g.cfg.NT)
    (suffix todo input stack : List T) :
    g.toOneTurnNPDA.Reaches
      (input, (.pushBranch B suffix todo, .push), stack)
      (input, (.derive B, .push), todo.reverse ++ stack) := by
  induction todo generalizing stack with
  | nil =>
      apply Relation.ReflTransGen.single
      apply Mathling.Automata.OneTurnNPDA.Step.epsilon
      change LinearRawStep g _ _ _ _ _ _ _
      exact LinearRawStep.continue
  | cons a todo ih =>
      have hstep : g.toOneTurnNPDA.Step
          (input, (.pushBranch B suffix (a :: todo), .push), stack)
          (input, (.pushBranch B suffix todo, .push), a :: stack) := by
        apply Mathling.Automata.OneTurnNPDA.Step.epsilon
        change LinearRawStep g _ _ _ _ _ _ _
        exact LinearRawStep.push
      have hrest' : g.toOneTurnNPDA.Reaches
          (input, (.pushBranch B suffix todo, .push), a :: stack)
          (input, (.derive B, .push), (a :: todo).reverse ++ stack) := by
        simpa [List.reverse_cons, List.append_assoc] using ih (a :: stack)
      exact hrest'.head hstep

@[grind .] private theorem matchStack_reaches (g : LinearGrammar T) (stack : List T) :
    g.toOneTurnNPDA.Reaches
      (stack, (.matchStack, .pop), stack)
      ([], (.finished, .pop), []) := by
  induction stack with
  | nil =>
      apply Relation.ReflTransGen.single
      apply Mathling.Automata.OneTurnNPDA.Step.epsilon
      change LinearRawStep g _ _ _ _ _ _ _
      exact LinearRawStep.finish
  | cons a stack ih =>
      have hstep : g.toOneTurnNPDA.Step
          (a :: stack, (.matchStack, .pop), a :: stack)
          (stack, (.matchStack, .pop), stack) := by
        apply Mathling.Automata.OneTurnNPDA.Step.consume
        change LinearRawStep g _ _ _ _ _ _ _
        exact LinearRawStep.matchStack
      exact ih.head hstep

```

`generates_reaches` はこれらの部品を `LinearGenerates` の帰納法に沿って接続し、任意の生成木に対して、その終端列を先頭に積んだ入力から出発して `finished` 状態・空スタックへ到達する実行列を構成する。leaf ケースでは規則選択・終端列消費・pop フェーズへの折り返し・スタック照合をこの順に繋ぐだけでよい。branch ケースでは、前置終端列の消費・push フェーズの開始・後置終端列のスタックへの積み込みに続けて、帰納法の仮定 `ih` を子の非終端 `B` に適用することで、部分木の実行列を全体の実行列へ組み込んでいる。この定理が、文法が生成する語を PDA が受理するという含意（`toOneTurnNPDA_language` の一方向）の核心を担う。

```lean
@[grind .] private theorem generates_reaches (g : LinearGrammar T)
    {A : g.cfg.NT} {word : List T} (h : LinearGenerates g A word)
    (stack : List T) :
    g.toOneTurnNPDA.Reaches
      (word ++ stack, (.derive A, .push), stack)
      ([], (.finished, .pop), []) := by
  induction h generalizing stack with
  | @leaf r word hr hout =>
      have hchoose : g.toOneTurnNPDA.Step
          (word ++ stack, (.derive r.input, .push), stack)
          (word ++ stack, (.prefixLeaf r hr word word hout, .push), stack) := by
        apply Mathling.Automata.OneTurnNPDA.Step.epsilon
        change LinearRawStep g _ _ _ _ _ _ _
        exact LinearRawStep.chooseLeaf hr hout
      have hconsume := consumeLeaf_reaches g (r := r) (hr := hr)
        (word := word) (hout := hout) word stack stack
      have hpop : g.toOneTurnNPDA.Step
          (stack, (.prefixLeaf r hr word [] hout, .push), stack)
          (stack, (.matchStack, .pop), stack) := by
        apply Mathling.Automata.OneTurnNPDA.Step.epsilon
        change LinearRawStep g _ _ _ _ _ _ _
        exact LinearRawStep.finishLeaf
      exact ((Relation.ReflTransGen.single hchoose).trans hconsume).tail hpop
        |>.trans (matchStack_reaches g stack)
  | @branch r pre suffix middle B hr hout child ih =>
      have hchoose : g.toOneTurnNPDA.Step
          ((pre ++ middle ++ suffix) ++ stack, (.derive r.input, .push), stack)
          ((pre ++ middle ++ suffix) ++ stack,
            (.prefixBranch r hr pre pre B suffix hout, .push), stack) := by
        apply Mathling.Automata.OneTurnNPDA.Step.epsilon
        change LinearRawStep g _ _ _ _ _ _ _
        exact LinearRawStep.chooseBranch hr hout
      have hconsume := consumeBranch_reaches g (r := r) (hr := hr)
        (pre := pre) (B := B) (suffix := suffix) (hout := hout)
        pre (middle ++ suffix ++ stack) stack
      have hbegin : g.toOneTurnNPDA.Step
          (middle ++ suffix ++ stack,
            (.prefixBranch r hr pre [] B suffix hout, .push), stack)
          (middle ++ suffix ++ stack,
            (.pushBranch B suffix suffix.reverse, .push), stack) := by
        apply Mathling.Automata.OneTurnNPDA.Step.epsilon
        change LinearRawStep g _ _ _ _ _ _ _
        exact LinearRawStep.beginPush
      have hpush := pushBranch_reaches g B suffix suffix.reverse
        (middle ++ suffix ++ stack) stack
      have hpush' : g.toOneTurnNPDA.Reaches
          (middle ++ suffix ++ stack,
            (.pushBranch B suffix suffix.reverse, .push), stack)
          (middle ++ suffix ++ stack, (.derive B, .push), suffix ++ stack) := by
        simpa using hpush
      have hchild := ih (suffix ++ stack)
      exact ((Relation.ReflTransGen.single hchoose).trans
        (by simpa [List.append_assoc] using hconsume)).tail hbegin
        |>.trans hpush' |>.trans (by simpa [List.append_assoc] using hchild)

```

## 逆方向：受理から生成木を復元する不変条件

逆向きの含意——PDA が入力を受理するならば、その入力は文法から生成される——を示すには、実行列を終点から始点へ向かって逆にたどりながら、各中間状態に「これまでの入力とスタックの内容が、ある生成木と整合している」という不変条件を保つ必要がある。`LinearGood` はこの不変条件を制御状態ごとに場合分けして定義する。

```math
\begin{aligned}
\mathrm{LinearGood}(\texttt{derive}\ A,\ \texttt{push})(\text{input},\text{stack})
  &\iff \exists\ \text{word},\ \text{input} = \text{word} \mathbin{+\!\!+} \text{stack} \land \mathrm{LinearGenerates}\ A\ \text{word} \\
\mathrm{LinearGood}(\texttt{prefixLeaf}\ \cdots\ \text{todo}\ \cdots,\ \texttt{push})(\text{input},\text{stack})
  &\iff \text{input} = \text{todo} \mathbin{+\!\!+} \text{stack} \\
\mathrm{LinearGood}(\texttt{prefixBranch}\ \cdots\ \text{todo}\ B\ \text{suffix}\ \cdots,\ \texttt{push})(\text{input},\text{stack})
  &\iff \exists\ \text{middle},\ \mathrm{LinearGenerates}\ B\ \text{middle} \land
     \text{input} = \text{todo} \mathbin{+\!\!+} \text{middle} \mathbin{+\!\!+} \text{suffix} \mathbin{+\!\!+} \text{stack} \\
\mathrm{LinearGood}(\texttt{pushBranch}\ B\ \_\ \text{todo},\ \texttt{push})(\text{input},\text{stack})
  &\iff \exists\ \text{middle},\ \mathrm{LinearGenerates}\ B\ \text{middle} \land
     \text{input} = \text{middle} \mathbin{+\!\!+} \text{todo.reverse} \mathbin{+\!\!+} \text{stack} \\
\mathrm{LinearGood}(\texttt{matchStack},\ \texttt{pop})(\text{input},\text{stack})
  &\iff \text{input} = \text{stack} \\
\mathrm{LinearGood}(\texttt{finished}, \_)(\text{input}, \_)
  &\iff \text{input} = []
\end{aligned}
```

各節はちょうど、`generates_reaches` の対応する部品がその状態から出発するときに仮定していた事実を、逆向きに回収できる形になっている。たとえば `derive A` における `∃ word, ...` は `generates_reaches` の出発点そのものであり、`prefixBranch`／`pushBranch` に埋め込まれた `∃ middle, LinearGenerates g B middle` は、子の非終端の生成がまだ完了していないことと、完了した暁にはどの終端列に置き換わるかを同時に記録している。それ以外の状態と位相の組み合わせ（本来到達し得ない組）には `False` を割り当て、健全性をそもそも型で保証している。

```lean
private def LinearGood (g : LinearGrammar T) :
    Mathling.Automata.OneTurnNPDA.ID T (LinearPDAState g) T → Prop
  | (input, (.derive A, .push), stack) =>
      ∃ word, input = word ++ stack ∧ LinearGenerates g A word
  | (input, (.prefixLeaf _ _ _ todo _, .push), stack) =>
      input = todo ++ stack
  | (input, (.prefixBranch _ _ _ todo B suffix _, .push), stack) =>
      ∃ middle, LinearGenerates g B middle ∧
        input = todo ++ middle ++ suffix ++ stack
  | (input, (.pushBranch B _ todo, .push), stack) =>
      ∃ middle, LinearGenerates g B middle ∧
        input = middle ++ todo.reverse ++ stack
  | (input, (.matchStack, .pop), stack) => input = stack
  | (input, (.finished, _), _) => input = []
  | _ => False

```

`raw_step_good` は `LinearRawStep` の各構成子について、遷移後の状態で `LinearGood` が成り立つならば遷移前の状態でも成り立つことを１ステップずつ確認する。これは各ミクロ遷移が `LinearGood` の場合分けとちょうど噛み合うように設計されていることの裏付けであり、たとえば `consumeLeaf` は `todo` の１文字消費に対応して入力の１文字消費が起こるだけなので `simp` で閉じ、`chooseBranch` は規則の出力を非終端記号の生成木へ組み替える証明の要となる。`step_good` はこれを `OneTurnNPDA.Step`（`consume`／`epsilon` の２通り）に持ち上げ、`reaches_good` はさらに `Reaches`（反射推移閉包）全体へ、終点から始点への逆向き帰納法（`head_induction_on`）で持ち上げる。この結果、実行列の終点における不変条件（受理状態での `input = []`）さえ分かれば、始点における不変条件を機械的に導けるようになる。

```lean
@[grind .] private theorem raw_step_good (g : LinearGrammar T)
    {q q' : LinearPDAState g} {p p' : Mathling.Automata.TurnPhase}
    {sym : Option T} {stack stack' : List T}
    (h : LinearRawStep g q p sym stack q' p' stack') (input : List T) :
    LinearGood g (input, (q', p'), stack') →
      LinearGood g
        ((match sym with | none => input | some a => a :: input), (q, p), stack) := by
  cases h with
  | @chooseLeaf r word stack hr hout =>
      intro hinput
      exact ⟨word, hinput, LinearGenerates.leaf hr hout⟩
  | @chooseBranch r pre B suffix stack hr hout =>
      rintro ⟨middle, hmiddle, hinput⟩
      refine ⟨pre ++ middle ++ suffix, ?_, LinearGenerates.branch hr hout hmiddle⟩
      simpa [List.append_assoc] using hinput
  | consumeLeaf =>
      simp [LinearGood]
  | consumeBranch =>
      simp [LinearGood, List.append_assoc]
  | finishLeaf =>
      simp [LinearGood]
  | beginPush =>
      simp [LinearGood, List.append_assoc]
  | push =>
      simp [LinearGood, List.reverse_cons, List.append_assoc]
  | «continue» =>
      rintro ⟨middle, hinput, hmiddle⟩
      exact ⟨middle, hmiddle, by simpa using hinput⟩
  | matchStack =>
      simp [LinearGood]
  | finish =>
      simp [LinearGood]

@[grind .] private theorem step_good (g : LinearGrammar T)
    {c c' : Mathling.Automata.OneTurnNPDA.ID T (LinearPDAState g) T}
    (h : g.toOneTurnNPDA.Step c c') :
    LinearGood g c' → LinearGood g c := by
  cases h with
  | consume hraw =>
      change LinearRawStep g _ _ _ _ _ _ _ at hraw
      exact raw_step_good g hraw _
  | epsilon hraw =>
      change LinearRawStep g _ _ _ _ _ _ _ at hraw
      exact raw_step_good g hraw _

@[grind .] private theorem reaches_good (g : LinearGrammar T)
    {c c' : Mathling.Automata.OneTurnNPDA.ID T (LinearPDAState g) T}
    (h : g.toOneTurnNPDA.Reaches c c') :
    LinearGood g c' → LinearGood g c := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact id
  | head hstep _ ih =>
      intro hgood
      exact step_good g hstep (ih hgood)

```

## 主定理：構成した PDA の言語と文法の言語の一致

`toOneTurnNPDA_language` は、これまでの２方向の議論をそれぞれ適用して主張を完成させる。`⊆` 方向では、受理実行列の始点 `(input, (.derive g.cfg.initial, .push), [])` に `reaches_good` を適用し、得られる `LinearGood` の中身（ある終端列 `word` について `input = word` かつ `LinearGenerates g g.cfg.initial word`）から `linearGenerates_iff` を経由して `input ∈ g.language` を得る。`⊇` 方向では `linearGenerates_iff` で得た生成木に `generates_reaches` を適用し、空スタックから空スタックへ戻る受理実行列を直接構成する。こうして、生成規則を１本ずつ制御状態として持つという非常に具体的な PDA 構成が、文法の言語をちょうど過不足なく受理することが示される。

```lean
/-- The local one-turn PDA accepts exactly the language generated by the linear grammar. -/
@[important, grind =, simp] public theorem toOneTurnNPDA_language (g : LinearGrammar T) :
    g.toOneTurnNPDA.language = g.language := by
  ext input
  constructor
  · intro hinput
    change g.toOneTurnNPDA.Accepts input at hinput
    rcases hinput with ⟨start, hstart, final, hfinal, finalPhase, stack, hreach⟩
    change start ∈ ({.derive g.cfg.initial} : Set (LinearPDAState g)) at hstart
    simp only [Set.mem_singleton_iff] at hstart
    subst start
    change final ∈ g.toOneTurnNPDA.accept at hfinal
    change final ∈ ({.finished} : Set (LinearPDAState g)) at hfinal
    simp only [Set.mem_singleton_iff] at hfinal
    subst final
    have hgood : LinearGood g
        (input, (.derive g.cfg.initial, .push), []) :=
      reaches_good g hreach (by simp [LinearGood])
    rcases hgood with ⟨word, hword, hgenerates⟩
    simp only [List.append_nil] at hword
    subst input
    exact (linearGenerates_iff g word).mp hgenerates
  · intro hinput
    have hgenerates := (linearGenerates_iff g input).mpr hinput
    change g.toOneTurnNPDA.Accepts input
    refine ⟨.derive g.cfg.initial, ?_, .finished, ?_, .pop, [], ?_⟩
    · simp [toOneTurnNPDA]
    · simp [toOneTurnNPDA]
    · simpa [toOneTurnNPDA] using
        generates_reaches g hgenerates []

```

以上で線形文法に対する production-tree 意味論と一回転 NPDA 構成の証明が完結したため、開いていた `namespace` を閉じる。

```lean
end LinearGrammar

end Mathling.Grammar

```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
