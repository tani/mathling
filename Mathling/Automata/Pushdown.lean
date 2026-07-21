    module

    public import Mathling.Automata.Core

    import LiterateLean
    open scoped LiterateLean


# Mathling / Automata / Pushdown モジュール

局所遷移で記述した非決定性プッシュダウン・オートマトンと一回転 NPDA の実行意味論を定める。構成、反射推移閉包による実行、受理条件、言語という順に公開し、文法変換側が参照する機械モデルの境界を固定する。

```lean
/-!
# Pushdown automata

Nondeterministic, deterministic, and one-turn pushdown automata.
-/



namespace Mathling.Automata

/-- One local pushdown rule: inspect one stack symbol, optionally consume one
input symbol, and replace the inspected symbol by a finite stack word. -/


@[ext] public structure PushdownRule (α State Stack : Type*) where
  source : State
  input : Option α
  pop : Stack
  target : State
  push : List Stack
```

`NPDA` は `PushdownRule` の有限列と、開始・受理状態集合、初期スタックをまとめたデータである。規則が有限列であることが後続のすべての証明（有限支持集合 `stackSupport`、正規化の停止性など）の基盤になる——無限規則集合を許すと決定不能な境界になってしまう。

```lean
/-- A nondeterministic pushdown automaton presented by a finite rule list. -/
@[ext] public structure NPDA (α State Stack : Type*) where
  rules : List (PushdownRule α State Stack)
  start : List State
  accept : List State
  initialStack : List Stack
```

以降の実行意味論は、すべて `NPDA` 名前空間の下にまとめて公開する。こうして「構成 → 反射推移閉包による実行 → 受理条件 → 言語」という順序が名前空間の構造そのものに現れ、利用側は `NPDA.` を通じてのみこれらへアクセスする。

```lean
namespace NPDA

```

瞬間記述 `ID` は「未読入力・現在の状態・現在のスタック」の三つ組であり、以降のすべての遷移関係・到達関係・不変条件はこの型を土台にして定義される。

```lean
variable {α State Stack : Type*}

/-- An instantaneous description: unread input, control state, and stack. -/
public abbrev ID (α State Stack : Type*) := List α × State × List Stack
```

`Step` は局所規則を1回適用する遷移関係で、入力記号を1つ消費する `consume` と、入力を読まない `epsilon` の2種類のコンストラクタを持つ。どちらもスタック先頭の1記号 `pop` を要求し、それを `push` で置き換える——この局所性こそが `PushdownRule` の設計意図であり、以降の反射推移閉包・受理条件はすべてこの一段階遷移の閉包として定義される。

```lean
/-- One consuming or epsilon application of a local pushdown rule. -/
@[grind cases] public inductive Step (M : NPDA α State Stack) :
    ID α State Stack → ID α State Stack → Prop
  | consume {a : α} {input : List α} {stack : List Stack}
      (rule : PushdownRule α State Stack) (mem : rule ∈ M.rules)
      (input_eq : rule.input = some a) :
      Step M (a :: input, rule.source, rule.pop :: stack)
        (input, rule.target, rule.push ++ stack)
  | epsilon {input : List α} {stack : List Stack}
      (rule : PushdownRule α State Stack) (mem : rule ∈ M.rules)
      (input_eq : rule.input = none) :
      Step M (input, rule.source, rule.pop :: stack)
        (input, rule.target, rule.push ++ stack)
```

`Reaches` は `Step` の反射推移閉包であり、複数回の局所遷移を一つの実行としてまとめる。受理条件や変換定理はすべて個々の `Step` ではなくこの `Reaches` を単位にして述べられるため、ここが「1ステップの意味論」から「実行全体の意味論」への橋渡しになる。

```lean
/-- Zero or more local transitions. -/
public abbrev Reaches (M : NPDA α State Stack) := Relation.ReflTransGen M.Step
```

`Accepts` はある開始状態・受理状態の組と残余スタックが存在して、全入力を消費する実行が到達可能であることとして受理を定める。本体を `@[expose]` にしているのは、文法変換側の証明が受理の存在証明を分解し、`Reaches` の到達証拠として再構成する必要があるためである。

```lean
/-- Acceptance by a local NPDA.

Its body is exposed because public grammar conversions destruct acceptance
witnesses and reconstruct them as reachability witnesses. -/


@[expose] public def Accepts (M : NPDA α State Stack) (w : List α) : Prop :=
  ∃ q₀ ∈ M.start, ∃ qf ∈ M.accept, ∃ stack,
    M.Reaches (w, q₀, M.initialStack) ([], qf, stack)
```

`language` は `Accepts` を集合内包で言語へ持ち上げるだけの薄いラッパーだが、この境界を固定することで文法変換モジュールは `Accepts` の構造ではなく `language` の等式だけを見ればよくなる。

```lean
/-- The language accepted by a local NPDA.

Its body is exposed because public language-equivalence theorems rewrite
membership into the corresponding acceptance predicate. -/


@[expose] public def language (M : NPDA α State Stack) : Language α := {w | M.Accepts w}
```

`Balanced` と `StackBalanced` は、局所遷移から「文法規則の生成物のように振る舞う」木構造の実行を切り出すための相互再帰的な述語である。`Balanced` はスタック先頭1記号をちょうど1回分の入れ替えとして消費し尽くす実行を、`StackBalanced` はその列をスタック語全体に拡張する。両者を分けて定義するのは、後続の文法変換が「1記号あたりの生成規則」を単位に構成規則を書き下すため、その単位に対応する実行の形が独立に必要になるからである。

```lean
mutual
  /-- A run that removes one designated top symbol while preserving an
  arbitrary stack suffix. -/


  @[grind cases] public inductive Balanced (M : NPDA α State Stack) :
      State → Stack → State → List α → Prop
    | rule {q : State} {childWord : List α}
        (r : PushdownRule α State Stack) (mem : r ∈ M.rules)
        (children : StackBalanced M r.target r.push q childWord) :
        Balanced M r.source r.pop q (r.input.toList ++ childWord)

  /-- A sequence of balanced runs that removes a complete stack word. -/
  @[grind cases] public inductive StackBalanced (M : NPDA α State Stack) :
      State → List Stack → State → List α → Prop
    | nil (q : State) : StackBalanced M q [] q []
    | cons {p mid q : State} {top : Stack} {stack : List Stack}
        {u v : List α} (head : Balanced M p top mid u)
        (tail : StackBalanced M mid stack q v) :
        StackBalanced M p (top :: stack) q (u ++ v)
end
```

`Balanced.reaches` は `Balanced` の帰納的定義を具体的な `Reaches` 実行に翻訳する健全性の半分であり、任意の未読入力 `input` と任意の未使用スタック接尾 `suffix` を後ろに付け足せることを相互帰納法（`motive_1`/`motive_2`）で同時に証明する。この汎化がないと帰納法の仮定が弱すぎて証明が回らない。

```lean
/-- A balanced one-symbol computation induces a concrete run with arbitrary
unread input and an arbitrary untouched stack suffix. -/


@[grind .] public theorem Balanced.reaches {M : NPDA α State Stack}
    {p q : State} {top : Stack} {word : List α}
    (h : Balanced M p top q word)
    (input : List α) (suffix : List Stack) :
    M.Reaches (word ++ input, p, top :: suffix) (input, q, suffix) := by
  refine Balanced.rec (M := M)
    (motive_1 := fun p top q word _ => ∀ input suffix,
      M.Reaches (word ++ input, p, top :: suffix) (input, q, suffix))
    (motive_2 := fun p stack q word _ => ∀ input suffix,
      M.Reaches (word ++ input, p, stack ++ suffix) (input, q, suffix))
    ?_ ?_ ?_ h input suffix
  · intro q childWord r mem children ih input suffix
    cases hi : r.input with
    | none =>
        simpa [hi] using Relation.ReflTransGen.head
          (Step.epsilon r mem hi (input := childWord ++ input) (stack := suffix))
          (ih input suffix)
    | some a =>
        simpa [hi] using Relation.ReflTransGen.head
          (Step.consume r mem hi (input := childWord ++ input) (stack := suffix))
          (ih input suffix)
  · intro q input suffix
    exact Relation.ReflTransGen.refl
  · intro p mid q top stack u v head tail ihHead ihTail input suffix
    simpa [List.append_assoc] using
      Relation.ReflTransGen.trans (ihHead (v ++ input) (stack ++ suffix))
        (ihTail input suffix)
```

`StackBalanced.reaches` は同じ相互帰納法のもう半分で、スタック語全体を1本の実行へ翻訳する。証明本体は `Balanced.reaches` と同一の `rec` 呼び出しを共有しており、実質的には両定理が一つの相互帰納証明を別々の主張として取り出したものである。

```lean
/-- A balanced stack-word computation induces a concrete run. -/
@[grind .] theorem StackBalanced.reaches {M : NPDA α State Stack}
    {p q : State} {stack : List Stack} {word : List α}
    (h : StackBalanced M p stack q word)
    (input : List α) (suffix : List Stack) :
    M.Reaches (word ++ input, p, stack ++ suffix) (input, q, suffix) := by
  refine StackBalanced.rec (M := M)
    (motive_1 := fun p top q word _ => ∀ input suffix,
      M.Reaches (word ++ input, p, top :: suffix) (input, q, suffix))
    (motive_2 := fun p stack q word _ => ∀ input suffix,
      M.Reaches (word ++ input, p, stack ++ suffix) (input, q, suffix))
    ?_ ?_ ?_ h input suffix
  · intro q childWord r mem children ih input suffix
    cases hi : r.input with
    | none =>
        simpa [hi] using Relation.ReflTransGen.head
          (Step.epsilon r mem hi (input := childWord ++ input) (stack := suffix))
          (ih input suffix)
    | some a =>
        simpa [hi] using Relation.ReflTransGen.head
          (Step.consume r mem hi (input := childWord ++ input) (stack := suffix))
          (ih input suffix)
  · intro q input suffix
    exact Relation.ReflTransGen.refl
  · intro p mid q top stack u v head tail ihHead ihTail input suffix
    simpa [List.append_assoc] using
      Relation.ReflTransGen.trans (ihHead (v ++ input) (stack ++ suffix))
        (ihTail input suffix)
```

## 有限局所規則と受理形の正規化

`NPDA` の公開表現は、スタック先頭の1記号を取り除き、有限列 `push` で置き換える局所規則の有限列である。`Balanced` と `StackBalanced` は、スタックの未使用接尾を保存しながら、1記号または記号列全体を取り除く実行を表す。この局所性が、後続の文法変換で有限な生成規則を得るための境界となる。

`finalToEmpty` は底記号 `bottom` と `boot` / `sim` / `drain` / `done` の制御局面を追加する。元の受理状態へ到達した後だけ `drain` へ移り、支持集合上のスタック記号を排出して、底記号を取り除いたときに限り `done` に入る。`FinalStackGood` は底記号が最終遷移まで一意に保たれる不変条件を記録し、受理状態と空スタックの同値を保証する。

```lean
/-- Fresh control states used to turn final-state acceptance into empty-stack
acceptance. -/


@[grind cases] public inductive FinalState (State : Type*) where
  | boot
  | sim (state : State)
  | drain
  | done
  deriving Repr, DecidableEq
```

`FinalStack` は元のスタック記号を `old` で包み、それとは別に一意な `bottom` 底記号を追加する。この分離のおかげで「元のスタックが空になった」ことと「底記号だけが残っている」ことを型レベルで区別でき、`FinalStackGood` のような不変条件が構成しやすくなる。

```lean
/-- Fresh bottom marker plus embedded symbols of the original stack alphabet. -/
@[grind cases] public inductive FinalStack (Stack : Type*) where
  | bottom
  | old (symbol : Stack)
  deriving Repr, DecidableEq
```

`stackSupport` は初期スタックと全規則の `pop`/`push` から現れうるスタック記号を静的に有限枚挙する。`drainRules` はこの支持集合ぶんの規則しか生成しないため、実際の実行で現れるスタック記号がここに含まれることを保証する `StackSupported` 系の補題（後述）なしには排出フェーズの完全性が成り立たない。

```lean
/-- Every stack symbol that can occur in a run from the declared initial
stack. -/


def stackSupport (M : NPDA α State Stack) : List Stack :=
  M.initialStack ++ M.rules.flatMap fun r => r.pop :: r.push
```

以下の `Internal` 名前空間は `finalToEmpty` を構成する規則族を6種類に分けて定義する。これらは公開 API ではなく、`finalToEmpty` の定義と、生成された規則を分類する `finalRule_cases` からのみ参照される実装の詳細である。`bootRules` はただ一つの新しい開始状態 `.boot` から、各元の開始状態 `q` の `.sim q` へ、底記号越しに初期スタックを積んで遷移する。

```lean
namespace Internal

public def bootRules (M : NPDA α State Stack) :
    List (PushdownRule α (FinalState State) (FinalStack Stack)) :=
  M.start.map fun q =>
    { source := .boot, input := none, pop := .bottom, target := .sim q
      push := M.initialStack.map FinalStack.old ++ [.bottom] }
```

`simulationRules` は元の各規則を `.sim` 局面の中でそのまま再現する。スタック記号だけを `FinalStack.old` で包み直し、底記号を触らない——これにより元の機械の実行が正規化後の機械の中でそっくり複製される。

```lean
public def simulationRules (M : NPDA α State Stack) :
    List (PushdownRule α (FinalState State) (FinalStack Stack)) :=
  M.rules.map fun r =>
    { source := .sim r.source, input := r.input, pop := .old r.pop
      target := .sim r.target, push := r.push.map FinalStack.old }
```

`enterDrainRules` は各受理状態 `q` と支持集合中の各スタック記号 `x` の組ごとに、`.sim q` から `.drain` へ抜ける epsilon 規則を生成する。受理状態に到達した直後だけ排出局面へ入れることが、「最終状態受理」と「空スタック受理」の同値性の要となる。

```lean
public def enterDrainRules (M : NPDA α State Stack) :
    List (PushdownRule α (FinalState State) (FinalStack Stack)) :=
  M.accept.flatMap fun q => M.stackSupport.map fun x =>
    { source := .sim q, input := none, pop := .old x
      target := .drain, push := [] }
```

`acceptBottomRules` は排出すべき `old` 記号が残っていない場合、つまり元のスタックが既に空だった場合に、底記号を直接取り除いて `.done` へ入る近道を用意する。この規則がないと空スタックで受理した実行が `drain` を経由できず取りこぼされる。

```lean
public def acceptBottomRules (M : NPDA α State Stack) :
    List (PushdownRule α (FinalState State) (FinalStack Stack)) :=
  M.accept.map fun q =>
    { source := .sim q, input := none, pop := .bottom
      target := .done, push := [] }
```

`drainRules` は `.drain` 局面にいる間、支持集合上の任意の `old` 記号を1つずつ取り除き続けられるようにする。支持集合全体を対象にしているのは、受理時点でスタックに残っている記号が静的解析で先取りできないため、起こりうる全記号に対して排出経路を用意しておく必要があるからである。

```lean
public def drainRules (M : NPDA α State Stack) :
    List (PushdownRule α (FinalState State) (FinalStack Stack)) :=
  M.stackSupport.map fun x =>
    { source := .drain, input := none, pop := .old x
      target := .drain, push := [] }
```

`finishDrainRule` は排出が完了し底記号だけが残った状態で、最後に底記号自体を取り除いて `.done` へ入る唯一の規則である。`drainRules` が「支持集合の記号を取り除く」規則であるのに対し、これは底記号専用の特別扱いであり、両者が揃って初めてスタック全体を空にできる。

```lean
public def finishDrainRule :
    PushdownRule α (FinalState State) (FinalStack Stack) :=
  { source := .drain, input := none, pop := .bottom
    target := .done, push := [] }

end Internal
```

`finalToEmpty` は前段で定義した6種類の内部規則族を連結し、開始状態を一意な `.boot`、受理状態を一意な `.done`、初期スタックを底記号1枚に固定した新しい `NPDA` を組み立てる。この構成が、後段の `finalToEmpty_language` によって元の言語を保つことが証明される。

```lean
/-- Convert final-state acceptance into empty-stack acceptance.

Its body is exposed because public conversion theorems simplify its generated
rules and endpoints when transporting accepting runs. -/


@[expose] public def finalToEmpty (M : NPDA α State Stack) :
    NPDA α (FinalState State) (FinalStack Stack) where
  rules := Internal.bootRules M ++ Internal.simulationRules M ++
    Internal.enterDrainRules M ++ Internal.acceptBottomRules M ++
    Internal.drainRules M ++ [Internal.finishDrainRule]
  start := [.boot]
  accept := [.done]
  initialStack := [.bottom]
```

`FinalStackGood` は `finalToEmpty` が生成した機械の到達可能な構成が満たす形状不変条件を、制御状態ごとに場合分けして記述する。`boot`/`sim`/`drain` では底記号がスタック末尾に唯一残っており、`done` でのみスタックが完全に空になる。この不変条件があるおかげで、正規化後の実行から元の実行を復元する際にスタックの形を仮定として使える。

```lean
/-- Reachable normalized configurations keep exactly one bottom marker until
the final transition removes it.

Its body is exposed because public conversion proofs simplify the invariant
at the final configuration to recover an empty stack. -/


@[expose] public def FinalStackGood :
    ID α (FinalState State) (FinalStack Stack) → Prop
  | (_, .boot, stack) => stack = [.bottom]
  | (_, .sim _, stack) | (_, .drain, stack) =>
      ∃ oldStack : List Stack,
        stack = oldStack.map FinalStack.old ++ [.bottom]
  | (_, .done, stack) => stack = []
```

`finalRule_cases` は `finalToEmpty.rules` の所属を6つの規則族のいずれか一つの具体的な形へ分解する。以降のすべての「どの規則が使われたか」に基づく場合分け証明（`finalStep_run_good` など）はこの補題を通じて `rules` の定義展開を一度きりで済ませる。

```lean
/-- Exhaustive classification of the six families of normalization rules. -/
@[grind .] theorem finalRule_cases (M : NPDA α State Stack)
    {r : PushdownRule α (FinalState State) (FinalStack Stack)}
    (hr : r ∈ M.finalToEmpty.rules) :
    (∃ q ∈ M.start, r =
      { source := .boot, input := none, pop := .bottom, target := .sim q
        push := M.initialStack.map FinalStack.old ++ [.bottom] }) ∨
    (∃ old ∈ M.rules, r =
      { source := .sim old.source, input := old.input, pop := .old old.pop
        target := .sim old.target, push := old.push.map FinalStack.old }) ∨
    (∃ q ∈ M.accept, ∃ x ∈ M.stackSupport, r =
      { source := .sim q, input := none, pop := .old x
        target := .drain, push := [] }) ∨
    (∃ q ∈ M.accept, r =
      { source := .sim q, input := none, pop := .bottom
        target := .done, push := [] }) ∨
    (∃ x ∈ M.stackSupport, r =
      { source := .drain, input := none, pop := .old x
        target := .drain, push := [] }) ∨
    r = Internal.finishDrainRule := by
  simp only [finalToEmpty, List.mem_append, List.mem_singleton] at hr
  rcases hr with ((((hr | hr) | hr) | hr) | hr) | hr
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
    exact Or.inl ⟨q, hq, rfl⟩
  · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hr
    exact Or.inr (Or.inl ⟨old, hold, rfl⟩)
  · obtain ⟨q, hq, hinner⟩ := List.mem_flatMap.mp hr
    obtain ⟨x, hx, heq⟩ := List.mem_map.mp hinner
    subst r
    exact Or.inr (Or.inr (Or.inl ⟨q, hq, x, hx, rfl⟩))
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨q, hq, rfl⟩)))
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨x, hx, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hr))))
```

`StackSupported` を満たすスタックだけが排出フェーズ (`drainRules`) で確実に処理できる。以降の一連の補題は、初期スタックから到達可能などんな構成のスタックも常にこの述語を満たし続けることを積み上げて示し、最終的に `finalToEmpty_language` で排出が失敗しないことの根拠になる。

```lean
/-- Every symbol in a stack belongs to the machine's finite stack support. -/
def StackSupported (M : NPDA α State Stack) (stack : List Stack) : Prop :=
  ∀ x ∈ stack, x ∈ M.stackSupport
```

初期スタックの記号は `stackSupport` の定義そのものに含まれているので、出発点は自明に支持される。

```lean
@[grind .] theorem initialStack_supported (M : NPDA α State Stack) :
    M.StackSupported M.initialStack := by
  intro x hx
  exact List.mem_append_left _ hx

```

規則が消費するスタック先頭記号 `pop` もまた `stackSupport` に含まれる、という単純だが以降の帰納法の要となる事実。

```lean
@[grind .] theorem rule_pop_mem_stackSupport (M : NPDA α State Stack)
    {r : PushdownRule α State Stack} (hr : r ∈ M.rules) :
    r.pop ∈ M.stackSupport := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  exact ⟨r, hr, by simp⟩

```

規則が積む記号列 `push` の各記号も同様に支持集合に含まれる。`rule_pop_mem_stackSupport` と対になって、1回の遷移で消費される記号と生成される記号の双方が有限な支持集合に収まることを保証する。

```lean
@[grind .] theorem rule_push_supported (M : NPDA α State Stack)
    {r : PushdownRule α State Stack} (hr : r ∈ M.rules) :
    M.StackSupported r.push := by
  intro x hx
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  exact ⟨r, hr, by simp [hx]⟩

```

`StackSupported` が1回の `Step` で保存されることを示す。消費された先頭記号は捨てられ、新たに積まれた記号は `rule_push_supported` により支持され、残りの接尾は仮定からそのまま支持される。

```lean
@[grind .] theorem Step.stack_supported {M : NPDA α State Stack}
    {c c' : ID α State Stack} (h : M.Step c c') :
    M.StackSupported c.2.2 → M.StackSupported c'.2.2 := by
  cases h with
  | @consume a input tail r hr input_eq =>
      intro hs x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact M.rule_push_supported hr x hx
      · exact hs x (by simp [hx])
  | @epsilon input tail r hr input_eq =>
      intro hs x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact M.rule_push_supported hr x hx
      · exact hs x (by simp [hx])

```

1ステップの保存を反射推移閉包へ持ち上げ、任意の到達可能な構成のスタックが常に支持されることを得る。これが `stackBalanced_of_reaches_to_empty` や `finalToEmpty_language` で排出フェーズの完全性を示す際に使われる。

```lean
@[grind .] theorem Reaches.stack_supported {M : NPDA α State Stack}
    {c c' : ID α State Stack} (h : M.Reaches c c') :
    M.StackSupported c.2.2 → M.StackSupported c'.2.2 := by
  induction h with
  | refl => exact id
  | tail h step ih => exact fun hs => step.stack_supported (ih hs)

```

ここから先の一群の補題は、`finalRule_cases` が挙げる6種類の規則それぞれが実際に `finalToEmpty.rules` の要素であることを個別に確認する所属補題である。`finalRule_cases` が逆方向（要素ならばこの形）を示すのに対し、これらは順方向（この形なら要素）を示し、両者が揃って規則集合の完全な特徴づけを与える。`bootRule_mem` は生成された `.boot` 起動規則がちょうど `bootRules` の像に一致することを確認する。

```lean
@[grind .] theorem bootRule_mem (M : NPDA α State Stack)
    {q : State} (hq : q ∈ M.start) :
    ({ source := .boot, input := none, pop := .bottom, target := .sim q
       push := M.initialStack.map FinalStack.old ++ [.bottom] } :
      PushdownRule α (FinalState State) (FinalStack Stack)) ∈
      M.finalToEmpty.rules := by
  simp [finalToEmpty, Internal.bootRules, hq]

```

`simulationRule_mem` は元の任意の規則 `r` を `.sim` 局面へ持ち上げた版が、確かに `finalToEmpty.rules` に含まれることを確認する。この所属補題が `Step.finalToEmpty`（後述）で元の遷移を正規化後の遷移として再構成する際の唯一の根拠になる。

```lean
@[grind .] theorem simulationRule_mem (M : NPDA α State Stack)
    {r : PushdownRule α State Stack} (hr : r ∈ M.rules) :
    ({ source := .sim r.source, input := r.input, pop := .old r.pop
       target := .sim r.target, push := r.push.map FinalStack.old } :
      PushdownRule α (FinalState State) (FinalStack Stack)) ∈
      M.finalToEmpty.rules := by
  simp only [finalToEmpty, List.mem_append, List.mem_singleton]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
    (List.mem_map.mpr ⟨r, hr, rfl⟩)))))

```

`enterDrainRule_mem` は特定の受理状態・支持記号の組に対応する排出開始規則が `finalToEmpty.rules` に属することを示し、`drain_reaches_done` が排出列を1歩ずつ構成する際に使われる。

```lean
@[grind .] theorem enterDrainRule_mem (M : NPDA α State Stack)
    {q : State} (hq : q ∈ M.accept) {x : Stack}
    (hx : x ∈ M.stackSupport) :
    ({ source := .sim q, input := none, pop := .old x
       target := .drain, push := [] } :
      PushdownRule α (FinalState State) (FinalStack Stack)) ∈
      M.finalToEmpty.rules := by
  simp [finalToEmpty, Internal.enterDrainRules, hq, hx]

```

`acceptBottomRule_mem` は空スタックで受理する近道規則の所属を保証し、`finalToEmpty_language` の証明で「排出すべき記号が残っていない」場合の分岐に使われる。

```lean
@[grind .] theorem acceptBottomRule_mem (M : NPDA α State Stack)
    {q : State} (hq : q ∈ M.accept) :
    ({ source := .sim q, input := none, pop := .bottom
       target := .done, push := [] } :
      PushdownRule α (FinalState State) (FinalStack Stack)) ∈
      M.finalToEmpty.rules := by
  simp [finalToEmpty, Internal.acceptBottomRules, hq]

```

`drainRule_mem` は排出継続規則の所属を保証し、`drain_reaches_done` の帰納法の各コンス段階でスタック記号を1つずつ取り除く根拠として使われる。

```lean
@[grind .] theorem drainRule_mem (M : NPDA α State Stack)
    {x : Stack} (hx : x ∈ M.stackSupport) :
    ({ source := .drain, input := none, pop := .old x
       target := .drain, push := [] } :
      PushdownRule α (FinalState State) (FinalStack Stack)) ∈
      M.finalToEmpty.rules := by
  simp [finalToEmpty, Internal.drainRules, hx]

```

`finishDrainRule_mem` closes this group of membership lemmas: it confirms the single bottom-removing rule is present, giving `drain_reaches_done` its base case.

```lean
@[grind .] theorem finishDrainRule_mem (M : NPDA α State Stack) :
    (Internal.finishDrainRule :
      PushdownRule α (FinalState State) (FinalStack Stack)) ∈
      M.finalToEmpty.rules := by
  simp [finalToEmpty]
```

With every regenerated rule now confirmed to belong to `finalToEmpty.rules`, the next pair of theorems lift entire original computations into the `.sim` simulation phase, one step at a time and then by induction over `Reaches`.

```lean
/-- Lift one original local transition into the simulation phase. -/
@[grind .] theorem Step.finalToEmpty {M : NPDA α State Stack}
    {c c' : ID α State Stack} (h : M.Step c c') :
    M.finalToEmpty.Step
      (c.1, FinalState.sim c.2.1,
        c.2.2.map FinalStack.old ++ [FinalStack.bottom])
      (c'.1, FinalState.sim c'.2.1,
        c'.2.2.map FinalStack.old ++ [FinalStack.bottom]) := by
  cases h with
  | @consume a input tail r hr input_eq =>
      simpa [List.map_append, List.append_assoc] using
        Step.consume
          ({ source := FinalState.sim r.source, input := r.input,
             pop := FinalStack.old r.pop, target := FinalState.sim r.target,
             push := r.push.map FinalStack.old } :
            PushdownRule α (FinalState State) (FinalStack Stack))
          (M.simulationRule_mem hr) input_eq
  | @epsilon input tail r hr input_eq =>
      simpa [List.map_append, List.append_assoc] using
        Step.epsilon
          ({ source := FinalState.sim r.source, input := r.input,
             pop := FinalStack.old r.pop, target := FinalState.sim r.target,
             push := r.push.map FinalStack.old } :
            PushdownRule α (FinalState State) (FinalStack Stack))
          (M.simulationRule_mem hr) input_eq
```

Extending the single-step lift by induction over `Reaches` gives the full-run version, so any complete original computation embeds as a `.sim`-phase computation of the normalized machine without needing to touch the drain phase yet.

```lean
/-- Lift a complete original run into the simulation phase. -/
@[grind .] theorem Reaches.finalToEmpty {M : NPDA α State Stack}
    {c c' : ID α State Stack} (h : M.Reaches c c') :
    M.finalToEmpty.Reaches
      (c.1, FinalState.sim c.2.1,
        c.2.2.map FinalStack.old ++ [FinalStack.bottom])
      (c'.1, FinalState.sim c'.2.1,
        c'.2.2.map FinalStack.old ++ [FinalStack.bottom]) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail h step ih => exact ih.tail step.finalToEmpty
```

`drain_reaches_done` is the constructive counterpart of `enterDrainRules`/`drainRules`/`finishDrainRule`: given that the embedded stack is fully within `stackSupport` (guaranteed by `Reaches.stack_supported`), it produces an explicit run that strips every remaining symbol and the bottom marker in order, ending exactly at `.done` with an empty stack.

```lean
/-- Drain a supported embedded stack and finally remove the bottom marker. -/
@[grind .] theorem drain_reaches_done (M : NPDA α State Stack)
    {input : List α} {stack : List Stack} (hs : M.StackSupported stack) :
    M.finalToEmpty.Reaches
      (input, FinalState.drain,
        stack.map FinalStack.old ++ [FinalStack.bottom])
      (input, FinalState.done, []) := by
  induction stack with
  | nil =>
      apply Relation.ReflTransGen.single
      simpa [Internal.finishDrainRule] using
        Step.epsilon Internal.finishDrainRule
        M.finishDrainRule_mem rfl
  | cons x stack ih =>
      have hx : x ∈ M.stackSupport := hs x (by simp)
      have htail : M.StackSupported stack := by
        intro y hy
        exact hs y (by simp [hy])
      have first : M.finalToEmpty.Step
          (input, FinalState.drain,
            FinalStack.old x :: stack.map FinalStack.old ++ [FinalStack.bottom])
          (input, FinalState.drain,
            stack.map FinalStack.old ++ [FinalStack.bottom]) := by
        simpa using Step.epsilon
          ({ source := FinalState.drain, input := none,
             pop := FinalStack.old x, target := FinalState.drain, push := [] } :
            PushdownRule α (FinalState State) (FinalStack Stack))
          (M.drainRule_mem hx) rfl
      exact (ih htail).head first
```

`AcceptingPrefix` records that the *original* machine can already reach one of its accept states after consuming some prefix of `word`, leaving `input` unread. It is the semantic anchor that `FinalRunGood` attaches to the `.drain` and `.done` phases below, connecting the normalized machine's bookkeeping back to a genuine original-machine acceptance witness.

```lean
/-- Original-machine acceptance evidence with a possibly unread suffix. -/
def AcceptingPrefix (M : NPDA α State Stack) (word input : List α) : Prop :=
  ∃ q₀ ∈ M.start, ∃ qf ∈ M.accept, ∃ stack,
    M.Reaches (word, q₀, M.initialStack) (input, qf, stack)
```

`FinalRunGood` is the full semantic invariant (as opposed to `FinalStackGood`'s purely syntactic stack-shape invariant): for each control phase it states not just what the stack looks like but what original-machine fact that shape witnesses — an in-progress simulated run in `.sim`, or a completed `AcceptingPrefix` once draining begins. It is preserved by `finalStep_run_good`/`finalReaches_run_good` and drives the correctness proof `finalToEmpty_language`.

```lean
/-- Semantic invariant carried by every phase of the normalized machine. -/
def FinalRunGood (M : NPDA α State Stack) (word : List α) :
    ID α (FinalState State) (FinalStack Stack) → Prop
  | (input, .boot, stack) => input = word ∧ stack = [.bottom]
  | (input, .sim q, stack) =>
      ∃ q₀ ∈ M.start, ∃ oldStack,
        stack = oldStack.map FinalStack.old ++ [.bottom] ∧
        M.Reaches (word, q₀, M.initialStack) (input, q, oldStack)
  | (input, .drain, stack) =>
      (∃ oldStack : List Stack,
        stack = oldStack.map FinalStack.old ++ [.bottom]) ∧
      M.AcceptingPrefix word input
  | (input, .done, stack) =>
      stack = [] ∧ M.AcceptingPrefix word input
```

`old_cons_parts` is a small inversion lemma: whenever an embedded stack `oldStack.map FinalStack.old ++ [.bottom]` happens to start with an `.old x` symbol, it recovers the underlying original stack `x :: rest` and the corresponding embedded tail. This unwrapping step recurs throughout `finalStep_run_good` whenever a rule pops an `.old` symbol and the invariant must be restated in terms of the original stack.

```lean
@[grind .] private theorem old_cons_parts {x : Stack} {tail : List (FinalStack Stack)}
    {stack : List Stack}
    (h : FinalStack.old x :: tail =
      stack.map FinalStack.old ++ [FinalStack.bottom]) :
    ∃ rest, stack = x :: rest ∧
      tail = rest.map FinalStack.old ++ [FinalStack.bottom] := by
  cases stack with
  | nil => simp at h
  | cons y stack =>
      simp only [List.map_cons, List.cons_append] at h
      obtain ⟨hy, htail⟩ := List.cons.inj h
      cases hy
      exact ⟨stack, rfl, htail⟩

```

`bottom_parts` is the dual inversion lemma for the case where the embedded stack begins with the `.bottom` marker itself: since `.bottom` is unique and only ever appears at the very end, seeing it at the head forces the whole stack to be empty. This is used whenever a rule pops `.bottom`, i.e. at the transitions into `.done`.

```lean
@[grind .] private theorem bottom_parts {tail : List (FinalStack Stack)}
    {stack : List Stack}
    (h : FinalStack.bottom :: tail =
      stack.map FinalStack.old ++ [FinalStack.bottom]) :
    stack = [] ∧ tail = [] := by
  cases stack with
  | nil => simpa using h
  | cons x stack =>
      simp only [List.map_cons, List.cons_append] at h
      cases (List.cons.inj h).1
```

`finalStep_run_good` is the core preservation lemma: it case-splits on `finalRule_cases`' six rule families and, for each, either rules it out (the phase/stack shape makes it impossible, discharged by `simp`) or reconstructs the invariant for the successor configuration using `old_cons_parts`/`bottom_parts` to unpack the stack shape. Establishing this once, per rule kind, is what makes the induction over full runs in `finalReaches_run_good` a one-line consequence.

```lean
/-- One normalization step preserves the semantic run invariant. -/
@[grind .] theorem finalStep_run_good (M : NPDA α State Stack)
    (word : List α) {c c' : ID α (FinalState State) (FinalStack Stack)}
    (h : M.finalToEmpty.Step c c') :
    M.FinalRunGood word c → M.FinalRunGood word c' := by
  cases h with
  | @consume a input tail r hr input_eq =>
      rcases M.finalRule_cases hr with
        ⟨q, hq, rfl⟩ | ⟨old, hold, rfl⟩ |
        ⟨q, hq, x, hx, rfl⟩ | ⟨q, hq, rfl⟩ |
        ⟨x, hx, rfl⟩ | rfl
      · simp at input_eq
      · intro hgood
        rcases hgood with ⟨q₀, hq₀, oldStack, hstack, hreach⟩
        obtain ⟨rest, rfl, htail⟩ := old_cons_parts hstack
        refine ⟨q₀, hq₀, old.push ++ rest, ?_, ?_⟩
        · simpa [List.map_append, List.append_assoc] using htail
        · exact hreach.tail (Step.consume old hold input_eq)
      · simp at input_eq
      · simp at input_eq
      · simp at input_eq
      · simp [Internal.finishDrainRule] at input_eq
  | @epsilon input tail r hr input_eq =>
      rcases M.finalRule_cases hr with
        ⟨q, hq, rfl⟩ | ⟨old, hold, rfl⟩ |
        ⟨q, hq, x, hx, rfl⟩ | ⟨q, hq, rfl⟩ |
        ⟨x, hx, rfl⟩ | rfl
      · rintro ⟨rfl, hstack⟩
        simp only [List.cons.injEq, true_and] at hstack
        subst tail
        refine ⟨q, hq, M.initialStack, ?_, Relation.ReflTransGen.refl⟩
        simp
      · intro hgood
        rcases hgood with ⟨q₀, hq₀, oldStack, hstack, hreach⟩
        obtain ⟨rest, rfl, htail⟩ := old_cons_parts hstack
        refine ⟨q₀, hq₀, old.push ++ rest, ?_, ?_⟩
        · simpa [List.map_append, List.append_assoc] using htail
        · exact hreach.tail (Step.epsilon old hold input_eq)
      · intro hgood
        rcases hgood with ⟨q₀, hq₀, oldStack, hstack, hreach⟩
        obtain ⟨rest, rfl, htail⟩ := old_cons_parts hstack
        exact ⟨⟨rest, by simpa using htail⟩,
          q₀, hq₀, q, hq, x :: rest, hreach⟩
      · intro hgood
        rcases hgood with ⟨q₀, hq₀, oldStack, hstack, hreach⟩
        obtain ⟨rfl, rfl⟩ := bottom_parts hstack
        exact ⟨rfl, q₀, hq₀, q, hq, [], hreach⟩
      · rintro ⟨⟨oldStack, hstack⟩, haccept⟩
        obtain ⟨rest, rfl, htail⟩ := old_cons_parts hstack
        exact ⟨⟨rest, by simpa using htail⟩, haccept⟩
      · rintro ⟨⟨oldStack, hstack⟩, haccept⟩
        obtain ⟨rfl, rfl⟩ := bottom_parts hstack
        exact ⟨rfl, haccept⟩
```

Lifting `finalStep_run_good` by induction over `Reaches` gives the invariant's preservation across a whole normalized run, exactly the form `finalReaches_stack_good` and `finalToEmpty_language` consume.

```lean
/-- The semantic invariant propagates over a complete normalized run. -/
@[grind .] theorem finalReaches_run_good (M : NPDA α State Stack)
    (word : List α) {c c' : ID α (FinalState State) (FinalStack Stack)}
    (h : M.finalToEmpty.Reaches c c') :
    M.FinalRunGood word c → M.FinalRunGood word c' := by
  induction h with
  | refl => exact id
  | tail h step ih => exact fun hc => M.finalStep_run_good word step (ih hc)
```

`finalReaches_stack_good` derives the purely syntactic `FinalStackGood` invariant as a corollary of the richer `FinalRunGood`, specialized to runs starting at the canonical `.boot` configuration. Keeping the two invariants separate lets callers who only need the stack shape (e.g. to justify a `simp` rewrite) avoid unpacking the semantic content.

```lean
/-- The stack-shape component of the normalization invariant propagates over
reachable configurations. -/


@[grind .] public theorem finalReaches_stack_good (M : NPDA α State Stack)
    {word : List α} {c' : ID α (FinalState State) (FinalStack Stack)}
    (h : M.finalToEmpty.Reaches
      (word, (FinalState.boot : FinalState State),
        [(FinalStack.bottom : FinalStack Stack)]) c') :
    FinalStackGood (α := α)
      (word, (FinalState.boot : FinalState State),
        [(FinalStack.bottom : FinalStack Stack)]) →
      FinalStackGood (α := α) c' := by
  intro _
  have hout := M.finalReaches_run_good word h (by simp [FinalRunGood])
  cases c' with
  | mk input rest =>
    rcases rest with ⟨state, stack⟩
    cases state with
    | boot => exact hout.2
    | sim q =>
        rcases hout with ⟨q₀, hq₀, oldStack, hstack, hreach⟩
        exact ⟨oldStack, hstack⟩
    | drain => exact hout.1
    | done => exact hout.1
```

`finalToEmpty_language` is the payoff of this whole section: it shows `finalToEmpty` does not change the accepted language. The forward direction reads off `AcceptingPrefix` from `FinalRunGood` at the `.done` configuration; the reverse direction assembles a concrete accepting run for `finalToEmpty` out of `bootRule_mem`, `Reaches.finalToEmpty`, and `drain_reaches_done`, branching on whether the original machine's leftover stack is empty or not.

```lean
/-- Final-state normalization preserves the accepted language. -/
@[grind =, simp] public theorem finalToEmpty_language (M : NPDA α State Stack) :
    M.finalToEmpty.language = M.language := by
  ext word
  constructor
  · rintro ⟨start, hstart, finalState, hdone, stack, hreach⟩
    simp only [finalToEmpty, List.mem_singleton] at hstart hdone
    subst start
    subst finalState
    have hreach' : M.finalToEmpty.Reaches
        (word, FinalState.boot, [FinalStack.bottom])
        ([], FinalState.done, stack) := by
      simpa [finalToEmpty] using hreach
    have hgood := M.finalReaches_run_good word hreach'
      (by simp [FinalRunGood])
    exact hgood.2
  · rintro ⟨q₀, hq₀, qf, hqf, stack, hreach⟩
    refine ⟨FinalState.boot, by simp [finalToEmpty], FinalState.done,
      by simp [finalToEmpty], [], ?_⟩
    have hboot : M.finalToEmpty.Step
        (word, FinalState.boot, [FinalStack.bottom])
        (word, FinalState.sim q₀,
          M.initialStack.map FinalStack.old ++ [FinalStack.bottom]) := by
      simpa using Step.epsilon
        ({ source := FinalState.boot, input := none,
           pop := FinalStack.bottom, target := FinalState.sim q₀,
           push := M.initialStack.map FinalStack.old ++ [FinalStack.bottom] } :
          PushdownRule α (FinalState State) (FinalStack Stack))
        (M.bootRule_mem hq₀) rfl
    have hsim := hreach.finalToEmpty
    have hs : M.StackSupported stack :=
      hreach.stack_supported M.initialStack_supported
    have hprefix := (Relation.ReflTransGen.single hboot).trans hsim
    cases stack with
    | nil =>
        have hdoneStep : M.finalToEmpty.Step
            ([], FinalState.sim qf, [FinalStack.bottom])
            ([], FinalState.done, []) := by
          simpa using Step.epsilon
            ({ source := FinalState.sim qf, input := none,
               pop := FinalStack.bottom, target := FinalState.done, push := [] } :
              PushdownRule α (FinalState State) (FinalStack Stack))
            (M.acceptBottomRule_mem hqf) rfl
        exact hprefix.tail hdoneStep
    | cons x stack =>
        have hx : x ∈ M.stackSupport := hs x (by simp)
        have htail : M.StackSupported stack := by
          intro y hy
          exact hs y (by simp [hy])
        have henter : M.finalToEmpty.Step
            ([], FinalState.sim qf,
              FinalStack.old x :: stack.map FinalStack.old ++ [FinalStack.bottom])
            ([], FinalState.drain,
              stack.map FinalStack.old ++ [FinalStack.bottom]) := by
          simpa using Step.epsilon
            ({ source := FinalState.sim qf, input := none,
               pop := FinalStack.old x, target := FinalState.drain, push := [] } :
              PushdownRule α (FinalState State) (FinalStack Stack))
            (M.enterDrainRule_mem hqf hx) rfl
        exact (hprefix.tail henter).trans (M.drain_reaches_done htail)
```

This closes the `finalToEmpty` correctness story. The remaining two theorems return to the earlier `Balanced`/`StackBalanced` machinery and establish its converse: not just that balanced computations induce concrete runs (already shown by `.reaches`), but that any concrete run emptying a full stack word actually arose as a balanced computation. `StackBalanced.split` is the structural lemma that makes this possible, decomposing a balanced run over a concatenated stack word `left ++ right` into two independent balanced runs — this is what lets an inductive proof peel off one stack symbol at a time from an arbitrary concatenation.

```lean
/-- Split a balanced computation at a concatenation boundary in its initial
stack word. -/


@[grind .] theorem StackBalanced.split {M : NPDA α State Stack}
    {p q : State} {left right : List Stack} {word : List α}
    (h : StackBalanced M p (left ++ right) q word) :
    ∃ mid u v, word = u ++ v ∧
      StackBalanced M p left mid u ∧ StackBalanced M mid right q v := by
  induction left generalizing p word with
  | nil =>
      exact ⟨p, [], word, by simp, StackBalanced.nil p, by simpa using h⟩
  | cons top left ih =>
      cases h with
      | cons head tail =>
          obtain ⟨mid, u, v, hword, hleft, hright⟩ := ih tail
          exact ⟨mid, _, v, by simp [hword, List.append_assoc],
            StackBalanced.cons head hleft, hright⟩
```

`stackBalanced_of_reaches_to_empty` is the completeness half promised above: given a run that reaches an empty stack, it reconstructs a `StackBalanced` witness by reverse induction on the run (`head_induction_on`), using `StackBalanced.split` at each step to separate the just-applied rule's contribution from the rest. This equivalence between concrete runs and the balanced/tree-shaped semantics is exactly what grammar-conversion modules need to translate PDA acceptance into a generative grammar and back.

```lean
/-- Any concrete run that empties its complete initial stack decomposes into
the balanced semantics used by the triple construction. -/


@[grind .] public theorem stackBalanced_of_reaches_to_empty {M : NPDA α State Stack}
    {p q : State} {stack : List Stack} {word : List α}
    (h : M.Reaches (word, p, stack) ([], q, [])) :
    StackBalanced M p stack q word :=
  reachesAux h
where
  reachesAux {M : NPDA α State Stack} {c : ID α State Stack} {q : State}
      (h : M.Reaches c ([], q, [])) :
      StackBalanced M c.2.1 c.2.2 q c.1 := by
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact StackBalanced.nil q
    | head step rest ih =>
        cases step with
        | @consume a input tail r mem input_eq =>
            obtain ⟨mid, u, v, hinput, hpush, htail⟩ :=
              StackBalanced.split ih
            change input = u ++ v at hinput
            change StackBalanced M r.source (r.pop :: tail) q (a :: input)
            rw [hinput]
            simpa [input_eq, List.append_assoc] using
              StackBalanced.cons (Balanced.rule r mem hpush) htail
        | @epsilon input tail r mem input_eq =>
            obtain ⟨mid, u, v, hinput, hpush, htail⟩ :=
              StackBalanced.split ih
            change input = u ++ v at hinput
            change StackBalanced M r.source (r.pop :: tail) q input
            rw [hinput]
            simpa [input_eq, List.append_assoc] using
              StackBalanced.cons (Balanced.rule r mem hpush) htail

end NPDA
```

## 局所規則を持つ DPDA

`DPDA` は有限局所規則 `NPDA` と、その規則表が決定的である証拠を束ねる。二つの規則が
同じ状態とスタック先頭で競合し、同じ入力を読むか一方が epsilon 規則なら、その二規則は
同一でなければならない。この条件により epsilon 遷移と consuming 遷移の競合も排除される。

```lean
/-- A deterministic pushdown automaton with a single start state. -/
public structure DPDA (α State Stack : Type*) where
  rules : List (PushdownRule α State Stack)
  start : State
  accept : List State
  initialStack : List Stack
  deterministic : ∀ {r s}, r ∈ rules → s ∈ rules →
    r.source = s.source → r.pop = s.pop →
    (r.input = none ∨ s.input = none ∨ r.input = s.input) → r = s

```

以降の `DPDA` に関する定義・定理は `DPDA` 名前空間の下にまとめられ、`M.toNPDA` のように呼び出せるようにする。

```lean
namespace DPDA

```

`toNPDA` は決定性の証拠を単に忘れ、唯一の開始状態を単集合 `[M.start]` として `NPDA` へ埋め込む。本体を公開しているのは、決定性を経由せずに済む言語保存証明が、生成された `NPDA` の各フィールドをそのまま簡約する必要があるためである。

```lean
variable {α State Stack : Type*}

/-- Forget determinism and expose the unique start state as a singleton list.

Its body is exposed because public language-preservation proofs reduce the
resulting NPDA fields across the automata-module boundary. -/


@[expose] public def toNPDA (M : DPDA α State Stack) : NPDA α State Stack where
  rules := M.rules
  start := [M.start]
  accept := M.accept
  initialStack := M.initialStack
```

`DPDA` 自身は独立した実行意味論を持たず、`language` は常に `toNPDA.language` を通じて定義される。これにより `NPDA` 側の受理・実行の定義を一度書けば `DPDA` にも自動的に適用される。

```lean
/-- The language of a DPDA is the language of its underlying local NPDA. -/
@[expose] public def language (M : DPDA α State Stack) : Language α := M.toNPDA.language
```

この等式は `rfl` で閉じる定義的な同値であり、`toNPDA` と `language` が矛盾なく同じ言語を指すという最小限の健全性を確認する。

```lean
/-- Forgetting determinism preserves the accepted language definitionally. -/
@[grind =, simp] public theorem toNPDA_language (M : DPDA α State Stack) :
    M.toNPDA.language = M.language := rfl

end DPDA
```

## 一手番 PDA（OneTurnNPDA）

`TurnPhase` はスタックが伸びる `push` 局面と縮む `pop` 局面を区別する。`OneTurnNPDA` はこの局面を制御状態の一部として持ち、次の3つの不変条件によって「一度だけ向きを変える」計算に制限する。

```mermaid
stateDiagram-v2
    [*] --> push
    push --> push : スタック高さが非減少
    push --> pop : 局面切替（以後 push には戻らない）
    pop --> pop : スタック高さが非増加
    pop --> [*]
```

- `pop_stays_pop`: 一度 `pop` 局面に入ったら二度と `push` 局面へは戻らない。
- `push_phase_nonshrinking`: `push` 局面ではスタックの高さが単調非減少（局所規則でスタック記号を1つ消費して1つ以上積む）。
- `pop_phase_nongrowing`: `pop` 局面ではスタックの高さが単調非増加（局所規則でスタック記号を1つ消費して1つ以下積む）。

この制限クラスは、線形文法（linear grammar）から構成される PDA が自然にこの形を取ることから、他モジュールでの変換の中間表現として用いられる。実行意味論は `toNPDA` を通じて `NPDA` に忘却することによって定義される。

```lean
/-- The phase of a one-turn pushdown computation. -/
@[grind cases] public inductive TurnPhase where
  | push
  | pop
  deriving Repr, DecidableEq
```

`OneTurnNPDA` は状態を `State × TurnPhase` に組み込むことで、局面を規則ごとに検査可能にし、上のダイアグラムで示した3つの不変条件をフィールドとして機械の定義そのものに埋め込む。こうすることで「一度だけ向きを変える」という制約は構成時に保証され、以降のすべての証明はこの不変条件を仮定として自由に使える。

```lean
/-- A nondeterministic PDA whose stack height first grows and then shrinks. -/
public structure OneTurnNPDA (α State Stack : Type*) where
  rules : List (PushdownRule α (State × TurnPhase) Stack)
  start : List State
  accept : List State
  initialStack : List Stack
  pop_stays_pop : ∀ r ∈ rules,
    (r.source).2 = TurnPhase.pop → (r.target).2 = TurnPhase.pop
  push_phase_nonshrinking : ∀ r ∈ rules,
    (r.source).2 = TurnPhase.push → r.push.length ≥ 1
  pop_phase_nongrowing : ∀ r ∈ rules,
    (r.target).2 = TurnPhase.pop → r.push.length ≤ 1
```

`NondeterministicOneTurnPDA` is a purely descriptive alias, letting call sites that emphasize the nondeterminism over the one-turn restriction read more naturally without introducing a second incompatible type.

```lean
/-- Alternate descriptive name for a nondeterministic one-turn PDA. -/
public abbrev NondeterministicOneTurnPDA := OneTurnNPDA
```

以降の実行意味論・正規化はすべて `OneTurnNPDA` 名前空間の下にまとめ、`NPDA` と同様に構成・実行・受理・言語という順序で公開する。

```lean
namespace OneTurnNPDA

```

`ID` は基礎の `NPDA.ID` と同じ形をしているが、状態成分が `State × TurnPhase` になっている点だけが異なる。この定義が以降のすべての一手番機械向け遷移・到達関係の型を決める。

```lean
variable {α State Stack : Type*}

/-- An instantaneous description including the one-turn phase. -/
public abbrev ID (α State Stack : Type*) :=
  List α × (State × TurnPhase) × List Stack
```

`toNPDA` は一手番の3不変条件を忘れ、開始状態を push 局面に固定し、受理状態は push/pop 両局面を許して `NPDA` へ埋め込む。以降の `Step`/`Reaches`/`Accepts`/`language` はすべてこの `toNPDA` を経由して定義され、一手番固有の実行意味論を独自に再定義する必要をなくす。

```lean
/-- Forget the one-turn constraints and map to a standard local NPDA.

Its body is exposed because public language-preservation proofs reduce the
resulting NPDA fields across the automata-module boundary. -/


@[expose] public def toNPDA (M : OneTurnNPDA α State Stack) : NPDA α (State × TurnPhase) Stack where
  rules := M.rules
  start := M.start.map (·, TurnPhase.push)
  accept := M.accept.flatMap fun q => [(q, TurnPhase.push), (q, TurnPhase.pop)]
  initialStack := M.initialStack
```

`Step` は独自定義を持たず `toNPDA.Step` の別名にすぎない。これにより一手番機械の1ステップ意味論は、通常の `NPDA` の1ステップ意味論と定義的に一致する。

```lean
/-- One consuming or epsilon transition of a one-turn machine. -/
public abbrev Step (M : OneTurnNPDA α State Stack) :
    ID α State Stack → ID α State Stack → Prop := M.toNPDA.Step
```

同様に `Reaches` も `toNPDA.Reaches` の別名であり、独自の反射推移閉包を再構築する必要をなくす。

```lean
/-- Zero or more one-turn transitions. -/
public abbrev Reaches (M : OneTurnNPDA α State Stack) := M.toNPDA.Reaches
```

`Accepts` は開始が常に push 局面であることを `toNPDA.start` の構成に委ね、終了局面は push/pop どちらでもよいことを `toNPDA.accept` の構成に委ねる。本体を公開しているのは、一手番専用の受理変換証明がこの委譲を分解する必要があるためである。

```lean
/-- Acceptance starts in the push phase and ends in any phase. -/
@[expose] public def Accepts (M : OneTurnNPDA α State Stack) (w : List α) : Prop :=
  M.toNPDA.Accepts w
```

`language` は `Accepts` と同様、`toNPDA.language` への薄い委譲であり、一手番機械の言語論的な境界を固定する。

```lean
/-- The language accepted by a one-turn PDA. -/
@[expose] public def language (M : OneTurnNPDA α State Stack) : Language α :=
  M.toNPDA.language
```

`Step`/`Reaches`/`Accepts`/`language` がすべて `toNPDA` への定義的な委譲であることから、この保存定理は `rfl` で閉じる。これは一手番の構造を忘れても言語が変わらないことを保証する、最も基本的な健全性チェックである。

```lean
/-- Forgetting the one-turn structure preserves the accepted language definitionally. -/
@[grind =, simp] public theorem toNPDA_language (M : OneTurnNPDA α State Stack) :
    M.toNPDA.language = M.language := rfl
```

ここから一手番機械を「複数記号を一度に push する局所規則」から「高々2記号しか押さない局所規則」へ正規化する変換を構築する。`NormalState` はこの変換が導入する管理状態の族であり、`boot`（起動）、`initialize`（初期スタックの構築中）、`sim`（元の規則をそのまま模倣）、`expand`（長い push の分割中）、`drain`（受理後の排出）、`done`（受理完了）を区別する。

```lean
/-- Administrative states used by the local one-turn normalizer. -/
@[grind cases] public inductive NormalState (α State Stack : Type*) where
  | boot
  | initialize (start : State) (done remaining : List Stack)
  | sim (state : State)
  | expand (rule : PushdownRule α (State × TurnPhase) Stack)
      (done remaining : List Stack)
  | drain
  | done
```

以下の `Internal` 名前空間は正規化規則を生成する内部実装であり、公開 API ではなく `normalize` の定義と分類補題 `NormalizedRuleKind` からのみ参照される。`initializationChain` は複数記号からなる初期スタックを、2記号以下しか押さない `initialize` 遷移の連鎖へ分割する補助関数で、末尾から1記号ずつ`current`/`next` の対を処理して初期スタックの向きを保ったまま構築する。

```lean
namespace Internal

public def initializationChain (q : State) : List Stack → List Stack →
    List (PushdownRule α (NormalState α State Stack × TurnPhase) (NPDA.FinalStack Stack))
  | _, [] => []
  | [], _ => []
  | current :: done, next :: rest =>
      [{ source := (.initialize q (current :: done) (next :: rest), .push),
         input := none, pop := .old current,
         target := (if rest.isEmpty then (.sim q, .push)
           else (.initialize q (next :: current :: done) rest, .push)),
         push := [.old next, .old current] }] ++
      initializationChain q (next :: current :: done) rest
```

`initializationRules` は各開始状態ごとに、底記号越しの起動規則と、必要なら `initializationChain` による続きの連鎖を組み合わせて、初期スタック全体を構築する規則を生成する。1記号だけの初期スタックは連鎖なしで直接 `.sim` へ入れる。

```lean
public def initializationRules (M : OneTurnNPDA α State Stack) :
    List (PushdownRule α (NormalState α State Stack × TurnPhase) (NPDA.FinalStack Stack)) :=
  M.start.flatMap fun q =>
    match M.initialStack.reverse with
    | [] =>
        [{ source := (.boot, .push), input := none, pop := .bottom,
           target := (.sim q, .push), push := [.bottom] }]
    | first :: rest =>
        [{ source := (.boot, .push), input := none, pop := .bottom,
           target := (if rest.isEmpty then (.sim q, .push)
             else (.initialize q [first] rest, .push)),
           push := [.old first, .bottom] }] ++
        initializationChain q [first] rest
```

`expansionChain` は `initializationChain` と対をなす補助関数で、元の一手番機械の1つの push 規則が長さ2を超える `push` を持つ場合に、それを2記号以下の局所遷移の連鎖へ展開する。分割された各遷移は元の規則 `r` を覚えており、これが後続の `NormalizedRuleKind.expand` で元の規則へ遡るための手がかりになる。

```lean
public def expansionChain (r : PushdownRule α (State × TurnPhase) Stack) :
    List Stack → List Stack →
    List (PushdownRule α (NormalState α State Stack × TurnPhase) (NPDA.FinalStack Stack))
  | _, [] => []
  | [], _ => []
  | current :: done, next :: rest =>
      [{ source := (.expand r (current :: done) (next :: rest), .push),
         input := none, pop := .old current,
         target := (if rest.isEmpty then (.sim r.target.1, .push)
           else (.expand r (next :: current :: done) rest, .push)),
         push := [.old next, .old current] }] ++
      expansionChain r (next :: current :: done) rest
```

`normalizedSimulationRules` maps every original rule into the normalized alphabet: rules whose source and target are both in the push phase get their (possibly long) `push` split via `expansionChain`, while every other rule (any rule touching the pop phase) is simply re-embedded unchanged, since `pop_phase_nongrowing` already guarantees its `push` has length at most one.

```lean
public def normalizedSimulationRules (M : OneTurnNPDA α State Stack) :
    List (PushdownRule α (NormalState α State Stack × TurnPhase) (NPDA.FinalStack Stack)) :=
  M.rules.flatMap fun r =>
    if r.source.2 = .push ∧ r.target.2 = .push then
      match r.push.reverse with
      | [] => []
      | first :: rest =>
          [{ source := (.sim r.source.1, .push), input := r.input, pop := .old r.pop,
             target := (if rest.isEmpty then (.sim r.target.1, .push)
               else (.expand r [first] rest, .push)),
             push := [.old first] }] ++
          expansionChain r [first] rest
    else
      [{ source := (.sim r.source.1, r.source.2), input := r.input, pop := .old r.pop,
         target := (.sim r.target.1, r.target.2), push := r.push.map NPDA.FinalStack.old }]
```

`enterDrainRules` lets simulation exit into the `.drain` phase from either turn phase once an accept state is reached, ranging over the finite `stackSupport` for the symbols that may still be on the stack. Push-phase exits also carry the just-inspected symbol back onto the stack (since the pop phase must not grow it further before draining), while pop-phase exits discard it immediately.

```lean
public def enterDrainRules (M : OneTurnNPDA α State Stack) :
    List (PushdownRule α (NormalState α State Stack × TurnPhase) (NPDA.FinalStack Stack)) :=
  M.accept.flatMap fun q =>
    [TurnPhase.push, TurnPhase.pop].flatMap fun phase =>
      ((M.toNPDA.stackSupport).map fun x =>
        { source := (.sim q, phase), input := none, pop := .old x,
          target := (.drain, .pop),
          push := if phase = .push then [.old x] else [] }) ++
      [{ source := (.sim q, phase), input := none, pop := .bottom,
         target := (if phase = .push then (.drain, .pop) else (.done, .pop)),
         push := if phase = .push then [.bottom] else [] }]
```

`normalizedDrainRules` mirrors `NPDA.Internal.drainRules`/`finishDrainRule` for the one-turn normalizer: from `.drain` it strips any supported symbol one at a time and finally removes the bottom marker into `.done`.

```lean
public def normalizedDrainRules (M : OneTurnNPDA α State Stack) :
    List (PushdownRule α (NormalState α State Stack × TurnPhase) (NPDA.FinalStack Stack)) :=
  ((M.toNPDA.stackSupport).map fun x =>
    { source := (.drain, .pop), input := none, pop := .old x,
      target := (.drain, .pop), push := [] }) ++
  [{ source := (.drain, .pop), input := none, pop := .bottom,
     target := (.done, .pop), push := [] }]
```

`normalizedRules` concatenates the four rule families defined above into the single rule list underlying `normalize`. This assembly is analogous to `NPDA.finalToEmpty`'s six-family union, but here it must additionally guarantee the "at most two symbols per rule" shape that `normalize_rule_shape` later verifies.

```lean
public def normalizedRules (M : OneTurnNPDA α State Stack) :
    List (PushdownRule α (NormalState α State Stack × TurnPhase) (NPDA.FinalStack Stack)) :=
  initializationRules M ++ normalizedSimulationRules M ++ enterDrainRules M ++
    normalizedDrainRules M
```

`NormalizedRuleKind` is the one-turn analogue of `NPDA.finalRule_cases`: rather than a theorem proving a disjunction of shapes, it is packaged as an inductive predicate whose ten constructors enumerate every syntactic origin a normalized rule can have (boot with/without an initial stack, one initialization step, one split or expansion step, an unchanged simulation, entering drain from an old symbol or the bottom marker, and draining). Making it an inductive type rather than a raw disjunction lets `cases` destructure it directly in later proofs such as `normalize_rule_shape`.

```lean
inductive NormalizedRuleKind (M : OneTurnNPDA α State Stack) :
    PushdownRule α (NormalState α State Stack × TurnPhase) (NPDA.FinalStack Stack) →
      Prop where
  | bootEmpty (q : State) (hq : q ∈ M.start) (hstack : M.initialStack.reverse = []) :
      NormalizedRuleKind M
        { source := (.boot, .push), input := none, pop := .bottom,
          target := (.sim q, .push), push := [.bottom] }
  | bootCons (q : State) (hq : q ∈ M.start) (first : Stack) (rest : List Stack)
      (hstack : M.initialStack.reverse = first :: rest) :
      NormalizedRuleKind M
        { source := (.boot, .push), input := none, pop := .bottom,
          target := (if rest.isEmpty then (.sim q, .push)
            else (.initialize q [first] rest, .push)),
          push := [.old first, .bottom] }
  | initStep (q : State) (hq : q ∈ M.start) (current : Stack)
      (done : List Stack) (next : Stack) (rest : List Stack) :
      NormalizedRuleKind M
        { source := (.initialize q (current :: done) (next :: rest), .push),
          input := none, pop := .old current,
          target := (if rest.isEmpty then (.sim q, .push)
            else (.initialize q (next :: current :: done) rest, .push)),
          push := [.old next, .old current] }
  | split (old : PushdownRule α (State × TurnPhase) Stack)
      (hold : old ∈ M.rules) (first : Stack) (rest : List Stack)
      (hphase : old.source.2 = .push ∧ old.target.2 = .push)
      (hpush : old.push.reverse = first :: rest) :
      NormalizedRuleKind M
        { source := (.sim old.source.1, .push), input := old.input, pop := .old old.pop,
          target := (if rest.isEmpty then (.sim old.target.1, .push)
            else (.expand old [first] rest, .push)),
          push := [.old first] }
  | expand (old : PushdownRule α (State × TurnPhase) Stack)
      (hold : old ∈ M.rules) (current : Stack) (done : List Stack)
      (next : Stack) (rest : List Stack)
      (hphase : old.source.2 = .push ∧ old.target.2 = .push)
      (hpush : old.push.reverse = (current :: done).reverse ++ next :: rest) :
      NormalizedRuleKind M
        { source := (.expand old (current :: done) (next :: rest), .push),
          input := none, pop := .old current,
          target := (if rest.isEmpty then (.sim old.target.1, .push)
            else (.expand old (next :: current :: done) rest, .push)),
          push := [.old next, .old current] }
  | simulate (old : PushdownRule α (State × TurnPhase) Stack)
      (hold : old ∈ M.rules)
      (hphase : ¬ (old.source.2 = .push ∧ old.target.2 = .push)) :
      NormalizedRuleKind M
        { source := (.sim old.source.1, old.source.2), input := old.input,
          pop := .old old.pop, target := (.sim old.target.1, old.target.2),
          push := old.push.map NPDA.FinalStack.old }
  | enterOld (q : State) (hq : q ∈ M.accept) (phase : TurnPhase)
      (hphase : phase ∈ [TurnPhase.push, TurnPhase.pop]) (x : Stack)
      (hx : x ∈ M.toNPDA.stackSupport) :
      NormalizedRuleKind M
        { source := (.sim q, phase), input := none, pop := .old x,
          target := (.drain, .pop),
          push := if phase = .push then [.old x] else [] }
  | enterBottom (q : State) (hq : q ∈ M.accept) (phase : TurnPhase)
      (hphase : phase ∈ [TurnPhase.push, TurnPhase.pop]) :
      NormalizedRuleKind M
        { source := (.sim q, phase), input := none, pop := .bottom,
          target := (if phase = .push then (.drain, .pop) else (.done, .pop)),
          push := if phase = .push then [.bottom] else [] }
  | drainOld (x : Stack) (hx : x ∈ M.toNPDA.stackSupport) :
      NormalizedRuleKind M
        { source := (.drain, .pop), input := none, pop := .old x,
          target := (.drain, .pop), push := [] }
  | drainBottom :
      NormalizedRuleKind M
        { source := (.drain, .pop), input := none, pop := .bottom,
          target := (.done, .pop), push := [] }

```

`initializationChain_kind` shows that every rule produced by `initializationChain` is an `.initStep` instance of `NormalizedRuleKind`, by induction that mirrors the recursive structure of `initializationChain` itself.

```lean
theorem initializationChain_kind (M : OneTurnNPDA α State Stack)
    (q : State) (hq : q ∈ M.start) (done remaining : List Stack)
    {r : PushdownRule α (NormalState α State Stack × TurnPhase)
      (NPDA.FinalStack Stack)}
    (hr : r ∈ initializationChain q done remaining) : NormalizedRuleKind M r := by
  induction remaining generalizing done with
  | nil => simp [initializationChain] at hr
  | cons next rest ih =>
      cases done with
      | nil => simp [initializationChain] at hr
      | cons current done =>
          simp only [initializationChain, List.mem_append, List.mem_singleton] at hr
          rcases hr with rfl | hr
          · exact .initStep q hq current done next rest
          · exact ih (next :: current :: done) hr

```

`expansionChain_kind` is the corresponding classification for `expansionChain`'s output, tagging each generated rule as `.expand`. The `hpush` hypothesis threading `done.reverse ++ remaining` through the induction is what lets each recursive call reconstruct the exact original-rule push decomposition demanded by `NormalizedRuleKind.expand`.

```lean
theorem expansionChain_kind (M : OneTurnNPDA α State Stack)
    (old : PushdownRule α (State × TurnPhase) Stack) (hold : old ∈ M.rules)
    (hphase : old.source.2 = .push ∧ old.target.2 = .push)
    (done remaining : List Stack)
    (hpush : old.push.reverse = done.reverse ++ remaining)
    {r : PushdownRule α (NormalState α State Stack × TurnPhase)
      (NPDA.FinalStack Stack)}
    (hr : r ∈ expansionChain old done remaining) : NormalizedRuleKind M r := by
  induction remaining generalizing done with
  | nil => simp [expansionChain] at hr
  | cons next rest ih =>
      cases done with
      | nil => simp [expansionChain] at hr
      | cons current done =>
          simp only [expansionChain, List.mem_append, List.mem_singleton] at hr
          rcases hr with rfl | hr
          · apply NormalizedRuleKind.expand old hold current done next rest hphase
            simpa [List.append_assoc] using hpush
          · apply ih (next :: current :: done)
              (by simpa [List.append_assoc] using hpush) hr

```

`normalizedRule_kind` assembles the four chain/family-level classification lemmas into the top-level statement that *every* rule in `normalizedRules M` matches one of `NormalizedRuleKind`'s constructors, unfolding `normalizedRules` and dispatching each of the four rule families (initialization, simulation, enter-drain, drain) to its corresponding sub-lemma.

```lean
theorem normalizedRule_kind (M : OneTurnNPDA α State Stack)
    {r : PushdownRule α (NormalState α State Stack × TurnPhase)
      (NPDA.FinalStack Stack)} (hr : r ∈ normalizedRules M) :
    NormalizedRuleKind M r := by
  unfold normalizedRules at hr
  simp only [List.mem_append] at hr
  rcases hr with ((hr | hr) | hr) | hr
  · unfold initializationRules at hr
    simp only [List.mem_flatMap] at hr
    rcases hr with ⟨q, hq, hr⟩
    cases hstack : M.initialStack.reverse with
    | nil =>
        rw [hstack] at hr
        simp only [List.mem_singleton] at hr
        subst r
        exact .bootEmpty q hq hstack
    | cons first rest =>
        rw [hstack] at hr
        simp only [List.mem_append, List.mem_singleton] at hr
        rcases hr with rfl | hr
        · exact .bootCons q hq first rest hstack
        · exact initializationChain_kind M q hq [first] rest hr
  · unfold normalizedSimulationRules at hr
    simp only [List.mem_flatMap] at hr
    rcases hr with ⟨old, hold, hr⟩
    by_cases hphase : old.source.2 = .push ∧ old.target.2 = .push
    · rw [if_pos hphase] at hr
      cases hpush : old.push.reverse with
      | nil => simp [hpush] at hr
      | cons first rest =>
          rw [hpush] at hr
          simp only [List.mem_append, List.mem_singleton] at hr
          rcases hr with rfl | hr
          · exact .split old hold first rest hphase hpush
          · exact expansionChain_kind M old hold hphase [first] rest
              (by simpa using hpush) hr
    · rw [if_neg hphase] at hr
      simp only [List.mem_singleton] at hr
      subst r
      exact .simulate old hold hphase
  · unfold enterDrainRules at hr
    simp only [List.mem_flatMap, List.mem_append, List.mem_map,
      List.mem_singleton] at hr
    rcases hr with ⟨q, hq, phase, hphase, hr⟩
    rcases hr with ⟨x, hx, rfl⟩ | rfl
    · exact .enterOld q hq phase hphase x hx
    · exact .enterBottom q hq phase hphase
  · unfold normalizedDrainRules at hr
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hr
    rcases hr with ⟨x, hx, rfl⟩ | rfl
    · exact .drainOld x hx
    · exact .drainBottom

```

`initializationChain_shape` records that every rule generated by `initializationChain` is a push-phase rule pushing exactly two symbols. It is `@[aesop safe apply]` because this shape fact is a routine ingredient of the well-formedness proof `normalizedRule_wellformed`, and letting `aesop` apply it automatically avoids re-deriving it by hand at every use site.

```lean
@[aesop safe apply] theorem initializationChain_shape (q : State) (done : List Stack)
    {rest : List Stack}
    {r : PushdownRule α (NormalState α State Stack × TurnPhase) (NPDA.FinalStack Stack)}
    (hr : r ∈ initializationChain (α := α) q done rest) :
    r.source.2 = .push ∧ r.target.2 = .push ∧ r.push.length = 2 := by
  induction rest generalizing done with
  | nil => simp [initializationChain] at hr
  | cons next rest ih =>
      cases done with
      | nil => simp [initializationChain] at hr
      | cons current done =>
          simp only [initializationChain, List.mem_append, List.mem_singleton] at hr
          rcases hr with rfl | hr
          · cases rest <;> simp
          · exact ih (next :: current :: done) hr

```

`expansionChain_shape` is the matching shape fact for `expansionChain`'s output: every generated rule stays in the push phase and pushes exactly two symbols, which is what lets the split-and-expand construction preserve the one-turn machine's non-shrinking/non-growing constraints at every intermediate step.

```lean
@[aesop safe apply] theorem expansionChain_shape
    (old : PushdownRule α (State × TurnPhase) Stack) (done : List Stack)
    {rest : List Stack}
    {r : PushdownRule α (NormalState α State Stack × TurnPhase) (NPDA.FinalStack Stack)}
    (hr : r ∈ expansionChain old done rest) :
    r.source.2 = .push ∧ r.target.2 = .push ∧ r.push.length = 2 := by
  induction rest generalizing done with
  | nil => simp [expansionChain] at hr
  | cons next rest ih =>
      cases done with
      | nil => simp [expansionChain] at hr
      | cons current done =>
          simp only [expansionChain, List.mem_append, List.mem_singleton] at hr
          rcases hr with rfl | hr
          · cases rest <;> simp
          · exact ih (next :: current :: done) hr

```

`initializationRules_shape` lifts `initializationChain_shape` (and the direct boot cases) to the whole `initializationRules` family: every generated rule is a push-phase rule pushing at least one symbol, which is exactly the growth-direction constraint `normalizedRule_wellformed` must establish for this rule family.

```lean
theorem initializationRules_shape (M : OneTurnNPDA α State Stack)
    {r : PushdownRule α (NormalState α State Stack × TurnPhase) (NPDA.FinalStack Stack)}
    (hr : r ∈ initializationRules M) :
    r.source.2 = .push ∧ r.target.2 = .push ∧ 1 ≤ r.push.length := by
  unfold initializationRules at hr
  simp only [List.mem_flatMap] at hr
  rcases hr with ⟨q, hq, hr⟩
  cases hrev : M.initialStack.reverse with
  | nil =>
      rw [hrev] at hr
      simp only [List.mem_singleton] at hr
      subst r
      simp
  | cons first rest =>
      rw [hrev] at hr
      simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with rfl | hr
      · cases rest <;> simp
      · have hshape := initializationChain_shape q [first] hr
        exact ⟨hshape.1, hshape.2.1, by omega⟩

```

`normalizedSimulationRules_shape` establishes the full three-part phase/height discipline (`pop_stays_pop`, push-growth, pop-shrink) for the simulation rule family, splitting on whether the original rule was expanded via `expansionChain_shape` or passed through unchanged — in the latter case, the original machine's own three invariants (`pop_stays_pop`, `push_phase_nonshrinking`, `pop_phase_nongrowing`) are reused directly.

```lean
theorem normalizedSimulationRules_shape (M : OneTurnNPDA α State Stack)
    {r : PushdownRule α (NormalState α State Stack × TurnPhase) (NPDA.FinalStack Stack)}
    (hr : r ∈ normalizedSimulationRules M) :
    (r.source.2 = .pop → r.target.2 = .pop) ∧
    (r.source.2 = .push → 1 ≤ r.push.length) ∧
    (r.target.2 = .pop → r.push.length ≤ 1) := by
  unfold normalizedSimulationRules at hr
  simp only [List.mem_flatMap] at hr
  rcases hr with ⟨old, hold, hr⟩
  by_cases hp : old.source.2 = .push ∧ old.target.2 = .push
  · rw [if_pos hp] at hr
    cases hrev : old.push.reverse with
    | nil => simp [hrev] at hr
    | cons first rest =>
        rw [hrev] at hr
        simp only [List.mem_append, List.mem_singleton] at hr
        rcases hr with rfl | hr
        · cases rest <;> simp
        · have hshape := expansionChain_shape old [first] hr
          exact ⟨by simp [hshape.1, hshape.2.1],
            fun _ => by omega, by simp [hshape.2.1]⟩
  · rw [if_neg hp] at hr
    simp only [List.mem_singleton] at hr
    subst r
    constructor
    · intro hs
      exact M.pop_stays_pop old hold hs
    constructor
    · intro hs
      simpa using M.push_phase_nonshrinking old hold hs
    · intro ht
      simpa using M.pop_phase_nongrowing old hold ht

```

`enterDrainRules_shape` verifies the same discipline for the drain-entry family: every generated rule targets `.drain, .pop`, so `pop_stays_pop` is trivial, and the push/pop length bounds follow directly by unfolding the definition and case-splitting on the phase.

```lean
theorem enterDrainRules_shape (M : OneTurnNPDA α State Stack)
    {r : PushdownRule α (NormalState α State Stack × TurnPhase) (NPDA.FinalStack Stack)}
    (hr : r ∈ enterDrainRules M) :
    (r.source.2 = .pop → r.target.2 = .pop) ∧
    (r.source.2 = .push → 1 ≤ r.push.length) ∧
    (r.target.2 = .pop → r.push.length ≤ 1) := by
  unfold enterDrainRules at hr
  simp only [List.mem_flatMap, List.mem_append, List.mem_map, List.mem_singleton] at hr
  rcases hr with ⟨q, hq, phase, hphase, hr⟩
  simp only [List.mem_cons] at hphase
  rcases hphase with rfl | hphase
  · rcases hr with ⟨x, hx, rfl⟩ | rfl <;> simp
  · rcases hphase with rfl | hphase
    · rcases hr with ⟨x, hx, rfl⟩ | rfl <;> simp
    · simp at hphase

```

`normalizedDrainRules_shape` closes out the four shape lemmas: since every rule in this family already targets `.drain, .pop` or `.done, .pop`, the discipline holds by simple unfolding — after which `Internal` has proved shape facts for all four rule families that `normalizedRule_wellformed` combines outside this namespace.

```lean
theorem normalizedDrainRules_shape (M : OneTurnNPDA α State Stack)
    {r : PushdownRule α (NormalState α State Stack × TurnPhase) (NPDA.FinalStack Stack)}
    (hr : r ∈ normalizedDrainRules M) :
    (r.source.2 = .pop → r.target.2 = .pop) ∧
    (r.source.2 = .push → 1 ≤ r.push.length) ∧
    (r.target.2 = .pop → r.push.length ≤ 1) := by
  unfold normalizedDrainRules at hr
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at hr
  rcases hr with ⟨x, hx, rfl⟩ | rfl <;> simp

end Internal

```

Having proved the shape facts for each *generated* rule family inside `Internal`, we now step back outside that namespace to restate the *original* machine's three structural invariants as bare `aesop`-friendly lemmas. `original_pop_stays_pop` simply exposes `M.pop_stays_pop` in a form `aesop`'s automation can apply without unfolding the structure projection each time.

```lean
@[aesop safe apply] private theorem original_pop_stays_pop
    (M : OneTurnNPDA α State Stack)
    (r : PushdownRule α (State × TurnPhase) Stack) (hr : r ∈ M.rules)
    (hp : r.source.2 = .pop) : r.target.2 = .pop :=
  M.pop_stays_pop r hr hp

```

`original_push_nonshrinking` is the matching restatement for `push_phase_nonshrinking`, and together with its two siblings it lets the well-formedness proof below discharge the "unchanged simulation rule" case by plain `aesop`/`simpa` rather than manual field access.

```lean
@[aesop safe apply] private theorem original_push_nonshrinking
    (M : OneTurnNPDA α State Stack)
    (r : PushdownRule α (State × TurnPhase) Stack) (hr : r ∈ M.rules)
    (hp : r.source.2 = .push) : 1 ≤ r.push.length :=
  M.push_phase_nonshrinking r hr hp

```

`original_pop_nongrowing` completes the trio by restating `pop_phase_nongrowing`.

```lean
@[aesop safe apply] private theorem original_pop_nongrowing
    (M : OneTurnNPDA α State Stack)
    (r : PushdownRule α (State × TurnPhase) Stack) (hr : r ∈ M.rules)
    (hp : r.target.2 = .pop) : r.push.length ≤ 1 :=
  M.pop_phase_nongrowing r hr hp
```

`normalizedRule_wellformed` is the payoff of the whole `Internal` shape-lemma effort: it shows that *every* rule of `Internal.normalizedRules M`, regardless of which of the four families it came from, satisfies the same three-part phase/height discipline that `OneTurnNPDA`'s fields require. This is exactly the obligation `normalize` must discharge to type-check as a well-formed `OneTurnNPDA`.

```lean
private theorem normalizedRule_wellformed (M : OneTurnNPDA α State Stack)
    (r : PushdownRule α (NormalState α State Stack × TurnPhase) (NPDA.FinalStack Stack))
    (hr : r ∈ Internal.normalizedRules M) :
    (r.source.2 = .pop → r.target.2 = .pop) ∧
    (r.source.2 = .push → 1 ≤ r.push.length) ∧
    (r.target.2 = .pop → r.push.length ≤ 1) := by
  unfold Internal.normalizedRules at hr
  simp only [List.mem_append] at hr
  rcases hr with ((hr | hr) | hr) | hr
  · have h := Internal.initializationRules_shape M hr
    exact ⟨fun hp => by simp [h.1] at hp,
      fun _ => h.2.2, fun hp => by simp [h.2.1] at hp⟩
  · exact Internal.normalizedSimulationRules_shape M hr
  · exact Internal.enterDrainRules_shape M hr
  · exact Internal.normalizedDrainRules_shape M hr
```

`normalize` is the constructive payoff of the whole `Internal` machinery: it packages `Internal.normalizedRules` together with the canonical `.boot`/`.done`/bottom-marker fields into a genuine `OneTurnNPDA`, discharging its three structural obligations directly from `normalizedRule_wellformed`. Its output is the machine whose rules are guaranteed to push at most two symbols, which downstream conversions rely on.

```lean
/-- Split multi-symbol pushes and normalize acceptance to one bottom marker,
one start state, and one final state. -/
public def normalize (M : OneTurnNPDA α State Stack) :
    OneTurnNPDA α (NormalState α State Stack) (NPDA.FinalStack Stack) where
  rules := Internal.normalizedRules M
  start := [.boot]
  accept := [.done]
  initialStack := [.bottom]
  pop_stays_pop := by
    intro r hr hp
    exact (normalizedRule_wellformed M r hr).1 hp
  push_phase_nonshrinking := by
    intro r hr hp
    exact (normalizedRule_wellformed M r hr).2.1 hp
  pop_phase_nongrowing := by
    intro r hr hp
    exact (normalizedRule_wellformed M r hr).2.2 hp
```

`normalize_rule_shape` sharpens `normalizedRule_wellformed`'s height-direction bounds into the concrete numeric claim that every normalized rule pushes at most two symbols. Case-splitting on `NormalizedRuleKind` handles the generated families by `simp` alone (their shape is syntactically visible), while the `simulate` case must additionally reason about the original rule's phase to rule out a push exceeding length two.

```lean
/-- Every normalized rule changes stack height by at most one: its replacement
word has length zero, one, or two, with the phase constraints ruling out the
wrong direction. -/


@[grind .] public theorem normalize_rule_shape (M : OneTurnNPDA α State Stack)
    {r : PushdownRule α
      (NormalState α State Stack × TurnPhase) (NPDA.FinalStack Stack)}
    (hr : r ∈ M.normalize.rules) :
    r.push.length ≤ 2 ∧
      (r.source.2 = .push → 1 ≤ r.push.length) ∧
      (r.target.2 = .pop → r.push.length ≤ 1) := by
  have hkind := Internal.normalizedRule_kind M hr
  have hwell := normalizedRule_wellformed M r hr
  refine ⟨?_, hwell.2⟩
  cases hkind with
  | bootEmpty q hq hstack => simp
  | bootCons q hq first rest hstack => simp
  | initStep q hq current done next rest => simp
  | split old hold first rest hphase hpush => simp
  | expand old hold current done next rest hphase hpush => simp
  | simulate old hold hphase =>
      cases hs : old.source.2 <;> cases ht : old.target.2
      · simp [hs, ht] at hphase
      · have := M.pop_phase_nongrowing old hold (by simp [ht])
        simpa using (show old.push.length ≤ 2 by omega)
      · have hstay := M.pop_stays_pop old hold hs
        simp [ht] at hstay
      · have := M.pop_phase_nongrowing old hold (by simp [ht])
        simpa using (show old.push.length ≤ 2 by omega)
  | enterOld q hq phase hphase x hx =>
      cases phase <;> simp
  | enterBottom q hq phase hphase =>
      cases phase <;> simp
  | drainOld x hx => simp
  | drainBottom => simp
```

`normalize_done_rule` isolates the unique syntactic shape of any rule that transitions into `.done`: it must be a pop-phase, epsilon, empty-push rule. `NormalizedRuleKind`'s ten constructors are checked exhaustively — only `drainBottom` (and the `enterBottom` pop case) can actually target `.done`, and the rest are dismissed because their target's first component can never be `.done`.

```lean
/-- A normalized rule entering the unique final state is the last pop-phase
step and removes its inspected symbol without consuming input. -/


@[grind .] public theorem normalize_done_rule (M : OneTurnNPDA α State Stack)
    {r : PushdownRule α
      (NormalState α State Stack × TurnPhase) (NPDA.FinalStack Stack)}
    (hr : r ∈ M.normalize.rules) (hdone : r.target.1 = .done) :
    r.source.2 = .pop ∧ r.target.2 = .pop ∧ r.push = [] ∧ r.input = none := by
  have hkind := Internal.normalizedRule_kind M hr
  cases hkind with
  | bootEmpty => simp at hdone
  | bootCons q hq first rest hstack =>
      split at hdone <;> simp at hdone
  | initStep q hq current done next rest =>
      split at hdone <;> simp at hdone
  | split old hold first rest hphase hpush =>
      split at hdone <;> simp at hdone
  | expand old hold current done next rest hphase hpush =>
      split at hdone <;> simp at hdone
  | simulate => simp at hdone
  | enterOld => simp at hdone
  | enterBottom q hq phase hphase =>
      cases phase <;> simp_all
  | drainOld => simp at hdone
  | drainBottom => simp
```

### 正規化実行の意味的不変条件

管理状態は、元のスタックを `old` 記号へ写した列の末尾に唯一の `bottom` を置く。
`initialize` は初期スタックを一記号ずつ構築し、`expand` は長い push を局所的な
長さ 2 以下の規則へ分割する。`NormalRunGood` は各管理状態について、正規化側の
構成と元の機械の到達可能構成を対応付ける。特に `done` ではスタックが空であり、
元の機械が受理状態へ到達済みであることを保持する。

```lean
/-- Original-machine acceptance evidence with a possibly unread suffix. -/
def AcceptingPrefix (M : OneTurnNPDA α State Stack) (word input : List α) : Prop :=
  ∃ q₀ ∈ M.start, ∃ qf ∈ M.accept, ∃ phase stack,
    M.Reaches (word, (q₀, .push), M.initialStack) (input, (qf, phase), stack)
```

`NormalRunGood` is the `OneTurnNPDA` analogue of `NPDA.FinalRunGood`, but with more control-state cases since `NormalState` has six constructors instead of four: `.boot`/`.initialize` must be in the push phase or the invariant is `False`, `.sim` and the mid-`.expand` states track a genuine original-machine `Reaches` witness (the latter also remembering which original rule is being split), and `.drain`/`.done` carry an `AcceptingPrefix` witness. Every phase/state combination that cannot actually occur (e.g. `.boot` in the pop phase) is pinned to `False` so the invariant is vacuously easy to falsify there.

```lean
/-- The semantic invariant carried by initialization, split pushes, simulation,
and final stack draining. -/


def NormalRunGood (M : OneTurnNPDA α State Stack) (word : List α) :
    ID α (NormalState α State Stack) (NPDA.FinalStack Stack) → Prop
  | (input, (.boot, .push), stack) => input = word ∧ stack = [.bottom]
  | (_, (.boot, .pop), _) => False
  | (input, (.initialize q done remaining, .push), stack) =>
      q ∈ M.start ∧ input = word ∧
      M.initialStack = remaining.reverse ++ done ∧
      stack = done.map NPDA.FinalStack.old ++ [.bottom]
  | (_, (.initialize _ _ _, .pop), _) => False
  | (input, (.sim q, phase), stack) =>
      ∃ q₀ ∈ M.start, ∃ oldStack,
        stack = oldStack.map NPDA.FinalStack.old ++ [.bottom] ∧
        M.Reaches (word, (q₀, .push), M.initialStack)
          (input, (q, phase), oldStack)
  | (input, (.expand old done remaining, .push), stack) =>
      ∃ q₀ ∈ M.start, ∃ tail,
        old ∈ M.rules ∧ old.source.2 = .push ∧ old.target.2 = .push ∧
        old.push = remaining.reverse ++ done ∧
        stack = done.map NPDA.FinalStack.old ++
          tail.map NPDA.FinalStack.old ++ [.bottom] ∧
        M.Reaches (word, (q₀, .push), M.initialStack)
          (old.input.toList ++ input, old.source, old.pop :: tail)
  | (_, (.expand _ _ _, .pop), _) => False
  | (input, (.drain, .pop), stack) =>
      (∃ oldStack : List Stack,
        stack = oldStack.map NPDA.FinalStack.old ++ [.bottom]) ∧
      AcceptingPrefix M word input
  | (_, (.drain, .push), _) => False
  | (input, (.done, .pop), stack) =>
      stack = [] ∧ AcceptingPrefix M word input
  | (_, (.done, .push), _) => False
```

`normal_old_cons_parts` is the `OneTurnNPDA` counterpart of `NPDA.old_cons_parts`: it un-wraps an embedded stack that starts with `.old x` back to the underlying original-alphabet stack `x :: rest`. It recurs throughout `normalizeStep_run_good` whenever a normalized rule pops an `.old` symbol.

```lean
private theorem normal_old_cons_parts {x : Stack} {tail : List (NPDA.FinalStack Stack)}
    {stack : List Stack}
    (h : NPDA.FinalStack.old x :: tail =
      stack.map NPDA.FinalStack.old ++ [NPDA.FinalStack.bottom]) :
    ∃ rest, stack = x :: rest ∧
      tail = rest.map NPDA.FinalStack.old ++ [NPDA.FinalStack.bottom] := by
  cases stack with
  | nil => simp at h
  | cons y stack =>
      simp only [List.map_cons, List.cons_append] at h
      obtain ⟨hy, htail⟩ := List.cons.inj h
      cases hy
      exact ⟨stack, rfl, htail⟩
```

`normal_bottom_parts` is the dual inversion for the bottom marker: seeing `.bottom` at the head of an embedded stack forces the whole thing to be empty, since `.bottom` only ever appears as the final symbol. Used at the transitions that pop the bottom marker, i.e. entering `.done`.

```lean
private theorem normal_bottom_parts {tail : List (NPDA.FinalStack Stack)}
    {stack : List Stack}
    (h : NPDA.FinalStack.bottom :: tail =
      stack.map NPDA.FinalStack.old ++ [NPDA.FinalStack.bottom]) :
    stack = [] ∧ tail = [] := by
  cases stack with
  | nil => simpa using h
  | cons x stack =>
      simp only [List.map_cons, List.cons_append] at h
      cases (List.cons.inj h).1
```

`originalRule_step` repackages a rule of the *original* one-turn machine as a `Step` of `M.toNPDA`, choosing `Step.consume` or `Step.epsilon` depending on whether the rule reads input. This bridges the gap between reasoning about `M.rules` directly (as `NormalRunGood`'s `.expand` case does) and the generic `NPDA.Step`/`Reaches` machinery.

```lean
private theorem originalRule_step (M : OneTurnNPDA α State Stack)
    (r : PushdownRule α (State × TurnPhase) Stack) (hr : r ∈ M.rules)
    (input : List α) (tail : List Stack) :
    M.Step (r.input.toList ++ input, r.source, r.pop :: tail)
      (input, r.target, r.push ++ tail) := by
  cases hinput : r.input with
  | none =>
      simpa [hinput, toNPDA] using
        NPDA.Step.epsilon r hr hinput (input := input) (stack := tail)
  | some a =>
      simpa [hinput, toNPDA] using
        NPDA.Step.consume r hr hinput (input := input) (stack := tail)
```

`normalizeStep_run_good` is the main preservation step, the `OneTurnNPDA` analogue of `NPDA.finalStep_run_good`: it case-splits on `NormalizedRuleKind` and, for each of the ten rule shapes, either derives a contradiction from `NormalRunGood`'s current phase (many combinations are impossible given the source rule's fixed phase) or reconstructs the invariant at the successor configuration, using `normal_old_cons_parts`/`normal_bottom_parts` and `originalRule_step` to translate stack shape facts back into original-machine reachability.

```lean
/-- One generated normalization step preserves the semantic run invariant. -/
theorem normalizeStep_run_good (M : OneTurnNPDA α State Stack)
    (word : List α)
    {c c' : ID α (NormalState α State Stack) (NPDA.FinalStack Stack)}
    (h : M.normalize.Step c c') : M.NormalRunGood word c → M.NormalRunGood word c' := by
  cases h with
  | @consume a input tail r hr input_eq =>
      have hkind := Internal.normalizedRule_kind M hr
      cases hkind with
      | bootEmpty q hq hstack => simp at input_eq
      | bootCons q hq first rest hstack => simp at input_eq
      | initStep q hq current done next rest => simp at input_eq
      | split old hold first rest hphase hpush =>
          intro hgood
          rcases hgood with ⟨q₀, hq₀, oldStack, hstack, hreach⟩
          obtain ⟨oldTail, rfl, htail⟩ := normal_old_cons_parts hstack
          cases rest with
          | nil =>
              have holdPush : old.push = [first] := by
                have := congrArg List.reverse hpush
                simpa using this
              refine ⟨q₀, hq₀, old.push ++ oldTail, ?_, ?_⟩
              · simpa [holdPush] using htail
              · have hs : old.source = (old.source.1, TurnPhase.push) := by
                  exact Prod.ext rfl hphase.1
                have hreach' : M.Reaches
                    (word, (q₀, .push), M.initialStack)
                    (a :: input, old.source, old.pop :: oldTail) := by
                  rw [hs]
                  exact hreach
                have hout := hreach'.tail (NPDA.Step.consume old hold input_eq)
                have ht : old.target = (old.target.1, TurnPhase.push) := by
                  exact Prod.ext rfl hphase.2
                rw [← ht]
                exact hout
          | cons next rest =>
              refine ⟨q₀, hq₀, oldTail, hold, hphase.1, hphase.2, ?_, ?_, ?_⟩
              · have := congrArg List.reverse hpush
                simpa [List.append_assoc] using this
              · simpa using htail
              · have hs : old.source = (old.source.1, TurnPhase.push) := by
                  exact Prod.ext rfl hphase.1
                rw [hs, input_eq]
                exact hreach
      | expand old hold current done next rest hphase hpush => simp at input_eq
      | simulate old hold hphase =>
          intro hgood
          rcases hgood with ⟨q₀, hq₀, oldStack, hstack, hreach⟩
          obtain ⟨oldTail, rfl, htail⟩ := normal_old_cons_parts hstack
          refine ⟨q₀, hq₀, old.push ++ oldTail, ?_, ?_⟩
          · simpa [List.map_append, List.append_assoc] using htail
          · exact hreach.tail (NPDA.Step.consume old hold input_eq)
      | enterOld q hq phase hphase x hx => simp at input_eq
      | enterBottom q hq phase hphase => simp at input_eq
      | drainOld x hx => simp at input_eq
      | drainBottom => simp at input_eq
  | @epsilon input tail r hr input_eq =>
      have hkind := Internal.normalizedRule_kind M hr
      cases hkind with
      | bootEmpty q hq hstack =>
          rintro ⟨hword, htail⟩
          simp only [List.cons.injEq, true_and] at htail
          subst tail
          have hinitial : M.initialStack = [] := by
            have := congrArg List.reverse hstack
            simpa using this
          refine ⟨q, hq, [], by simp, ?_⟩
          simpa [hword, hinitial] using
            (Relation.ReflTransGen.refl : M.Reaches
              (input, (q, .push), M.initialStack) (input, (q, .push), M.initialStack))
      | bootCons q hq first rest hstack =>
          rintro ⟨hword, htail⟩
          simp only [List.cons.injEq, true_and] at htail
          subst tail
          cases rest with
          | nil =>
              have hinitial : M.initialStack = [first] := by
                have := congrArg List.reverse hstack
                simpa using this
              refine ⟨q, hq, [first], by simp, ?_⟩
              simpa [hword, hinitial] using
                (Relation.ReflTransGen.refl : M.Reaches
                  (input, (q, .push), M.initialStack)
                    (input, (q, .push), M.initialStack))
          | cons next rest =>
              refine ⟨hq, hword, ?_, by simp⟩
              have := congrArg List.reverse hstack
              simpa [List.append_assoc] using this
      | initStep q hq current done next rest =>
          rintro ⟨hstart, hword, hinitial, hstack⟩
          simp only [List.map_cons, List.cons_append] at hstack
          have htail := (List.cons.inj hstack).2
          cases rest with
          | nil =>
              refine ⟨q, hstart, next :: current :: done, ?_, ?_⟩
              · simpa using htail
              · simpa [hword, hinitial] using
                  (Relation.ReflTransGen.refl : M.Reaches
                    (input, (q, .push), M.initialStack)
                      (input, (q, .push), M.initialStack))
          | cons after rest =>
              refine ⟨hstart, hword, ?_, ?_⟩
              · simpa [List.append_assoc] using hinitial
              · simpa using htail
      | split old hold first rest hphase hpush =>
          intro hgood
          rcases hgood with ⟨q₀, hq₀, oldStack, hstack, hreach⟩
          obtain ⟨oldTail, rfl, htail⟩ := normal_old_cons_parts hstack
          cases rest with
          | nil =>
              have holdPush : old.push = [first] := by
                have := congrArg List.reverse hpush
                simpa using this
              refine ⟨q₀, hq₀, old.push ++ oldTail, ?_, ?_⟩
              · simpa [holdPush] using htail
              · have hs : old.source = (old.source.1, TurnPhase.push) := by
                  exact Prod.ext rfl hphase.1
                have hreach' : M.Reaches
                    (word, (q₀, .push), M.initialStack)
                    (input, old.source, old.pop :: oldTail) := by
                  rw [hs]
                  exact hreach
                have hout := hreach'.tail (NPDA.Step.epsilon old hold input_eq)
                have ht : old.target = (old.target.1, TurnPhase.push) := by
                  exact Prod.ext rfl hphase.2
                rw [← ht]
                exact hout
          | cons next rest =>
              refine ⟨q₀, hq₀, oldTail, hold, hphase.1, hphase.2, ?_, ?_, ?_⟩
              · have := congrArg List.reverse hpush
                simpa [List.append_assoc] using this
              · simpa using htail
              · have hs : old.source = (old.source.1, TurnPhase.push) := by
                  exact Prod.ext rfl hphase.1
                rw [hs, input_eq]
                exact hreach
      | expand old hold current done next rest hphase hpush =>
          intro hgood
          rcases hgood with
            ⟨q₀, hq₀, oldTail, hold', hsource, htarget, holdPush, hstack, hreach⟩
          simp only [List.map_cons, List.cons_append] at hstack
          have htail := (List.cons.inj hstack).2
          cases rest with
          | nil =>
              refine ⟨q₀, hq₀, old.push ++ oldTail, ?_, ?_⟩
              · simpa [holdPush, List.map_append, List.append_assoc] using htail
              · have hs : old.target = (old.target.1, TurnPhase.push) := by
                  exact Prod.ext rfl htarget
                rw [← hs]
                exact hreach.tail (originalRule_step M old hold' input oldTail)
          | cons after rest =>
              refine ⟨q₀, hq₀, oldTail, hold', hsource, htarget, ?_, ?_, hreach⟩
              · simpa [List.append_assoc] using holdPush
              · simpa using htail
      | simulate old hold hphase =>
          intro hgood
          rcases hgood with ⟨q₀, hq₀, oldStack, hstack, hreach⟩
          obtain ⟨oldTail, rfl, htail⟩ := normal_old_cons_parts hstack
          refine ⟨q₀, hq₀, old.push ++ oldTail, ?_, ?_⟩
          · simpa [List.map_append, List.append_assoc] using htail
          · exact hreach.tail (NPDA.Step.epsilon old hold input_eq)
      | enterOld q hq phase hphase x hx =>
          intro hgood
          rcases hgood with ⟨q₀, hq₀, oldStack, hstack, hreach⟩
          obtain ⟨oldTail, rfl, htail⟩ := normal_old_cons_parts hstack
          cases phase with
          | push =>
              exact ⟨⟨x :: oldTail, by simpa using htail⟩,
                q₀, hq₀, q, hq, .push, x :: oldTail, hreach⟩
          | pop =>
              exact ⟨⟨oldTail, by simpa using htail⟩,
                q₀, hq₀, q, hq, .pop, x :: oldTail, hreach⟩
      | enterBottom q hq phase hphase =>
          intro hgood
          rcases hgood with ⟨q₀, hq₀, oldStack, hstack, hreach⟩
          obtain ⟨rfl, rfl⟩ := normal_bottom_parts hstack
          cases phase with
          | push =>
              exact ⟨⟨[], by simp⟩, q₀, hq₀, q, hq, .push, [], hreach⟩
          | pop =>
              exact ⟨rfl, q₀, hq₀, q, hq, .pop, [], hreach⟩
      | drainOld x hx =>
          rintro ⟨⟨oldStack, hstack⟩, haccept⟩
          obtain ⟨oldTail, rfl, htail⟩ := normal_old_cons_parts hstack
          exact ⟨⟨oldTail, by simpa using htail⟩, haccept⟩
      | drainBottom =>
          rintro ⟨⟨oldStack, hstack⟩, haccept⟩
          obtain ⟨rfl, rfl⟩ := normal_bottom_parts hstack
          exact ⟨rfl, haccept⟩
```

Extending `normalizeStep_run_good` by induction over `Reaches` gives the full-run version, exactly as `NPDA.finalReaches_run_good` did for `finalToEmpty`: the invariant established at the `.boot` starting configuration is carried unchanged through any complete normalized run.

```lean
/-- The semantic invariant propagates over a complete normalized run. -/
theorem normalizeReaches_run_good (M : OneTurnNPDA α State Stack)
    (word : List α)
    {c c' : ID α (NormalState α State Stack) (NPDA.FinalStack Stack)}
    (h : M.normalize.Reaches c c') : M.NormalRunGood word c → M.NormalRunGood word c' := by
  induction h with
  | refl => exact id
  | tail h step ih => exact fun hc => M.normalizeStep_run_good word step (ih hc)
```

### 元の実行と正規化実行の相互変換

生成した規則族ごとの所属補題を使い、初期化、元規則のシミュレーション、受理後の
drain を具体的な到達列として構成する。複数記号 push は先頭記号を保持したまま
`expand` 状態を進み、元の置換語と同じ順序のスタックを復元する。この層では入力の
消費と epsilon 遷移を区別したまま、元の到達列全体を正規化側へ持ち上げる。

`initializationRule_mem` は初期化規則族の所属補題で、`initializationChain_reaches` などが構成する遷移が実際に `M.normalize.rules` の要素であることを保証する。以下4つの `_mem` 補題は `Internal.normalizedRules` の連結構造をなぞって、4つの規則族それぞれの所属を一度に確認する。

```lean
private theorem initializationRule_mem (M : OneTurnNPDA α State Stack)
    {r : PushdownRule α (NormalState α State Stack × TurnPhase)
      (NPDA.FinalStack Stack)} (hr : r ∈ Internal.initializationRules M) :
    r ∈ M.normalize.rules := by
  simp only [normalize, Internal.normalizedRules, List.mem_append]
  exact Or.inl (Or.inl (Or.inl hr))
```

`simulationRule_mem` is the corresponding membership lemma for the simulation family, used by `Step.normalize` whenever an original rule (split or unchanged) is lifted into a normalized step.

```lean
private theorem simulationRule_mem (M : OneTurnNPDA α State Stack)
    {r : PushdownRule α (NormalState α State Stack × TurnPhase)
      (NPDA.FinalStack Stack)} (hr : r ∈ Internal.normalizedSimulationRules M) :
    r ∈ M.normalize.rules := by
  simp only [normalize, Internal.normalizedRules, List.mem_append]
  exact Or.inl (Or.inl (Or.inr hr))
```

`enterRule_mem` is the membership lemma for the drain-entry family, used later in `accepted_reaches_done` to justify the step out of `.sim` once an accept state is reached.

```lean
private theorem enterRule_mem (M : OneTurnNPDA α State Stack)
    {r : PushdownRule α (NormalState α State Stack × TurnPhase)
      (NPDA.FinalStack Stack)} (hr : r ∈ Internal.enterDrainRules M) :
    r ∈ M.normalize.rules := by
  simp only [normalize, Internal.normalizedRules, List.mem_append]
  exact Or.inl (Or.inr hr)
```

`normalizedDrainRule_mem` closes out this quartet, giving `normalizedDrain_reaches_done` its stepping stones through the `.drain` phase.

```lean
private theorem normalizedDrainRule_mem (M : OneTurnNPDA α State Stack)
    {r : PushdownRule α (NormalState α State Stack × TurnPhase)
      (NPDA.FinalStack Stack)} (hr : r ∈ Internal.normalizedDrainRules M) :
    r ∈ M.normalize.rules := by
  simp only [normalize, Internal.normalizedRules, List.mem_append]
  exact Or.inr hr
```

With the membership lemmas in hand, `initializationChain_reaches` constructs an explicit `Reaches` witness for one `initializationChain` recursion step: it either takes a single step directly to `.sim q` (base case) or one step followed by a recursive appeal to itself, threading the accumulated `done`/`remaining` split exactly as `initializationChain` does syntactically.

```lean
private theorem initializationChain_reaches (M : OneTurnNPDA α State Stack)
    (q : State) (current : Stack) (done : List Stack) (next : Stack)
    (rest : List Stack) (input : List α)
    (hall : ∀ r, r ∈ Internal.initializationChain (α := α) q
      (current :: done) (next :: rest) → r ∈ Internal.initializationRules M) :
    M.normalize.Reaches
      (input, (.initialize q (current :: done) (next :: rest), .push),
        (current :: done).map NPDA.FinalStack.old ++ [.bottom])
      (input, (.sim q, .push),
        ((next :: rest).reverse ++ current :: done).map NPDA.FinalStack.old ++
          [.bottom]) := by
  let r : PushdownRule α
      (NormalState α State Stack × TurnPhase) (NPDA.FinalStack Stack) :=
    { source := (.initialize q (current :: done) (next :: rest), .push),
      input := none, pop := .old current,
      target := (if rest.isEmpty then (.sim q, .push)
        else (.initialize q (next :: current :: done) rest, .push)),
      push := [.old next, .old current] }
  have hrChain : r ∈ Internal.initializationChain q (current :: done) (next :: rest) := by
    simp [r, Internal.initializationChain]
  have hr := M.initializationRule_mem (hall r hrChain)
  have first : M.normalize.Step
      (input, (.initialize q (current :: done) (next :: rest), .push),
        (current :: done).map NPDA.FinalStack.old ++ [.bottom])
      (input, r.target,
        (next :: current :: done).map NPDA.FinalStack.old ++ [.bottom]) := by
    simpa [r] using NPDA.Step.epsilon r hr rfl
  cases rest with
  | nil =>
      simpa [r] using Relation.ReflTransGen.single first
  | cons after rest =>
      have hall' : ∀ r, r ∈ Internal.initializationChain (α := α) q
          (next :: current :: done) (after :: rest) →
          r ∈ Internal.initializationRules M := by
        intro old hold
        apply hall old
        rw [Internal.initializationChain]
        exact List.mem_append_right _ hold
      simpa [r, List.append_assoc] using
        (initializationChain_reaches M q next (current :: done) after rest input
          hall').head (by simpa [r] using first)
```

`initialization_reaches` is the top-level counterpart that handles the *whole* initial stack, not just one chain step: it dispatches on whether the reversed initial stack is empty, a singleton, or longer, invoking `initializationChain_reaches` only in the last case. The result is the single reachability fact `Step.normalize`'s callers (ultimately `normalize_language`) need to get from `.boot` to the simulation phase with the entire initial stack embedded.

```lean
private theorem initialization_reaches (M : OneTurnNPDA α State Stack)
    (q : State) (hq : q ∈ M.start) (input : List α) :
    M.normalize.Reaches
      (input, (.boot, .push), [NPDA.FinalStack.bottom])
      (input, (.sim q, .push),
        M.initialStack.map NPDA.FinalStack.old ++ [.bottom]) := by
  cases hstack : M.initialStack.reverse with
  | nil =>
      let r : PushdownRule α
          (NormalState α State Stack × TurnPhase) (NPDA.FinalStack Stack) :=
        { source := (.boot, .push), input := none, pop := .bottom,
          target := (.sim q, .push), push := [.bottom] }
      have hrInit : r ∈ Internal.initializationRules M := by
        unfold Internal.initializationRules
        apply List.mem_flatMap.mpr
        refine ⟨q, hq, ?_⟩
        rw [hstack]
        simp [r]
      have hs : M.initialStack = [] := by
        have := congrArg List.reverse hstack
        simpa using this
      simpa [r, hs] using Relation.ReflTransGen.single
        (NPDA.Step.epsilon r (M.initializationRule_mem hrInit) rfl)
  | cons first rest =>
      let r : PushdownRule α
          (NormalState α State Stack × TurnPhase) (NPDA.FinalStack Stack) :=
        { source := (.boot, .push), input := none, pop := .bottom,
          target := (if rest.isEmpty then (.sim q, .push)
            else (.initialize q [first] rest, .push)),
          push := [.old first, .bottom] }
      have hrInit : r ∈ Internal.initializationRules M := by
        unfold Internal.initializationRules
        apply List.mem_flatMap.mpr
        refine ⟨q, hq, ?_⟩
        rw [hstack]
        exact List.mem_append_left _ (by simp [r])
      have firstStep : M.normalize.Step
          (input, (.boot, .push), [NPDA.FinalStack.bottom])
          (input, r.target, [.old first, .bottom]) := by
        simpa [r] using NPDA.Step.epsilon r (M.initializationRule_mem hrInit) rfl
      cases rest with
      | nil =>
          have hs : M.initialStack = [first] := by
            have := congrArg List.reverse hstack
            simpa using this
          simpa [r, hs] using Relation.ReflTransGen.single firstStep
      | cons next rest =>
          have hall : ∀ old,
              old ∈ Internal.initializationChain (α := α) q [first]
                (next :: rest) → old ∈ Internal.initializationRules M := by
            intro old hold
            unfold Internal.initializationRules
            apply List.mem_flatMap.mpr
            refine ⟨q, hq, ?_⟩
            rw [hstack]
            exact List.mem_append_right _ hold
          have hchain := initializationChain_reaches M q first [] next rest input hall
          have hs : M.initialStack = (next :: rest).reverse ++ [first] := by
            have := congrArg List.reverse hstack
            simpa [List.append_assoc] using this
          simpa [r, hs] using
            (Relation.ReflTransGen.single firstStep).trans hchain
```

`expansionChain_reaches` mirrors `initializationChain_reaches` for the `expand` family: it constructs an explicit run through one long push's epsilon chain, carrying an arbitrary already-pushed `tail` alongside the portion of the original push being rebuilt. This threading of `tail` is what lets `Step.normalize` splice a split-push transition into a larger surrounding computation.

```lean
private theorem expansionChain_reaches (M : OneTurnNPDA α State Stack)
    (old : PushdownRule α (State × TurnPhase) Stack)
    (current : Stack) (done : List Stack) (next : Stack) (rest : List Stack)
    (input : List α) (tail : List Stack)
    (hall : ∀ r, r ∈ Internal.expansionChain old (current :: done) (next :: rest) →
      r ∈ Internal.normalizedSimulationRules M) :
    M.normalize.Reaches
      (input, (.expand old (current :: done) (next :: rest), .push),
        (current :: done).map NPDA.FinalStack.old ++
          tail.map NPDA.FinalStack.old ++ [.bottom])
      (input, (.sim old.target.1, .push),
        ((next :: rest).reverse ++ current :: done).map NPDA.FinalStack.old ++
          tail.map NPDA.FinalStack.old ++ [.bottom]) := by
  let r : PushdownRule α
      (NormalState α State Stack × TurnPhase) (NPDA.FinalStack Stack) :=
    { source := (.expand old (current :: done) (next :: rest), .push),
      input := none, pop := .old current,
      target := (if rest.isEmpty then (.sim old.target.1, .push)
        else (.expand old (next :: current :: done) rest, .push)),
      push := [.old next, .old current] }
  have hrChain : r ∈ Internal.expansionChain old (current :: done) (next :: rest) := by
    simp [r, Internal.expansionChain]
  have hr := M.simulationRule_mem (hall r hrChain)
  have first : M.normalize.Step
      (input, (.expand old (current :: done) (next :: rest), .push),
        (current :: done).map NPDA.FinalStack.old ++
          tail.map NPDA.FinalStack.old ++ [.bottom])
      (input, r.target, (next :: current :: done).map NPDA.FinalStack.old ++
        tail.map NPDA.FinalStack.old ++ [.bottom]) := by
    simpa [r] using NPDA.Step.epsilon r hr rfl
  cases rest with
  | nil => simpa [r] using Relation.ReflTransGen.single first
  | cons after rest =>
      have hall' : ∀ r, r ∈ Internal.expansionChain old
          (next :: current :: done) (after :: rest) →
          r ∈ Internal.normalizedSimulationRules M := by
        intro nextRule hnext
        apply hall nextRule
        rw [Internal.expansionChain]
        exact List.mem_append_right _ hnext
      simpa [r, List.append_assoc] using
        (expansionChain_reaches M old next (current :: done) after rest input tail
          hall').head (by simpa [r] using first)
```

`Step.normalize` is the central lifting theorem: it takes one step of the original one-turn machine and produces a `Reaches` (not just `Step`!) witness in the normalized machine, because a single long-push rule may need to unfold into several epsilon steps via `expansionChain_reaches`. It splits on whether the rule is a push-to-push rule (needing possible expansion) or not (embedded unchanged), and further on whether the step consumed input or was an epsilon transition.

```lean
/-- Lift one original transition to the normalized machine, expanding a long
push into a finite epsilon chain when necessary. -/


theorem Step.normalize {M : OneTurnNPDA α State Stack}
    {c c' : ID α State Stack} (h : M.Step c c') :
    M.normalize.Reaches
      (c.1, (.sim c.2.1.1, c.2.1.2),
        c.2.2.map NPDA.FinalStack.old ++ [.bottom])
      (c'.1, (.sim c'.2.1.1, c'.2.1.2),
        c'.2.2.map NPDA.FinalStack.old ++ [.bottom]) := by
  cases h with
  | @consume a input tail old hold input_eq =>
      by_cases hphase : old.source.2 = .push ∧ old.target.2 = .push
      · have hlen : 1 ≤ old.push.length :=
          M.push_phase_nonshrinking old hold hphase.1
        cases hpush : old.push.reverse with
        | nil =>
            have hempty : old.push = [] := List.reverse_eq_nil_iff.mp hpush
            have hzero : old.push.length = 0 := List.length_eq_zero_iff.mpr hempty
            omega
        | cons first rest =>
            let r : PushdownRule α
                (NormalState α State Stack × TurnPhase) (NPDA.FinalStack Stack) :=
              { source := (.sim old.source.1, .push), input := old.input,
                pop := .old old.pop,
                target := (if rest.isEmpty then (.sim old.target.1, .push)
                  else (.expand old [first] rest, .push)),
                push := [.old first] }
            have hrSim : r ∈ Internal.normalizedSimulationRules M := by
              unfold Internal.normalizedSimulationRules
              apply List.mem_flatMap.mpr
              refine ⟨old, hold, ?_⟩
              rw [if_pos hphase, hpush]
              exact List.mem_append_left _ (by simp [r])
            have firstStep : M.normalize.Step
                (a :: input, (.sim old.source.1, .push),
                  NPDA.FinalStack.old old.pop ::
                    tail.map NPDA.FinalStack.old ++ [.bottom])
                (input, r.target,
                  NPDA.FinalStack.old first ::
                    tail.map NPDA.FinalStack.old ++ [.bottom]) := by
              simpa [r] using NPDA.Step.consume r (M.simulationRule_mem hrSim) input_eq
            cases rest with
            | nil =>
                have hword : old.push = [first] := by
                  have := congrArg List.reverse hpush
                  simpa using this
                simpa [r, hphase.1, hphase.2, hword] using
                  Relation.ReflTransGen.single firstStep
            | cons next rest =>
                have hall : ∀ nextRule,
                    nextRule ∈ Internal.expansionChain old [first] (next :: rest) →
                    nextRule ∈ Internal.normalizedSimulationRules M := by
                  intro nextRule hnext
                  unfold Internal.normalizedSimulationRules
                  apply List.mem_flatMap.mpr
                  refine ⟨old, hold, ?_⟩
                  rw [if_pos hphase, hpush]
                  exact List.mem_append_right _ hnext
                have hchain := expansionChain_reaches M old first [] next rest input tail hall
                have hword : old.push = (next :: rest).reverse ++ [first] := by
                  have := congrArg List.reverse hpush
                  simpa [List.append_assoc] using this
                simpa [r, hphase.1, hphase.2, hword, List.map_append,
                  List.append_assoc] using
                  (Relation.ReflTransGen.single firstStep).trans hchain
      · let r : PushdownRule α
            (NormalState α State Stack × TurnPhase) (NPDA.FinalStack Stack) :=
          { source := (.sim old.source.1, old.source.2), input := old.input,
            pop := .old old.pop, target := (.sim old.target.1, old.target.2),
            push := old.push.map NPDA.FinalStack.old }
        have hrSim : r ∈ Internal.normalizedSimulationRules M := by
          unfold Internal.normalizedSimulationRules
          apply List.mem_flatMap.mpr
          refine ⟨old, hold, ?_⟩
          rw [if_neg hphase]
          simp [r]
        simpa [r, List.map_append, List.append_assoc] using
          Relation.ReflTransGen.single
            (NPDA.Step.consume r (M.simulationRule_mem hrSim) input_eq)
  | @epsilon input tail old hold input_eq =>
      by_cases hphase : old.source.2 = .push ∧ old.target.2 = .push
      · have hlen : 1 ≤ old.push.length :=
          M.push_phase_nonshrinking old hold hphase.1
        cases hpush : old.push.reverse with
        | nil =>
            have hempty : old.push = [] := List.reverse_eq_nil_iff.mp hpush
            have hzero : old.push.length = 0 := List.length_eq_zero_iff.mpr hempty
            omega
        | cons first rest =>
            let r : PushdownRule α
                (NormalState α State Stack × TurnPhase) (NPDA.FinalStack Stack) :=
              { source := (.sim old.source.1, .push), input := old.input,
                pop := .old old.pop,
                target := (if rest.isEmpty then (.sim old.target.1, .push)
                  else (.expand old [first] rest, .push)),
                push := [.old first] }
            have hrSim : r ∈ Internal.normalizedSimulationRules M := by
              unfold Internal.normalizedSimulationRules
              apply List.mem_flatMap.mpr
              refine ⟨old, hold, ?_⟩
              rw [if_pos hphase, hpush]
              exact List.mem_append_left _ (by simp [r])
            have firstStep : M.normalize.Step
                (input, (.sim old.source.1, .push),
                  NPDA.FinalStack.old old.pop ::
                    tail.map NPDA.FinalStack.old ++ [.bottom])
                (input, r.target,
                  NPDA.FinalStack.old first ::
                    tail.map NPDA.FinalStack.old ++ [.bottom]) := by
              simpa [r] using NPDA.Step.epsilon r (M.simulationRule_mem hrSim) input_eq
            cases rest with
            | nil =>
                have hword : old.push = [first] := by
                  have := congrArg List.reverse hpush
                  simpa using this
                simpa [r, hphase.1, hphase.2, hword] using
                  Relation.ReflTransGen.single firstStep
            | cons next rest =>
                have hall : ∀ nextRule,
                    nextRule ∈ Internal.expansionChain old [first] (next :: rest) →
                    nextRule ∈ Internal.normalizedSimulationRules M := by
                  intro nextRule hnext
                  unfold Internal.normalizedSimulationRules
                  apply List.mem_flatMap.mpr
                  refine ⟨old, hold, ?_⟩
                  rw [if_pos hphase, hpush]
                  exact List.mem_append_right _ hnext
                have hchain := expansionChain_reaches M old first [] next rest input tail hall
                have hword : old.push = (next :: rest).reverse ++ [first] := by
                  have := congrArg List.reverse hpush
                  simpa [List.append_assoc] using this
                simpa [r, hphase.1, hphase.2, hword, List.map_append,
                  List.append_assoc] using
                  (Relation.ReflTransGen.single firstStep).trans hchain
      · let r : PushdownRule α
            (NormalState α State Stack × TurnPhase) (NPDA.FinalStack Stack) :=
          { source := (.sim old.source.1, old.source.2), input := old.input,
            pop := .old old.pop, target := (.sim old.target.1, old.target.2),
            push := old.push.map NPDA.FinalStack.old }
        have hrSim : r ∈ Internal.normalizedSimulationRules M := by
          unfold Internal.normalizedSimulationRules
          apply List.mem_flatMap.mpr
          refine ⟨old, hold, ?_⟩
          rw [if_neg hphase]
          simp [r]
        simpa [r, List.map_append, List.append_assoc] using
          Relation.ReflTransGen.single
            (NPDA.Step.epsilon r (M.simulationRule_mem hrSim) input_eq)
```

Extending `Step.normalize` by induction over the original machine's `Reaches` gives `Reaches.normalize`: any complete original computation embeds as a normalized computation confined to the `.sim` states. Combined with `initialization_reaches` (to enter `.sim`) and `accepted_reaches_done` (to leave it, below), this is the last piece needed to lift a full accepting run of the original machine into one for `normalize`.

```lean
/-- Lift an original run into the normalized simulation states. -/
theorem Reaches.normalize {M : OneTurnNPDA α State Stack}
    {c c' : ID α State Stack} (h : M.Reaches c c') :
    M.normalize.Reaches
      (c.1, (.sim c.2.1.1, c.2.1.2),
        c.2.2.map NPDA.FinalStack.old ++ [.bottom])
      (c'.1, (.sim c'.2.1.1, c'.2.1.2),
        c'.2.2.map NPDA.FinalStack.old ++ [.bottom]) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail h step ih => exact ih.trans (OneTurnNPDA.Step.normalize step)
```

### 一意な受理構成と保存定理

受理状態に着いた後は `drain` が残りの `old` 記号と `bottom` を順に除く。したがって
正規化後の受理は、boot/push の初期構成から done/pop の空スタック構成への到達と
同値である。この一意な形を `normalize_accepts_iff_reaches_done` が公開し、最後に元の
受理実行との双方向変換を合成して言語保存を得る。

`normalizedDrain_reaches_done` は `NPDA.drain_reaches_done` の正規化版で、`.drain` に入った後に支持集合内の記号を1つずつ帰納的に取り除き、最後に底記号を消して `.done` に到達する具体的な実行を構成する。

```lean
private theorem normalizedDrain_reaches_done (M : OneTurnNPDA α State Stack)
    (input : List α) (stack : List Stack) (hs : M.toNPDA.StackSupported stack) :
    M.normalize.Reaches
      (input, (.drain, .pop),
        stack.map NPDA.FinalStack.old ++ [.bottom])
      (input, (.done, .pop), []) := by
  induction stack with
  | nil =>
      let r : PushdownRule α
          (NormalState α State Stack × TurnPhase) (NPDA.FinalStack Stack) :=
        { source := (.drain, .pop), input := none, pop := .bottom,
          target := (.done, .pop), push := [] }
      have hrDrain : r ∈ Internal.normalizedDrainRules M := by
        unfold Internal.normalizedDrainRules
        exact List.mem_append_right _ (by simp [r])
      simpa [r] using Relation.ReflTransGen.single
        (NPDA.Step.epsilon r (M.normalizedDrainRule_mem hrDrain) rfl)
  | cons x stack ih =>
      have hx : x ∈ M.toNPDA.stackSupport := hs x (by simp)
      have htail : M.toNPDA.StackSupported stack := by
        intro y hy
        exact hs y (by simp [hy])
      let r : PushdownRule α
          (NormalState α State Stack × TurnPhase) (NPDA.FinalStack Stack) :=
        { source := (.drain, .pop), input := none, pop := .old x,
          target := (.drain, .pop), push := [] }
      have hrDrain : r ∈ Internal.normalizedDrainRules M := by
        unfold Internal.normalizedDrainRules
        apply List.mem_append_left
        exact List.mem_map.mpr ⟨x, hx, by simp [r]⟩
      have first : M.normalize.Step
          (input, (.drain, .pop),
            NPDA.FinalStack.old x ::
              stack.map NPDA.FinalStack.old ++ [.bottom])
          (input, (.drain, .pop),
            stack.map NPDA.FinalStack.old ++ [.bottom]) := by
        simpa [r] using NPDA.Step.epsilon r (M.normalizedDrainRule_mem hrDrain) rfl
      exact (ih htail).head first
```

`accepted_reaches_done` builds on `normalizedDrain_reaches_done` to handle the transition *into* `.drain`/`.done` from a `.sim` accept state: whether the current stack is empty or not, and whether the phase is push or pop, determine exactly one `enterDrainRules` step to take before (if anything remains) handing off to the drain induction.

```lean
private theorem accepted_reaches_done (M : OneTurnNPDA α State Stack)
    (q : State) (hq : q ∈ M.accept) (phase : TurnPhase)
    (input : List α) (stack : List Stack) (hs : M.toNPDA.StackSupported stack) :
    M.normalize.Reaches
      (input, (.sim q, phase),
        stack.map NPDA.FinalStack.old ++ [.bottom])
      (input, (.done, .pop), []) := by
  cases stack with
  | nil =>
      let r : PushdownRule α
          (NormalState α State Stack × TurnPhase) (NPDA.FinalStack Stack) :=
        { source := (.sim q, phase), input := none, pop := .bottom,
          target := (if phase = .push then (.drain, .pop) else (.done, .pop)),
          push := if phase = .push then [.bottom] else [] }
      have hrEnter : r ∈ Internal.enterDrainRules M := by
        unfold Internal.enterDrainRules
        apply List.mem_flatMap.mpr
        refine ⟨q, hq, ?_⟩
        apply List.mem_flatMap.mpr
        refine ⟨phase, by cases phase <;> simp, ?_⟩
        exact List.mem_append_right _ (by simp [r])
      have first : M.normalize.Step
          (input, (.sim q, phase), [NPDA.FinalStack.bottom])
          (input, r.target, r.push) := by
        change M.normalize.toNPDA.Step
          (input, (.sim q, phase), [NPDA.FinalStack.bottom])
          (input, r.target, r.push)
        simpa only [List.append_nil] using
          NPDA.Step.epsilon (M := M.normalize.toNPDA) r
            (by change r ∈ M.normalize.rules; exact M.enterRule_mem hrEnter) rfl
            (input := input) (stack := [])
      cases phase with
      | push =>
          exact (M.normalizedDrain_reaches_done input []
            (by intro x hx; simp at hx)).head
            (by simpa [r] using first)
      | pop => simpa [r] using Relation.ReflTransGen.single first
  | cons x stack =>
      have hx : x ∈ M.toNPDA.stackSupport := hs x (by simp)
      have htail : M.toNPDA.StackSupported stack := by
        intro y hy
        exact hs y (by simp [hy])
      let r : PushdownRule α
          (NormalState α State Stack × TurnPhase) (NPDA.FinalStack Stack) :=
        { source := (.sim q, phase), input := none, pop := .old x,
          target := (.drain, .pop),
          push := if phase = .push then [.old x] else [] }
      have hrEnter : r ∈ Internal.enterDrainRules M := by
        unfold Internal.enterDrainRules
        apply List.mem_flatMap.mpr
        refine ⟨q, hq, ?_⟩
        apply List.mem_flatMap.mpr
        refine ⟨phase, by cases phase <;> simp, ?_⟩
        apply List.mem_append_left
        exact List.mem_map.mpr ⟨x, hx, by simp [r]⟩
      cases phase with
      | push =>
          have first : M.normalize.Step
              (input, (.sim q, .push),
                NPDA.FinalStack.old x ::
                  stack.map NPDA.FinalStack.old ++ [.bottom])
              (input, (.drain, .pop),
                NPDA.FinalStack.old x ::
                  stack.map NPDA.FinalStack.old ++ [.bottom]) := by
            simpa [r] using NPDA.Step.epsilon r (M.enterRule_mem hrEnter) rfl
          exact (M.normalizedDrain_reaches_done input (x :: stack) hs).head first
      | pop =>
          have first : M.normalize.Step
              (input, (.sim q, .pop),
                NPDA.FinalStack.old x ::
                  stack.map NPDA.FinalStack.old ++ [.bottom])
              (input, (.drain, .pop),
                stack.map NPDA.FinalStack.old ++ [.bottom]) := by
            simpa [r] using NPDA.Step.epsilon r (M.enterRule_mem hrEnter) rfl
          exact (M.normalizedDrain_reaches_done input stack htail).head first
```

`normalize_accepts_iff_reaches_done` collapses the general definition of `Accepts` (an existential over start/accept states and residual stack) down to reachability between two fixed, unique configurations, exploiting that `normalize` has exactly one start state `.boot` and one accept state `.done` with an empty final stack. This canonical form is what `normalize_language`'s bidirectional proof is actually built around.

```lean
/-- Acceptance by the normalized machine is exactly reachability from its
unique boot configuration to its unique drained final configuration. -/


@[grind .] public theorem normalize_accepts_iff_reaches_done
    (M : OneTurnNPDA α State Stack) (word : List α) :
    M.normalize.Accepts word ↔
      M.normalize.Reaches
        (word, (.boot, .push), [.bottom])
        ([], (.done, .pop), []) := by
  constructor
  · rintro ⟨start, hstart, finalState, hfinal, stack, hreach⟩
    change start ∈ [((.boot, .push) :
      NormalState α State Stack × TurnPhase)] at hstart
    change finalState ∈ [((.done, .push) :
      NormalState α State Stack × TurnPhase), (.done, .pop)] at hfinal
    simp only [List.mem_singleton] at hstart
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hfinal
    subst start
    rcases hfinal with rfl | rfl
    · change M.normalize.Reaches
        (word, (.boot, .push), [.bottom])
        ([], (.done, .push), stack) at hreach
      have hgood := M.normalizeReaches_run_good word hreach
        (by simp [NormalRunGood])
      simp [NormalRunGood] at hgood
    · change M.normalize.Reaches
        (word, (.boot, .push), [.bottom])
        ([], (.done, .pop), stack) at hreach
      have hgood := M.normalizeReaches_run_good word hreach
        (by simp [NormalRunGood])
      have hstack : stack = [] := hgood.1
      subst stack
      exact hreach
  · intro hreach
    refine ⟨(.boot, .push), by simp [normalize, toNPDA],
      (.done, .pop), by simp [normalize, toNPDA], [], hreach⟩
```

`normalize_language` is the final payoff theorem for this whole module: normalizing a one-turn NPDA (splitting long pushes, unifying start/accept states) preserves its language exactly. The forward direction reads an `AcceptingPrefix` witness off `NormalRunGood` at `.done`; the reverse direction assembles `initialization_reaches`, `Reaches.normalize`, and `accepted_reaches_done` into one concrete accepting run of `normalize`, branching on whether the original accepting run ended in the push or pop phase.

```lean
/-- Normalization preserves the language of a one-turn NPDA. -/
@[grind =, simp] public theorem normalize_language (M : OneTurnNPDA α State Stack) :
    M.normalize.language = M.language := by
  ext word
  constructor
  · rintro ⟨start, hstart, finalState, hfinal, stack, hreach⟩
    change start ∈ [((.boot, .push) :
      NormalState α State Stack × TurnPhase)] at hstart
    change finalState ∈ [((.done, .push) :
      NormalState α State Stack × TurnPhase), (.done, .pop)] at hfinal
    simp only [List.mem_singleton] at hstart
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hfinal
    subst start
    rcases hfinal with rfl | rfl
    · change M.normalize.toNPDA.Reaches
        (word, (.boot, .push), [NPDA.FinalStack.bottom])
        ([], (.done, .push), stack) at hreach
      have hgood := M.normalizeReaches_run_good word hreach
          (by simp [NormalRunGood])
      simp [NormalRunGood] at hgood
    · change M.normalize.toNPDA.Reaches
        (word, (.boot, .push), [NPDA.FinalStack.bottom])
        ([], (.done, .pop), stack) at hreach
      have hgood := M.normalizeReaches_run_good word hreach
          (by simp [NormalRunGood])
      rcases hgood.2 with ⟨q₀, hq₀, qf, hqf, phase, oldStack, horiginal⟩
      refine ⟨(q₀, .push), ?_, (qf, phase), ?_, oldStack, horiginal⟩
      · simp [toNPDA, hq₀]
      · change (qf, phase) ∈ M.accept.flatMap fun q => [(q, .push), (q, .pop)]
        apply List.mem_flatMap.mpr
        exact ⟨qf, hqf, by cases phase <;> simp⟩
  · rintro ⟨q₀, hq₀, qf, hqf, stack, hreach⟩
    simp only [toNPDA, List.mem_map] at hq₀
    rcases hq₀ with ⟨q₀, hq₀, rfl⟩
    simp only [toNPDA, List.mem_flatMap] at hqf
    rcases hqf with ⟨qf, hqf, hphase⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hphase
    rcases hphase with rfl | rfl
    · refine ⟨(.boot, .push), by simp [normalize, toNPDA],
        (.done, .pop), by simp [normalize, toNPDA], [], ?_⟩
      have hinit := M.initialization_reaches q₀ hq₀ word
      have hsim := OneTurnNPDA.Reaches.normalize hreach
      have hs := hreach.stack_supported M.toNPDA.initialStack_supported
      exact (hinit.trans hsim).trans (M.accepted_reaches_done qf hqf .push [] stack hs)
    · refine ⟨(.boot, .push), by simp [normalize, toNPDA],
        (.done, .pop), by simp [normalize, toNPDA], [], ?_⟩
      have hinit := M.initialization_reaches q₀ hq₀ word
      have hsim := OneTurnNPDA.Reaches.normalize hreach
      have hs := hreach.stack_supported M.toNPDA.initialStack_supported
      exact (hinit.trans hsim).trans (M.accepted_reaches_done qf hqf .pop [] stack hs)

end OneTurnNPDA

end Mathling.Automata
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
