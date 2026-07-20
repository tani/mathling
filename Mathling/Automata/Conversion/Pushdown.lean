    module

    public import Mathling.Automata.Core

    public import LiterateLean
    open scoped LiterateLean

    @[expose] public section

# Mathling / Automata / Conversion / Pushdown モジュール

局所遷移で記述した非決定性プッシュダウン・オートマトンと一回転 NPDA の実行意味論を定める。構成、反射推移閉包による実行、受理条件、言語という順に公開し、文法変換側が参照する機械モデルの境界を固定する。

```lean
@[expose] public section

/-!
# Pushdown automata

Nondeterministic, deterministic, and one-turn pushdown automata.
-/

namespace Mathling.Automata

/-- A nondeterministic pushdown automaton with whole-stack transitions. -/
@[ext] structure NPDA (α State Stack : Type*) where
  step : State → Option α → List Stack → Set (State × List Stack)
  start : Set State
  accept : Set State
  initialStack : List Stack

namespace NPDA

variable {α State Stack : Type*}

/-- An instantaneous description: unread input, control state, and stack. -/
abbrev ID (α State Stack : Type*) := List α × State × List Stack

/-- One consuming or epsilon transition of an NPDA. -/
inductive Step (M : NPDA α State Stack) : ID α State Stack → ID α State Stack → Prop
  | consume {a input q stack q' stack'}
      (h : (q', stack') ∈ M.step q (some a) stack) :
      Step M (a :: input, q, stack) (input, q', stack')
  | epsilon {input q stack q' stack'}
      (h : (q', stack') ∈ M.step q none stack) :
      Step M (input, q, stack) (input, q', stack')

/-- Zero or more transitions of an NPDA. -/
abbrev Reaches (M : NPDA α State Stack) := Relation.ReflTransGen M.Step

/-- Acceptance by final state after consuming all input. -/
def Accepts (M : NPDA α State Stack) (w : List α) : Prop :=
  ∃ q₀ ∈ M.start, ∃ qf ∈ M.accept, ∃ stack,
    M.Reaches (w, q₀, M.initialStack) ([], qf, stack)

/-- The language accepted by an NPDA. -/
def language (M : NPDA α State Stack) : Language α := {w | M.Accepts w}

end NPDA

```

## NPDA の意味論

`NPDA` はスタック全体を書き換える遷移関数 `step : State → Option α → List Stack → Set (State × List Stack)` を持つ非決定性プッシュダウンオートマトンである。`ID`（instantaneous description）は未読入力・制御状態・スタックの組であり、`Step` はこの上の一手の遷移関係を `consume`（入力を1文字消費する遷移）と `epsilon`（入力を消費しない遷移）の2コンストラクタで帰納的に定義する。`Reaches` はこの一手関係の反射推移閉包であり、受理は

```math
M.\mathrm{Accepts}(w) \iff \exists\, q_0 \in M.\mathrm{start},\ \exists\, q_f \in M.\mathrm{accept},\ \exists\, s,\ M.\mathrm{Reaches}\,(w, q_0, M.\mathrm{initialStack})\,([\,], q_f, s)
```

として定義される。初期状態・初期スタックから出発して入力 `w` を読み尽くし、受理状態へ到達する経路が存在すれば受理される（到達時のスタックの中身そのものは問わない）。`language` はこの `Accepts` 述語をそのまま言語として束ねたものである。

以下では、この `NPDA` を土台として決定性版 `DPDA` を定義し、`NPDA` への埋め込みとして意味論を与える。

```lean
/-- A deterministic pushdown automaton with a single start state. -/
structure DPDA (α State Stack : Type*) where
  step : State → Option α → List Stack → Option (State × List Stack)
  start : State
  accept : Set State
  initialStack : List Stack

namespace DPDA

variable {α State Stack : Type*}

/-- Regard a deterministic PDA as a nondeterministic PDA with singleton transitions. -/
def toNPDA (M : DPDA α State Stack) : NPDA α State Stack where
  step q sym stack := {next | M.step q sym stack = some next}
  start := {M.start}
  accept := M.accept
  initialStack := M.initialStack

/-- The language of a DPDA is the language of its underlying NPDA. -/
def language (M : DPDA α State Stack) : Language α := M.toNPDA.language

/-- Forgetting determinism preserves a DPDA's language. -/
@[simp] theorem toNPDA_language (M : DPDA α State Stack) :
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
- `push_phase_nonshrinking`: `push` 局面ではスタックの高さが単調非減少。
- `pop_phase_nongrowing`: `pop` 局面ではスタックの高さが単調非増加。

この制限クラスは、線形文法（linear grammar）から構成される PDA が自然にこの形を取ることから、他モジュールでの変換の中間表現として用いられる。`toNPDA` は局面を制御状態 `State × TurnPhase` へ埋め込むことで一手番の不変条件そのものを忘れ、通常の `NPDA` として意味論を与える。`toNPDA_language` はこの忘却が受理言語を変えないことを保証する。

```lean
/-- The phase of a one-turn pushdown computation. -/
inductive TurnPhase where
  | push
  | pop
  deriving Repr, DecidableEq

/-- A nondeterministic PDA whose stack height first grows and then shrinks. -/
structure OneTurnNPDA (α State Stack : Type*) where
  step : State → TurnPhase → Option α → List Stack →
    Set (State × TurnPhase × List Stack)
  start : Set State
  accept : Set State
  initialStack : List Stack
  pop_stays_pop : ∀ {q p sym stack q' p' stack'},
    (q', p', stack') ∈ step q p sym stack → p = TurnPhase.pop → p' = TurnPhase.pop
  push_phase_nonshrinking : ∀ {q sym stack q' stack'},
    (q', TurnPhase.push, stack') ∈ step q TurnPhase.push sym stack →
      stack.length ≤ stack'.length
  pop_phase_nongrowing : ∀ {q p sym stack q' stack'},
    (q', TurnPhase.pop, stack') ∈ step q p sym stack →
      stack'.length ≤ stack.length

/-- Alternate descriptive name for a nondeterministic one-turn PDA. -/
abbrev NondeterministicOneTurnPDA := OneTurnNPDA

namespace OneTurnNPDA

variable {α State Stack : Type*}

/-- Forget the one-turn invariants while retaining the phase in the control state. -/
def toNPDA (M : OneTurnNPDA α State Stack) : NPDA α (State × TurnPhase) Stack where
  step qp sym stack :=
    {next | (next.1.1, next.1.2, next.2) ∈ M.step qp.1 qp.2 sym stack}
  start := {qp | qp.1 ∈ M.start ∧ qp.2 = TurnPhase.push}
  accept := {qp | qp.1 ∈ M.accept}
  initialStack := M.initialStack

/-- The language of a one-turn PDA is the language of its underlying NPDA. -/
def language (M : OneTurnNPDA α State Stack) : Language α := M.toNPDA.language

/-- Forgetting the one-turn invariants preserves the accepted language. -/
@[simp] theorem toNPDA_language (M : OneTurnNPDA α State Stack) :
    M.toNPDA.language = M.language := rfl

end OneTurnNPDA

end Mathling.Automata

```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
