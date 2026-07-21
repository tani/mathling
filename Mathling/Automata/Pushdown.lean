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

/-- A nondeterministic pushdown automaton presented by a finite rule list. -/
@[ext] public structure NPDA (α State Stack : Type*) where
  rules : List (PushdownRule α State Stack)
  start : List State
  accept : List State
  initialStack : List Stack

namespace NPDA

variable {α State Stack : Type*}

/-- An instantaneous description: unread input, control state, and stack. -/
public abbrev ID (α State Stack : Type*) := List α × State × List Stack

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

/-- Zero or more local transitions. -/
public abbrev Reaches (M : NPDA α State Stack) := Relation.ReflTransGen M.Step

/-- Acceptance by a local NPDA.

Its body is exposed because public grammar conversions destruct acceptance
witnesses and reconstruct them as reachability witnesses. -/
@[expose] public def Accepts (M : NPDA α State Stack) (w : List α) : Prop :=
  ∃ q₀ ∈ M.start, ∃ qf ∈ M.accept, ∃ stack,
    M.Reaches (w, q₀, M.initialStack) ([], qf, stack)

/-- The language accepted by a local NPDA.

Its body is exposed because public language-equivalence theorems rewrite
membership into the corresponding acceptance predicate. -/
@[expose] public def language (M : NPDA α State Stack) : Language α := {w | M.Accepts w}

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

/-- Fresh bottom marker plus embedded symbols of the original stack alphabet. -/
@[grind cases] public inductive FinalStack (Stack : Type*) where
  | bottom
  | old (symbol : Stack)
  deriving Repr, DecidableEq

/-- Every stack symbol that can occur in a run from the declared initial
stack. -/
def stackSupport (M : NPDA α State Stack) : List Stack :=
  M.initialStack ++ M.rules.flatMap fun r => r.pop :: r.push

namespace Internal

public def bootRules (M : NPDA α State Stack) :
    List (PushdownRule α (FinalState State) (FinalStack Stack)) :=
  M.start.map fun q =>
    { source := .boot, input := none, pop := .bottom, target := .sim q
      push := M.initialStack.map FinalStack.old ++ [.bottom] }

public def simulationRules (M : NPDA α State Stack) :
    List (PushdownRule α (FinalState State) (FinalStack Stack)) :=
  M.rules.map fun r =>
    { source := .sim r.source, input := r.input, pop := .old r.pop
      target := .sim r.target, push := r.push.map FinalStack.old }

public def enterDrainRules (M : NPDA α State Stack) :
    List (PushdownRule α (FinalState State) (FinalStack Stack)) :=
  M.accept.flatMap fun q => M.stackSupport.map fun x =>
    { source := .sim q, input := none, pop := .old x
      target := .drain, push := [] }

public def acceptBottomRules (M : NPDA α State Stack) :
    List (PushdownRule α (FinalState State) (FinalStack Stack)) :=
  M.accept.map fun q =>
    { source := .sim q, input := none, pop := .bottom
      target := .done, push := [] }

public def drainRules (M : NPDA α State Stack) :
    List (PushdownRule α (FinalState State) (FinalStack Stack)) :=
  M.stackSupport.map fun x =>
    { source := .drain, input := none, pop := .old x
      target := .drain, push := [] }

public def finishDrainRule :
    PushdownRule α (FinalState State) (FinalStack Stack) :=
  { source := .drain, input := none, pop := .bottom
    target := .done, push := [] }

end Internal

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

/-- Every symbol in a stack belongs to the machine's finite stack support. -/
def StackSupported (M : NPDA α State Stack) (stack : List Stack) : Prop :=
  ∀ x ∈ stack, x ∈ M.stackSupport

@[grind .] theorem initialStack_supported (M : NPDA α State Stack) :
    M.StackSupported M.initialStack := by
  intro x hx
  exact List.mem_append_left _ hx

@[grind .] theorem rule_pop_mem_stackSupport (M : NPDA α State Stack)
    {r : PushdownRule α State Stack} (hr : r ∈ M.rules) :
    r.pop ∈ M.stackSupport := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  exact ⟨r, hr, by simp⟩

@[grind .] theorem rule_push_supported (M : NPDA α State Stack)
    {r : PushdownRule α State Stack} (hr : r ∈ M.rules) :
    M.StackSupported r.push := by
  intro x hx
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  exact ⟨r, hr, by simp [hx]⟩

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

@[grind .] theorem Reaches.stack_supported {M : NPDA α State Stack}
    {c c' : ID α State Stack} (h : M.Reaches c c') :
    M.StackSupported c.2.2 → M.StackSupported c'.2.2 := by
  induction h with
  | refl => exact id
  | tail h step ih => exact fun hs => step.stack_supported (ih hs)

@[grind .] theorem bootRule_mem (M : NPDA α State Stack)
    {q : State} (hq : q ∈ M.start) :
    ({ source := .boot, input := none, pop := .bottom, target := .sim q
       push := M.initialStack.map FinalStack.old ++ [.bottom] } :
      PushdownRule α (FinalState State) (FinalStack Stack)) ∈
      M.finalToEmpty.rules := by
  simp [finalToEmpty, Internal.bootRules, hq]

@[grind .] theorem simulationRule_mem (M : NPDA α State Stack)
    {r : PushdownRule α State Stack} (hr : r ∈ M.rules) :
    ({ source := .sim r.source, input := r.input, pop := .old r.pop
       target := .sim r.target, push := r.push.map FinalStack.old } :
      PushdownRule α (FinalState State) (FinalStack Stack)) ∈
      M.finalToEmpty.rules := by
  simp only [finalToEmpty, List.mem_append, List.mem_singleton]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
    (List.mem_map.mpr ⟨r, hr, rfl⟩)))))

@[grind .] theorem enterDrainRule_mem (M : NPDA α State Stack)
    {q : State} (hq : q ∈ M.accept) {x : Stack}
    (hx : x ∈ M.stackSupport) :
    ({ source := .sim q, input := none, pop := .old x
       target := .drain, push := [] } :
      PushdownRule α (FinalState State) (FinalStack Stack)) ∈
      M.finalToEmpty.rules := by
  simp [finalToEmpty, Internal.enterDrainRules, hq, hx]

@[grind .] theorem acceptBottomRule_mem (M : NPDA α State Stack)
    {q : State} (hq : q ∈ M.accept) :
    ({ source := .sim q, input := none, pop := .bottom
       target := .done, push := [] } :
      PushdownRule α (FinalState State) (FinalStack Stack)) ∈
      M.finalToEmpty.rules := by
  simp [finalToEmpty, Internal.acceptBottomRules, hq]

@[grind .] theorem drainRule_mem (M : NPDA α State Stack)
    {x : Stack} (hx : x ∈ M.stackSupport) :
    ({ source := .drain, input := none, pop := .old x
       target := .drain, push := [] } :
      PushdownRule α (FinalState State) (FinalStack Stack)) ∈
      M.finalToEmpty.rules := by
  simp [finalToEmpty, Internal.drainRules, hx]

@[grind .] theorem finishDrainRule_mem (M : NPDA α State Stack) :
    (Internal.finishDrainRule :
      PushdownRule α (FinalState State) (FinalStack Stack)) ∈
      M.finalToEmpty.rules := by
  simp [finalToEmpty]

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

/-- Original-machine acceptance evidence with a possibly unread suffix. -/
def AcceptingPrefix (M : NPDA α State Stack) (word input : List α) : Prop :=
  ∃ q₀ ∈ M.start, ∃ qf ∈ M.accept, ∃ stack,
    M.Reaches (word, q₀, M.initialStack) (input, qf, stack)

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

/-- The semantic invariant propagates over a complete normalized run. -/
@[grind .] theorem finalReaches_run_good (M : NPDA α State Stack)
    (word : List α) {c c' : ID α (FinalState State) (FinalStack Stack)}
    (h : M.finalToEmpty.Reaches c c') :
    M.FinalRunGood word c → M.FinalRunGood word c' := by
  induction h with
  | refl => exact id
  | tail h step ih => exact fun hc => M.finalStep_run_good word step (ih hc)

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

## 全スタック関係への境界

`WholeStackNPDA` は、任意のスタック全体を関係で書き換えられる別の意味論モデルである。有限局所規則の `NPDA` とは意図的に区別し、`NPDA.toWholeStackNPDA` だけを変換境界とする。`step_toWholeStackNPDA_iff` と `reaches_toWholeStackNPDA_iff` が1歩と実行列の両方を対応させるため、局所規則の公開 API を保ったまま、既存の高階な PDA 構成で全スタック意味論を利用できる。

```lean

/-- A nondeterministic pushdown automaton whose transition relation may inspect
and replace the whole stack at once. -/
@[ext] public structure WholeStackNPDA (α State Stack : Type*) where
  step : State → Option α → List Stack → Set (State × List Stack)
  start : Set State
  accept : Set State
  initialStack : List Stack

namespace WholeStackNPDA

variable {α State Stack : Type*}

/-- An instantaneous description: unread input, control state, and stack. -/
public abbrev ID (α State Stack : Type*) := List α × State × List Stack

/-- One consuming or epsilon transition of an NPDA. -/
@[grind cases] public inductive Step (M : WholeStackNPDA α State Stack) :
    ID α State Stack → ID α State Stack → Prop
  | consume {a input q stack q' stack'}
      (h : (q', stack') ∈ M.step q (some a) stack) :
      Step M (a :: input, q, stack) (input, q', stack')
  | epsilon {input q stack q' stack'}
      (h : (q', stack') ∈ M.step q none stack) :
      Step M (input, q, stack) (input, q', stack')

/-- Zero or more transitions of an NPDA. -/
public abbrev Reaches (M : WholeStackNPDA α State Stack) := Relation.ReflTransGen M.Step

/-- Acceptance by final state after consuming all input. -/
/- Exposed because exported conversion proofs destructure the shared acceptance predicate. -/
@[expose] public def Accepts (M : WholeStackNPDA α State Stack) (w : List α) : Prop :=
  ∃ q₀ ∈ M.start, ∃ qf ∈ M.accept, ∃ stack,
    M.Reaches (w, q₀, M.initialStack) ([], qf, stack)

/-- The language accepted by an NPDA. -/
/- Exposed so exported conversion specifications can reduce the shared language observation. -/
@[expose] public def language (M : WholeStackNPDA α State Stack) : Language α := {w | M.Accepts w}

end WholeStackNPDA

namespace NPDA

variable {α State Stack : Type*}

/-- Interpret local rules as a whole-stack transition relation. -/
public def toWholeStackNPDA (M : NPDA α State Stack) : WholeStackNPDA α State Stack where
  step q sym stack := {next | ∃ r ∈ M.rules, r.source = q ∧ r.input = sym ∧
    ∃ tail, stack = r.pop :: tail ∧ next = (r.target, r.push ++ tail)}
  start := {q | q ∈ M.start}
  accept := {q | q ∈ M.accept}
  initialStack := M.initialStack

@[grind .] theorem step_toWholeStackNPDA_iff (M : NPDA α State Stack)
    {c c' : ID α State Stack} :
    M.Step c c' ↔ M.toWholeStackNPDA.Step c c' := by
  constructor
  · intro h
    cases h with
    | @consume a input tail r hr input_eq =>
        apply WholeStackNPDA.Step.consume
        exact ⟨r, hr, rfl, input_eq, tail, rfl, rfl⟩
    | @epsilon input tail r hr input_eq =>
        apply WholeStackNPDA.Step.epsilon
        exact ⟨r, hr, rfl, input_eq, tail, rfl, rfl⟩
  · intro h
    cases h with
    | @consume a input q stack q' stack' hmem =>
        rcases hmem with ⟨r, hr, hsource, hinput, tail, hstack, hnext⟩
        subst q
        subst stack
        obtain ⟨rfl, rfl⟩ := hnext
        exact Step.consume r hr hinput
    | @epsilon input q stack q' stack' hmem =>
        rcases hmem with ⟨r, hr, hsource, hinput, tail, hstack, hnext⟩
        subst q
        subst stack
        obtain ⟨rfl, rfl⟩ := hnext
        exact Step.epsilon r hr hinput

@[grind .] theorem reaches_toWholeStackNPDA_iff (M : NPDA α State Stack)
    {c c' : ID α State Stack} :
    M.Reaches c c' ↔ M.toWholeStackNPDA.Reaches c c' := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail h step ih => exact ih.tail ((M.step_toWholeStackNPDA_iff).mp step)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail h step ih => exact ih.tail ((M.step_toWholeStackNPDA_iff).mpr step)

/-- The whole-stack interpretation is exactly the operational semantics of
the finite local rule list. -/
@[grind =, simp] public theorem toWholeStackNPDA_language (M : NPDA α State Stack) :
    M.toWholeStackNPDA.language = M.language := by
  ext word
  constructor
  · rintro ⟨q₀, hq₀, qf, hqf, stack, hreach⟩
    exact ⟨q₀, hq₀, qf, hqf, stack,
      (M.reaches_toWholeStackNPDA_iff).mpr hreach⟩
  · rintro ⟨q₀, hq₀, qf, hqf, stack, hreach⟩
    exact ⟨q₀, hq₀, qf, hqf, stack,
      (M.reaches_toWholeStackNPDA_iff).mp hreach⟩

end NPDA

```

## 全スタック PDA と DPDA の意味論

`WholeStackNPDA` はスタック全体を書き換える遷移関数 `step : State → Option α → List Stack → Set (State × List Stack)` を持つ。`ID`（instantaneous description）は未読入力・制御状態・スタックの組であり、`Step` はこの上の一手の遷移関係を `consume`（入力を1文字消費する遷移）と `epsilon`（入力を消費しない遷移）の2コンストラクタで帰納的に定義する。`Reaches` はこの一手関係の反射推移閉包であり、受理は

```math
M.\mathrm{Accepts}(w) \iff \exists\, q_0 \in M.\mathrm{start},\ \exists\, q_f \in M.\mathrm{accept},\ \exists\, s,\ M.\mathrm{Reaches}\,(w, q_0, M.\mathrm{initialStack})\,([\,], q_f, s)
```

として定義される。初期状態・初期スタックから出発して入力 `w` を読み尽くし、受理状態へ到達する経路が存在すれば受理される（到達時のスタックの中身そのものは問わない）。`language` はこの `Accepts` 述語をそのまま言語として束ねたものである。

以下では、決定性版 `DPDA` を定義し、`WholeStackNPDA` への埋め込みとして意味論を与える。

```lean
/-- A deterministic pushdown automaton with a single start state. -/
public structure DPDA (α State Stack : Type*) where
  step : State → Option α → List Stack → Option (State × List Stack)
  start : State
  accept : Set State
  initialStack : List Stack

namespace DPDA

variable {α State Stack : Type*}

/-- Regard a deterministic PDA as a nondeterministic PDA with singleton transitions. -/
/- Exposed because the exported language-preservation theorem below is definitionally proved by
unfolding this representation-changing conversion. -/
@[expose] public def toWholeStackNPDA (M : DPDA α State Stack) : WholeStackNPDA α State Stack where
  step q sym stack := {next | M.step q sym stack = some next}
  start := {M.start}
  accept := M.accept
  initialStack := M.initialStack

/-- The language of a DPDA is the language of its underlying NPDA. -/
/- Exposed because `DPDA.toWholeStackNPDA_language` is an exported definitional specification. -/
@[expose] public def language (M : DPDA α State Stack) : Language α := M.toWholeStackNPDA.language

/-- Forgetting determinism preserves a DPDA's language. -/
@[grind =, simp] public theorem toWholeStackNPDA_language (M : DPDA α State Stack) :
    M.toWholeStackNPDA.language = M.language := rfl

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

この制限クラスは、線形文法（linear grammar）から構成される PDA が自然にこの形を取ることから、他モジュールでの変換の中間表現として用いられる。`toWholeStackNPDA` は局面を制御状態 `State × TurnPhase` へ埋め込むことで一手番の不変条件そのものを忘れ、`WholeStackNPDA` として意味論を与える。`toWholeStackNPDA_language` はこの忘却が受理言語を変えないことを保証する。

```lean
/-- The phase of a one-turn pushdown computation. -/
@[grind cases] public inductive TurnPhase where
  | push
  | pop
  deriving Repr, DecidableEq

/-- A nondeterministic PDA whose stack height first grows and then shrinks. -/
public structure OneTurnNPDA (α State Stack : Type*) where
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
public abbrev NondeterministicOneTurnPDA := OneTurnNPDA

namespace OneTurnNPDA

variable {α State Stack : Type*}

/-- Forget the one-turn invariants while retaining the phase in the control state. -/
/- Exposed because the exported language-preservation theorem below is definitionally proved by
unfolding this representation-changing conversion. -/
@[expose] public def toWholeStackNPDA (M : OneTurnNPDA α State Stack) :
    WholeStackNPDA α (State × TurnPhase) Stack where
  step qp sym stack :=
    {next | (next.1.1, next.1.2, next.2) ∈ M.step qp.1 qp.2 sym stack}
  start := {qp | qp.1 ∈ M.start ∧ qp.2 = TurnPhase.push}
  accept := {qp | qp.1 ∈ M.accept}
  initialStack := M.initialStack

/-- The language of a one-turn PDA is the language of its underlying NPDA. -/
/- Exposed because `OneTurnNPDA.toWholeStackNPDA_language` is an exported definitional
specification. -/
@[expose] public def language (M : OneTurnNPDA α State Stack) : Language α :=
  M.toWholeStackNPDA.language

/-- Forgetting the one-turn invariants preserves the accepted language. -/
@[grind =, simp] public theorem toWholeStackNPDA_language (M : OneTurnNPDA α State Stack) :
    M.toWholeStackNPDA.language = M.language := rfl

end OneTurnNPDA

end Mathling.Automata

```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
