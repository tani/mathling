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

```lean
/-- A nondeterministic pushdown automaton presented by a finite rule list. -/
@[ext] public structure NPDA (α State Stack : Type*) where
  rules : List (PushdownRule α State Stack)
  start : List State
  accept : List State
  initialStack : List Stack
```

```lean
namespace NPDA

```

```lean
variable {α State Stack : Type*}

/-- An instantaneous description: unread input, control state, and stack. -/
public abbrev ID (α State Stack : Type*) := List α × State × List Stack
```

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

```lean
/-- Zero or more local transitions. -/
public abbrev Reaches (M : NPDA α State Stack) := Relation.ReflTransGen M.Step
```

```lean
/-- Acceptance by a local NPDA.

Its body is exposed because public grammar conversions destruct acceptance
witnesses and reconstruct them as reachability witnesses. -/


@[expose] public def Accepts (M : NPDA α State Stack) (w : List α) : Prop :=
  ∃ q₀ ∈ M.start, ∃ qf ∈ M.accept, ∃ stack,
    M.Reaches (w, q₀, M.initialStack) ([], qf, stack)
```

```lean
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
```

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

```lean
/-- Fresh bottom marker plus embedded symbols of the original stack alphabet. -/
@[grind cases] public inductive FinalStack (Stack : Type*) where
  | bottom
  | old (symbol : Stack)
  deriving Repr, DecidableEq
```

```lean
/-- Every stack symbol that can occur in a run from the declared initial
stack. -/


def stackSupport (M : NPDA α State Stack) : List Stack :=
  M.initialStack ++ M.rules.flatMap fun r => r.pop :: r.push
```

```lean
namespace Internal

public def bootRules (M : NPDA α State Stack) :
    List (PushdownRule α (FinalState State) (FinalStack Stack)) :=
  M.start.map fun q =>
    { source := .boot, input := none, pop := .bottom, target := .sim q
      push := M.initialStack.map FinalStack.old ++ [.bottom] }
```

```lean
public def simulationRules (M : NPDA α State Stack) :
    List (PushdownRule α (FinalState State) (FinalStack Stack)) :=
  M.rules.map fun r =>
    { source := .sim r.source, input := r.input, pop := .old r.pop
      target := .sim r.target, push := r.push.map FinalStack.old }
```

```lean
public def enterDrainRules (M : NPDA α State Stack) :
    List (PushdownRule α (FinalState State) (FinalStack Stack)) :=
  M.accept.flatMap fun q => M.stackSupport.map fun x =>
    { source := .sim q, input := none, pop := .old x
      target := .drain, push := [] }
```

```lean
public def acceptBottomRules (M : NPDA α State Stack) :
    List (PushdownRule α (FinalState State) (FinalStack Stack)) :=
  M.accept.map fun q =>
    { source := .sim q, input := none, pop := .bottom
      target := .done, push := [] }
```

```lean
public def drainRules (M : NPDA α State Stack) :
    List (PushdownRule α (FinalState State) (FinalStack Stack)) :=
  M.stackSupport.map fun x =>
    { source := .drain, input := none, pop := .old x
      target := .drain, push := [] }
```

```lean
public def finishDrainRule :
    PushdownRule α (FinalState State) (FinalStack Stack) :=
  { source := .drain, input := none, pop := .bottom
    target := .done, push := [] }

end Internal
```

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

```lean
/-- Every symbol in a stack belongs to the machine's finite stack support. -/
def StackSupported (M : NPDA α State Stack) (stack : List Stack) : Prop :=
  ∀ x ∈ stack, x ∈ M.stackSupport
```

```lean
@[grind .] theorem initialStack_supported (M : NPDA α State Stack) :
    M.StackSupported M.initialStack := by
  intro x hx
  exact List.mem_append_left _ hx

```

```lean
@[grind .] theorem rule_pop_mem_stackSupport (M : NPDA α State Stack)
    {r : PushdownRule α State Stack} (hr : r ∈ M.rules) :
    r.pop ∈ M.stackSupport := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  exact ⟨r, hr, by simp⟩

```

```lean
@[grind .] theorem rule_push_supported (M : NPDA α State Stack)
    {r : PushdownRule α State Stack} (hr : r ∈ M.rules) :
    M.StackSupported r.push := by
  intro x hx
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  exact ⟨r, hr, by simp [hx]⟩

```

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

```lean
@[grind .] theorem Reaches.stack_supported {M : NPDA α State Stack}
    {c c' : ID α State Stack} (h : M.Reaches c c') :
    M.StackSupported c.2.2 → M.StackSupported c'.2.2 := by
  induction h with
  | refl => exact id
  | tail h step ih => exact fun hs => step.stack_supported (ih hs)

```

```lean
@[grind .] theorem bootRule_mem (M : NPDA α State Stack)
    {q : State} (hq : q ∈ M.start) :
    ({ source := .boot, input := none, pop := .bottom, target := .sim q
       push := M.initialStack.map FinalStack.old ++ [.bottom] } :
      PushdownRule α (FinalState State) (FinalStack Stack)) ∈
      M.finalToEmpty.rules := by
  simp [finalToEmpty, Internal.bootRules, hq]

```

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

```lean
@[grind .] theorem acceptBottomRule_mem (M : NPDA α State Stack)
    {q : State} (hq : q ∈ M.accept) :
    ({ source := .sim q, input := none, pop := .bottom
       target := .done, push := [] } :
      PushdownRule α (FinalState State) (FinalStack Stack)) ∈
      M.finalToEmpty.rules := by
  simp [finalToEmpty, Internal.acceptBottomRules, hq]

```

```lean
@[grind .] theorem drainRule_mem (M : NPDA α State Stack)
    {x : Stack} (hx : x ∈ M.stackSupport) :
    ({ source := .drain, input := none, pop := .old x
       target := .drain, push := [] } :
      PushdownRule α (FinalState State) (FinalStack Stack)) ∈
      M.finalToEmpty.rules := by
  simp [finalToEmpty, Internal.drainRules, hx]

```

```lean
@[grind .] theorem finishDrainRule_mem (M : NPDA α State Stack) :
    (Internal.finishDrainRule :
      PushdownRule α (FinalState State) (FinalStack Stack)) ∈
      M.finalToEmpty.rules := by
  simp [finalToEmpty]
```

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

```lean
/-- Original-machine acceptance evidence with a possibly unread suffix. -/
def AcceptingPrefix (M : NPDA α State Stack) (word input : List α) : Prop :=
  ∃ q₀ ∈ M.start, ∃ qf ∈ M.accept, ∃ stack,
    M.Reaches (word, q₀, M.initialStack) (input, qf, stack)
```

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

```lean
namespace DPDA

```

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

```lean
/-- The language of a DPDA is the language of its underlying local NPDA. -/
@[expose] public def language (M : DPDA α State Stack) : Language α := M.toNPDA.language
```

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

```lean
/-- Alternate descriptive name for a nondeterministic one-turn PDA. -/
public abbrev NondeterministicOneTurnPDA := OneTurnNPDA
```

```lean
namespace OneTurnNPDA

```

```lean
variable {α State Stack : Type*}

/-- An instantaneous description including the one-turn phase. -/
public abbrev ID (α State Stack : Type*) :=
  List α × (State × TurnPhase) × List Stack
```

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

```lean
/-- One consuming or epsilon transition of a one-turn machine. -/
public abbrev Step (M : OneTurnNPDA α State Stack) :
    ID α State Stack → ID α State Stack → Prop := M.toNPDA.Step
```

```lean
/-- Zero or more one-turn transitions. -/
public abbrev Reaches (M : OneTurnNPDA α State Stack) := M.toNPDA.Reaches
```

```lean
/-- Acceptance starts in the push phase and ends in any phase. -/
@[expose] public def Accepts (M : OneTurnNPDA α State Stack) (w : List α) : Prop :=
  M.toNPDA.Accepts w
```

```lean
/-- The language accepted by a one-turn PDA. -/
@[expose] public def language (M : OneTurnNPDA α State Stack) : Language α :=
  M.toNPDA.language
```

```lean
/-- Forgetting the one-turn structure preserves the accepted language definitionally. -/
@[grind =, simp] public theorem toNPDA_language (M : OneTurnNPDA α State Stack) :
    M.toNPDA.language = M.language := rfl
```

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

```lean
public def normalizedDrainRules (M : OneTurnNPDA α State Stack) :
    List (PushdownRule α (NormalState α State Stack × TurnPhase) (NPDA.FinalStack Stack)) :=
  ((M.toNPDA.stackSupport).map fun x =>
    { source := (.drain, .pop), input := none, pop := .old x,
      target := (.drain, .pop), push := [] }) ++
  [{ source := (.drain, .pop), input := none, pop := .bottom,
     target := (.done, .pop), push := [] }]
```

```lean
public def normalizedRules (M : OneTurnNPDA α State Stack) :
    List (PushdownRule α (NormalState α State Stack × TurnPhase) (NPDA.FinalStack Stack)) :=
  initializationRules M ++ normalizedSimulationRules M ++ enterDrainRules M ++
    normalizedDrainRules M
```

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

```lean
@[aesop safe apply] private theorem original_pop_stays_pop
    (M : OneTurnNPDA α State Stack)
    (r : PushdownRule α (State × TurnPhase) Stack) (hr : r ∈ M.rules)
    (hp : r.source.2 = .pop) : r.target.2 = .pop :=
  M.pop_stays_pop r hr hp

```

```lean
@[aesop safe apply] private theorem original_push_nonshrinking
    (M : OneTurnNPDA α State Stack)
    (r : PushdownRule α (State × TurnPhase) Stack) (hr : r ∈ M.rules)
    (hp : r.source.2 = .push) : 1 ≤ r.push.length :=
  M.push_phase_nonshrinking r hr hp

```

```lean
@[aesop safe apply] private theorem original_pop_nongrowing
    (M : OneTurnNPDA α State Stack)
    (r : PushdownRule α (State × TurnPhase) Stack) (hr : r ∈ M.rules)
    (hp : r.target.2 = .pop) : r.push.length ≤ 1 :=
  M.pop_phase_nongrowing r hr hp
```

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

```lean
private theorem initializationRule_mem (M : OneTurnNPDA α State Stack)
    {r : PushdownRule α (NormalState α State Stack × TurnPhase)
      (NPDA.FinalStack Stack)} (hr : r ∈ Internal.initializationRules M) :
    r ∈ M.normalize.rules := by
  simp only [normalize, Internal.normalizedRules, List.mem_append]
  exact Or.inl (Or.inl (Or.inl hr))
```

```lean
private theorem simulationRule_mem (M : OneTurnNPDA α State Stack)
    {r : PushdownRule α (NormalState α State Stack × TurnPhase)
      (NPDA.FinalStack Stack)} (hr : r ∈ Internal.normalizedSimulationRules M) :
    r ∈ M.normalize.rules := by
  simp only [normalize, Internal.normalizedRules, List.mem_append]
  exact Or.inl (Or.inl (Or.inr hr))
```

```lean
private theorem enterRule_mem (M : OneTurnNPDA α State Stack)
    {r : PushdownRule α (NormalState α State Stack × TurnPhase)
      (NPDA.FinalStack Stack)} (hr : r ∈ Internal.enterDrainRules M) :
    r ∈ M.normalize.rules := by
  simp only [normalize, Internal.normalizedRules, List.mem_append]
  exact Or.inl (Or.inr hr)
```

```lean
private theorem normalizedDrainRule_mem (M : OneTurnNPDA α State Stack)
    {r : PushdownRule α (NormalState α State Stack × TurnPhase)
      (NPDA.FinalStack Stack)} (hr : r ∈ Internal.normalizedDrainRules M) :
    r ∈ M.normalize.rules := by
  simp only [normalize, Internal.normalizedRules, List.mem_append]
  exact Or.inr hr
```

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
