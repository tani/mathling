module

public import Mathling.Automata.Finite

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
