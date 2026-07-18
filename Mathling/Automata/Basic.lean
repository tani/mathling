import Mathlib.Computability.DFA
import Mathlib.Computability.NFA
import Mathlib.Computability.EpsilonNFA
import Mathlib.Computability.MyhillNerode
import Mathlib.Data.Finite.Card

/-!
# Automata

Finite automata, pushdown automata, conversions, and Myhill--Nerode minimization.
-/

namespace Mathling.Automata

/-- Mathlib's deterministic finite automata, re-exported in the Mathling namespace. -/
abbrev DFA (α σ : Type*) := _root_.DFA α σ

/-- Mathlib's nondeterministic finite automata, re-exported in the Mathling namespace. -/
abbrev NFA (α σ : Type*) := _root_.NFA α σ

/-- Mathlib's epsilon-NFAs, re-exported in the Mathling namespace. -/
abbrev εNFA (α σ : Type*) := _root_.εNFA α σ

/-- Converting a DFA to an NFA preserves its language. -/
@[simp] theorem DFA.toNFA_language {α σ : Type*} (M : DFA α σ) :
    M.toNFA.accepts = M.accepts := _root_.DFA.toNFA_correct M

/-- Determinizing an NFA preserves its language. -/
@[simp] theorem NFA.toDFA_language {α σ : Type*} (M : NFA α σ) :
    M.toDFA.accepts = M.accepts := _root_.NFA.toDFA_correct

/-- Removing epsilon transitions preserves an epsilon-NFA's language. -/
@[simp] theorem εNFA.toNFA_language {α σ : Type*} (M : εNFA α σ) :
    M.toNFA.accepts = M.accepts := _root_.εNFA.toNFA_correct M

/-- A language is regular exactly when some finite-state NFA accepts it. -/
theorem Language.isRegular_iff_nfa {α : Type*} {L : Language α} :
    L.IsRegular ↔ ∃ σ : Type*, ∃ _ : Fintype σ, ∃ M : NFA α σ, M.accepts = L := by
  constructor
  · rintro h
    obtain ⟨σ, _, M, rfl⟩ := Language.isRegular_iff.mp h
    exact ⟨σ, inferInstance, M.toNFA, _root_.DFA.toNFA_correct M⟩
  · rintro ⟨σ, _, M, rfl⟩
    apply Language.isRegular_iff.mpr
    exact ⟨Set σ, inferInstance, M.toDFA, _root_.NFA.toDFA_correct⟩

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

namespace NFA

/-- Regard an NFA as an NPDA that never changes its empty stack. -/
def toNPDA (M : NFA α σ) : NPDA α σ PUnit where
  step q sym stack :=
    match sym with
    | some a => {next | next.1 ∈ M.step q a ∧ next.2 = stack}
    | none => ∅
  start := M.start
  accept := M.accept
  initialStack := []

private theorem path_toNPDA_reaches (M : NFA α σ) {q q' : σ} {w : List α}
    (p : M.Path q q' w) (stack : List PUnit) :
    M.toNPDA.Reaches (w, q, stack) ([], q', stack) := by
  induction p with
  | nil => exact Relation.ReflTransGen.refl
  | cons t s u a x hstep _ ih =>
      exact ih.head (.consume ⟨hstep, rfl⟩)

private theorem toNPDA_reaches_path_aux (M : NFA α σ) {c : NPDA.ID α σ PUnit}
    {q' : σ} {stack' : List PUnit}
    (h : M.toNPDA.Reaches c ([], q', stack')) :
    stack' = c.2.2 ∧ Nonempty (M.Path c.2.1 q' c.1) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨rfl, ⟨.nil q'⟩⟩
  | head hstep _ ih =>
      cases hstep with
      | consume hmem =>
          obtain ⟨hpathStack, ⟨path⟩⟩ := ih
          obtain ⟨edge, rfl⟩ := hmem
          exact ⟨hpathStack, ⟨.cons _ _ _ _ _ edge path⟩⟩
      | epsilon hmem => simp [toNPDA] at hmem

private theorem toNPDA_reaches_path (M : NFA α σ) {q q' : σ} {w : List α}
    {stack stack' : List PUnit}
    (h : M.toNPDA.Reaches (w, q, stack) ([], q', stack')) :
    stack' = stack ∧ Nonempty (M.Path q q' w) :=
  M.toNPDA_reaches_path_aux h

/-- The stack-free NPDA conversion accepts exactly the NFA language. -/
@[simp] theorem toNPDA_language (M : NFA α σ) :
    M.toNPDA.language = M.accepts := by
  ext w
  rw [NFA.accepts_iff_exists_path]
  constructor
  · rintro ⟨q, hq, q', hq', stack, hreach⟩
    exact ⟨q, hq, q', hq', (M.toNPDA_reaches_path hreach).2⟩
  · rintro ⟨q, hq, q', hq', ⟨path⟩⟩
    exact ⟨q, hq, q', hq', [], M.path_toNPDA_reaches path []⟩

end NFA

namespace DFA

/-- Regard a DFA as a deterministic PDA that never changes its empty stack. -/
def toDPDA (M : DFA α σ) : DPDA α σ PUnit where
  step q sym stack := sym.map fun a => (M.step q a, stack)
  start := M.start
  accept := M.accept
  initialStack := []

/-- The stack-free DPDA conversion accepts exactly the DFA language. -/
@[simp] theorem toDPDA_language (M : DFA α σ) :
    M.toDPDA.language = M.accepts := by
  have h : DPDA.toNPDA (DFA.toDPDA M) =
      Mathling.Automata.NFA.toNPDA M.toNFA := by
    apply NPDA.ext
    · funext q sym stack
      ext next
      rcases next with ⟨nextq, nextStack⟩
      cases sym <;>
        simp [DFA.toDPDA, DPDA.toNPDA, Mathling.Automata.NFA.toNPDA]
    · ext q
      simp [DFA.toDPDA, DPDA.toNPDA, Mathling.Automata.NFA.toNPDA]
    · rfl
    · rfl
  rw [DPDA.language, h, Mathling.Automata.NFA.toNPDA_language,
    _root_.DFA.toNFA_correct]

end DFA

/-- The canonical DFA whose states are the left quotients of a language. -/
noncomputable abbrev Language.minimalDFA (L : Language α) :
    DFA α (Set.range L.leftQuotient) := L.toDFA

/-- The canonical quotient DFA accepts its defining language. -/
@[simp] theorem Language.minimalDFA_accepts (L : Language α) :
    (Language.minimalDFA L).accepts = L := by
  change L.toDFA.accepts = L
  exact Language.accepts_toDFA L

/-- Regularity equips the state type of the canonical quotient DFA with a `Fintype`. -/
noncomputable def Language.minimalDFAFintype {L : Language α} (h : L.IsRegular) :
    Fintype (Set.range L.leftQuotient) :=
  h.finite_range_leftQuotient.fintype

/-- The quotient DFA has no more states than any DFA accepting the same language. -/
theorem Language.minimalDFA_card_le {α σ : Type*} [Fintype σ]
    (M : DFA α σ) :
    Nat.card (Set.range M.accepts.leftQuotient) ≤ Fintype.card σ := by
  rw [Language.leftQuotient_accepts]
  let inclusion : Set.range (M.acceptsFrom ∘ M.eval) → Set.range M.acceptsFrom :=
    fun x => ⟨x.1, by
      obtain ⟨w, hw⟩ := x.2
      exact ⟨M.eval w, hw⟩⟩
  have inclusion_injective : Function.Injective inclusion := fun x y h =>
    Subtype.ext (congrArg (fun z : Set.range M.acceptsFrom => z.1) h)
  letI : Finite (Set.range M.acceptsFrom) :=
    Finite.of_surjective (Set.rangeFactorization M.acceptsFrom)
      Set.rangeFactorization_surjective
  letI : Finite (Set.range (M.acceptsFrom ∘ M.eval)) :=
    Finite.of_injective inclusion inclusion_injective
  calc
    Nat.card (Set.range (M.acceptsFrom ∘ M.eval)) ≤
        Nat.card (Set.range M.acceptsFrom) :=
      Nat.card_le_card_of_injective inclusion inclusion_injective
    _ ≤ Nat.card σ := Finite.card_range_le M.acceptsFrom
    _ = Fintype.card σ := Nat.card_eq_fintype_card

end Mathling.Automata
