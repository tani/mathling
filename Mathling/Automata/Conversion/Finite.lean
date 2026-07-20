    module

    public import Mathling.Automata.Conversion.Pushdown

    public import LiterateLean
    open scoped LiterateLean

    @[expose] public section

# Mathling / Automata / Conversion / Finite モジュール

このモジュールは Mathling のこの領域に属する定義、変換、および証明を提供する。公開される契約と依存関係は import 境界で明示し、実装は以下の Lean ブロックに限定する。

```lean
@[expose] public section

/-!
# Finite-to-pushdown conversions

Language-preserving conversions from NFAs and DFAs to pushdown automata.
-/

namespace Mathling.Automata

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
  have hconversion : DPDA.toNPDA (DFA.toDPDA M) =
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
  rw [DPDA.language, hconversion, Mathling.Automata.NFA.toNPDA_language,
    _root_.DFA.toNFA_correct]

end DFA

end Mathling.Automata

```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
