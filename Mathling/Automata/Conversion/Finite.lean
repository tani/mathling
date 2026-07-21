    module

    public import Mathling.Automata.Conversion.Pushdown

    import LiterateLean
    open scoped LiterateLean


# Mathling / Automata / Conversion / Finite モジュール

DFA を NFA に、さらに有限オートマトンをスタックを実質的に使わない NPDA に埋め込む。各埋め込みは遷移構造だけでなく受理言語を保存し、正則言語から文脈自由言語への包含を構成的に接続する。

```lean

/-!
# Finite-to-pushdown conversions

Language-preserving conversions from NFAs and DFAs to pushdown automata.
-/

namespace Mathling.Automata

namespace NFA

/-- Regard an NFA as an NPDA that never changes its empty stack. -/
public def toWholeStackNPDA (M : NFA α σ) : WholeStackNPDA α σ PUnit where
  step q sym stack :=
    match sym with
    | some a => {next | next.1 ∈ M.step q a ∧ next.2 = stack}
    | none => ∅
  start := M.start
  accept := M.accept
  initialStack := []

private theorem path_toWholeStackNPDA_reaches (M : NFA α σ) {q q' : σ} {w : List α} :
    Nonempty (M.Path q q' w) → ∀ stack : List PUnit,
      M.toWholeStackNPDA.Reaches (w, q, stack) ([], q', stack) := by
  rintro ⟨p⟩ stack
  induction p with
  | nil => exact Relation.ReflTransGen.refl
  | cons t s u a x hstep _ ih =>
      exact ih.head (.consume ⟨hstep, rfl⟩)

grind_pattern path_toWholeStackNPDA_reaches =>
  M.Path q q' w,
  M.toWholeStackNPDA.Reaches (w, q, stack) ([], q', stack)

@[grind .] private theorem toWholeStackNPDA_reaches_path_aux (M : NFA α σ)
    {c : WholeStackNPDA.ID α σ PUnit}
    {q' : σ} {stack' : List PUnit}
    (h : M.toWholeStackNPDA.Reaches c ([], q', stack')) :
    stack' = c.2.2 ∧ Nonempty (M.Path c.2.1 q' c.1) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨rfl, ⟨.nil q'⟩⟩
  | head hstep _ ih =>
      cases hstep with
      | consume hmem =>
          obtain ⟨hpathStack, ⟨path⟩⟩ := ih
          obtain ⟨edge, rfl⟩ := hmem
          exact ⟨hpathStack, ⟨.cons _ _ _ _ _ edge path⟩⟩
      | epsilon hmem => simp [toWholeStackNPDA] at hmem

@[grind .] private theorem toWholeStackNPDA_reaches_path (M : NFA α σ)
    {q q' : σ} {w : List α}
    {stack stack' : List PUnit}
    (h : M.toWholeStackNPDA.Reaches (w, q, stack) ([], q', stack')) :
    stack' = stack ∧ Nonempty (M.Path q q' w) :=
  M.toWholeStackNPDA_reaches_path_aux h

/-- The stack-free NPDA conversion accepts exactly the NFA language. -/
@[grind =, simp] public theorem toWholeStackNPDA_language (M : NFA α σ) :
    M.toWholeStackNPDA.language = M.accepts := by
  ext w
  rw [NFA.accepts_iff_exists_path]
  constructor
  · rintro ⟨q, hq, q', hq', stack, hreach⟩
    exact ⟨q, hq, q', hq', (M.toWholeStackNPDA_reaches_path hreach).2⟩
  · rintro ⟨q, hq, q', hq', ⟨path⟩⟩
    exact ⟨q, hq, q', hq', [], M.path_toWholeStackNPDA_reaches ⟨path⟩ []⟩

end NFA

```

## NFA から NPDA への埋め込み

`NFA.toWholeStackNPDA` は NFA をスタック型 `PUnit`（要素が1つしかない型）の `WholeStackNPDA` とみなすことで、「スタックを一切使わない PDA」として埋め込む。`step` は入力記号ありの遷移のみを NFA の遷移関係からそのまま持ち上げ、スタックの中身 `stack` は変化させない（`next.2 = stack`）。epsilon 遷移は NFA 側に存在しないため空集合を返す。

正しさの証明は「NFA の経路（`Path`）」と「全スタック PDA の到達関係（`Reaches`）」を往復させる形を取る。`path_toWholeStackNPDA_reaches` は NFA の経路から対応する到達列を構成し、`toWholeStackNPDA_reaches_path`（内部で `toWholeStackNPDA_reaches_path_aux` に委譲）は逆向きに経路とスタック不変性を回復する。`toWholeStackNPDA_language` はこの往復から `accepts_iff_exists_path` を経由して言語の一致を導く。

続いて、DFA を決定性版の DPDA へ同様に埋め込む。この場合は NFA の場合に帰着させることで証明を再利用する。

```lean
namespace DFA

/-- Regard a DFA as a deterministic PDA that never changes its empty stack. -/
public def toDPDA (M : DFA α σ) : DPDA α σ PUnit where
  step q sym stack := sym.map fun a => (M.step q a, stack)
  start := M.start
  accept := M.accept
  initialStack := []

/-- The stack-free DPDA conversion accepts exactly the DFA language. -/
@[grind =, simp] public theorem toDPDA_language (M : DFA α σ) :
    M.toDPDA.language = M.accepts := by
  have hconversion : DPDA.toWholeStackNPDA (DFA.toDPDA M) =
      Mathling.Automata.NFA.toWholeStackNPDA M.toNFA := by
    apply WholeStackNPDA.ext
    · funext q sym stack
      ext next
      rcases next with ⟨nextq, nextStack⟩
      cases sym <;>
        simp [DFA.toDPDA, DPDA.toWholeStackNPDA,
          Mathling.Automata.NFA.toWholeStackNPDA]
    · ext q
      simp [DFA.toDPDA, DPDA.toWholeStackNPDA,
        Mathling.Automata.NFA.toWholeStackNPDA]
    · rfl
    · rfl
  rw [DPDA.language, hconversion,
    Mathling.Automata.NFA.toWholeStackNPDA_language,
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
