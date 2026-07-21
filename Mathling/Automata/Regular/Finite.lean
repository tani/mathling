    module

    public import Mathling.Automata.Pushdown

    import LiterateLean
    open scoped LiterateLean


# Mathling / Automata / Regular / Finite モジュール

DFA を NFA に、さらに有限オートマトンをスタックを実質的に使わない NPDA に埋め込む。各埋め込みは遷移構造だけでなく受理言語を保存し、正則言語から文脈自由言語への包含を構成的に接続する。

```lean

/-!
# Finite-to-pushdown conversions

Language-preserving conversions from NFAs and DFAs to pushdown automata.
-/

namespace Mathling.Automata

namespace NFA

/-- Enumerate the local, stack-preserving pushdown rules of a finite NFA. -/
public noncomputable def localPushdownRules [Fintype α] [Fintype σ]
    (M : NFA α σ) : List (PushdownRule α σ PUnit) := by
  classical
  exact ((Finset.univ.product (Finset.univ.product Finset.univ)).filter fun qa =>
    qa.2.2 ∈ M.step qa.1 qa.2.1).toList.map fun qa =>
      { source := qa.1
        input := some qa.2.1
        pop := PUnit.unit
        target := qa.2.2
        push := [PUnit.unit] }

/-- Regard a finite NFA as a finite-local NPDA whose sole stack marker is
preserved by every transition. -/
public noncomputable def toNPDA [Fintype α] [Fintype σ]
    (M : NFA α σ) : NPDA α σ PUnit := by
  classical
  exact
    { rules := M.localPushdownRules
      start := (Finset.univ.filter fun q => q ∈ M.start).toList
      accept := (Finset.univ.filter fun q => q ∈ M.accept).toList
      initialStack := [PUnit.unit] }

private theorem path_toNPDA_reaches [Fintype α] [Fintype σ]
    (M : NFA α σ) {q q' : σ} {w : List α} (p : M.Path q q' w) :
    M.toNPDA.Reaches (w, q, [PUnit.unit]) ([], q', [PUnit.unit]) := by
  induction p with
  | nil => exact Relation.ReflTransGen.refl
  | cons t s u a x hedge _ ih =>
      apply ih.head
      apply Mathling.Automata.NPDA.Step.consume
        ({ source := s, input := some a, pop := PUnit.unit,
           target := t, push := [PUnit.unit] } : PushdownRule α σ PUnit)
      · classical
        simp [toNPDA, localPushdownRules, hedge]
      · rfl

private theorem toNPDA_reaches_path [Fintype α] [Fintype σ]
    (M : NFA α σ) {c : NPDA.ID α σ PUnit} {q' : σ} {stack' : List PUnit}
    (h : M.toNPDA.Reaches c ([], q', stack'))
    (hstack : c.2.2 = [PUnit.unit]) :
    stack' = [PUnit.unit] ∧ Nonempty (M.Path c.2.1 q' c.1) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨hstack, ⟨.nil q'⟩⟩
  | head hstep _ ih =>
      cases hstep with
      | @consume a input tail rule mem input_eq =>
          classical
          simp only [toNPDA, localPushdownRules, List.mem_map,
            Finset.mem_toList, Finset.mem_filter] at mem
          rcases mem with ⟨qa, hqa, rfl⟩
          have ha : qa.2.1 = a := Option.some.inj input_eq
          subst a
          have htail : tail = [] := (List.cons.inj hstack).2
          subst tail
          rcases ih rfl with ⟨hfinal, ⟨path⟩⟩
          exact ⟨hfinal, ⟨.cons qa.2.2 qa.1 q' qa.2.1 input hqa.2 path⟩⟩
      | epsilon rule mem input_eq =>
          classical
          simp only [toNPDA, localPushdownRules, List.mem_map,
            Finset.mem_toList, Finset.mem_filter] at mem
          rcases mem with ⟨qa, hqa, rfl⟩
          exact (Option.some_ne_none _ input_eq).elim

/-- The finite-local NPDA embedding accepts exactly the NFA language. -/
@[important, grind =, simp] public theorem toNPDA_language [Fintype α] [Fintype σ]
    (M : NFA α σ) : M.toNPDA.language = M.accepts := by
  ext w
  rw [NFA.accepts_iff_exists_path]
  constructor
  · rintro ⟨q, hq, q', hq', stack, hreach⟩
    classical
    simp only [toNPDA, Finset.mem_toList, Finset.mem_filter,
      Finset.mem_univ, true_and] at hq hq'
    rcases M.toNPDA_reaches_path hreach rfl with ⟨_, path⟩
    exact ⟨q, hq, q', hq', path⟩
  · rintro ⟨q, hq, q', hq', ⟨path⟩⟩
    classical
    exact ⟨q, by simpa [toNPDA] using hq, q', by simpa [toNPDA] using hq',
      [PUnit.unit], M.path_toNPDA_reaches path⟩

end NFA

```

## NFA から有限局所 NPDA への埋め込み

有限な入力 alphabet と状態集合のもとで、`localPushdownRules` は NFA の遷移辺を有限列として列挙する。各規則は唯一の `PUnit` マーカーを pop して同じマーカーを push するため、スタックは実質的に変化しない。したがって変換後も探索の分岐は元の NFA の遷移関係だけで決まる。

正しさは NFA の `Path` と局所 NPDA の `Reaches` を相互変換して示す。逆変換では、すべての規則が consuming 規則であり、マーカーを保存することも同時に回収する。DFA の変換はこの NFA 埋め込みを再利用し、規則の一意性を元の遷移関数の単値性から証明する。

続いて、DFA を決定性版の DPDA へ同様に埋め込む。この場合は NFA の場合に帰着させることで証明を再利用する。

```lean
namespace DFA

/-- Regard a finite DFA as a deterministic finite-local PDA that preserves one
dummy stack marker. -/
public noncomputable def toDPDA [Fintype α] [Fintype σ]
    (M : DFA α σ) : DPDA α σ PUnit := by
  classical
  refine { toNPDA := Mathling.Automata.NFA.toNPDA M.toNFA, deterministic := ?_ }
  intro r s hr hs hsource _ hinput
  simp only [Mathling.Automata.NFA.toNPDA,
    Mathling.Automata.NFA.localPushdownRules, List.mem_map,
    Finset.mem_toList, Finset.mem_filter] at hr hs
  rcases hr with ⟨⟨q, a, q'⟩, hqa, rfl⟩
  rcases hs with ⟨⟨p, b, p'⟩, hpb, rfl⟩
  have hsymbol : a = b := by
    simpa only [Option.some_ne_none, false_or, Option.some.injEq] using hinput
  have hstate : q = p := hsource
  have htarget : q' = M.step q a := by
    simpa only [DFA.toNFA_step, Set.mem_singleton_iff] using hqa.2
  have htarget' : p' = M.step p b := by
    simpa only [DFA.toNFA_step, Set.mem_singleton_iff] using hpb.2
  subst p
  subst b
  subst q'
  subst p'
  rfl

/-- The stack-free local DPDA accepts exactly the DFA language. -/
@[important, grind =, simp] public theorem toDPDA_language
    [Fintype α] [Fintype σ] (M : DFA α σ) :
    M.toDPDA.language = M.accepts := by
  change (Mathling.Automata.NFA.toNPDA M.toNFA).language = M.accepts
  rw [Mathling.Automata.NFA.toNPDA_language, _root_.DFA.toNFA_correct]

end DFA

end Mathling.Automata

```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
