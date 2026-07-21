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

```

## NFA から有限局所 NPDA への埋め込み

有限な入力 alphabet と状態集合のもとで、`localPushdownRules` は NFA の遷移辺を有限列として列挙する。各規則は唯一の `PUnit` マーカーを pop して同じマーカーを push するため、スタックは実質的に変化しない。したがって変換後も探索の分岐は元の NFA の遷移関係だけで決まる。

有限NFAの遷移辺をひとつのpush/pop規則へ機械的に翻訳する。各規則はスタックマーカー`PUnit`を一つpopし同じマーカーを一つpushするため、スタック操作は事後的に何の情報も運ばない——つまりこの規則列は「スタックなしのNPDA」を模倣するためだけに存在する。ここで生成された規則リストが、以下の `toNPDA`／`toDPDA` の遷移構造そのものになる。

```lean
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
```

`localPushdownRules` で得た規則列を NPDA 構造体に詰め、開始・受理状態集合とスタック初期値 `[PUnit.unit]` を設定する。スタックマーカーを常に一枚に保つことで、以降の証明はスタックの深さを気にせず経路の存在だけに帰着できる。

```lean
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
```

正しさは NFA の `Path` と局所 NPDA の `Reaches` を相互変換して示す。まずこの一方向: NFA の `Path` を `toNPDA` 上の `Reaches` へ単調に持ち上げる。帰納法の各ステップでは、`localPushdownRules` により生成された対応する規則が存在することを `classical simp` で示すだけでよく、スタックは常に `[PUnit.unit]` のまま消費規則を辿れることを保証する。次の `toNPDA_reaches_path` と対になり、`toNPDA_language` の両方向の証明を支える。

```lean
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
```

逆変換では、すべての規則が consuming 規則であり、マーカーを保存することも同時に回収する。スタックが常に単一マーカーのまま `Reaches` した経路は、対応する NFA の `Path` へ折り返せる。`NPDA.Step` の `epsilon` 規則が `localPushdownRules` には現れない（`input` は常に `some` であり、`Option` の `none` 反証で即座に排除される）ことが鍵であり、これにより NPDA の経路が NFA の経路と一対一に対応することが保証される。

```lean
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
```

`path_toNPDA_reaches` と `toNPDA_reaches_path` を組み合わせ、`toNPDA` が元の NFA の受理言語をそのまま保つことを結論する主定理。`@[important]` が付き、この埋め込みが正則言語から文脈自由言語（NPDA 受理言語）への構成的な包含関係を与える橋渡しであることを示す。

```lean
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

## DFA から決定性 DPDA への埋め込み

続いて、DFA を決定性版の DPDA へ同様に埋め込む。この場合は NFA の場合に帰着させることで証明を再利用する。`toDPDA` は DFA の遷移関数を `localPushdownRules M.toNFA` で生成される規則に基づき構成し、決定性 (`deterministic`) を証明する。決定性の証明は「同じ `source` と `input` を持つ二つの規則は同じ `target` を持つ」ことを `DFA.toNFA_step` の単一性 (`Set.mem_singleton_iff`) から導く点が核心であり、これがなければ一般の PDA 規則から作った `toDPDA` が実際に決定性オートマトンとして well-formed であることが保証できない。

```lean
namespace DFA

/-- Regard a finite DFA as a deterministic finite-local PDA that preserves one
dummy stack marker. -/
public noncomputable def toDPDA [Fintype α] [Fintype σ]
    (M : DFA α σ) : Mathling.Automata.DPDA α σ PUnit := by
  classical
  refine
    { rules := Mathling.Automata.NFA.localPushdownRules M.toNFA
      start := M.start
      accept := (Finset.univ.filter fun q => q ∈ M.accept).toList
      initialStack := [PUnit.unit]
      deterministic := ?_ }
  intro r s hr hs hsource _ hinput
  simp only [Mathling.Automata.NFA.localPushdownRules, List.mem_map,
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
```

`toDPDA` の `toNPDA` が（開始状態リストの表現を除いて）NFA 側の `toNPDA M.toNFA` と定義上一致することを `hmachine` で示し、既に証明済みの `NFA.toNPDA_language` と `DFA.toNFA_correct` を合成して結論する。これにより Finite.lean の埋め込み系列全体——NFA→NPDA、DFA→DPDA——が受理言語を保存する一貫した変換であることが確定する。

```lean
/-- The stack-free local DPDA accepts exactly the DFA language. -/
@[important, grind =, simp] public theorem toDPDA_language
    [Fintype α] [Fintype σ] (M : DFA α σ) :
    M.toDPDA.language = M.accepts := by
  classical
  have hstart :
      (Finset.univ.filter fun q : σ => q ∈ M.toNFA.start).toList = [M.start] := by
    rw [show (Finset.univ.filter fun q : σ => q ∈ M.toNFA.start) = {M.start} by
      ext q
      simp]
    exact Finset.toList_singleton M.start
  have hmachine : M.toDPDA.toNPDA = Mathling.Automata.NFA.toNPDA M.toNFA := by
    change
      ({ rules := Mathling.Automata.NFA.localPushdownRules M.toNFA
         start := [M.start]
         accept := (Finset.univ.filter fun q => q ∈ M.accept).toList
         initialStack := [PUnit.unit] } : NPDA α σ PUnit) =
      ({ rules := Mathling.Automata.NFA.localPushdownRules M.toNFA
         start := (Finset.univ.filter fun q => q ∈ M.toNFA.start).toList
         accept := (Finset.univ.filter fun q => q ∈ M.toNFA.accept).toList
         initialStack := [PUnit.unit] } : NPDA α σ PUnit)
    rw [hstart]
    rfl
  rw [Mathling.Automata.DPDA.language, hmachine,
    Mathling.Automata.NFA.toNPDA_language, _root_.DFA.toNFA_correct]

end DFA

end Mathling.Automata
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
