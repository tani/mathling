    module

    public import Mathlib.Computability.DFA
    public import Mathlib.Computability.NFA
    public import Mathlib.Computability.EpsilonNFA
    public import Mathling.Meta.Important
    import LiterateLean
    open scoped LiterateLean


# Mathling / Automata / Core モジュール

Mathlib の DFA/NFA を Mathling の名前空間から利用するための型別名と、DFA を NFA として忘却する変換を提供する。変換後も受理言語が等しいことがこの層の中心契約であり、後続の正則言語変換はその等式だけに依存する。

```lean

/-!
# Finite automata

Finite automata aliases, conversions, and regular-language characterizations.
-/

namespace Mathling.Automata

/-- Mathlib's deterministic finite automata, re-exported in the Mathling namespace. -/
public abbrev DFA (α σ : Type*) := _root_.DFA α σ

/-- Mathlib's nondeterministic finite automata, re-exported in the Mathling namespace. -/
public abbrev NFA (α σ : Type*) := _root_.NFA α σ

/-- Mathlib's epsilon-NFAs, re-exported in the Mathling namespace. -/
public abbrev εNFA (α σ : Type*) := _root_.εNFA α σ

/-- Converting a DFA to an NFA preserves its language. -/
@[grind =, simp] public theorem DFA.toNFA_language {α σ : Type*} (M : DFA α σ) :
    M.toNFA.accepts = M.accepts := _root_.DFA.toNFA_correct M

/-- Determinizing an NFA preserves its language. -/
@[grind =, simp] public theorem NFA.toDFA_language {α σ : Type*} (M : NFA α σ) :
    M.toDFA.accepts = M.accepts := _root_.NFA.toDFA_correct

/-- Removing epsilon transitions preserves an epsilon-NFA's language. -/
@[grind =, simp] public theorem εNFA.toNFA_language {α σ : Type*} (M : εNFA α σ) :
    M.toNFA.accepts = M.accepts := _root_.εNFA.toNFA_correct M

```

## 型の再輸出と変換の正しさ

`DFA`／`NFA`／`εNFA` は Mathlib の同名の型をそのまま `Mathling.Automata` 名前空間へ再輸出する `abbrev` であり、新たな構造を導入するものではない。3つの `simp` 補題 `DFA.toNFA_language`／`NFA.toDFA_language`／`εNFA.toNFA_language` は、決定性化・非決定性化・epsilon 除去という各変換が受理言語を保存することを記録する。これらは以降のモジュールで変換を跨いだ書き換えを `simp` に任せるための基礎となる。

続く `Language.isRegular_iff_nfa` は、これらの変換の正しさを使って `IsRegular` の存在量化を DFA から NFA へ移し替える。証明はどちらの向きも一方向の変換を適用するだけでよい: `IsRegular`（DFA の存在）から NFA の存在を得るには `M.toNFA` を、逆向きには `M.toDFA` を witness として渡し、対応する `simp` 補題（`DFA.toNFA_correct`／`NFA.toDFA_correct`）で言語の一致を示す。つまり NFA 存在版の定義は DFA 存在版の定義と同値になる——変換が言語を保存する以上、「間に有限状態機械が挟まる」という条件は DFA でも NFA でも本質的に同じ制約だからである。

```lean
/-- A language is regular exactly when some finite-state NFA accepts it. -/
@[important, grind =] public theorem Language.isRegular_iff_nfa {α : Type*} {L : Language α} :
    L.IsRegular ↔ ∃ σ : Type*, ∃ _ : Fintype σ, ∃ M : NFA α σ, M.accepts = L := by
  constructor
  · rintro h
    obtain ⟨σ, _, M, rfl⟩ := Language.isRegular_iff.mp h
    exact ⟨σ, inferInstance, M.toNFA, _root_.DFA.toNFA_correct M⟩
  · rintro ⟨σ, _, M, rfl⟩
    apply Language.isRegular_iff.mpr
    exact ⟨Set σ, inferInstance, M.toDFA, _root_.NFA.toDFA_correct⟩

end Mathling.Automata

```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
