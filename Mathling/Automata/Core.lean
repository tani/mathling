    module

    public import Mathlib.Computability.DFA
    public import Mathlib.Computability.NFA
    public import Mathlib.Computability.EpsilonNFA
    public import Mathling.Meta.Important
    import LiterateLean
    open scoped LiterateLean


# Mathling / Automata / Core モジュール

Mathlib の DFA/NFA を Mathling の名前空間から利用するための型別名と、DFA を NFA として忘却する変換を提供する。変換後も受理言語が等しいことがこの層の中心契約であり、後続の正則言語変換はその等式だけに依存する。

このモジュールの冒頭では `Mathling.Automata` 名前空間を開き、その中で `DFA` を Mathlib の同名の型の単なる別名として定義する。新しい型を持ち込まず `abbrev` で再輸出するのは、後続のモジュールが Mathlib の DFA API（状態遷移、`accepts` など）をそのまま呼び出せるようにするためであり、もし独自の構造体として包み直していたら、Mathlib 側の補題を都度移植する二重管理が発生していた。

```lean
/-!
# Finite automata

Finite automata aliases, conversions, and regular-language characterizations.
-/



namespace Mathling.Automata

/-- Mathlib's deterministic finite automata, re-exported in the Mathling namespace. -/
public abbrev DFA (α σ : Type*) := _root_.DFA α σ
```

`NFA` も同じ理由・同じパターンで再輸出する。`DFA` とは独立に定義されているのは、Mathlib 上で両者が別個の型だからであり、両者を結びつけるのは後述の `toNFA_language` の役目である。ここで `NFA` 自体に新しい制約を課さないことで、非決定性オートマトンに関する既存の Mathlib の補題（受理判定や合成演算）を無変更で流用できる。

```lean
/-- Mathlib's nondeterministic finite automata, re-exported in the Mathling namespace. -/
public abbrev NFA (α σ : Type*) := _root_.NFA α σ
```

同様に `εNFA` を再輸出する。epsilon 遷移を許す最も一般的なオートマトン表現をここで用意しておくことで、後続の言語変換（例えば正規表現から NFA を経由せず直接 εNFA を構成する場合）が中間の epsilon 除去なしに定義できるようになる。

```lean
/-- Mathlib's epsilon-NFAs, re-exported in the Mathling namespace. -/
public abbrev εNFA (α σ : Type*) := _root_.εNFA α σ
```

以上の3つの型別名を用意しただけでは、DFA・NFA・εNFA が「同じ言語を表す3つの見方」であることは保証されない。この補題はその最初の橋渡しであり、`M.toNFA`（Mathlib 提供の忘却変換）が言語を変えないことを `simp`／`grind` に登録する。これがないと、DFA 側で示した性質を NFA 側の議論に持ち込むたびに手動で `DFA.toNFA_correct` を展開する必要が生じる。

```lean
/-- Converting a DFA to an NFA preserves its language. -/
@[grind =, simp] public theorem DFA.toNFA_language {α σ : Type*} (M : DFA α σ) :
    M.toNFA.accepts = M.accepts := _root_.DFA.toNFA_correct M
```

逆向きの橋渡しとして、NFA を決定性化する `M.toDFA` も受理言語を保存することを記録する。`DFA.toNFA_language` と対になることで、DFA と NFA のどちらの表現からでも他方へ言語を保ったまま行き来できるという対称性が成立し、これが直後の `Language.isRegular_iff_nfa` で存在量化子の書き換えに使われる。

```lean
/-- Determinizing an NFA preserves its language. -/
@[grind =, simp] public theorem NFA.toDFA_language {α σ : Type*} (M : NFA α σ) :
    M.toDFA.accepts = M.accepts := _root_.NFA.toDFA_correct
```

εNFA からその epsilon 除去済みの NFA への変換も同様に言語を保つ。これにより εNFA を経由する構成（例えば和・連接・Kleene 閉包で自然に epsilon 遷移が現れる場合）を、最終的に epsilon なしの NFA へ落とし込んでも受理言語の議論を継続できる。

```lean
/-- Removing epsilon transitions preserves an epsilon-NFA's language. -/
@[grind =, simp] public theorem εNFA.toNFA_language {α σ : Type*} (M : εNFA α σ) :
    M.toNFA.accepts = M.accepts := _root_.εNFA.toNFA_correct M
```

最後に、NFA を（空の遷移集合を追加するだけで）εNFA として埋め込む向きの保存性も記録する。この4つの `simp`／`grind` 補題が揃うことで、DFA・NFA・εNFA の三者間の変換はどの順に組み合わせても受理言語を変えないという閉じた体系になり、以降の証明はこれらを土台として `Language.isRegular_iff_nfa`／`Language.isRegular_iff_εnfa` を導出するだけで済む。

```lean
/-- Adding empty epsilon transitions to an NFA preserves its language. -/
@[grind =, simp] public theorem NFA.toεNFA_language {α σ : Type*} (M : NFA α σ) :
    M.toεNFA.accepts = M.accepts := _root_.NFA.toεNFA_correct M
```

## 正則言語の存在量化を書き換える

ここまでの型別名と4つの保存補題は道具立てに過ぎない。この節ではそれらを使って、`IsRegular` の定義に登場する有限状態機械の種類（DFA／NFA／εNFA）を、証明の都合に応じて自由に取り換えられるようにする——これが本モジュールの中心契約である。

`Language.isRegular_iff_nfa` は、これらの変換の正しさを使って `IsRegular` の存在量化を DFA から NFA へ移し替える。証明はどちらの向きも一方向の変換を適用するだけでよい: `IsRegular`（DFA の存在）から NFA の存在を得るには `M.toNFA` を、逆向きには `M.toDFA` を witness として渡し、対応する `simp` 補題（`DFA.toNFA_correct`／`NFA.toDFA_correct`）で言語の一致を示す。つまり NFA 存在版の定義は DFA 存在版の定義と同値になる——変換が言語を保存する以上、「間に有限状態機械が挟まる」という条件は DFA でも NFA でも本質的に同じ制約だからである。この同値がないと、以降のモジュールで NFA を使って正則性を示すたびに DFA の定義まで遡って議論する必要が生じる。

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
```

`Language.isRegular_iff_εnfa` は同じ書き換えを εNFA まで一段延長する。ここでは `DFA.toNFA_correct` を直接使わず、直前の `Language.isRegular_iff_nfa` を経由してから `εNFA.toNFA_language`／`NFA.toεNFA_language` を適用するだけで証明が閉じる点に注意したい——これは DFA・NFA・εNFA が言語を保ったまま互いに変換できるという先の4補題の効果であり、もしそれらがなければこの補題も `isRegular_iff` まで遡って一から証明し直す必要があった。名前空間 `Mathling.Automata` はこの補題の直後で閉じられ、以降のモジュールはここで確立された3つの同値な `IsRegular` の特徴づけだけを外部契約として利用する。

```lean
/-- A language is regular exactly when some finite-state epsilon-NFA accepts it. -/
@[important, grind =] public theorem Language.isRegular_iff_εnfa
    {α : Type*} {L : Language α} :
    L.IsRegular ↔ ∃ σ : Type*, ∃ _ : Fintype σ, ∃ M : εNFA α σ, M.accepts = L := by
  constructor
  · intro h
    obtain ⟨σ, inst, M, hM⟩ := Language.isRegular_iff_nfa.mp h
    exact ⟨σ, inst, M.toεNFA, M.toεNFA_language.trans hM⟩
  · rintro ⟨σ, inst, M, hM⟩
    apply Language.isRegular_iff_nfa.mpr
    exact ⟨σ, inst, M.toNFA, M.toNFA_language.trans hM⟩

end Mathling.Automata
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
