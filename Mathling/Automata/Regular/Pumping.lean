    module

    public import Mathling.Automata.Core
    public import Mathling.Meta.Important

    import LiterateLean
    open scoped LiterateLean


# Mathling / Automata / Regular / Pumping モジュール

Mathlib の有限オートマトン版 pumping lemma を、Mathling が公開する言語レベルの正則性述語へ接続する。得られる分解は語の長さ境界、非空な反復部分、すべての反復回数での言語所属を同時に保証する。

`Language.IsRegular` は「有限状態の DFA が存在して受理する」という存在量化として定義されているため、汲み上げ補題の移送は単純である: 証人の DFA を取り出し（`rcases h with ⟨σ, _, M, rfl⟩`）、その DFA に対して Mathlib が既に持つ `DFA.pumping_lemma` をそのまま適用するだけでよい。汲み上げ定数 $`p`$ は状態数 $`\mathrm{Fintype.card}\ σ`$ に取り、$`p \ge 1`$ は開始状態 `M.start` の存在から従う。

```lean

/-!
# Pumping lemma for regular languages

This module transfers Mathlib's DFA pumping lemma to `Language.IsRegular`.
-/



namespace Mathling.Automata

```

```lean
open Computability

/-- Every regular language satisfies the pumping lemma. -/
@[grind ., important] public theorem Language.IsRegular.pumping_lemma
    {α : Type*} {L : Language α} (h : L.IsRegular) :
    ∃ p ≥ 1, ∀ x ∈ L, p ≤ x.length →
      ∃ a b c, x = a ++ b ++ c ∧ a.length + b.length ≤ p ∧ b ≠ [] ∧
        (({a} : Language α) * KStar.kstar ({b} : Language α) *
          ({c} : Language α)) ≤ L := by
  rcases h with ⟨σ, _, M, rfl⟩
  refine ⟨Fintype.card σ, Fintype.card_pos_iff.mpr ⟨M.start⟩, ?_⟩
  intro x hx hlen
  exact M.pumping_lemma hx hlen

end Mathling.Automata

```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
