    module

    public import Mathling.Automata.Core
    public import Mathlib.Computability.MyhillNerode
    public import Mathlib.Data.Finite.Card
    public import Mathling.Meta.Important

    public import LiterateLean
    open scoped LiterateLean

    @[expose] public section

# Mathling / Automata / Theory / Minimization モジュール

このモジュールは Mathling のこの領域に属する定義、変換、および証明を提供する。公開される契約と依存関係は import 境界で明示し、実装は以下の Lean ブロックに限定する。

```lean
@[expose] public section

/-!
# DFA minimization

The canonical Myhill--Nerode quotient DFA and its cardinality bound.
-/

namespace Mathling.Automata

/-- The canonical DFA whose states are the left quotients of a language. -/
abbrev Language.minimalDFA (L : Language α) :
    DFA α (Set.range L.leftQuotient) := L.toDFA

/-- The canonical quotient DFA accepts its defining language. -/
@[simp] theorem Language.minimalDFA_accepts (L : Language α) :
    (Language.minimalDFA L).accepts = L := by
  change L.toDFA.accepts = L
  exact Language.accepts_toDFA L


/-- The quotient DFA has no more states than any DFA accepting the same language. -/
@[important] theorem Language.minimalDFA_card_le {α σ : Type*} [Fintype σ]
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

```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
