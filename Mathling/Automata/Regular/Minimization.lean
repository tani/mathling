    module

    public import Mathling.Automata.Core
    public import Mathlib.Computability.MyhillNerode
    public import Mathlib.SetTheory.Cardinal.NatCard
    public import Mathling.Meta.Important

    import LiterateLean
    open scoped LiterateLean


# Mathling / Automata / Regular / Minimization モジュール

DFA の状態を将来の受理挙動で同値視し、その Myhill–Nerode 商を最小化 DFA として構成する。商への射影が遷移と受理を保存し、元の DFA と同じ言語を認識することまでを公開契約とする。

```lean
/-!
# DFA minimization

The canonical Myhill--Nerode quotient DFA and its cardinality bound.
-/



namespace Mathling.Automata

/-- The canonical DFA whose states are the left quotients of a language. -/
public abbrev Language.minimalDFA (L : Language α) :
    DFA α (Set.range L.leftQuotient) := L.toDFA
```

```lean
/-- The canonical quotient DFA accepts its defining language. -/
@[important, grind =, simp] public theorem Language.minimalDFA_accepts (L : Language α) :
    (Language.minimalDFA L).accepts = L := by
  change L.toDFA.accepts = L
  exact Language.accepts_toDFA L
```

## 正準商 DFA とその受理言語

$`L`$ の左商（left quotient）$`L.\mathrm{leftQuotient}`$ は、語 $`u`$ を「その後に続く語 $`v`$ が $`uv \in L`$ を満たすかどうか」という述語に写す。`Language.minimalDFA` はこの左商のなす集合 `Set.range L.leftQuotient` を状態集合とする DFA（`Language.toDFA` の再掲）であり、Myhill–Nernode の同値類そのものを状態として採用する正準構成である。`minimalDFA_accepts` はこの DFA が定義もとの言語 $`L`$ を過不足なく受理することを保証し、以降の議論はこの事実を土台に「状態数の最小性」へ進む。

なぜ左商が「状態」として正しい単位なのか——2つの語 $`u_1, u_2`$ が同じ状態に写るべきなのは、任意の $`v`$ について $`u_1 v \in L \iff u_2 v \in L`$ が成り立つとき、かつそのときに限る。これはまさに左商が等しいという条件 $`L.\mathrm{leftQuotient}\,u_1 = L.\mathrm{leftQuotient}\,u_2`$ に一致する。したがって左商の相異なる値の個数は、言語 $`L`$ を区別するために必要な状態数の下限を与える。次の定理はこれを、任意の DFA が持つ状態数の上限として定式化する。

```lean
/-- The quotient DFA has no more states than any DFA accepting the same language. -/
@[important, grind .] public theorem Language.minimalDFA_card_le {α σ : Type*} [Fintype σ]
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
