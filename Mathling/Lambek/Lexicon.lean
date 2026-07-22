    module

    import Mathlib.Data.List.Basic

    import LiterateLean
    open scoped LiterateLean


# Lambek lexicons

A lexicon is a finite, ambiguous relation between terminal symbols and
categories. Its categorization relation preserves the order and length of the
input word.

```lean
namespace Mathling.Lambek

public structure Lexicon (T Cat : Type*) where
  entries : List (T × Cat)
```

```lean
namespace Lexicon

variable {T Cat : Type*}
```

Each constructor consumes exactly one terminal and one category. Membership in
the entry list permits several categories for the same terminal.

```lean
@[grind cases] public inductive Categorizes (lexicon : Lexicon T Cat) :
    List T → List Cat → Prop
  | nil : Categorizes lexicon [] []
  | cons {a : T} {A : Cat} {w : List T} {Γ : List Cat}
      (head : (a, A) ∈ lexicon.entries)
      (tail : Categorizes lexicon w Γ) :
      Categorizes lexicon (a :: w) (A :: Γ)
```

Categorization preserves list length, an invariant used when excluding the
empty Lambek antecedent.

```lean
@[grind .] public theorem Categorizes.length_eq
    {lexicon : Lexicon T Cat} {w : List T} {Γ : List Cat}
    (h : lexicon.Categorizes w Γ) : w.length = Γ.length := by
  induction h <;> simp_all
```

```lean
end Lexicon
end Mathling.Lambek
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
