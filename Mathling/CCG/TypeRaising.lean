import Mathling.CCG.Basic

namespace TypeRaising

inductive Derives
  {g : CategorialGrammar α σ}
  : List σ → Category α → Prop
| lexicon (term : σ) :
  g.lexicon term x →
  Derives [term] x
| forwardApp :
  Derives β₁ (x / y) →
  Derives β₂ y →
  Derives (β₁ ++ β₂) x
| backwardApp :
  Derives β₁ y →
  Derives β₂ (x \ y) →
  Derives (β₁ ++ β₂) x
| forwardTypeRaise :
  Derives β x →
  Derives β (y / (y \ x))
| backwardTypeRaise :
  Derives β x →
  Derives β (y \ (y / x))

infixl:65 " :: " => Derives

end TypeRaising

