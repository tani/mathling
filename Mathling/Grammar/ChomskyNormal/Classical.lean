module

public import Mathling.Grammar.ChomskyNormal

@[expose] public section

namespace Mathling.Grammar
namespace ContextFreeGrammar
namespace Classical

/-- Convert an arbitrary context-free grammar to Chomsky normal form, choosing
classical orders.  Use `ContextFreeGrammar.toChomskyNormalGrammar` when executable
code is required. -/
noncomputable def toChomskyNormalGrammar {T : Type*}
    (g : ContextFreeGrammar T) : ChomskyNormalGrammar T := by
  classical
  letI : LinearOrder T := linearOrderOfSTO WellOrderingRel
  letI : LinearOrder g.NT := linearOrderOfSTO WellOrderingRel
  exact _root_.Mathling.Grammar.ContextFreeGrammar.toChomskyNormalGrammar g

@[simp] theorem toChomskyNormalGrammar_language {T : Type*}
    (g : ContextFreeGrammar T) :
    (Classical.toChomskyNormalGrammar g).language = g.language := by
  classical
  simp [Classical.toChomskyNormalGrammar,
    _root_.Mathling.Grammar.ContextFreeGrammar.toChomskyNormalGrammar_language]

end Classical
end ContextFreeGrammar
end Mathling.Grammar
