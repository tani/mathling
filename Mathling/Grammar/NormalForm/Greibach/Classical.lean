module

public import Mathling.Grammar.NormalForm.Greibach.Conversion

@[expose] public section

namespace Mathling.Grammar
namespace ContextFreeGrammar
namespace Classical

/-- Convert a context-free grammar over a small terminal type to Greibach normal
form, choosing classical orders. Use `ContextFreeGrammar.toGreibachNormalGrammar`
when executable code is required. -/
noncomputable def toGreibachNormalGrammar {T : Type}
    (g : ContextFreeGrammar T) : GreibachNormalGrammar T := by
  classical
  letI : LinearOrder T := linearOrderOfSTO WellOrderingRel
  letI : LinearOrder g.NT := linearOrderOfSTO WellOrderingRel
  exact _root_.Mathling.Grammar.ContextFreeGrammar.toGreibachNormalGrammar g

@[simp] theorem toGreibachNormalGrammar_language {T : Type}
    (g : ContextFreeGrammar T) :
    (Classical.toGreibachNormalGrammar g).language = g.language := by
  classical
  simp [Classical.toGreibachNormalGrammar,
    _root_.Mathling.Grammar.ContextFreeGrammar.toGreibachNormalGrammar_language]

end Classical
end ContextFreeGrammar
end Mathling.Grammar
