    module

    import Mathling.Automata.Pushdown
    import Mathling.Automata.Regular.Finite
    import Mathling.Grammar.Regular.Regex

    import LiterateLean
    open scoped LiterateLean


# Mathling 回帰テストドライバ

有限局所規則の NPDA と、終状態受理から空スタック受理への正規化の最小回帰例を型検査する。マシンは epsilon 遷移で1つのスタック記号を取り除き、非受理状態から受理状態へ移る。さらに有限 NFA の局所 NPDA 埋め込みと、正規表現から正則・文脈自由言語への接続 API も型検査する。

```lean
namespace Mathling.Tests

open Mathling.Automata

def popRule : PushdownRule Unit Bool PUnit.{1} where
  source := false
  input := none
  pop := PUnit.unit
  target := true
  push := []

def popMachine : NPDA Unit Bool PUnit.{1} where
  rules := [popRule]
  start := [false]
  accept := [true]
  initialStack := [PUnit.unit]

@[grind .] theorem popMachine_accepts_empty : popMachine.Accepts [] := by
  refine ⟨false, by simp [popMachine], true, by simp [popMachine], [], ?_⟩
  apply Relation.ReflTransGen.single
  simpa [popMachine, popRule] using
    (NPDA.Step.epsilon (M := popMachine) popRule (by simp [popMachine]) rfl
      (input := []) (stack := []))

@[grind =] theorem finalToEmpty_regression :
    popMachine.finalToEmpty.language = popMachine.language :=
  NPDA.finalToEmpty_language popMachine

def singletonNFA : Mathling.Automata.NFA Bool Bool where
  step q a := if q = false ∧ a = true then {true} else ∅
  start := {false}
  accept := {true}

@[grind =] theorem finiteNFA_toNPDA_regression :
  singletonNFA.toNPDA.language = singletonNFA.accepts :=
  Mathling.Automata.NFA.toNPDA_language singletonNFA

@[grind =] theorem finiteNFA_toRegex_regression :
    Mathling.Automata.RegularExpression.language singletonNFA.toRegex =
      singletonNFA.accepts :=
  Mathling.Automata.NFA.toRegex_language singletonNFA

@[grind .] theorem regex_hierarchy_regression :
    Language.HasRegularExpression
      (Mathling.Automata.RegularExpression.language
        (Mathling.Automata.RegularExpression.symbol true)) := by
  exact ⟨Mathling.Automata.RegularExpression.symbol true, rfl⟩

@[grind .] theorem regex_contextFree_regression :
    (Mathling.Automata.RegularExpression.language
      (Mathling.Automata.RegularExpression.symbol true)).IsContextFree :=
  regex_hierarchy_regression.isContextFree

@[grind =] theorem regex_compileNFA_regression :
    (Mathling.Automata.RegularExpression.compileNFA
      (Mathling.Automata.RegularExpression.symbol true)).machine.accepts =
      Mathling.Automata.RegularExpression.language
        (Mathling.Automata.RegularExpression.symbol true) :=
  Mathling.Automata.RegularExpression.compileNFA_language _

@[grind =] theorem kleene_equivalence_regression :
    (Mathling.Automata.RegularExpression.language
      (Mathling.Automata.RegularExpression.symbol true)).IsRegular ↔
      Language.HasRegularExpression
        (Mathling.Automata.RegularExpression.language
          (Mathling.Automata.RegularExpression.symbol true)) :=
  Language.isRegular_iff_hasRegularExpression

def run : IO Unit :=
  IO.println "Mathling regression proofs compiled successfully."

end Mathling.Tests

public def main : IO Unit := Mathling.Tests.run
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
