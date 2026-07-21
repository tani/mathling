    module

    import Mathling.Automata.Pushdown
    import Mathling.Automata.Regular.Finite
    import Mathling.Grammar.Regular.Regex
    import Mathling.Grammar.Regular.Linear
    import Mathling.Grammar.Deterministic

    import LiterateLean
    open scoped LiterateLean


# Mathling 回帰テストドライバ

有限局所規則の NPDA と、終状態受理から空スタック受理への正規化の最小回帰例を型検査する。
一回転機械の例は空語上で epsilon 遷移だけを使い、多記号 push、push/pop 両局面の
中立規則、局面切替、完全な pop を順に実行する。これにより正規化と Bridge 文法への
逆変換を同じ具体例で検査する。さらに有限 NFA の局所 NPDA 埋め込みと、正規表現から
正則・文脈自由言語への接続 API も型検査する。

```lean
namespace Mathling.Tests

```

```lean
open Mathling.Automata

```

```lean
def popRule : PushdownRule Unit Bool PUnit.{1} where
  source := false
  input := none
  pop := PUnit.unit
  target := true
  push := []

```

```lean
def popMachine : NPDA Unit Bool PUnit.{1} where
  rules := [popRule]
  start := [false]
  accept := [true]
  initialStack := [PUnit.unit]

```

```lean
@[grind .] theorem popMachine_accepts_empty : popMachine.Accepts [] := by
  refine ⟨false, by simp [popMachine], true, by simp [popMachine], [], ?_⟩
  apply Relation.ReflTransGen.single
  simpa [popMachine, popRule] using
    (NPDA.Step.epsilon (M := popMachine) popRule (by simp [popMachine]) rfl
      (input := []) (stack := []))

```

```lean
@[grind =] theorem finalToEmpty_regression :
    popMachine.finalToEmpty.language = popMachine.language :=
  NPDA.finalToEmpty_language popMachine

```

## 一回転正規化と Bridge 文法

次の機械は空語を受理するが、実行中に長さ 3 の push、push 局面の中立規則、局面切替、
pop 局面の中立規則をすべて通る。その後に三記号を除いて空スタックへ到達するため、
正規化の分割規則と Bridge 文法の四種類の規則を一つの回帰例で検査できる。

```lean
inductive OneTurnRegressionState where
  | start
  | grown
  | pushNeutral
  | switched
  | popNeutral
  | popMiddle
  | popLast
  | done
  deriving DecidableEq

```

```lean
open OneTurnRegressionState

```

```lean
def growRule : PushdownRule Unit (OneTurnRegressionState × TurnPhase) Bool :=
  { source := (.start, .push), input := none, pop := false,
    target := (.grown, .push), push := [true, false, true] }

```

```lean
def pushNeutralRule : PushdownRule Unit
    (OneTurnRegressionState × TurnPhase) Bool :=
  { source := (.grown, .push), input := none, pop := true,
    target := (.pushNeutral, .push), push := [true] }

```

```lean
def switchRule : PushdownRule Unit (OneTurnRegressionState × TurnPhase) Bool :=
  { source := (.pushNeutral, .push), input := none, pop := true,
    target := (.switched, .pop), push := [true] }

```

```lean
def popNeutralRule : PushdownRule Unit
    (OneTurnRegressionState × TurnPhase) Bool :=
  { source := (.switched, .pop), input := none, pop := true,
    target := (.popNeutral, .pop), push := [true] }

```

```lean
def popFirstRule : PushdownRule Unit (OneTurnRegressionState × TurnPhase) Bool :=
  { source := (.popNeutral, .pop), input := none, pop := true,
    target := (.popMiddle, .pop), push := [] }

```

```lean
def popMiddleRule : PushdownRule Unit (OneTurnRegressionState × TurnPhase) Bool :=
  { source := (.popMiddle, .pop), input := none, pop := false,
    target := (.popLast, .pop), push := [] }

```

```lean
def popLastRule : PushdownRule Unit (OneTurnRegressionState × TurnPhase) Bool :=
  { source := (.popLast, .pop), input := none, pop := true,
    target := (.done, .pop), push := [] }

```

```lean
def oneTurnRegressionMachine : OneTurnNPDA Unit OneTurnRegressionState Bool where
  rules := [growRule, pushNeutralRule, switchRule, popNeutralRule,
    popFirstRule, popMiddleRule, popLastRule]
  start := [.start]
  accept := [.done]
  initialStack := [false]
  pop_stays_pop := by
    intro r hr hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [growRule, pushNeutralRule, switchRule, popNeutralRule,
        popFirstRule, popMiddleRule, popLastRule]
  push_phase_nonshrinking := by
    intro r hr hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [growRule, pushNeutralRule, switchRule, popNeutralRule,
        popFirstRule, popMiddleRule, popLastRule]
  pop_phase_nongrowing := by
    intro r hr hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [growRule, pushNeutralRule, switchRule, popNeutralRule,
        popFirstRule, popMiddleRule, popLastRule]

private theorem regressionEpsilonStep
    (r : PushdownRule Unit (OneTurnRegressionState × TurnPhase) Bool)
    (hr : r ∈ oneTurnRegressionMachine.rules) (hinput : r.input = none)
    (tail : List Bool) :
    oneTurnRegressionMachine.Step
      ([], r.source, r.pop :: tail) ([], r.target, r.push ++ tail) := by
  change oneTurnRegressionMachine.toNPDA.Step
    ([], r.source, r.pop :: tail) ([], r.target, r.push ++ tail)
  apply NPDA.Step.epsilon r
  · change r ∈ oneTurnRegressionMachine.rules
    exact hr
  · exact hinput

```

```lean
@[grind .] theorem oneTurnRegressionMachine_accepts_empty :
    oneTurnRegressionMachine.Accepts [] := by
  refine ⟨(.start, .push), ?_, (.done, .pop), ?_, [], ?_⟩
  · change (OneTurnRegressionState.start, TurnPhase.push) ∈
      [(OneTurnRegressionState.start, TurnPhase.push)]
    simp
  · change (OneTurnRegressionState.done, TurnPhase.pop) ∈
      [(OneTurnRegressionState.done, TurnPhase.push),
        (OneTurnRegressionState.done, TurnPhase.pop)]
    simp
  have hGrow := Relation.ReflTransGen.single
    (regressionEpsilonStep growRule
      (by simp [oneTurnRegressionMachine]) rfl [])
  have hPushNeutral := Relation.ReflTransGen.single
    (regressionEpsilonStep pushNeutralRule
      (by simp [oneTurnRegressionMachine]) rfl [false, true])
  have hSwitch := Relation.ReflTransGen.single
    (regressionEpsilonStep switchRule
      (by simp [oneTurnRegressionMachine]) rfl [false, true])
  have hPopNeutral := Relation.ReflTransGen.single
    (regressionEpsilonStep popNeutralRule
      (by simp [oneTurnRegressionMachine]) rfl [false, true])
  have hPopFirst := Relation.ReflTransGen.single
    (regressionEpsilonStep popFirstRule
      (by simp [oneTurnRegressionMachine]) rfl [false, true])
  have hPopMiddle := Relation.ReflTransGen.single
    (regressionEpsilonStep popMiddleRule
      (by simp [oneTurnRegressionMachine]) rfl [true])
  have hPopLast := Relation.ReflTransGen.single
    (regressionEpsilonStep popLastRule
      (by simp [oneTurnRegressionMachine]) rfl [])
  change oneTurnRegressionMachine.Reaches
    ([], (.start, .push), [false]) ([], (.done, .pop), [])
  simpa [growRule, pushNeutralRule, switchRule, popNeutralRule,
    popFirstRule, popMiddleRule, popLastRule] using
      ((((((hGrow.trans hPushNeutral).trans hSwitch).trans hPopNeutral).trans
        hPopFirst).trans hPopMiddle).trans hPopLast)

```

```lean
@[grind =] theorem oneTurn_normalize_regression :
    oneTurnRegressionMachine.normalize.language =
      oneTurnRegressionMachine.language :=
  oneTurnRegressionMachine.normalize_language

```

```lean
@[grind =] theorem oneTurn_toLinearGrammar_regression :
    oneTurnRegressionMachine.toLinearGrammar.language =
      oneTurnRegressionMachine.language :=
  oneTurnRegressionMachine.toLinearGrammar_language

```

```lean
@[grind .] theorem oneTurn_language_isLinear_regression :
    oneTurnRegressionMachine.language.IsLinear :=
  oneTurnRegressionMachine.language_isLinear

```

## 有限オートマトンと正規表現の接続

残りの例は有限 NFA の pushdown 埋め込み、epsilon-NFA、正規表現への変換、および
正則言語から決定性文脈自由言語への包含を型検査する。

```lean
def singletonNFA : Mathling.Automata.NFA Bool Bool where
  step q a := if q = false ∧ a = true then {true} else ∅
  start := {false}
  accept := {true}

```

```lean
@[grind =] theorem finiteNFA_toNPDA_regression :
  singletonNFA.toNPDA.language = singletonNFA.accepts :=
  Mathling.Automata.NFA.toNPDA_language singletonNFA

```

```lean
@[grind =] theorem finiteNFA_toεNFA_regression :
    singletonNFA.toεNFA.accepts = singletonNFA.accepts :=
  Mathling.Automata.NFA.toεNFA_language singletonNFA

```

```lean
@[grind .] theorem regular_dcfl_regression :
    singletonNFA.accepts.IsDeterministicContextFree := by
  exact (Language.isRegular_iff_nfa.mpr
    ⟨Bool, inferInstance, singletonNFA, rfl⟩).isDeterministicContextFree

```

```lean
@[grind .] theorem regular_dcfl_is_cfl_regression :
    singletonNFA.accepts.IsContextFree :=
  regular_dcfl_regression.isContextFree

```

```lean
@[grind =] theorem finiteNFA_toRegex_regression :
    Mathling.Automata.RegularExpression.language singletonNFA.toRegex =
      singletonNFA.accepts :=
  Mathling.Automata.NFA.toRegex_language singletonNFA

```

```lean
@[grind .] theorem regex_hierarchy_regression :
    Language.HasRegularExpression
      (Mathling.Automata.RegularExpression.language
        (Mathling.Automata.RegularExpression.symbol true)) := by
  exact ⟨Mathling.Automata.RegularExpression.symbol true, rfl⟩

```

```lean
@[grind .] theorem regex_contextFree_regression :
    (Mathling.Automata.RegularExpression.language
      (Mathling.Automata.RegularExpression.symbol true)).IsContextFree :=
  regex_hierarchy_regression.isContextFree

```

```lean
@[grind =] theorem regex_compileNFA_regression :
    (Mathling.Automata.RegularExpression.compileNFA
      (Mathling.Automata.RegularExpression.symbol true)).machine.accepts =
      Mathling.Automata.RegularExpression.language
        (Mathling.Automata.RegularExpression.symbol true) :=
  Mathling.Automata.RegularExpression.compileNFA_language _

```

```lean
@[grind =] theorem kleene_equivalence_regression :
    (Mathling.Automata.RegularExpression.language
      (Mathling.Automata.RegularExpression.symbol true)).IsRegular ↔
      Language.HasRegularExpression
        (Mathling.Automata.RegularExpression.language
          (Mathling.Automata.RegularExpression.symbol true)) :=
  Language.isRegular_iff_hasRegularExpression

```

```lean
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
