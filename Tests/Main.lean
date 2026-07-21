    module

    import Mathling.Automata.Pushdown

    import LiterateLean
    open scoped LiterateLean


# Mathling 回帰テストドライバ

有限局所規則の NPDA と、終状態受理から空スタック受理への正規化の最小回帰例を型検査する。マシンは epsilon 遷移で1つのスタック記号を取り除き、非受理状態から受理状態へ移る。これにより、局所遷移の実行と `finalToEmpty` の言語保存 API の両方を検査する。

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
