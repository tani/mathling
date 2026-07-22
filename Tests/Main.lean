    module

    import Mathling.Automata.Pushdown
    import Mathling.Automata.Regular.Finite
    import Mathling.Grammar.Regular.Regex
    import Mathling.Grammar.Regular.Linear
    import Mathling.Grammar.Deterministic
    import Mathling.Lambek.ProductFree.Fragments.Language

    import LiterateLean
    open scoped LiterateLean


# Mathling 回帰テストドライバ

有限局所規則の NPDA と、終状態受理から空スタック受理への正規化の最小回帰例を型検査する。
一回転機械の例は空語上で epsilon 遷移だけを使い、多記号 push、push/pop 両局面の
中立規則、局面切替、完全な pop を順に実行する。これにより正規化と Bridge 文法への
逆変換を同じ具体例で検査する。さらに有限 NFA の局所 NPDA 埋め込みと、正規表現から
正則・文脈自由言語への接続 API も型検査する。

以下のテスト本体はすべて `Mathling.Tests` 名前空間に閉じ込める。名前空間を開き忘れると
以降の補助定義が意図せずグローバル名前空間に漏れ、他モジュールとの命名衝突を検出できなくなる。

```lean
namespace Mathling.Tests

```

`Mathling.Automata` を開いておくことで、以下の `NPDA` / `PushdownRule` 等の型を完全修飾なしで
参照できる。この `open` が欠けると各定義の型注釈がすべて壊れ、どの回帰例が失敗しているのか
分からなくなる。

```lean
open Mathling.Automata

```

`popMachine` が使う唯一の規則。空記号列上で pop だけを行う最小の NPDA 遷移規則であり、
push を一切伴わない最短の受理経路を作るための土台になる。この規則の `pop`/`push` フィールドの
向きを取り違えると、次に定義する空語受理の証明がそもそも成り立たなくなる。

```lean
def popRule : PushdownRule Unit Bool PUnit.{1} where
  source := false
  input := none
  pop := PUnit.unit
  target := true
  push := []

```

`popRule` だけを規則集合として持つ NPDA。「初期スタックを一度 pop するだけで受理状態に
到達する」という NPDA の最小骨格を固定する回帰対象であり、この機械の定義が壊れると
以降の空語受理性と `finalToEmpty` 正規化の両方の検査が意味を失う。

```lean
def popMachine : NPDA Unit Bool PUnit.{1} where
  rules := [popRule]
  start := [false]
  accept := [true]
  initialStack := [PUnit.unit]

```

`popMachine` が空語 `[]` を実際に受理することを一段の epsilon 遷移だけで証明する、
最も単純な受理性回帰。この定理が失敗するなら `NPDA.Step.epsilon` の基本的な適用条件
そのものが壊れている可能性が高い。

```lean
@[grind .] theorem popMachine_accepts_empty : popMachine.Accepts [] := by
  refine ⟨false, by simp [popMachine], true, by simp [popMachine], [], ?_⟩
  apply Relation.ReflTransGen.single
  simpa [popMachine, popRule] using
    (NPDA.Step.epsilon (M := popMachine) popRule (by simp [popMachine]) rfl
      (input := []) (stack := []))

```

`popMachine` が空語 `[]` を受理することを直接検査する。この定理がなければ、後段の
`finalToEmpty_regression` は「等しい2つの空言語」を比較しているだけになり、
正規化前後で言語が保存されているという主張の実質的な内容が失われる。

```lean
@[grind =] theorem finalToEmpty_regression :
    popMachine.finalToEmpty.language = popMachine.language :=
  NPDA.finalToEmpty_language popMachine

```

終状態受理から空スタック受理への変換 (`finalToEmpty`) が言語を変えないことを、
実際に非自明な言語を持つ具体例で検査する。この等式が崩れると、変換 API が
サイレントに言語を変えてしまうリグレッションを検出できなくなる。

## 一回転正規化と Bridge 文法

次の機械は空語を受理するが、実行中に長さ 3 の push、push 局面の中立規則、局面切替、
pop 局面の中立規則をすべて通る。その後に三記号を除いて空スタックへ到達するため、
正規化の分割規則と Bridge 文法の四種類の規則を一つの回帰例で検査できる。

この列挙は「一回転」機械が通過すべき八段階の局面 (`start` → … → `done`) を名前付きで
固定する。段階名を減らしたり順序を変えたりすると、以下の各規則が参照する `source`/`target`
がずれ、経路全体の意図が読み取れなくなる。

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

コンストラクタ名を修飾なしで書けるようにする。これがないと以下の規則定義がすべて
`OneTurnRegressionState.start` のような完全修飾名を要求し、可読性のリグレッションになる。

```lean
open OneTurnRegressionState

```

長さ3の push を行う最初の遷移規則。`push` 局面で一度に複数記号を積む経路を検査対象に
含めるためのもので、この規則を削ると「多記号 push」のカバレッジが失われる。

```lean
def growRule : PushdownRule Unit (OneTurnRegressionState × TurnPhase) Bool :=
  { source := (.start, .push), input := none, pop := false,
    target := (.grown, .push), push := [true, false, true] }

```

push 局面のまま pop と push を同時に行う「中立」規則。push 局面中に pop が起きても
局面のフェーズ分類が崩れないことを検査するためのもので、これがないと push 局面での
中立遷移のカバレッジが失われる。

```lean
def pushNeutralRule : PushdownRule Unit
    (OneTurnRegressionState × TurnPhase) Bool :=
  { source := (.grown, .push), input := none, pop := true,
    target := (.pushNeutral, .push), push := [true] }

```

push 局面から pop 局面への切り替えを行う唯一の規則。一回転機械の定義上、push から pop へは
一度しか切り替わってはならないという不変条件をこの規則が体現しており、これを欠くと
`OneTurnNPDA` の局面切替そのものを検査できなくなる。

```lean
def switchRule : PushdownRule Unit (OneTurnRegressionState × TurnPhase) Bool :=
  { source := (.pushNeutral, .push), input := none, pop := true,
    target := (.switched, .pop), push := [true] }

```

pop 局面でも同様に pop と push を同時に行う中立規則。push 局面の中立規則と対になっており、
pop 局面での中立遷移が正しく「非成長」として扱われることを検査する。

```lean
def popNeutralRule : PushdownRule Unit
    (OneTurnRegressionState × TurnPhase) Bool :=
  { source := (.switched, .pop), input := none, pop := true,
    target := (.popNeutral, .pop), push := [true] }

```

pop 局面で純粋な pop（push なし）を初めて行う規則。ここから `oneTurnRegressionMachine` は
スタックを縮め始め、`pop_phase_nongrowing` の証明義務が実質的に効いてくる区間に入る。

```lean
def popFirstRule : PushdownRule Unit (OneTurnRegressionState × TurnPhase) Bool :=
  { source := (.popNeutral, .pop), input := none, pop := true,
    target := (.popMiddle, .pop), push := [] }

```

pop 局面の中間段階。連続する pop 遷移が途中で壊れないことを検査するための一段であり、
これを省くと popFirst から popLast への遷移列が短くなりすぎて回帰の意味が薄れる。

```lean
def popMiddleRule : PushdownRule Unit (OneTurnRegressionState × TurnPhase) Bool :=
  { source := (.popMiddle, .pop), input := none, pop := false,
    target := (.popLast, .pop), push := [] }

```

最後の pop 規則で、これを実行すると受理局面 `done` に到達し、スタックは完全に空になる。
この規則を欠くと機械は決して空スタックで受理状態に達せず、以降の空語受理性の証明が
成り立たなくなる。

```lean
def popLastRule : PushdownRule Unit (OneTurnRegressionState × TurnPhase) Bool :=
  { source := (.popLast, .pop), input := none, pop := true,
    target := (.done, .pop), push := [] }

```

七つの規則を束ね、`OneTurnNPDA` の三つの構造的不変条件（pop 局面は pop のままである、
push 局面はスタックを縮めない、pop 局面はスタックを伸ばさない）を証明として満たす機械を
組み立てる。これら三つの `by` ブロックのいずれかが崩れると、一回転正規化アルゴリズムが
前提とする不変条件そのものが機械から失われ、正規化の健全性が保証できなくなる。

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
```

各規則がすべて空記号 (`input = none`) 上の遷移であることを利用して、規則の適用を
`NPDA.Step.epsilon` の具体的なインスタンスへ変換する補助補題。これがないと以下の
空語受理の証明で毎回同じ epsilon-step の組み立てを手書きする必要があり、規則構造が
変わった際にどこが壊れたか追跡しづらくなる。

```lean
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

七つの規則すべてを一つずつ連鎖させて空語受理を証明する、ファイル冒頭の要約が約束する
「多記号 push、push/pop 両局面の中立規則、局面切替、完全な pop」を一本の実行系列として
実際にたどる回帰例。途中の `have` のどれか一つでも規則の並びとずれると、遷移列全体が
`Reaches` として繋がらなくなり証明が失敗するため、規則追加・削除時の配線ミスを検出できる。

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

一回転機械の正規化 (`normalize`) が、push/pop 両局面の中立規則と局面切替を含む
非自明な機械についても言語を保存することを検査する。分割規則の実装に不具合があると
正規化後の言語がずれ、この等式が最初に壊れる箇所になる。

```lean
@[grind =] theorem oneTurn_normalize_regression :
    oneTurnRegressionMachine.normalize.language =
      oneTurnRegressionMachine.language :=
  oneTurnRegressionMachine.normalize_language

```

一回転機械から Bridge 文法（線形文法）への逆変換が言語を保存することを検査する。
四種類の規則（push、中立×2、切替、pop）をすべて含む機械で検査しているため、
Bridge 文法側のいずれかの規則生成が欠落・誤変換された場合にこの等式が崩れる。

```lean
@[grind =] theorem oneTurn_toLinearGrammar_regression :
    oneTurnRegressionMachine.toLinearGrammar.language =
      oneTurnRegressionMachine.language :=
  oneTurnRegressionMachine.toLinearGrammar_language

```

一回転機械の言語が線形文法で生成可能であること（`IsLinear`）を検査する。この性質は
一回転 NPDA から Bridge 文法への変換が文法階層上どこに位置づけられるかという主張の
根拠になっており、崩れると言語階層の分類自体が誤りになる。

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

`false` から `true` への単一記号 `true` の遷移のみを持つ最小の NFA。以下の一連の
接続 API（pushdown 埋め込み、ε-NFA 変換、正規表現変換、階層関係）をすべて共通の
非自明な具体例で検査するための基準点であり、これが空言語や恒等関数に縮退すると
以降の等式の多くが自明になって検査力を失う。

```lean
@[grind =] theorem finiteNFA_toNPDA_regression :
  singletonNFA.toNPDA.language = singletonNFA.accepts :=
  Mathling.Automata.NFA.toNPDA_language singletonNFA

```

有限 NFA を局所 NPDA として埋め込む変換 (`toNPDA`) が受理言語を保存することを検査する。
この等式が崩れると、正則言語をより一般的な pushdown 系の枠組みで扱う際に言語がサイレントに
変わってしまう。

```lean
@[grind =] theorem finiteNFA_toεNFA_regression :
    singletonNFA.toεNFA.accepts = singletonNFA.accepts :=
  Mathling.Automata.NFA.toεNFA_language singletonNFA

```

NFA から ε-NFA への変換が受理言語を保存することを検査する。ε 遷移を許す表現へ
一般化しても言語が変わらないという契約であり、崩れると ε-NFA を経由する後続処理
（正規表現変換など）の正しさの前提が失われる。

```lean
@[grind .] theorem regular_dcfl_regression :
    singletonNFA.accepts.IsDeterministicContextFree := by
  exact (Language.isRegular_iff_nfa.mpr
    ⟨Bool, inferInstance, singletonNFA, rfl⟩).isDeterministicContextFree

```

正則言語が決定性文脈自由言語であるという言語階層上の包含関係を、具体的な NFA 受理言語
について検査する。`isRegular_iff_nfa` と `isDeterministicContextFree` の橋渡しが
壊れると、正則から DCFL への自動的な格上げが効かなくなる。

```lean
@[grind .] theorem regular_dcfl_is_cfl_regression :
    singletonNFA.accepts.IsContextFree :=
  regular_dcfl_regression.isContextFree

```

決定性文脈自由言語がさらに文脈自由言語でもあるという、階層のもう一段上への包含を検査する。
前の定理からの単純な帰結だが、`isContextFree` の変換自体が壊れていないかを直接確認する
最後の砦になっている。

```lean
@[grind =] theorem finiteNFA_toRegex_regression :
    Mathling.Automata.RegularExpression.language singletonNFA.toRegex =
      singletonNFA.accepts :=
  Mathling.Automata.NFA.toRegex_language singletonNFA

```

NFA から正規表現への変換 (`toRegex`) が受理言語を保存することを検査する。この等式が
崩れると、オートマトン側と正規表現側という同じ正則言語の二つの表現が食い違ってしまい、
以降の Kleene 同値性の主張全体の土台が崩れる。

```lean
@[grind .] theorem regex_hierarchy_regression :
    Language.HasRegularExpression
      (Mathling.Automata.RegularExpression.language
        (Mathling.Automata.RegularExpression.symbol true)) := by
  exact ⟨Mathling.Automata.RegularExpression.symbol true, rfl⟩

```

正規表現の言語が文脈自由言語でもあるという、正規表現側からの階層包含を検査する。
`toRegex`/`compileNFA` を経由する変換群がすべて同じ言語階層の中で整合していることの
確認であり、この定理が崩れると正規表現由来の言語が CFG の枠組みで扱えなくなる。

```lean
@[grind .] theorem regex_contextFree_regression :
    (Mathling.Automata.RegularExpression.language
      (Mathling.Automata.RegularExpression.symbol true)).IsContextFree :=
  regex_hierarchy_regression.isContextFree

```

正規表現から NFA へのコンパイル (`compileNFA`) が、コンパイル前の正規表現の意味論と
一致する言語を受理することを検査する。Kleene の定理の一方向（正規表現 → オートマトン）
の実装が正しいことの直接的な証拠であり、崩れるとコンパイル結果が元の正規表現と
異なる言語を受理してしまう。

```lean
@[grind =] theorem regex_compileNFA_regression :
    (Mathling.Automata.RegularExpression.compileNFA
      (Mathling.Automata.RegularExpression.symbol true)).machine.accepts =
      Mathling.Automata.RegularExpression.language
        (Mathling.Automata.RegularExpression.symbol true) :=
  Mathling.Automata.RegularExpression.compileNFA_language _

```

Kleene の定理そのもの、すなわち「正則である」ことと「正規表現で表現できる」ことの
同値性を検査する最終的な回帰例。ここまでの `toNPDA`/`toεNFA`/`toRegex`/`compileNFA`
の各変換がすべて正しく噛み合っていなければこの同値が成立しないため、接続 API 全体の
一貫性を束ねて確認する役割を持つ。

```lean
@[grind =] theorem kleene_equivalence_regression :
    (Mathling.Automata.RegularExpression.language
      (Mathling.Automata.RegularExpression.symbol true)).IsRegular ↔
      Language.HasRegularExpression
        (Mathling.Automata.RegularExpression.language
          (Mathling.Automata.RegularExpression.symbol true)) :=
  Language.isRegular_iff_hasRegularExpression

```

ここまでの回帰定理はすべて型検査が通ること自体が検査内容であり、実行時に副作用を
起こす必要はない。`run` はテスト実行器が「コンパイルが成功した」ことを目視確認できるよう
一行のメッセージを出力するだけの最小限のエントリポイントである。

```lean
def run : IO Unit :=
  IO.println "Mathling regression proofs compiled successfully."

end Mathling.Tests
```

Lake の実行可能ターゲットが期待する `main : IO Unit` を、テスト名前空間内の `run` へ
委譲する薄いブリッジ。この定義が欠けるかシグネチャが合わないと、`lake test` が
実行可能ファイルとしてこのモジュールを起動できなくなる。

```lean
public def main : IO Unit := Mathling.Tests.run
```

## Shallow Lambek 語彙文法

この回帰テストは、語彙受理、三つの具体的な順方向変換、および各変換の言語保存定理が
公開 API としてテストターゲットから利用できることを固定する。

\`\`\`lean
namespace Mathling.Tests

example (g : Mathling.Lambek.ProductFree.Shallow.Grammar Unit) :
    [] ∉ g.language :=
  g.empty_not_mem

noncomputable example (g : Mathling.Lambek.ProductFree.Shallow.Grammar Unit) :
    Mathling.Grammar.LinearGrammar Unit :=
  g.toLinearGrammar

noncomputable example (g : Mathling.Lambek.ProductFree.Left.Shallow.Grammar Unit) :
    Mathling.Grammar.LeftLinearGrammar Unit :=
  g.toLeftLinearGrammar

noncomputable example (g : Mathling.Lambek.ProductFree.Right.Shallow.Grammar Unit) :
    Mathling.Grammar.RightLinearGrammar Unit :=
  g.toRightLinearGrammar

noncomputable example (g : Mathling.Lambek.ProductFree.Shallow.Grammar Unit) :
    g.toLinearGrammar.language = g.language :=
  g.toLinearGrammar_language

noncomputable example (g : Mathling.Lambek.ProductFree.Left.Shallow.Grammar Unit) :
    g.toLeftLinearGrammar.language = g.language :=
  g.toLeftLinearGrammar_language

noncomputable example (g : Mathling.Lambek.ProductFree.Right.Shallow.Grammar Unit) :
    g.toRightLinearGrammar.language = g.language :=
  g.toRightLinearGrammar_language

example (g : Mathling.Lambek.ProductFree.Shallow.Grammar Unit) :
    g.language.IsLinear :=
  g.language_isLinear

example (g : Mathling.Lambek.ProductFree.Left.Shallow.Grammar Unit) :
    g.language.IsRegular :=
  g.language_isRegular

example (g : Mathling.Lambek.ProductFree.Right.Shallow.Grammar Unit) :
    g.language.IsRegular :=
  g.language_isRegular

end Mathling.Tests
\`\`\`
<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
