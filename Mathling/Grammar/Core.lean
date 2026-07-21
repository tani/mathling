    module

    public import Mathlib.Computability.ContextFreeGrammar

    import LiterateLean
    open scoped LiterateLean


# Mathling / Grammar / Core モジュール

文脈自由文法で共有する記号操作と規則形状を定義し、線形・左右線形・Chomsky・Greibach の各文法を証拠付き構造として束ねる。後続の変換はここで定める形状述語を出力不変条件として用いる。

`Mathling.Grammar` 名前空間は、以降のすべての文法変換モジュールが共有する語彙の置き場である。`terminalSymbols` はここで最初に定義される基礎操作で、生の終端記号列を文脈自由文法の文形（`Symbol T N` のリスト）へ持ち上げる。これがなければ、各変換パイプラインの入出力ごとに終端埋め込みを書き直すことになり、埋め込みの一貫性を検証する箇所も分散してしまう。

```lean

/-!
# Grammar hierarchy

Shared context-free grammar utilities, rule-shape predicates, and bundles for
linear, right-linear, left-linear, Chomsky-normal, and Greibach-normal grammars.
-/



namespace Mathling.Grammar

/-- Embed a terminal word into a context-free sentential form. -/
public abbrev terminalSymbols {T N : Type*} (w : List T) : List (Symbol T N) :=
  w.map Symbol.terminal

```

`terminalSymbols` を空リストに適用したときの正規化補題。`grind` と `simp` に登録することで、後続の証明が `terminalSymbols` の適用結果を自動的に `[]` へ畳み込めるようにし、境界ケースを個別に場合分けする手間を消す。

```lean
@[grind =, simp] public theorem terminalSymbols_nil {T N : Type*} :
    terminalSymbols (T := T) (N := N) [] = [] := rfl

```

`terminalSymbols` の余帰納的な展開規則。単語の先頭要素を埋め込みリストの先頭に押し出すことで、単語に関する帰納法の各ステップで `terminalSymbols` を書き換え可能にし、導出変換の証明で単語を１文字ずつ処理する際の要となる。

```lean
@[grind =, simp] public theorem terminalSymbols_cons {T N : Type*} (a : T) (w : List T) :
    terminalSymbols (N := N) (a :: w) =
      Symbol.terminal a :: terminalSymbols w := rfl
```

文法変換（例えば Chomsky 標準形化や自動機との相互変換）は、非終端記号の集合をしばしば作り替えた別の型へ写す必要がある。`Symbol.mapNonterminal` はその写像を記号レベルで与える単一の関手的操作であり、終端記号は不変に保ったまま非終端記号だけを `f` で送る。本体を `@[expose]` で公開しているのは、変換の正しさを示す公開補題群がこの写像を書き換えて簡約する必要があるためである。

```lean
/-- Rename the nonterminal carried by a symbol, preserving terminals.

Its body is exposed because public rewrite-preservation theorems reduce this
mapping while transporting derivations across grammar conversions. -/


@[expose] public def Symbol.mapNonterminal {T N M : Type*} (f : N → M) :
    Symbol T N → Symbol T M
  | .terminal a => .terminal a
  | .nonterminal A => .nonterminal (f A)
```

`mapNonterminal` を終端記号に適用しても記号は変化しないという不変条件。これにより「非終端記号のリネームは終端記号列に影響しない」という文法変換の基本契約を、場合分けなしに書き換えとして使える。

```lean
@[grind =, simp] public theorem Symbol.mapNonterminal_terminal {T N M : Type*}
    (f : N → M) (a : T) :
    Symbol.mapNonterminal f (.terminal a) = .terminal a := rfl

```

`mapNonterminal` を非終端記号に適用した場合の展開規則。非終端記号の写像が `f` の適用そのものに簡約されることを保証し、非終端集合の付け替えを追跡する後続証明の要となる。

```lean
@[grind =, simp] public theorem Symbol.mapNonterminal_nonterminal {T N M : Type*}
    (f : N → M) (A : N) :
    Symbol.mapNonterminal f (.nonterminal A : Symbol T N) =
      (.nonterminal (f A) : Symbol T M) := rfl
```

記号レベルの `Symbol.mapNonterminal` を規則全体（入力の非終端記号と出力の文形の両方）に持ち上げたのが `ContextFreeRule.mapNonterminal` である。文法全体を新しい非終端集合へ移す変換は、規則集合をこの操作で一斉に写すことに帰着するため、これがなければ各変換がフィールドごとに手作業で書き換える必要が生じる。本体を公開しているのは、変換の健全性証明がこの写像を展開して規則の入出力を直接分析するためである。

```lean
/-- Rename every nonterminal in a context-free rule.

Its body is exposed because public conversion proofs simplify the mapped rule
to construct and analyse transported rewrites. -/


@[expose] public def ContextFreeRule.mapNonterminal {T N M : Type*} (f : N → M)
    (r : ContextFreeRule T N) : ContextFreeRule T M :=
  { input := f r.input, output := r.output.map (Symbol.mapNonterminal f) }
```

写された規則の入力フィールドが `f` を単純適用した結果と一致するという射影補題。規則の左辺（生成される非終端記号）が写像と可換であることを保証し、初期記号の追跡など、規則の入力側だけを見る証明で使われる。

```lean
@[grind =, simp] public theorem ContextFreeRule.mapNonterminal_input {T N M : Type*}
    (f : N → M) (r : ContextFreeRule T N) :
    (ContextFreeRule.mapNonterminal f r).input = f r.input := rfl

```

対応する出力側の射影補題。規則の右辺（文形）の写像が、各記号への `Symbol.mapNonterminal` の要素ごとの適用に一致することを示し、規則形状述語（線形性・Chomsky 形など）が写像後も保存されることを示す証明の橋渡しをする。

```lean
@[grind =, simp] public theorem ContextFreeRule.mapNonterminal_output {T N M : Type*}
    (f : N → M) (r : ContextFreeRule T N) :
    (ContextFreeRule.mapNonterminal f r).output =
      r.output.map (Symbol.mapNonterminal f) := rfl
```

後続の規則形状述語（線形性・Chomsky/Greibach 形など）はすべて「出力中の何個の位置が非終端記号か」を数えたり判定したりする必要がある。`Symbol.IsNonterminal` はその判定を命題として与える最小単位であり、これがなければ各述語が `Symbol` のコンストラクタで直接場合分けを繰り返すことになる。本体を公開しているのは、コンストラクタ等式による自動簡約を公開補題群で使うためである。

```lean
/-- Whether a symbol is structurally a nonterminal.

Its body is exposed because the public constructor equations reduce it. -/


@[expose] public def Symbol.IsNonterminal {T N : Type*} : Symbol T N → Prop
  | .terminal _ => False
  | .nonterminal _ => True
```

終端記号は非終端ではないという境界ケースの正規化。`IsNonterminal` を含む述語を終端記号に適用した式を `False` へ自動的に畳み込み、以後の証明で終端記号の場合を即座に排除できるようにする。

```lean
@[grind =, simp] public theorem Symbol.isNonterminal_terminal {T N : Type*} (a : T) :
    Symbol.IsNonterminal (.terminal a : Symbol T N) = False := rfl

```

対応する非終端記号側の正規化。この対で `IsNonterminal` は常に `True`/`False` の具体値へ簡約され、`allNonterminals` や線形性述語のような、この述語をリスト全体・規則全体に持ち上げた定義の展開を機械的に進められる。

```lean
@[grind =, simp] public theorem Symbol.isNonterminal_nonterminal {T N : Type*} (A : N) :
    Symbol.IsNonterminal (.nonterminal A : Symbol T N) = True := rfl
```

正規形変換（特に Chomsky 標準形の構成）では、置換後の文形がすべて非終端記号から成るという不変条件を保ちながら規則を書き換える場面が繰り返し現れる。`allNonterminals` はその文形全体に対する要請を一つの命題にまとめたもので、これがなければ変換のたびに同じ全称論理式を書き下す必要が生じる。本体を公開しているのは、正規形変換がこの各点不変条件を規則構成時に消去（適用）するためである。

```lean
/-- Every symbol in the sentential form is a nonterminal.

Its body is exposed because public normal-form conversions eliminate this
pointwise invariant when constructing replacement rules. -/


@[expose] public def allNonterminals {T N : Type*} (xs : List (Symbol T N)) : Prop :=
  ∀ x ∈ xs, Symbol.IsNonterminal x
```

`Symbol.IsNonterminal` が命題（`Prop`）であるのに対し、`nonterminalCount`（後述）のような計算的な数え上げには決定可能な `Bool` 判定が要る。`symbolIsNonterminal` はその橋渡し役で、命題版と多くの補題を共有しつつ、`List.countP` のような計算関数にそのまま渡せる形を提供する。本体を公開しているのは、右線形・左線形の埋め込みがこの判定から導かれる非終端記号数を簡約するためである。

```lean
/-- Test the symbol shape for public linearity predicates and conversions.

Its body is exposed because public right- and left-linear embeddings simplify
the induced nonterminal count. -/


@[expose] public def symbolIsNonterminal {T N : Type*} : Symbol T N → Bool
  | .terminal _ => false
  | .nonterminal _ => true
```

ここから先の規則形状述語（線形・右線形・左線形・Chomsky・Greibach）はすべて単一規則 `ContextFreeRule T N` について述べるものなので、`ContextFreeRule` 名前空間の中にまとめて置く。こうすることで各述語は完全修飾なしで参照でき、他モジュールから見たときも「規則の形状を分類する語彙」という一まとまりの API として現れる。

```lean
namespace ContextFreeRule

```

`nonterminalCount` は、規則の出力（右辺の文形）に非終端記号がいくつ現れるかを数える。この数こそが線形文法の定義（非終端記号は高々一つ）の核心なので、`symbolIsNonterminal` を `List.countP` に渡すこの一手間を独立させておくことで、線形性判定を単なる数値比較に還元できる。本体を公開しているのは、正則文法への埋め込み証明がこの数え上げを正規化して評価するためである。

```lean
variable {T N : Type*}

/-- The number of nonterminal symbols on the right-hand side of a rule.

Its body is exposed because public linearity proofs calculate this count. -/


@[expose] public def nonterminalCount (r : ContextFreeRule T N) : Nat :=
  r.output.countP symbolIsNonterminal
```

線形文法（`LinearGrammar`、後述）を成り立たせる規則側の契約が `IsLinear` である。非終端記号数がたかだか一つという条件を `nonterminalCount` 経由で述べることで、線形性の証明は数値の不等式に帰着し、右線形・左線形といったより強い形状述語の妥当性チェックの土台にもなる。本体を公開しているのは、正則文法への埋め込みがこの数え上げの正規化によって証明されるためである。

```lean
/-- A rule is linear when its output contains at most one nonterminal.

Its body is exposed because public regular-grammar embeddings prove it by
normalizing the public count definition. -/


@[expose] public def IsLinear (r : ContextFreeRule T N) : Prop :=
  Mathling.Grammar.ContextFreeRule.nonterminalCount r ≤ 1
```

`IsRightLinear` は正則文法との対応で使う「一記号右線形標準形」を規則の形として直接記述する述語で、`RightLinearGrammar`（後述）の妥当性条件を構成する。ε規則・終端のみの規則・「終端＋非終端が右端」の規則という三択の非交和で表しているため、右線形文法から有限オートマトンへの変換はこの三分岐にそのまま従って構成できる。本体を公開しているのは、右線形変換の証明項がこの三択述語をそのまま消去して場合分けするためである。

```lean
/-- The one-symbol right-linear normal form.

Its body is exposed because public right-linear conversions eliminate this
three-way rule-shape predicate in their proof terms. -/


@[expose] public def IsRightLinear (r : ContextFreeRule T N) : Prop :=
  r.output = [] ∨
  (∃ a, r.output = [Symbol.terminal a]) ∨
  (∃ a B, r.output = [Symbol.terminal a, Symbol.nonterminal B])
```

`IsLeftLinear` は `IsRightLinear` の鏡像で、非終端記号が右辺の左端に来る形を規定する。両者を独立した述語として用意しておくことで、右線形文法を反転（reversal）して左線形文法を得るような変換が、片方の述語をもう片方へ書き換えるだけで完結する。本体を公開しているのは、反転変換の証明項がこの三択述語を直接消去するためである。

```lean
/-- The one-symbol left-linear normal form.

Its body is exposed because public reversal conversions eliminate this
three-way rule-shape predicate in their proof terms. -/


@[expose] public def IsLeftLinear (r : ContextFreeRule T N) : Prop :=
  r.output = [] ∨
  (∃ a, r.output = [Symbol.terminal a]) ∨
  (∃ A a, r.output = [Symbol.nonterminal A, Symbol.terminal a])
```

`IsChomskyNormal` は `ChomskyNormalGrammar`（後述）の中核契約であり、初期記号 `S` を明示的な引数に取る点が線形系の述語と異なる。これは標準的な Chomsky 標準形が「初期記号のみ ε を生成してよい」という例外を許すためで、この例外を述語に組み込んでおくことで、ε除去や単位規則除去を行う変換がこの一つの述語に対して健全性を示せば済む。本体を公開しているのは、正規形変換の証明が各許容ケースをここから直接構成するためである。

```lean
/-- Chomsky rule shape, including the standard initial-symbol ε exception.

Its body is exposed because public normal-form conversions construct each
admissible rule-shape case directly. -/


@[expose] public def IsChomskyNormal (S : N) (r : ContextFreeRule T N) : Prop :=
  (r.input = S ∧ r.output = []) ∨
  (∃ a : T, r.output = [Symbol.terminal a]) ∨
  (∃ B C : N, r.output = [Symbol.nonterminal B, Symbol.nonterminal C])
```

`IsGreibachNormal` は同じ初期記号例外を持ちつつ、右辺の先頭に必ず終端記号を置き、その後ろに非終端記号列だけを許す形を規定する。この形は構文解析器がトークンを一つ読むたびに規則を一意に選べるという操作的な保証（先頭終端記号による決定性）に直結しており、`GreibachNormalGrammar`（後述）が保証する不変条件そのものである。本体を公開しているのは、Greibach 変換の証明項がこの述語のケースを直接構成するためである。この名前空間を閉じることで、以降の述語はふたたび `Mathling.Grammar` 直下、すなわち文法そのもの（規則の集合）を扱う層に戻る。

```lean
/-- Greibach rule shape, including the standard initial-symbol ε exception.

Its body is exposed because public Greibach conversions construct its cases
directly in their proof terms. -/


@[expose] public def IsGreibachNormal (S : N) (r : ContextFreeRule T N) : Prop :=
  (r.input = S ∧ r.output = []) ∨
  ∃ a : T, ∃ tail : List N,
    r.output = Symbol.terminal a :: tail.map Symbol.nonterminal
end ContextFreeRule
```

`ContextFreeRule.IsLinear` は個々の規則についての述語だったが、実際の変換や証明が扱う対象は文法全体である。`LinearGrammar` は生の `ContextFreeGrammar` を、その全規則が線形であるという全称証明ごと束ねた証拠付き構造で、以後この型を受け取る関数・定理はフィールド `linear` を取り出すだけで線形性を利用でき、規則集合を毎回走査し直す必要がない。

```lean
/-- A context-free grammar all of whose rules are linear. -/
public structure LinearGrammar (T : Type*) where
  cfg : ContextFreeGrammar T
  linear : ∀ r ∈ cfg.rules, Mathling.Grammar.ContextFreeRule.IsLinear r
```

`LinearGrammar.language` は証拠付き構造から生成言語だけを取り出す忘却写像である。線形性の証明はこの言語自体には影響しないため、線形文法を通常の `Language` として扱いたい呼び出し側（例えば別の文法クラスとの言語同値を示す場面）に対して、証拠を運ばない素の言語表現への出口を提供する。

```lean
namespace LinearGrammar

/-- The language generated after forgetting the linearity certificate. -/
@[expose] public def language (g : LinearGrammar T) : Language T := g.cfg.language

end LinearGrammar
```

`RightLinearGrammar` は `LinearGrammar` と同じ束ね方を、より強い形状述語 `IsRightLinear` に対して行ったものである。右線形文法は有限オートマトンと直接対応するため、この型は「正則言語であることの証拠」を運ぶ器として、正則文法との相互変換モジュールから参照される。

```lean
/-- A context-free grammar in one-symbol right-linear normal form. -/
public structure RightLinearGrammar (T : Type*) where
  cfg : ContextFreeGrammar T
  rightLinear : ∀ r ∈ cfg.rules, Mathling.Grammar.ContextFreeRule.IsRightLinear r
```

## 証拠付き文法構造

左右線形文法に加え、Chomsky および Greibach 標準形を、規則形状の全称証明と初期記号が右辺に現れない不変条件ごと束ねる。変換の出力型そのものが、後続定理で必要な整形式を保持する。

`LeftLinearGrammar` は `RightLinearGrammar` の対となる構造で、`IsLeftLinear` の全称証明を運ぶ。右線形文法を反転して得られる文法はこの型に属するため、反転変換の出力型としてそのまま使われ、呼び出し側が改めて左線形性を証明し直す必要がない。

```lean
/-- A context-free grammar in one-symbol left-linear normal form. -/
public structure LeftLinearGrammar (T : Type*) where
  cfg : ContextFreeGrammar T
  leftLinear : ∀ r ∈ cfg.rules, Mathling.Grammar.ContextFreeRule.IsLeftLinear r
```

`ChomskyNormalGrammar` は線形系の構造よりも証拠が一つ多い。規則形状 `chomskyNormal` に加えて `initial_not_output` を持ち、初期記号がどの規則の右辺にも現れないことを保証する。この第二の不変条件がなければ、Chomsky 標準形からの構文解析（CYK 法など）が初期記号を巡回的に生成し得るという想定外のケースを排除できず、正規形変換の出力型としてこの二条件を同時に運ぶことが以後の定理の前提を単純に保つ鍵になる。

```lean
/-- A context-free grammar in Chomsky normal form. -/
public structure ChomskyNormalGrammar (T : Type*) where
  cfg : ContextFreeGrammar T
  chomskyNormal : ∀ r ∈ cfg.rules,
    Mathling.Grammar.ContextFreeRule.IsChomskyNormal cfg.initial r
  initial_not_output : ∀ r ∈ cfg.rules,
    Symbol.nonterminal cfg.initial ∉ r.output
```

`GreibachNormalGrammar` はモジュール末尾の最も強い形状保証で、`IsGreibachNormal` と同じ「初期記号は右辺に現れない」不変条件を組み合わせる。Greibach 標準形は各導出ステップで必ず一文字の終端記号を消費するため、この型を受け取る証明・アルゴリズムは無限降下（左再帰）が起こらないことを型レベルの証拠から直接引き出せる。ここで `end Mathling.Grammar` により、モジュール冒頭で開いた名前空間を閉じ、以降のモジュールはこれらの述語・構造を修飾名または `open` を通じて利用する。

```lean
/-- A context-free grammar in Greibach normal form. -/
public structure GreibachNormalGrammar (T : Type*) where
  cfg : ContextFreeGrammar T
  greibachNormal : ∀ r ∈ cfg.rules,
    Mathling.Grammar.ContextFreeRule.IsGreibachNormal cfg.initial r
  initial_not_output : ∀ r ∈ cfg.rules,
    Symbol.nonterminal cfg.initial ∉ r.output
end Mathling.Grammar
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
