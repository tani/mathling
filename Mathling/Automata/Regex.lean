    module

    public import Mathling.Automata.Core
    public import Mathlib.Computability.RegularExpressions
    public import Mathling.Meta.Important

    import Cslib.Computability.Languages.RegularLanguage
    import LiterateLean
    open scoped LiterateLean


# Mathling / Automata / Regex モジュール

正規表現の抽象構文、表示言語、実行可能なマッチャ、および文字列からのパーサーを一つの API としてまとめる。意味論と計算結果の一致、およびパース失敗を `Option.none` として返す境界が主要な契約である。

## 型と基本コンストラクタ

Mathlib の `RegularExpression` をそのまま Mathling 名前空間へ再輸出し、`empty`/`epsilon`/`symbol`/`union`/`concat`/`star` という短い構成子省略形を与える。これらはすべて `abbrev` であり、対応する Mathlib 側のコンストラクタと定義的に等しいため、後続の証明で展開のコストを気にする必要はない。

このフェンスはモジュール冒頭のドキュメンテーションコメントと `Computability` の scoped 記法を開くだけであり、以降のすべての宣言が参照する暗黙の環境設定を確立する。ここで `open scoped Computability` を行っておかないと、後段の `language` 補題群で正則言語の演算記号(`0, 1, +, *`)が期待通りに表示・解決されない。

```lean

/-!
# Regular expressions

Regular-expression syntax, language semantics, and executable matching.
-/



open scoped Computability

```

`Mathling.Automata` 名前空間を開き、Mathlib の `RegularExpression` 型そのものをこの名前空間の下に再輸出する。これにより、以降のすべての構成子・補題は `Mathling.Automata.RegularExpression` として参照でき、クライアントは Mathlib の型と定義的に同一の型に対してプログラムする一方、API としては Mathling 側の名前空間だけに依存すればよい。

```lean
namespace Mathling.Automata

/-- Mathlib's regular expressions, re-exported in the Mathling namespace. -/
public abbrev RegularExpression (α : Type*) := _root_.RegularExpression α

```

`RegularExpression` の名前空間を開き、以下の一群の構成子省略形(`empty` から `star` まで)を定義する。まず `empty` は空言語 $`0`$ に対応する構成子で、後述の `parseUnion`/`parseConcat` がバックトラックせずに失敗を表現する際の意味論的な基盤にもなる。

```lean
namespace RegularExpression

/-- The regular expression that matches no words. -/
public abbrev empty : RegularExpression α := (0 : _root_.RegularExpression α)
```

`epsilon` は空語のみを含む言語 $`1`$ に対応し、具象構文パーサー `parse` が入力文字列 `""` を受け取ったときの戻り値としてそのまま使われる。

```lean
/-- The regular expression that matches only the empty word. -/
public abbrev epsilon : RegularExpression α := (1 : _root_.RegularExpression α)
```

`symbol` は単一文字を受理する基本構成子であり、具象構文パーサーの `parseAtom` が予約文字以外の文字を読んだときにこの構成子へ落とし込む、パーサーとの直接の対応点である。

```lean
/-- The regular expression that matches a single symbol. -/
public abbrev symbol (a : α) : RegularExpression α := _root_.RegularExpression.char a
```

`union` は二つの正規表現の選言を表す。具象構文では `|` 演算子に対応し、優先順位が最も低いため `parseUnion`/`parseUnionTail` の再帰構造の最終的な合成点になる。

```lean
/-- Union of two regular expressions. -/
public abbrev union (r s : RegularExpression α) : RegularExpression α := r + s
```

`concat` は連接(積)を表し、具象構文では暗黙の並置に対応する。`union` より優先度が高く `star` より低いため、パーサー側では `parseConcat`/`parseConcatTail` がこのレベルを担当する。

```lean
/-- Concatenation of two regular expressions. -/
public abbrev concat (r s : RegularExpression α) : RegularExpression α := r * s
```

`star` は Kleene star($`{}^*`$)を表し、演算子の中で最も優先度が高い。具象構文パーサーでは `parseStarTail` が `*` を貪欲に読み進めながらこの構成子を繰り返し適用する。

```lean
/-- Kleene star of a regular expression. -/
public abbrev star (r : RegularExpression α) : RegularExpression α :=
  _root_.RegularExpression.star r
```

## denoted language: 意味論としての展開補題

$`\mathrm{language} : \mathrm{RegularExpression}\,\alpha \to \mathrm{Language}\,\alpha`$ は正規表現が指し示す言語そのものであり、証明のための「意味論」として機能する。続く `@[simp]` 補題群は、この `language` が各コンストラクタの下でどのように展開されるかを規定するものであり、正規表現に対する構造的な議論を `Language` 上の演算($`0, 1, +, *, {}^*`$)についての等式へ自動的に書き換えるために使われる。

```lean
/-- The language denoted by a regular expression. -/
public abbrev language (r : RegularExpression α) : Language α :=
  _root_.RegularExpression.matches' r

```

`language_empty` は `empty` が空言語 $`0`$ を指示することを固定する。この等式がないと、`empty` を含む式に対する構造帰納法(`language_isRegular` など)が `Language` 側の $`0`$ の性質(閉包性など)にたどり着けない。

```lean
@[grind =, simp] public theorem language_empty : language (empty : RegularExpression α) = 0 := rfl

```

`language_epsilon` は `epsilon` が単位言語 $`1`$(空語のみ)を指示することを固定し、`parse` が `""` を `epsilon` として返す設計と `language` の意味論とを結びつける。

```lean
@[grind =, simp] public theorem language_epsilon :
    language (epsilon : RegularExpression α) = 1 := rfl

```

`language_symbol` は `symbol a` が単一文字言語 `{[a]}` を指示することを固定し、後述の `symbolDFA` が同じ言語を認識することを示す `symbolDFA_language` と対をなす架け橋になる。

```lean
@[grind =, simp] public theorem language_symbol (a : α) :
    language (symbol a) = ({[a]} : Language α) := rfl

```

`language_union` は選言構成子が言語レベルの和に対応することを規定し、`language_isRegular` の `plus` ケースで正則言語の加法閉包性(`Cslib.Language.IsRegular.add`)を適用するための書き換え規則として使われる。

```lean
@[grind =, simp] public theorem language_union (r s : RegularExpression α) :
    language (union r s) = language r + language s := rfl

```

`language_concat` は連接構成子が言語レベルの積に対応することを規定し、同様に `language_isRegular` の `comp` ケースで乗法閉包性を適用するために使われる。

```lean
@[grind =, simp] public theorem language_concat (r s : RegularExpression α) :
    language (concat r s) = language r * language s := rfl

```

`language_star` は Kleene star 構成子が言語レベルの star 演算に対応することを規定し、`language_isRegular` の `star` ケースで star 閉包性(`Cslib.Language.IsRegular.kstar`)へ橋渡しする最後の展開補題である。

```lean
@[grind =, simp] public theorem language_star (r : RegularExpression α) :
    language (star r) = (language r)∗ := rfl

```

## 正規表現から正則言語への接続

一文字言語には三状態 DFA を直接与える。開始状態から指定文字を読んだ場合だけ受理状態へ
移り、それ以外または二文字目以降は dead 状態へ移る。和・連接・Kleene star については
正則言語の閉包性を用いるため、正規表現の構文帰納法がそのまま有限オートマトンの存在証明に
なる。連接と star の構成が要求する alphabet の基準要素は `Nonempty` から局所的に選ぶ。

`symbolDFA` は単一文字言語 `{[a]}` を認識する具体的な三状態 DFA を与える。状態は `Option Bool` で表現し、`none` が開始状態、`some false` が受理状態、`some true` が dead 状態である。これは `language_isRegular` の `char` ケースで正則性の基礎ケースを与えるための私的な補助構成であり、外部からは直接使われない。

```lean
private def symbolDFA [DecidableEq α] (a : α) : DFA α (Option Bool) where
  step state b :=
    match state with
    | none => if b = a then some false else some true
    | some _ => some true
  start := none
  accept := {some false}

```

`symbolDFA_evalFrom_dead` は dead 状態が吸収状態であること、すなわち一度 dead へ落ちたら以後どんな入力を読んでも dead のままであることを保証する補題である。この不変量がないと `symbolDFA_language` の二文字以上のケースで評価結果を追跡できない。

```lean
@[grind =, simp] private theorem symbolDFA_evalFrom_dead [DecidableEq α]
    (a : α) (word : List α) :
    (symbolDFA a).evalFrom (some true) word = some true := by
  induction word with
  | nil => rfl
  | cons b word ih => simpa [symbolDFA] using ih

```

`symbolDFA_language` は `symbolDFA` が実際に単一文字言語 `{[a]}` を認識することを示し、`language_symbol` と対をなして `language_isRegular` の `char` ケースの正則性証人を完成させる。空語・単一文字・二文字以上の三通りに場合分けし、後者では直前の `symbolDFA_evalFrom_dead` を用いて dead 状態からは受理されないことを確認する。

```lean
@[grind =] private theorem symbolDFA_language [DecidableEq α] (a : α) :
    (symbolDFA a).accepts = ({[a]} : Language α) := by
  ext word
  cases word with
  | nil =>
      change (symbolDFA a).eval [] = some false ↔ ([] : List α) = [a]
      simp [symbolDFA, DFA.eval, DFA.evalFrom]
  | cons b tail =>
      cases tail with
      | nil =>
          change (symbolDFA a).eval [b] = some false ↔ [b] = [a]
          simp [symbolDFA, DFA.eval, DFA.evalFrom]
      | cons c tail =>
          change (symbolDFA a).eval (b :: c :: tail) = some false ↔
            b :: c :: tail = [a]
          have heval : (symbolDFA a).eval (b :: c :: tail) = some true := by
            rw [DFA.eval, DFA.evalFrom_cons, DFA.evalFrom_cons]
            by_cases h : b = a <;>
              simpa [symbolDFA, h] using symbolDFA_evalFrom_dead a tail
          simp [heval]
```

この定理は、上の展開補題群(`language_empty` から `language_star`)と `symbolDFA_language` を組み合わせ、正規表現の構文帰納法によって正則性の閉包演算を積み上げる。`@[important]` が付されているのは、これがモジュールの中心的な成果——正規表現の言語は常に正則である——だからであり、以降の `compileNFA` はこの証明から具体的なオートマトンを取り出す。

```lean
/-- Every regular expression over a nonempty finite alphabet denotes a regular
language.  The proof is the language-level form of Thompson construction. -/


@[important, grind .] public theorem language_isRegular [Nonempty α]
    (r : RegularExpression α) : (language r).IsRegular := by
  letI : Inhabited α := ⟨Classical.choice inferInstance⟩
  letI : DecidableEq α := Classical.decEq α
  induction r with
  | zero => exact Cslib.Language.IsRegular.zero
  | epsilon => exact Cslib.Language.IsRegular.one
  | char a =>
      exact Language.isRegular_iff.mpr
        ⟨Option Bool, inferInstance, symbolDFA a, symbolDFA_language a⟩
  | plus r s hr hs => exact Cslib.Language.IsRegular.add hr hs
  | comp r s hr hs => exact Cslib.Language.IsRegular.mul hr hs
  | star r hr => exact Cslib.Language.IsRegular.kstar hr
```

`language_isRegular` は正則性の存在だけを証明し、具体的な状態型は `Classical.choice` の背後に隠れたままである。`FiniteNFA` はこの存在証明から取り出せる有限 NFA を、その状態の有限性(`Fintype`)と認識言語の証明(`language_eq`)とともに束ねるプレゼンテーション型であり、クライアントが具体的な状態表現に依存しないための境界を作る。

```lean
/-- A finite-state NFA together with its recognized-language specification. -/
public structure FiniteNFA (α : Type*) (L : Language α) where
  State : Type
  stateFintype : Fintype State
  machine : NFA α State
  language_eq : machine.accepts = L
```

`compileNFA` は `language_isRegular` を `Language.isRegular_iff_nfa` 経由で NFA の存在に翻訳し、`Classical.choose` で状態型・有限性インスタンス・機械・正当性を取り出して `FiniteNFA` にパックする。`noncomputable` であるのはこの取り出しが選択原理を経由するためで、実行可能なマッチングには前節の `matches`(Brzozowski 導関数ベース)を使うべきであり、このオートマトンは主に正則性を利用する証明側の道具である。

```lean
/-- Compile a regular expression to a finite NFA.  The concrete state type is
hidden behind the presentation record so clients depend only on its language. -/
public noncomputable def compileNFA [Nonempty α]
    (r : RegularExpression α) : FiniteNFA α (language r) := by
  classical
  let witness := Mathling.Automata.Language.isRegular_iff_nfa.mp r.language_isRegular
  let State := Classical.choose witness
  let inst := Classical.choose (Classical.choose_spec witness)
  let machine := Classical.choose (Classical.choose_spec (Classical.choose_spec witness))
  have correct := Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec witness))
  exact
    { State := State
      stateFintype := inst
      machine := machine
      language_eq := correct }
```

`compileNFA_language` restates the `language_eq` field of the compiled `FiniteNFA` as a top-level `simp`/`grind` lemma, so downstream proofs can rewrite `r.compileNFA.machine.accepts` to `language r` without unfolding the `FiniteNFA` record. It closes the loop between the semantic `language` and the constructive automaton produced by `compileNFA`.

```lean
/-- The compiled finite NFA recognizes exactly the denoted regex language. -/
@[important, grind =, simp] public theorem compileNFA_language [Nonempty α]
    (r : RegularExpression α) : r.compileNFA.machine.accepts = language r :=
  r.compileNFA.language_eq
```

## executable matcher とその正当性

`language` が証明に便利な「指示される言語」であるのに対し、`matches` はそれとは独立に定義された実行可能なブール値判定関数(Brzozowski 導関数に基づく Mathlib の `rmatch`)であり、計算効率のために別途用意されている。両者は定義上一致するとは限らないため、`matches_iff_mem_language` がこの実行可能マッチャーと指示される言語の外延的な一致を保証する橋渡し定理となる。以降のモジュールはこの定理を通じてのみ `matches` の正しさを利用する。

`«matches»` is the abbreviation clients actually call at runtime: it wraps Mathlib's `rmatch`, a Brzozowski-derivative-based decision procedure, so that regex matching is computable and efficient rather than relying on the nonconstructive `compileNFA`. It has no proven relationship to `language` on its own; that connection is established by the next theorem.

```lean
/-- Decides whether a word matches a regular expression. -/
public abbrev «matches» [DecidableEq α] (r : RegularExpression α) (w : List α) : Bool :=
  _root_.RegularExpression.rmatch r w
```

`matches_iff_mem_language` is the bridge theorem promised above: it certifies that the executable `«matches»` agrees extensionally with the denoted `language` for every word. Everything downstream — including the concrete-syntax `match` entry point — relies on `«matches»` being correct only through this lemma, never by inspecting `rmatch`'s implementation directly.

```lean
/-- The executable matcher recognizes exactly the denoted language. -/
@[important, grind =, simp] public theorem matches_iff_mem_language [DecidableEq α]
    (r : RegularExpression α) (w : List α) :
    «matches» r w ↔ w ∈ language r :=
  _root_.RegularExpression.rmatch_iff_matches' r w
```

## 具象構文の内部パーサー

ここから先は、正規表現の具象構文(文字列表現)を解析するための内部実装であり、`Internal` 名前空間に分離される。演算子の優先順位は和(`|`)・連接(暗黙)・星(`*`)・原子の順に低くなり、これを再帰下降法で以下のように相互再帰(`mutual`)する一群の関数として実装する。各関数は残り燃料(`fuel : Nat`)を消費しながら再帰することで停止性を保証しており、燃料が尽きた場合は「式が複雑すぎる」というエラーを返す。

```mermaid
flowchart LR
  U["parseUnion (`|`)"] --> C["parseConcat (連接)"]
  C --> S["parseStar (`*`)"]
  S --> A["parseAtom (原子・括弧)"]
  A -->|"'(' ... ')'"| U
```

`Internal` 名前空間を開くことで、以下のパーサー実装が `Mathling.Automata.Regex` の公開 API から切り離され、`isRegexReserved` や個々の `parse*` 関数は外部から直接参照されない実装詳細であることを型システムのレベルで明示する。

```lean
namespace Internal

```

`isRegexReserved` は演算子として予約された文字(`(`, `)`, `|`, `*`)を判定する。`parseAtom` がこれを使って「予約文字以外はすべて単一文字リテラルとして受理する」という具象構文の境界を引く。

```lean
def isRegexReserved (c : Char) : Bool :=
  c == '(' || c == ')' || c == '|' || c == '*'
```

`ParseState` はこの再帰下降パーサー全体が共有する戻り値の形であり、成功時には解析済みの正規表現と未消費の残り文字列を、失敗時にはエラーメッセージを運ぶ。以下の `mutual` ブロックは、この型を介して連鎖する六つの相互再帰関数(`parseUnion`/`parseUnionTail`/`parseConcat`/`parseConcatTail`/`parseStar`/`parseStarTail`/`parseAtom`)をまとめて定義する——上のフローチャートに示した優先順位の階層をそのままコードとして実装したものである。停止性は各関数が受け取る `fuel : Nat` が呼び出しのたびに厳密に減ることで保証され、`fuel = 0` で強制終了して「式が複雑すぎる」エラーを返すことで、悪意ある・巨大な入力に対しても停止性が Lean の停止性検査を通ることを保証する。

```lean
/-- Intermediate parse result: a regex plus the unconsumed characters. -/
abbrev ParseState := Except String (RegularExpression Char × List Char)

mutual

  def parseUnion (fuel : Nat) (cs : List Char) : ParseState :=
    match fuel with
    | 0 => .error "expression too complex"
    | f + 1 =>
      match parseConcat f cs with
      | .ok (first, rest) => parseUnionTail f first rest
      | .error e => .error e


  def parseUnionTail (fuel : Nat) (acc : RegularExpression Char)
      (cs : List Char) : ParseState :=
    match fuel with
    | 0 => .error "expression too complex"
    | f + 1 =>
      match cs with
      | '|' :: cs' =>
        match parseConcat f cs' with
        | .ok (nxt, rest) => parseUnionTail f (acc + nxt) rest
        | .error e => .error e
      | cs' => .ok (acc, cs')


  def parseConcat (fuel : Nat) (cs : List Char) : ParseState :=
    match fuel with
    | 0 => .error "expression too complex"
    | f + 1 =>
      match parseStar f cs with
      | .ok (first, rest) => parseConcatTail f first rest
      | .error e => .error e


  def parseConcatTail (fuel : Nat) (acc : RegularExpression Char)
      (cs : List Char) : ParseState :=
    match fuel with
    | 0 => .error "expression too complex"
    | f + 1 =>
      match parseStar f cs with
      | .ok (nxt, rest) => parseConcatTail f (acc * nxt) rest
      | .error _ => .ok (acc, cs)


  def parseStar (fuel : Nat) (cs : List Char) : ParseState :=
    match fuel with
    | 0 => .error "expression too complex"
    | f + 1 =>
      match parseAtom f cs with
      | .ok (base, rest) => .ok (parseStarTail f base rest)
      | .error e => .error e


  def parseStarTail (fuel : Nat) (acc : RegularExpression Char)
      (cs : List Char) : RegularExpression Char × List Char :=
    match fuel with
    | 0 => (acc, cs)
    | f + 1 =>
      match cs with
      | '*' :: cs' => parseStarTail f (star acc) cs'
      | cs' => (acc, cs')


  def parseAtom (fuel : Nat) (cs : List Char) : ParseState :=
    match fuel with
    | 0 => .error "expression too complex"
    | f + 1 =>
      match cs with
      | '(' :: cs' =>
        match parseUnion f cs' with
        | .ok (inner, rest) =>
          match rest with
          | ')' :: rest' => .ok (inner, rest')
          | _ => .error "expected ')'"
        | .error e => .error e
      | c :: cs' =>
        if isRegexReserved c then .error "unexpected reserved character"
        else .ok (symbol c, cs')
      | [] => .error "unexpected end of input"
end

end Internal
```

## 公開パーサー API

`end` で内部の `mutual` ブロックと `Internal` 名前空間を閉じたのち、モジュールの公開エントリポイントである `parse` と `match` を定義する。ここから先はもう `Internal` の実装詳細に触れる必要がなく、`parseUnion` を単一の入口として扱えばよい。

`parse` は空文字列を `epsilon` として特別扱いし、それ以外の入力に対しては `Internal.parseUnion` を燃料 `4 * cs.length + 4` で起動する。この燃料の量は各相互再帰関数が一文字あたり高々定数回しか消費しないことに基づく安全側の見積もりであり、停止性検査を通すためのものであって、意味論的な意味は持たない。パーサーが入力の途中までしか消費できなかった場合(`rest ≠ []`)は「末尾に余分な入力がある」エラーとし、構文的に閉じていない・不正な文字列を静かに受理してしまわないようにする。

```lean
/-- Parse a string as a regular expression over `Char`; `""` denotes epsilon. -/
public def parse (s : String) : Except String (RegularExpression Char) :=
  let cs := s.toList
  match cs with
  | [] => .ok epsilon
  | _ =>
    match Internal.parseUnion (4 * cs.length + 4) cs with
    | .ok (r, rest) =>
      match rest with
      | [] => .ok r
      | _ => .error "unexpected trailing input"
    | .error e => .error e
```

`match` はモジュール全体の最終的な利用者向けエントリポイントであり、`parse` と `matches` という二つの独立した契約(構文解析の成否、および `matches_iff_mem_language` で正当化された意味論的マッチング)を一つの `Bool` に合成する。パース失敗を例外として伝播させず単に `false` を返すのは、意図的な設計判断である——呼び出し側は不正なパターン文字列を特別扱いする必要がなく、「解釈できない正規表現は何にもマッチしない」という一貫した契約だけを気にすればよい。

```lean
/-- Parses a regular expression and decides whether it matches the input string.
Malformed regular expressions do not match any input. -/
public def «match» (pattern input : String) : Bool :=
  match parse pattern with
  | .ok r => «matches» r input.toList
  | .error _ => false

end RegularExpression

end Mathling.Automata
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
