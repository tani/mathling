    module

    public import Mathling.Automata.Core
    public import Mathlib.Computability.RegularExpressions
    public import Mathling.Meta.Important

    public import LiterateLean
    open scoped LiterateLean

    @[expose] public section

# Mathling / Automata / Conversion / Regex モジュール

正規表現の抽象構文、表示言語、実行可能なマッチャ、および文字列からのパーサーを一つの API としてまとめる。意味論と計算結果の一致、およびパース失敗を `Option.none` として返す境界が主要な契約である。

## 型と基本コンストラクタ

Mathlib の `RegularExpression` をそのまま Mathling 名前空間へ再輸出し、`empty`/`epsilon`/`symbol`/`union`/`concat`/`star` という短い構成子省略形を与える。これらはすべて `abbrev` であり、対応する Mathlib 側のコンストラクタと定義的に等しいため、後続の証明で展開のコストを気にする必要はない。

```lean
public section

/-!
# Regular expressions

Regular-expression syntax, language semantics, and executable matching.
-/

open scoped Computability

namespace Mathling.Automata

/-- Mathlib's regular expressions, re-exported in the Mathling namespace. -/
abbrev RegularExpression (α : Type*) := _root_.RegularExpression α

namespace RegularExpression

/-- The regular expression that matches no words. -/
abbrev empty : RegularExpression α := (0 : _root_.RegularExpression α)

/-- The regular expression that matches only the empty word. -/
abbrev epsilon : RegularExpression α := (1 : _root_.RegularExpression α)

/-- The regular expression that matches a single symbol. -/
abbrev symbol (a : α) : RegularExpression α := _root_.RegularExpression.char a

/-- Union of two regular expressions. -/
abbrev union (r s : RegularExpression α) : RegularExpression α := r + s

/-- Concatenation of two regular expressions. -/
abbrev concat (r s : RegularExpression α) : RegularExpression α := r * s

/-- Kleene star of a regular expression. -/
abbrev star (r : RegularExpression α) : RegularExpression α :=
  _root_.RegularExpression.star r
```

## denoted language: 意味論としての展開補題

$`\mathrm{language} : \mathrm{RegularExpression}\,\alpha \to \mathrm{Language}\,\alpha`$ は正規表現が指し示す言語そのものであり、証明のための「意味論」として機能する。続く `@[simp]` 補題群は、この `language` が各コンストラクタの下でどのように展開されるかを規定するものであり、正規表現に対する構造的な議論を `Language` 上の演算($`0, 1, +, *, {}^*`$)についての等式へ自動的に書き換えるために使われる。

```lean
/-- The language denoted by a regular expression. -/
abbrev language (r : RegularExpression α) : Language α :=
  _root_.RegularExpression.matches' r

@[grind =, simp] theorem language_empty : language (empty : RegularExpression α) = 0 := rfl

@[grind =, simp] theorem language_epsilon : language (epsilon : RegularExpression α) = 1 := rfl

@[grind =, simp] theorem language_symbol (a : α) :
    language (symbol a) = ({[a]} : Language α) := rfl

@[grind =, simp] theorem language_union (r s : RegularExpression α) :
    language (union r s) = language r + language s := rfl

@[grind =, simp] theorem language_concat (r s : RegularExpression α) :
    language (concat r s) = language r * language s := rfl

@[grind =, simp] theorem language_star (r : RegularExpression α) :
    language (star r) = (language r)∗ := rfl
```

## executable matcher とその正当性

`language` が証明に便利な「指示される言語」であるのに対し、`matches` はそれとは独立に定義された実行可能なブール値判定関数(Brzozowski 導関数に基づく Mathlib の `rmatch`)であり、計算効率のために別途用意されている。両者は定義上一致するとは限らないため、`matches_iff_mem_language` がこの実行可能マッチャーと指示される言語の外延的な一致を保証する橋渡し定理となる。以降のモジュールはこの定理を通じてのみ `matches` の正しさを利用する。

```lean
/-- Decides whether a word matches a regular expression. -/
abbrev «matches» [DecidableEq α] (r : RegularExpression α) (w : List α) : Bool :=
  _root_.RegularExpression.rmatch r w

/-- The executable matcher recognizes exactly the denoted language. -/
@[important, grind =, simp] theorem matches_iff_mem_language [DecidableEq α]
    (r : RegularExpression α) (w : List α) :
    «matches» r w ↔ w ∈ language r :=
  _root_.RegularExpression.rmatch_iff_matches' r w
```

## 具象構文の内部パーサー

ここから先は、正規表現の具象構文(文字列表現)を解析するための内部実装であり、モジュール外には公開されない(`private`)。演算子の優先順位は和(`|`)・連接(暗黙)・星(`*`)・原子の順に低くなり、これを再帰下降法で below のように相互再帰(`mutual`)する一群の関数として実装する。各関数は残り燃料(`fuel : Nat`)を消費しながら再帰することで停止性を保証しており、燃料が尽きた場合は「式が複雑すぎる」というエラーを返す。

```mermaid
flowchart LR
  U["parseUnion (`|`)"] --> C["parseConcat (連接)"]
  C --> S["parseStar (`*`)"]
  S --> A["parseAtom (原子・括弧)"]
  A -->|"'(' ... ')'"| U
```

```lean
private def isRegexReserved (c : Char) : Bool :=
  c == '(' || c == ')' || c == '|' || c == '*'

/-- Intermediate parse result: a regex plus the unconsumed characters. -/
private abbrev ParseState := Except String (RegularExpression Char × List Char)

mutual
  private def parseUnion (fuel : Nat) (cs : List Char) : ParseState :=
    match fuel with
    | 0 => .error "expression too complex"
    | f + 1 =>
      match parseConcat f cs with
      | .ok (first, rest) => parseUnionTail f first rest
      | .error e => .error e

  private def parseUnionTail (fuel : Nat) (acc : RegularExpression Char)
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

  private def parseConcat (fuel : Nat) (cs : List Char) : ParseState :=
    match fuel with
    | 0 => .error "expression too complex"
    | f + 1 =>
      match parseStar f cs with
      | .ok (first, rest) => parseConcatTail f first rest
      | .error e => .error e

  private def parseConcatTail (fuel : Nat) (acc : RegularExpression Char)
      (cs : List Char) : ParseState :=
    match fuel with
    | 0 => .error "expression too complex"
    | f + 1 =>
      match parseStar f cs with
      | .ok (nxt, rest) => parseConcatTail f (acc * nxt) rest
      | .error _ => .ok (acc, cs)

  private def parseStar (fuel : Nat) (cs : List Char) : ParseState :=
    match fuel with
    | 0 => .error "expression too complex"
    | f + 1 =>
      match parseAtom f cs with
      | .ok (base, rest) => .ok (parseStarTail f base rest)
      | .error e => .error e

  private def parseStarTail (fuel : Nat) (acc : RegularExpression Char)
      (cs : List Char) : RegularExpression Char × List Char :=
    match fuel with
    | 0 => (acc, cs)
    | f + 1 =>
      match cs with
      | '*' :: cs' => parseStarTail f (star acc) cs'
      | cs' => (acc, cs')

  private def parseAtom (fuel : Nat) (cs : List Char) : ParseState :=
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
```

## 公開パーサー API

`end` で内部の `mutual` ブロックを閉じたのち、モジュールの公開エントリポイントである `parse` と `match` を定義する。`parse` は空文字列を `epsilon` として扱い、それ以外は上の相互再帰パーサーを十分な燃料(`4 * cs.length + 4`)付きで起動し、入力を消費し切れなかった場合は「末尾に余分な入力がある」エラーとする。`match` は `parse` の結果に応じて `matches` を呼び出す薄いラッパーであり、構文的に不正な正規表現は(エラーを伝播させず)単に何にもマッチしないものとして扱う。

```lean
end

/-- Parse a string as a regular expression over `Char`; `""` denotes epsilon. -/
def parse (s : String) : Except String (RegularExpression Char) :=
  let cs := s.toList
  match cs with
  | [] => .ok epsilon
  | _ =>
    match parseUnion (4 * cs.length + 4) cs with
    | .ok (r, rest) =>
      match rest with
      | [] => .ok r
      | _ => .error "unexpected trailing input"
    | .error e => .error e

/-- Parses a regular expression and decides whether it matches the input string.
Malformed regular expressions do not match any input. -/
def «match» (pattern input : String) : Bool :=
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
