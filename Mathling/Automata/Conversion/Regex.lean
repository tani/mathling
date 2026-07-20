    module

    public import Mathling.Automata.Core
    public import Mathlib.Computability.RegularExpressions

    public import LiterateLean
    open scoped LiterateLean

    @[expose] public section

# Mathling / Automata / Conversion / Regex モジュール

このモジュールは Mathling のこの領域に属する定義、変換、および証明を提供する。公開される契約と依存関係は import 境界で明示し、実装は以下の Lean ブロックに限定する。

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

/-- The language denoted by a regular expression. -/
abbrev language (r : RegularExpression α) : Language α :=
  _root_.RegularExpression.matches' r

@[simp] theorem language_empty : language (empty : RegularExpression α) = 0 := rfl

@[simp] theorem language_epsilon : language (epsilon : RegularExpression α) = 1 := rfl

@[simp] theorem language_symbol (a : α) :
    language (symbol a) = ({[a]} : Language α) := rfl

@[simp] theorem language_union (r s : RegularExpression α) :
    language (union r s) = language r + language s := rfl

@[simp] theorem language_concat (r s : RegularExpression α) :
    language (concat r s) = language r * language s := rfl

@[simp] theorem language_star (r : RegularExpression α) :
    language (star r) = (language r)∗ := rfl

/-- Decides whether a word matches a regular expression. -/
abbrev «matches» [DecidableEq α] (r : RegularExpression α) (w : List α) : Bool :=
  _root_.RegularExpression.rmatch r w

/-- The executable matcher recognizes exactly the denoted language. -/
@[simp] theorem matches_iff_mem_language [DecidableEq α]
    (r : RegularExpression α) (w : List α) :
    «matches» r w ↔ w ∈ language r :=
  _root_.RegularExpression.rmatch_iff_matches' r w

/-- The empty word belongs to the epsilon language. -/
theorem nil_mem_epsilon : ([] : List α) ∈ language (epsilon : RegularExpression α) := by
  simp

/-- A symbol belongs to its singleton-symbol language. -/
theorem symbol_mem_symbol (a : α) : [a] ∈ language (symbol a) := by
  exact Set.mem_singleton _

/-- The empty word belongs to every Kleene-star language. -/
theorem nil_mem_star (r : RegularExpression α) : ([] : List α) ∈ language (star r) := by
  exact Language.nil_mem_kstar _

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

## 実装の継続

次の定義群は前節で確立した型・不変条件・補題を利用して、このモジュールの契約を段階的に拡張する。

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
