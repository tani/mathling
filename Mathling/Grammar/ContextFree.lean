    module

    public import Mathling.Grammar.Core
    public import Mathlib.Data.Finset.Union
    public import Mathlib.Data.List.Sublists

    public import LiterateLean
    open scoped LiterateLean

    @[expose] public section

# Mathling / Grammar / ContextFree モジュール

文脈自由文法の有限台を抽出し、導出を構造化した証拠木へ変換する補助理論を提供する。有限性の計算可能な境界と、通常の書換え導出と木構造意味論の往復が、後続のオートマトン変換の基盤になる。

```lean
@[expose] public section

/-!
# Context-free grammar support

Shared finite-support and derivation utilities used by normal-form conversions.
The semantic notions of rewriting, derivation, and language remain Mathlib's
`ContextFreeGrammar` notions.
-/

namespace Mathling.Grammar

/-- Nonterminals occurring in a sentential form, in their original order. -/
def rhsNonterminals {T N : Type*} : List (Symbol T N) → List N
  | [] => []
  | Symbol.terminal _ :: xs => rhsNonterminals xs
  | Symbol.nonterminal A :: xs => A :: rhsNonterminals xs

namespace ContextFreeRule

/-- The input and all right-hand-side nonterminals of a rule. -/
def nonterminals {T N : Type*} (r : ContextFreeRule T N) : List N :=
  r.input :: rhsNonterminals r.output


end ContextFreeRule

```

## 有限台の抽出

`rhsNonterminals` は文中に現れる非終端記号を出現順に取り出す走査であり、`ContextFreeRule.nonterminals` はそれに規則の左辺 `input` を先頭として加えたものである。これらを部品として、次節では文法全体が実際に参照する非終端記号の有限集合を構成する。

```lean
namespace ContextFreeGrammar

variable {T N : Type*}

/-- The finite support explicitly mentioned by a grammar. -/
def activeNonterminals (g : ContextFreeGrammar T) [DecidableEq g.NT] : Finset g.NT :=
  {g.initial} ∪ g.rules.biUnion fun r =>
    (ContextFreeRule.nonterminals r).toFinset

@[simp] theorem initial_mem_activeNonterminals (g : ContextFreeGrammar T)
    [DecidableEq g.NT] :
    g.initial ∈ activeNonterminals g := by
  classical
  simp [activeNonterminals]

theorem rule_input_mem_activeNonterminals (g : ContextFreeGrammar T)
    [DecidableEq g.NT]
    {r : ContextFreeRule T g.NT} (hr : r ∈ g.rules) :
    r.input ∈ activeNonterminals g := by
  classical
  simp only [activeNonterminals, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_biUnion]
  right
  exact ⟨r, hr, by simp [ContextFreeRule.nonterminals]⟩

private theorem mem_rhsNonterminals_of_nonterminal_mem
    {xs : List (Symbol T N)} {A : N}
    (hA : Symbol.nonterminal A ∈ xs) : A ∈ rhsNonterminals xs := by
  induction xs with
  | nil => simp at hA
  | cons x xs ih =>
      cases x with
      | terminal a =>
          rcases List.mem_cons.mp hA with hEq | htail
          · cases hEq
          · exact ih htail
      | nonterminal B =>
          rcases List.mem_cons.mp hA with hEq | htail
          · exact List.mem_cons.mpr (Or.inl (Symbol.nonterminal.inj hEq))
          · exact List.mem_cons.mpr (Or.inr (ih htail))

theorem rule_rhs_mem_activeNonterminals (g : ContextFreeGrammar T)
    [DecidableEq g.NT]
    {r : ContextFreeRule T g.NT} {A : g.NT} (hr : r ∈ g.rules)
    (hA : Symbol.nonterminal A ∈ r.output) :
    A ∈ activeNonterminals g := by
  classical
  simp only [activeNonterminals, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_biUnion]
  right
  refine ⟨r, hr, ?_⟩
  change A ∈ (ContextFreeRule.nonterminals r).toFinset
  simp only [List.mem_toFinset, ContextFreeRule.nonterminals, List.mem_cons]
  exact Or.inr (mem_rhsNonterminals_of_nonterminal_mem hA)

```

## 文法の有限台とその所属補題

`activeNonterminals g` は初期記号と全規則の入出力に現れる非終端記号を合わせた有限集合であり、文法 `g` が実際に参照する非終端記号だけを過不足なく捉える。`initial_mem_activeNonterminals`・`rule_input_mem_activeNonterminals`・`rule_rhs_mem_activeNonterminals` はそれぞれ、初期記号・各規則の左辺・各規則の右辺に現れる非終端記号がこの集合に属することを保証し、内部の `mem_rhsNonterminals_of_nonterminal_mem` はそのうち右辺に関するものを `rhsNonterminals` の構造的な性質として支える。

次に、終端記号列だけからなる文に関する基本的な性質を確立する。

```lean
/-- Terminal embedding is injective. -/
theorem terminalSymbols_injective {u v : List T} :
    (terminalSymbols (N := N) u) = terminalSymbols v → u = v := by
  intro h
  induction u generalizing v with
  | nil => simpa using h
  | cons a u ih =>
      cases v with
      | nil => simp at h
      | cons b v =>
          change Symbol.terminal a :: terminalSymbols u =
            Symbol.terminal b :: terminalSymbols v at h
          obtain ⟨hsym, htail⟩ := List.cons.inj h
          cases hsym
          exact congrArg (a :: ·) (ih htail)

/-- A context-free rule cannot rewrite a terminal-only sentential form. -/
theorem no_rewrites_terminals (r : ContextFreeRule T N) {w : List T}
    {v : List (Symbol T N)} :
    r.Rewrites (terminalSymbols w) v → False := by
  intro h
  induction w generalizing v with
  | nil => cases h
  | cons a w ih =>
      cases h with
      | cons _ htail => exact ih htail

/-- A derivation between terminal-only forms does not change the word. -/
theorem derives_terminals_eq (g : ContextFreeGrammar T) {u v : List T} :
    g.Derives (terminalSymbols u) (terminalSymbols v) → u = v := by
  intro h
  rcases h.eq_or_head with heq | ⟨_, ⟨r, _, hr⟩, _⟩
  · exact terminalSymbols_injective heq
  · exact (no_rewrites_terminals r hr).elim

```

## 導出木による証拠の明示化

`ContextFreeGrammar.Derives` は書き換え関係 `Rewrites` の反射推移閉包であり、ある文が別の文へ導出可能かという命題を与えるだけで、その導出が「どのような形」をしていたかという情報を保持しない。以降で定義する相互帰納型 `DerivationSymbolTree`/`DerivationFormTree` は、終端記号列への導出それぞれに対して明示的な証拠木を与える。$`\mathrm{DerivationSymbolTree}\ g\ X\ w`$ は記号 $`X`$ が語 $`w`$ へ導出されることの証拠木であり、非終端記号の場合はある規則の適用とその右辺全体に対する導出木を子として持つ。$`\mathrm{DerivationFormTree}\ g\ xs\ w`$ は文 $`xs`$ が語 $`w`$ へ導出されることの証拠木であり、`cons` コンストラクタは先頭記号の木と残りの文の木を独立な子として保持する。

この明示的な木を持つことの利点は、`Derives` の証拠だけでは行えない「導出の形に関する構造的帰納法・再帰」ができる点にある。特に、連接された文 `xs ++ ys` への導出は `xs` への導出と `ys` への導出に独立に分解できる（後述 `derivationFormTree_split_append`）。この分解可能性が、後続節および正規形変換モジュールで「規則ごとに独立して導出を組み立てる」議論の土台になる。

```lean
mutual
  inductive DerivationSymbolTree (g : ContextFreeGrammar T) :
      Symbol T g.NT → List T → Prop
    | terminal (a : T) : DerivationSymbolTree g (.terminal a) [a]
    | nonterminal (r : ContextFreeRule T g.NT) (hr : r ∈ g.rules)
        {w : List T} (children : DerivationFormTree g r.output w) :
        DerivationSymbolTree g (.nonterminal r.input) w

  inductive DerivationFormTree (g : ContextFreeGrammar T) :
      List (Symbol T g.NT) → List T → Prop
    | nil : DerivationFormTree g [] []
    | cons {x : Symbol T g.NT} {u : List T}
        {xs : List (Symbol T g.NT)} {v : List T}
        (head : DerivationSymbolTree g x u)
        (tail : DerivationFormTree g xs v) :
        DerivationFormTree g (x :: xs) (u ++ v)
end

```

## 木の連結と分解

`DerivationFormTree` は文の連接に対して閉じている（`derivationFormTree_append`）。逆に、連接された文 `xs ++ ys` への証拠木は、`xs` への証拠木と `ys` への証拠木へ一意に分解できる（`derivationFormTree_split_append`）。後者は、次節で一歩の書き換えを証拠木の言葉に翻訳する際の中心的な道具になる。

```lean
private theorem derivationFormTree_append (g : ContextFreeGrammar T)
    {xs ys : List (Symbol T g.NT)} {u v : List T}
    (hx : DerivationFormTree g xs u) (hy : DerivationFormTree g ys v) :
    DerivationFormTree g (xs ++ ys) (u ++ v) := by
  cases hx with
  | nil => simpa using hy
  | cons head tail =>
      simpa [List.append_assoc] using
        DerivationFormTree.cons head (derivationFormTree_append g tail hy)
termination_by xs.length

private theorem derivationFormTree_split_append (g : ContextFreeGrammar T)
    {xs ys : List (Symbol T g.NT)} {w : List T}
    (h : DerivationFormTree g (xs ++ ys) w) :
    ∃ u v, w = u ++ v ∧
      DerivationFormTree g xs u ∧ DerivationFormTree g ys v := by
  cases xs with
  | nil => exact ⟨[], w, by simp, DerivationFormTree.nil, by simpa using h⟩
  | cons x xs =>
      cases h with
      | cons head tail =>
          obtain ⟨u, v, rfl, hu, hv⟩ :=
            derivationFormTree_split_append g (xs := xs) (ys := ys) tail
          exact ⟨_, v, by simp [List.append_assoc],
            DerivationFormTree.cons head hu, hv⟩
termination_by xs

```

## 導出から証拠木を構成する

ここからは通常の導出関係 `Derives` を実際に証拠木へ変換する。終端記号列のみからなる文は自明な証拠木を持ち（`derivationFormTree_terminals`）、一歩の書き換え `Produces` を挟んでも証拠木は保たれる：書き換えられた部分を `derivationFormTree_split_append` で切り出し、規則適用のノードに置き換えてから `derivationFormTree_append` で貼り戻す（`derivationFormTree_of_produces`）。これを導出列全体に沿って畳み込むことで、任意の終端導出に対する証拠木が得られる（`derivationFormTree_of_derives`）。

```lean
private theorem derivationFormTree_terminals (g : ContextFreeGrammar T)
    (w : List T) : DerivationFormTree g (terminalSymbols w) w := by
  induction w with
  | nil => exact DerivationFormTree.nil
  | cons a w ih =>
      simpa [terminalSymbols] using
        DerivationFormTree.cons (DerivationSymbolTree.terminal a) ih

private theorem derivationFormTree_of_produces
    (g : ContextFreeGrammar T)
    {u v : List (Symbol T g.NT)} {w : List T}
    (hstep : g.Produces u v) (hv : DerivationFormTree g v w) :
    DerivationFormTree g u w := by
  rcases hstep with ⟨r, hr, hrewrite⟩
  obtain ⟨p, q, rfl, rfl⟩ := hrewrite.exists_parts
  have hv' : DerivationFormTree g (p ++ (r.output ++ q)) w := by
    simpa [List.append_assoc] using hv
  obtain ⟨wp, wrest, hw, hp, hrest⟩ :=
    derivationFormTree_split_append g (xs := p) (ys := r.output ++ q) hv'
  subst w
  obtain ⟨wout, wq, rfl, hout, hq⟩ :=
    derivationFormTree_split_append g (xs := r.output) (ys := q) hrest
  simpa [List.append_assoc] using
    derivationFormTree_append g hp
      (DerivationFormTree.cons (DerivationSymbolTree.nonterminal r hr hout) hq)

theorem derivationFormTree_of_derives
    (g : ContextFreeGrammar T) {xs : List (Symbol T g.NT)} {w : List T}
    (h : g.Derives xs (terminalSymbols w)) :
    DerivationFormTree g xs w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact derivationFormTree_terminals g w
  | head hstep hrest ih => exact derivationFormTree_of_produces g hstep ih

```

## 逆方向：導出のシミュレーションの持ち上げ

最後に逆方向として、先頭記号への導出と残りの文への導出を独立に行った結果を連結できること（`derives_cons_of`）を確認し、これを用いて「一歩の生成規則がターゲット文法の導出をシミュレートする」という仮定から「任意の導出全体のシミュレーションが従う」こと（`derives_lift_of_produces`）を示す。これは正規形変換などで規則ごとの対応を文法全体の言語保存へ一般化する際の共通部品として使われる。

```lean
private theorem derives_cons_of
    (g : ContextFreeGrammar T)
    {x : Symbol T g.NT} {u : List T}
    {xs : List (Symbol T g.NT)} {v : List T}
    (hx : g.Derives [x] (terminalSymbols u))
    (ht : g.Derives xs (terminalSymbols v)) :
    g.Derives (x :: xs) (terminalSymbols (u ++ v)) := by
  have h₁ := hx.append_right xs
  have h₂ := ht.append_left (terminalSymbols u)
  simpa [terminalSymbols, List.map_append, List.append_assoc] using h₁.trans h₂

/-- Lift a simulation of source production steps to complete derivations. -/
theorem derives_lift_of_produces
    {g₁ : ContextFreeGrammar T} {g₂ : ContextFreeGrammar T}
    {mapSym : Symbol T g₁.NT → Symbol T g₂.NT}
    (hstep : ∀ {u v}, g₁.Produces u v →
      g₂.Derives (u.map mapSym) (v.map mapSym)) :
    ∀ {u v}, g₁.Derives u v →
      g₂.Derives (u.map mapSym) (v.map mapSym) := by
  intro u v h
  induction h with
  | refl => exact ContextFreeGrammar.Derives.refl _
  | tail hxy hyz ih => exact ih.trans (hstep hyz)

end ContextFreeGrammar
end Mathling.Grammar

```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
