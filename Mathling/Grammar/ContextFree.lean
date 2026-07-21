    module

    public import Mathling.Grammar.Core
    public import Mathlib.Data.Finset.Union
    public import Mathlib.Data.List.Sublists

    import LiterateLean
    open scoped LiterateLean


# Mathling / Grammar / ContextFree モジュール

文脈自由文法の有限台を抽出し、導出を構造化した証拠木へ変換する補助理論を提供する。有限性の計算可能な境界と、通常の書換え導出と木構造意味論の往復が、後続のオートマトン変換の基盤になる。

`rhsNonterminals` は文中に現れる非終端記号を出現順に取り出す走査関数であり、以降で構成する有限台や証拠木の基礎となる。これが非終端記号だけを順序を保って正しく収集することが、次に定義する `ContextFreeRule.nonterminals` や `activeNonterminals` の正しさの前提になる。

```lean

/-!
# Context-free grammar support

Shared finite-support and derivation utilities used by normal-form conversions.
The semantic notions of rewriting, derivation, and language remain Mathlib's
`ContextFreeGrammar` notions.
-/



namespace Mathling.Grammar

/-- Nonterminals occurring in a sentential form, in their original order. -/
public def rhsNonterminals {T N : Type*} : List (Symbol T N) → List N
  | [] => []
  | Symbol.terminal _ :: xs => rhsNonterminals xs
  | Symbol.nonterminal A :: xs => A :: rhsNonterminals xs

```

`ContextFreeRule.nonterminals` は `rhsNonterminals` を用いて、規則の左辺 `input` と右辺に現れる非終端記号をまとめて列挙する。これにより「その規則が言及する非終端記号」が一つの値として取り出せるようになり、次節の文法全体の有限台の定義が、規則ごとのこの列挙の単純な合併として書ける。

```lean
namespace ContextFreeRule

/-- The input and all right-hand-side nonterminals of a rule. -/
public def nonterminals {T N : Type*} (r : ContextFreeRule T N) : List N :=
  r.input :: rhsNonterminals r.output
```

`Rewrites.mapNonterminal` は、非終端記号の名前替え `f` が一歩の書き換え関係と可換であることを示す：規則 `r` による書き換えを `f` で写した結果は、写された規則 `ContextFreeRule.mapNonterminal f r` による書き換えと一致する。この可換性がなければ、非終端記号を付け替える文法変換（正規形変換など）が書き換え関係を保つことを変換のたびに個別に証明し直す必要が生じる。

```lean
/-- Renaming nonterminals preserves a one-rule rewrite. -/
@[grind .] public theorem Rewrites.mapNonterminal {T N M : Type*}
    {r : ContextFreeRule T N} {u v : List (Symbol T N)}
    (h : r.Rewrites u v) (f : N → M) :
    (ContextFreeRule.mapNonterminal f r).Rewrites
      (u.map (Symbol.mapNonterminal f))
      (v.map (Symbol.mapNonterminal f)) := by
  induction h with
  | head s =>
      simpa [ContextFreeRule.mapNonterminal, List.map_append] using
        (ContextFreeRule.Rewrites.head
          (r := ContextFreeRule.mapNonterminal f r)
          (s.map (Symbol.mapNonterminal f)))
  | cons x h ih =>
      exact ContextFreeRule.Rewrites.cons (Symbol.mapNonterminal f x) ih

end ContextFreeRule
```

## 有限台の抽出

`rhsNonterminals` は文中に現れる非終端記号を出現順に取り出す走査であり、`ContextFreeRule.nonterminals` はそれに規則の左辺 `input` を先頭として加えたものである。これらを部品として、次節では文法全体が実際に参照する非終端記号の有限集合を構成する。

以下、`ContextFreeGrammar` 名前空間の中で文法全体の有限台を定義する。

```lean
namespace ContextFreeGrammar

```

`activeNonterminals g` は、初期記号と全規則の入出力に現れる非終端記号を合わせた有限集合であり、文法 `g` が実際に「言及する」非終端記号だけを過不足なく捉える。この集合が有限であること自体が、後続の正規形変換で非終端記号の一覧を計算的に扱うための土台になる。もし文法の台が無限であり得るなら、こうした変換アルゴリズムはそもそも構成できない。

```lean
variable {T N : Type*}

/-- The finite support explicitly mentioned by a grammar. -/
public def activeNonterminals (g : ContextFreeGrammar T) [DecidableEq g.NT] : Finset g.NT :=
  {g.initial} ∪ g.rules.biUnion fun r =>
    (ContextFreeRule.nonterminals r).toFinset

```

`initial_mem_activeNonterminals` は、初期記号が定義から自明にこの有限集合へ含まれることを確認する、最も基本的な所属補題である。

```lean
@[grind ., simp] public theorem initial_mem_activeNonterminals (g : ContextFreeGrammar T)
    [DecidableEq g.NT] :
    g.initial ∈ activeNonterminals g := by
  classical
  simp [activeNonterminals]

```

`rule_input_mem_activeNonterminals` は、文法の各規則の左辺非終端記号が `activeNonterminals` に属することを示す。規則を有限個列挙するだけでは、その左辺が「文法の台」に含まれることは定義から自動的には従わないため、この補題が両者を結びつける。

```lean
@[grind =>] public theorem rule_input_mem_activeNonterminals (g : ContextFreeGrammar T)
    [DecidableEq g.NT]
    {r : ContextFreeRule T g.NT} (hr : r ∈ g.rules) :
    r.input ∈ activeNonterminals g := by
  classical
  simp only [activeNonterminals, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_biUnion]
  right
  exact ⟨r, hr, by simp [ContextFreeRule.nonterminals]⟩

```

次の `rule_rhs_mem_activeNonterminals` の証明に使う補助として、まず `rhsNonterminals` の構造的な性質を確立する：ある非終端記号が文中に（`Symbol.nonterminal` として）出現するなら、`rhsNonterminals` による走査でも必ずその記号が取り出されることを示す。

```lean
@[grind .] private theorem mem_rhsNonterminals_of_nonterminal_mem
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

```

`rule_rhs_mem_activeNonterminals` は、規則の右辺に現れる非終端記号もまた `activeNonterminals` に属することを、直前の補助補題を使って示す。`rule_input_mem_activeNonterminals` と合わせて、規則の左右両辺のすべての非終端記号がこの有限集合に収まることが保証される。

```lean
@[grind =>] public theorem rule_rhs_mem_activeNonterminals (g : ContextFreeGrammar T)
    [DecidableEq g.NT]
    {r : ContextFreeRule T g.NT} {A : g.NT} (hr : r ∈ g.rules)
    (hA : Symbol.nonterminal A ∈ r.output) :
    A ∈ activeNonterminals g := by
  classical
  simp only [activeNonterminals, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_biUnion]
  right
  refine ⟨r, hr, ?_⟩
  simp only [List.mem_toFinset, ContextFreeRule.nonterminals, List.mem_cons]
  exact Or.inr (mem_rhsNonterminals_of_nonterminal_mem hA)

```

## 文法の有限台とその所属補題

`activeNonterminals g` は初期記号と全規則の入出力に現れる非終端記号を合わせた有限集合であり、文法 `g` が実際に参照する非終端記号だけを過不足なく捉える。`initial_mem_activeNonterminals`・`rule_input_mem_activeNonterminals`・`rule_rhs_mem_activeNonterminals` はそれぞれ、初期記号・各規則の左辺・各規則の右辺に現れる非終端記号がこの集合に属することを保証し、内部の `mem_rhsNonterminals_of_nonterminal_mem` はそのうち右辺に関するものを `rhsNonterminals` の構造的な性質として支える。

次に、終端記号列だけからなる文に関する基本的な性質を確立する。`terminalSymbols_injective` は、終端記号だけへの埋め込み `terminalSymbols` が単射であることを示す。これは、書き換え結果を語として一意に読み取るための前提であり、次の `derives_terminals_eq` で「導出しても語が変わらない」ことを示す際に使われる。

```lean
/-- Terminal embedding is injective. -/
@[grind .] public theorem terminalSymbols_injective {u v : List T} :
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
```

`no_rewrites_terminals` は、終端記号だけからなる文が文脈自由規則によって一切書き換えられないことを示す。非終端記号を持たない文にはもう展開の余地がない、という直感を形式化しており、次の `derives_terminals_eq` で「導出列の最初の一歩」を排除する場合分けに使われる。

```lean
/-- A context-free rule cannot rewrite a terminal-only sentential form. -/
@[grind .] public theorem no_rewrites_terminals (r : ContextFreeRule T N) {w : List T}
    {v : List (Symbol T N)} :
    r.Rewrites (terminalSymbols w) v → False := by
  intro h
  induction w generalizing v with
  | nil => cases h
  | cons a w ih =>
      cases h with
      | cons _ htail => exact ih htail
```

`derives_terminals_eq` は、終端記号列同士の導出が実は同じ語を保つことを示す：導出が空でなければ最初の一歩が `no_rewrites_terminals` により矛盾するため導出は反射的でしかあり得ず、`terminalSymbols_injective` により語が一致する。この事実は、後の証拠木の構成（`derivationFormTree_terminals`）で「これ以上導出が進まない」終端状態を扱う際の基盤になる。

```lean
/-- A derivation between terminal-only forms does not change the word. -/
@[grind .] public theorem derives_terminals_eq (g : ContextFreeGrammar T) {u v : List T} :
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
  public inductive DerivationSymbolTree (g : ContextFreeGrammar T) :
      Symbol T g.NT → List T → Prop
    | terminal (a : T) : DerivationSymbolTree g (.terminal a) [a]
    | nonterminal (r : ContextFreeRule T g.NT) (hr : r ∈ g.rules)
        {w : List T} (children : DerivationFormTree g r.output w) :
        DerivationSymbolTree g (.nonterminal r.input) w

  public inductive DerivationFormTree (g : ContextFreeGrammar T) :
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
@[grind .] private theorem derivationFormTree_append (g : ContextFreeGrammar T)
    {xs ys : List (Symbol T g.NT)} {u v : List T}
    (hx : DerivationFormTree g xs u) (hy : DerivationFormTree g ys v) :
    DerivationFormTree g (xs ++ ys) (u ++ v) := by
  cases hx with
  | nil => simpa using hy
  | cons head tail =>
      simpa [List.append_assoc] using
        DerivationFormTree.cons head (derivationFormTree_append g tail hy)
termination_by xs.length

```

`derivationFormTree_split_append` は `derivationFormTree_append` の逆方向であり、連接された文 `xs ++ ys` への証拠木が与えられたとき、それを `xs` への証拠木と `ys` への証拠木、およびそれぞれが生成する語 `u`・`v`（`w = u ++ v`）へ一意に分解する。この分解が、次節で一歩の書き換え `Produces` を証拠木へ翻訳する際に、書き換えられた部分だけを取り出す道具として使われる。

```lean
@[grind .] private theorem derivationFormTree_split_append (g : ContextFreeGrammar T)
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
@[grind .] private theorem derivationFormTree_terminals (g : ContextFreeGrammar T)
    (w : List T) : DerivationFormTree g (terminalSymbols w) w := by
  induction w with
  | nil => exact DerivationFormTree.nil
  | cons a w ih =>
      simpa [terminalSymbols] using
        DerivationFormTree.cons (DerivationSymbolTree.terminal a) ih

```

`derivationFormTree_of_produces` は、一歩の生成 `Produces u v` と `v` への証拠木から `u` への証拠木を構成する。`hstep.exists_parts` で書き換え箇所の前後 `p`・`q` を取り出し、`derivationFormTree_split_append` で証拠木をその境目ごとに分解し、書き換えられた非終端記号の位置を規則適用ノード（`DerivationSymbolTree.nonterminal`）に置き換えてから `derivationFormTree_append` で貼り戻す。この一段階の変換が、次の `derivationFormTree_of_derives` で導出列全体を畳み込むための帰納法の核となる。

```lean
@[grind .] private theorem derivationFormTree_of_produces
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

```

`derivationFormTree_of_derives` は、任意の終端記号列への導出 `Derives` から証拠木を構成する、この節の目標である。`Derives` が反射推移閉包であることを使い、`Relation.ReflTransGen.head_induction_on` で先頭の一歩ずつ `derivationFormTree_of_produces` を適用していくことで、導出列全体に対応する証拠木を組み立てる。

```lean
@[grind .] public theorem derivationFormTree_of_derives
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
@[grind .] public theorem derives_cons_of
    (g : ContextFreeGrammar T)
    {x : Symbol T g.NT} {u : List T}
    {xs : List (Symbol T g.NT)} {v : List T}
    (hx : g.Derives [x] (terminalSymbols u))
    (ht : g.Derives xs (terminalSymbols v)) :
    g.Derives (x :: xs) (terminalSymbols (u ++ v)) := by
  have h₁ := hx.append_right xs
  have h₂ := ht.append_left (terminalSymbols u)
  simpa [terminalSymbols, List.map_append, List.append_assoc] using h₁.trans h₂
```

`derives_lift_of_produces` は、生成規則ごとの対応（`g₁` の一歩の生成を `g₂` の導出でシミュレートできるという仮定 `hstep`）を、`g₁` の任意の導出全体のシミュレーションへ持ち上げる。`Derives` の反射推移閉包上の帰納法により、`refl` の場合は自明に、`tail` の場合は直前までのシミュレーションと最後の一歩のシミュレーションを推移性でつなぐ。正規形変換などで「規則ごとに言語保存を示せば文法全体の言語保存が従う」という議論を、この補題一つに集約できる。

```lean
/-- Lift a simulation of source production steps to complete derivations. -/
@[grind .] public theorem derives_lift_of_produces
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
