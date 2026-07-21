    module

    public import Mathling.Grammar.ContextFree
    public import Mathling.Automata.Pushdown
    public import Mathling.Meta.Important

    import LiterateLean
    open scoped LiterateLean


# Mathling / Grammar / Pushdown モジュール

文脈自由文法と有限局所 NPDA の間の変換を与える。文法から機械への変換では、
文型をそのままスタックへ置き、生成規則を ε 遷移、終端記号の照合を入力消費遷移にする。
bottom 記号だけが残ったときに専用受理状態へ移るため、公開される最終状態受理と
文法の完全導出が一致する。

以下の空フェンスは、実行可能な宣言を含まない構造上の区切りである。ヘッダー直後に
置くことで、モジュール冒頭の説明文と最初の名前空間宣言とを別々の Lean フェンスへ
分離し、各フェンスが単一の宣言（またはその欠如）に対応するという分割規約を保つ。

```lean

```

`Mathling.Grammar` 名前空間を開く。これ以降の直接構成（文法から NPDA へ）に関する
定義・補題はすべてこの名前空間の下、特に `ContextFreeGrammar` の拡張として置かれる。

```lean
namespace Mathling.Grammar

```

GrammarPDAState は直接構成で使う制御状態をちょうど二つに限定する：`run` は文法の
文型をスタック上でまだ書き換えている途中を表し、`done` は bottom 記号を取り除いた
後にだけ到達できる専用の受理状態である。状態をこの二つだけに絞ることで、
受理条件（最終状態が `done` であること）とスタックが bottom だけになったことが
同義になるという後段の証明の要となる不変量が成り立つ。

```lean
open Mathling.Automata

/-- Control states of the direct grammar-to-PDA construction. -/
@[grind cases] public inductive GrammarPDAState where
  | run
  | done
  deriving Repr, DecidableEq
```

スタックのアルファベットは文法記号（終端・非終端）そのものに、私的な bottom 記号を
足したものである。文型を一切符号化し直さずスタックへそのまま積めるため、後段の
`encodeForm` は単なる `List.map` で済み、文型と符号化されたスタックとの間の
往復がほぼ定義的に成り立つ。

```lean
/-- Grammar symbols plus a private bottom marker. -/
@[grind cases] public inductive GrammarPDAStack (T N : Type*) where
  | bottom
  | symbol (value : Symbol T N)
  deriving Repr
```

以降の定義・補題は `ContextFreeGrammar` の名前空間の下に置き、`g.toNPDA` のように
文法の値からドット記法で呼び出せるようにする。

```lean
namespace ContextFreeGrammar

```

以降のセクションでは終端記号の型 `T` を固定し、決定可能性を要求しない
`noncomputable section` の下で構成を進める（有限集合上の `Finset` 演算を直接使うため）。
rhsTerminals は一つの文型 `xs` に現れる終端記号だけを、非終端記号を無視しつつ左から
順に取り出す補助関数であり、繰り返しも保持する。これは `terminalRule` を文法規則ごとに
一つずつ生成するのではなく、実際に必要な入力記号の集合を絞り込むための下請けである。

```lean
variable {T : Type*}

noncomputable section

/-- Terminals mentioned by a sentential form, preserving repetitions. -/
public def rhsTerminals {N : Type*} : List (Symbol T N) → List T
  | [] => []
  | .terminal a :: xs => a :: rhsTerminals xs
  | .nonterminal _ :: xs => rhsTerminals xs
```

terminalSupport は文法の全規則の右辺を rhsTerminals で舐め、実際に構文に現れる
終端記号だけを集めた有限リストである。`toNPDA` はこのリストの要素ごとに一つずつ
`terminalRule` を生成するので、terminalSupport が文法規則から到達可能な終端記号を
すべて（かつそれだけを）含むことが、後の `output_supported` や `terminalRule_mem` の
土台になる。

```lean
/-- The finite list of terminals explicitly mentioned by grammar rules. -/
public def terminalSupport (g : ContextFreeGrammar T) : List T :=
  g.rules.toList.flatMap fun r => rhsTerminals r.output
```

expansionRule は文法規則 `r` を一つの ε 遷移へ翻訳する：スタック先頭の非終端記号
`r.input` を取り除き、その代わりに右辺 `r.output` を符号化して積み直す。入力記号を
消費しない（`input := none`）ことと、制御状態が `run` のまま変わらないことが、
文法の書き換えがスタック操作だけで完結し、機械の状態遷移とは独立であるという
直接構成の基本アイデアを体現している。

```lean
public def expansionRule {g : ContextFreeGrammar T}
    (r : ContextFreeRule T g.NT) :
    PushdownRule T GrammarPDAState (GrammarPDAStack T g.NT) where
  source := .run
  input := none
  pop := .symbol (.nonterminal r.input)
  target := .run
  push := r.output.map GrammarPDAStack.symbol
```

terminalRule は文法が実際に生成しうる終端記号 `a` それぞれについて、入力から `a` を
一文字読み、スタック上の対応する終端記号を取り除く消費遷移を与える。文型に現れる
終端記号とスタックに積まれた終端記号が常に一致していることが保たれるのは、
`expansionRule` がスタックへ積む終端記号と、ここで照合対象にする終端記号が
同じ符号化 `GrammarPDAStack.symbol` を経由するためである。

```lean
public def terminalRule (g : ContextFreeGrammar T) (a : T) :
    PushdownRule T GrammarPDAState (GrammarPDAStack T g.NT) where
  source := .run
  input := some a
  pop := .symbol (.terminal a)
  target := .run
  push := []
```

finishRule は唯一 `run` から `done` へ抜け出す遷移であり、スタックに bottom 記号
だけが残っている場合にのみ発火する。文型がすべて終端記号へ書き換えられ
消費し尽くされて初めてスタックが空に近い状態（bottom のみ）になるため、この遷移が
可能であることが「文法が完全に導出を終えた」ことの機械側での表現になる。

```lean
public def finishRule (g : ContextFreeGrammar T) :
    PushdownRule T GrammarPDAState (GrammarPDAStack T g.NT) where
  source := .run
  input := none
  pop := .bottom
  target := .done
  push := []
```

toNPDA はここまでの三種類の遷移（expansionRule・terminalRule・finishRule）を
それぞれ規則ごと・終端記号ごとに列挙して合わせ、初期スタックを開始記号と bottom の
符号化とすることで、文法全体を一つの有限局所 NPDA へ組み立てる。この機械の言語が
文法の言語に一致することが `toNPDA_language` の主張であり、以降の補題群は
すべてこの一致を示すための積み上げである。

```lean
/-- Directly convert a context-free grammar to a finite local NPDA. -/
public def toNPDA (g : ContextFreeGrammar T) :
    NPDA T GrammarPDAState (GrammarPDAStack T g.NT) where
  rules := g.rules.toList.map expansionRule ++
    (terminalSupport g).map (terminalRule g) ++ [finishRule g]
  start := [.run]
  accept := [.done]
  initialStack := [.symbol (.nonterminal g.initial), .bottom]
```

encodeForm は一つの文型をスタック語へ翻訳する変換であり、`GrammarPDAStack.symbol`
を各記号にかぶせるだけの単純な写像である。以降の健全性の証明では、文型を直接
扱う代わりに常にこの符号化を経由してスタックと比較するため、encodeForm が
単射的かつ構造を保つことが暗黙の前提になる。

```lean
public def encodeForm {N : Type*} (xs : List (Symbol T N)) :
    List (GrammarPDAStack T N) := xs.map GrammarPDAStack.symbol
```

Supported は一つの記号が `toNPDA g` の遷移だけで実際に処理できることを表す述語で、
終端記号については terminalSupport に属することを要求し、非終端記号は常に許す。
文法規則の右辺に現れる記号がすべて Supported であること（`output_supported`）を
帰納法の仮定として使うことで、`formTree_reaches` は任意の導出木がちょうど対応する
NPDA の実行へ翻訳できることを示せる。

```lean
public def Supported (g : ContextFreeGrammar T) : Symbol T g.NT → Prop
  | .terminal a => a ∈ terminalSupport g
  | .nonterminal _ => True
```

mem_rhsTerminals は rhsTerminals が右辺に現れる終端記号を漏らさず拾うことを示す
補助補題であり、次の output_supported がこれを使って規則の右辺全体の Supported 性を
導く際の帰納法の受け皿になる。

```lean
@[grind .] theorem mem_rhsTerminals {N : Type*} {a : T}
    {xs : List (Symbol T N)} (h : Symbol.terminal a ∈ xs) :
    a ∈ rhsTerminals xs := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
      cases x with
      | terminal b =>
          rcases List.mem_cons.mp h with h | h
          · cases h; simp [rhsTerminals]
          · simp [rhsTerminals, ih h]
      | nonterminal B =>
          rcases List.mem_cons.mp h with h | h
          · cases h
          · simpa [rhsTerminals] using ih h

```

output_supported は文法規則 `r` の右辺に現れる記号がすべて Supported であることを
mem_rhsTerminals を使って示す。これにより、規則を一段展開しても
Supported という不変量が失われないことが保証され、導出木の帰納法をこの仮定つきで
最後まで回せるようになる。

```lean
@[grind .] theorem output_supported (g : ContextFreeGrammar T)
    {r : ContextFreeRule T g.NT} (hr : r ∈ g.rules) :
    ∀ x ∈ r.output, Supported g x := by
  intro x hx
  cases x with
  | nonterminal => simp [Supported]
  | terminal a =>
      simp only [Supported, terminalSupport, List.mem_flatMap]
      refine ⟨r, ?_, ?_⟩
      · simpa using hr
      · exact mem_rhsTerminals hx

```

expansionRule_mem・terminalRule_mem・finishRule_mem の三つは、それぞれの遷移生成関数が
実際に `toNPDA g` の規則リストへ属することを確認するだけの補題だが、この後の
`toNPDARule_cases` による逆向きの場合分け（ある規則が toNPDA の規則である「ならば」
それは三種類のいずれかの形をしている、という主張）と対をなし、両方向の同値を
成立させるために欠かせない。expansionRule_mem は文法規則ごとの ε 遷移について示す。

```lean
@[grind .] theorem expansionRule_mem (g : ContextFreeGrammar T)
    {r : ContextFreeRule T g.NT} (hr : r ∈ g.rules) :
    expansionRule r ∈ (toNPDA g).rules := by
  simp only [toNPDA, List.mem_append, List.mem_map, Finset.mem_toList]
  exact Or.inl (Or.inl ⟨r, hr, rfl⟩)

```

terminalRule_mem は同じ確認を、終端記号の消費遷移について行う（`a` が
terminalSupport に属することが前提）。

```lean
@[grind .] theorem terminalRule_mem (g : ContextFreeGrammar T)
    {a : T} (ha : a ∈ terminalSupport g) :
    terminalRule g a ∈ (toNPDA g).rules := by
  simp only [toNPDA, List.mem_append, List.mem_map]
  exact Or.inl (Or.inr ⟨a, ha, rfl⟩)

```

finishRule_mem は唯一の受理遷移 finishRule g が toNPDA の規則リストの末尾に
実際に含まれることを示す、三つ組のうち最後の確認である。

```lean
@[grind .] theorem finishRule_mem (g : ContextFreeGrammar T) :
    finishRule g ∈ (toNPDA g).rules := by
  simp [toNPDA]

```

導出木の各節点は、対応するスタック区間をちょうど取り除く実行へ翻訳できる。
接尾スタックを一切観測しない局所性により、子の実行を左から順に連結できる。

```lean
@[grind .] theorem formTree_reaches (g : ContextFreeGrammar T)
    {xs : List (Symbol T g.NT)} {w : List T}
    (tree : DerivationFormTree g xs w)
    (hs : ∀ x ∈ xs, Supported g x)
    (rest : List T) (suffix : List (GrammarPDAStack T g.NT)) :
    (toNPDA g).Reaches
      (w ++ rest, .run, encodeForm xs ++ suffix)
      (rest, .run, suffix) := by
  refine DerivationFormTree.rec (g := g)
    (motive_1 := fun x w _ =>
      ∀ (_ : Supported g x) (rest : List T)
        (suffix : List (GrammarPDAStack T g.NT)),
        (toNPDA g).Reaches
          (w ++ rest, .run, .symbol x :: suffix)
          (rest, .run, suffix))
    (motive_2 := fun xs w _ =>
      ∀ (_ : ∀ x ∈ xs, Supported g x) (rest : List T)
        (suffix : List (GrammarPDAStack T g.NT)),
        (toNPDA g).Reaches
          (w ++ rest, .run, encodeForm xs ++ suffix)
          (rest, .run, suffix))
    ?_ ?_ ?_ ?_ tree hs rest suffix
  · intro a hs rest suffix
    apply Relation.ReflTransGen.single
    exact NPDA.Step.consume (terminalRule g a)
      (terminalRule_mem g hs) rfl
  · intro r hr w children ih hs rest suffix
    have first : (toNPDA g).Step
        (w ++ rest, .run, .symbol (.nonterminal r.input) :: suffix)
        (w ++ rest, .run, encodeForm r.output ++ suffix) := by
      simpa [expansionRule, encodeForm] using NPDA.Step.epsilon (expansionRule r)
        (expansionRule_mem g hr) rfl
    exact (ih (output_supported g hr) rest suffix).head first
  · intro hs rest suffix
    exact Relation.ReflTransGen.refl
  · intro x u xs v head tail ihHead ihTail hs rest suffix
    have hx : Supported g x := hs x (by simp)
    have hxs : ∀ y ∈ xs, Supported g y := by
      intro y hy
      exact hs y (by simp [hy])
    have hhead := ihHead hx (v ++ rest) (encodeForm xs ++ suffix)
    have htail := ihTail hxs rest suffix
    simpa [encodeForm, List.append_assoc] using hhead.trans htail

```

generates_reaches は formTree_reaches を文法全体の導出木（開始記号一つからなる
文型）に適用し、末尾の finishRule による一回の遷移を継ぎ足すことで、文法が語 `w`
を生成するならば toNPDA g の初期配置から受理配置 `([], .done, [])` へちょうど
到達できることを結論する。これが健全性方向（文法の言語 ⊆ 機械の言語）の核心である。

```lean
@[grind .] theorem generates_reaches (g : ContextFreeGrammar T) {w : List T}
    (h : w ∈ g.language) :
    (toNPDA g).Reaches
      (w, .run, [.symbol (.nonterminal g.initial), .bottom])
      ([], .done, []) := by
  have tree := derivationFormTree_of_derives g h
  have hform := formTree_reaches g tree (by
    intro x hx
    simp only [List.mem_singleton] at hx
    subst x
    simp [Supported]) [] [.bottom]
  have hfinish : (toNPDA g).Step ([], .run, [.bottom]) ([], .done, []) := by
    simpa [finishRule] using
      NPDA.Step.epsilon (finishRule g) (finishRule_mem g) rfl
  simpa [encodeForm] using hform.tail hfinish

```

逆包含では、run 状態のスタックが常にある文型の符号化と bottom の連結であり、
入力から既に消費した接頭辞とその文型の連結が開始記号から導出可能であることを保つ。
done 状態へ移れるのは文型が空になった場合だけである。

```lean
@[grind .] theorem toNPDARule_cases (g : ContextFreeGrammar T)
    {r : PushdownRule T GrammarPDAState (GrammarPDAStack T g.NT)}
    (hr : r ∈ (toNPDA g).rules) :
    (∃ gr ∈ g.rules, r = expansionRule gr) ∨
    (∃ a ∈ terminalSupport g, r = terminalRule g a) ∨
    r = finishRule g := by
  simp only [toNPDA, List.mem_append, List.mem_map, List.mem_singleton] at hr
  rcases hr with (⟨gr, hgr, hEq⟩ | ⟨a, ha, hEq⟩) | hEq
  · exact Or.inl ⟨gr, Finset.mem_toList.mp hgr, hEq.symm⟩
  · exact Or.inr (Or.inl ⟨a, ha, hEq.symm⟩)
  · exact Or.inr (Or.inr hEq)
```

GrammarRunGood はこれから示す逆包含（機械が受理する語は文法も生成する）の核心となる
不変量である。`run` 状態では、既に消費した入力の接頭辞 `consumed` と残りの文型 `form`
の組がスタック内容と対応し、かつ開始記号から `consumed` を終端記号列に見立てたものと
`form` の連結が導出可能であることを要求する。`done` 状態では文型が空であることまで
要求し、これがちょうど文法が語全体を導出し終えたことを意味する。

```lean
public def GrammarRunGood (g : ContextFreeGrammar T) (word : List T) :
    NPDA.ID T GrammarPDAState (GrammarPDAStack T g.NT) → Prop
  | (input, .run, stack) =>
      ∃ consumed form,
        word = consumed ++ input ∧
        stack = encodeForm form ++ [.bottom] ∧
        g.Derives [.nonterminal g.initial]
          (terminalSymbols consumed ++ form)
  | (input, .done, stack) =>
      ∃ consumed,
        word = consumed ++ input ∧ stack = [] ∧
        g.Derives [.nonterminal g.initial] (terminalSymbols consumed)
```

encoded_cons_parts と bottom_parts は、GrammarRunGood の中で仮定されている
「スタックが encodeForm form ++ [.bottom] の形をしている」という等式から、
スタックの先頭を機械的に剥がして対応する文型の情報を取り出すための下請け補題である。
encoded_cons_parts はスタック先頭が符号化された記号である場合を扱い、対応する文型
`form` が空でないこと、その先頭が同じ記号であることを取り出す。

```lean
@[grind .] private theorem encoded_cons_parts (g : ContextFreeGrammar T)
    {x : Symbol T g.NT} {rest : List (GrammarPDAStack T g.NT)}
    {form : List (Symbol T g.NT)}
    (h : GrammarPDAStack.symbol x :: rest =
      encodeForm form ++ [.bottom]) :
    ∃ tail, form = x :: tail ∧ rest = encodeForm tail ++ [.bottom] := by
  cases form with
  | nil => simp [encodeForm] at h
  | cons y ys =>
      simp only [encodeForm, List.map_cons, List.cons_append] at h
      obtain ⟨hy, hrest⟩ := List.cons.inj h
      cases hy
      exact ⟨ys, rfl, hrest⟩

```

bottom_parts は対になる場合、すなわちスタック先頭が bottom 記号そのものである場合を
扱い、そのときは対応する文型が既に空でなければならないことを示す。この二つの補題が
揃って初めて、`grammarStep_good` はスタックの形についての場合分けを尽くせる。

```lean
@[grind .] private theorem bottom_parts (g : ContextFreeGrammar T)
    {rest : List (GrammarPDAStack T g.NT)} {form : List (Symbol T g.NT)}
    (h : GrammarPDAStack.bottom :: rest =
      encodeForm form ++ [.bottom]) :
    form = [] ∧ rest = [] := by
  cases form with
  | nil => simpa [encodeForm] using h
  | cons x xs =>
      simp only [encodeForm, List.map_cons, List.cons_append] at h
      cases x <;> cases (List.cons.inj h).1

```

grammarStep_good と grammarReaches_good は、GrammarRunGood が実際に不変量であることを示す。
前者は toNPDARule_cases による三通りの場合分けに沿って一回の遷移で GrammarRunGood が
保たれることを確認し、encoded_cons_parts と bottom_parts はそのためにスタックの先頭を
機械的に剥がす補助補題である。後者は Reaches の反射推移閉包に沿ってこれを繰り返し
適用するだけである。

```lean
@[grind .] theorem grammarStep_good (g : ContextFreeGrammar T) (word : List T)
    {c c' : NPDA.ID T GrammarPDAState (GrammarPDAStack T g.NT)}
    (h : (toNPDA g).Step c c') :
    GrammarRunGood g word c → GrammarRunGood g word c' := by
  cases h with
  | @consume a input rest r hr ha =>
      rcases toNPDARule_cases g hr with
        ⟨gr, hgr, rfl⟩ | ⟨b, hb, rfl⟩ | rfl
      · simp [expansionRule] at ha
      · simp only [terminalRule, Option.some.injEq] at ha
        subst a
        rintro ⟨consumed, form, hword, hstack, hderives⟩
        obtain ⟨tail, rfl, hrest⟩ := encoded_cons_parts g hstack
        refine ⟨consumed ++ [b], tail, ?_, ?_, ?_⟩
        · simpa [List.append_assoc] using hword
        · simpa [terminalRule] using hrest
        · simpa [terminalSymbols, List.map_append, List.append_assoc] using hderives
      · simp [finishRule] at ha
  | @epsilon input rest r hr ha =>
      rcases toNPDARule_cases g hr with
        ⟨gr, hgr, rfl⟩ | ⟨a, haSupport, rfl⟩ | rfl
      · rintro ⟨consumed, form, hword, hstack, hderives⟩
        obtain ⟨tail, hform, hrest⟩ := encoded_cons_parts g hstack
        subst form
        have hproduces : g.Produces
            (terminalSymbols consumed ++ .nonterminal gr.input :: tail)
            (terminalSymbols consumed ++ (gr.output ++ tail)) := by
          refine ⟨gr, hgr, ?_⟩
          simpa [List.append_assoc] using
            (ContextFreeRule.Rewrites.head tail).append_left
              (terminalSymbols consumed)
        refine ⟨consumed, gr.output ++ tail, hword, ?_,
          hderives.trans_produces hproduces⟩
        simpa [expansionRule, encodeForm, List.map_append,
          List.append_assoc] using hrest
      · simp [terminalRule] at ha
      · rintro ⟨consumed, form, hword, hstack, hderives⟩
        obtain ⟨rfl, rfl⟩ := bottom_parts g hstack
        refine ⟨consumed, hword, ?_, ?_⟩
        · simp [finishRule]
        · simpa using hderives

```

grammarReaches_good は grammarStep_good を Reaches の反射推移閉包に沿って繰り返し
適用するだけの持ち上げであり、これによって GrammarRunGood が一回の遷移だけでなく
任意の長さの実行に沿って保存される不変量になる。

```lean
@[grind .] theorem grammarReaches_good (g : ContextFreeGrammar T) (word : List T)
    {c c' : NPDA.ID T GrammarPDAState (GrammarPDAStack T g.NT)}
    (h : (toNPDA g).Reaches c c') :
    GrammarRunGood g word c → GrammarRunGood g word c' := by
  induction h with
  | refl => exact id
  | tail h step ih => exact fun hc => grammarStep_good g word step (ih hc)

```

toNPDA_language はこの不変量を初期配置と受理配置に適用し、直接構成した NPDA の言語が
文法の言語とちょうど一致することを結論する。これで文法から機械への変換の正しさが完結する。

```lean
/-- The direct NPDA accepts exactly the language generated by the grammar. -/
@[important, grind =, simp] public theorem toNPDA_language (g : ContextFreeGrammar T) :
    (toNPDA g).language = g.language := by
  ext word
  constructor
  · rintro ⟨q₀, hq₀, qf, hqf, stack, hreach⟩
    have hq₀' : q₀ = .run := by
      simpa only [toNPDA, List.mem_singleton] using hq₀
    have hqf' : qf = .done := by
      simpa only [toNPDA, List.mem_singleton] using hqf
    subst q₀
    subst qf
    have hgood : GrammarRunGood g word
        ([], .done, stack) := grammarReaches_good g word hreach (by
      simpa [toNPDA] using
        (show GrammarRunGood g word
          (word, .run,
            [.symbol (.nonterminal g.initial), .bottom]) from
          ⟨[], [.nonterminal g.initial], by simp,
            by simp [encodeForm], Relation.ReflTransGen.refl⟩))
    rcases hgood with ⟨consumed, hword, _, hderives⟩
    simp only [List.append_nil] at hword
    subst consumed
    exact hderives
  · intro hword
    refine ⟨.run, by simp [toNPDA], .done, by simp [toNPDA], [], ?_⟩
    exact generates_reaches g hword

```

以降の Classical 名前空間は、decidable equality のインスタンスを要求しない選択公理版の
言い換えを与えるだけであり、内容上の新しい主張は無い。

```lean
namespace Classical

/-- Classical spelling of the direct conversion; no decidable equality is required. -/
public noncomputable abbrev toNPDA (g : ContextFreeGrammar T) :=
  _root_.Mathling.Grammar.ContextFreeGrammar.toNPDA g

```

この Classical.toNPDA についても toNPDA_language をそのまま書き写すだけであり、
decidable equality を要求しない呼び出し側から見た言い換えを提供する。

```lean
@[grind =, simp] theorem toNPDA_language (g : ContextFreeGrammar T) :
    (Classical.toNPDA g).language = g.language :=
  _root_.Mathling.Grammar.ContextFreeGrammar.toNPDA_language g

end Classical

end
end ContextFreeGrammar
end Mathling.Grammar

```

ここからは逆方向、すなわち有限局所 NPDA から文脈自由文法を構成する三つ組構成
（triple construction）を扱う。機械の各遷移と、その遷移が押し出すスタック語に整合する
制御状態の経路とを組にして、一つの文法規則へ翻訳するのが基本アイデアである。

`Mathling.Automata` 名前空間を開き、これ以降の逆方向構成を NPDA 側の拡張として
定義できるようにする。

```lean
namespace Mathling.Automata
```

三つ組構成それ自体は `NPDA` 名前空間の下に置き、`M.emptyToContextFreeGrammar` の
ように機械の値からドット記法で呼び出せるようにする。

```lean
namespace NPDA

```

`Mathling.Grammar` を開いて `ContextFreeGrammar` などの文法側の型をそのまま参照できる
ようにし、状態・記号の型が属する universe を `u` として固定する。

```lean
open Mathling.Grammar

universe u

```

ContextFreeNT は三つ組構成の非終端記号そのものであり、「source 状態からスタック記号
`pop` を一つ取り除いて target 状態へ至る」という機械側の局所的な遷移可能性を、
文法側の一つの記号として抽象化したものである。この対応関係が以降の segmentForm や
contextFreeRule、そして balanced_derives / balanced_of_derives による健全性・完全性の
議論全体を貫く基本の型になる。

```lean
variable {T : Type u} {State Stack : Type}

/-- Triple nonterminals: from state, removed stack symbol, and destination state. -/
@[ext] public structure ContextFreeNT (State Stack : Type) where
  source : State
  pop : Stack
  target : State
  deriving Repr, DecidableEq
```

listsOfLength は有限個の候補 `choices` からちょうど指定した長さの経路をすべて
列挙する組合せ的な補助関数であり、機械の制御状態が有限であることを
「候補の経路も有限個しかない」という事実へ変換するために使う。これがなければ
一つの遷移に整合する状態経路を存在量化のまま扱わねばならず、生成される文法規則を
有限集合として構成できない。

```lean
/-- Enumerate lists of a fixed length over a finite list of choices. -/
public def listsOfLength (choices : List State) : Nat → List (List State)
  | 0 => [[]]
  | n + 1 => choices.flatMap fun q =>
      (listsOfLength choices n).map (q :: ·)
```

stateSupport は開始状態・受理状態・全遷移の源泉と行き先から、機械に実際に現れる
制御状態だけを集めた有限リストである。listsOfLength と組み合わせることで、
「target 状態から到達しうる経路」を stateSupport 上の経路として有限に列挙できる。

```lean
/-- Control states explicitly occurring in a finite NPDA presentation. -/
public def stateSupport (M : NPDA T State Stack) : List State :=
  M.start ++ M.accept ++ M.rules.flatMap fun r => [r.source, r.target]
```

segmentForm は、ある制御状態の経路とそれに対応するスタック語を隣り合わせに並べ、
連続する二状態とその間で取り除かれるスタック記号から一つの ContextFreeNT を作り、
それらを列にする。これは一回の遷移が push する複数のスタック記号それぞれについて、
どの状態対の間でその記号が最終的に取り除かれるかを非決定的に選ぶ、という
三つ組構成の核心操作である。

```lean
/-- Adjacent triples determined by a control-state path and a stack word. -/
public def segmentForm : List State → List Stack →
    List (Symbol T (ContextFreeNT State Stack))
  | p :: q :: states, x :: stack =>
      .nonterminal ⟨p, x, q⟩ :: segmentForm (q :: states) stack
  | _, _ => []
```

contextFreeRule は一つの遷移 `r` とそれに整合する経路 `path` から、入力記号（あれば）
と push されたスタック語の segmentForm を右辺とする規則を一つ作る。左辺の非終端記号は
`⟨r.source, r.pop, path.getLastD r.target⟩` であり、経路が空でない限り最後の要素は
`r.target` に一致する。

```lean
/-- A transition and a compatible state path determine one grammar production. -/
public def contextFreeRule (r : PushdownRule T State Stack) (path : List State) :
    ContextFreeRule T (ContextFreeNT State Stack) where
  input := ⟨r.source, r.pop, path.getLastD r.target⟩
  output := r.input.toList.map Symbol.terminal ++ segmentForm path r.push
```

compatiblePaths は stateSupport の有限性を用いて listsOfLength で経路を列挙し、
先頭が遷移の target 状態と一致するものだけへ絞り込む。「先頭が target と一致する」
という条件は、target 状態から始めて push されたスタック記号を順に取り除いていく
という直感を経路として固定するためのものであり、これが後の balanced_derives・
contextFreeRule_meaning で経路の一意な復元を可能にする。

```lean
/-- State paths compatible with the pushed stack word of a transition. -/
public def compatiblePaths [DecidableEq State] (M : NPDA T State Stack)
    (r : PushdownRule T State Stack) : List (List State) :=
  (listsOfLength M.stateSupport (r.push.length + 1)).filter
    fun path => path.head? = some r.target
```

emptyToContextFreeGrammar は全ての遷移とそれぞれに整合する経路の組について
contextFreeRule を適用し、集めた有限集合を規則とする文法を組み立てる。開始記号を
指定した start・bottom・done から作った三つ組とすることで、この文法が生成する
文全体が、機械が start 状態から bottom 記号を取り除いて done 状態へ至る
Balanced な計算にちょうど対応するという同値（後の
`mem_emptyToContextFreeGrammar_language_iff`）が成り立つ土台になる。

```lean
/-- Triple-construction grammar for a machine whose accepting run removes one
distinguished initial stack symbol. -/
public def emptyToContextFreeGrammar [DecidableEq T] [DecidableEq State]
    [DecidableEq Stack] (M : NPDA T State Stack)
    (start : State) (bottom : Stack) (done : State) : ContextFreeGrammar T where
  NT := ContextFreeNT State Stack
  initial := ⟨start, bottom, done⟩
  rules := (M.rules.flatMap fun r =>
    (M.compatiblePaths r).map (contextFreeRule r)).toFinset
```

mem_listsOfLength は listsOfLength が「候補内の要素からなる、指定した長さの経路」を
すべて実際に列挙していることを示す、有限性の主張の存在方向である。

```lean
@[grind .] theorem mem_listsOfLength {choices path : List State} {n : Nat}
    (hlen : path.length = n) (hall : ∀ q ∈ path, q ∈ choices) :
    path ∈ listsOfLength choices n := by
  induction n generalizing path with
  | zero =>
      have : path = [] := List.eq_nil_of_length_eq_zero hlen
      subst path
      simp [listsOfLength]
  | succ n ih =>
      cases path with
      | nil => simp at hlen
      | cons q path =>
          simp only [List.length_cons] at hlen
          simp only [listsOfLength, List.mem_flatMap, List.mem_map]
          refine ⟨q, hall q (by simp), path, ?_, rfl⟩
          apply ih
          · omega
          · exact fun x hx => hall x (by simp [hx])

```

length_eq_of_mem_listsOfLength は逆方向、すなわち listsOfLength choices n に属する経路は
実際に長さ n しか持たないことを示し、mem_listsOfLength と合わせて listsOfLength の
仕様が過不足なく成り立つことを確定させる。

```lean
@[grind .] theorem length_eq_of_mem_listsOfLength {choices path : List State} {n : Nat}
    (h : path ∈ listsOfLength choices n) : path.length = n := by
  induction n generalizing path with
  | zero => simpa [listsOfLength] using h
  | succ n ih =>
      simp only [listsOfLength, List.mem_flatMap, List.mem_map] at h
      obtain ⟨q, hq, tail, htail, rfl⟩ := h
      simp [ih htail]

```

rule_source_mem_stateSupport は、どの遷移についてもその source 状態が stateSupport に
属することを述べる小さな事実だが、balanced_derives の帰納法の中で新しく現れる状態
（子計算の始点）が引き続き stateSupport に属することを確認するために使われる。

```lean
@[grind .] theorem rule_source_mem_stateSupport (M : NPDA T State Stack)
    {r : PushdownRule T State Stack} (hr : r ∈ M.rules) :
    r.source ∈ M.stateSupport := by
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨r, hr, by simp⟩

```

contextFreeRule_mem は emptyToContextFreeGrammar の定義を展開して、遷移と整合経路の
組から作った規則が実際に生成された文法の規則集合に属することを示す、存在方向の
確認である。

```lean
@[grind .] theorem contextFreeRule_mem [DecidableEq T] [DecidableEq State]
    [DecidableEq Stack] (M : NPDA T State Stack)
    {r : PushdownRule T State Stack} (hr : r ∈ M.rules)
    {path : List State} (hpath : path ∈ M.compatiblePaths r)
    {start bottom done} :
    contextFreeRule r path ∈
      (M.emptyToContextFreeGrammar start bottom done).rules := by
  change contextFreeRule r path ∈
    (M.rules.flatMap fun r =>
      (M.compatiblePaths r).map (contextFreeRule r)).toFinset
  rw [List.mem_toFinset]
  exact List.mem_flatMap.mpr ⟨r, hr,
    List.mem_map.mpr ⟨path, hpath, rfl⟩⟩

```

contextFreeRule_cases はその逆、生成された文法の規則ならば必ずある遷移とある整合経路
から contextFreeRule によって作られたことを示す、場合分け方向の主張である。この二つが
揃うことで、生成された文法の規則についての議論を機械の遷移と経路についての議論へ
自由に読み替えられるようになる。

```lean
@[grind .] theorem contextFreeRule_cases [DecidableEq T] [DecidableEq State]
    [DecidableEq Stack] (M : NPDA T State Stack)
    {start done : State} {bottom : Stack}
    {gr : ContextFreeRule T (ContextFreeNT State Stack)}
    (hgr : gr ∈ (M.emptyToContextFreeGrammar start bottom done).rules) :
    ∃ r ∈ M.rules, ∃ path ∈ M.compatiblePaths r,
      gr = contextFreeRule r path := by
  change gr ∈ (M.rules.flatMap fun r =>
    (M.compatiblePaths r).map (contextFreeRule r)).toFinset at hgr
  rw [List.mem_toFinset] at hgr
  obtain ⟨r, hr, hpath⟩ := List.mem_flatMap.mp hgr
  obtain ⟨path, hpath', heq⟩ := List.mem_map.mp hpath
  exact ⟨r, hr, path, hpath', heq.symm⟩

```

mem_listsOfLength・length_eq_of_mem_listsOfLength は listsOfLength が指定した長さの経路を
ちょうど列挙することを、contextFreeRule_mem・contextFreeRule_cases は生成された文法の
規則が遷移と整合経路の組に一対一対応することを保証する。以下の balanced_derives と
balanced_of_derives は、これらを用いて文法規則についての場合分けを機械の遷移についての
場合分けへ読み替える。

```lean
@[grind .] theorem balanced_derives [DecidableEq T] [DecidableEq State]
    [DecidableEq Stack] (M : NPDA T State Stack)
    {start done : State} {bottom : Stack}
    {p q : State} {top : Stack} {word : List T}
    (h : Balanced M p top q word) (hq : q ∈ M.stateSupport) :
    (M.emptyToContextFreeGrammar start bottom done).Derives
      [.nonterminal ⟨p, top, q⟩] (terminalSymbols word) := by
  let g := M.emptyToContextFreeGrammar start bottom done
  refine Balanced.rec (M := M)
    (motive_1 := fun p top q word _ => ∀ (_ : q ∈ M.stateSupport),
      g.Derives [.nonterminal ⟨p, top, q⟩] (terminalSymbols word))
    (motive_2 := fun p stack q word _ => ∀ (_ : q ∈ M.stateSupport),
      ∃ path,
        path.length = stack.length + 1 ∧
        path.head? = some p ∧ path.getLastD p = q ∧
        (∀ state ∈ path, state ∈ M.stateSupport) ∧
        g.Derives (segmentForm path stack) (terminalSymbols word))
    ?_ ?_ ?_ h hq
  · intro q childWord r hr children ih hq
    obtain ⟨path, hlen, hhead, hlast, hsupported, hchildren⟩ := ih hq
    have hpath : path ∈ M.compatiblePaths r := by
      simp only [compatiblePaths, List.mem_filter]
      constructor
      · exact mem_listsOfLength hlen hsupported
      · simp [hhead]
    have hrule := M.contextFreeRule_mem hr hpath
      (start := start) (bottom := bottom) (done := done)
    have hproduces : g.Produces
        [.nonterminal ⟨r.source, r.pop, q⟩]
        (contextFreeRule r path).output := by
      refine ⟨contextFreeRule r path, hrule, ?_⟩
      change (contextFreeRule r path).Rewrites
        [.nonterminal ⟨r.source, r.pop, q⟩]
        (contextFreeRule r path).output
      rw [← hlast]
      exact ContextFreeRule.Rewrites.input_output
    have houtput : g.Derives (contextFreeRule r path).output
        (terminalSymbols (r.input.toList ++ childWord)) := by
      have := hchildren.append_left
        (r.input.toList.map Symbol.terminal)
      convert this using 1 <;>
        simp [contextFreeRule, terminalSymbols, List.map_append]; rfl
    exact hproduces.single.trans houtput
  · intro q hq
    exact ⟨[q], by simp, by simp, by simp,
      fun state hstate => (List.mem_singleton.mp hstate) ▸ hq,
      Relation.ReflTransGen.refl⟩
  · intro p mid q top stack u v head tail ihHead ihTail hq
    obtain ⟨path, hlen, hpathHead, hlast, hsupported, htail⟩ := ihTail hq
    cases path with
    | nil => simp at hpathHead
    | cons first path =>
        simp only [List.head?_cons, Option.some.injEq] at hpathHead
        subst first
        have hmid : mid ∈ M.stateSupport := hsupported mid (by simp)
        have hhead := ihHead hmid
        refine ⟨p :: mid :: path, ?_, by simp, ?_, ?_, ?_⟩
        · simpa using congrArg Nat.succ hlen
        · rw [List.getLastD_cons, List.getLastD_cons]
          rw [List.getLastD_cons] at hlast
          exact hlast
        · intro state hstate
          rcases List.mem_cons.mp hstate with rfl | hstate
          · cases head with
            | rule r hr children => exact M.rule_source_mem_stateSupport hr
          · exact hsupported state hstate
        · change g.Derives
            (.nonterminal ⟨p, top, mid⟩ :: segmentForm (mid :: path) stack)
            (terminalSymbols (u ++ v))
          simpa [terminalSymbols, List.map_append] using
            ContextFreeGrammar.derives_cons_of g hhead htail

```

balanced_derives は健全性の半分を与える。p から top を取り除いて q へ至る Balanced な
計算が存在し、かつ q が stateSupport に属するならば、三つ組非終端記号 ⟨p, top, q⟩ から
同じ入力語がちょうど導出可能である。逆方向（導出可能ならば balanced な計算が存在する
こと）を示すため、導出木の各記号・各文型が意味的に何を表すかを述べる相互帰納的な述語
SymbolMeaning・FormMeaning を導入する。

```lean
mutual
  /-- Semantic meaning of one symbol in the triple grammar. -/
  public inductive SymbolMeaning (M : NPDA T State Stack) :
      Symbol T (ContextFreeNT State Stack) → List T → Prop
    | terminal (a : T) : SymbolMeaning M (.terminal a) [a]
    | nonterminal {p q : State} {top : Stack} {word : List T}
        (run : Balanced M p top q word) :
        SymbolMeaning M (.nonterminal ⟨p, top, q⟩) word

  /-- Semantic meaning of a complete form in the triple grammar. -/
  public inductive FormMeaning (M : NPDA T State Stack) :
      List (Symbol T (ContextFreeNT State Stack)) → List T → Prop
    | nil : FormMeaning M [] []
    | cons {x : Symbol T (ContextFreeNT State Stack)} {u : List T}
        {xs : List (Symbol T (ContextFreeNT State Stack))} {v : List T}
        (head : SymbolMeaning M x u) (tail : FormMeaning M xs v) :
        FormMeaning M (x :: xs) (u ++ v)
end

```

getLastD_cons_default は、空でないリストの `getLastD` がデフォルト値に依存しないことを
示す純粋に技術的な補題である。経路の最後の要素を `path.getLastD p` や
`path.getLastD r.target` のように異なるデフォルト値で書いている箇所を後で
同一視するために必要になる。

```lean
@[grind .] theorem getLastD_cons_default (x : State) (xs : List State) (a b : State) :
    (x :: xs).getLastD a = (x :: xs).getLastD b := by
  induction xs generalizing x with
  | nil => simp
  | cons y ys ih => simpa [List.getLastD_cons] using ih y
```

segmentForm_stackBalanced は意味論と Balanced 述語を結ぶ核心的な補題である。経路
path とスタック stack から作った segmentForm が実際に意味を持つ（FormMeaning）ならば、
それはちょうど p から path.getLastD p へ至る StackBalanced な計算であることを示す。
以下の完全性方向（機械が受理する語は文法も生成すること）の証明はすべてこれに依拠する。

```lean
/-- A meaningful segment form is exactly a balanced computation of its stack
word along the encoded control-state path. -/


@[grind .] theorem segmentForm_stackBalanced (M : NPDA T State Stack)
    {path : List State} {stack : List Stack} {p : State} {word : List T}
    (hlen : path.length = stack.length + 1)
    (hhead : path.head? = some p)
    (hmeaning : FormMeaning M (segmentForm path stack) word) :
    StackBalanced M p stack (path.getLastD p) word := by
  induction stack generalizing path p word with
  | nil =>
      simp only [List.length_nil, Nat.zero_add] at hlen
      cases path with
      | nil => simp at hlen
      | cons first tail =>
          cases tail with
          | nil =>
              simp only [List.head?_cons, Option.some.injEq] at hhead
              subst first
              simp only [segmentForm] at hmeaning
              cases hmeaning
              exact StackBalanced.nil p
          | cons second rest => simp at hlen
  | cons top stack ih =>
      cases path with
      | nil => simp at hlen
      | cons first tail =>
          cases tail with
          | nil => simp at hlen
          | cons mid rest =>
              simp only [List.head?_cons, Option.some.injEq] at hhead
              subst first
              simp only [segmentForm] at hmeaning
              cases hmeaning with
              | cons htop htail =>
                  cases htop with
                  | nonterminal hrun =>
                      have hlen' : (mid :: rest).length = stack.length + 1 := by
                        simp only [List.length_cons] at hlen ⊢
                        omega
                      have hstack := ih hlen' (p := mid) (by simp) htail
                      have hlast := getLastD_cons_default mid rest p mid
                      rw [List.getLastD_cons, hlast]
                      exact StackBalanced.cons hrun hstack
```

contextFreeRule_meaning は segmentForm_stackBalanced を使い、一つの生成規則の右辺の
意味を、元になった遷移の入力動作（あれば一文字消費）と push されたスタックの
計算へ翻訳する。これにより、規則単位の意味づけが遷移単位の Balanced 計算へ
一段階ずつ対応することが分かる。

```lean
/-- The right-hand side of a generated production describes precisely the
input action and pushed-stack computation of its source transition. -/


@[grind .] theorem contextFreeRule_meaning [DecidableEq State]
    (M : NPDA T State Stack) (r : PushdownRule T State Stack)
    {path : List State} (hpath : path ∈ M.compatiblePaths r)
    {word : List T}
    (hmeaning : FormMeaning M (contextFreeRule r path).output word) :
    ∃ childWord,
      word = r.input.toList ++ childWord ∧
      StackBalanced M r.target r.push (path.getLastD r.target) childWord := by
  have hfiltered := (List.mem_filter.mp hpath).1
  have hlen := length_eq_of_mem_listsOfLength hfiltered
  have hhead : path.head? = some r.target := by
    simpa [compatiblePaths] using (List.mem_filter.mp hpath).2
  cases hin : r.input with
  | none =>
      simp only [contextFreeRule, hin, Option.toList_none, List.map_nil,
        List.nil_append] at hmeaning ⊢
      exact ⟨word, rfl, segmentForm_stackBalanced M hlen hhead hmeaning⟩
  | some a =>
      simp only [contextFreeRule, hin, Option.toList_some, List.map_cons,
        List.map_nil] at hmeaning
      cases hmeaning with
      | cons hterminal htail =>
          cases hterminal
          exact ⟨_, rfl, segmentForm_stackBalanced M hlen hhead htail⟩
```

derivationFormTree_meaning は contextFreeRule_meaning を、一つの規則ではなく生成された
文法の任意の導出木へ拡張する。SymbolMeaning・FormMeaning の相互帰納に沿って木を
辿り、各適用ステップで contextFreeRule_cases によって規則を遷移と経路の組へ戻し、
子の意味づけから親の意味づけを組み立てる。

```lean
/-- A derivation tree of the generated grammar denotes balanced NPDA runs. -/
@[grind .] theorem derivationFormTree_meaning [DecidableEq T] [DecidableEq State]
    [DecidableEq Stack] (M : NPDA T State Stack)
    {start done : State} {bottom : Stack}
    {form : List (Symbol T (ContextFreeNT State Stack))} {word : List T}
    (tree : ContextFreeGrammar.DerivationFormTree
      (M.emptyToContextFreeGrammar start bottom done) form word) :
    FormMeaning M form word := by
  let g := M.emptyToContextFreeGrammar start bottom done
  exact ContextFreeGrammar.DerivationFormTree.rec
    (motive_1 := fun symbol word _ => SymbolMeaning M symbol word)
    (motive_2 := fun form word _ => FormMeaning M form word)
    (fun a => SymbolMeaning.terminal a)
    (fun gr hgr children _ ih => by
      obtain ⟨r, hr, path, hpath, rfl⟩ := M.contextFreeRule_cases hgr
      obtain ⟨childWord, rfl, hchildren⟩ :=
        contextFreeRule_meaning M r hpath ih
      exact SymbolMeaning.nonterminal (Balanced.rule r hr hchildren))
    FormMeaning.nil
    (fun head tail ihHead ihTail => FormMeaning.cons ihHead ihTail)
    tree
```

balanced_of_derives は derivationFormTree_meaning を、開始記号が三つ組非終端記号
⟨p, top, q⟩ 一つだけの導出木に適用し、意味づけの結果から直接 Balanced M p top q word
を取り出す。これで完全性方向（導出可能ならば対応する Balanced な機械の計算が存在する
こと）が確立する。

```lean
/-- Every terminal derivation from a triple nonterminal reconstructs a
balanced run of the original NPDA. -/


@[grind .] theorem balanced_of_derives [DecidableEq T] [DecidableEq State]
    [DecidableEq Stack] (M : NPDA T State Stack)
    {start done : State} {bottom : Stack}
    {p q : State} {top : Stack} {word : List T}
    (h : (M.emptyToContextFreeGrammar start bottom done).Derives
      [.nonterminal ⟨p, top, q⟩] (terminalSymbols word)) :
    Balanced M p top q word := by
  have tree := ContextFreeGrammar.derivationFormTree_of_derives _ h
  have meaning := derivationFormTree_meaning M tree
  cases meaning with
  | cons hhead htail =>
      cases htail
      cases hhead with
      | nonterminal run => simpa using run
```

mem_emptyToContextFreeGrammar_language_iff は balanced_derives（健全性）と
balanced_of_derives（完全性）を合わせ、done が stateSupport に属する限り
emptyToContextFreeGrammar の言語と `Balanced M start bottom done` による受理とが
同値であることを述べる。健全性・完全性の両方向がここで一つの iff にまとまる。

```lean
/-- The generated triple grammar and balanced-run semantics coincide whenever
the requested target state belongs to the finite state support. -/


@[grind .] theorem mem_emptyToContextFreeGrammar_language_iff
    [DecidableEq T] [DecidableEq State] [DecidableEq Stack]
    (M : NPDA T State Stack) {start done : State} {bottom : Stack}
    (hdone : done ∈ M.stateSupport) (word : List T) :
    word ∈ (M.emptyToContextFreeGrammar start bottom done).language ↔
      Balanced M start bottom done word := by
  change (M.emptyToContextFreeGrammar start bottom done).Derives
      [.nonterminal ⟨start, bottom, done⟩] (terminalSymbols word) ↔ _
  exact ⟨M.balanced_of_derives, fun h => M.balanced_derives h hdone⟩
```

finalToEmpty_accepts_iff_balanced は、mem_emptyToContextFreeGrammar_language_iff が
要求する形（ある一つの区別された bottom 記号を取り除く Balanced 計算）へ、任意の
最終状態受理の機械を橋渡しする。finalToEmpty 正規化を経た機械の最終状態受理が、
専用の boot 状態から bottom 記号を取り除いて done 状態へ至る一回の Balanced 計算に
他ならないことを示す。

```lean
/-- Acceptance of the normalized machine is precisely one balanced computation
that removes its private bottom marker. -/


@[grind .] theorem finalToEmpty_accepts_iff_balanced (M : NPDA T State Stack)
    (word : List T) :
    M.finalToEmpty.Accepts word ↔
      Balanced M.finalToEmpty .boot .bottom .done word := by
  constructor
  · rintro ⟨start, hstart, finalState, hdone, stack, hreach⟩
    simp only [finalToEmpty, List.mem_singleton] at hstart hdone
    subst start
    subst finalState
    have hstack : stack = [] :=
      M.finalReaches_stack_good hreach (by simp [FinalStackGood])
    subst stack
    have hbalanced := stackBalanced_of_reaches_to_empty hreach
    cases hbalanced with
    | cons head tail =>
        cases tail
        simpa using head
  · intro h
    refine ⟨.boot, by simp [finalToEmpty], .done, by simp [finalToEmpty], [], ?_⟩
    simpa [finalToEmpty] using h.reaches [] []
```

toContextFreeGrammar はこれまでの構成をすべて合成した、逆方向の最終的な計算可能な
構成である：任意の局所 NPDA `M` をまず finalToEmpty で最終状態受理から空スタック
受理相当の形へ正規化し、その専用状態 boot・bottom・done に対して
emptyToContextFreeGrammar を適用する。DecidableEq の仮定は listsOfLength・
compatiblePaths が有限集合演算として計算可能であるために必要になる。

```lean
/-- Computable triple construction from a finite local NPDA to a CFG. -/
public def toContextFreeGrammar [DecidableEq T] [DecidableEq State]
    [DecidableEq Stack] (M : NPDA T State Stack) : ContextFreeGrammar T :=
  M.finalToEmpty.emptyToContextFreeGrammar .boot .bottom .done
```

toContextFreeGrammar_language は mem_emptyToContextFreeGrammar_language_iff・
finalToEmpty_accepts_iff_balanced・finalToEmpty の言語保存性をすべて連結し、
この文法の言語が元の NPDA の受理言語とちょうど一致することを結論する。これで
逆方向（NPDA から文脈自由文法へ）の構成の正しさが完結する。

```lean
/-- The NPDA-to-CFG construction preserves exactly the accepted language. -/
@[important, grind =, simp] public theorem toContextFreeGrammar_language [DecidableEq T]
    [DecidableEq State] [DecidableEq Stack] (M : NPDA T State Stack) :
    M.toContextFreeGrammar.language = M.language := by
  ext word
  change word ∈
      (M.finalToEmpty.emptyToContextFreeGrammar .boot .bottom .done).language ↔ _
  rw [mem_emptyToContextFreeGrammar_language_iff]
  · rw [← M.finalToEmpty_language]
    exact (M.finalToEmpty_accepts_iff_balanced word).symm
  · simp [stateSupport, finalToEmpty]
```

toContextFreeGrammar の計算可能版は DecidableEq の仮定を要求するが、`isContextFree_iff_exists_npda`
のような意味論的な同値の主張ではその仮定を持ち出したくない。そこで Classical 名前空間の下に、
`classical` タクティクで選択公理から DecidableEq インスタンスを合成して呼び出すだけの
ラッパーを用意する。

```lean
namespace Classical

noncomputable section

/-- Choice-based wrapper requiring no decidable-equality instances. -/
public def toContextFreeGrammar (M : NPDA T State Stack) : ContextFreeGrammar T := by
  classical
  exact M.toContextFreeGrammar

```

同様に、この Classical.toContextFreeGrammar についても言語保存性を書き写し、
呼び出し側が DecidableEq を意識せずに使える形の同値を与える。

```lean
@[grind =, simp] theorem toContextFreeGrammar_language (M : NPDA T State Stack) :
    (toContextFreeGrammar M).language = M.language := by
  classical
  exact NPDA.toContextFreeGrammar_language M

end

end Classical

end NPDA
end Mathling.Automata

```

以降の Language 名前空間では、ここまで積み上げた両方向の構成（文法 → NPDA、
NPDA → 文法）を組み合わせて、文脈自由性の意味論的な定義と操作的な特徴づけの
同値性そのものを述べる。

```lean
namespace Language

```

isContextFree_iff_exists_npda はここまでの全体の到達点であり、`ContextFreeGrammar` を
使った意味論的な定義 `L.IsContextFree` と、有限局所 NPDA が受理する言語であるという
操作的な特徴づけとが同値であることを述べる。往路は g.toNPDA と toNPDA_language
（直接構成）を、復路は Classical.toContextFreeGrammar と
Classical.toContextFreeGrammar_language（三つ組構成の選択公理版）を witness として使う。

```mermaid
flowchart LR
    G["ContextFreeGrammar g"] -- "toNPDA" --> N["NPDA (GrammarPDAState, GrammarPDAStack)"]
    N -- "toNPDA_language" --> G
    M["NPDA M"] -- "Classical.toContextFreeGrammar" --> G2["ContextFreeGrammar"]
    G2 -- "Classical.toContextFreeGrammar_language" --> M
```

```lean
open Mathling.Automata Mathling.Grammar

/-- A language is context-free exactly when some standard finite local NPDA
accepts it. Both machine state and stack alphabets are existential witnesses. -/


@[important, grind =] public theorem isContextFree_iff_exists_npda {T : Type} {L : Language T} :
    L.IsContextFree ↔
      ∃ State Stack : Type, ∃ M : NPDA T State Stack, M.language = L := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨GrammarPDAState, GrammarPDAStack T g.NT, g.toNPDA,
      ContextFreeGrammar.toNPDA_language g⟩
  · rintro ⟨State, Stack, M, rfl⟩
    exact ⟨Mathling.Automata.NPDA.Classical.toContextFreeGrammar M,
      Mathling.Automata.NPDA.Classical.toContextFreeGrammar_language M⟩
```

IsDeterministicContextFree はこのモジュールが確立した NPDA 側の操作的な語彙を
決定性版へそのまま横滑りさせた定義であり、ある有限局所 DPDA が受理する言語である
こととして述べる。CFL の操作的特徴づけが NPDA の存在で書けたのと対称的な形に
することで、以降の DCFL ⊆ CFL の議論を素直に進められる。

```lean
/-- A language is deterministic context-free when a finite local DPDA accepts it. -/
@[expose] public def IsDeterministicContextFree {T : Type}
    (L : Language T) : Prop :=
  ∃ State Stack : Type, ∃ M : DPDA T State Stack, M.language = L
```

isDeterministicContextFree_iff_exists_dpda は IsDeterministicContextFree が定義の
展開だけで既にその操作的特徴づけそのものになっている（`rfl` で閉じる）ことを
明示的な補題として名前付けし、他の同値と並べて `simp`・`grind` から使えるようにする。

```lean
/-- The operational DPDA presentation of deterministic context-freeness. -/
@[important, grind =, simp] public theorem isDeterministicContextFree_iff_exists_dpda
    {T : Type} {L : Language T} :
    L.IsDeterministicContextFree ↔
      ∃ State Stack : Type, ∃ M : DPDA T State Stack, M.language = L := by
  rfl
```

IsDeterministicContextFree.isContextFree は、DPDA の決定性を単に忘れて NPDA として
扱うことで（`M.toNPDA` は既存の DPDA-to-NPDA 変換）、決定性文脈自由言語が常に
文脈自由言語でもあることを示す。これが標準的な包含関係 DCFL ⊆ CFL の証明である。

```lean
/-- Forgetting determinism proves the standard inclusion DCFL ⊆ CFL. -/
@[important, grind .] public theorem IsDeterministicContextFree.isContextFree
    {T : Type} {L : Language T} (h : L.IsDeterministicContextFree) :
    L.IsContextFree := by
  obtain ⟨State, Stack, M, rfl⟩ := h
  exact Language.isContextFree_iff_exists_npda.mpr
    ⟨State, Stack, M.toNPDA, M.toNPDA_language⟩

end Language
```

isContextFree_iff_exists_npda を NPDA 自身のメソッドとしても使えるよう、
`Mathling.Automata.NPDA` 名前空間へ移って結果を書き直す。

```lean
namespace Mathling.Automata.NPDA

```

language_isContextFree は isContextFree_iff_exists_npda を機械自身を witness として
即座に適用するだけの帰結であり、「任意の有限局所 NPDA が受理する言語は文脈自由である」
という、CFL の操作的特徴づけの実用上の主要な使い方を短い補題として固定する。

```lean
variable {T State Stack : Type}

/-- The language of every finite-local NPDA is context-free.  The classical
CFG construction supplies the witness without exposing decidable-equality
requirements in the statement. -/


@[important, grind .] public theorem language_isContextFree
    (M : NPDA T State Stack) : M.language.IsContextFree :=
  Language.isContextFree_iff_exists_npda.mpr ⟨State, Stack, M, rfl⟩

end Mathling.Automata.NPDA

```

同様に、DPDA 側からも決定性文脈自由性の主張を機械のメソッドとして使えるよう
`Mathling.Automata.DPDA` 名前空間へ移る。

```lean
namespace Mathling.Automata.DPDA

```

language_isDeterministicContextFree は IsDeterministicContextFree の定義を機械自身を
witness として即座に満たすだけの帰結であり、language_isContextFree の決定性版に
あたる。

```lean
variable {T State Stack : Type}

/-- Every local DPDA recognizes a deterministic context-free language. -/
@[important, grind .] public theorem language_isDeterministicContextFree
    (M : DPDA T State Stack) : M.language.IsDeterministicContextFree :=
  ⟨State, Stack, M, rfl⟩

end Mathling.Automata.DPDA

```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
