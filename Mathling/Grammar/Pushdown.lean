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

```lean

```

```lean
namespace Mathling.Grammar

```

```lean
open Mathling.Automata

/-- Control states of the direct grammar-to-PDA construction. -/
@[grind cases] public inductive GrammarPDAState where
  | run
  | done
  deriving Repr, DecidableEq
```

```lean
/-- Grammar symbols plus a private bottom marker. -/
@[grind cases] public inductive GrammarPDAStack (T N : Type*) where
  | bottom
  | symbol (value : Symbol T N)
  deriving Repr
```

```lean
namespace ContextFreeGrammar

```

```lean
variable {T : Type*}

noncomputable section

/-- Terminals mentioned by a sentential form, preserving repetitions. -/
public def rhsTerminals {N : Type*} : List (Symbol T N) → List T
  | [] => []
  | .terminal a :: xs => a :: rhsTerminals xs
  | .nonterminal _ :: xs => rhsTerminals xs
```

```lean
/-- The finite list of terminals explicitly mentioned by grammar rules. -/
public def terminalSupport (g : ContextFreeGrammar T) : List T :=
  g.rules.toList.flatMap fun r => rhsTerminals r.output
```

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

```lean
public def terminalRule (g : ContextFreeGrammar T) (a : T) :
    PushdownRule T GrammarPDAState (GrammarPDAStack T g.NT) where
  source := .run
  input := some a
  pop := .symbol (.terminal a)
  target := .run
  push := []
```

```lean
public def finishRule (g : ContextFreeGrammar T) :
    PushdownRule T GrammarPDAState (GrammarPDAStack T g.NT) where
  source := .run
  input := none
  pop := .bottom
  target := .done
  push := []
```

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

```lean
public def encodeForm {N : Type*} (xs : List (Symbol T N)) :
    List (GrammarPDAStack T N) := xs.map GrammarPDAStack.symbol
```

```lean
public def Supported (g : ContextFreeGrammar T) : Symbol T g.NT → Prop
  | .terminal a => a ∈ terminalSupport g
  | .nonterminal _ => True
```

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

```lean
@[grind .] theorem expansionRule_mem (g : ContextFreeGrammar T)
    {r : ContextFreeRule T g.NT} (hr : r ∈ g.rules) :
    expansionRule r ∈ (toNPDA g).rules := by
  simp only [toNPDA, List.mem_append, List.mem_map, Finset.mem_toList]
  exact Or.inl (Or.inl ⟨r, hr, rfl⟩)

```

```lean
@[grind .] theorem terminalRule_mem (g : ContextFreeGrammar T)
    {a : T} (ha : a ∈ terminalSupport g) :
    terminalRule g a ∈ (toNPDA g).rules := by
  simp only [toNPDA, List.mem_append, List.mem_map]
  exact Or.inl (Or.inr ⟨a, ha, rfl⟩)

```

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

```lean
namespace Mathling.Automata
```

```lean
namespace NPDA

```

```lean
open Mathling.Grammar

universe u

```

```lean
variable {T : Type u} {State Stack : Type}

/-- Triple nonterminals: from state, removed stack symbol, and destination state. -/
@[ext] public structure ContextFreeNT (State Stack : Type) where
  source : State
  pop : Stack
  target : State
  deriving Repr, DecidableEq
```

```lean
/-- Enumerate lists of a fixed length over a finite list of choices. -/
public def listsOfLength (choices : List State) : Nat → List (List State)
  | 0 => [[]]
  | n + 1 => choices.flatMap fun q =>
      (listsOfLength choices n).map (q :: ·)
```

```lean
/-- Control states explicitly occurring in a finite NPDA presentation. -/
public def stateSupport (M : NPDA T State Stack) : List State :=
  M.start ++ M.accept ++ M.rules.flatMap fun r => [r.source, r.target]
```

```lean
/-- Adjacent triples determined by a control-state path and a stack word. -/
public def segmentForm : List State → List Stack →
    List (Symbol T (ContextFreeNT State Stack))
  | p :: q :: states, x :: stack =>
      .nonterminal ⟨p, x, q⟩ :: segmentForm (q :: states) stack
  | _, _ => []
```

```lean
/-- A transition and a compatible state path determine one grammar production. -/
public def contextFreeRule (r : PushdownRule T State Stack) (path : List State) :
    ContextFreeRule T (ContextFreeNT State Stack) where
  input := ⟨r.source, r.pop, path.getLastD r.target⟩
  output := r.input.toList.map Symbol.terminal ++ segmentForm path r.push
```

```lean
/-- State paths compatible with the pushed stack word of a transition. -/
public def compatiblePaths [DecidableEq State] (M : NPDA T State Stack)
    (r : PushdownRule T State Stack) : List (List State) :=
  (listsOfLength M.stateSupport (r.push.length + 1)).filter
    fun path => path.head? = some r.target
```

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

ContextFreeNT は「source 状態から pop 記号を1つ取り除いて target 状態へ至る」という
三つ組を非終端記号とする。segmentForm は制御状態の経路とスタック語を並べて隣接する
三つ組の列を作り、contextFreeRule は一つの遷移とそれに整合する経路から、入力記号
（あれば）と push されたスタック語の segmentForm を右辺とする規則を作る。compatiblePaths
は stateSupport の有限性を用いて listsOfLength で経路を列挙し、先頭が target 状態に
一致するものだけへ絞り込む。emptyToContextFreeGrammar はこれらを全ての遷移と整合経路に
ついて集め、指定した start・bottom・done に対応する三つ組を開始記号とする文法である。

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

```lean
@[grind .] theorem rule_source_mem_stateSupport (M : NPDA T State Stack)
    {r : PushdownRule T State Stack} (hr : r ∈ M.rules) :
    r.source ∈ M.stateSupport := by
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨r, hr, by simp⟩

```

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

```lean
@[grind .] theorem getLastD_cons_default (x : State) (xs : List State) (a b : State) :
    (x :: xs).getLastD a = (x :: xs).getLastD b := by
  induction xs generalizing x with
  | nil => simp
  | cons y ys ih => simpa [List.getLastD_cons] using ih y
```

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

segmentForm_stackBalanced は、経路 path とスタック stack から作った segmentForm が実際に
意味を持つ（FormMeaning）ならば、それがちょうど p から path.getLastD p へ至る
StackBalanced な計算であることを示す。これは意味論と Balanced 述語を結ぶ核心的な補題で
あり、以下の完全性方向の証明はすべてこれに依拠する。

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

contextFreeRule_meaning は一つの生成規則の右辺の意味を、元になった遷移の入力動作と
push されたスタックの計算へ翻訳し、derivationFormTree_meaning はこれを任意の導出木へ
拡張する。balanced_of_derives はこれらを合わせ、三つ組非終端記号から終端列への導出が
存在すればそれがちょうど Balanced な機械の計算に対応することを結論し、これで健全性・
完全性の両方向が揃う。

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

mem_emptyToContextFreeGrammar_language_iff は balanced_derives と balanced_of_derives を
合わせ、done が stateSupport に属する限り emptyToContextFreeGrammar の言語と
Balanced start bottom done による受理とが同値であることを述べる。
finalToEmpty_accepts_iff_balanced は、finalToEmpty 正規化を経た機械の最終状態受理が、
専用の boot 状態から bottom 記号を取り除いて done 状態へ至る一回の Balanced 計算に
他ならないことを示し、両者を結び付ける橋渡しとなる。

```lean
/-- Computable triple construction from a finite local NPDA to a CFG. -/
public def toContextFreeGrammar [DecidableEq T] [DecidableEq State]
    [DecidableEq Stack] (M : NPDA T State Stack) : ContextFreeGrammar T :=
  M.finalToEmpty.emptyToContextFreeGrammar .boot .bottom .done
```

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

```lean
namespace Classical

noncomputable section

/-- Choice-based wrapper requiring no decidable-equality instances. -/
public def toContextFreeGrammar (M : NPDA T State Stack) : ContextFreeGrammar T := by
  classical
  exact M.toContextFreeGrammar

```

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

toContextFreeGrammar は finalToEmpty 正規化と emptyToContextFreeGrammar を合成した、
計算可能な逆方向構成である。toContextFreeGrammar_language はここまでの補題を連結し、
この文法の言語が元の NPDA の受理言語とちょうど一致することを示す。Classical 名前空間は
decidable equality のインスタンスを要求しない選択公理版を与える。最後に
isContextFree_iff_exists_npda が、toNPDA_language と toContextFreeGrammar_language
（の classical 版）を組み合わせて、文脈自由性の意味論的定義と、有限局所 NPDA が受理する
言語であるという操作的特徴づけの同値性を結論する。

```lean
namespace Language

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

```lean
/-- A language is deterministic context-free when a finite local DPDA accepts it. -/
@[expose] public def IsDeterministicContextFree {T : Type}
    (L : Language T) : Prop :=
  ∃ State Stack : Type, ∃ M : DPDA T State Stack, M.language = L
```

```lean
/-- The operational DPDA presentation of deterministic context-freeness. -/
@[important, grind =, simp] public theorem isDeterministicContextFree_iff_exists_dpda
    {T : Type} {L : Language T} :
    L.IsDeterministicContextFree ↔
      ∃ State Stack : Type, ∃ M : DPDA T State Stack, M.language = L := by
  rfl
```

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

```lean
namespace Mathling.Automata.NPDA

```

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

```lean
namespace Mathling.Automata.DPDA

```

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
