    module

    public import Mathling.Grammar.NormalForms.ChomskyClassical
    public import Mathling.Meta.Important

    import LiterateLean
    open scoped LiterateLean


# Mathling / Grammar / Theory モジュール

Chomsky 標準形の二分導出木から文脈自由言語の pumping 分解を抽出する。高さと葉数の境界、型付き一穴文脈、反復する非終端記号を結び付け、空語の例外を含む言語レベルの定理へ持ち上げる。

以下の証明パイプラインは Chomsky 標準形の文法 `g` を固定した名前空間 `Mathling.Grammar` の中で進む。二分木の高さの数え方（葉が高さ `1`）をここで固定しておくことで、後続の指数境界 `2 ^ (height - 1)` や pumping 定数 `2 ^ m` の式がずれなく積み上がる。

```lean

/-!
# Pumping lemma for context-free languages

Parse-tree height counts nodes: a leaf has height `1`, and a binary node has
height one plus the maximum height of its children.
-/



namespace Mathling.Grammar

universe u

```

CNF 文法 `g` に対する導出木の型 `ParseTree` を定義する。コンストラクタは文法規則の集合 `g.cfg.rules` に属する規則の証拠を直接埋め込むので、木として構成できる値は必ず妥当な導出に対応し、無効な導出を表す項は存在しない。この不変条件が、以降のすべての yield / height 計算と pumping 論法の土台になる。

```lean
variable {T : Type u}

/-- A nonempty derivation tree for a grammar in Chomsky normal form. -/
@[grind cases] public inductive ParseTree (g : ChomskyNormalGrammar T) : g.cfg.NT → Type u where
  | leaf (A : g.cfg.NT) (a : T)
      (h : ({ input := A, output := [Symbol.terminal a] } :
        ContextFreeRule T g.cfg.NT) ∈ g.cfg.rules) : ParseTree g A
  | node (A B C : g.cfg.NT)
      (h : ({ input := A, output := [Symbol.nonterminal B, Symbol.nonterminal C] } :
        ContextFreeRule T g.cfg.NT) ∈ g.cfg.rules)
      (l : ParseTree g B) (r : ParseTree g C) : ParseTree g A

```

`ParseTree.yield` は木の葉を左から右へ読み上げて得られる終端記号列であり、これが最終的に pumping lemma で扱う言語の語 `w` そのものになる。木の構造から直接読み取れる定義なので、後続の `yield_derives` によって「この語が実際に `g` から導出可能である」ことと結び付けられる。

```lean
namespace ParseTree

/-- The terminal word along the leaves of a parse tree. -/
public def yield {g : ChomskyNormalGrammar T} {A : g.cfg.NT} :
    ParseTree g A → List T
  | .leaf _ a _ => [a]
  | .node _ _ _ _ l r => yield l ++ yield r
```

`height` は pumping lemma のパラメータ `p` を決める指標である。木の高さが十分大きければ根から葉への経路上に非終端記号の重複が鳩の巣原理で保証される、という後段の `exists_pump` の議論はすべてこの定義に依存する。

```lean
/-- Node height, with leaves at height one. -/
public def height {g : ChomskyNormalGrammar T} {A : g.cfg.NT} :
    ParseTree g A → Nat
  | .leaf _ _ _ => 1
  | .node _ _ _ _ l r => 1 + max (height l) (height r)
```

木が非空である以上、高さは常に正である。この下界は `height_le_plug` や `exists_pump` の残余の高さ計算で `Nat` の引き算 `height - 1` が不自然に切り捨てられないことを保証するために使われる小さいが欠かせない補題である。

```lean
@[grind ., simp] theorem one_le_height {g : ChomskyNormalGrammar T} {A : g.cfg.NT}
    (t : ParseTree g A) : 1 ≤ height t := by
  cases t <;> simp [height]

```

同様に yield も空にはならない。この事実は `proper_yield_pos` で「proper な文脈は穴の外に少なくとも一つの終端記号を持つ」ことを示す際に、部分木の yield 長が正であることの根拠として使われる。

```lean
@[grind ., simp] theorem one_le_yield_length {g : ChomskyNormalGrammar T} {A : g.cfg.NT}
    (t : ParseTree g A) : 1 ≤ (yield t).length := by
  induction t with
  | leaf => simp [yield]
  | node A B C h l r ihl ihr =>
      simp only [yield, List.length_append]
      omega
```

二分木という構造そのものから来る指数境界 $`|{\rm yield}(t)| \le 2^{{\rm height}(t)-1}`$ を確立する。この境界が pumping lemma の定数 `p = 2 ^ m`（`m` は非終端記号数）の導出で使われ、「十分長い語なら十分高い木を持つ」という対偶の議論を可能にする。

```lean
/-- A binary parse tree of height `h` has at most `2^(h-1)` leaves. -/
@[grind .] theorem yield_length_le {g : ChomskyNormalGrammar T} {A : g.cfg.NT}
    (t : ParseTree g A) : (yield t).length ≤ 2 ^ (height t - 1) := by
  induction t with
  | leaf => simp [yield, height]
  | node A B C h l r ihl ihr =>
      simp only [yield, height, List.length_append]
      let m := max (height l) (height r)
      have hlm : height l ≤ m := Nat.le_max_left _ _
      have hrm : height r ≤ m := Nat.le_max_right _ _
      have hlpow : 2 ^ (height l - 1) ≤ 2 ^ (m - 1) :=
        Nat.pow_le_pow_right (by omega) (Nat.sub_le_sub_right hlm 1)
      have hrpow : 2 ^ (height r - 1) ≤ 2 ^ (m - 1) :=
        Nat.pow_le_pow_right (by omega) (Nat.sub_le_sub_right hrm 1)
      calc
        (yield l).length + (yield r).length
            ≤ 2 ^ (height l - 1) + 2 ^ (height r - 1) := Nat.add_le_add ihl ihr
        _ ≤ 2 ^ (m - 1) + 2 ^ (m - 1) := Nat.add_le_add hlpow hrpow
        _ = 2 * 2 ^ (m - 1) := by omega
        _ = 2 ^ (m - 1 + 1) := by rw [Nat.pow_succ']
        _ = 2 ^ m := by
          congr 1
          have hm : 1 ≤ m := le_trans (one_le_height l) hlm
          omega
        _ = 2 ^ (1 + m - 1) := by
          congr 1
          omega
```

`yield` は木の内部での構造上の読み上げにすぎないが、この定理によって初めてそれが `g.cfg.Derives` という文法の書き換え関係の言葉で正当化される。逆向き（導出から木を作る）は `ParseTree.exists_of_derives` が担い、この二つが揃って「導出」と「parse tree」の往復を完成させる。

```lean
/-- A parse tree witnesses a grammar derivation of its yield. -/
@[grind .] theorem yield_derives {g : ChomskyNormalGrammar T} {A : g.cfg.NT}
    (t : ParseTree g A) :
    g.cfg.Derives [Symbol.nonterminal A] (terminalSymbols (yield t)) := by
  induction t with
  | leaf A a h =>
      exact ContextFreeGrammar.Produces.single
        ⟨_, h, ContextFreeRule.Rewrites.input_output⟩
  | node A B C h l r ihl ihr =>
      apply (ContextFreeGrammar.Produces.single
        ⟨_, h, ContextFreeRule.Rewrites.input_output⟩).trans
      have hl := ihl.append_right [Symbol.nonterminal C]
      have hr := ihr.append_left (terminalSymbols (yield l))
      change g.cfg.Derives [Symbol.nonterminal B, Symbol.nonterminal C]
        (terminalSymbols (yield l ++ yield r))
      simpa [terminalSymbols, List.map_append, List.append_assoc] using hl.trans hr

end ParseTree
```

pumping lemma の核心は「木の途中に開いた穴に、同じ型の別の部分木を差し込んでも導出が壊れない」という性質であり、それを型で表現するのが一穴文脈 `ParseCtx` である。`hole` はそのまま、`left`/`right` は二分ノードのどちら側に穴を残すかを表し、この型自体が `A`（元の根）から `X`（穴のラベル）への構造的な依存関係を静的に保証する。

```lean
/-- A typed one-hole context in a CNF parse tree. -/
@[grind cases] public inductive ParseCtx (g : ChomskyNormalGrammar T) :
    g.cfg.NT → g.cfg.NT → Type u where
  | hole (A : g.cfg.NT) : ParseCtx g A A
  | left (A B C X : g.cfg.NT)
      (h : ({ input := A, output := [Symbol.nonterminal B, Symbol.nonterminal C] } :
        ContextFreeRule T g.cfg.NT) ∈ g.cfg.rules)
      (c : ParseCtx g B X) (r : ParseTree g C) : ParseCtx g A X
  | right (A B C X : g.cfg.NT)
      (h : ({ input := A, output := [Symbol.nonterminal B, Symbol.nonterminal C] } :
        ContextFreeRule T g.cfg.NT) ∈ g.cfg.rules)
      (l : ParseTree g B) (c : ParseCtx g C X) : ParseCtx g A X
```

`plug` は文脈と部分木を合わせて元の全体木を復元する操作であり、以降のすべての文脈演算（`compose`、`nest`、そして pumping lemma 本体）はこの一つの関数を通じて木を組み立て直す。文脈と穴の中身を独立に選べること自体が、同じ非終端記号を再訪する区間だけを反復できるという pumping の直感を型レベルで支える。

```lean
namespace ParseCtx

/-- Fill a parse context's hole. -/
public def plug {g : ChomskyNormalGrammar T} {A X : g.cfg.NT} :
    ParseCtx g A X → ParseTree g X → ParseTree g A
  | .hole _, t => t
  | .left A B C X h c r, t => .node A B C h (plug c t) r
  | .right A B C X h l c, t => .node A B C h l (plug c t)

```

## 一穴文脈の観測量

穴の左側と右側の yield、および plug 後の高さを制御する文脈寄与を定義する。proper な文脈は穴の外側に少なくとも一つの終端記号を持つため、後の pumping 部分が空にならない。

`preYield` は文脈を `plug` した結果の yield のうち、穴より前に来る接頭部分だけを木を作らずに取り出す。これが最終的な pumping lemma の分解 `u ++ v ++ x ++ y ++ z` のうち反復対象 `v`（および外側の `u`）に対応する。

```lean
/-- Terminals strictly to the left of a context's hole. -/
public def preYield {g : ChomskyNormalGrammar T} {A X : g.cfg.NT} :
    ParseCtx g A X → List T
  | .hole _ => []
  | .left _ _ _ _ _ c _ => preYield c
  | .right _ _ _ _ _ l c => ParseTree.yield l ++ preYield c
```

`preYield` と対をなす `postYield` は穴より後ろに来る接尾部分を取り出し、pumping 分解の反復対象 `y`（および外側の `z`）に対応する。二つを合わせることで `yield_plug` が「文脈を通した yield は接頭・穴・接尾の連結である」という不変条件を確立できる。

```lean
/-- Terminals strictly to the right of a context's hole. -/
public def postYield {g : ChomskyNormalGrammar T} {A X : g.cfg.NT} :
    ParseCtx g A X → List T
  | .hole _ => []
  | .left _ _ _ _ _ c r => postYield c ++ ParseTree.yield r
  | .right _ _ _ _ _ _ c => postYield c
```

`ctxHeight` は文脈だけが `plug` 後の木の高さにどれだけ寄与し得るかを穴の中身と無関係に測る量であり、`height_plug_le` の上界 `ctxHeight c + height t` を与える基礎になる。文脈側の高さと差し込む木側の高さを分離できることが、後で「反復部分の高さだけを `m + 1` 以下に抑える」議論を可能にする。

```lean
/-- The maximum contextual contribution to the height of a plugged tree. -/
public def ctxHeight {g : ChomskyNormalGrammar T} {A X : g.cfg.NT} :
    ParseCtx g A X → Nat
  | .hole _ => 0
  | .left _ _ _ _ _ c r => 1 + max (ctxHeight c) (ParseTree.height r)
  | .right _ _ _ _ _ l c => 1 + max (ParseTree.height l) (ctxHeight c)
```

`IsProper` は空の `hole` 文脈を除外するための判定であり、これがないと文脈による「反復」が恒等写像になってしまい、pumping lemma の非自明性条件 `v ++ y ≠ []` を満たせなくなる。`proper_yield_pos` はこの述語を利用して、proper な文脈が必ず穴の外に終端記号を持つことを示す。

```lean
/-- A context is proper when its hole is strictly below its root. -/
public def IsProper {g : ChomskyNormalGrammar T} {A X : g.cfg.NT} :
    ParseCtx g A X → Prop
  | .hole _ => False
  | .left _ _ _ _ _ _ _ => True
  | .right _ _ _ _ _ _ _ => True
```

これが文脈まわりの中心的な yield 補題である。`plug` によって組み立てた木の yield が、常に `preYield ++ 穴の yield ++ postYield` という連結に分解できることを示し、pumping lemma 本体で最終的な語の分解 `u ++ v ++ x ++ y ++ z` を構成する際に直接使われる。

```lean
@[grind =, simp] theorem yield_plug {g : ChomskyNormalGrammar T} {A X : g.cfg.NT}
    (c : ParseCtx g A X) (t : ParseTree g X) :
    ParseTree.yield (plug c t) =
      preYield c ++ ParseTree.yield t ++ postYield c := by
  induction c with
  | hole => simp [plug, preYield, postYield]
  | left A B C X h c r ih =>
      simp [plug, ParseTree.yield, preYield, postYield, ih, List.append_assoc]
  | right A B C X h l c ih =>
      simp [plug, ParseTree.yield, preYield, postYield, ih, List.append_assoc]

```

`ctxHeight` の定義から直接従う上界であり、文脈に何を差し込んでも全体の高さは「文脈自身の寄与＋差し込む木の高さ」を超えないことを保証する。この上界（と後述の `height_le_plug` による下界）の両側から、`exists_pump` で「反復対象の高さをちょうど `m + 1` 以下に収める」評価を行う。

```lean
@[grind ., simp] theorem height_plug_le {g : ChomskyNormalGrammar T} {A X : g.cfg.NT}
    (c : ParseCtx g A X) (t : ParseTree g X) :
    ParseTree.height (plug c t) ≤ ctxHeight c + ParseTree.height t := by
  induction c with
  | hole => simp [plug, ctxHeight]
  | left A B C X h c r ih =>
      simp only [plug, ParseTree.height, ctxHeight]
      have hc := ih t
      have hleft := Nat.le_max_left (ctxHeight c) (ParseTree.height r)
      have hright := Nat.le_max_right (ctxHeight c) (ParseTree.height r)
      omega
  | right A B C X h l c ih =>
      simp only [plug, ParseTree.height, ctxHeight]
      have hc := ih t
      have hleft := Nat.le_max_left (ParseTree.height l) (ctxHeight c)
      have hright := Nat.le_max_right (ParseTree.height l) (ctxHeight c)
      omega
```

この定理が pumping lemma の非自明性条件 `v ++ y ≠ []` の根拠そのものである。`IsProper` な文脈は必ずどちらか一方の枝に実際の部分木を持ち、`one_le_yield_length` によりその yield が空でないことから、穴の外側に少なくとも一つの終端記号が存在することが従う。

```lean
/-- A proper context contributes at least one terminal outside its hole. -/
@[grind .] theorem proper_yield_pos {g : ChomskyNormalGrammar T} {A X : g.cfg.NT}
    (c : ParseCtx g A X) (hc : IsProper c) :
    1 ≤ (preYield c ++ postYield c).length := by
  cases c with
  | hole => simp [IsProper] at hc
  | left A B C X h c r =>
      simp only [preYield, postYield, List.length_append]
      have hr := ParseTree.one_le_yield_length r
      omega
  | right A B C X h l c =>
      simp only [preYield, postYield, List.length_append]
      have hl := ParseTree.one_le_yield_length l
      omega
```

`compose` は二つの文脈を穴で継ぎ合わせて一つの文脈にする操作であり、`exists_pump` で「根から重複ラベルまでの外側の道のり `cout`」と「スパイン探索で得た途中までの文脈」を一本の文脈に統合するために使われる。`plug` との整合性は次の `plug_compose` が保証する。

```lean
/-- Compose contexts by grafting the second context at the first context's hole. -/
public def compose {g : ChomskyNormalGrammar T} {A X Y : g.cfg.NT} :
    ParseCtx g A X → ParseCtx g X Y → ParseCtx g A Y
  | .hole _, d => d
  | .left A B C X h c r, d => .left A B C Y h (compose c d) r
  | .right A B C X h l c, d => .right A B C Y h l (compose c d)
```

`compose` が `plug` と可換であること、すなわち二段階に分けて差し込んでも一段階で合成した文脈を差し込んでも同じ木になることを示す。これがないと `exists_pump` で合成した外側文脈 `cout.compose cmid` を使って元の木を再構成する等式が成り立たない。

```lean
@[grind =, simp] theorem plug_compose {g : ChomskyNormalGrammar T} {A X Y : g.cfg.NT}
    (c : ParseCtx g A X) (d : ParseCtx g X Y) (t : ParseTree g Y) :
    plug (compose c d) t = plug c (plug d t) := by
  induction c with
  | hole => rfl
  | left A B C X h c r ih => simp [compose, plug, ih]
  | right A B C X h l c ih => simp [compose, plug, ih]

```

合成された文脈の接頭 yield は、外側文脈の接頭に内側文脈の接頭を連結したものに一致する。この可換性補題群（本補題と次の `postYield_compose`）により、pumping lemma 本体で `u`（外側の接頭）を `cout.preYield` だけから計算してよいことが保証される。

```lean
@[grind =, simp] theorem preYield_compose {g : ChomskyNormalGrammar T} {A X Y : g.cfg.NT}
    (c : ParseCtx g A X) (d : ParseCtx g X Y) :
    preYield (compose c d) = preYield c ++ preYield d := by
  induction c with
  | hole => simp [compose, preYield]
  | left A B C X h c r ih => simp [compose, preYield, ih]
  | right A B C X h l c ih =>
      simp [compose, preYield, ih, List.append_assoc]

```

対称的に、合成された文脈の接尾 yield は内側の接尾を外側の接尾より先に連結したものになる（内側の穴の方が根から遠いため）。`preYield_compose` と対で、pumping lemma の `z`（外側の接尾）を `cout.postYield` から取り出せることを保証する。

```lean
@[grind =, simp] theorem postYield_compose {g : ChomskyNormalGrammar T} {A X Y : g.cfg.NT}
    (c : ParseCtx g A X) (d : ParseCtx g X Y) :
    postYield (compose c d) = postYield d ++ postYield c := by
  induction c with
  | hole => simp [compose, postYield]
  | left A B C X h c r ih =>
      simp [compose, postYield, ih, List.append_assoc]
  | right A B C X h l c ih => simp [compose, postYield, ih]
```

`height_plug_le` の逆向きの下界であり、穴に何を差し込んでも全体の高さは差し込んだ木の高さを下回らないことを示す。`exists_pump` はこれを使って、内側文脈 `cmid` を通した後でも反復対象の高さの評価 `(cin.plug s).height = t'.height = m + 1` を保てることを確認する。

```lean
/-- Plugging a context cannot decrease the height of its argument. -/
@[grind .] theorem height_le_plug {g : ChomskyNormalGrammar T} {A X : g.cfg.NT}
    (c : ParseCtx g A X) (t : ParseTree g X) :
    ParseTree.height t ≤ ParseTree.height (plug c t) := by
  induction c with
  | hole => simp [plug]
  | left A B C X h c r ih =>
      simp only [plug, ParseTree.height]
      exact le_trans (ih t)
        (le_trans (Nat.le_max_left _ _) (Nat.le_add_left _ _))
  | right A B C X h l c ih =>
      simp only [plug, ParseTree.height]
      exact le_trans (ih t)
        (le_trans (Nat.le_max_right _ _) (Nat.le_add_left _ _))

end ParseCtx
```

## 指定高さの部分木と spine

高い二分木から指定高さの部分木を切り出し、根から穴までの経路を `Spine` として記録する。有限個の非終端記号より長い spine に鳩の巣原理を適用する準備を整える。

```lean
/-- Every height between one and a tree's height occurs at some subtree. -/
@[grind .] theorem ParseTree.exists_subtree_height_eq
    {g : ChomskyNormalGrammar T} {A : g.cfg.NT} {k : Nat}
    (t : ParseTree g A) (hk : 1 ≤ k) (hk' : k ≤ t.height) :
    ∃ (X : g.cfg.NT) (c : ParseCtx g A X) (s : ParseTree g X),
      c.plug s = t ∧ s.height = k := by
  induction t generalizing k with
  | leaf A a h =>
      have hkeq : k = 1 := by
        simp only [ParseTree.height] at hk'
        omega
      subst k
      exact ⟨A, .hole A, .leaf A a h, rfl, rfl⟩
  | node A B C h l r ihl ihr =>
      by_cases heq : k = ParseTree.height (.node A B C h l r)
      · subst k
        exact ⟨A, .hole A, .node A B C h l r, rfl, rfl⟩
      · have hlt : k < ParseTree.height (.node A B C h l r) :=
          lt_of_le_of_ne hk' heq
        have hkmax : k ≤ max l.height r.height := by
          simp only [ParseTree.height] at hlt
          omega
        by_cases hkl : k ≤ l.height
        · obtain ⟨X, c, s, hplug, hs⟩ := ihl hk hkl
          exact ⟨X, .left A B C X h c r, s,
            by simp [ParseCtx.plug, hplug], hs⟩
        · have hkr : k ≤ r.height := by
            exact (le_max_iff.mp hkmax).resolve_left hkl
          obtain ⟨X, c, s, hplug, hs⟩ := ihr hk hkr
          exact ⟨X, .right A B C X h l c, s,
            by simp [ParseCtx.plug, hplug], hs⟩
```

`Spine` は根から葉までの一本道を、各段の部分木そのものの列として記録する型である。分岐のたびに左右どちらへ降りたかという証拠付きの選択を保持するため、この型の値から `exists_context_of_mem` によって途中の任意の段に対応する文脈と部分木を復元できる。

```lean
/-- A root-to-leaf branch, represented by its successive parse-tree roots. -/
@[grind cases] public inductive Spine (g : ChomskyNormalGrammar T) :
    {A : g.cfg.NT} → ParseTree g A → Type u where
  | stop (A : g.cfg.NT) (t : ParseTree g A) : Spine g t
  | downLeft (A B C : g.cfg.NT)
      (h : ({ input := A, output := [Symbol.nonterminal B, Symbol.nonterminal C] } :
        ContextFreeRule T g.cfg.NT) ∈ g.cfg.rules)
      (l : ParseTree g B) (r : ParseTree g C) (b : Spine g l) :
      Spine g (.node A B C h l r)
  | downRight (A B C : g.cfg.NT)
      (h : ({ input := A, output := [Symbol.nonterminal B, Symbol.nonterminal C] } :
        ContextFreeRule T g.cfg.NT) ∈ g.cfg.rules)
      (l : ParseTree g B) (r : ParseTree g C) (b : Spine g r) :
      Spine g (.node A B C h l r)
```

`vars` は分岐の各段で通過した非終端記号だけを取り出したラベル列である。鳩の巣原理を適用する対象はまさにこのラベル列であり、その長さが非終端記号の総数を超えれば重複が保証される――これが `exists_pump` の核心的な論法になる。

```lean
namespace Spine

/-- Variables encountered along a branch. -/
public def vars {g : ChomskyNormalGrammar T} {A : g.cfg.NT}
    {t : ParseTree g A} : Spine g t → List g.cfg.NT
  | .stop A _ => [A]
  | .downLeft A _ _ _ _ _ b => A :: vars b
  | .downRight A _ _ _ _ _ b => A :: vars b
```

`longest` は木の高さを実現する枝、すなわち常により高い方の子へ降りる分岐を選ぶ。これにより `vars (longest t)` の長さがちょうど `t.height` になり（次の `vars_longest_length` が保証）、高い木を選べば選ぶほど長いラベル列を鳩の巣原理に投入できるようになる。

```lean
/-- Choose a branch whose length is the height of the tree. -/
public def longest {g : ChomskyNormalGrammar T} {A : g.cfg.NT}
    (t : ParseTree g A) : Spine g t :=
  match t with
  | .leaf A a h => .stop A (.leaf A a h)
  | .node A B C h l r =>
      if r.height ≤ l.height then
        .downLeft A B C h l r (longest l)
      else
        .downRight A B C h l r (longest r)
termination_by sizeOf t
```

`longest` が本当に高さを実現する枝を選んでいることの正当化であり、`exists_pump` で「枝の長さ `= m + 1`」から「非終端記号数 `m` を超えるラベル列」への橋渡しに使われる、この節の中心的な等式である。

```lean
@[grind =, simp] theorem vars_longest_length
    {g : ChomskyNormalGrammar T} {A : g.cfg.NT}
    (t : ParseTree g A) : (vars (longest t)).length = t.height := by
  induction t with
  | leaf => simp [longest, vars, ParseTree.height]
  | node A B C h l r ihl ihr =>
      simp only [longest]
      split
      · simp [vars, ParseTree.height, ihl, max_eq_left ‹_›, Nat.add_comm]
      · have hlr : l.height ≤ r.height := Nat.le_of_lt (Nat.lt_of_not_ge ‹_›)
        simp [vars, ParseTree.height, ihr, max_eq_right hlr, Nat.add_comm]
```

鳩の巣原理を機能させるには、ラベルの取りうる値の集合が有限でなければならない。この定理は任意の parse tree の根が文法の「実際に使われる非終端記号」の有限集合 `activeNonterminals` に属することを示し、次の `vars_mem_active` を通じて枝上の全ラベルがこの有限集合に収まることの出発点になる。

```lean
/-- The root variable of every parse tree occurs in the grammar's active support. -/
theorem root_mem_active
    {g : ChomskyNormalGrammar T} {A : g.cfg.NT} (t : ParseTree g A) :
    A ∈ ContextFreeGrammar.activeNonterminals g.cfg := by
  cases t with
  | leaf A a h => exact ContextFreeGrammar.rule_input_mem_activeNonterminals g.cfg h
  | node A B C h l r =>
      exact ContextFreeGrammar.rule_input_mem_activeNonterminals g.cfg h

grind_pattern root_mem_active =>
  ParseTree.height t, A ∈ ContextFreeGrammar.activeNonterminals g.cfg
```

`root_mem_active` を枝の各段に拡張し、`vars b` に現れるラベルがすべて有限集合 `activeNonterminals` の元であることを示す。`exists_pump` はこの事実と `vars_longest_length` を合わせて、枝の長さが `activeNonterminals` の濃度を超えれば重複が生じることを鳩の巣原理（`Finset.card_le_card` 経由）で導く。

```lean
@[grind .] theorem vars_mem_active
    {g : ChomskyNormalGrammar T} {A : g.cfg.NT} {t : ParseTree g A}
    (b : Spine g t) :
    ∀ X ∈ vars b, X ∈ ContextFreeGrammar.activeNonterminals g.cfg := by
  induction b with
  | stop A t =>
      intro X hX
      simp only [vars, List.mem_singleton] at hX
      subst X
      exact root_mem_active t
  | downLeft A B C h l r b ih =>
      intro X hX
      simp only [vars, List.mem_cons] at hX
      rcases hX with hEq | hX
      · subst X
        exact ContextFreeGrammar.rule_input_mem_activeNonterminals g.cfg h
      · exact ih X hX
  | downRight A B C h l r b ih =>
      intro X hX
      simp only [vars, List.mem_cons] at hX
      rcases hX with hEq | hX
      · subst X
        exact ContextFreeGrammar.rule_input_mem_activeNonterminals g.cfg h
      · exact ih X hX
```

枝上のある段にラベル `X` が現れれば、そのラベルの位置を穴とする文脈と、そこにある部分木を復元できる。`Spine` という「経路」の情報を `ParseCtx`／`ParseTree` という「差し込み可能な構造」に変換するこの補題が、次節で重複ラベルの二箇所を実際に二つの一穴文脈へ分解する際の直接の道具になる。

```lean
/-- An entry on a branch determines a subtree and the context above it. -/
@[grind .] theorem exists_context_of_mem
    {g : ChomskyNormalGrammar T} {A : g.cfg.NT} {t : ParseTree g A}
    (b : Spine g t) {X : g.cfg.NT} (hX : X ∈ vars b) :
    ∃ (c : ParseCtx g A X) (s : ParseTree g X), c.plug s = t := by
  induction b with
  | stop A t =>
      simp only [vars, List.mem_singleton] at hX
      subst X
      exact ⟨.hole A, t, rfl⟩
  | downLeft A B C h l r b ih =>
      simp only [vars, List.mem_cons] at hX
      rcases hX with hEq | hX
      · subst X
        exact ⟨.hole A, .node A B C h l r, rfl⟩
      · obtain ⟨c, s, hs⟩ := ih hX
        exact ⟨.left A B C X h c r, s, by simp [ParseCtx.plug, hs]⟩
  | downRight A B C h l r b ih =>
      simp only [vars, List.mem_cons] at hX
      rcases hX with hEq | hX
      · subst X
        exact ⟨.hole A, .node A B C h l r, rfl⟩
      · obtain ⟨c, s, hs⟩ := ih hX
        exact ⟨.right A B C X h l c, s, by simp [ParseCtx.plug, hs]⟩
```

## 反復する非終端記号から pump 可能な分解へ

spine 上の重複ラベルを二つの一穴文脈に分解し、同じ非終端記号を再訪する区間を反復可能にする。yield の分解と長さ境界を同時に保持して、木レベルの pumping 証人を構成する。

```lean
/-- A repeated variable on a branch gives a nontrivial self-context. -/
@[grind .] theorem exists_repeat_of_not_nodup
    {g : ChomskyNormalGrammar T} {A : g.cfg.NT} {t : ParseTree g A}
    (b : Spine g t) (hdup : ¬ (vars b).Nodup) :
    ∃ (X : g.cfg.NT) (cin : ParseCtx g X X) (s : ParseTree g X)
        (cmid : ParseCtx g A X),
      cmid.plug (cin.plug s) = t ∧ cin.IsProper := by
  induction b with
  | stop A t => simp [vars] at hdup
  | downLeft A B C h l r b ih =>
      simp only [vars, List.nodup_cons] at hdup
      by_cases hmem : A ∈ vars b
      · obtain ⟨d, s, hs⟩ := exists_context_of_mem b hmem
        exact ⟨A, .left A B C A h d r, s, .hole A,
          by simp [ParseCtx.plug, hs], by simp [ParseCtx.IsProper]⟩
      · have htail : ¬ (vars b).Nodup := by tauto
        obtain ⟨X, cin, s, cmid, hs, hp⟩ := ih htail
        exact ⟨X, cin, s, .left A B C X h cmid r,
          by simp [ParseCtx.plug, hs], hp⟩
  | downRight A B C h l r b ih =>
      simp only [vars, List.nodup_cons] at hdup
      by_cases hmem : A ∈ vars b
      · obtain ⟨d, s, hs⟩ := exists_context_of_mem b hmem
        exact ⟨A, .right A B C A h l d, s, .hole A,
          by simp [ParseCtx.plug, hs], by simp [ParseCtx.IsProper]⟩
      · have htail : ¬ (vars b).Nodup := by tauto
        obtain ⟨X, cin, s, cmid, hs, hp⟩ := ih htail
        exact ⟨X, cin, s, .right A B C X h l cmid,
          by simp [ParseCtx.plug, hs], hp⟩

end Spine
```

`exists_pump` はここまでの部品（`exists_subtree_height_eq`、`Spine.longest`、鳩の巣原理、`exists_repeat_of_not_nodup`）を組み合わせ、木レベルの pumping 分解を一つの定理としてまとめる。十分高い木からちょうど高さ `m + 1` の部分木を切り出し、その最長枝で重複ラベルを見つけて内側文脈 `cin` を得ることで、外側 `cout`・内側 `cin`・穴の中身 `s` への三分解と、反復部分の高さが `m + 1` を超えないという評価を同時に確立する。

```lean
/-- A sufficiently tall parse tree contains a repeated variable on a bounded
suffix of a root-to-leaf branch. -/


@[grind .] theorem ParseTree.exists_pump
    {g : ChomskyNormalGrammar T} {A : g.cfg.NT} (t : ParseTree g A)
    (hm : (ContextFreeGrammar.activeNonterminals g.cfg).card < t.height) :
    ∃ (X : g.cfg.NT) (cout : ParseCtx g A X)
        (cin : ParseCtx g X X) (s : ParseTree g X),
      cout.plug (cin.plug s) = t ∧ cin.IsProper ∧
      (cin.plug s).height ≤
        (ContextFreeGrammar.activeNonterminals g.cfg).card + 1 := by
  classical
  let m := (ContextFreeGrammar.activeNonterminals g.cfg).card
  have hk : 1 ≤ m + 1 := by omega
  have hkt : m + 1 ≤ t.height := by omega
  obtain ⟨X₀, c, t', ht', hh⟩ :=
    ParseTree.exists_subtree_height_eq t hk hkt
  let b := Spine.longest t'
  have hdup : ¬ (Spine.vars b).Nodup := by
    intro hn
    have hsubset :
        (Spine.vars b).toFinset ⊆ ContextFreeGrammar.activeNonterminals g.cfg := by
      intro X hX
      rw [List.mem_toFinset] at hX
      exact Spine.vars_mem_active b X hX
    have hcard := Finset.card_le_card hsubset
    rw [List.toFinset_card_of_nodup hn, Spine.vars_longest_length, hh] at hcard
    omega
  obtain ⟨X, cin, s, cmid, hmid, hproper⟩ :=
    Spine.exists_repeat_of_not_nodup b hdup
  refine ⟨X, c.compose cmid, cin, s, ?_, hproper, ?_⟩
  · rw [ParseCtx.plug_compose, hmid, ht']
  · calc
      (cin.plug s).height ≤ (cmid.plug (cin.plug s)).height :=
        ParseCtx.height_le_plug cmid _
      _ = t'.height := congrArg ParseTree.height hmid
      _ = m + 1 := hh
```

`exists_pump` の議論はここで完結する。以降は全く別の話題――一般の導出木を Chomsky 標準形の parse tree（または初期記号の空語導出）に変換する `CnfSymbolResult`／`CnfFormResult` の相互再帰的な仕様――であり、次節「導出と parse tree の往復」で使われる。

```lean
mutual
  /-- A generic derivation tree converted to either a CNF parse tree or the
  distinguished initial-symbol epsilon derivation. -/
  public inductive CnfSymbolResult (g : ChomskyNormalGrammar T) :
      Symbol T g.cfg.NT → List T → Prop
    | terminal (a : T) : CnfSymbolResult g (.terminal a) [a]
    | tree {A : g.cfg.NT} (t : ParseTree g A) :
        CnfSymbolResult g (.nonterminal A) t.yield
    | empty (A : g.cfg.NT) (hA : A = g.cfg.initial) :
        CnfSymbolResult g (.nonterminal A) []

  public inductive CnfFormResult (g : ChomskyNormalGrammar T) :
      List (Symbol T g.cfg.NT) → List T → Prop
    | nil : CnfFormResult g [] []
    | cons {x : Symbol T g.cfg.NT} {u : List T}
        {xs : List (Symbol T g.cfg.NT)} {v : List T}
        (head : CnfSymbolResult g x u) (tail : CnfFormResult g xs v) :
        CnfFormResult g (x :: xs) (u ++ v)
end
```

この補助定理は、ある規則 `r` の右辺 `r.output` から得られた `CnfFormResult`（右辺の各記号がそれぞれ何を導出するかの記録）を、規則を一段適用した結果としての `r.input` に対する `CnfSymbolResult` へまとめ上げる。CNF の規則は「終端一つ」「非終端二つ」「初期記号のみの空語」の三通りに限定される（`g.chomskyNormal`）ため、場合分けはちょうどこの三通りで尽き、終端規則では `ParseTree.leaf`、二項規則では二つの子木から `ParseTree.node` を組み立てる。この private 補題がなければ、次の `cnfFormResult_of_derivationTree` の帰納的な構成で規則適用のたびに同じ場合分けを書き下す必要が生じる。

```lean
@[grind .] private theorem cnfNonterminalResult
    (g : ChomskyNormalGrammar T)
    (r : ContextFreeRule T g.cfg.NT) (hr : r ∈ g.cfg.rules)
    {w : List T} (hc : CnfFormResult g r.output w) :
    CnfSymbolResult g (.nonterminal r.input) w := by
  rcases g.chomskyNormal r hr with hε | ⟨a, hout⟩ | ⟨B, C, hout⟩
  · rcases hε with ⟨hin, hout⟩
    rw [hout] at hc
    cases hc
    exact .empty r.input hin
  · rw [hout] at hc
    cases hc with
    | cons hs ht =>
        cases hs with
        | terminal =>
            cases ht
            let t : ParseTree g r.input :=
              ParseTree.leaf r.input a (by
                have heq :
                    ({ input := r.input, output := [Symbol.terminal a] } :
                      ContextFreeRule T g.cfg.NT) = r := by
                  cases r
                  simp_all
                rw [heq]
                exact hr)
            have hyield : t.yield = [a] := rfl
            rw [← hyield]
            exact CnfSymbolResult.tree t
  · rw [hout] at hc
    cases hc with
    | cons hsB rest =>
        cases rest with
        | cons hsC tail =>
            cases tail
            cases hsB with
            | tree tB =>
                cases hsC with
                | tree tC =>
                    let t : ParseTree g r.input :=
                      ParseTree.node r.input B C (by
                        have heq :
                            ({ input := r.input, output :=
                              [Symbol.nonterminal B, Symbol.nonterminal C] } :
                              ContextFreeRule T g.cfg.NT) = r := by
                          cases r
                          simp_all
                        rw [heq]
                        exact hr) tB tC
                    have hyield :
                        t.yield = tB.yield ++ tC.yield := rfl
                    simp only [List.append_nil]
                    rw [← hyield]
                    exact CnfSymbolResult.tree t
                | empty _ hC =>
                    exfalso
                    apply g.initial_not_output r hr
                    simp [hout, hC]
            | empty _ hB =>
                exfalso
                apply g.initial_not_output r hr
                simp [hout, hB]

```

## 導出と parse tree の往復

Chomsky 標準形の導出結果を分類し、非空な終端語の導出から `ParseTree` を復元する。文脈の反復 `nest` が yield 上では左右の反復部分に対応することもここで証明する。

```lean
@[grind .] theorem cnfFormResult_of_derivationTree
    {g : ChomskyNormalGrammar T}
    {xs : List (Symbol T g.cfg.NT)} {w : List T}
    (h : ContextFreeGrammar.DerivationFormTree g.cfg xs w) :
    CnfFormResult g xs w := by
  exact ContextFreeGrammar.DerivationFormTree.rec
    (motive_1 := fun x w _ => CnfSymbolResult g x w)
    (motive_2 := fun xs w _ => CnfFormResult g xs w)
    (fun a => CnfSymbolResult.terminal a)
    (fun r hr _ children ih => cnfNonterminalResult g r hr ih)
    CnfFormResult.nil
    (fun head tail ihHead ihTail => CnfFormResult.cons ihHead ihTail)
    h
```

これが「導出から parse tree へ」の往復を完成させる定理であり、`yield_derives` の逆方向にあたる。空語の場合を除外しているのは、`CnfSymbolResult.empty` が初期記号のみに許された特別なケースであって `ParseTree` には対応する値が存在しないためであり、この非空条件が pumping lemma 本体で `w ≠ []` を仮定してから木を取り出す理由になっている。

```lean
/-- A nonempty terminal derivation in CNF has a binary parse tree. -/
@[grind .] theorem ParseTree.exists_of_derives
    {g : ChomskyNormalGrammar T} {A : g.cfg.NT} {w : List T}
    (hw : w ≠ [])
    (h : g.cfg.Derives [Symbol.nonterminal A] (terminalSymbols w)) :
    ∃ t : ParseTree g A, t.yield = w := by
  have htree := ContextFreeGrammar.derivationFormTree_of_derives g.cfg h
  have hresult := cnfFormResult_of_derivationTree (g := g) htree
  cases hresult with
  | cons hs tail =>
      cases tail
      cases hs with
      | tree t => exact ⟨t, by simp⟩
      | empty _ _ => exact (hw rfl).elim
```

`nest` は proper な自己文脈 `cin : ParseCtx g X X` を `i` 回繰り返し差し込む操作であり、これがまさに pumping lemma で言う「`i` 回反復した語」を木のレベルで実現する構成である。`i = 0` では中身 `s` がそのまま残り、`i + 1` では一段外側にもう一度 `cin` を被せる再帰的な定義になっている。

```lean
/-- Repeatedly plug a self-context around a parse tree. -/
public def ParseCtx.nest {g : ChomskyNormalGrammar T} {X : g.cfg.NT}
    (c : ParseCtx g X X) (s : ParseTree g X) : Nat → ParseTree g X
  | 0 => s
  | i + 1 => c.plug (nest c s i)
```

これは `nest` の yield を計算するための純粋なリスト補題であり、文法や木とは無関係に、単語 `w` を `i` 回複製した平坦化リストと `w` 単体との可換性だけを述べる。次の `yield_nest` の帰納段でリストの結合順を入れ替えるために必要になる。

```lean
@[grind .] private theorem append_flatten_replicate_comm (w : List T) (i : Nat) :
    w ++ (List.replicate i w).flatten =
      (List.replicate i w).flatten ++ w := by
  induction i with
  | zero => simp
  | succ i ih =>
      simp only [List.replicate_succ, List.flatten_cons]
      rw [List.append_assoc, ih, ← List.append_assoc]

```

前補題の系として、`i + 1` 回複製した平坦化リストを「`i` 回複製したもの＋末尾に `w` を一つ」という形に書き換える。`yield_nest` の帰納法で `nest` の再帰的定義と `List.replicate` の再帰的定義の食い違いを揃えるために使う。

```lean
@[grind .] private theorem flatten_replicate_succ_right (w : List T) (i : Nat) :
    (List.replicate (i + 1) w).flatten =
      (List.replicate i w).flatten ++ w := by
  simpa [List.replicate_succ] using append_flatten_replicate_comm w i

```

この定理が pumping lemma 最終定理の反復条件そのものを与える。`i` 回反復した木の yield が `(replicate i preYield の平坦化) ++ 穴の yield ++ (replicate i postYield の平坦化)` に一致することを示し、これによって `Language.IsContextFree.pumping_lemma` の結論にある `u ++ (replicate i v).flatten ++ x ++ (replicate i y).flatten ++ z ∈ L` という形の式がそのまま導ける。

```lean
@[grind =, simp] theorem ParseCtx.yield_nest
    {g : ChomskyNormalGrammar T} {X : g.cfg.NT}
    (c : ParseCtx g X X) (s : ParseTree g X) (i : Nat) :
    (c.nest s i).yield =
      (List.replicate i c.preYield).flatten ++ s.yield ++
        (List.replicate i c.postYield).flatten := by
  induction i with
  | zero => simp [ParseCtx.nest]
  | succ i ih =>
      simp only [ParseCtx.nest, ParseCtx.yield_plug, ih]
      rw [flatten_replicate_succ_right]
      simp only [List.replicate_succ, List.flatten_cons]
      simp only [List.append_assoc]
      let p := (List.replicate i c.preYield).flatten
      let q := (List.replicate i c.postYield).flatten
      change c.preYield ++ (p ++ (s.yield ++ (q ++ c.postYield))) =
        p ++ (c.preYield ++ (s.yield ++ (c.postYield ++ q)))
      calc
        c.preYield ++ (p ++ (s.yield ++ (q ++ c.postYield))) =
            (c.preYield ++ p) ++ (s.yield ++ (q ++ c.postYield)) :=
          (List.append_assoc _ _ _).symm
        _ = (p ++ c.preYield) ++ (s.yield ++ (q ++ c.postYield)) := by
          rw [append_flatten_replicate_comm c.preYield i]
        _ = (p ++ c.preYield) ++ (s.yield ++ (c.postYield ++ q)) := by
          rw [← append_flatten_replicate_comm c.postYield i]
        _ = p ++ (c.preYield ++ (s.yield ++ (c.postYield ++ q))) := by
          simp [List.append_assoc]
```

## 言語レベルの pumping lemma

これがモジュールの最終契約であり、ここまでの木レベルの構成をすべて起動する。与えられた文脈自由言語 `L` を、その定義（ある文法 `g₀` の言語であること）から一旦 Chomsky 標準形の文法 `g` に変換し、`p := 2 ^ m`（`m` は `g` の実効非終端記号数）を pumping 定数として選ぶ。長さ `p` 以上の任意の語 `w ∈ L` に対して、非空性から parse tree `t` を得（`exists_of_derives`）、`yield_length_le` の対偶で `t` の高さが `m` を超えることを導き、`exists_pump` で反復可能な三分解 `cout, cin, s` を取り出す。最後に `cin.nest s i` を通じて、全ての反復回数 `i` について書き換えられた語がやはり `g` の言語（ひいては元の `L`）に属することを `yield_derives` と `mem_language_iff` で確認する。空語 `w = []` は長さの仮定 `p ≤ w.length` と `p ≥ 1` から排除され、反復部分の非自明性 `v ++ y ≠ []` は `proper_yield_pos` から従う。

```lean
/-- Every context-free language satisfies the pumping lemma. -/
@[grind ., important] public theorem Language.IsContextFree.pumping_lemma
    {T : Type} {L : Language T} (h : L.IsContextFree) :
    ∃ p ≥ 1, ∀ w ∈ L, p ≤ w.length →
      ∃ u v x y z, w = u ++ v ++ x ++ y ++ z ∧
        (v ++ x ++ y).length ≤ p ∧ v ++ y ≠ [] ∧
        ∀ i : ℕ, u ++ (List.replicate i v).flatten ++ x ++
          (List.replicate i y).flatten ++ z ∈ L := by
  rcases h with ⟨g₀, rfl⟩
  let g := ContextFreeGrammar.Classical.toChomskyNormalGrammar g₀
  let m := (ContextFreeGrammar.activeNonterminals g.cfg).card
  have hp : 1 ≤ 2 ^ m := by simpa using Nat.one_le_pow' m 1
  refine ⟨2 ^ m, hp, ?_⟩
  intro w hw hlen
  have hwg : w ∈ g.language := by simpa [g] using hw
  have hwne : w ≠ [] := by
    intro heq
    subst w
    simp at hlen
  have hder :
      g.cfg.Derives [Symbol.nonterminal g.cfg.initial] (terminalSymbols w) :=
    (ContextFreeGrammar.mem_language_iff g.cfg w).mp hwg
  obtain ⟨t, htYield⟩ := ParseTree.exists_of_derives hwne hder
  have hpows : 2 ^ m ≤ 2 ^ (t.height - 1) := by
    calc
      2 ^ m ≤ w.length := hlen
      _ = t.yield.length := congrArg List.length htYield |>.symm
      _ ≤ 2 ^ (t.height - 1) := ParseTree.yield_length_le t
  have hmheight : m < t.height := by
    have hexp : m ≤ t.height - 1 :=
      (Nat.pow_le_pow_iff_right (by omega)).mp hpows
    exact lt_of_le_of_lt hexp
      (Nat.sub_lt (ParseTree.one_le_height t) (by omega))
  obtain ⟨X, cout, cin, s, htree, hproper, hheight⟩ :=
    ParseTree.exists_pump t hmheight
  let u := cout.preYield
  let v := cin.preYield
  let x := s.yield
  let y := cin.postYield
  let z := cout.postYield
  refine ⟨u, v, x, y, z, ?_, ?_, ?_, ?_⟩
  · calc
      w = t.yield := htYield.symm
      _ = (cout.plug (cin.plug s)).yield :=
        congrArg ParseTree.yield htree |>.symm
      _ = u ++ v ++ x ++ y ++ z := by
        simp [u, v, x, y, z, ParseCtx.yield_plug, List.append_assoc]
  · have hyield := ParseTree.yield_length_le (cin.plug s)
    have hexp : (cin.plug s).height - 1 ≤ m := by omega
    have hpow : 2 ^ ((cin.plug s).height - 1) ≤ 2 ^ m :=
      Nat.pow_le_pow_right (by omega) hexp
    calc
      (v ++ x ++ y).length = (cin.plug s).yield.length := by
        simp [v, x, y, ParseCtx.yield_plug]
      _ ≤ 2 ^ ((cin.plug s).height - 1) := hyield
      _ ≤ 2 ^ m := hpow
  · intro hempty
    have hpos := ParseCtx.proper_yield_pos cin hproper
    rw [show v ++ y = cin.preYield ++ cin.postYield by rfl, hempty] at hpos
    simp at hpos
  · intro i
    have hd := ParseTree.yield_derives (cout.plug (cin.nest s i))
    have hyield :
        (cout.plug (cin.nest s i)).yield =
          u ++ (List.replicate i v).flatten ++ x ++
            (List.replicate i y).flatten ++ z := by
      simp [u, v, x, y, z, ParseCtx.yield_plug, ParseCtx.yield_nest,
        List.append_assoc]
    have hmemg :
        u ++ (List.replicate i v).flatten ++ x ++
            (List.replicate i y).flatten ++ z ∈ g.language := by
      apply (ContextFreeGrammar.mem_language_iff g.cfg _).mpr
      simpa [hyield] using hd
    simpa [g] using hmemg
```

これでモジュール本体の証明は完結する。以下は名前空間 `Mathling.Grammar` を閉じるだけの構文的な締めくくりであり、新たな宣言は導入しない。

```lean
end Mathling.Grammar

```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
