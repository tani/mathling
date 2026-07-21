    module

    public import Mathling.Automata.Regex
    public import Mathling.Automata.Core

    import LiterateLean
    open scoped LiterateLean


# Mathling / Automata / Regular / Kleene モジュール

有限 alphabet 上の NFA を正規表現へ変換する状態除去法を実装する。除去済み状態の集合を
経路の中間状態に対する許可集合として解釈し、新しい状態 `k` を追加したときの経路を
`k` を通らない場合と、`k` への入口・自己 loop 列・出口を通る場合へ分解する。

```math
R_{S \cup \{k\}}(p,q)
=R_S(p,q)+R_S(p,k)\,R_S(k,k)^*\,R_S(k,q).
```

```mermaid
flowchart LR
    P["p"] -->|"R_S(p,k)"| K["k"]
    K -->|"R_S(k,k)*"| K
    K -->|"R_S(k,q)"| Q["q"]
```

`RestrictedPath` がこの式の意味論的不変条件である。入力文字を一つ読む通常の NFA path
だけを扱うため、空語経路は反射経路だけであり、基底式は epsilon と一文字遷移の和になる。

```lean
namespace Mathling.Automata

```

状態除去アルゴリズムはこの後の補題群を通じて `NFA` 名前空間の内部に閉じる。以降の宣言はすべて非公開 (`private`) であり、公開されるのは最終的な `toRegex` と `toRegex_language` だけである。

```lean
namespace NFA

```

正規表現側の演算子名 (`union`, `concat`, `star`, `epsilon`, `symbol` など) を裸の識別子として使うため、`RegularExpression` 名前空間を開く。

```lean
open RegularExpression

```

`RestrictedPath M allowed p q word` は、`p` から `q` への `word` を読む NFA の経路のうち、途中に現れる状態がすべて `allowed` に属するものだけを表す。`allowed` を空集合から始めて一状態ずつ増やしていく（状態除去法の核心）ための補助的な帰納述語であり、以降のすべての補題はこの述語の性質として述べられる。

```lean
variable {α σ : Type*}

/-- An NFA path whose proper intermediate states lie in `allowed`. -/
@[grind cases] private inductive RestrictedPath (M : NFA α σ) (allowed : Set σ) :
    σ → σ → List α → Prop
  | nil (p : σ) : RestrictedPath M allowed p p []
  | cons {p mid q : σ} {a : α} {word : List α}
      (edge : mid ∈ M.step p a)
      (rest : RestrictedPath M allowed mid q word)
      (internal : word = [] ∨ mid ∈ allowed) :
      RestrictedPath M allowed p q (a :: word)

```

`allowed` による制約は「経路が存在するかどうか」自体には影響しない——制約を忘れれば普通の `Path` が得られる、という一方向の埋め込みを与える。これにより、最終的に `RestrictedPath` で構成した正規表現の言語が本物の NFA の受理語を含むことを示せる。

```lean
@[grind .] private theorem RestrictedPath.toPath
    {M : NFA α σ} {allowed : Set σ} {p q : σ} {word : List α}
    (h : RestrictedPath M allowed p q word) : Nonempty (M.Path p q word) := by
  induction h with
  | nil p => exact ⟨.nil p⟩
  | cons edge rest internal ih =>
      rcases ih with ⟨path⟩
      exact ⟨.cons _ _ _ _ _ edge path⟩
```

逆方向: 任意の NFA の `Path` は、制約集合を状態全体 `Set.univ` にとれば必ず `RestrictedPath` として実現できる。`toRegex` の最終定理は、状態集合全体を許可した `eliminate` がもとの NFA と同じ言語を持つことを示す必要があるため、この極限ケースへの持ち上げが不可欠になる。

```lean
private theorem RestrictedPath.ofPath_univ
    {M : NFA α σ} {p q : σ} {word : List α}
    (h : M.Path p q word) : RestrictedPath M Set.univ p q word := by
  induction h with
  | nil p => exact .nil p
  | cons mid p q a word edge rest ih =>
      exact .cons edge ih (Or.inr (Set.mem_univ mid))
```

許可集合を大きくしても、既に成り立っていた `RestrictedPath` は成り立ち続ける（単調性）。これは状態除去法で許可集合を一状態ずつ増やしていく際、「まだ除去していない状態だけを通る経路」を「今除去した状態を通ってよい経路」へ横滑りさせるために使う基本補題であり、後続の `restrictedPath_insert_iff` の両方向でともに利用される。

```lean
@[grind .] private theorem RestrictedPath.mono
    {M : NFA α σ} {S U : Set σ} (hSU : S ⊆ U)
    {p q : σ} {word : List α} (h : RestrictedPath M S p q word) :
    RestrictedPath M U p q word := by
  induction h with
  | nil p => exact .nil p
  | cons edge rest internal ih =>
      exact .cons edge ih (internal.imp_right fun h => hSU h)

```

同じ許可集合のもとでの二つの `RestrictedPath` を、中間状態 `mid` が許可集合に属している限り連結できる。状態除去の式 $`R_{S\cup\{k\}}(p,q)=R_S(p,q)+R_S(p,k)\,R_S(k,k)^*\,R_S(k,q)`$ の右辺（入口・自己 loop・出口の連結）を構成的に組み立てるための土台であり、直後の `restrictedPath_insert_iff` の逆方向で三つの `RestrictedPath` を貼り合わせるのに使われる。

```lean
@[grind .] private theorem RestrictedPath.append
    {M : NFA α σ} {S : Set σ} {p mid q : σ} {u v : List α}
    (hmid : mid ∈ S) (hu : RestrictedPath M S p mid u)
    (hv : RestrictedPath M S mid q v) :
    RestrictedPath M S p q (u ++ v) := by
  induction hu with
  | nil p => simpa using hv
  | @cons p next mid a word edge rest internal ih =>
      simp only [List.cons_append]
      apply RestrictedPath.cons edge (ih hmid hv)
      by_cases hword : word = []
      · right
        have hnext : next = mid := by
          subst word
          cases rest
          rfl
        simpa [hnext] using hmid
      · exact internal.resolve_left hword |> Or.inr
```

状態除去法そのものを述語のレベルで実証する中心定理。新しく状態 `k` を許可集合に加えたときの `RestrictedPath` を、「`k` を全く通らない経路」と「`k` への入口 `pre`・`k` 上の自己 loop 列 `loops`・`k` からの出口 `suffix` に分解できる経路」の直和として特徴づける。順方向は `Path` の帰納法で `k` を最初に通る場所ごとに場合分けし、逆方向は `RestrictedPath.append` を繰り返し使って三つの断片を貼り戻す。この同値が成り立たなければ、以下の正規表現側の `eliminate` 漸化式が言語として正しいことを主張できない。

```lean
/-- The state-elimination decomposition at one newly allowed state. -/
@[grind .] private theorem restrictedPath_insert_iff
    (M : NFA α σ) (S : Set σ) (k p q : σ) (word : List α) :
    RestrictedPath M (insert k S) p q word ↔
      RestrictedPath M S p q word ∨
      ∃ (pre : List α) (loops : List (List α)) (suffix : List α),
        RestrictedPath M S p k pre ∧
        (∀ loop ∈ loops, RestrictedPath M S k k loop) ∧
        RestrictedPath M S k q suffix ∧
        word = pre ++ loops.flatten ++ suffix := by
  constructor
  · intro h
    induction h with
    | nil p => exact Or.inl (.nil p)
    | @cons p mid q a restWord edge rest internal ih =>
        rcases internal with rfl | hmid
        · left
          cases rest
          exact .cons edge (.nil mid) (Or.inl rfl)
        · rcases Set.mem_insert_iff.mp hmid with rfl | hmidS
          · rcases ih with hrest | ⟨pre, loops, suffix, hp, hloops, hs, hword⟩
            · right
              exact ⟨[a], [], restWord, .cons edge (.nil mid) (Or.inl rfl),
                by simp, hrest, by simp⟩
            · right
              exact ⟨[a], pre :: loops, suffix,
                .cons edge (.nil mid) (Or.inl rfl), by
                  intro loop hloop
                  rcases List.mem_cons.mp hloop with rfl | hloop
                  · exact hp
                  · exact hloops loop hloop,
                hs, by simp [hword, List.append_assoc]⟩
          · rcases ih with hrest | ⟨pre, loops, suffix, hp, hloops, hs, hword⟩
            · left
              exact .cons edge hrest (Or.inr hmidS)
            · right
              exact ⟨a :: pre, loops, suffix,
                .cons edge hp (Or.inr hmidS), hloops, hs,
                by simp [hword, List.append_assoc]⟩
  · rintro (h | ⟨pre, loops, suffix, hp, hloops, hs, hword⟩)
    · exact h.mono (Set.subset_insert k S)
    · subst word
      have hk : k ∈ insert k S := Set.mem_insert k S
      have hp' := hp.mono (Set.subset_insert k S)
      have hs' := hs.mono (Set.subset_insert k S)
      have hloops' : RestrictedPath M (insert k S) k k loops.flatten := by
        induction loops with
        | nil => exact .nil k
        | cons loop loops ih =>
            simp only [List.flatten_cons]
            exact (hloops loop (by simp)).mono (Set.subset_insert k S) |>.append hk
              (ih (by
                intro x hx
                exact hloops x (by simp [hx])))
      exact (hp'.append hk hloops').append hk hs'
```

## 正規表現側の状態除去

`unionAll` は有限個の正規表現の和である。基底 `edgeRegex` は alphabet を列挙して一文字
遷移を集め、`baseRegex` は反射 epsilon 経路を加える。`eliminate` は上の漸化式を状態列に
沿って反復する。

有限本の正規表現を一つの和にまとめる補助関数。`toRegex` は「開始状態から受理状態への `eliminate` 結果」を全ペアぶん `unionAll` で束ねるので、ここが有限個の場合分けを一つの正規表現に潰す唯一の場所になる。

```lean
private def unionAll : List (RegularExpression α) → RegularExpression α
  | [] => empty
  | r :: rs => union r (unionAll rs)

```

`unionAll` の言語が要素の言語の和集合（存在量化）に一致することを述べる。`edgeRegex`・`toRegex` のどちらも `unionAll` で組んだ式の言語的な意味を扱うため、以降のほぼすべての言語同値の証明はこの補題を経由する。

```lean
@[grind =, simp] private theorem mem_language_unionAll
    (rs : List (RegularExpression α)) (word : List α) :
    word ∈ language (unionAll rs) ↔ ∃ r ∈ rs, word ∈ language r := by
  induction rs with
  | nil => simp [unionAll]
  | cons r rs ih =>
      simp only [unionAll, language_union, Language.mem_add, ih, List.mem_cons]
      constructor
      · rintro (hr | ⟨s, hs, hword⟩)
        · exact ⟨r, Or.inl rfl, hr⟩
        · exact ⟨s, Or.inr hs, hword⟩
      · rintro ⟨s, rfl | hs, hword⟩
        · exact Or.inl hword
        · exact Or.inr ⟨s, hs, hword⟩
```

状態除去の漸化式の基底部分のうち「一文字で `p` から `q` へ直接遷移する」部分を正規表現化する。alphabet を有限として列挙し、`q ∈ M.step p a` を満たす記号 `a` すべてについて `symbol a` の和をとる。これが空語を含まないちょうど長さ 1 の言語になることが、次の `baseRegex` で epsilon 経路と正しく切り分けるために必要になる。

```lean
private noncomputable def edgeRegex [Fintype α]
    (M : NFA α σ) (p q : σ) : RegularExpression α := by
  classical
  exact unionAll ((Finset.univ.filter fun a => q ∈ M.step p a).toList.map symbol)
```

`edgeRegex` の言語が「`p` から `q` へ一文字 `a` で遷移できる」という NFA の遷移関係とちょうど一致することを述べる。以降 `baseRegex` や `eliminate` の正しさの証明はこの言語的意味づけを土台にする。

```lean
@[grind =] private theorem mem_language_edgeRegex [Fintype α]
    (M : NFA α σ) (p q : σ) (word : List α) :
    word ∈ language (edgeRegex M p q) ↔
      ∃ a, q ∈ M.step p a ∧ word = [a] := by
  classical
  rw [edgeRegex, mem_language_unionAll]
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, ⟨a, edge, rfl⟩, hword⟩
    exact ⟨a, edge, Set.mem_singleton_iff.mp hword⟩
  · rintro ⟨a, edge, rfl⟩
    exact ⟨symbol a, ⟨a, edge, rfl⟩, Set.mem_singleton [a]⟩
```

状態除去漸化式の基底ケース（許可集合が空のとき）そのもの。`p = q` なら反射的な空語経路を `epsilon` で表し、そうでなければ一文字遷移だけを `edgeRegex` で表す。この if 分岐が正しいのは、許可集合が空だと `RestrictedPath` の経路は長さ 0 か長さ 1 しかありえないためであり、`mem_language_baseRegex` がその事実を証明する。

```lean
private noncomputable def baseRegex [Fintype α]
    (M : NFA α σ) (p q : σ) : RegularExpression α := by
  classical
  exact union (if p = q then epsilon else empty) (edgeRegex M p q)
```

`baseRegex` の言語が「許可集合を空にした `RestrictedPath`」とちょうど一致することを述べ、状態除去帰納法 (`eliminate`) の基底段 (`states = []`) の正しさを保証する。

```lean
@[grind =] private theorem mem_language_baseRegex [Fintype α]
    (M : NFA α σ) (p q : σ) (word : List α) :
    word ∈ language (baseRegex M p q) ↔
      RestrictedPath M ∅ p q word := by
  classical
  constructor
  · intro h
    simp only [baseRegex, language_union, Language.mem_add] at h
    rcases h with h | h
    · split at h
      next heq =>
        subst q
        have hword : word = [] := by simpa using h
        subst word
        exact .nil p
      next hne => simp at h
    · rcases (mem_language_edgeRegex M p q word).mp h with ⟨a, edge, rfl⟩
      exact .cons edge (.nil q) (Or.inl rfl)
  · intro h
    cases h with
    | nil p =>
        simp only [baseRegex, language_union, Language.mem_add]
        exact Or.inl (by simp)
    | @cons p mid q a restWord edge rest internal =>
        have hrest : restWord = [] := by
          rcases internal with h | h
          · exact h
          · exact (Set.notMem_empty mid h).elim
        subst restWord
        cases rest
        simp only [baseRegex, language_union, Language.mem_add]
        exact Or.inr ((mem_language_edgeRegex M p _ [a]).mpr ⟨a, edge, rfl⟩)
```

状態除去アルゴリズムの中心となる再帰定義。`states` に列挙された状態を一つずつ「除去」しながら、冒頭の漸化式 $`R_{S\cup\{k\}}(p,q)=R_S(p,q)+R_S(p,k)\,R_S(k,k)^*\,R_S(k,q)`$ をそのまま正規表現の演算 (`union`, `concat`, `star`) へ翻訳する。基底は `baseRegex`、状態を一つ増やすたびに `k` を経由する部分を `star` で束ねる。

```lean
private noncomputable def eliminate [Fintype α]
    (M : NFA α σ) : List σ → σ → σ → RegularExpression α
  | [], p, q => baseRegex M p q
  | k :: states, p, q =>
      union (eliminate M states p q)
        (concat (concat (eliminate M states p k)
          (star (eliminate M states k k)))
          (eliminate M states k q))
```

`eliminate` の再帰定義が実際にこの漸化式の意味を持つことを、`restrictedPath_insert_iff` を使って状態リストに関する帰納法で証明する。これが `RestrictedPath` の組合せ論的な性質を正規表現の言語同値へ変換する要となる補題であり、最終的な `toRegex_language` はこの補題を状態全体に適用するだけで得られる。

```lean
@[grind =] private theorem mem_language_eliminate [Fintype α]
    (M : NFA α σ) (states : List σ) (p q : σ) (word : List α) :
    word ∈ language (eliminate M states p q) ↔
      RestrictedPath M {s | s ∈ states} p q word := by
  induction states generalizing p q word with
  | nil => simpa [eliminate] using mem_language_baseRegex M p q word
  | cons k states ih =>
      rw [show ({s | s ∈ k :: states} : Set σ) = insert k {s | s ∈ states} by ext; simp]
      rw [restrictedPath_insert_iff]
      simp only [eliminate, language_union, Language.mem_add, language_concat,
        Language.mem_mul, language_star, Language.mem_kstar, ih]
      constructor
      · rintro (direct | ⟨joined, hj, suffix, hs, hjoin⟩)
        · exact Or.inl direct
        · rcases hj with ⟨pre, hp, loopWord, hloops, rfl⟩
          rcases hloops with ⟨loops, hloopWord, hloops⟩
          subst loopWord
          exact Or.inr ⟨pre, loops, suffix, hp, hloops, hs, hjoin.symm⟩
      · rintro (direct | ⟨pre, loops, suffix, hp, hloops, hs, hword⟩)
        · exact Or.inl direct
        · right
          refine ⟨pre ++ loops.flatten, ?_, suffix, hs, ?_⟩
          · exact ⟨pre, hp, loops.flatten,
              ⟨loops, rfl, hloops⟩, rfl⟩
          · simpa [List.append_assoc] using hword.symm

```

## 公開変換と正当性

全状態を許可した `eliminate` を開始状態・受理状態の全組について有限和にする。最終定理は
NFA の `Path` 特徴付けと `RestrictedPath` の忘却・持ち上げを合成し、状態除去後の正規表現が
元の受理言語と外延的に等しいことを述べる。

```lean
/-- State-elimination conversion from a finite NFA over a finite alphabet. -/
public noncomputable def toRegex [Fintype α] [Fintype σ]
    (M : NFA α σ) : RegularExpression α := by
  classical
  let states : List σ := Finset.univ.toList
  let starts : List σ := (Finset.univ.filter fun p => p ∈ M.start).toList
  let accepts : List σ := (Finset.univ.filter fun q => q ∈ M.accept).toList
  exact unionAll (starts.flatMap fun p => accepts.map fun q => eliminate M states p q)
```

`toRegex` の正しさは、NFA の `accepts_iff_exists_path`（開始状態から受理状態への `Path` として受理を特徴づける）と、`mem_language_eliminate` を `states` 全体に適用したもの（`RestrictedPath.toPath`／`RestrictedPath.ofPath_univ` で `RestrictedPath` と生の `Path` を行き来する）を組み合わせて示す。`@[important]` が付いたこの定理が、本モジュール冒頭で述べた「NFA を正規表現へ変換する状態除去法」の公開契約そのものである。

```lean
/-- State elimination preserves the accepted language. -/
@[important, grind =, simp] public theorem toRegex_language [Fintype α] [Fintype σ]
    (M : NFA α σ) : language M.toRegex = M.accepts := by
  classical
  ext word
  rw [NFA.accepts_iff_exists_path]
  simp only [toRegex, mem_language_unionAll, List.mem_flatMap, List.mem_map,
    Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨r, ⟨p, hp, q, hq, rfl⟩, hr⟩
    have hrestricted := (mem_language_eliminate M Finset.univ.toList p q word).mp hr
    exact ⟨p, hp, q, hq, hrestricted.toPath⟩
  · rintro ⟨p, hp, q, hq, ⟨path⟩⟩
    refine ⟨eliminate M Finset.univ.toList p q, ?_, ?_⟩
    · exact ⟨p, hp, q, hq, rfl⟩
    · apply (mem_language_eliminate M Finset.univ.toList p q word).mpr
      simpa using RestrictedPath.ofPath_univ path

end NFA

end Mathling.Automata
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
