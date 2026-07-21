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

```lean
namespace NFA

```

```lean
open RegularExpression

```

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

```lean
private theorem RestrictedPath.ofPath_univ
    {M : NFA α σ} {p q : σ} {word : List α}
    (h : M.Path p q word) : RestrictedPath M Set.univ p q word := by
  induction h with
  | nil p => exact .nil p
  | cons mid p q a word edge rest ih =>
      exact .cons edge ih (Or.inr (Set.mem_univ mid))
```

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

```lean
private def unionAll : List (RegularExpression α) → RegularExpression α
  | [] => empty
  | r :: rs => union r (unionAll rs)

```

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

```lean
private noncomputable def edgeRegex [Fintype α]
    (M : NFA α σ) (p q : σ) : RegularExpression α := by
  classical
  exact unionAll ((Finset.univ.filter fun a => q ∈ M.step p a).toList.map symbol)
```

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

```lean
private noncomputable def baseRegex [Fintype α]
    (M : NFA α σ) (p q : σ) : RegularExpression α := by
  classical
  exact union (if p = q then epsilon else empty) (edgeRegex M p q)
```

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
