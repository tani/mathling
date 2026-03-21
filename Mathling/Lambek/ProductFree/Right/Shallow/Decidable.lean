import Mathlib.Data.Bool.Basic
import Mathlib.Data.List.Basic
import Mathling.Lambek.ProductFree.Right.Shallow.Basic
import Lean.LibrarySuggestions.Default
import LiterateLean

# Lambek 計算の決定可能性の証明 (Shallow)

このファイルでは、Shallowな右除法のみを含むLambek計算において、
与えられたシーケントに対して証明が存在するかどうかを判定する手続きが決定可能であることを証明する。

```lean
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.maxHeartbeats false
namespace Mathling.Lambek.ProductFree.Right.Shallow
```

## 非決定的なリスト操作

### 分割

```lean
@[grind]
def splits {α} : List α → List (List α × List α)
  | [] => [([], [])]
  | x :: xs => ([], x :: xs) :: (splits xs).map (fun (l, r) => (x :: l, r))

@[grind .]
lemma splits_list_degree (h : X ∈ splits Γ) :
  X.1 ++ X.2 = Γ := by
  induction Γ generalizing X <;> grind

@[grind .]
lemma splits_mem {α} (Γ Δ : List α) : (Γ, Δ) ∈ splits (Γ ++ Δ) := by
  induction Γ with
  | nil =>
      cases Δ <;> simp [splits]
  | cons x xs ih =>
      apply List.mem_cons_of_mem
      refine List.mem_map.mpr ?_
      refine ⟨(xs, Δ), ih, ?_⟩
      simp
```

### 選択

```lean
@[grind]
def picks {α} : List α → List (List α × α × List α)
  | [] => []
  | x :: xs => ([], x, xs) :: (picks xs).map (fun (l, a, r) => (x :: l, a, r))

@[grind =>]
lemma picks_list_degree (h : X ∈ picks Γ) :
   X.1 ++ [X.2.1] ++ X.2.2 = Γ := by
  induction Γ generalizing X <;> grind

@[grind .]
lemma picks_mem {α} (Γ Δ : List α) (a : α) :
    (Γ, a, Δ) ∈ picks (Γ ++ [a] ++ Δ) := by
  induction Γ with
  | nil => simp [picks]
  | cons x xs ih =>
      apply List.mem_cons_of_mem
      refine List.mem_map.mpr ?_
      refine ⟨(xs, a, Δ), ?_, ?_⟩
      · simpa [List.append_assoc] using ih
      · simp
```

## 証明探索の候補

```lean
@[grind]
inductive Cand where
  | rdiv (L : List Tp) (B A : String) (Δ Λ : List Tp)

@[grind]
def candidates (Γ : List Tp) : List Cand :=
  (picks Γ).flatMap (fun (L, f, R) =>
    match f with
    | B ⧸ A =>
        (splits R).map (fun (Δ, Λ) => .rdiv L B A Δ Λ)
    | # _ => [])

@[grind =>]
lemma candidates_list_degree (h : c ∈ candidates Γ) :
  match c with
    | .rdiv L B A Δ Λ => L ++ [B ⧸ A] ++ Δ ++ Λ = Γ := by
  simp only [candidates, List.mem_flatMap, Prod.exists] at h
  rcases h with ⟨L, f, R, h_pick, h_cand⟩
  cases f with
  | atom s =>
      grind
  | rdiv B A =>
      simp only [List.mem_map, Prod.exists] at h_cand
      rcases h_cand with ⟨X, Y, hX, rfl⟩
      have h_split : X ++ Y = R := splits_list_degree hX
      grind

@[grind .]
lemma candidates_rdiv_mem (Γ Δ Λ : List Tp) (A B : String) :
  Cand.rdiv Γ B A Δ Λ ∈ candidates (Γ ++ [B ⧸ A] ++ Δ ++ Λ) := by
  unfold candidates
  refine List.mem_flatMap.mpr ?_
  refine ⟨(Γ, B ⧸ A, Δ ++ Λ), ?_, ?_⟩
  · grind
  · refine List.mem_map.mpr ?_
    refine ⟨(Δ, Λ), ?_, ?_⟩ <;> grind
```

## 決定可能手続きの定義

```lean
@[grind .]
def prove1 (Γ : List Tp) (A : Tp) : Bool :=
  match A with
  | Tp.atom s =>
    (Γ = [Tp.atom s]) ||
    (candidates Γ).attach.any (fun ⟨c, _hc⟩ =>
      match c with
      | .rdiv L B A' Δ Λ =>
        prove1 Δ (# A') && prove1 (L ++ [# B] ++ Λ) (# s))
  | Tp.rdiv B A' =>
    Γ ≠ [] && prove1 (Γ ++ [# A']) (# B)
termination_by
  list_degree Γ + tp_degree A
decreasing_by
  all_goals grind

@[grind .]
def proveAux : Nat → List Tp → Tp → Bool
  | 0, _,  _ => false
  | n + 1, Γ,  A =>
    match A with
    | Tp.atom s =>
        (Γ = [Tp.atom s]) ||
        (candidates Γ).any (fun c =>
          match c with
          | .rdiv L B A' Δ Λ =>
              proveAux n Δ (# A') &&
              proveAux n (L ++ [# B] ++ Λ) (# s))
    | Tp.rdiv B A' =>
        (Γ ≠ []) && proveAux n (Γ ++ [# A']) (# B)

@[grind .]
def prove2 (Γ : List Tp) (A : Tp) : Bool :=
  proveAux (list_degree Γ + tp_degree A + 1) Γ A
```

性質の証明：

```lean
@[grind =>]
lemma proveAux_mono (h : proveAux n Γ A) :
  proveAux (n + 1) Γ A := by
  induction n generalizing Γ A <;> grind

@[grind =>]
lemma proveAux_mono_le {n m : Nat} (h : n ≤ m) (hp : proveAux n Γ A) :
    proveAux m Γ A := by
  induction h <;> grind
```

健全性：

```lean
@[grind =>]
lemma proveAux_sound (h : proveAux n Γ A) : prove1 Γ A := by
  induction n generalizing Γ A with
  | zero => grind
  | succ n ih =>
      cases A with
      | atom s =>
        simp only [proveAux, Bool.or_eq_true, List.any_eq_true] at h
        unfold prove1
        simp only [Bool.or_eq_true]
        rcases h with h_base | h_cand
        · grind
        · right
          rcases h_cand with ⟨c, hc_mem, hc_val⟩
          simp only [List.any_eq_true]
          refine ⟨⟨c, hc_mem⟩, by simp, ?_⟩
          grind
      | rdiv B A' => grind
```

完全性：

```lean
-- 複雑なパターンマッチングによる grind のタイムアウトを回避するため
set_option maxHeartbeats 1000000 in
@[grind =>]
lemma proveAux_complete (h : prove1 Γ A) : prove2 Γ A := by
  unfold prove2
  induction Γ, A using prove1.induct
  case case1 Γ s h_rdiv_left h_rdiv_right =>
    unfold prove1 at h
    unfold proveAux
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at h ⊢
    rcases h with h_ax | h_left
    · grind
    · right
      rcases h_left with ⟨⟨c, hc_mem⟩, -, hc_val⟩
      refine ⟨c, hc_mem, ?_⟩
      cases c with
      | rdiv L B A' Δ Λ =>
        simp only [Bool.and_eq_true] at hc_val ⊢
        constructor
        · have h_le :
            list_degree Δ + tp_degree (# A') + 1 ≤
              list_degree Γ + tp_degree (# s) := by
            grind
          exact proveAux_mono_le h_le (by grind)
        · have h_le :
            list_degree (L ++ [# B] ++ Λ) + tp_degree (# s) + 1 ≤
              list_degree Γ + tp_degree (# s) := by
            grind
          exact proveAux_mono_le h_le (by grind)
  case case2 Γ B A' h_rec =>
    unfold prove1 at h
    unfold proveAux
    simp only [Bool.and_eq_true] at h ⊢
    rcases h with ⟨h_ne, h_inner⟩
    constructor
    · grind
    · have h_eq :
        list_degree (Γ ++ [# A']) + tp_degree (# B) + 1 =
          list_degree Γ + tp_degree (B ⧸ A') := by
        grind
      grind

lemma prove1_iff_prove2 : prove1 Γ A ↔ prove2 Γ A := by grind
```

## 論理体系との一致

健全性：

```lean
-- 複雑なパターンマッチングによる grind のタイムアウトを回避するため
set_option maxHeartbeats 1000000 in
@[grind =>]
lemma prove1_sound (h : prove1 Γ A) : Γ ⇒ A := by
  induction Γ, A using prove1.induct with
  | case1 Γ s h_rdiv_left h_rdiv_right =>
      unfold prove1 at h
      simp only [Bool.or_eq_true, List.any_eq_true] at h
      rcases h with h_ax | h_cand
      · have h_eq := of_decide_eq_true h_ax
        subst h_eq
        exact Sequent.ax
      · rcases h_cand with ⟨⟨c, hc_mem⟩, -, hc_val⟩
        cases c with
        | rdiv L B A' Δ Λ =>
            simp only [Bool.and_eq_true] at hc_val
            have h1 := h_rdiv_left L B A' Δ Λ hc_mem hc_val.1
            have h2 := h_rdiv_right L B A' Δ Λ hc_mem hc_val.2
            have h_eq := candidates_list_degree hc_mem
            rw [← h_eq]
            exact Sequent.rdiv_l h1 h2
  | case2 Γ B A' h_rec => grind

-- 複雑なパターンマッチングによる grind のタイムアウトを回避するため
set_option maxHeartbeats 1000000 in
@[grind =>]
lemma prove1_complete (h : Γ ⇒ A) : prove1 Γ A := by
  revert h
  classical
  have hp :
      ∀ n Γ A, list_degree Γ + tp_degree A = n → Γ ⇒ A → prove1 Γ A := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih Γ A h_deg h
    unfold prove1
    cases A with
    | atom s =>
        cases h with
        | ax => grind
        | rdiv_l d_arg d_main =>
            rename_i Δ A' Γ₁ B Λ
            simp only [Bool.or_eq_true, List.any_eq_true]
            right
            refine ⟨⟨Cand.rdiv Γ₁ B A' Δ Λ, by grind⟩, by simp, ?_⟩
            grind
    | rdiv B A' => grind
  grind

@[grind .]
lemma prove1_iff_sequent : prove1 Γ A ↔ Γ ⇒ A := by grind

@[grind .]
theorem prove2_iff_sequent : prove2 Γ A ↔ Γ ⇒ A := by grind

instance : Decidable (Γ ⇒ A) :=
  decidable_of_iff (prove2 Γ A) (by grind)

example : [Tp.rdiv "q" "p", Tp.atom "p"] ⇒ Tp.atom "q" :=
  by decide

end Mathling.Lambek.ProductFree.Right.Shallow
```

<!-- vim: set filetype=markdown : -->
