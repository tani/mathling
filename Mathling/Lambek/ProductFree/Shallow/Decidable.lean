import Mathlib.Data.Bool.Basic
import Mathlib.Data.List.Basic
import Mathling.Lambek.ProductFree.Shallow.Basic
import Lean.LibrarySuggestions.Default
import LiterateLean

# Lambek 計算の決定可能性の証明 (Shallow)

このファイルでは、Shallowな左除法と右除法の両方を含むLambek計算において、
与えられたシーケントに対して証明が存在するかどうかを判定する手続きが決定可能であることを証明する。

```lean
set_option linter.style.emptyLine false
set_option linter.style.whitespace false

namespace Mathling.Lambek.ProductFree.Shallow

-- 明示的に名前空間をオープンする
open Mathling.Lambek.ProductFree.Shallow.Tp
open Mathling.Lambek.ProductFree.Shallow.Sequent
```

## 非決定的なリスト操作

### 分割

```lean
@[grind]
def splits {α} : List α → List (List α × List α)
  | [] => [([], [])]
  | x :: xs => ([], x :: xs) :: (splits xs).map (fun (l, r) => (x :: l, r))

@[grind .]
lemma splits_list_degree {α} {Γ : List α} {X : List α × List α} (h : X ∈ splits Γ) :
    X.1 ++ X.2 = Γ := by
  induction Γ generalizing X <;> grind

@[grind .]
lemma splits_mem {α} (Γ Δ : List α) : (Γ, Δ) ∈ splits (Γ ++ Δ) := by
  induction Γ with
  | nil => cases Δ <;> simp [splits]
  | cons x xs ih =>
      apply List.mem_cons_of_mem
      refine List.mem_map.mpr ⟨(xs, Δ), ih, by simp⟩
```

### 選択

```lean
@[grind]
def picks {α} : List α → List (List α × α × List α)
  | [] => []
  | x :: xs => ([], x, xs) :: (picks xs).map (fun (l, a, r) => (x :: l, a, r))

@[grind =>]
lemma picks_list_degree {α} {Γ : List α} {X : List α × α × List α} (h : X ∈ picks Γ) :
    X.1 ++ [X.2.1] ++ X.2.2 = Γ := by
  induction Γ generalizing X <;> grind

@[grind .]
lemma picks_mem {α} (Γ Δ : List α) (a : α) : (Γ, a, Δ) ∈ picks (Γ ++ [a] ++ Δ) := by
  induction Γ with
  | nil => simp [picks]
  | cons x xs ih =>
      apply List.mem_cons_of_mem
      refine List.mem_map.mpr ⟨(xs, a, Δ), ?_, by simp⟩
      simpa [List.append_assoc] using ih
```

## 証明探索の候補

```lean
@[grind]
inductive Cand where
  | ldiv (Γ Δ : List Mathling.Lambek.ProductFree.Shallow.Tp) (A B : String) (Λ : List Mathling.Lambek.ProductFree.Shallow.Tp)
  | rdiv (L : List Mathling.Lambek.ProductFree.Shallow.Tp) (B A : String) (Δ Λ : List Mathling.Lambek.ProductFree.Shallow.Tp)

@[grind]
def candidates (Γ : List Mathling.Lambek.ProductFree.Shallow.Tp) : List Cand :=
  (picks Γ).flatMap (fun (L, f, R) =>
    match f with
    | Mathling.Lambek.ProductFree.Shallow.Tp.atom _ => []
    | Mathling.Lambek.ProductFree.Shallow.Tp.ldiv A B => (splits L).map (fun (Γ₁, Δ) => .ldiv Γ₁ Δ A B R)
    | Mathling.Lambek.ProductFree.Shallow.Tp.rdiv B A => (splits R).map (fun (Δ, Λ) => .rdiv L B A Δ Λ))

@[grind =>]
lemma candidates_list_degree {Γ : List Mathling.Lambek.ProductFree.Shallow.Tp} {c : Cand} (h : c ∈ candidates Γ) :
  match c with
    | .ldiv Γ₁ Δ A B R => Γ₁ ++ Δ ++ [Mathling.Lambek.ProductFree.Shallow.Tp.ldiv A B] ++ R = Γ
    | .rdiv L B A Δ Λ => L ++ [Mathling.Lambek.ProductFree.Shallow.Tp.rdiv B A] ++ Δ ++ Λ = Γ := by
  simp only [candidates, List.mem_flatMap, Prod.exists] at h
  rcases h with ⟨L, f, R, h_pick, h_cand⟩
  cases f with
  | atom s => grind
  | ldiv A B =>
      simp only [List.mem_map, Prod.exists] at h_cand
      rcases h_cand with ⟨X, Y, hX, rfl⟩
      have h_split : X ++ Y = L := splits_list_degree hX
      grind
  | rdiv B A =>
      simp only [List.mem_map, Prod.exists] at h_cand
      rcases h_cand with ⟨X, Y, hX, rfl⟩
      have h_split : X ++ Y = R := splits_list_degree hX
      grind

@[grind .]
lemma candidates_ldiv_mem (Γ₁ Δ R : List Mathling.Lambek.ProductFree.Shallow.Tp) (A B : String) :
  Cand.ldiv Γ₁ Δ A B R ∈ candidates (Γ₁ ++ Δ ++ [Mathling.Lambek.ProductFree.Shallow.Tp.ldiv A B] ++ R) := by
  unfold candidates
  refine List.mem_flatMap.mpr ⟨(Γ₁ ++ Δ, Mathling.Lambek.ProductFree.Shallow.Tp.ldiv A B, R), by grind [picks_mem], ?_⟩
  refine List.mem_map.mpr ⟨(Γ₁, Δ), by grind [splits_mem], by grind⟩

@[grind .]
lemma candidates_rdiv_mem (L Δ Λ : List Mathling.Lambek.ProductFree.Shallow.Tp) (B A : String) :
  Cand.rdiv L B A Δ Λ ∈ candidates (L ++ [Mathling.Lambek.ProductFree.Shallow.Tp.rdiv B A] ++ Δ ++ Λ) := by
  unfold candidates
  refine List.mem_flatMap.mpr ⟨(L, Mathling.Lambek.ProductFree.Shallow.Tp.rdiv B A, Δ ++ Λ), by grind [picks_mem], ?_⟩
  refine List.mem_map.mpr ⟨(Δ, Λ), by grind [splits_mem], by grind⟩
```

## 決定可能手続きの定義

```lean
@[grind .]
def prove1 (Γ : List Mathling.Lambek.ProductFree.Shallow.Tp) (A : Mathling.Lambek.ProductFree.Shallow.Tp) : Bool :=
  match A with
  | Mathling.Lambek.ProductFree.Shallow.Tp.atom s =>
    (Γ = [Mathling.Lambek.ProductFree.Shallow.Tp.atom s]) ||
    (candidates Γ).attach.any (fun ⟨c, _hc⟩ =>
      match c with
      | .ldiv Γ₁ Δ A' B R => prove1 Δ (Mathling.Lambek.ProductFree.Shallow.Tp.atom A') && prove1 (Γ₁ ++ [Mathling.Lambek.ProductFree.Shallow.Tp.atom B] ++ R) (Mathling.Lambek.ProductFree.Shallow.Tp.atom s)
      | .rdiv L B A' Δ Λ => prove1 Δ (Mathling.Lambek.ProductFree.Shallow.Tp.atom A') && prove1 (L ++ [Mathling.Lambek.ProductFree.Shallow.Tp.atom B] ++ Λ) (Mathling.Lambek.ProductFree.Shallow.Tp.atom s))
  | Mathling.Lambek.ProductFree.Shallow.Tp.ldiv A' B => Γ ≠ [] && prove1 ([Mathling.Lambek.ProductFree.Shallow.Tp.atom A'] ++ Γ) (Mathling.Lambek.ProductFree.Shallow.Tp.atom B)
  | Mathling.Lambek.ProductFree.Shallow.Tp.rdiv B A' => Γ ≠ [] && prove1 (Γ ++ [Mathling.Lambek.ProductFree.Shallow.Tp.atom A']) (Mathling.Lambek.ProductFree.Shallow.Tp.atom B)
termination_by Mathling.Lambek.ProductFree.Shallow.list_degree Γ + Mathling.Lambek.ProductFree.Shallow.tp_degree A
decreasing_by all_goals grind

@[grind .]
def proveAux : Nat → List Mathling.Lambek.ProductFree.Shallow.Tp → Mathling.Lambek.ProductFree.Shallow.Tp → Bool
  | 0, _,  _ => false
  | n + 1, Γ,  A =>
    match A with
    | Mathling.Lambek.ProductFree.Shallow.Tp.atom s =>
        (Γ = [Mathling.Lambek.ProductFree.Shallow.Tp.atom s]) ||
        (candidates Γ).any (fun c =>
          match c with
          | .ldiv Γ₁ Δ A' B R => proveAux n Δ (Mathling.Lambek.ProductFree.Shallow.Tp.atom A') && proveAux n (Γ₁ ++ [Mathling.Lambek.ProductFree.Shallow.Tp.atom B] ++ R) (Mathling.Lambek.ProductFree.Shallow.Tp.atom s)
          | .rdiv L B A' Δ Λ => proveAux n Δ (Mathling.Lambek.ProductFree.Shallow.Tp.atom A') && proveAux n (L ++ [Mathling.Lambek.ProductFree.Shallow.Tp.atom B] ++ Λ) (Mathling.Lambek.ProductFree.Shallow.Tp.atom s))
    | Mathling.Lambek.ProductFree.Shallow.Tp.ldiv A' B => (Γ ≠ []) && proveAux n ([Mathling.Lambek.ProductFree.Shallow.Tp.atom A'] ++ Γ) (Mathling.Lambek.ProductFree.Shallow.Tp.atom B)
    | Mathling.Lambek.ProductFree.Shallow.Tp.rdiv B A' => (Γ ≠ []) && proveAux n (Γ ++ [Mathling.Lambek.ProductFree.Shallow.Tp.atom A']) (Mathling.Lambek.ProductFree.Shallow.Tp.atom B)

@[grind .]
def prove2 (Γ : List Mathling.Lambek.ProductFree.Shallow.Tp) (A : Mathling.Lambek.ProductFree.Shallow.Tp) : Bool :=
  proveAux (Mathling.Lambek.ProductFree.Shallow.list_degree Γ + Mathling.Lambek.ProductFree.Shallow.tp_degree A + 1) Γ A
```

## 性質の証明

```lean
@[grind =>]
lemma proveAux_mono {n : Nat} {Γ : List Mathling.Lambek.ProductFree.Shallow.Tp} {A : Mathling.Lambek.ProductFree.Shallow.Tp} (h : proveAux n Γ A) : proveAux (n + 1) Γ A := by
  induction n generalizing Γ A <;> grind

@[grind =>]
lemma proveAux_mono_le {n m : Nat} {Γ : List Mathling.Lambek.ProductFree.Shallow.Tp} {A : Mathling.Lambek.ProductFree.Shallow.Tp} (h : n ≤ m) (hp : proveAux n Γ A) :
    proveAux m Γ A := by
  induction h <;> grind
```

## 一致の証明

健全性：

```lean
@[grind .]
lemma proveAux_sound {n : Nat} {Γ : List Mathling.Lambek.ProductFree.Shallow.Tp} {A : Mathling.Lambek.ProductFree.Shallow.Tp} (h : proveAux n Γ A) : prove1 Γ A := by
  induction n generalizing Γ A with
  | zero => grind
  | succ n ih =>
      cases A with
      | atom s =>
        simp only [proveAux, Bool.or_eq_true, List.any_eq_true] at h
        unfold prove1; simp only [Bool.or_eq_true]
        rcases h with h_base | h_cand
        · left; grind
        · right; rcases h_cand with ⟨c, hc_mem, hc_val⟩
          simp only [List.any_eq_true]; refine ⟨⟨c, hc_mem⟩, by simp, ?_⟩
          grind
      | ldiv A' B => grind
      | rdiv B A' => grind
```

完全性：

```lean
set_option maxHeartbeats 1000000 in
@[grind =>]
lemma proveAux_complete {Γ : List Mathling.Lambek.ProductFree.Shallow.Tp} {A : Mathling.Lambek.ProductFree.Shallow.Tp} (h : prove1 Γ A) : prove2 Γ A := by
  unfold prove2
  induction Γ, A using prove1.induct
  case case1 Γ s h_cand_ih =>
    unfold prove1 at h; unfold proveAux; simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at h ⊢
    rcases h with h_ax | h_left
    · left; grind
    · right; rcases h_left with ⟨⟨c, hc_mem⟩, -, hc_val⟩
      refine ⟨c, hc_mem, ?_⟩
      cases c with
      | ldiv Γ₁ Δ A' B R =>
          simp only [Bool.and_eq_true] at hc_val ⊢
          constructor
          · have h_le : Mathling.Lambek.ProductFree.Shallow.list_degree Δ + Mathling.Lambek.ProductFree.Shallow.tp_degree (Mathling.Lambek.ProductFree.Shallow.Tp.atom A') + 1 ≤ Mathling.Lambek.ProductFree.Shallow.list_degree Γ + Mathling.Lambek.ProductFree.Shallow.tp_degree (Mathling.Lambek.ProductFree.Shallow.Tp.atom s) := by grind
            exact proveAux_mono_le (m := Mathling.Lambek.ProductFree.Shallow.list_degree Γ + Mathling.Lambek.ProductFree.Shallow.tp_degree (Mathling.Lambek.ProductFree.Shallow.Tp.atom s)) (by grind) (by grind)
          · have h_le : Mathling.Lambek.ProductFree.Shallow.list_degree (Γ₁ ++ [Mathling.Lambek.ProductFree.Shallow.Tp.atom B] ++ R) + Mathling.Lambek.ProductFree.Shallow.tp_degree (Mathling.Lambek.ProductFree.Shallow.Tp.atom s) + 1 ≤ Mathling.Lambek.ProductFree.Shallow.list_degree Γ + Mathling.Lambek.ProductFree.Shallow.tp_degree (Mathling.Lambek.ProductFree.Shallow.Tp.atom s) := by grind
            exact proveAux_mono_le (m := Mathling.Lambek.ProductFree.Shallow.list_degree Γ + Mathling.Lambek.ProductFree.Shallow.tp_degree (Mathling.Lambek.ProductFree.Shallow.Tp.atom s)) (by grind) (by grind)
      | rdiv L B A' Δ Λ =>
          simp only [Bool.and_eq_true] at hc_val ⊢
          constructor
          · have h_le : Mathling.Lambek.ProductFree.Shallow.list_degree Δ + Mathling.Lambek.ProductFree.Shallow.tp_degree (Mathling.Lambek.ProductFree.Shallow.Tp.atom A') + 1 ≤ Mathling.Lambek.ProductFree.Shallow.list_degree Γ + Mathling.Lambek.ProductFree.Shallow.tp_degree (Mathling.Lambek.ProductFree.Shallow.Tp.atom s) := by grind
            exact proveAux_mono_le (m := Mathling.Lambek.ProductFree.Shallow.list_degree Γ + Mathling.Lambek.ProductFree.Shallow.tp_degree (Mathling.Lambek.ProductFree.Shallow.Tp.atom s)) (by grind) (by grind)
          · have h_le : Mathling.Lambek.ProductFree.Shallow.list_degree (L ++ [Mathling.Lambek.ProductFree.Shallow.Tp.atom B] ++ Λ) + Mathling.Lambek.ProductFree.Shallow.tp_degree (Mathling.Lambek.ProductFree.Shallow.Tp.atom s) + 1 ≤ Mathling.Lambek.ProductFree.Shallow.list_degree Γ + Mathling.Lambek.ProductFree.Shallow.tp_degree (Mathling.Lambek.ProductFree.Shallow.Tp.atom s) := by grind
            exact proveAux_mono_le (m := Mathling.Lambek.ProductFree.Shallow.list_degree Γ + Mathling.Lambek.ProductFree.Shallow.tp_degree (Mathling.Lambek.ProductFree.Shallow.Tp.atom s)) (by grind) (by grind)
  case case2 Γ A' B h_rec =>
    unfold prove1 at h; unfold proveAux; simp only [Bool.and_eq_true] at h ⊢
    rcases h with ⟨h_ne, h_inner⟩
    constructor; · grind
    · have h_eq : Mathling.Lambek.ProductFree.Shallow.list_degree ([Mathling.Lambek.ProductFree.Shallow.Tp.atom A'] ++ Γ) + Mathling.Lambek.ProductFree.Shallow.tp_degree (Mathling.Lambek.ProductFree.Shallow.Tp.atom B) + 1 = Mathling.Lambek.ProductFree.Shallow.list_degree Γ + Mathling.Lambek.ProductFree.Shallow.tp_degree (Mathling.Lambek.ProductFree.Shallow.Tp.ldiv A' B) := by grind
      grind
  case case3 Γ B A' h_rec =>
    unfold prove1 at h; unfold proveAux; simp only [Bool.and_eq_true] at h ⊢
    rcases h with ⟨h_ne, h_inner⟩
    constructor; · grind
    · have h_eq : Mathling.Lambek.ProductFree.Shallow.list_degree (Γ ++ [Mathling.Lambek.ProductFree.Shallow.Tp.atom A']) + Mathling.Lambek.ProductFree.Shallow.tp_degree (Mathling.Lambek.ProductFree.Shallow.Tp.atom B) + 1 = Mathling.Lambek.ProductFree.Shallow.list_degree Γ + Mathling.Lambek.ProductFree.Shallow.tp_degree (Mathling.Lambek.ProductFree.Shallow.Tp.rdiv B A') := by grind
      grind

lemma prove1_iff_prove2 {Γ : List Mathling.Lambek.ProductFree.Shallow.Tp} {A : Mathling.Lambek.ProductFree.Shallow.Tp} : prove1 Γ A ↔ prove2 Γ A := by grind
```

## 論理体系との一致

健全性：

```lean
set_option maxHeartbeats 1000000 in
@[grind .]
lemma prove1_sound {Γ : List Mathling.Lambek.ProductFree.Shallow.Tp} {A : Mathling.Lambek.ProductFree.Shallow.Tp} (h : prove1 Γ A) : Mathling.Lambek.ProductFree.Shallow.Sequent Γ A := by
  induction Γ, A using prove1.induct with
  | case1 Γ s h_cand_ih =>
      unfold prove1 at h; simp only [Bool.or_eq_true, List.any_eq_true] at h
      rcases h with h_ax | h_cand
      · subst (of_decide_eq_true h_ax); exact Mathling.Lambek.ProductFree.Shallow.Sequent.ax
      · rcases h_cand with ⟨⟨c, hc_mem⟩, -, hc_val⟩
        cases c with
        | ldiv Γ₁ Δ A' B R =>
            simp only [Bool.and_eq_true] at hc_val
            have h1 := h_cand_ih.1 Γ₁ Δ A' B R hc_mem hc_val.1
            have h2 := h_cand_ih.2 Γ₁ Δ A' B R hc_mem hc_val.2
            rw [← candidates_list_degree hc_mem]
            exact Mathling.Lambek.ProductFree.Shallow.Sequent.ldiv_l h1 h2
        | rdiv L B A' Δ Λ =>
            simp only [Bool.and_eq_true] at hc_val
            have h1 := h_cand_ih.1 L B A' Δ Λ hc_mem hc_val.1
            have h2 := h_cand_ih.2 L B A' Δ Λ hc_mem hc_val.2
            rw [← candidates_list_degree hc_mem]
            exact Mathling.Lambek.ProductFree.Shallow.Sequent.rdiv_l h1 h2
  | case2 Γ A' B h_rec => grind [Mathling.Lambek.ProductFree.Shallow.Sequent.ldiv_r]
  | case3 Γ B A' h_rec => grind [Mathling.Lambek.ProductFree.Shallow.Sequent.rdiv_r]
```

完全性：

```lean
set_option maxHeartbeats 1000000 in
@[grind .]
lemma prove1_complete {Γ : List Mathling.Lambek.ProductFree.Shallow.Tp} {A : Mathling.Lambek.ProductFree.Shallow.Tp} (h : Mathling.Lambek.ProductFree.Shallow.Sequent Γ A) : prove1 Γ A := by
  revert h; classical
  have hp : ∀ n Γ A, Mathling.Lambek.ProductFree.Shallow.list_degree Γ + Mathling.Lambek.ProductFree.Shallow.tp_degree A = n → Mathling.Lambek.ProductFree.Shallow.Sequent Γ A → prove1 Γ A := by
    intro n ih Γ A h_deg h
    unfold prove1; cases A with
    | atom s =>
        cases h with
        | ax => grind
        | ldiv_l d_arg d_main =>
            rename_i Δ A' Γ₁ B Λ; simp only [Bool.or_eq_true, List.any_eq_true]; right
            refine ⟨⟨Cand.ldiv Γ₁ Δ A' B Λ, by grind [candidates_ldiv_mem]⟩, by simp, ?_⟩; grind
        | rdiv_l d_arg d_main =>
            rename_i Δ A' Γ₁ B Λ; simp only [Bool.or_eq_true, List.any_eq_true]; right
            refine ⟨⟨Cand.rdiv Γ₁ B A' Δ Λ, by grind [candidates_rdiv_mem]⟩, by simp, ?_⟩; grind
        | ldiv_r => grind
        | rdiv_r => grind
    | ldiv A' B => grind
    | rdiv B A' => grind
  grind

@[grind .]
lemma prove1_iff_sequent {Γ : List Mathling.Lambek.ProductFree.Shallow.Tp} {A : Mathling.Lambek.ProductFree.Shallow.Tp} : prove1 Γ A ↔ Mathling.Lambek.ProductFree.Shallow.Sequent Γ A := by
  constructor <;> [apply prove1_sound; apply prove1_complete]

@[grind .]
theorem prove2_iff_sequent {Γ : List Mathling.Lambek.ProductFree.Shallow.Tp} {A : Mathling.Lambek.ProductFree.Shallow.Tp} : prove2 Γ A ↔ Mathling.Lambek.ProductFree.Shallow.Sequent Γ A := by
  rw [← prove1_iff_prove2, prove1_iff_sequent]

instance {Γ : List Mathling.Lambek.ProductFree.Shallow.Tp} {A : Mathling.Lambek.ProductFree.Shallow.Tp} : Decidable (Mathling.Lambek.ProductFree.Shallow.Sequent Γ A) :=
  decidable_of_iff (prove2 Γ A) prove2_iff_sequent

example : Mathling.Lambek.ProductFree.Shallow.Sequent [atom "p", Mathling.Lambek.ProductFree.Shallow.Tp.ldiv "p" "q"] (Mathling.Lambek.ProductFree.Shallow.Tp.atom "q") := by decide
example : Mathling.Lambek.ProductFree.Shallow.Sequent [Mathling.Lambek.ProductFree.Shallow.Tp.rdiv "q" "p", Mathling.Lambek.ProductFree.Shallow.Tp.atom "p"] (Mathling.Lambek.ProductFree.Shallow.Tp.atom "q") := by decide

end Mathling.Lambek.ProductFree.Shallow
```

<!-- vim: set filetype=markdown : -->
