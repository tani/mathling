import Mathlib.Data.Bool.Basic
import Mathling.Lambek.ProductFree.Basic
import Lean.LibrarySuggestions.Default

namespace Mathling.Lambek.ProductFree

@[grind]
def splits {α} : List α → List (List α × List α)
  | [] => [([], [])]
  | x :: xs => ([], x :: xs) :: (splits xs).map (fun (l, r) => (x :: l, r))

@[grind .]
lemma splits_list_degree (h : X ∈ splits Γ) :
  X.1 ++ X.2 = Γ := by
  induction Γ generalizing X <;> grind

@[grind]
def picks {α} : List α → List (List α × α × List α)
  | [] => []
  | x :: xs => ([], x, xs) :: (picks xs).map (fun (l, a, r) => (x :: l, a, r))

@[grind =>]
lemma picks_list_degree (h : X ∈ picks Γ) :
   X.1 ++ [X.2.1] ++ X.2.2 = Γ := by
  induction Γ generalizing X <;> grind

@[grind]
inductive Cand where
  | rdiv (L : List Tp) (B A : Tp) (Δ Λ : List Tp)
  | ldiv (Γ Δ : List Tp) (A B : Tp) (Λ : List Tp)

@[grind]
def candidates (Γ : List Tp) : List Cand :=
  (picks Γ).flatMap (fun (L, f, R) =>
    match f with
    | B ⧸ A =>
        (splits R).map (fun (Δ, Λ) => .rdiv L B A Δ Λ)
    | A ⧹ B =>
        (splits L).map (fun (Γ, Δ) => .ldiv Γ Δ A B R)
    | # _ => [])

@[grind =>]
lemma candidates_list_degree (h : c ∈ candidates Γ) :
  match c with
    | .rdiv L B A Δ Λ => L ++ [B ⧸ A] ++ Δ ++ Λ = Γ
    | .ldiv Γ₁ Δ A B R => Γ₁ ++ Δ ++ [A ⧹ B] ++ R = Γ := by
  simp only [candidates, List.mem_flatMap, Prod.exists] at h
  rcases h with ⟨L, f, R, h_pick, h_cand⟩
  have h_geom : L ++ [f] ++ R = Γ := by
    simpa using (picks_list_degree h_pick)
  cases f with
  | atom s =>
      grind
  | rdiv B A =>
      simp only [List.mem_map, Prod.exists] at h_cand
      rcases h_cand with ⟨X, Y, hX, rfl⟩
      have h_split : X ++ Y = R := splits_list_degree hX
      grind
  | ldiv A B =>
      simp only [List.mem_map, Prod.exists] at h_cand
      rcases h_cand with ⟨X, Y, hX, rfl⟩
      have h_split : X ++ Y = L := splits_list_degree hX
      grind

@[grind .]
def prove1 (Γ : List Tp) (A : Tp) : Bool :=
  match A with
  | Tp.atom s =>
    (Γ = [Tp.atom s]) ||
    (candidates Γ).attach.any (fun ⟨c, _hc⟩ =>
      match c with
      | .rdiv L B A' Δ Λ =>
        prove1 Δ A' && prove1 (L ++ [B] ++ Λ) (# s)
      | .ldiv Λ Δ A' B R =>
        prove1 Δ A' && prove1 (Λ ++ [B] ++ R) (# s))
  | Tp.ldiv A' B =>
    Γ ≠ [] && prove1 ([A'] ++ Γ) B
  | Tp.rdiv B A' =>
    Γ ≠ [] && prove1 (Γ ++ [A']) B
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
              proveAux n Δ A' &&
              proveAux n (L ++ [B] ++ Λ) (# s)
          | .ldiv Γ₁ Δ A' B R =>
              proveAux n Δ A' &&
              proveAux n (Γ₁ ++ [B] ++ R) (# s))
    | Tp.ldiv A' B =>
        (Γ ≠ []) && proveAux n ([A'] ++ Γ) B
    | Tp.rdiv B A' =>
        (Γ ≠ []) && proveAux n (Γ ++ [A']) B

@[grind .]
def prove2 (Γ : List Tp) (A : Tp) : Bool :=
  proveAux (list_degree Γ + tp_degree A + 1) Γ A

@[grind =>]
lemma proveAux_mono (h : proveAux n Γ A) :
  proveAux (n + 1) Γ A := by
  induction n generalizing Γ A <;> grind

@[grind =>]
lemma proveAux_mono_le {n m : Nat} (h : n ≤ m) (hp : proveAux n Γ A) :
    proveAux m Γ A := by
  induction h <;> grind

lemma proveAux_sound : proveAux n Γ A → prove1 Γ A := by
  induction n generalizing Γ A with
  | zero => grind
  | succ n ih =>
      cases A with
      | atom s =>
        intro h
        simp only [proveAux, Bool.or_eq_true, List.any_eq_true] at h
        unfold prove1
        simp only [Bool.or_eq_true]
        rcases h with h_base | h_cand
        · grind
        · right
          rcases h_cand with ⟨c, hc_mem, hc_val⟩
          simp only [List.any_eq_true]
          refine ⟨⟨c, hc_mem⟩, by simp, ?_⟩
          split at hc_val <;> split
          all_goals grind
      | ldiv A' B => grind
      | rdiv B A' => grind

lemma proveAux_complete : prove1 Γ A → prove2 Γ A := by
  unfold prove2
  intro h
  induction Γ, A using prove1.induct
  case case1 s Γ h_rec_rdiv h_rec_ldiv =>
    unfold prove1 at h
    unfold proveAux
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at h ⊢
    rcases h with h_ax | h_left
    · left; exact h_ax
    · right
      rcases h_left with ⟨⟨c, hc_mem⟩, -, hc_val⟩
      refine ⟨c, hc_mem, ?_⟩
      cases c with
      | rdiv L B A' Δ Λ =>
        simp only [Bool.and_eq_true] at hc_val ⊢
        constructor
        · sorry --fillout here
        · sorry --fillout here
      | ldiv Γ₁ Δ A' B R =>
        simp only [Bool.and_eq_true] at hc_val ⊢
        constructor
        · sorry --fillout here
        · sorry --fillout here
  case case2 A' B Γ h_ne => sorry --fillout here
  case case3 B A' Γ h_ne => sorry --fillout here

lemma prove1_iff_prove2 : prove1 Γ A ↔ prove2 Γ A := sorry

lemma prove1_iff_sequent : prove1 Γ A ↔ Γ ⇒ A := sorry

theorem prove2_iff_sequent : prove2 Γ A ↔ Γ ⇒ A := sorry

end Mathling.Lambek.ProductFree
