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
  | ldiv (Γ : List Tp) (A B : Tp) (Δ : List Tp) (R : List Tp)

@[grind]
def candidates (Γ : List Tp) : List Cand :=
  (picks Γ).flatMap (fun (L, f, R) =>
    match f with
    | B ⧸ A => (splits R).map (fun (Δ, Λ) => .rdiv L B A Δ Λ)
    | A ⧹ B => (splits L).map (fun (Γ, Δ) => .ldiv Γ A B Δ R)
    | # _ => [])

@[grind =>]
lemma candidates_list_degree (h : c ∈ candidates Γ) :
  match c with
    | .rdiv L B A Δ Λ => L ++ [B ⧸ A] ++ Δ ++ Λ = Γ
    | .ldiv Λ A B Δ R => Λ ++ [A ⧹ B] ++ Δ ++ R = Γ := by
  simp only [candidates, List.mem_flatMap, Prod.exists] at h
  rcases h with ⟨_, f, _, h_pick, h_cand⟩
  have h_geom := picks_list_degree h_pick
  match f with
  | B ⧸ A =>
      simp only [List.mem_map, Prod.exists] at h_cand
      rcases h_cand with ⟨_, _, h_split, _⟩
      have h_geom_split := splits_list_degree h_split
      sorry
  | A ⧹ B =>
      simp only [List.mem_map, Prod.exists] at h_cand
      rcases h_cand with ⟨_, _, h_split, _⟩
      have h_geom_split := splits_list_degree h_split
      sorry
  | # _ => grind

def prove (Γ : List Tp) (A : Tp) : Bool :=
  match A with
  | Tp.atom s =>
    (Γ = [Tp.atom s]) ||
    (candidates Γ).any (fun
      | .rdiv L B A' Δ Λ =>
          have h0: L ++ [B ⧸ A'] ++ Δ ++ Λ = Γ := sorry
          have h1: list_degree Δ + tp_degree A' < list_degree Γ + tp_degree (# s) := by grind
          have h2: list_degree (L ++ [B] ++ Λ) + tp_degree (# s) < list_degree Γ + tp_degree (# s) := by grind
          prove Δ A' && prove (L ++ [B] ++ Λ) (# s)
      | .ldiv Λ A' B Δ R =>
          have h0: Λ ++ [A' ⧹ B] ++ Δ ++ R = Γ := sorry
          have h1: list_degree Δ + tp_degree A' < list_degree Γ + tp_degree (# s) := by grind
          have h2: list_degree (Λ ++ [B] ++ R) + tp_degree (# s) < list_degree Γ + tp_degree (# s) := by grind
          prove Δ A' && prove (Λ ++ [B] ++ R) (# s))
  | Tp.ldiv A' B =>
    have h0: A = A' ⧹ B := sorry
    have h1: list_degree ([A'] ++ Γ) + tp_degree B < list_degree Γ + tp_degree A := by grind
    Γ ≠ [] && prove ([A'] ++ Γ) B
  | Tp.rdiv B A' =>
    have h0: A = B ⧸ A' := sorry
    have h1: list_degree (Γ ++ [A']) + tp_degree B < list_degree Γ + tp_degree A := by grind
    Γ ≠ [] && prove (Γ ++ [A']) B
termination_by
  list_degree Γ + tp_degree A
decreasing_by
  all_goals grind


end Mathling.Lambek.ProductFree
