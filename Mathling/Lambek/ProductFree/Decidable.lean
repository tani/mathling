import Mathlib.Data.Bool.Basic
import Mathling.Lambek.ProductFree.Basic

namespace Mathling.Lambek.ProductFree

@[grind]
def splits {α} : List α → List (List α × List α)
  | [] => [([], [])]
  | x :: xs => ([], x :: xs) :: (splits xs).map (fun (l, r) => (x :: l, r))

@[grind .]
lemma splits_list_degree :
  ∀ X ∈ splits Γ, (list_degree X.1) + (list_degree X.2) = (list_degree Γ) := by
    induction Γ <;> grind

@[grind]
def picks {α} : List α → List (List α × α × List α)
  | [] => []
  | x :: xs => ([], x, xs) :: (picks xs).map (fun (l, a, r) => (x :: l, a, r))

@[grind .]
lemma picks_list_degree :
  ∀ X ∈ picks Γ, (list_degree X.1) + (tp_degree X.2.1) + (list_degree X.2.2) = (list_degree Γ) := by
    induction Γ <;> grind

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
    | _ => [])

@[grind .]
lemma candidates_list_degree :
  ∀ c ∈ candidates Γ,
  match c with
    | .rdiv L B _ Δ Λ =>
        list_degree Δ < list_degree Γ ∧
        (list_degree L + tp_degree B + list_degree Λ) < list_degree Γ
    | .ldiv Γ₀ _ B Δ R =>
        list_degree Δ < list_degree Γ ∧
        (list_degree Γ₀ + tp_degree B + list_degree R) < list_degree Γ := by
  intro c hc
  simp only [candidates, List.mem_flatMap, Prod.exists] at hc
  rcases hc with ⟨L, f, R, hpicks, hf⟩
  have h_f_deg := picks_list_degree (L, f, R) hpicks
  cases f with
  | rdiv B A =>
    simp only [List.mem_map, Prod.exists] at hf
    rcases hf with ⟨Δ, Λ, hsplit, rfl⟩
    have h_split_deg := splits_list_degree (Δ, Λ) hsplit
    grind
  | ldiv A B =>
    simp only [List.mem_map, Prod.exists] at hf
    rcases hf with ⟨Γ₀, Δ, hsplit, rfl⟩
    have h_split_deg := splits_list_degree (Γ₀, Δ) hsplit
    grind
  | _ => contradiction

def prove (Γ : List Tp) (A : Tp) : Bool :=
  match A with
  | Tp.atom s =>
    (Γ = [Tp.atom s]) ||
    (candidates Γ).any (fun
      | .rdiv L B A Δ Λ =>
          prove Δ A && prove (L ++ [B] ++ Λ) (Tp.atom s)
      | .ldiv Γ A B Δ R =>
          prove Δ A && prove (Γ ++ [B] ++ R) (Tp.atom s))
  | Tp.ldiv A B =>
    Γ ≠ [] && prove ([A] ++ Γ) B
  | Tp.rdiv B A =>
    Γ ≠ [] && prove (Γ ++ [A]) B
termination_by
  list_degree Γ + tp_degree A
decreasing_by
  all_goals
    sorry
-- example : [Tp.atom "A" ⧸ Tp.atom "B", Tp.atom "B"] ⇒ (Tp.atom "A") := by grind

end Mathling.Lambek.ProductFree
