import Mathling.LambekCalculus.ProductFree.Basic

namespace Mathling.LambekCalculus.ProductFree

inductive Search (α : Type) : Type where
  | found : α → Search α
  | not_found : (α → False) → Search α

def searchExists {α} (xs : List α) (p : α → Prop)
    (dec : ∀ x, Decidable (p x)) : Search {x : α // x ∈ xs ∧ p x} := by
  induction xs with
  | nil => exact Search.not_found (by grind)
  | cons x xs ih =>
      cases dec x with
      | isTrue hx =>
          exact Search.found ⟨x, by simp, hx⟩
      | isFalse hx =>
          cases ih with
          | found h =>
              refine Search.found ?_
              rcases h with ⟨y, hy, hp⟩
              exact ⟨y, by grind, hp⟩
          | not_found h =>
              exact Search.not_found (by
                intro h'
                rcases h' with ⟨y, hy, hp⟩
                have : y = x ∨ y ∈ xs := by grind
                cases this with
                | inl hxy => grind
                | inr hys => exact h ⟨y, hys, hp⟩)

@[grind]
def list_splits {α} : List α → List (List α × List α)
  | [] => [([], [])]
  | x :: xs => ([], x :: xs) :: (list_splits xs).map (fun (l, r) => (x :: l, r))

@[grind .]
lemma mem_list_splits_iff {α} {xs : List α} :
    ∀ {l r : List α}, (l, r) ∈ list_splits xs ↔ xs = l ++ r := by
  induction xs with
  | nil =>
      intro l r
      simp [list_splits]
  | cons x xs ih =>
      intro l r
      constructor
      · intro h
        grind
      · intro h
        grind [List.cons_eq_append_iff]

@[grind]
def picks {α} : List α → List (List α × α × List α)
  | [] => []
  | x :: xs => ([], x, xs) :: (picks xs).map (fun (l, a, r) => (x :: l, a, r))

@[grind .]
lemma mem_picks_iff {α} {xs : List α} :
    ∀ {l : List α} {x : α} {r : List α}, (l, x, r) ∈ picks xs ↔ xs = l ++ x :: r := by
  induction xs with
  | nil =>
      intro l x r
      simp [picks]
  | cons y ys ih =>
      intro l x r
      constructor
      · intro h
        grind
      · intro h
        grind [List.cons_eq_append_iff]

structure RDivCand where
  left : List Tp
  B : Tp
  A : Tp
  Δ : List Tp
  Λ : List Tp

structure LDivCand where
  left : List Tp
  A : Tp
  B : Tp
  Δ : List Tp
  Λ : List Tp

@[grind]
def rdiv_candidates (Γ : List Tp) : List RDivCand :=
  (picks Γ).flatMap (fun (left, f, right) =>
    match f with
    | B ⧸ A => (list_splits right).map (fun (Δ, Λ) => ⟨left, B, A, Δ, Λ⟩)
    | _ => [])

@[grind]
def ldiv_candidates (Γ : List Tp) : List LDivCand :=
  (picks Γ).flatMap (fun (left, f, right) =>
    match f with
    | A ⧹ B => (list_splits left).map (fun (Γ0, Δ) => ⟨Γ0, A, B, Δ, right⟩)
    | _ => [])

@[grind .]
lemma rdiv_candidates_spec {Γ : List Tp} {cand : RDivCand} :
    cand ∈ rdiv_candidates Γ ↔
      Γ = cand.left ++ [cand.B ⧸ cand.A] ++ cand.Δ ++ cand.Λ := by
  cases cand with
  | mk left B A Δ Λ =>
      constructor
      · intro h
        rcases List.mem_flatMap.mp h
        grind
      · intro h
        apply List.mem_flatMap.mpr
        refine ⟨(left, B ⧸ A, Δ ++ Λ), ?_, ?_⟩
        · grind
        · apply List.mem_map.mpr
          refine ⟨(Δ, Λ), ?_, rfl⟩
          grind

@[grind .]
lemma ldiv_candidates_spec {Γ : List Tp} {cand : LDivCand} :
    cand ∈ ldiv_candidates Γ ↔
      Γ = cand.left ++ cand.Δ ++ [cand.A ⧹ cand.B] ++ cand.Λ := by
  cases cand with
  | mk left A B Δ Λ =>
      constructor
      · intro h
        rcases List.mem_flatMap.mp h
        grind
      · intro h
        apply List.mem_flatMap.mpr
        refine ⟨(left ++ Δ, A ⧹ B, Λ), ?_, ?_⟩
        · grind
        · apply List.mem_map.mpr
          refine ⟨(left, Δ), ?_, rfl⟩
          grind

def derive (Γ : List Tp) (A : Tp) : Decidable (Γ ⇒ A) := by
  cases A with
  | atom s =>
      by_cases hax : Γ = [Tp.atom s]
      · exact isTrue (by grind)
      · let rdiv_cands := (rdiv_candidates Γ).attach
        let rdiv_pred : {c // c ∈ rdiv_candidates Γ} → Prop := fun cand =>
          (cand.1.Δ ⇒ cand.1.A) ∧ ((cand.1.left ++ [cand.1.B] ++ cand.1.Λ) ⇒ Tp.atom s)
        have dec_rdiv_pred : ∀ cand, Decidable (rdiv_pred cand) := by
          intro cand
          cases derive cand.1.Δ cand.1.A with
          | isTrue d_arg =>
              cases derive (cand.1.left ++ [cand.1.B] ++ cand.1.Λ) (Tp.atom s) with
              | isTrue d_main => exact isTrue (by grind)
              | isFalse h_main => exact isFalse (by grind)
          | isFalse h_arg => exact isFalse (by grind)
        cases (searchExists rdiv_cands rdiv_pred dec_rdiv_pred) with
        | found h => exact isTrue (by grind)
        | not_found h_rdiv =>
            let ldiv_cands := (ldiv_candidates Γ).attach
            let ldiv_pred : {c // c ∈ ldiv_candidates Γ} → Prop := fun cand =>
              (cand.1.Δ ⇒ cand.1.A) ∧ ((cand.1.left ++ [cand.1.B] ++ cand.1.Λ) ⇒ Tp.atom s)
            have dec_ldiv_pred : ∀ cand, Decidable (ldiv_pred cand) := by
              intro cand
              cases derive cand.1.Δ cand.1.A with
              | isTrue d_arg =>
                  cases derive (cand.1.left ++ [cand.1.B] ++ cand.1.Λ) (Tp.atom s) with
                  | isTrue d_main => exact isTrue (by grind)
                  | isFalse h_main => exact isFalse (by grind)
              | isFalse h_arg =>
                  exact isFalse (by grind)
            cases (searchExists ldiv_cands ldiv_pred dec_ldiv_pred) with
            | found h =>
                exact isTrue (by grind)
            | not_found h_ldiv =>
                exact isFalse (by
                  intro hder
                  cases hder
                  case ax => grind
                  case rdiv_l Δ A Γ_left B Λ d_arg d_main =>
                    let cand0 : RDivCand := ⟨Γ_left, B, A, Δ, Λ⟩
                    let cand : {c // c ∈ rdiv_candidates (Γ_left ++ [B ⧸ A] ++ Δ ++ Λ)} :=
                      ⟨cand0, by grind⟩
                    exact h_rdiv ⟨cand, by grind, (by grind)⟩
                  case ldiv_l Δ A Γ_left B Λ d_arg d_main =>
                    let cand0 : LDivCand := ⟨Γ_left, A, B, Δ, Λ⟩
                    let cand : {c // c ∈ ldiv_candidates (Γ_left ++ Δ ++ [A ⧹ B] ++ Λ)} :=
                      ⟨cand0, by grind⟩
                    exact h_ldiv ⟨cand, by grind, (by grind)⟩)
  | ldiv A B =>
      by_cases hΓ : Γ = []
      · exact isFalse (by grind)
      · cases derive ([A] ++ Γ) B with
        | isTrue h => exact isTrue (by grind)
        | isFalse h => exact isFalse (by grind)
  | rdiv B A =>
      by_cases hΓ : Γ = []
      · exact isFalse (by grind)
      · cases derive (Γ ++ [A]) B with
        | isTrue h => exact isTrue (by grind)
        | isFalse h => exact isFalse (by grind)
termination_by
  list_degree Γ + tp_degree A
decreasing_by
  all_goals grind

instance (Γ : List Tp) (A : Tp) : Decidable (Γ ⇒ A) := derive Γ A

end Mathling.LambekCalculus.ProductFree
