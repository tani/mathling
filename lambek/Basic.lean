import Lean.LibrarySuggestions.Default
import Aesop
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic

namespace Lambek

@[grind cases]
inductive Tp where
  | atom (s : String) : Tp
  | ldiv (a b : Tp)   : Tp
  | rdiv (a b : Tp)   : Tp
  deriving Repr, DecidableEq

prefix:50 "#" => Tp.atom
infixr:60 " ⧹ " => Tp.ldiv
infixl:60 " ⧸ " => Tp.rdiv

@[grind intro]
inductive Derive : List Tp → Tp → Prop where
  | ax : Derive [A] A
  | rdiv_r :
      Γ ≠ [] →
      Derive (Γ ++ [A]) B →
      Derive Γ (B ⧸ A)
  | ldiv_r :
      Γ ≠ [] →
      Derive ([A] ++ Γ) B →
      Derive Γ (A ⧹ B)
  | rdiv_l :
      Derive Δ A →
      Derive (Γ ++ [B] ++ Λ) C →
      Derive (Γ ++ [B ⧸ A] ++ Δ ++ Λ) C
  | ldiv_l :
      Derive Δ A →
      Derive (Γ ++ [B] ++ Λ) C →
      Derive (Γ ++ Δ ++ [A ⧹ B] ++ Λ) C

infixl:50 " ⇒ " => Derive

@[grind =]
def tp_degree : Tp → Nat
  | # _     => 1
  | A ⧹ B   => tp_degree A + tp_degree B + 1
  | A ⧸ B   => tp_degree A + tp_degree B + 1

@[grind =]
def list_degree : List Tp → Nat
  | []        => 0
  | A :: Γ    => tp_degree A + list_degree Γ

@[grind =]
theorem list_degree_tp_degree : list_degree [X] = tp_degree X := by grind

@[grind =]
theorem list_degree_traversible : list_degree (X ++ Y) = list_degree X + list_degree Y := by
  induction X
  · grind
  · grind

@[grind =>]
theorem nonempty_premises (h : Γ ⇒ A) : Γ ≠ [] := by
  induction h
  · grind
  · grind
  · grind
  · aesop
  · aesop

theorem list_split_2_cases
  (h : Γ₁ ++ [α] ++ Γ₂ = Δ₁ ++ Δ₂) :
  (∃ R, Δ₁ = Γ₁ ++ [α] ++ R ∧ Γ₂ = R ++ Δ₂) ∨
  (∃ L R, Δ₂ = L ++ [α] ++ R ∧ Γ₁ = Δ₁ ++ L ∧ Γ₂ = R) := by
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h
  rcases List.append_eq_append_iff.mp h with ⟨m, rfl, hm⟩ | ⟨m, rfl, hm⟩
  · cases m with
    | nil => grind
    | cons => grind
  · grind

theorem list_split_3_cases
  (h : Γ₁ ++ [α] ++ Γ₂ = Δ₁ ++ Δ₂ ++ Δ₃) :
  (∃ R, Δ₁ = Γ₁ ++ [α] ++ R ∧ Γ₂ = R ++ Δ₂ ++ Δ₃) ∨
  (∃ L R, Δ₂ = L ++ [α] ++ R ∧ Γ₁ = Δ₁ ++ L ∧ Γ₂ = R ++ Δ₃) ∨
  (∃ L R, Δ₃ = L ++ [α] ++ R ∧ Γ₁ = Δ₁ ++ Δ₂ ++ L ∧ Γ₂ = R) := by
  rcases list_split_2_cases (by simpa using h)
    with ⟨R, h1, h2⟩ | ⟨L, R, h1, h2, h3⟩
  · grind
  · rcases list_split_2_cases h1.symm with ⟨R', h4, h5⟩ | ⟨L', R', h4, h5, h6⟩
    · grind
    · grind

theorem list_split_4_cases
  (h : Γ₁ ++ [α] ++ Γ₂ = Δ₁ ++ Δ₂ ++ Δ₃ ++ Δ₄) :
  (∃ R, Δ₁ = Γ₁ ++ [α] ++ R ∧ Γ₂ = R ++ Δ₂ ++ Δ₃ ++ Δ₄)
  ∨ (∃ L R, Δ₂ = L ++ [α] ++ R ∧ Γ₁ = Δ₁ ++ L ∧ Γ₂ = R ++ Δ₃ ++ Δ₄)
  ∨ (∃ L R, Δ₃ = L ++ [α] ++ R ∧ Γ₁ = Δ₁ ++ Δ₂ ++ L ∧ Γ₂ = R ++ Δ₄)
  ∨ (∃ L R, Δ₄ = L ++ [α] ++ R ∧ Γ₁ = Δ₁ ++ Δ₂ ++ Δ₃ ++ L ∧ Γ₂ = R) := by
  rcases list_split_2_cases (by simpa using h)
    with ⟨R, h1, h2⟩ | ⟨L, R, h1, h2, h3⟩
  · grind
  · rcases list_split_3_cases (by simpa using h1.symm)
      with ⟨R', h4, h5⟩ | ⟨L', R', h4, h5, h6⟩ | ⟨L', R', h4, h5, h6⟩
    · grind
    · grind
    · grind

@[grind =>]
theorem nonempty_append (h : Γ ≠ []) : Δ ++ Γ ++ Λ ≠ [] := by
  induction Δ
  induction Λ
  · grind
  · simp
  grind

set_option maxHeartbeats 4000000 in
  --
theorem cut_admissible {A B : Tp} {Γ Δ Λ : List Tp}
  (d_left : Γ ⇒ A)
  (d_right : Δ ++ [A] ++ Λ ⇒ B) :
  Δ ++ Γ ++ Λ ⇒ B := by
    let deg := list_degree (Δ ++ Γ ++ Λ) + tp_degree A + tp_degree B
    generalize h_n : deg = n
    induction n using Nat.strong_induction_on generalizing Γ Δ Λ A B
    next n ih =>
      subst h_n
      cases d_left with
      | ax => grind
      | ldiv_r a b =>
        rename_i A' B'
        generalize d_right_eq_x : Δ ++ [A' ⧹ B'] ++ Λ = X at d_right
        cases d_right with
        | ax => grind only [List.cons_eq_cons, List.append_assoc, List.append_cons,
          List.append_eq_nil_iff, List.append_eq_singleton_iff, Derive.ldiv_r]
        | ldiv_r x y =>
          rename_i C' D'
          let m := list_degree ([C'] ++ Δ ++ Γ ++ Λ) + tp_degree (A' ⧹ B') + tp_degree D'
          have mn : m < deg := by grind
          have e_r : Γ ⇒ A' ⧹ B' := by grind
          have e_l : [C'] ++ Δ ++ [ A' ⧹ B' ] ++ Λ ⇒ D' := by grind
          have e_c : [C'] ++ Δ ++ Γ ++ Λ ⇒ D' := by grind
          grind
        | rdiv_r x y =>
          rename_i C' D'
          let m := list_degree (Δ ++ Γ ++ Λ ++ [C']) + tp_degree (A' ⧹ B') + tp_degree D'
          have mn : m < deg := by grind
          have e_r : Γ ⇒ (A' ⧹ B') := by grind
          have e_l : Δ ++ [ A' ⧹ B' ] ++ Λ ++ [C'] ⇒ D' := by grind
          have e_c : Δ ++ Γ ++ Λ ++ [C'] ⇒ D' := by grind
          grind
        | ldiv_l x y => sorry -- todo
        | rdiv_l x y => sorry -- todo
      | rdiv_r a b =>
        rename_i A' B'
        have c: Γ ⇒ B' ⧸ A' := by grind
        generalize d_right_eq_x : Δ ++ [B' ⧸ A'] ++ Λ = X at d_right
        cases d_right with
        | ax => grind only [nonempty_append, List.cons_eq_cons, List.append_assoc, List.append_cons,
          List.append_eq_nil_iff, List.append_eq_singleton_iff, Derive.rdiv_r]
        | ldiv_r x y =>
          rename_i C' D'
          let m := list_degree ([C'] ++ Δ ++ Γ ++ Λ) + tp_degree (B' ⧸ A') + tp_degree D'
          have mn : m < deg := by
            grind only [list_degree, tp_degree, list_degree_traversible]
          have e_l : [C'] ++ Δ ++ [ B' ⧸ A' ] ++ Λ ⇒ D' := by grind
          have e_c : [C'] ++ Δ ++ Γ ++ Λ ⇒ D' := by grind
          grind
        | rdiv_r x y =>
          rename_i C' D'
          let m := list_degree (Δ ++ Γ ++ Λ ++ [C']) + tp_degree ( B' ⧸ A' ) + tp_degree D'
          have mn : m < deg := by
            grind only [list_degree, tp_degree, list_degree_traversible]
          have e_l : Δ ++ [ B' ⧸ A' ] ++ Λ ++ [C'] ⇒ D' := by grind
          have e_c : Δ ++ Γ ++ Λ ++ [C'] ⇒ D' := by grind
          grind
        | ldiv_l x y =>
          rename_i S T U V W
          rcases list_split_4_cases d_right_eq_x
            with ⟨R, rfl, rfl⟩
               | ⟨L, R, rfl, rfl, rfl⟩
               | ⟨L, R, h_contra, rfl, rfl⟩
               | ⟨L, R, rfl, rfl, rfl⟩
          · let m := list_degree (Δ ++ Γ ++ (R ++ [V] ++ W)) + tp_degree (B' ⧸ A') + tp_degree B
            have mn : m < deg := by
              grind only [list_degree, tp_degree, list_degree_traversible]
            have e: Δ ++ Γ ++ R ++ [V] ++ W ⇒ B := by grind
            have f: Δ ++ Γ ++ R ++ S ++ [T ⧹ V] ++ W ⇒ B := by grind
            grind
          · let m := list_degree (L ++ Γ ++ R) + tp_degree T + tp_degree B
            have mn : m < deg := by
              grind only [list_degree, tp_degree, list_degree_traversible]
            have d: L ++ Γ ++ R ⇒ T := by grind
            have e: U ++ (L ++ Γ ++ R) ++ [T ⧹ V] ++ W ⇒ B := by grind
            grind
          · have f: ¬ ([T ⧹ V] = L ++ [B' ⧸ A'] ++ R) := by
              intro h
              cases L with
              | nil => grind
              | cons head tail => grind
            grind
          · let m := list_degree (U ++ [V] ++ L ++ Γ ++ Λ) + tp_degree (B' ⧸ A') + tp_degree B
            have mn : m < deg := by
              grind only [list_degree, tp_degree, list_degree_traversible]
            have d: U ++ [V] ++ L ++ Γ ++ Λ ⇒ B := by grind
            have e: U ++ S ++ [T ⧹ V] ++ (L ++ Γ ++ Λ) ⇒ B := by grind
            grind
        | rdiv_l x y =>
          rename_i S T U V W
          rcases list_split_4_cases d_right_eq_x
            with ⟨R, rfl, rfl⟩
               | ⟨L, R, h, rfl, rfl⟩
               | ⟨L, R, rfl, rfl, rfl⟩
               | ⟨L, R, rfl, rfl, rfl⟩
          · let m := list_degree (Δ ++ Γ ++ R ++ [V] ++ W) + tp_degree (B' ⧸ A') + tp_degree B
            have mn : m < deg := by
              grind only [list_degree, tp_degree, list_degree_traversible]
            have d: Δ ++ Γ ++ (R ++ [V] ++ W) ⇒ B := by grind
            have e: (Δ ++ Γ ++ R) ++ [V ⧸ T] ++ S ++ W ⇒ B := by grind
            grind
          · have he: [V ⧸ T] = L ++ [B' ⧸ A'] ++ R → L = [] ∧ R = [] ∧ V = B' ∧ T = A' := by
              intro h
              cases L with
              | nil => grind
              | cons head tail => grind
            have hf: [V ⧸ T] = L ++ [B' ⧸ A'] ++ R → L = [] ∧ R = [] ∧ V = B' ∧ T = A' := by grind
            let m1 := list_degree (U ++ (Γ ++ [A']) ++ W) + tp_degree B' + tp_degree B
            have m1n : m1 < deg := by
              grind only [list_degree, tp_degree, list_degree_traversible]
            have c: (U ++ Γ) ++ S ++ W ⇒ B := by grind
            grind
          · let m := list_degree (L ++ Γ ++ R) + tp_degree (B' ⧸ A') + tp_degree T
            have mn : m < deg := by
              grind only [list_degree_traversible, list_degree, tp_degree]
            have d: L ++ Γ ++ R ⇒ T := by grind
            have e: U ++ [V ⧸ T] ++ (L ++ Γ ++ R) ++ W ⇒ B := by grind
            grind
          · let m := list_degree (U ++ [V] ++ L ++ Γ ++ Λ) + tp_degree (B' ⧸ A') + tp_degree B
            have mn : m < deg := by
              grind only [list_degree_traversible, list_degree, tp_degree]
            have d: U ++ [V] ++ L ++ [B' ⧸ A'] ++ Λ ⇒ B := by grind
            have e: U ++ [V] ++ L ++ Γ ++ Λ ⇒ B := by grind
            grind
      | rdiv_l a b =>
        rename_i A' B' C' D' E'
        cases d_right with
        | ax => sorry
        | rdiv_r _ _ => sorry
        | ldiv_r _ _ => sorry
        | rdiv_l _ _ => sorry
        | ldiv_l _ _ => sorry
        sorry
      | ldiv_l =>
        rename_i A' B' C' D' E'
        cases d_right with
        | ax => sorry
        | rdiv_r _ _ => sorry
        | ldiv_r _ _ => sorry
        | rdiv_l _ _ => sorry
        | ldiv_l _ _ => sorry
        sorry

end Lambek
