import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import LiterateLean

```lean
namespace Mathling.Lambek.ProductFree.Right.Shallow
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.maxHeartbeats false
```

## 論理式の定義

```lean
@[grind cases]
inductive Tp where
  | atom (name : String) : Tp
  | rdiv (B A : String)  : Tp
  deriving Repr, DecidableEq

prefix:65 "#" => Tp.atom
infixl:60 " ⧸ " => Tp.rdiv
```

## シーケント体系の定義

```lean
@[grind intro]
inductive Sequent : List Tp → Tp → Prop where
  | ax : Sequent [A] A
  | rdiv_r :
      Γ ≠ [] →
      Sequent (Γ ++ [# A]) (# B) →
      Sequent Γ (B ⧸ A)
  | rdiv_l :
      Sequent Δ (# A) →
      Sequent (Γ ++ [# B] ++ Λ) C →
      Sequent (Γ ++ [B ⧸ A] ++ Δ ++ Λ) C

infixl:50 " ⇒ " => Sequent
```

## 次数（Degree）の定義

```lean
@[grind =]
def tp_degree : Tp → Nat
  | # _     => 1
  | _ ⧸ _   => 3

@[grind =]
def list_degree : List Tp → Nat
  | []        => 0
  | A :: Γ    => tp_degree A + list_degree Γ

@[grind =]
lemma list_degree_traversible : list_degree (Γ ++ Δ) = list_degree Γ + list_degree Δ := by
  induction Γ <;> grind
```

## シーケントの基本的な性質

```lean
@[grind =>]
lemma nonempty_premises (h : Γ ⇒ A) : Γ ≠ [] := by
  induction h <;> grind [List.append_eq_nil_iff]

@[grind =>]
lemma nonempty_append (h : Γ ≠ []) : Δ ++ Γ ++ Λ ≠ [] := by
  grind only [List.append_eq_nil_iff]
```

## リスト分割に関する補題

```lean
lemma list_split_2_cases
  (h : Γ₁ ++ [α] ++ Γ₂ = Δ₁ ++ Δ₂) :
  (∃ R, Δ₁ = Γ₁ ++ [α] ++ R ∧ Γ₂ = R ++ Δ₂) ∨
  (∃ L R, Δ₂ = L ++ [α] ++ R ∧ Γ₁ = Δ₁ ++ L ∧ Γ₂ = R) := by
  simp only [List.append_assoc] at h
  rcases List.append_eq_append_iff.mp h with ⟨m, rfl, hm⟩ | ⟨m, rfl, hm⟩
  · simp [List.cons_eq_append_iff] at hm
    grind
  · grind

lemma list_split_3_cases
  (h : Γ₁ ++ [α] ++ Γ₂ = Δ₁ ++ Δ₂ ++ Δ₃) :
  (∃ R, Δ₁ = Γ₁ ++ [α] ++ R ∧ Γ₂ = R ++ Δ₂ ++ Δ₃) ∨
  (∃ L R, Δ₂ = L ++ [α] ++ R ∧ Γ₁ = Δ₁ ++ L ∧ Γ₂ = R ++ Δ₃) ∨
  (∃ L R, Δ₃ = L ++ [α] ++ R ∧ Γ₁ = Δ₁ ++ Δ₂ ++ L ∧ Γ₂ = R) := by
  rcases list_split_2_cases (by simpa using h)
    with ⟨R, h1, h2⟩ | ⟨L, R, h1, h2, h3⟩
  · grind
  · rcases list_split_2_cases h1.symm with ⟨R', h4, h5⟩ | ⟨L', R', h4, h5, h6⟩ <;> grind

lemma list_split_4_cases
  (h : Γ₁ ++ [α] ++ Γ₂ = Δ₁ ++ Δ₂ ++ Δ₃ ++ Δ₄) :
  (∃ R, Δ₁ = Γ₁ ++ [α] ++ R ∧ Γ₂ = R ++ Δ₂ ++ Δ₃ ++ Δ₄)
  ∨ (∃ L R, Δ₂ = L ++ [α] ++ R ∧ Γ₁ = Δ₁ ++ L ∧ Γ₂ = R ++ Δ₃ ++ Δ₄)
  ∨ (∃ L R, Δ₃ = L ++ [α] ++ R ∧ Γ₁ = Δ₁ ++ Δ₂ ++ L ∧ Γ₂ = R ++ Δ₄)
  ∨ (∃ L R, Δ₄ = L ++ [α] ++ R ∧ Γ₁ = Δ₁ ++ Δ₂ ++ Δ₃ ++ L ∧ Γ₂ = R) := by
  rcases list_split_2_cases (by simpa using h)
    with ⟨R, h1, h2⟩ | ⟨L, R, h1, h2, h3⟩
  · grind
  · rcases list_split_3_cases (by simpa using h1.symm)
    with ⟨R', h4, h5⟩ | ⟨L', R', h4, h5, h6⟩ | ⟨L', R', h4, h5, h6⟩ <;> grind

lemma rdiv_princ_decomp {L R : List Tp} {B_res A_arg B_left A_left : String}
  (h : [B_res ⧸ A_arg] = L ++ [B_left ⧸ A_left] ++ R) :
  L = [] ∧ R = [] ∧ B_res = B_left ∧ A_arg = A_left := by
  grind [List.singleton_eq_append_iff]

```

## カット除去定理（演繹の許容性）

```lean
set_option maxHeartbeats 1000000 in
@[grind =>]
theorem cut_admissible
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
      | rdiv_r h_ne_L d_inner_L =>
        rename_i A_left B_left
        have h_der_A : Γ ⇒ B_left ⧸ A_left := by grind
        generalize d_right_eq_x : Δ ++ [B_left ⧸ A_left] ++ Λ = ContextRight at d_right
        cases d_right with
        | ax => grind only [List.cons_eq_cons, List.append_assoc, List.append_cons,
          List.append_eq_nil_iff, List.append_eq_singleton_iff, Sequent.rdiv_r]
        | rdiv_r h_ne_R d_inner_R =>
          rename_i C D
          let m := list_degree (Δ ++ Γ ++ Λ ++ [# C]) +
              tp_degree (B_left ⧸ A_left) + tp_degree (# D)
          have h_deg_lt : m < deg := by
            grind only [list_degree, tp_degree, list_degree_traversible]
          have d_cut_result_ih : Δ ++ Γ ++ (Λ ++ [# C]) ⇒ # D := 
            ih m h_deg_lt h_der_A (by
              rw [← d_right_eq_x] at d_inner_R
              have h : Δ ++ [B_left ⧸ A_left] ++ (Λ ++ [# C]) =
                  (Δ ++ [B_left ⧸ A_left] ++ Λ) ++ [# C] := by
                simp only [List.append_assoc]
              rw [h]
              exact d_inner_R) (by grind only [list_degree, tp_degree, list_degree_traversible])
          have d_cut_result : (Δ ++ Γ ++ Λ) ++ [# C] ⇒ # D := by
            have h : Δ ++ Γ ++ (Λ ++ [# C]) = (Δ ++ Γ ++ Λ) ++ [# C] := by
              simp only [List.append_assoc]
            rw [← h]
            exact d_cut_result_ih
          have h_ax : Δ ++ Γ ++ Λ ≠ [] := by grind [nonempty_append]
          exact Sequent.rdiv_r h_ax d_cut_result
        | rdiv_l d_arg d_main =>
          rename_i Δ_arg A_arg Γ_L B_res Γ_R
          rcases list_split_4_cases d_right_eq_x
            with ⟨R, rfl, rfl⟩
               | ⟨L, R, h_princ, rfl, rfl⟩
               | ⟨L, R, rfl, rfl, rfl⟩
               | ⟨L, R, rfl, rfl, rfl⟩
          · let m := list_degree (Δ ++ Γ ++ (R ++ [# B_res] ++ Γ_R)) + tp_degree (B_left ⧸ A_left) + tp_degree B
            have h_deg_lt : m < deg := by
              grind only [list_degree, tp_degree, list_degree_traversible]
            have d_cut_main_ih : Δ ++ Γ ++ (R ++ [# B_res] ++ Γ_R) ⇒ B := 
              ih m h_deg_lt h_der_A (by
                have h : Δ ++ [B_left ⧸ A_left] ++ (R ++ [# B_res] ++ Γ_R) = (Δ ++ [B_left ⧸ A_left] ++ R) ++ [# B_res] ++ Γ_R := by simp only [List.append_assoc]
                rw [h]
                exact d_main) (by grind only [list_degree, tp_degree, list_degree_traversible])
            have d_cut_main : Δ ++ Γ ++ R ++ [# B_res] ++ Γ_R ⇒ B := by
              have h : Δ ++ Γ ++ (R ++ [# B_res] ++ Γ_R) = Δ ++ Γ ++ R ++ [# B_res] ++ Γ_R := by simp only [List.append_assoc]
              rw [← h]
              exact d_cut_main_ih
            have h_eq : Δ ++ Γ ++ (R ++ [B_res ⧸ A_arg] ++ Δ_arg ++ Γ_R) = (Δ ++ Γ ++ R) ++ [B_res ⧸ A_arg] ++ Δ_arg ++ Γ_R := by
              simp only [List.append_assoc]
            rw [h_eq]
            exact Sequent.rdiv_l (Λ := Γ_R) d_arg (by
              have h2 : (Δ ++ Γ ++ R) ++ [# B_res] ++ Γ_R = Δ ++ Γ ++ R ++ [# B_res] ++ Γ_R := by simp only [List.append_assoc]
              rw [h2]
              exact d_cut_main)
          · have h_decomp: L = [] ∧ R = [] ∧ B_res = B_left ∧ A_arg = A_left := rdiv_princ_decomp h_princ
            rcases h_decomp with ⟨rfl, rfl, rfl, rfl⟩
            clear h_princ 
            let m0 := list_degree (Γ ++ Δ_arg ++ []) + tp_degree (# A_arg) + tp_degree (# B_res)
            have h_deg_lt0 : m0 < deg := by
              grind only [list_degree, tp_degree, list_degree_traversible]
            have d_cut1_ih : Γ ++ Δ_arg ++ [] ⇒ # B_res :=
              ih m0 h_deg_lt0 d_arg (by
                have h : Γ ++ [# A_arg] ++ [] = Γ ++ [# A_arg] := by simp only [List.append_nil]
                rw [h]
                exact d_inner_L) (by grind only [list_degree, tp_degree, list_degree_traversible])
            have d_cut1 : Γ ++ Δ_arg ⇒ # B_res := by
              have h : Γ ++ Δ_arg ++ [] = Γ ++ Δ_arg := by
                simp only [List.append_nil, List.append_assoc]
              rw [← h]
              exact d_cut1_ih
            let m1 := list_degree (Γ_L ++ (Γ ++ Δ_arg) ++ Γ_R) + tp_degree (# B_res) + tp_degree B
            have h_deg_lt1 : m1 < deg := by
              grind only [list_degree, tp_degree, list_degree_traversible]
            have d_cut2_ih : Γ_L ++ (Γ ++ Δ_arg) ++ Γ_R ⇒ B :=
              ih m1 h_deg_lt1 d_cut1 d_main
                (by grind only [list_degree, tp_degree, list_degree_traversible])
            have d_cut2 : Γ_L ++ Γ ++ Δ_arg ++ Γ_R ⇒ B := by
              have h : Γ_L ++ (Γ ++ Δ_arg) ++ Γ_R = Γ_L ++ Γ ++ Δ_arg ++ Γ_R := by simp only [List.append_assoc]
              rw [← h]
              exact d_cut2_ih
            have h_eq : (Γ_L ++ []) ++ Γ ++ ([] ++ Δ_arg ++ Γ_R) = Γ_L ++ Γ ++ Δ_arg ++ Γ_R := by
              simp only [List.append_nil, List.nil_append, List.append_assoc]
            rw [h_eq]
            exact d_cut2
          · let m := list_degree (L ++ Γ ++ R) + tp_degree (B_left ⧸ A_left) + tp_degree (# A_arg)
            have h_deg_lt : m < deg := by
              grind only [list_degree, tp_degree, list_degree_traversible]
            have d_cut_arg : L ++ Γ ++ R ⇒ # A_arg :=
              ih m h_deg_lt h_der_A d_arg
                (by grind only [list_degree, tp_degree, list_degree_traversible])
            have h_eq : (Γ_L ++ [B_res ⧸ A_arg] ++ L) ++ Γ ++ (R ++ Γ_R) = Γ_L ++ [B_res ⧸ A_arg] ++ (L ++ Γ ++ R) ++ Γ_R := by
              simp only [List.append_assoc]
            rw [h_eq]
            exact Sequent.rdiv_l (Λ := Γ_R) d_cut_arg d_main
          · let m := list_degree (Γ_L ++ [# B_res] ++ L ++ Γ ++ Λ) + tp_degree (B_left ⧸ A_left) + tp_degree B
            have h_deg_lt : m < deg := by
              grind only [list_degree, tp_degree, list_degree_traversible]
            have d_cut_main : Γ_L ++ [# B_res] ++ L ++ Γ ++ Λ ⇒ B := 
              ih m h_deg_lt h_der_A (by
                have h : Γ_L ++ [# B_res] ++ (L ++ [B_left ⧸ A_left] ++ Λ) = Γ_L ++ [# B_res] ++ L ++ [B_left ⧸ A_left] ++ Λ := by simp only [List.append_assoc]
                rw [← h]
                exact d_main) (by grind only [list_degree, tp_degree, list_degree_traversible])
            have h_eq : (Γ_L ++ [B_res ⧸ A_arg] ++ Δ_arg ++ L) ++ Γ ++ Λ = Γ_L ++ [B_res ⧸ A_arg] ++ Δ_arg ++ (L ++ Γ ++ Λ) := by
              simp only [List.append_assoc]
            rw [h_eq]
            exact Sequent.rdiv_l (Λ := L ++ Γ ++ Λ) d_arg (by
              have h2 : Γ_L ++ [# B_res] ++ (L ++ Γ ++ Λ) = Γ_L ++ [# B_res] ++ L ++ Γ ++ Λ := by simp only [List.append_assoc]
              rw [h2]
              exact d_cut_main)
      | rdiv_l d_arg d_main =>
        rename_i Δ_arg A_arg Γ_L B_res Γ_R
        let m := list_degree (Δ ++ Γ_L ++ [# B_res] ++ Γ_R ++ Λ) + tp_degree A + tp_degree B
        have h_deg_lt : m < deg := by
          grind only [list_degree, tp_degree, list_degree_traversible]
        have d_restored_context_ih : Δ ++ (Γ_L ++ [# B_res] ++ Γ_R) ++ Λ ⇒ B := ih m h_deg_lt d_main d_right (by grind only [list_degree, tp_degree, list_degree_traversible])
        have d_restored_context : Δ ++ Γ_L ++ [# B_res] ++ Γ_R ++ Λ ⇒ B := by
          have h : Δ ++ (Γ_L ++ [# B_res] ++ Γ_R) ++ Λ = Δ ++ Γ_L ++ [# B_res] ++ Γ_R ++ Λ := by simp only [List.append_assoc]
          rw [← h]
          exact d_restored_context_ih
        have h_goal : Δ ++ (Γ_L ++ [B_res ⧸ A_arg] ++ Δ_arg ++ Γ_R) ++ Λ = (Δ ++ Γ_L) ++ [B_res ⧸ A_arg] ++ Δ_arg ++ (Γ_R ++ Λ) := by
          simp only [List.append_assoc]
        rw [h_goal]
        have h_premise : (Δ ++ Γ_L) ++ [# B_res] ++ (Γ_R ++ Λ) = Δ ++ Γ_L ++ [# B_res] ++ Γ_R ++ Λ := by
          simp only [List.append_assoc]
        exact Sequent.rdiv_l (Λ := Γ_R ++ Λ) d_arg (by rw [h_premise]; exact d_restored_context)
```

## 除法の逆転可能性（Invertibility）

```lean
@[grind =>]
theorem rdiv_invertible {Γ : List Tp} {B A : String} (h : Γ ⇒ (B ⧸ A)) :
  Γ ++ [# A] ⇒ # B := by
    have a: [# A] ⇒ # A := by grind
    have b: [# B] ⇒ # B := by grind
    have c: [] ++ [B ⧸ A] ++ [# A] ++ [] ⇒ # B := by grind
    grind
```

## 原子式に関する性質

```lean
@[grind]
def is_atom : Tp → Prop
  | Tp.atom _ => True
  | _   => False

@[grind =>]
theorem atom_generation
  (h_ctx : ∀ x ∈ Γ, is_atom x)
  (h_der : Γ ⇒ Tp.atom s) :
    Γ = [Tp.atom s] := by
  cases h_der with
  | ax =>
      grind
  | rdiv_l d_arg d_main =>
      rename_i Δ A Γ₁ B Λ
      have hbad : is_atom (B ⧸ A) := by grind
      grind
```

```lean
end Mathling.Lambek.ProductFree.Right.Shallow
```
