import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import LiterateLean

# Shallow Fragment of Product-Free Lambek Calculus

```lean
set_option linter.style.emptyLine false
set_option linter.style.whitespace false

namespace Mathling.Lambek.ProductFree.Shallow
```

## 論理式の定義

```lean
@[grind cases]
inductive Tp where
  | atom (name : String) : Tp
  | ldiv (A B : String)  : Tp
  | rdiv (B A : String)  : Tp
  deriving Repr, DecidableEq

prefix:65 "#" => Tp.atom
infixr:60 " ⧹ " => Tp.ldiv
infixl:60 " ⧸ " => Tp.rdiv
```

## シーケント体系の定義

```lean
@[grind intro]
inductive Sequent : List Tp → Tp → Prop where
  | ax : Sequent [A] A
  | ldiv_r :
      Γ ≠ [] →
      Sequent ([# A] ++ Γ) (# B) →
      Sequent Γ (A ⧹ B)
  | rdiv_r :
      Γ ≠ [] →
      Sequent (Γ ++ [# A]) (# B) →
      Sequent Γ (B ⧸ A)
  | ldiv_l :
      Sequent Δ (# A) →
      Sequent (Γ ++ [# B] ++ Λ) C →
      Sequent (Γ ++ Δ ++ [A ⧹ B] ++ Λ) C
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
  | _ ⧹ _   => 3
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
  simp only [List.append_assoc, List.nil_append] at h
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

lemma ldiv_princ_decomp {L R : List Tp} {A_arg B_res A_den B_num : String}
  (h : [A_arg ⧹ B_res] = L ++ [A_den ⧹ B_num] ++ R) :
  L = [] ∧ R = [] ∧ A_arg = A_den ∧ B_res = B_num := by
  grind [List.singleton_eq_append_iff]

lemma rdiv_princ_decomp {L R : List Tp} {B_res A_arg B_num A_den : String}
  (h : [B_res ⧸ A_arg] = L ++ [B_num ⧸ A_den] ++ R) :
  L = [] ∧ R = [] ∧ B_res = B_num ∧ A_arg = A_den := by
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
    induction n using Nat.strong_induction_on generalizing Γ Δ Λ A B d_left d_right
    next n ih =>
      subst h_n
      cases d_left with
      | ax => simp at d_right; exact d_right
      | ldiv_r h_ne_L d_inner_L =>
        rename_i A_den B_num
        generalize d_right_eq_x : Δ ++ [A_den ⧹ B_num] ++ Λ = ContextRight at d_right
        cases d_right with
        | ax =>
          simp [List.append_eq_nil_iff, List.cons_eq_append_iff] at d_right_eq_x
          rcases d_right_eq_x with ⟨rfl, rfl, rfl⟩
          exact Sequent.ldiv_r h_ne_L d_inner_L
        | ldiv_r h_ne_R d_inner_R =>
          rename_i C_den D_num
          let m := list_degree ([# C_den] ++ Δ ++ Γ ++ Λ) + tp_degree (A_den ⧹ B_num) + tp_degree (# D_num)
          have h_m : m < list_degree (Δ ++ Γ ++ Λ) + tp_degree (A_den ⧹ B_num) + tp_degree (C_den ⧹ D_num) := by
            grind only [list_degree, tp_degree, list_degree_traversible]
          exact Sequent.ldiv_r h_ne_R (ih m h_m (by grind) (by grind) (by grind))
        | rdiv_r h_ne_R d_inner_R =>
          rename_i D_num C_den
          let m := list_degree (Δ ++ Γ ++ Λ ++ [# C_den]) + tp_degree (A_den ⧹ B_num) + tp_degree (# D_num)
          have h_m : m < list_degree (Δ ++ Γ ++ Λ) + tp_degree (A_den ⧹ B_num) + tp_degree (D_num ⧸ C_den) := by
            grind only [list_degree, tp_degree, list_degree_traversible]
          exact Sequent.rdiv_r h_ne_R (ih m h_m (by grind) (by grind) (by grind))
        | ldiv_l d_arg d_main =>
          rename_i Δ_p A_p Γ_p B_p Λ_p C_p
          rcases list_split_4_cases d_right_eq_x with ⟨R, h1, h2⟩ | ⟨L, R, h1, h2, h3⟩ | ⟨L, R, h1, h2, h3⟩ | ⟨L, R, h1, h2, h3⟩
          · subst h1; subst h2
            have deg_val := list_degree (Δ ++ Γ ++ (R ++ [# B_p] ++ Λ_p)) + tp_degree (A_den ⧹ B_num) + tp_degree B
            have d_cut := ih deg_val (by grind only [list_degree, tp_degree, list_degree_traversible]) d_left d_main (by grind)
            exact Sequent.ldiv_l d_arg (by grind)
          · subst h2; subst h3
            have deg_val := list_degree (L ++ Γ ++ R) + tp_degree (A_den ⧹ B_num) + tp_degree (# A_p)
            have d_cut := ih deg_val (by grind only [list_degree, tp_degree, list_degree_traversible]) d_left d_arg (by grind)
            exact Sequent.ldiv_l d_cut (by grind)
          · rcases ldiv_princ_decomp h1 with ⟨rfl, rfl, rfl, rfl⟩
            subst h2; subst h3
            let m1 := list_degree ([] ++ Δ_p ++ Γ) + tp_degree (# A_den) + tp_degree (# B_num)
            have d_cut1 := ih m1 (by grind only [list_degree, tp_degree, list_degree_traversible]) d_arg d_inner_L (by grind)
            let m2 := list_degree (Γ_p ++ (Δ_p ++ Γ) ++ Λ_p) + tp_degree (# B_num) + tp_degree B
            exact ih m2 (by grind only [list_degree, tp_degree, list_degree_traversible]) d_cut1 d_main (by grind)
          · subst h2; subst h3
            have deg_val := list_degree (Γ_p ++ [# B_p] ++ (L ++ Γ ++ R)) + tp_degree (A_den ⧹ B_num) + tp_degree B
            have d_cut := ih deg_val (by grind only [list_degree, tp_degree, list_degree_traversible]) d_left d_main (by grind)
            exact Sequent.ldiv_l d_arg (by grind)
        | rdiv_l d_arg d_main =>
          rename_i Δ_p A_p Γ_p B_p Λ_p C_p
          rcases list_split_4_cases d_right_eq_x with ⟨R, h1, h2⟩ | ⟨L, R, h1, h2, h3⟩ | ⟨L, R, h1, h2, h3⟩ | ⟨L, R, h1, h2, h3⟩
          · subst h1; subst h2
            have deg_val := list_degree (Δ ++ Γ ++ (R ++ [# B_p] ++ Λ_p)) + tp_degree (A_den ⧹ B_num) + tp_degree B
            have d_cut := ih deg_val (by grind only [list_degree, tp_degree, list_degree_traversible]) d_left d_main (by grind)
            exact Sequent.rdiv_l d_arg (by grind)
          · grind [Tp.injectivity]
          · subst h2; subst h3
            have deg_val := list_degree (L ++ Γ ++ R) + tp_degree (A_den ⧹ B_num) + tp_degree (# A_p)
            have d_cut := ih deg_val (by grind only [list_degree, tp_degree, list_degree_traversible]) d_left d_arg (by grind)
            exact Sequent.rdiv_l d_cut (by grind)
          · subst h2; subst h3
            have deg_val := list_degree (Γ_p ++ [# B_p] ++ (L ++ Γ ++ R)) + tp_degree (A_den ⧹ B_num) + tp_degree B
            have d_cut := ih deg_val (by grind only [list_degree, tp_degree, list_degree_traversible]) d_left d_main (by grind)
            exact Sequent.rdiv_l d_arg (by grind)
      | rdiv_r h_ne_L d_inner_L =>
        rename_i B_num A_den
        generalize d_right_eq_x : Δ ++ [B_num ⧸ A_den] ++ Λ = ContextRight at d_right
        cases d_right with
        | ax =>
          simp [List.append_eq_nil_iff, List.cons_eq_append_iff] at d_right_eq_x
          rcases d_right_eq_x with ⟨rfl, rfl, rfl⟩
          exact Sequent.rdiv_r h_ne_L d_inner_L
        | ldiv_r h_ne_R d_inner_R =>
          rename_i C_den D_num
          let m := list_degree ([# C_den] ++ Δ ++ Γ ++ Λ) + tp_degree (B_num ⧸ A_den) + tp_degree (# D_num)
          exact Sequent.ldiv_r h_ne_R (ih m (by grind only [list_degree, tp_degree, list_degree_traversible]) (by grind) (by grind) (by grind))
        | rdiv_r h_ne_R d_inner_R =>
          rename_i D_num C_den
          let m := list_degree (Δ ++ Γ ++ Λ ++ [# C_den]) + tp_degree (B_num ⧸ A_den) + tp_degree (# D_num)
          exact Sequent.rdiv_r h_ne_R (ih m (by grind only [list_degree, tp_degree, list_degree_traversible]) (by grind) (by grind) (by grind))
        | ldiv_l d_arg d_main =>
          rename_i Δ_p A_p Γ_p B_p Λ_p C_p
          rcases list_split_4_cases d_right_eq_x with ⟨R, h1, h2⟩ | ⟨L, R, h1, h2, h3⟩ | ⟨L, R, h1, h2, h3⟩ | ⟨L, R, h1, h2, h3⟩
          · subst h1; subst h2
            have deg_val := list_degree (Δ ++ Γ ++ (R ++ [# B_p] ++ Λ_p)) + tp_degree (B_num ⧸ A_den) + tp_degree B
            have d_cut := ih deg_val (by grind only [list_degree, tp_degree, list_degree_traversible]) d_left d_main (by grind)
            exact Sequent.ldiv_l d_arg (by grind)
          · subst h2; subst h3
            have deg_val := list_degree (L ++ Γ ++ R) + tp_degree (B_num ⧸ A_den) + tp_degree (# A_p)
            have d_cut := ih deg_val (by grind only [list_degree, tp_degree, list_degree_traversible]) d_left d_arg (by grind)
            exact Sequent.ldiv_l d_cut (by grind)
          · grind [Tp.injectivity]
          · subst h2; subst h3
            have deg_val := list_degree (Γ_p ++ [# B_p] ++ (L ++ Γ ++ R)) + tp_degree (B_num ⧸ A_den) + tp_degree B
            have d_cut := ih deg_val (by grind only [list_degree, tp_degree, list_degree_traversible]) d_left d_main (by grind)
            exact Sequent.ldiv_l d_arg (by grind)
        | rdiv_l d_arg d_main =>
          rename_i Δ_p A_p Γ_p B_p Λ_p C_p
          rcases list_split_4_cases d_right_eq_x with ⟨R, h1, h2⟩ | ⟨L, R, h1, h2, h3⟩ | ⟨L, R, h1, h2, h3⟩ | ⟨L, R, h1, h2, h3⟩
          · subst h1; subst h2
            have deg_val := list_degree (Δ ++ Γ ++ (R ++ [# B_p] ++ Λ_p)) + tp_degree (B_num ⧸ A_den) + tp_degree B
            have d_cut := ih deg_val (by grind only [list_degree, tp_degree, list_degree_traversible]) d_left d_main (by grind)
            exact Sequent.rdiv_l d_arg (by grind)
          · rcases rdiv_princ_decomp h1 with ⟨rfl, rfl, rfl, rfl⟩
            subst h2; subst h3
            let m1 := list_degree (Γ ++ Δ_p ++ []) + tp_degree (# A_den) + tp_degree (# B_num)
            have d_cut1 := ih m1 (by grind only [list_degree, tp_degree, list_degree_traversible]) d_arg d_inner_L (by grind)
            let m2 := list_degree (Γ_p ++ (Γ ++ Δ_p) ++ Λ_p) + tp_degree (# B_num) + tp_degree B
            exact ih m2 (by grind only [list_degree, tp_degree, list_degree_traversible]) d_cut1 d_main (by grind)
          · subst h2; subst h3
            have deg_val := list_degree (L ++ Γ ++ R) + tp_degree (B_num ⧸ A_den) + tp_degree (# A_p)
            have d_cut := ih deg_val (by grind only [list_degree, tp_degree, list_degree_traversible]) d_left d_arg (by grind)
            exact Sequent.rdiv_l d_cut (by grind)
          · subst h2; subst h3
            have deg_val := list_degree (Γ_p ++ [# B_p] ++ (L ++ Γ ++ R)) + tp_degree (B_num ⧸ A_den) + tp_degree B
            have d_cut := ih deg_val (by grind only [list_degree, tp_degree, list_degree_traversible]) d_left d_main (by grind)
            exact Sequent.rdiv_l d_arg (by grind)
      | ldiv_l d_arg d_main =>
        rename_i Δ_p A_p Γ_p B_p Λ_p C_p
        let m := list_degree (Δ ++ Γ_p ++ [# B_p] ++ Λ_p ++ Λ) + tp_degree A + tp_degree B
        have d_cut := ih m (by grind only [list_degree, tp_degree, list_degree_traversible]) d_main d_right (by grind)
        exact Sequent.ldiv_l d_arg (by grind)
      | rdiv_l d_arg d_main =>
        rename_i Δ_p A_p Γ_p B_p Λ_p C_p
        let m := list_degree (Δ ++ (Γ_p ++ [# B_p] ++ Λ_p) ++ Λ) + tp_degree A + tp_degree B
        have d_cut := ih m (by grind only [list_degree, tp_degree, list_degree_traversible]) d_main d_right (by grind)
        exact Sequent.rdiv_l d_arg (by grind)
```

## 除法の逆転可能性（Invertibility）

```lean
@[grind =>]
theorem ldiv_invertible {Γ : List Tp} {A B : String} (h : Γ ⇒ (A ⧹ B)) :
  [# A] ++ Γ ⇒ # B := by
    have c : [# A] ++ [A ⧹ B] ⇒ # B := by repeat constructor
    exact cut_admissible h c

@[grind =>]
theorem rdiv_invertible {Γ : List Tp} {B A : String} (h : Γ ⇒ (B ⧸ A)) :
  Γ ++ [# A] ⇒ # B := by
    have c : [B ⧸ A] ++ [# A] ⇒ # B := by repeat constructor
    exact cut_admissible (Δ := []) (Λ := [# A]) h c
```

## 原子式に関する性質

```lean
@[grind]
def is_atom : Tp → Prop
  | Tp.atom _ => True
  | _   => False

@[grind =>]
theorem atom_generation (h_ctx : ∀ x ∈ Γ, is_atom x) (h_der : Γ ⇒ Tp.atom s) : Γ = [Tp.atom s] := by
  cases h_der with
  | ax => grind
  | ldiv_r => grind
  | rdiv_r => grind
  | ldiv_l d_arg d_main =>
      rename_i Δ A Γ₁ B Λ
      have hbad : is_atom (A ⧹ B) := by grind
      grind
  | rdiv_l d_arg d_main =>
      rename_i Δ A Γ₁ B Λ
      have hbad : is_atom (B ⧸ A) := by grind
      grind

end Mathling.Lambek.ProductFree.Shallow
```
