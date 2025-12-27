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

lemma splits_mem {α} (Γ Δ : List α) : (Γ, Δ) ∈ splits (Γ ++ Δ) := by
  induction Γ with
  | nil =>
      cases Δ <;> simp [splits]
  | cons x xs ih =>
      apply List.mem_cons_of_mem
      refine List.mem_map.mpr ?_
      refine ⟨(xs, Δ), ih, ?_⟩
      simp

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

lemma candidates_rdiv_mem (Γ Δ Λ : List Tp) (A B : Tp) :
  Cand.rdiv Γ B A Δ Λ ∈ candidates (Γ ++ [B ⧸ A] ++ Δ ++ Λ) := by
  unfold candidates
  refine List.mem_flatMap.mpr ?_
  refine ⟨(Γ, B ⧸ A, Δ ++ Λ), ?_, ?_⟩
  · simpa [List.append_assoc] using
      (picks_mem (Γ:=Γ) (a:=B ⧸ A) (Δ:=Δ ++ Λ))
  · refine List.mem_map.mpr ?_
    refine ⟨(Δ, Λ), ?_, ?_⟩
    · simpa [List.append_assoc] using (splits_mem (Γ:=Δ) (Δ:=Λ))
    · simp

lemma candidates_ldiv_mem (Γ₁ Δ R : List Tp) (A B : Tp) :
  Cand.ldiv Γ₁ Δ A B R ∈ candidates (Γ₁ ++ Δ ++ [A ⧹ B] ++ R) := by
  unfold candidates
  refine List.mem_flatMap.mpr ?_
  refine ⟨(Γ₁ ++ Δ, A ⧹ B, R), ?_, ?_⟩
  · simpa [List.append_assoc] using
      (picks_mem (Γ:=Γ₁ ++ Δ) (a:=A ⧹ B) (Δ:=R))
  · refine List.mem_map.mpr ?_
    refine ⟨(Γ₁, Δ), ?_, ?_⟩
    · simpa [List.append_assoc] using (splits_mem (Γ:=Γ₁) (Δ:=Δ))
    · simp

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
  case case1 Γ s h_rdiv_left h_rdiv_right h_ldiv_left h_ldiv_right =>
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
        · have h_le :
            list_degree Δ + tp_degree A' + 1 ≤
              list_degree Γ + tp_degree (# s) := by
            have h_ctx :
                L ++ [B ⧸ A'] ++ Δ ++ Λ = Γ := by
              simpa using
                (candidates_list_degree (Γ:=Γ) (c:=Cand.rdiv L B A' Δ Λ) hc_mem)
            grind only [list_degree_traversible, list_degree, tp_degree]
          exact proveAux_mono_le h_le (h_rdiv_left L B A' Δ Λ hc_mem hc_val.1)
        · have h_le :
            list_degree (L ++ [B] ++ Λ) + tp_degree (# s) + 1 ≤
              list_degree Γ + tp_degree (# s) := by
            have h_ctx :
                L ++ [B ⧸ A'] ++ Δ ++ Λ = Γ := by
              simpa using
                (candidates_list_degree (Γ:=Γ) (c:=Cand.rdiv L B A' Δ Λ) hc_mem)
            grind only [list_degree_traversible, list_degree, tp_degree]
          exact proveAux_mono_le h_le (h_rdiv_right L B A' Δ Λ hc_mem hc_val.2)
      | ldiv Γ₁ Δ A' B R =>
        simp only [Bool.and_eq_true] at hc_val ⊢
        constructor
        · have h_le :
            list_degree Δ + tp_degree A' + 1 ≤
              list_degree Γ + tp_degree (# s) := by
            have h_ctx :
                Γ₁ ++ Δ ++ [A' ⧹ B] ++ R = Γ := by
              simpa using
                (candidates_list_degree (Γ:=Γ) (c:=Cand.ldiv Γ₁ Δ A' B R) hc_mem)
            grind only [list_degree_traversible, list_degree, tp_degree]
          exact proveAux_mono_le h_le (h_ldiv_left Γ₁ Δ A' B R hc_mem hc_val.1)
        · have h_le :
            list_degree (Γ₁ ++ [B] ++ R) + tp_degree (# s) + 1 ≤
              list_degree Γ + tp_degree (# s) := by
            have h_ctx :
                Γ₁ ++ Δ ++ [A' ⧹ B] ++ R = Γ := by
              simpa using
                (candidates_list_degree (Γ:=Γ) (c:=Cand.ldiv Γ₁ Δ A' B R) hc_mem)
            grind only [list_degree_traversible, list_degree, tp_degree]
          exact proveAux_mono_le h_le (h_ldiv_right Γ₁ Δ A' B R hc_mem hc_val.2)
  case case2 Γ A' B h_rec =>
    unfold prove1 at h
    unfold proveAux
    simp only [Bool.and_eq_true] at h ⊢
    rcases h with ⟨h_ne, h_inner⟩
    constructor
    · exact h_ne
    · have h_eq :
        list_degree (A' :: Γ) + tp_degree B + 1 =
          list_degree Γ + tp_degree (A' ⧹ B) := by
        grind only [list_degree, tp_degree]
      simpa [h_eq] using (h_rec h_inner)
  case case3 Γ B A' h_rec =>
    unfold prove1 at h
    unfold proveAux
    simp only [Bool.and_eq_true] at h ⊢
    rcases h with ⟨h_ne, h_inner⟩
    constructor
    · exact h_ne
    · have h_eq :
        list_degree (Γ ++ [A']) + tp_degree B + 1 =
          list_degree Γ + tp_degree (B ⧸ A') := by
        grind only [list_degree_traversible, list_degree, tp_degree]
      simpa [h_eq] using (h_rec h_inner)

lemma prove1_iff_prove2 : prove1 Γ A ↔ prove2 Γ A := by
  constructor
  · exact proveAux_complete
  · intro h
    exact proveAux_sound h

lemma prove1_sound : prove1 Γ A → Γ ⇒ A := by
  induction Γ, A using prove1.induct with
  | case1 Γ s h_rdiv_left h_rdiv_right h_ldiv_left h_ldiv_right =>
      intro h
      unfold prove1 at h
      simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at h
      rcases h with h_ax | h_cand
      · subst h_ax
        exact Sequent.ax
      · rcases h_cand with ⟨⟨c, hc_mem⟩, -, hc_val⟩
        cases c with
        | rdiv L B A' Δ Λ =>
            simp only [Bool.and_eq_true] at hc_val
            have h_arg : Δ ⇒ A' := h_rdiv_left L B A' Δ Λ hc_mem hc_val.1
            have h_main : L ++ [B] ++ Λ ⇒ # s := h_rdiv_right L B A' Δ Λ hc_mem hc_val.2
            have h_ctx :
                L ++ [B ⧸ A'] ++ Δ ++ Λ = Γ := by
              simpa using
                (candidates_list_degree (Γ:=Γ) (c:=Cand.rdiv L B A' Δ Λ) hc_mem)
            have h_ctx' :
                L ++ (B ⧸ A') :: (Δ ++ Λ) = Γ := by
              simpa [List.append_assoc, List.cons_append] using h_ctx
            simpa [h_ctx'] using
              (Sequent.rdiv_l (Γ:=L) (Δ:=Δ) (Λ:=Λ) (A:=A') (B:=B) (C:=# s) h_arg h_main)
        | ldiv Γ₁ Δ A' B R =>
            simp only [Bool.and_eq_true] at hc_val
            have h_arg : Δ ⇒ A' := h_ldiv_left Γ₁ Δ A' B R hc_mem hc_val.1
            have h_main : Γ₁ ++ [B] ++ R ⇒ # s := h_ldiv_right Γ₁ Δ A' B R hc_mem hc_val.2
            have h_ctx :
                Γ₁ ++ Δ ++ [A' ⧹ B] ++ R = Γ := by
              simpa using
                (candidates_list_degree (Γ:=Γ) (c:=Cand.ldiv Γ₁ Δ A' B R) hc_mem)
            have h_ctx' :
                Γ₁ ++ (Δ ++ (A' ⧹ B) :: R) = Γ := by
              simpa [List.append_assoc, List.cons_append] using h_ctx
            simpa [h_ctx'] using
              (Sequent.ldiv_l (Γ:=Γ₁) (Δ:=Δ) (Λ:=R) (A:=A') (B:=B) (C:=# s) h_arg h_main)
  | case2 Γ A' B h_rec =>
      intro h
      unfold prove1 at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with ⟨h_ne, h_inner⟩
      exact Sequent.ldiv_r h_ne (h_rec h_inner)
  | case3 Γ B A' h_rec =>
      intro h
      unfold prove1 at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with ⟨h_ne, h_inner⟩
      exact Sequent.rdiv_r h_ne (h_rec h_inner)

lemma prove1_complete : Γ ⇒ A → prove1 Γ A := by
  classical
  have h :
      ∀ n Γ A, list_degree Γ + tp_degree A = n → Γ ⇒ A → prove1 Γ A := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih Γ A h_deg h
    cases A with
    | atom s =>
        cases h with
        | ax =>
            unfold prove1
            simp
        | rdiv_l d_arg d_main =>
            rename_i Δ A Γ₁ B Λ
            have h_lt_arg : list_degree Δ + tp_degree A < n := by
              have h_lt :
                  list_degree Δ + tp_degree A <
                    list_degree (Γ₁ ++ [B ⧸ A] ++ Δ ++ Λ) + tp_degree (# s) := by
                grind only [list_degree_traversible, list_degree, tp_degree]
              have h_lt' :
                  list_degree Δ + tp_degree A <
                    list_degree (Γ₁ ++ (B ⧸ A) :: (Δ ++ Λ)) + tp_degree (# s) := by
                simpa [List.append_assoc, List.cons_append] using h_lt
              have h_deg' :
                  list_degree (Γ₁ ++ (B ⧸ A) :: (Δ ++ Λ)) + tp_degree (# s) = n := by
                simpa [List.append_assoc, List.cons_append] using h_deg
              calc
                list_degree Δ + tp_degree A
                    < list_degree (Γ₁ ++ (B ⧸ A) :: (Δ ++ Λ)) + tp_degree (# s) := h_lt'
                _ = n := h_deg'
            have h_lt_main : list_degree (Γ₁ ++ [B] ++ Λ) + tp_degree (# s) < n := by
              have h_lt :
                  list_degree (Γ₁ ++ B :: Λ) <
                    list_degree (Γ₁ ++ (B ⧸ A) :: (Δ ++ Λ)) := by
                grind only [list_degree_traversible, list_degree, tp_degree]
              have h_lt' :
                  list_degree (Γ₁ ++ B :: Λ) + tp_degree (# s) <
                    list_degree (Γ₁ ++ (B ⧸ A) :: (Δ ++ Λ)) + tp_degree (# s) := by
                exact Nat.add_lt_add_right h_lt (tp_degree (# s))
              have h_deg' :
                  list_degree (Γ₁ ++ (B ⧸ A) :: (Δ ++ Λ)) + tp_degree (# s) = n := by
                simpa [List.append_assoc, List.cons_append] using h_deg
              calc
                list_degree (Γ₁ ++ [B] ++ Λ) + tp_degree (# s)
                    = list_degree (Γ₁ ++ B :: Λ) + tp_degree (# s) := by
                      simp [List.append_assoc, List.cons_append]
                _ < list_degree (Γ₁ ++ (B ⧸ A) :: (Δ ++ Λ)) + tp_degree (# s) := h_lt'
                _ = n := h_deg'
            have h_arg :
                prove1 Δ A := ih _ h_lt_arg Δ A rfl d_arg
            have h_main :
                prove1 (Γ₁ ++ [B] ++ Λ) (# s) := ih _ h_lt_main _ _ rfl d_main
            unfold prove1
            simp only [Bool.or_eq_true, List.any_eq_true]
            right
            refine ⟨⟨Cand.rdiv Γ₁ B A Δ Λ,
              candidates_rdiv_mem (Γ:=Γ₁) (Δ:=Δ) (Λ:=Λ) (A:=A) (B:=B)⟩, by simp, ?_⟩
            simp only [Bool.and_eq_true]
            exact ⟨h_arg, h_main⟩
        | ldiv_l d_arg d_main =>
            rename_i Δ A Γ₁ B Λ
            have h_lt_arg : list_degree Δ + tp_degree A < n := by
              have h_lt :
                  list_degree Δ + tp_degree A <
                    list_degree (Γ₁ ++ Δ ++ [A ⧹ B] ++ Λ) + tp_degree (# s) := by
                grind only [list_degree_traversible, list_degree, tp_degree]
              have h_lt' :
                  list_degree Δ + tp_degree A <
                    list_degree (Γ₁ ++ (Δ ++ (A ⧹ B) :: Λ)) + tp_degree (# s) := by
                simpa [List.append_assoc, List.cons_append] using h_lt
              have h_deg' :
                  list_degree (Γ₁ ++ (Δ ++ (A ⧹ B) :: Λ)) + tp_degree (# s) = n := by
                simpa [List.append_assoc, List.cons_append] using h_deg
              calc
                list_degree Δ + tp_degree A
                    < list_degree (Γ₁ ++ (Δ ++ (A ⧹ B) :: Λ)) + tp_degree (# s) := h_lt'
                _ = n := h_deg'
            have h_lt_main : list_degree (Γ₁ ++ [B] ++ Λ) + tp_degree (# s) < n := by
              have h_lt :
                  list_degree (Γ₁ ++ B :: Λ) <
                    list_degree (Γ₁ ++ (Δ ++ (A ⧹ B) :: Λ)) := by
                grind only [list_degree_traversible, list_degree, tp_degree]
              have h_lt' :
                  list_degree (Γ₁ ++ B :: Λ) + tp_degree (# s) <
                    list_degree (Γ₁ ++ (Δ ++ (A ⧹ B) :: Λ)) + tp_degree (# s) := by
                exact Nat.add_lt_add_right h_lt (tp_degree (# s))
              have h_deg' :
                  list_degree (Γ₁ ++ (Δ ++ (A ⧹ B) :: Λ)) + tp_degree (# s) = n := by
                simpa [List.append_assoc, List.cons_append] using h_deg
              calc
                list_degree (Γ₁ ++ [B] ++ Λ) + tp_degree (# s)
                    = list_degree (Γ₁ ++ B :: Λ) + tp_degree (# s) := by
                      simp [List.append_assoc, List.cons_append]
                _ < list_degree (Γ₁ ++ (Δ ++ (A ⧹ B) :: Λ)) + tp_degree (# s) := h_lt'
                _ = n := h_deg'
            have h_arg :
                prove1 Δ A := ih _ h_lt_arg Δ A rfl d_arg
            have h_main :
                prove1 (Γ₁ ++ [B] ++ Λ) (# s) := ih _ h_lt_main _ _ rfl d_main
            unfold prove1
            simp only [Bool.or_eq_true, List.any_eq_true]
            right
            refine ⟨⟨Cand.ldiv Γ₁ Δ A B Λ,
              candidates_ldiv_mem (Γ₁:=Γ₁) (Δ:=Δ) (R:=Λ) (A:=A) (B:=B)⟩, by simp, ?_⟩
            simp only [Bool.and_eq_true]
            exact ⟨h_arg, h_main⟩
    | ldiv A' B =>
        have h_ne : Γ ≠ [] := nonempty_premises h
        have h_inner : [A'] ++ Γ ⇒ B := ldiv_invertible h
        have h_lt_inner : list_degree ([A'] ++ Γ) + tp_degree B < n := by
          have h_lt :
              list_degree ([A'] ++ Γ) + tp_degree B <
                list_degree Γ + tp_degree (A' ⧹ B) := by
            grind only [list_degree_traversible, list_degree, tp_degree]
          simpa [h_deg] using h_lt
        have h_inner_p : prove1 ([A'] ++ Γ) B :=
          ih _ h_lt_inner _ _ rfl h_inner
        unfold prove1
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨h_ne, h_inner_p⟩
    | rdiv B A' =>
        have h_ne : Γ ≠ [] := nonempty_premises h
        have h_inner : Γ ++ [A'] ⇒ B := rdiv_invertible h
        have h_lt_inner : list_degree (Γ ++ [A']) + tp_degree B < n := by
          have h_lt :
              list_degree (Γ ++ [A']) + tp_degree B <
                list_degree Γ + tp_degree (B ⧸ A') := by
            grind only [list_degree_traversible, list_degree, tp_degree]
          simpa [h_deg] using h_lt
        have h_inner_p : prove1 (Γ ++ [A']) B :=
          ih _ h_lt_inner _ _ rfl h_inner
        unfold prove1
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨h_ne, h_inner_p⟩
  exact h (list_degree Γ + tp_degree A) Γ A rfl

lemma prove1_iff_sequent : prove1 Γ A ↔ Γ ⇒ A := by
  constructor
  · exact prove1_sound
  · exact prove1_complete

theorem prove2_iff_sequent : prove2 Γ A ↔ Γ ⇒ A := by
  simpa [prove1_iff_prove2] using (prove1_iff_sequent (Γ:=Γ) (A:=A))

instance : Decidable (Γ ⇒ A) :=
  decidable_of_iff (prove2 Γ A) (prove2_iff_sequent (Γ:=Γ) (A:=A))

example : [ # "a" ⧸ # "b", # "b"] ⇒ (# "a") := by decide

end Mathling.Lambek.ProductFree
