import lambek.Basic

namespace List

def decidableExists {α} (xs : List α) (p : α → Prop) [DecidablePred p] :
    Decidable (∃ x ∈ xs, p x) := by
  classical
  exact inferInstance

end List

namespace Lambek

def list_splits {α} : List α → List (List α × List α)
  | [] => [([], [])]
  | x :: xs => ([], x :: xs) :: (list_splits xs).map (fun (l, r) => (x :: l, r))

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
        have h' :
            (l, r) = ([], x :: xs) ∨
              (l, r) ∈ (list_splits xs).map (fun (l, r) => (x :: l, r)) := by
          simpa [list_splits] using h
        cases h' with
        | inl h0 =>
            cases h0
            simp
        | inr h0 =>
            rcases List.mem_map.mp h0 with ⟨pair, hpair, hEq⟩
            rcases pair with ⟨l1, r1⟩
            have hl : l = x :: l1 := by cases hEq; rfl
            have hr : r = r1 := by cases hEq; rfl
            have hxs : xs = l1 ++ r1 := (ih.mp hpair)
            calc
              x :: xs = x :: (l1 ++ r1) := by simp [hxs]
              _ = (x :: l1) ++ r1 := by simp
              _ = l ++ r := by simp [hl, hr]
      · intro h
        have h' := (List.cons_eq_append_iff (x := x) (cs := xs) (as := l) (bs := r)).mp h
        cases h' with
        | inl h0 =>
            rcases h0 with ⟨hl, hr⟩
            subst hl
            subst hr
            simp [list_splits]
        | inr h0 =>
            rcases h0 with ⟨l', hl, hr⟩
            subst hl
            have hmem : (l', r) ∈ list_splits xs := (ih.mpr hr)
            have hmem' :
                (x :: l', r) ∈ (list_splits xs).map (fun (l, r) => (x :: l, r)) :=
              List.mem_map.mpr ⟨(l', r), hmem, rfl⟩
            simpa [list_splits] using hmem'

def picks {α} : List α → List (List α × α × List α)
  | [] => []
  | x :: xs => ([], x, xs) :: (picks xs).map (fun (l, a, r) => (x :: l, a, r))

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
        have h' :
            (l, x, r) = ([], y, ys) ∨
              (l, x, r) ∈ (picks ys).map (fun (l, a, r) => (y :: l, a, r)) := by
          simpa [picks] using h
        cases h' with
        | inl h0 =>
            cases h0
            simp
        | inr h0 =>
            rcases List.mem_map.mp h0 with ⟨triple, htriple, hEq⟩
            rcases triple with ⟨l1, a1, r1⟩
            have hl : l = y :: l1 := by cases hEq; rfl
            have hx : x = a1 := by cases hEq; rfl
            have hr : r = r1 := by cases hEq; rfl
            have htriple' : (l1, x, r1) ∈ picks ys := by
              simpa [hx] using htriple
            have hys : ys = l1 ++ x :: r1 := (ih.mp htriple')
            calc
              y :: ys = y :: (l1 ++ x :: r1) := by simp [hys]
              _ = (y :: l1) ++ x :: r1 := by simp
              _ = l ++ x :: r := by simp [hl, hr]
      · intro h
        have h' := (List.cons_eq_append_iff (x := y) (cs := ys) (as := l) (bs := x :: r)).mp h
        cases h' with
        | inl h0 =>
            rcases h0 with ⟨hl, hr⟩
            subst hl
            have : x = y ∧ r = ys := by
              simpa using hr
            rcases this with ⟨hx, hr'⟩
            subst hx
            subst hr'
            simp [picks]
        | inr h0 =>
            rcases h0 with ⟨l', hl, hr⟩
            subst hl
            have hmem : (l', x, r) ∈ picks ys := (ih.mpr hr)
            have hmem' :
                (y :: l', x, r) ∈ (picks ys).map (fun (l, a, r) => (y :: l, a, r)) :=
              List.mem_map.mpr ⟨(l', x, r), hmem, rfl⟩
            simpa [picks] using hmem'

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

def rdiv_candidates (Γ : List Tp) : List RDivCand :=
  (picks Γ).flatMap (fun (left, f, right) =>
    match f with
    | B ⧸ A =>
        (list_splits right).map (fun (Δ, Λ) => ⟨left, B, A, Δ, Λ⟩)
    | _ => [])

def ldiv_candidates (Γ : List Tp) : List LDivCand :=
  (picks Γ).flatMap (fun (left, f, right) =>
    match f with
    | A ⧹ B =>
        (list_splits left).map (fun (Γ0, Δ) => ⟨Γ0, A, B, Δ, right⟩)
    | _ => [])

lemma measure_rdiv_right {Γ : List Tp} {A B : Tp} :
    list_degree (Γ ++ [A]) + tp_degree B <
      list_degree Γ + tp_degree (B ⧸ A) := by
  have hleft :
      list_degree (Γ ++ [A]) + tp_degree B =
        list_degree Γ + tp_degree A + tp_degree B := by
    simp [list_degree_traversible, list_degree, Nat.add_assoc]
  have hright :
      list_degree Γ + tp_degree (B ⧸ A) =
        list_degree Γ + tp_degree A + tp_degree B + 1 := by
    simp [tp_degree, Nat.add_assoc, Nat.add_comm]
  calc
    list_degree (Γ ++ [A]) + tp_degree B
        = list_degree Γ + tp_degree A + tp_degree B := hleft
    _ < list_degree Γ + tp_degree A + tp_degree B + 1 := by
        exact Nat.lt_succ_self _
    _ = list_degree Γ + tp_degree (B ⧸ A) := by
        simpa [Nat.add_assoc, Nat.add_comm] using hright.symm

lemma measure_ldiv_right {Γ : List Tp} {A B : Tp} :
    list_degree ([A] ++ Γ) + tp_degree B <
      list_degree Γ + tp_degree (A ⧹ B) := by
  have hleft :
      list_degree ([A] ++ Γ) + tp_degree B =
        list_degree Γ + tp_degree A + tp_degree B := by
    simp [list_degree, Nat.add_assoc, Nat.add_comm]
  have hright :
      list_degree Γ + tp_degree (A ⧹ B) =
        list_degree Γ + tp_degree A + tp_degree B + 1 := by
    simp [tp_degree, Nat.add_assoc]
  calc
    list_degree ([A] ++ Γ) + tp_degree B
        = list_degree Γ + tp_degree A + tp_degree B := hleft
    _ < list_degree Γ + tp_degree A + tp_degree B + 1 := by
        exact Nat.lt_succ_self _
    _ = list_degree Γ + tp_degree (A ⧹ B) := by
        simpa [Nat.add_assoc, Nat.add_comm] using hright.symm

lemma rdiv_candidates_spec {Γ : List Tp} {cand : RDivCand} :
    cand ∈ rdiv_candidates Γ ↔
      Γ = cand.left ++ [cand.B ⧸ cand.A] ++ cand.Δ ++ cand.Λ := by
  cases cand with
  | mk left B A Δ Λ =>
      constructor
      · intro h
        rcases List.mem_flatMap.mp h with ⟨triple, htriple, hmem⟩
        rcases triple with ⟨left', f, right⟩
        have hsplit : Γ = left' ++ f :: right := (mem_picks_iff).1 htriple
        cases f with
        | atom name => cases hmem
        | ldiv A' B' => cases hmem
        | rdiv B' A' =>
            rcases List.mem_map.mp hmem with ⟨pair, hpair, hEq⟩
            rcases pair with ⟨Δ1, Λ1⟩
            have hright : right = Δ1 ++ Λ1 := (mem_list_splits_iff).1 hpair
            have hleft' : left = left' := by cases hEq; rfl
            have hB' : B = B' := by cases hEq; rfl
            have hA' : A = A' := by cases hEq; rfl
            have hΔ' : Δ = Δ1 := by cases hEq; rfl
            have hΛ' : Λ = Λ1 := by cases hEq; rfl
            simp [hsplit, hright, hleft', hB', hA', hΔ', hΛ', List.append_assoc]
      · intro h
        apply List.mem_flatMap.mpr
        refine ⟨(left, B ⧸ A, Δ ++ Λ), ?_, ?_⟩
        · apply (mem_picks_iff).2
          simpa [List.append_assoc] using h
        · apply List.mem_map.mpr
          refine ⟨(Δ, Λ), ?_, rfl⟩
          apply (mem_list_splits_iff).2
          rfl

lemma ldiv_candidates_spec {Γ : List Tp} {cand : LDivCand} :
    cand ∈ ldiv_candidates Γ ↔
      Γ = cand.left ++ cand.Δ ++ [cand.A ⧹ cand.B] ++ cand.Λ := by
  cases cand with
  | mk left A B Δ Λ =>
      constructor
      · intro h
        rcases List.mem_flatMap.mp h with ⟨triple, htriple, hmem⟩
        rcases triple with ⟨left', f, right⟩
        have hsplit : Γ = left' ++ f :: right := (mem_picks_iff).1 htriple
        cases f with
        | atom name => cases hmem
        | rdiv B' A' => cases hmem
        | ldiv A' B' =>
            rcases List.mem_map.mp hmem with ⟨pair, hpair, hEq⟩
            rcases pair with ⟨left0, Δ0⟩
            have hleft : left' = left0 ++ Δ0 := (mem_list_splits_iff).1 hpair
            have hleft' : left = left0 := by cases hEq; rfl
            have hA' : A = A' := by cases hEq; rfl
            have hB' : B = B' := by cases hEq; rfl
            have hΔ' : Δ = Δ0 := by cases hEq; rfl
            have hΛ' : Λ = right := by cases hEq; rfl
            simp [hsplit, hleft, hleft', hA', hB', hΔ', hΛ', List.append_assoc]
      · intro h
        apply List.mem_flatMap.mpr
        refine ⟨(left ++ Δ, A ⧹ B, Λ), ?_, ?_⟩
        · apply (mem_picks_iff).2
          simp [List.append_assoc, h]
        · apply List.mem_map.mpr
          refine ⟨(left, Δ), ?_, rfl⟩
          apply (mem_list_splits_iff).2
          rfl

noncomputable def derive (Γ : List Tp) (A : Tp) : Decidable (Γ ⇒ A) := by
  classical
  cases A with
  | atom s =>
      by_cases hax : Γ = [Tp.atom s]
      · subst hax
        exact isTrue Derive.ax
      · let rdiv_pred : RDivCand → Prop := fun cand =>
          (cand.Δ ⇒ cand.A) ∧ ((cand.left ++ [cand.B] ++ cand.Λ) ⇒ Tp.atom s)
        haveI : DecidablePred rdiv_pred := by
          intro cand
          classical
          exact inferInstance
        cases (List.decidableExists (rdiv_candidates Γ) rdiv_pred) with
        | isTrue h =>
            classical
            have hcand : ∃ cand, cand ∈ rdiv_candidates Γ ∧ rdiv_pred cand := h
            let cand := Classical.choose hcand
            have hspec : cand ∈ rdiv_candidates Γ ∧ rdiv_pred cand :=
              Classical.choose_spec hcand
            have hctx :
                Γ = cand.left ++ [cand.B ⧸ cand.A] ++ cand.Δ ++ cand.Λ :=
              (rdiv_candidates_spec).1 hspec.1
            have d :
                cand.left ++ [cand.B ⧸ cand.A] ++ cand.Δ ++ cand.Λ ⇒ Tp.atom s :=
              Derive.rdiv_l hspec.2.1 hspec.2.2
            exact isTrue (by simpa [hctx] using d)
        | isFalse h_rdiv =>
            let ldiv_pred : LDivCand → Prop := fun cand =>
              (cand.Δ ⇒ cand.A) ∧ ((cand.left ++ [cand.B] ++ cand.Λ) ⇒ Tp.atom s)
            haveI : DecidablePred ldiv_pred := by
              intro cand
              classical
              exact inferInstance
            cases (List.decidableExists (ldiv_candidates Γ) ldiv_pred) with
            | isTrue h =>
                classical
                have hcand : ∃ cand, cand ∈ ldiv_candidates Γ ∧ ldiv_pred cand := h
                let cand := Classical.choose hcand
                have hspec : cand ∈ ldiv_candidates Γ ∧ ldiv_pred cand :=
                  Classical.choose_spec hcand
                have hctx :
                    Γ = cand.left ++ cand.Δ ++ [cand.A ⧹ cand.B] ++ cand.Λ :=
                  (ldiv_candidates_spec).1 hspec.1
                have d :
                    cand.left ++ cand.Δ ++ [cand.A ⧹ cand.B] ++ cand.Λ ⇒ Tp.atom s :=
                  Derive.ldiv_l hspec.2.1 hspec.2.2
                exact isTrue (by simpa [hctx] using d)
            | isFalse h_ldiv =>
                exact isFalse (by
                  intro hder
                  cases hder
                  case ax =>
                    exact hax rfl
                  case rdiv_l Δ A Γ_left B Λ d_arg d_main =>
                    let cand : RDivCand := ⟨Γ_left, B, A, Δ, Λ⟩
                    have hmem :
                        cand ∈ rdiv_candidates (Γ_left ++ [B ⧸ A] ++ Δ ++ Λ) := by
                      apply (rdiv_candidates_spec).2
                      simp [cand, List.append_assoc]
                    exact h_rdiv ⟨cand, hmem, ⟨d_arg, d_main⟩⟩
                  case ldiv_l Δ A Γ_left B Λ d_arg d_main =>
                    let cand : LDivCand := ⟨Γ_left, A, B, Δ, Λ⟩
                    have hmem :
                        cand ∈ ldiv_candidates (Γ_left ++ Δ ++ [A ⧹ B] ++ Λ) := by
                      apply (ldiv_candidates_spec).2
                      simp [cand, List.append_assoc]
                    exact h_ldiv ⟨cand, hmem, ⟨d_arg, d_main⟩⟩)
  | ldiv A B =>
      by_cases hΓ : Γ = []
      · subst hΓ
        exact isFalse (by
          intro h
          exact (nonempty_premises h) rfl)
      · cases derive ([A] ++ Γ) B with
        | isTrue h =>
            exact isTrue (Derive.ldiv_r hΓ h)
        | isFalse h =>
            exact isFalse (by
              intro hder
              exact h (ldiv_invertible hder))
  | rdiv B A =>
      by_cases hΓ : Γ = []
      · subst hΓ
        exact isFalse (by
          intro h
          exact (nonempty_premises h) rfl)
      · cases derive (Γ ++ [A]) B with
        | isTrue h =>
            exact isTrue (Derive.rdiv_r hΓ h)
        | isFalse h =>
            exact isFalse (by
              intro hder
              exact h (rdiv_invertible hder))
termination_by
  list_degree Γ + tp_degree A
decreasing_by
  all_goals
    first
    | exact (measure_ldiv_right (Γ := Γ) (A := A) (B := B))
    | exact (measure_rdiv_right (Γ := Γ) (A := A) (B := B))

end Lambek
