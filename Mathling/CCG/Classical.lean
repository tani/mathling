import Mathling.CCG.Basic
import Lean.LibrarySuggestions.Default

namespace Classical

@[grind cases]
inductive Derives : List Category → Category → Prop where
  | word (u : Category) :
    Derives [u] u
  | applyFoward :
    Derives l (v / u) →
    Derives r u →
    Derives (l ++ r) v
  | applyBackward :
    Derives l u →
    Derives r (u \ v) →
    Derives (l ++ r) v

@[grind]
def apply (l r : Category) : List Category :=
  (match l with
  | .forward v u => if u == r then [v] else []
  | _ => []) ++
  (match r with
  | .backward u v => if l == u then [v] else []
  | _ => [])

@[grind]
def apply' (l r : List Category) : List Category :=
  l.flatMap <| r.flatMap ∘ apply

@[grind]
def parse : List Category → List Category
| [] => []
| [x] => [x]
| xs =>
  List.finRange (xs.length - 1)
  |>.flatMap (fun i =>
    let n := i.1 + 1
    let l := parse (xs.take n)
    let r := parse (xs.drop n)
    apply' l r)
  termination_by xs => xs.length
  decreasing_by
    · have hsplit : i.1 + 1 < xs.length := (Nat.lt_sub_iff_add_lt).mp i.2
      rw [List.length_take]
      exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) hsplit
    · have hsplit : i.1 + 1 < xs.length := (Nat.lt_sub_iff_add_lt).mp i.2
      rw [List.length_drop]
      exact Nat.sub_lt (Nat.lt_trans (Nat.succ_pos i.1) hsplit) (Nat.succ_pos i.1)

@[grind]
def parse' (Γ : List Category) (A : Category) : Bool :=
  (parse Γ).contains A

@[grind =>]
theorem apply_sound {B C A : Category} (h : A ∈ apply B C) :
    (∃ u, B = A / u ∧ C = u) ∨ (∃ u, B = u ∧ C = u \ A) := by
  cases B <;> cases C <;> simp [apply] at h ⊢ <;> grind

@[grind .]
theorem apply_forward_mem (v u : Category) : v ∈ apply (v / u) u := by
  simp [apply]

@[grind .]
theorem apply_backward_mem (v u : Category) : v ∈ apply u (u \ v) := by
  simp [apply]

theorem apply'_sound {l r : List Category} {A : Category}
    (h : A ∈ apply' l r) :
    ∃ B C, B ∈ l ∧ C ∈ r ∧ A ∈ apply B C := by
  rw [apply'] at h
  rw [List.mem_flatMap] at h
  rcases h with ⟨B, hB, h⟩
  rw [Function.comp_apply, List.mem_flatMap] at h
  rcases h with ⟨C, hC, hA⟩
  exact ⟨B, C, hB, hC, hA⟩

theorem apply'_forward_mem {l r : List Category} {v u : Category}
    (hl : v / u ∈ l) (hr : u ∈ r) :
    v ∈ apply' l r := by
  rw [apply']
  refine (List.mem_flatMap).mpr ⟨v / u, hl, ?_⟩
  change v ∈ (r.flatMap ∘ apply) (v / u)
  rw [Function.comp_apply]
  exact (List.mem_flatMap).mpr ⟨u, hr, apply_forward_mem v u⟩

theorem apply'_backward_mem {l r : List Category} {v u : Category}
    (hl : u ∈ l) (hr : u \ v ∈ r) :
    v ∈ apply' l r := by
  rw [apply']
  refine (List.mem_flatMap).mpr ⟨u, hl, ?_⟩
  change v ∈ (r.flatMap ∘ apply) u
  rw [Function.comp_apply]
  exact (List.mem_flatMap).mpr ⟨u \ v, hr, apply_backward_mem v u⟩

theorem parse_sound_mem {Γ : List Category} {A : Category}
    (h : A ∈ parse Γ) : Derives Γ A := by
  revert A
  induction Γ using parse.induct with
  | case1 =>
      intro A h
      simp [parse] at h
  | case2 x =>
      intro A h
      simp [parse] at h
      subst A
      exact Derives.word x
  | case3 xs hnil hsingle ihTake ihDrop =>
      intro A h
      have hparse :
          parse xs =
            List.flatMap
              (fun i =>
                let n := i.1 + 1
                let left := parse (xs.take n)
                let right := parse (xs.drop n)
                apply' left right)
              (List.finRange (xs.length - 1)) := by
        simp [parse]
      rw [hparse] at h
      rcases (List.mem_flatMap.mp h) with ⟨i, _, hA⟩
      rcases apply'_sound hA with ⟨B, C, hB, hC, hApp⟩
      have dB : Derives (xs.take (i.1 + 1)) B := ihTake i hB
      have dC : Derives (xs.drop (i.1 + 1)) C := ihDrop i hC
      rcases apply_sound hApp with ⟨u, hB_eq, hC_eq⟩ | ⟨u, hB_eq, hC_eq⟩
      · have d : Derives (xs.take (i.1 + 1) ++ xs.drop (i.1 + 1)) A :=
          Derives.applyFoward
            (by simpa [hB_eq] using dB)
            (by simpa [hC_eq] using dC)
        simpa [List.take_append_drop] using d
      · have d : Derives (xs.take (i.1 + 1) ++ xs.drop (i.1 + 1)) A :=
          Derives.applyBackward
            (by simpa [hB_eq] using dB)
            (by simpa [hC_eq] using dC)
        simpa [List.take_append_drop] using d

theorem derives_length_pos {Γ : List Category} {A : Category}
    (h : Derives Γ A) : 0 < Γ.length := by
  induction h with
  | word u =>
      simp
  | applyFoward hLeft hRight ihLeft ihRight =>
      rw [List.length_append]
      exact Nat.add_pos_left ihLeft _
  | applyBackward hLeft hRight ihLeft ihRight =>
      rw [List.length_append]
      exact Nat.add_pos_left ihLeft _

theorem mem_parse_append_of_apply' {l r : List Category} {A : Category}
    (hl : 0 < l.length) (hr : 0 < r.length)
    (happ : A ∈ apply' (parse l) (parse r)) :
    A ∈ parse (l ++ r) := by
  have hnotnil : l ++ r = [] → False := by
    intro h
    have hlen : (l ++ r).length = 0 := by
      simpa using congrArg List.length h
    have hpos : 0 < (l ++ r).length := by
      rw [List.length_append]
      exact Nat.add_pos_left hl _
    exact (Nat.ne_of_gt hpos) hlen
  have hnotsingle : ∀ x, l ++ r = [x] → False := by
    intro x h
    have hlen : (l ++ r).length = 1 := by
      simpa using congrArg List.length h
    have hl1 : 1 ≤ l.length := Nat.succ_le_of_lt hl
    have hr1 : 1 ≤ r.length := Nat.succ_le_of_lt hr
    have hlen_gt : 1 < (l ++ r).length := by
      rw [List.length_append]
      exact Nat.lt_of_lt_of_le (by decide : 1 < 1 + 1) (Nat.add_le_add hl1 hr1)
    exact (Nat.ne_of_gt hlen_gt) hlen
  have hl1 : 1 ≤ l.length := Nat.succ_le_of_lt hl
  let i : Fin ((l ++ r).length - 1) :=
    ⟨l.length - 1, by
      rw [List.length_append]
      exact Nat.sub_lt_sub_right hl1 (Nat.lt_add_of_pos_right hr)⟩
  have hn : i.1 + 1 = l.length := by
    dsimp [i]
    exact Nat.sub_add_cancel hl1
  have htake : (l ++ r).take (i.1 + 1) = l := by
    simp [hn]
  have hdrop : (l ++ r).drop (i.1 + 1) = r := by
    simp [hn]
  have hmem :
      A ∈ List.flatMap
        (fun i =>
          let n := i.1 + 1
          let left := parse ((l ++ r).take n)
          let right := parse ((l ++ r).drop n)
          apply' left right)
        (List.finRange ((l ++ r).length - 1)) := by
    refine (List.mem_flatMap).mpr ⟨i, List.mem_finRange i, ?_⟩
    simpa [htake, hdrop] using happ
  simpa [parse, hnotnil, hnotsingle] using hmem

theorem parse_complete_mem {Γ : List Category} {A : Category}
    (h : Derives Γ A) : A ∈ parse Γ := by
  induction h with
  | word u =>
      simp [parse]
  | applyFoward hLeft hRight ihLeft ihRight =>
      exact mem_parse_append_of_apply'
        (derives_length_pos hLeft)
        (derives_length_pos hRight)
        (apply'_forward_mem ihLeft ihRight)
  | applyBackward hLeft hRight ihLeft ihRight =>
      exact mem_parse_append_of_apply'
        (derives_length_pos hLeft)
        (derives_length_pos hRight)
        (apply'_backward_mem ihLeft ihRight)

theorem parse_sound : parse' Γ A → Derives Γ A := by
  intro h
  exact parse_sound_mem ((List.contains_iff_mem).mp (by simpa [parse'] using h))

theorem parse_complete : Derives Γ A → parse' Γ A := by
  intro h
  simpa [parse'] using (List.contains_iff_mem).mpr (parse_complete_mem h)

theorem parse_iff_derives : parse' Γ A ↔ Derives Γ A := by
  constructor
  · exact parse_sound
  · exact parse_complete

instance : Decidable (Derives Γ A) :=
  decidable_of_iff (parse' Γ A) parse_iff_derives

end Classical
