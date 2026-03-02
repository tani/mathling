import Mathling.CCG.Ccg

universe u

variable {α : Type u} [DecidableEq α]

def Cat.dir_count {α : Type u}
  | Atom (_ : α) => 0
  | Fun _ b c => 1 + Cat.dir_count b + Cat.dir_count c

theorem af_apply_dir_count (x y z : Cat α) (h : some z = a_comb_f x y) :
    Cat.dir_count z + Cat.dir_count y + 1 = Cat.dir_count x := by
  cases x with
  | Atom _ =>
      cases y <;> cases h
  | Fun dir a b =>
      cases dir with
      | Fwd =>
          by_cases hb : b = y
          · subst hb
            have hz : z = a := by
              simpa [a_comb_f] using h
            subst hz
            simp [Cat.dir_count, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
          · have h' : False := by
              simpa [a_comb_f, hb] using h
            cases h'
      | Bwd =>
          cases h

theorem ab_apply_dir_count (x y z : Cat α) (h : some z = a_comb_b x y) :
    Cat.dir_count z + Cat.dir_count x + 1 = Cat.dir_count y := by
  cases y with
  | Atom _ =>
      cases h
  | Fun dir a b =>
      cases dir with
      | Fwd =>
          cases h
      | Bwd =>
          by_cases hb : b = x
          · subst hb
            have hz : z = a := by
              simpa [a_comb_b] using h
            subst hz
            simp [Cat.dir_count, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
          · have h' : False := by
              simpa [a_comb_b, hb] using h
            cases h'

theorem b_apply_dir_count (x y z : Cat α) (h : some z = b_comb x y) :
    Cat.dir_count x + Cat.dir_count y > Cat.dir_count z := by
  cases x with
  | Atom _ => cases y <;> cases h
  | Fun dir a b =>
      cases y with
      | Atom _ => simp [b_comb] at h
      | Fun dir' b' c =>
          cases dir with
          | Fwd =>
              cases dir' with
              | Bwd => cases h
              | Fwd =>
                  by_cases hb : b = b'
                  · subst hb
                    have hz : z = .Fun .Fwd a c := by simpa [b_comb] using h
                    subst hz
                    simp [Cat.dir_count]
                    omega
                  · have : False := by simpa [b_comb, hb] using h
                    cases this
          | Bwd =>
              cases dir' with
              | Fwd => cases h
              | Bwd =>
                  by_cases hb : b = b'
                  · subst hb
                    have hz : z = .Fun .Bwd a c := by simpa [b_comb] using h
                    subst hz
                    simp [Cat.dir_count]
                    omega
                  · have : False := by simpa [b_comb, hb] using h
                    cases this

omit [DecidableEq α] in
theorem tf_apply_dir_count (x y : Cat α) :
    Cat.dir_count y + 2 * Cat.dir_count x + 2 = Cat.dir_count (t_comb_f x y) := by
  dsimp [t_comb_f]
  dsimp [Cat.dir_count]
  grind

omit [DecidableEq α] in
theorem tb_apply_dir_count (x y : Cat α) :
    Cat.dir_count y + 2 * Cat.dir_count x + 2 <= Cat.dir_count (t_comb_b x y) := by
  dsimp [t_comb_b]
  dsimp [Cat.dir_count]
  grind
