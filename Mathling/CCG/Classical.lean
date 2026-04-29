import Mathling.CCG.Basic

namespace Classical

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

def apply : Category → Category → List Category
| .forward v u, w             => if u == w then [v] else []
| u           , .backward w v => if u == w then [v] else []
| _           , _             => []

def apply' (l r : List Category) : List Category :=
  l.flatMap <| r.flatMap ∘ apply

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

end Classical
