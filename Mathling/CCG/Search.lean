import Mathlib.Data.Bool.Basic
import Mathling.CCG.Derivation

/-!
# The fuel-bounded backward recognizer

This module defines the computational search procedure used by the decision
procedure: list splitting helpers, the backward view `BackRule` of binary
rules, the one-step backward search combinators `unaryBack` / `binaryBack`, and
the fuel-bounded recognizer `recognizes` together with its decidable wrapper.

It also proves the structural characterization lemmas
(`unaryBack_eq_true_iff`, `recognizes_succ_eq_true_iff`) that the soundness and
completeness developments share, so that those proofs avoid re-running the same
case analyses.
-/

namespace Mathling.CCG

open Tp

/-! ## List splitting -/

/-- All splits of a list into a left and right part. -/
@[grind]
def splits {α : Type u} : List α → List (List α × List α)
  | [] => [([], [])]
  | x :: xs => ([], x :: xs) :: (splits xs).map (fun p => (x :: p.1, p.2))

/-- Every split returned by `splits` appends back to the original list. -/
@[grind =>]
theorem splits_append_eq {α : Type u} {xs : List α} {p : List α × List α}
    (h : p ∈ splits xs) :
    p.1 ++ p.2 = xs := by
  induction xs generalizing p <;> grind

/-- The displayed split `(left, right)` occurs among the splits of `left ++ right`. -/
@[grind .]
theorem splits_mem {α : Type u} (left right : List α) :
    (left, right) ∈ splits (left ++ right) := by
  induction left with
  | nil => cases right <;> grind
  | cons _ _ _  => grind

/-- Boolean non-emptiness, used to keep binary CCG premises nonempty. -/
@[grind]
def nonemptyList {α : Type u} : List α → Bool
  | [] => false
  | _ :: _ => true

/-- Appending to a nonempty list remains nonempty. -/
@[grind =>]
theorem nonemptyList_append_left {α : Type u} {left right : List α}
    (hleft : nonemptyList left = true) :
    nonemptyList (left ++ right) = true := by
  cases left <;> grind

/-- Every inductively derivable CCG sequent has a nonempty antecedent. -/
@[grind =>]
theorem derives_nonemptyList {Γ : List Tp} {A : Tp} (h : Γ ⇒ccg A) :
    nonemptyList Γ = true := by
  induction h <;> grind

/-- The proper splits of a list: both sides are nonempty. -/
@[grind]
def properSplits {α : Type u} (xs : List α) : List (List α × List α) :=
  (splits xs).filter (fun p => nonemptyList p.1 && nonemptyList p.2)

/-- A pair of nonempty lists occurs as a proper split of its concatenation. -/
@[grind =>]
theorem properSplits_mem {α : Type u} {left right : List α}
    (hleft : nonemptyList left = true) (hright : nonemptyList right = true) :
    (left, right) ∈ properSplits (left ++ right) := by
  grind

/-- Proper splits also append back to the original list. -/
@[grind =>]
theorem properSplits_append_eq {α : Type u} {xs : List α} {p : List α × List α}
    (h : p ∈ properSplits xs) :
    p.1 ++ p.2 = xs := by
  grind

/-- The left side of a proper split is nonempty. -/
@[grind =>]
theorem properSplits_left_nonempty {α : Type u} {xs : List α} {p : List α × List α}
    (h : p ∈ properSplits xs) :
    nonemptyList p.1 = true := by
  grind

/-- The right side of a proper split is nonempty. -/
@[grind =>]
theorem properSplits_right_nonempty {α : Type u} {xs : List α} {p : List α × List α}
    (h : p ∈ properSplits xs) :
    nonemptyList p.2 = true := by
  grind

/-! ## Backward view of binary rules -/

/-- A backward view of a binary rule: it records two premise categories whose
binary combination has conclusion `target`. -/
@[grind cases]
inductive BackRule : Tp → Type where
  | appRight (C B : Tp) : BackRule C
  | appLeft (A C : Tp) : BackRule C
  | compRight (C B A : Tp) : BackRule (C ⧸ A)
  | compLeft (A B C : Tp) : BackRule (A ⧹ C)
  | crossedRight (C B A : Tp) : BackRule (A ⧹ C)
  | crossedLeft (B A C : Tp) : BackRule (C ⧸ A)

namespace BackRule

/-- Left premise category of a backward binary-rule instance. -/
@[grind]
def left : {target : Tp} → BackRule target → Tp
  | _, appRight C B => C ⧸ B
  | _, appLeft A _C => A
  | _, compRight C B _A => C ⧸ B
  | _, compLeft A B _C => A ⧹ B
  | _, crossedRight C B _A => C ⧸ B
  | _, crossedLeft B A _C => B ⧸ A

/-- Right premise category of a backward binary-rule instance. -/
@[grind]
def right : {target : Tp} → BackRule target → Tp
  | _, appRight _C B => B
  | _, appLeft A C => A ⧹ C
  | _, compRight _C B A => B ⧸ A
  | _, compLeft _A B C => B ⧹ C
  | _, crossedRight _C B A => A ⧹ B
  | _, crossedLeft B _A C => B ⧹ C

/-- The actual binary rule witnessed by a backward binary-rule instance. -/
@[grind .]
theorem sound : {target : Tp} → (r : BackRule target) → BinaryRule r.left r.right target
  | _, appRight _C _B => BinaryRule.appRight
  | _, appLeft _A _C => BinaryRule.appLeft
  | _, compRight _C _B _A => BinaryRule.compRight
  | _, compLeft _A _B _C => BinaryRule.compLeft
  | _, crossedRight _C _B _A => BinaryRule.crossedRight
  | _, crossedLeft _B _A _C => BinaryRule.crossedLeft

end BackRule

/-- The finite set of backward binary-rule instances considered for a target.
The list `K` supplies the finitely many choices for the hidden middle category. -/
@[grind]
def backRules (K : List Tp) : (target : Tp) → List (BackRule target)
  | # name =>
      (K.map (fun B => BackRule.appRight (# name) B)) ++
      (K.map (fun A => BackRule.appLeft A (# name)))
  | C ⧸ A =>
      (K.map (fun B => BackRule.appRight (C ⧸ A) B)) ++
      (K.map (fun B => BackRule.appLeft B (C ⧸ A))) ++
      (K.map (fun B => BackRule.compRight C B A)) ++
      (K.map (fun B => BackRule.crossedLeft B A C))
  | A ⧹ C =>
      (K.map (fun B => BackRule.appRight (A ⧹ C) B)) ++
      (K.map (fun B => BackRule.appLeft B (A ⧹ C))) ++
      (K.map (fun B => BackRule.compLeft A B C)) ++
      (K.map (fun B => BackRule.crossedRight C B A))

/-- The recognizer contains the forward-application backward rule. -/
@[grind .]
theorem backRules_appRight_mem {K : List Tp} (hK : ∀ A : Tp, A ∈ K) (C B : Tp) :
    BackRule.appRight C B ∈ backRules K C := by
  cases C <;> grind

/-- The recognizer contains the backward-application backward rule. -/
@[grind .]
theorem backRules_appLeft_mem {K : List Tp} (hK : ∀ A : Tp, A ∈ K) (A C : Tp) :
    BackRule.appLeft A C ∈ backRules K C := by
  cases C <;> grind

/-- Every forward binary-rule instance has a matching backward-rule instance in
`backRules`, provided the finite candidate list contains the hidden category. -/
theorem backRules_complete {K : List Tp} (hK : ∀ A : Tp, A ∈ K) {A B C : Tp}
    (rule : BinaryRule A B C) :
    ∃ r ∈ backRules K C, r.left = A ∧ r.right = B := by
  cases rule 
  case appRight => exact ⟨.appRight C B, by grind, by grind⟩
  case appLeft => exact ⟨.appLeft A C, by grind, by grind⟩
  case compRight C B A => exact ⟨.compRight C B A, by grind, by grind⟩
  case compLeft A B C => exact ⟨.compLeft A B C, by grind, by grind⟩
  case crossedRight C B A => exact ⟨.crossedRight C B A, by grind, by grind⟩
  case crossedLeft B A C => exact ⟨.crossedLeft B A C, by grind, by grind⟩

grind_pattern backRules_complete => backRules K C, BinaryRule A B C

/-! ## One-step backward search -/

/-- Backward search for one unary type-raising step. -/
@[grind =]
def unaryBack (rec : List Tp → Tp → Bool) (Γ : List Tp) : Tp → Bool
  | C ⧸ (A ⧹ C') => if C = C' then rec Γ A else false
  | (C' ⧸ A) ⧹ C => if C' = C then rec Γ A else false
  | _ => false

/-- A successful unary backward step is exactly one of the two type-raising
inverses with a successful recursive premise.  This single characterization
drives both the soundness and the monotonicity proofs. -/
@[grind =]
theorem unaryBack_eq_true_iff (rec : List Tp → Tp → Bool) (Γ : List Tp) (T : Tp) :
    unaryBack rec Γ T = true ↔
      (∃ C A, T = C ⧸ (A ⧹ C) ∧ rec Γ A = true) ∨
      (∃ C A, T = (C ⧸ A) ⧹ C ∧ rec Γ A = true) := by
  unfold unaryBack
  grind

/-- Backward search for one binary rule step. -/
@[grind =]
def binaryBack (K : List Tp) (rec : List Tp → Tp → Bool) (Γ : List Tp) (A : Tp) : Bool :=
  (properSplits Γ).any (fun p =>
    (backRules K A).any (fun r => rec p.1 r.left && rec p.2 r.right))

/-- A successful binary backward step exposes a proper split and a backward rule
whose two premises both succeed recursively. -/
@[grind =]
theorem binaryBack_eq_true_iff (K : List Tp) (rec : List Tp → Tp → Bool)
    (Γ : List Tp) (A : Tp) :
    binaryBack K rec Γ A = true ↔
      ∃ p ∈ properSplits Γ, ∃ r ∈ backRules K A,
        rec p.1 r.left = true ∧ rec p.2 r.right = true := by
  grind [binaryBack]

/-! ## The fuel-bounded recognizer -/

/-- Fuel-bounded recognizer over a finite candidate set `K`.

`fuel` bounds the number of backward rule expansions.  The base case still
recognizes a leaf item, so increasing fuel monotonically extends the search in
practice. -/
@[grind =]
def recognizes (K : List Tp) : Nat → List Tp → Tp → Bool
  | 0, Γ, A => Γ == [A]
  | fuel + 1, Γ, A =>
      (Γ == [A]) || unaryBack (recognizes K fuel) Γ A ||
        binaryBack K (recognizes K fuel) Γ A

@[grind =]
theorem recognizes_zero (K : List Tp) (Γ : List Tp) (A : Tp) :
    recognizes K 0 Γ A = (Γ == [A]) := rfl

/-- A successful recognizer step is a leaf, a unary step, or a binary step.
This flattens the boolean disjunction shared by every step-level proof. -/
@[grind =]
theorem recognizes_succ_eq_true_iff (K : List Tp) (fuel : Nat) (Γ : List Tp) (A : Tp) :
    recognizes K (fuel + 1) Γ A = true ↔
      (Γ == [A]) = true ∨
      unaryBack (recognizes K fuel) Γ A = true ∨
      binaryBack K (recognizes K fuel) Γ A = true := by
  grind

/-! ## Decidable wrapper -/

/-- A finite bounded derivability proposition, represented by the recognizer. -/
@[grind =]
def BoundedDerivable (K : List Tp) (fuel : Nat) (Γ : List Tp) (A : Tp) : Prop :=
  recognizes K fuel Γ A = true

instance boundedDerivableDecidable (K : List Tp) (fuel : Nat) (Γ : List Tp) (A : Tp) :
    Decidable (BoundedDerivable K fuel Γ A) := by
  unfold BoundedDerivable
  infer_instance

/-- The decision function for bounded derivability. -/
@[grind =]
def decideBounded (K : List Tp) (fuel : Nat) (Γ : List Tp) (A : Tp) : Bool :=
  recognizes K fuel Γ A

@[grind =]
theorem decideBounded_eq (K : List Tp) (fuel : Nat) (Γ : List Tp) (A : Tp) :
    decideBounded K fuel Γ A = recognizes K fuel Γ A := rfl

/-- The decision function agrees with the bounded derivability proposition. -/
@[grind =]
theorem decideBounded_iff (K : List Tp) (fuel : Nat) (Γ : List Tp) (A : Tp) :
    decideBounded K fuel Γ A = true ↔ BoundedDerivable K fuel Γ A := Iff.rfl

end Mathling.CCG
