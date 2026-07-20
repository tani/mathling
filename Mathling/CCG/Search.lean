module

public import Mathlib.Data.Bool.Basic
public import Mathling.CCG.Derivation

@[expose] public section

/-!
# The fuel-bounded backward recognizer

This module defines the computational search procedure used by the decision
procedure: list splitting helpers, the backward view `ReverseRule` of binary
rules, the one-step backward search combinators `tryUnaryStep` / `tryBinaryStep`, and
the fuel-bounded recognizer `recognize` together with its decidable wrapper.

It also proves the structural characterization lemmas
(`tryUnaryStep_eq_true_iff`, `recognize_succ_eq_true_iff`) that the soundness and
completeness developments share, so that those proofs avoid re-running the same
case analyses.
-/

set_option linter.style.longLine false

namespace Mathling.CCG

open Category

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
def isNonemptyList {α : Type u} : List α → Bool
  | [] => false
  | _ :: _ => true

/-- Appending to a nonempty list remains nonempty. -/
@[grind =>]
theorem isNonemptyList_append_left {α : Type u} {left right : List α}
    (hleft : isNonemptyList left = true) :
    isNonemptyList (left ++ right) = true := by
  cases left <;> grind

/-- Every inductively derivable CCG sequent has a nonempty antecedent. -/
@[grind =>]
theorem derives_isNonemptyList {Γ : List Category} {A : Category} (h : Γ ⇒ccg A) :
    isNonemptyList Γ = true := by
  induction h <;> grind

/-- The proper splits of a list: both sides are nonempty. -/
@[grind]
def nonemptySplits {α : Type u} (xs : List α) : List (List α × List α) :=
  (splits xs).filter (fun p => isNonemptyList p.1 && isNonemptyList p.2)

/-- A pair of nonempty lists occurs as a proper split of its concatenation. -/
@[grind =>]
theorem nonemptySplits_mem {α : Type u} {left right : List α}
    (hleft : isNonemptyList left = true) (hright : isNonemptyList right = true) :
    (left, right) ∈ nonemptySplits (left ++ right) := by
  grind

/-- Proper splits also append back to the original list. -/
@[grind =>]
theorem nonemptySplits_append_eq {α : Type u} {xs : List α} {p : List α × List α}
    (h : p ∈ nonemptySplits xs) :
    p.1 ++ p.2 = xs := by
  grind

/-- The left side of a proper split is nonempty. -/
@[grind =>]
theorem nonemptySplits_left_nonempty {α : Type u} {xs : List α} {p : List α × List α}
    (h : p ∈ nonemptySplits xs) :
    isNonemptyList p.1 = true := by
  grind

/-- The right side of a proper split is nonempty. -/
@[grind =>]
theorem nonemptySplits_right_nonempty {α : Type u} {xs : List α} {p : List α × List α}
    (h : p ∈ nonemptySplits xs) :
    isNonemptyList p.2 = true := by
  grind

/-! ## Backward view of binary rules -/

/-- A backward view of a binary rule: it records two premise categories whose
binary combination has conclusion `target`. -/
@[grind cases]
inductive ReverseRule : Category → Type where
  | appRight (C B : Category) : ReverseRule C
  | appLeft (A C : Category) : ReverseRule C
  | compRight (C B A : Category) : ReverseRule (C ⧸ A)
  | compLeft (A B C : Category) : ReverseRule (A ⧹ C)
  | crossedRight (C B A : Category) : ReverseRule (A ⧹ C)
  | crossedLeft (B A C : Category) : ReverseRule (C ⧸ A)

namespace ReverseRule

/-- Left premise category of a backward binary-rule instance. -/
@[grind]
def left : {target : Category} → ReverseRule target → Category
  | _, appRight C B => C ⧸ B
  | _, appLeft A _C => A
  | _, compRight C B _A => C ⧸ B
  | _, compLeft A B _C => A ⧹ B
  | _, crossedRight C B _A => C ⧸ B
  | _, crossedLeft B A _C => B ⧸ A

/-- Right premise category of a backward binary-rule instance. -/
@[grind]
def right : {target : Category} → ReverseRule target → Category
  | _, appRight _C B => B
  | _, appLeft A C => A ⧹ C
  | _, compRight _C B A => B ⧸ A
  | _, compLeft _A B C => B ⧹ C
  | _, crossedRight _C B A => A ⧹ B
  | _, crossedLeft B _A C => B ⧹ C

/-- The actual binary rule witnessed by a backward binary-rule instance. -/
@[grind .]
theorem sound : {target : Category} → (r : ReverseRule target) → Rule r.left r.right target
  | _, appRight _C _B => Rule.appRight
  | _, appLeft _A _C => Rule.appLeft
  | _, compRight _C _B _A => Rule.compRight
  | _, compLeft _A _B _C => Rule.compLeft
  | _, crossedRight _C _B _A => Rule.crossedRight
  | _, crossedLeft _B _A _C => Rule.crossedLeft

end ReverseRule

/-- The finite set of backward binary-rule instances considered for a target.
The list `K` supplies the finitely many choices for the hidden middle category. -/
@[grind]
def reverseRules (K : List Category) : (target : Category) → List (ReverseRule target)
  | # name =>
      (K.map (fun B => ReverseRule.appRight (# name) B)) ++
      (K.map (fun A => ReverseRule.appLeft A (# name)))
  | C ⧸ A =>
      (K.map (fun B => ReverseRule.appRight (C ⧸ A) B)) ++
      (K.map (fun B => ReverseRule.appLeft B (C ⧸ A))) ++
      (K.map (fun B => ReverseRule.compRight C B A)) ++
      (K.map (fun B => ReverseRule.crossedLeft B A C))
  | A ⧹ C =>
      (K.map (fun B => ReverseRule.appRight (A ⧹ C) B)) ++
      (K.map (fun B => ReverseRule.appLeft B (A ⧹ C))) ++
      (K.map (fun B => ReverseRule.compLeft A B C)) ++
      (K.map (fun B => ReverseRule.crossedRight C B A))

/-- The recognizer contains the forward-application backward rule. -/
@[grind .]
theorem reverseRules_appRight_mem {K : List Category} (hK : ∀ A : Category, A ∈ K) (C B : Category) :
    ReverseRule.appRight C B ∈ reverseRules K C := by
  cases C <;> grind

/-- The recognizer contains the displayed forward-application backward rule
when its hidden argument category is in the candidate list. -/
@[grind .]
theorem reverseRules_appRight_mem_of_mem {K : List Category} {B : Category} (hB : B ∈ K) (C : Category) :
    ReverseRule.appRight C B ∈ reverseRules K C := by
  cases C <;> grind

/-- The recognizer contains the backward-application backward rule. -/
@[grind .]
theorem reverseRules_appLeft_mem {K : List Category} (hK : ∀ A : Category, A ∈ K) (A C : Category) :
    ReverseRule.appLeft A C ∈ reverseRules K C := by
  cases C <;> grind

/-- The recognizer contains the displayed backward-application backward rule
when its hidden argument category is in the candidate list. -/
@[grind .]
theorem reverseRules_appLeft_mem_of_mem {K : List Category} {A : Category} (hA : A ∈ K) (C : Category) :
    ReverseRule.appLeft A C ∈ reverseRules K C := by
  cases C <;> grind

/-- Every forward binary-rule instance has a matching backward-rule instance in
`reverseRules`, provided the finite candidate list contains the hidden category. -/
theorem reverseRules_complete {K : List Category} (hK : ∀ A : Category, A ∈ K) {A B C : Category}
    (rule : Rule A B C) :
    ∃ r ∈ reverseRules K C, r.left = A ∧ r.right = B := by
  cases rule 
  case appRight => exact ⟨.appRight C B, by grind, by grind⟩
  case appLeft => exact ⟨.appLeft A C, by grind, by grind⟩
  case compRight C B A => exact ⟨.compRight C B A, by grind, by grind⟩
  case compLeft A B C => exact ⟨.compLeft A B C, by grind, by grind⟩
  case crossedRight C B A => exact ⟨.crossedRight C B A, by grind, by grind⟩
  case crossedLeft B A C => exact ⟨.crossedLeft B A C, by grind, by grind⟩

grind_pattern reverseRules_complete => reverseRules K C, Rule A B C

/-- Every finite-candidate-aware forward binary-rule instance has a matching
backward-rule instance in `reverseRules`.  Unlike `reverseRules_complete`, this only
uses membership of the actual schematic metavariables, not the impossible
assumption that a finite list contains every category. -/
@[grind =>]
theorem reverseRules_complete_of_ruleIn {K : List Category} {A B C : Category}
    (rule : ChartRule K A B C) :
    ∃ r ∈ reverseRules K C, r.left = A ∧ r.right = B := by
  cases rule
  case appRight hC hB hLeft =>
    exact ⟨.appRight C B, by apply reverseRules_appRight_mem_of_mem hC, by grind⟩
  case appLeft hA hC hRight =>
    exact ⟨.appLeft A C, by apply reverseRules_appLeft_mem_of_mem hA, by grind⟩
  case compRight C B A hC hB hA hLeft hRight hOut =>
    exact ⟨.compRight C B A, by grind [reverseRules], by grind⟩
  case compLeft A B C hA hB hC hLeft hRight hOut =>
    exact ⟨.compLeft A B C, by grind [reverseRules], by grind⟩
  case crossedRight C B A hC hB hA hLeft hRight hOut =>
    exact ⟨.crossedRight C B A, by grind [reverseRules], by grind⟩
  case crossedLeft B A C hB hA hC hLeft hRight hOut =>
    exact ⟨.crossedLeft B A C, by grind [reverseRules], by grind⟩

grind_pattern reverseRules_complete_of_ruleIn => reverseRules K C, ChartRule K A B C

/-! ## One-step backward search -/

/-- Backward search for one unary type-raising step. -/
@[grind =]
def tryUnaryStep (rec : List Category → Category → Bool) (Γ : List Category) : Category → Bool
  | C ⧸ (A ⧹ C') => if C = C' then rec Γ A else false
  | (C' ⧸ A) ⧹ C => if C' = C then rec Γ A else false
  | _ => false

/-- A successful unary backward step is exactly one of the two type-raising
inverses with a successful recursive premise.  This single characterization
drives both the soundness and the monotonicity proofs. -/
@[grind =]
theorem tryUnaryStep_eq_true_iff (rec : List Category → Category → Bool) (Γ : List Category) (T : Category) :
    tryUnaryStep rec Γ T = true ↔
      (∃ C A, T = C ⧸ (A ⧹ C) ∧ rec Γ A = true) ∨
      (∃ C A, T = (C ⧸ A) ⧹ C ∧ rec Γ A = true) := by
  unfold tryUnaryStep
  grind

/-- Backward search for one binary rule step. -/
@[grind =]
def tryBinaryStep (K : List Category) (rec : List Category → Category → Bool) (Γ : List Category) (A : Category) : Bool :=
  (nonemptySplits Γ).any (fun p =>
    (reverseRules K A).any (fun r => rec p.1 r.left && rec p.2 r.right))

/-- A successful binary backward step exposes a proper split and a backward rule
whose two premises both succeed recursively. -/
@[grind =]
theorem tryBinaryStep_eq_true_iff (K : List Category) (rec : List Category → Category → Bool)
    (Γ : List Category) (A : Category) :
    tryBinaryStep K rec Γ A = true ↔
      ∃ p ∈ nonemptySplits Γ, ∃ r ∈ reverseRules K A,
        rec p.1 r.left = true ∧ rec p.2 r.right = true := by
  grind [tryBinaryStep]

/-! ## The fuel-bounded recognizer -/

/-- Fuel-bounded recognizer over a finite candidate set `K`.

`fuel` bounds the number of backward rule expansions.  The base case still
recognize a leaf item, so increasing fuel monotonically extends the search in
practice. -/
@[grind =]
def recognize (K : List Category) : Nat → List Category → Category → Bool
  | 0, Γ, A => decide (A ∈ K) && (Γ == [A])
  | fuel + 1, Γ, A =>
      decide (A ∈ K) && ((Γ == [A]) || tryUnaryStep (recognize K fuel) Γ A ||
        tryBinaryStep K (recognize K fuel) Γ A)

@[grind =]
theorem recognize_zero (K : List Category) (Γ : List Category) (A : Category) :
    recognize K 0 Γ A = (decide (A ∈ K) && (Γ == [A])) := rfl

/-- A successful recognizer step is a leaf, a unary step, or a binary step.
This flattens the boolean disjunction shared by every step-level proof. -/
@[grind =]
theorem recognize_succ_eq_true_iff (K : List Category) (fuel : Nat) (Γ : List Category) (A : Category) :
    recognize K (fuel + 1) Γ A = true ↔
      A ∈ K ∧
        ((Γ == [A]) = true ∨
        tryUnaryStep (recognize K fuel) Γ A = true ∨
        tryBinaryStep K (recognize K fuel) Γ A = true) := by
  rw [recognize]
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hA, (hleaf | hunary) | hbinary⟩
    · exact ⟨hA, Or.inl hleaf⟩
    · exact ⟨hA, Or.inr (Or.inl hunary)⟩
    · exact ⟨hA, Or.inr (Or.inr hbinary)⟩
  · rintro ⟨hA, hleaf | hunary | hbinary⟩
    · exact ⟨hA, Or.inl (Or.inl hleaf)⟩
    · exact ⟨hA, Or.inl (Or.inr hunary)⟩
    · exact ⟨hA, Or.inr hbinary⟩

/-! ## Decidable wrapper -/

/-- A finite bounded derivability proposition, represented by the recognizer. -/
@[grind =]
def RecognizedWithFuel (K : List Category) (fuel : Nat) (Γ : List Category) (A : Category) : Prop :=
  recognize K fuel Γ A = true

instance instDecidableRecognizedWithFuel (K : List Category) (fuel : Nat) (Γ : List Category) (A : Category) :
    Decidable (RecognizedWithFuel K fuel Γ A) := by
  unfold RecognizedWithFuel
  infer_instance

/-- The decision function for bounded derivability. -/
@[grind =]
def decideWithFuel (K : List Category) (fuel : Nat) (Γ : List Category) (A : Category) : Bool :=
  recognize K fuel Γ A

@[grind =]
theorem decideWithFuel_eq (K : List Category) (fuel : Nat) (Γ : List Category) (A : Category) :
    decideWithFuel K fuel Γ A = recognize K fuel Γ A := rfl

/-- The decision function agrees with the bounded derivability proposition. -/
@[grind =]
theorem decideWithFuel_iff (K : List Category) (fuel : Nat) (Γ : List Category) (A : Category) :
    decideWithFuel K fuel Γ A = true ↔ RecognizedWithFuel K fuel Γ A := Iff.rfl

end Mathling.CCG
