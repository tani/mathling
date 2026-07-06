import Mathling.CCG.Category

/-!
# The eight-rule CCG derivability relation

This module defines the binary rule schemata and the inductive derivability
relation `⇒ccg`, together with convenient wrappers for each of the eight rules
and the atom-homomorphism preservation results used by the blueprint's
atom-erasure argument.
-/

namespace Mathling.CCG

open Category

/-- A single binary CCG rule instance. -/
@[grind intro]
inductive Rule : Category → Category → Category → Prop where
  | appRight : Rule (C ⧸ B) B C
  | appLeft : Rule A (A ⧹ C) C
  | compRight : Rule (C ⧸ B) (B ⧸ A) (C ⧸ A)
  | compLeft : Rule (A ⧹ B) (B ⧹ C) (A ⧹ C)
  | crossedRight : Rule (C ⧸ B) (A ⧹ B) (A ⧹ C)
  | crossedLeft : Rule (B ⧸ A) (B ⧹ C) (C ⧸ A)

/-- Binary rules never increase category depth: the conclusion is at most as
deep as the deeper premise.  Consequently unrestricted type raising is the
*only* source of unbounded intermediate categories, and the whole decidability
problem reduces to bounding type-raising targets. -/
theorem Rule.depth_le {A B C : Category} (h : Rule A B C) :
    C.depth ≤ Nat.max A.depth B.depth := by
  cases h <;> simp [Category.depth] <;> grind

/-!
`Rule` is the mathematical rule relation.  For finite-chart completeness
we also need the bookkeeping assertion that the schematic metavariables of a
rule instance are drawn from the finite candidate alphabet `K`.

This is deliberately stronger than merely asking that the three displayed node
labels belong to `K`: for example `C/B, B/A ⟶ C/A` requires the hidden middle
category `B` to be enumerated by the backward parser.
-/

/-- A binary CCG rule instance whose displayed categories and schematic
metavariables are all members of the finite candidate category list `K`. -/
@[grind intro]
inductive ChartRule (K : List Category) : Category → Category → Category → Prop where
  | appRight (hC : C ∈ K) (hB : B ∈ K) (hLeft : C ⧸ B ∈ K) :
      ChartRule K (C ⧸ B) B C
  | appLeft (hA : A ∈ K) (hC : C ∈ K) (hRight : A ⧹ C ∈ K) :
      ChartRule K A (A ⧹ C) C
  | compRight
      (hC : C ∈ K) (hB : B ∈ K) (hA : A ∈ K)
      (hLeft : C ⧸ B ∈ K) (hRight : B ⧸ A ∈ K) (hOut : C ⧸ A ∈ K) :
      ChartRule K (C ⧸ B) (B ⧸ A) (C ⧸ A)
  | compLeft
      (hA : A ∈ K) (hB : B ∈ K) (hC : C ∈ K)
      (hLeft : A ⧹ B ∈ K) (hRight : B ⧹ C ∈ K) (hOut : A ⧹ C ∈ K) :
      ChartRule K (A ⧹ B) (B ⧹ C) (A ⧹ C)
  | crossedRight
      (hC : C ∈ K) (hB : B ∈ K) (hA : A ∈ K)
      (hLeft : C ⧸ B ∈ K) (hRight : A ⧹ B ∈ K) (hOut : A ⧹ C ∈ K) :
      ChartRule K (C ⧸ B) (A ⧹ B) (A ⧹ C)
  | crossedLeft
      (hB : B ∈ K) (hA : A ∈ K) (hC : C ∈ K)
      (hLeft : B ⧸ A ∈ K) (hRight : B ⧹ C ∈ K) (hOut : C ⧸ A ∈ K) :
      ChartRule K (B ⧸ A) (B ⧹ C) (C ⧸ A)

namespace ChartRule

/-- Forget finite-candidate bookkeeping from a bounded binary rule instance. -/
@[grind =>]
theorem toRule {K : List Category} {A B C : Category}
    (h : ChartRule K A B C) : Rule A B C := by
  cases h <;> grind

/-- The left premise category of a finite-candidate-aware rule is in `K`. -/
@[grind =>]
theorem left_mem {K : List Category} {A B C : Category}
    (h : ChartRule K A B C) : A ∈ K := by
  cases h <;> grind

/-- The right premise category of a finite-candidate-aware rule is in `K`. -/
@[grind =>]
theorem right_mem {K : List Category} {A B C : Category}
    (h : ChartRule K A B C) : B ∈ K := by
  cases h <;> grind

/-- The result category of a finite-candidate-aware rule is in `K`. -/
@[grind =>]
theorem result_mem {K : List Category} {A B C : Category}
    (h : ChartRule K A B C) : C ∈ K := by
  cases h <;> grind

end ChartRule

/-- The eight-rule CCG derivability relation over a span/category list.

`Derivable Γ A` means that the category sequence `Γ` can be reduced to `A` by
CCG rules.  Unary constructors are the unrestricted type raising rules. -/
@[grind intro]
inductive Derivable : List Category → Category → Prop where
  | leaf : Derivable [A] A
  | typeRaiseRight : Derivable Γ A → Derivable Γ (C ⧸ (A ⧹ C))
  | typeRaiseLeft : Derivable Γ A → Derivable Γ ((C ⧸ A) ⧹ C)
  | binary :
      Derivable Γ A →
      Derivable Δ B →
      Rule A B C →
      Derivable (Γ ++ Δ) C

/-!
`ChartDerivable K Γ A` is the bounded-normal-form version of `Derivable`: every
category introduced by type raising, and every schematic metavariable used by a
binary rule, is known to be in the finite candidate list `K`.  This is the
formal interface between the paper's depth-bound theorem and the executable
finite parser.
-/

/-- A derivation whose category labels and binary-rule metavariables are
contained in the finite candidate list `K`. -/
@[grind intro]
inductive ChartDerivable (K : List Category) : List Category → Category → Prop where
  | leaf (hA : A ∈ K) : ChartDerivable K [A] A
  | typeRaiseRight (hC : C ∈ K) (hOut : C ⧸ (A ⧹ C) ∈ K) :
      ChartDerivable K Γ A → ChartDerivable K Γ (C ⧸ (A ⧹ C))
  | typeRaiseLeft (hC : C ∈ K) (hOut : (C ⧸ A) ⧹ C ∈ K) :
      ChartDerivable K Γ A → ChartDerivable K Γ ((C ⧸ A) ⧹ C)
  | binary :
      ChartDerivable K Γ A →
      ChartDerivable K Δ B →
      ChartRule K A B C →
      ChartDerivable K (Γ ++ Δ) C

@[inherit_doc] infixl:50 " ⇒ccg " => Derivable

namespace Derivable

/-- Forward application. -/
@[grind →]
theorem appRight (h₁ : Γ ⇒ccg (C ⧸ B)) (h₂ : Δ ⇒ccg B) :
    Γ ++ Δ ⇒ccg C :=
  Derivable.binary h₁ h₂ Rule.appRight

/-- Backward application. -/
@[grind →]
theorem appLeft (h₁ : Γ ⇒ccg A) (h₂ : Δ ⇒ccg (A ⧹ C)) :
    Γ ++ Δ ⇒ccg C :=
  Derivable.binary h₁ h₂ Rule.appLeft

/-- Forward composition. -/
@[grind →]
theorem compRight (h₁ : Γ ⇒ccg (C ⧸ B)) (h₂ : Δ ⇒ccg (B ⧸ A)) :
    Γ ++ Δ ⇒ccg (C ⧸ A) :=
  Derivable.binary h₁ h₂ Rule.compRight

/-- Backward composition. -/
@[grind →]
theorem compLeft (h₁ : Γ ⇒ccg (A ⧹ B)) (h₂ : Δ ⇒ccg (B ⧹ C)) :
    Γ ++ Δ ⇒ccg (A ⧹ C) :=
  Derivable.binary h₁ h₂ Rule.compLeft

/-- Forward crossed composition. -/
@[grind →]
theorem crossedRight (h₁ : Γ ⇒ccg (C ⧸ B)) (h₂ : Δ ⇒ccg (A ⧹ B)) :
    Γ ++ Δ ⇒ccg (A ⧹ C) :=
  Derivable.binary h₁ h₂ Rule.crossedRight

/-- Backward crossed composition. -/
@[grind →]
theorem crossedLeft (h₁ : Γ ⇒ccg (B ⧸ A)) (h₂ : Δ ⇒ccg (B ⧹ C)) :
    Γ ++ Δ ⇒ccg (C ⧸ A) :=
  Derivable.binary h₁ h₂ Rule.crossedLeft

end Derivable

namespace ChartDerivable

/-- Forget finite-candidate bookkeeping from a bounded derivation. -/
@[grind =>]
theorem toDerivable {K : List Category} {Γ : List Category} {A : Category}
    (h : ChartDerivable K Γ A) : Γ ⇒ccg A := by
  induction h with
  | leaf => exact Derivable.leaf
  | typeRaiseRight _ _ _ ih => exact Derivable.typeRaiseRight ih
  | typeRaiseLeft _ _ _ ih => exact Derivable.typeRaiseLeft ih
  | binary _ _ rule ih₁ ih₂ => exact Derivable.binary ih₁ ih₂ rule.toRule

/-- The result category of a bounded derivation is in its finite candidate
list. -/
@[grind =>]
theorem result_mem {K : List Category} {Γ : List Category} {A : Category}
    (h : ChartDerivable K Γ A) : A ∈ K := by
  induction h with
  | leaf hA => exact hA
  | typeRaiseRight _ hOut _ _ => exact hOut
  | typeRaiseLeft _ hOut _ _ => exact hOut
  | binary _ _ rule _ _ => exact rule.result_mem

end ChartDerivable

/-- Homomorphic atom maps preserve binary rule instances. -/
@[grind =>]
theorem Rule.mapAtoms {A B C : Category} (f : String → String)
    (h : Rule A B C) :
    Rule (A.mapAtoms f) (B.mapAtoms f) (C.mapAtoms f) := by
  cases h <;> grind

/-- Homomorphic atom maps preserve derivations.  This is the formal core of the
atom-erasure argument in the blueprint. -/
@[grind =>]
theorem Derivable.mapAtoms {Γ : List Category} {A : Category} (f : String → String)
    (h : Γ ⇒ccg A) :
    (Γ.map (Category.mapAtoms f)) ⇒ccg (A.mapAtoms f) := by
  induction h <;> grind

end Mathling.CCG
