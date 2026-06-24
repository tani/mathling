import Mathling.CCG.Category

/-!
# The eight-rule CCG derivability relation

This module defines the binary rule schemata and the inductive derivability
relation `⇒ccg`, together with convenient wrappers for each of the eight rules
and the atom-homomorphism preservation results used by the blueprint's
atom-erasure argument.
-/

namespace Mathling.CCG

open Tp

/-- A single binary CCG rule instance. -/
@[grind intro]
inductive BinaryRule : Tp → Tp → Tp → Prop where
  | appRight : BinaryRule (C ⧸ B) B C
  | appLeft : BinaryRule A (A ⧹ C) C
  | compRight : BinaryRule (C ⧸ B) (B ⧸ A) (C ⧸ A)
  | compLeft : BinaryRule (A ⧹ B) (B ⧹ C) (A ⧹ C)
  | crossedRight : BinaryRule (C ⧸ B) (A ⧹ B) (A ⧹ C)
  | crossedLeft : BinaryRule (B ⧸ A) (B ⧹ C) (C ⧸ A)

/-- The eight-rule CCG derivability relation over a span/category list.

`Derives Γ A` means that the category sequence `Γ` can be reduced to `A` by
CCG rules.  Unary constructors are the unrestricted type raising rules. -/
@[grind intro]
inductive Derives : List Tp → Tp → Prop where
  | leaf : Derives [A] A
  | typeRaiseRight : Derives Γ A → Derives Γ (C ⧸ (A ⧹ C))
  | typeRaiseLeft : Derives Γ A → Derives Γ ((C ⧸ A) ⧹ C)
  | binary :
      Derives Γ A →
      Derives Δ B →
      BinaryRule A B C →
      Derives (Γ ++ Δ) C

@[inherit_doc] infixl:50 " ⇒ccg " => Derives

namespace Derives

/-- Forward application. -/
@[grind →]
theorem appRight (h₁ : Γ ⇒ccg (C ⧸ B)) (h₂ : Δ ⇒ccg B) :
    Γ ++ Δ ⇒ccg C :=
  Derives.binary h₁ h₂ BinaryRule.appRight

/-- Backward application. -/
@[grind →]
theorem appLeft (h₁ : Γ ⇒ccg A) (h₂ : Δ ⇒ccg (A ⧹ C)) :
    Γ ++ Δ ⇒ccg C :=
  Derives.binary h₁ h₂ BinaryRule.appLeft

/-- Forward composition. -/
@[grind →]
theorem compRight (h₁ : Γ ⇒ccg (C ⧸ B)) (h₂ : Δ ⇒ccg (B ⧸ A)) :
    Γ ++ Δ ⇒ccg (C ⧸ A) :=
  Derives.binary h₁ h₂ BinaryRule.compRight

/-- Backward composition. -/
@[grind →]
theorem compLeft (h₁ : Γ ⇒ccg (A ⧹ B)) (h₂ : Δ ⇒ccg (B ⧹ C)) :
    Γ ++ Δ ⇒ccg (A ⧹ C) :=
  Derives.binary h₁ h₂ BinaryRule.compLeft

/-- Forward crossed composition. -/
@[grind →]
theorem crossedRight (h₁ : Γ ⇒ccg (C ⧸ B)) (h₂ : Δ ⇒ccg (A ⧹ B)) :
    Γ ++ Δ ⇒ccg (A ⧹ C) :=
  Derives.binary h₁ h₂ BinaryRule.crossedRight

/-- Backward crossed composition. -/
@[grind →]
theorem crossedLeft (h₁ : Γ ⇒ccg (B ⧸ A)) (h₂ : Δ ⇒ccg (B ⧹ C)) :
    Γ ++ Δ ⇒ccg (C ⧸ A) :=
  Derives.binary h₁ h₂ BinaryRule.crossedLeft

end Derives

/-- Homomorphic atom maps preserve binary rule instances. -/
@[grind =>]
theorem BinaryRule.mapAtoms {A B C : Tp} (f : String → String)
    (h : BinaryRule A B C) :
    BinaryRule (A.mapAtoms f) (B.mapAtoms f) (C.mapAtoms f) := by
  cases h <;> grind

/-- Homomorphic atom maps preserve derivations.  This is the formal core of the
atom-erasure argument in the blueprint. -/
@[grind =>]
theorem Derives.mapAtoms {Γ : List Tp} {A : Tp} (f : String → String)
    (h : Γ ⇒ccg A) :
    (Γ.map (Tp.mapAtoms f)) ⇒ccg (A.mapAtoms f) := by
  induction h <;> grind

end Mathling.CCG
