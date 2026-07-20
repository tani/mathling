module

public import Mathling.CCG.Derivation

@[expose] public section

/-!
# Explicit derivation trees for the eight-rule CCG system

`Derivable` is a `Prop`-valued relation: it records *that* a sequent is derivable
but discards the derivation itself.  The band-contraction argument of
`ccg_decidability_proof_3-1.pdf` reasons about a concrete derivation tree, its
occurrences, and a structural size measure `size`.  This module introduces the
`Type`-valued tree `DerivationTree Γ A` that carries that data, together with:

* the constructor-occurrence measure `DerivationTree.size` (the paper's `size(D)`),
* the forgetful map `DerivationTree.toDerivable`,
* existence of a tree for every derivation (`Derivable.exists_derivationTree`).

These are the data-level foundations on which `Occurrence`, `Trace` and `Band`
build.
-/

set_option linter.style.longLine false

namespace Mathling.CCG

open Category

/-- An explicit eight-rule CCG derivation tree with leaves `Γ` and root `A`.

This mirrors `Derivable` but lives in `Type`, so a derivation can be inspected,
measured and rewritten. -/
inductive DerivationTree : List Category → Category → Type where
  | leaf (A : Category) : DerivationTree [A] A
  | typeRaiseRight (C : Category) {Γ : List Category} {A : Category} (t : DerivationTree Γ A) :
      DerivationTree Γ (C ⧸ (A ⧹ C))
  | typeRaiseLeft (C : Category) {Γ : List Category} {A : Category} (t : DerivationTree Γ A) :
      DerivationTree Γ ((C ⧸ A) ⧹ C)
  | binary {Γ Δ : List Category} {A B C : Category}
      (t₁ : DerivationTree Γ A) (t₂ : DerivationTree Δ B) (r : Rule A B C) :
      DerivationTree (Γ ++ Δ) C

namespace DerivationTree

/-- The root category of a tree.  By construction this is exactly the succedent
index `A`. -/
def root : {Γ : List Category} → {A : Category} → DerivationTree Γ A → Category
  | _, A, _ => A

@[simp, grind =]
theorem root_eq {Γ : List Category} {A : Category} (t : DerivationTree Γ A) : t.root = A := rfl

/-- The list of leaf categories of a tree.  By construction this is exactly the
antecedent index `Γ`. -/
def leaves : {Γ : List Category} → {A : Category} → DerivationTree Γ A → List Category
  | Γ, _, _ => Γ

@[simp, grind =]
theorem leaves_eq {Γ : List Category} {A : Category} (t : DerivationTree Γ A) : t.leaves = Γ := rfl

/-- The constructor-occurrence measure `size(D)` of the paper: the sum, over every
node of the tree, of the number of slash constructors in that node's category.

The measure is written in terms of `root` so that the defining equations are
definitional (`rfl`), regardless of how the dependent indices are displayed. -/
def size : {Γ : List Category} → {A : Category} → DerivationTree Γ A → Nat
  | _, _, .leaf A => A.constructors
  | _, _, .typeRaiseRight C t => (C ⧸ (t.root ⧹ C)).constructors + size t
  | _, _, .typeRaiseLeft C t => ((C ⧸ t.root) ⧹ C).constructors + size t
  | _, _, .binary (C := C) t₁ t₂ _ => C.constructors + size t₁ + size t₂

@[simp, grind =]
theorem size_leaf (A : Category) : (DerivationTree.leaf A).size = A.constructors := rfl

@[simp, grind =]
theorem size_typeRaiseRight (C : Category) {Γ : List Category} {A : Category} (t : DerivationTree Γ A) :
    (DerivationTree.typeRaiseRight C t).size = (C ⧸ (A ⧹ C)).constructors + t.size := rfl

@[simp, grind =]
theorem size_typeRaiseLeft (C : Category) {Γ : List Category} {A : Category} (t : DerivationTree Γ A) :
    (DerivationTree.typeRaiseLeft C t).size = ((C ⧸ A) ⧹ C).constructors + t.size := rfl

@[simp, grind =]
theorem size_binary {Γ Δ : List Category} {A B C : Category}
    (t₁ : DerivationTree Γ A) (t₂ : DerivationTree Δ B) (r : Rule A B C) :
    (DerivationTree.binary t₁ t₂ r).size = C.constructors + t₁.size + t₂.size := rfl

/-- Forgetting the tree structure yields the underlying inductive derivation. -/
def toDerivable : {Γ : List Category} → {A : Category} → DerivationTree Γ A → (Γ ⇒ccg A)
  | _, _, .leaf _ => Derivable.leaf
  | _, _, .typeRaiseRight _ t => Derivable.typeRaiseRight t.toDerivable
  | _, _, .typeRaiseLeft _ t => Derivable.typeRaiseLeft t.toDerivable
  | _, _, .binary t₁ t₂ r => Derivable.binary t₁.toDerivable t₂.toDerivable r

end DerivationTree

/-- Every derivation is witnessed by some explicit tree.  The statement is a
`Prop` (`∃ _ : DerivationTree …, True`) so that it can be proved by induction on the
`Prop`-valued `Derivable`. -/
theorem Derivable.exists_derivationTree {Γ : List Category} {A : Category} (h : Γ ⇒ccg A) :
    ∃ _t : DerivationTree Γ A, True := by
  induction h with
  | leaf => exact ⟨.leaf _, trivial⟩
  | typeRaiseRight _ ih =>
      obtain ⟨t, _⟩ := ih
      exact ⟨.typeRaiseRight _ t, trivial⟩
  | typeRaiseLeft _ ih =>
      obtain ⟨t, _⟩ := ih
      exact ⟨.typeRaiseLeft _ t, trivial⟩
  | binary _ _ r ih₁ ih₂ =>
      obtain ⟨t₁, _⟩ := ih₁
      obtain ⟨t₂, _⟩ := ih₂
      exact ⟨.binary t₁ t₂ r, trivial⟩

/-- Derivability is logically equivalent to the existence of an explicit tree. -/
theorem Derivable.iff_exists_derivationTree {Γ : List Category} {A : Category} :
    (Γ ⇒ccg A) ↔ ∃ _t : DerivationTree Γ A, True := by
  constructor
  · exact Derivable.exists_derivationTree
  · rintro ⟨t, _⟩
    exact t.toDerivable

end Mathling.CCG
