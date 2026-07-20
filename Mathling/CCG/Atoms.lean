module

public import Mathling.CCG.Derivation
public import Mathling.CCG.Finite

@[expose] public section

/-!
# Atom erasure for the eight-rule CCG system

This module formalizes the atom-finiteness layer of the paper.  The key point is
that any derivation can be homomorphically collapsed to one whose intermediate
categories use only atoms from the input and target.  This is the Lean version
of the paper's atom-erasure lemma, stated as `Derivable.toAtomRestrictedDerivableUsingProblemAtoms`.
-/

set_option linter.style.longLine false

namespace Mathling.CCG

open Category List

/-! ## Atom containment predicates -/

/-- Every atom occurring in category `A` belongs to the finite atom list `atomNames`. -/
@[grind =]
def UsesOnlyAtoms (atomNames : List String) (A : Category) : Prop :=
  ∀ name ∈ A.atoms, name ∈ atomNames

/-- Every atom occurring in context `Γ` belongs to `atomNames`. -/
@[grind =]
def ContextUsesOnlyAtoms (atomNames : List String) (Γ : List Category) : Prop :=
  ∀ name ∈ contextAtoms Γ, name ∈ atomNames

@[grind =>]
theorem UsesOnlyAtoms.ldiv_left {atomNames : List String} {A B : Category}
    (h : UsesOnlyAtoms atomNames (A ⧹ B)) : UsesOnlyAtoms atomNames A := by
  intro name hname
  exact h name (by grind [UsesOnlyAtoms, Category.atoms])

@[grind =>]
theorem UsesOnlyAtoms.ldiv_right {atomNames : List String} {A B : Category}
    (h : UsesOnlyAtoms atomNames (A ⧹ B)) : UsesOnlyAtoms atomNames B := by
  intro name hname
  exact h name (by grind [UsesOnlyAtoms, Category.atoms])

@[grind =>]
theorem UsesOnlyAtoms.rdiv_left {atomNames : List String} {A B : Category}
    (h : UsesOnlyAtoms atomNames (A ⧸ B)) : UsesOnlyAtoms atomNames A := by
  intro name hname
  exact h name (by grind [UsesOnlyAtoms, Category.atoms])

@[grind =>]
theorem UsesOnlyAtoms.rdiv_right {atomNames : List String} {A B : Category}
    (h : UsesOnlyAtoms atomNames (A ⧸ B)) : UsesOnlyAtoms atomNames B := by
  intro name hname
  exact h name (by grind [UsesOnlyAtoms, Category.atoms])

@[grind =>]
theorem UsesOnlyAtoms.ldiv {atomNames : List String} {A B : Category}
    (hA : UsesOnlyAtoms atomNames A) (hB : UsesOnlyAtoms atomNames B) : UsesOnlyAtoms atomNames (A ⧹ B) := by
  intro name hname
  grind [UsesOnlyAtoms, Category.atoms]

@[grind =>]
theorem UsesOnlyAtoms.rdiv {atomNames : List String} {A B : Category}
    (hA : UsesOnlyAtoms atomNames A) (hB : UsesOnlyAtoms atomNames B) : UsesOnlyAtoms atomNames (A ⧸ B) := by
  intro name hname
  grind [UsesOnlyAtoms, Category.atoms]

/-- Every syntactic category contains at least one atom occurrence. -/
theorem Category.exists_mem_atoms (A : Category) : ∃ name, name ∈ A.atoms := by
  induction A with
  | atom name => exact ⟨name, by grind [Category.atoms]⟩
  | ldiv A B ihA ihB =>
      rcases ihA with ⟨name, hname⟩
      exact ⟨name, by grind [Category.atoms]⟩
  | rdiv A B ihA ihB =>
      rcases ihA with ⟨name, hname⟩
      exact ⟨name, by grind [Category.atoms]⟩

/-- A nonempty context has at least one atom occurrence. -/
theorem exists_mem_contextAtoms_of_ne_nil {Γ : List Category} (hΓ : Γ ≠ []) :
    ∃ name, name ∈ contextAtoms Γ := by
  cases Γ with
  | nil => contradiction
  | cons A Γ =>
      rcases A.exists_mem_atoms with ⟨name, hname⟩
      exact ⟨name, by grind [contextAtoms]⟩

/-- Atoms in the context are atoms of the corresponding recognition problem. -/
@[grind =>]
theorem mem_problemAtomNames_of_mem_contextAtoms {Γ : List Category} {goal : Category} {name : String}
    (h : name ∈ contextAtoms Γ) : name ∈ problemAtomNames Γ goal := by
  unfold problemAtomNames
  rw [mem_eraseDups_iff]
  grind

/-- Atoms in the goal are atoms of the corresponding recognition problem. -/
@[grind =>]
theorem mem_problemAtomNames_of_mem_goal {Γ : List Category} {goal : Category} {name : String}
    (h : name ∈ goal.atoms) : name ∈ problemAtomNames Γ goal := by
  unfold problemAtomNames
  rw [mem_eraseDups_iff]
  grind

/-- The input context uses only atoms from its own recognition problem. -/
@[grind =>]
theorem contextUsesOnlyProblemAtoms (Γ : List Category) (goal : Category) :
    ContextUsesOnlyAtoms (problemAtomNames Γ goal) Γ := by
  intro name hname
  exact mem_problemAtomNames_of_mem_contextAtoms hname

/-- The target uses only atoms from its own recognition problem. -/
@[grind =>]
theorem usesOnlyProblemAtoms_goal (Γ : List Category) (goal : Category) :
    UsesOnlyAtoms (problemAtomNames Γ goal) goal := by
  intro name hname
  exact mem_problemAtomNames_of_mem_goal hname

/-! ## Collapsing atoms by a homomorphism -/

/-- Collapse atoms not in `atomNames` to the fallback atom `fallback`. -/
@[grind =]
def collapseAtom (atomNames : List String) (fallback name : String) : String :=
  if name ∈ atomNames then name else fallback

@[grind =>]
theorem collapseAtom_mem {atomNames : List String} {fallback name : String}
    (hfallback : fallback ∈ atomNames) : collapseAtom atomNames fallback name ∈ atomNames := by
  unfold collapseAtom
  by_cases h : name ∈ atomNames <;> grind

@[grind =>]
theorem collapseAtom_of_mem {atomNames : List String} {fallback name : String}
    (h : name ∈ atomNames) : collapseAtom atomNames fallback name = name := by
  unfold collapseAtom
  grind

/-- If all atoms of `A` are fixed by `f`, then `mapAtoms f A = A`. -/
@[grind =>]
theorem Category.mapAtoms_eq_self_of_usesAtomsFrom {atomNames : List String} {f : String → String} :
    ∀ {A : Category}, UsesOnlyAtoms atomNames A → (∀ name, name ∈ atomNames → f name = name) → A.mapAtoms f = A
  | # name, hA, hf => by
      change # (f name) = # name
      rw [hf name (hA name (by grind [Category.atoms, UsesOnlyAtoms]))]
  | A ⧹ B, hAB, hf => by
      have hA : A.mapAtoms f = A := Category.mapAtoms_eq_self_of_usesAtomsFrom hAB.ldiv_left hf
      have hB : B.mapAtoms f = B := Category.mapAtoms_eq_self_of_usesAtomsFrom hAB.ldiv_right hf
      grind
  | A ⧸ B, hAB, hf => by
      have hA : A.mapAtoms f = A := Category.mapAtoms_eq_self_of_usesAtomsFrom hAB.rdiv_left hf
      have hB : B.mapAtoms f = B := Category.mapAtoms_eq_self_of_usesAtomsFrom hAB.rdiv_right hf
      grind

/-- If all context atoms are fixed by `f`, then mapping `f` over the context is
identity. -/
@[grind =>]
theorem map_mapAtoms_eq_self_of_contextUsesOnlyAtoms {atomNames : List String} {f : String → String} :
    ∀ {Γ : List Category}, ContextUsesOnlyAtoms atomNames Γ → (∀ name, name ∈ atomNames → f name = name) →
      Γ.map (Category.mapAtoms f) = Γ
  | [], _hΓ, _hf => rfl
  | A :: Γ, hΓ, hf => by
      have hA : UsesOnlyAtoms atomNames A := by
        intro name hname
        exact hΓ name (by grind [ContextUsesOnlyAtoms, contextAtoms])
      have htail : ContextUsesOnlyAtoms atomNames Γ := by
        intro name hname
        exact hΓ name (by grind [ContextUsesOnlyAtoms, contextAtoms])
      have hAeq : A.mapAtoms f = A := Category.mapAtoms_eq_self_of_usesAtomsFrom hA hf
      have hΓeq : Γ.map (Category.mapAtoms f) = Γ :=
        map_mapAtoms_eq_self_of_contextUsesOnlyAtoms htail hf
      grind

/-- Atom maps whose images lie in `atomNames` send every category to one using only
atoms in `atomNames`. -/
@[grind =>]
theorem Category.usesAtomsFrom_mapAtoms {atomNames : List String} {f : String → String}
    (hf : ∀ name, f name ∈ atomNames) : ∀ A : Category, UsesOnlyAtoms atomNames (A.mapAtoms f)
  | # name => by
      intro atom hatom
      grind [UsesOnlyAtoms, Category.atoms]
  | A ⧹ B => by
      exact UsesOnlyAtoms.ldiv (Category.usesAtomsFrom_mapAtoms hf A) (Category.usesAtomsFrom_mapAtoms hf B)
  | A ⧸ B => by
      exact UsesOnlyAtoms.rdiv (Category.usesAtomsFrom_mapAtoms hf A) (Category.usesAtomsFrom_mapAtoms hf B)

/-! ## Derivations with all intermediate atoms in a finite set -/

/-- Binary rules whose schematic metavariables use only atoms from `atomNames`. -/
@[grind intro]
inductive AtomRestrictedRule (atomNames : List String) : Category → Category → Category → Prop where
  | appRight (hC : UsesOnlyAtoms atomNames C) (hB : UsesOnlyAtoms atomNames B) :
      AtomRestrictedRule atomNames (C ⧸ B) B C
  | appLeft (hA : UsesOnlyAtoms atomNames A) (hC : UsesOnlyAtoms atomNames C) :
      AtomRestrictedRule atomNames A (A ⧹ C) C
  | compRight (hC : UsesOnlyAtoms atomNames C) (hB : UsesOnlyAtoms atomNames B) (hA : UsesOnlyAtoms atomNames A) :
      AtomRestrictedRule atomNames (C ⧸ B) (B ⧸ A) (C ⧸ A)
  | compLeft (hA : UsesOnlyAtoms atomNames A) (hB : UsesOnlyAtoms atomNames B) (hC : UsesOnlyAtoms atomNames C) :
      AtomRestrictedRule atomNames (A ⧹ B) (B ⧹ C) (A ⧹ C)
  | crossedRight (hC : UsesOnlyAtoms atomNames C) (hB : UsesOnlyAtoms atomNames B) (hA : UsesOnlyAtoms atomNames A) :
      AtomRestrictedRule atomNames (C ⧸ B) (A ⧹ B) (A ⧹ C)
  | crossedLeft (hB : UsesOnlyAtoms atomNames B) (hA : UsesOnlyAtoms atomNames A) (hC : UsesOnlyAtoms atomNames C) :
      AtomRestrictedRule atomNames (B ⧸ A) (B ⧹ C) (C ⧸ A)

namespace AtomRestrictedRule

/-- Forget atom-set bookkeeping from a binary rule. -/
@[grind =>]
theorem toRule {atomNames : List String} {A B C : Category}
    (h : AtomRestrictedRule atomNames A B C) : Rule A B C := by
  cases h <;> grind

/-- The result category of an atom-restricted rule uses only the tracked atoms. -/
@[grind =>]
theorem result_usesOnlyAtoms {atomNames : List String} {A B C : Category}
    (h : AtomRestrictedRule atomNames A B C) : UsesOnlyAtoms atomNames C := by
  cases h <;> grind

end AtomRestrictedRule

/-- A derivation whose intermediate categories and binary-rule metavariables use
only atoms from `atomNames`. -/
@[grind intro]
inductive AtomRestrictedDerivable (atomNames : List String) : List Category → Category → Prop where
  | leaf (hA : UsesOnlyAtoms atomNames A) : AtomRestrictedDerivable atomNames [A] A
  | typeRaiseRight (hC : UsesOnlyAtoms atomNames C) :
      AtomRestrictedDerivable atomNames Γ A → AtomRestrictedDerivable atomNames Γ (C ⧸ (A ⧹ C))
  | typeRaiseLeft (hC : UsesOnlyAtoms atomNames C) :
      AtomRestrictedDerivable atomNames Γ A → AtomRestrictedDerivable atomNames Γ ((C ⧸ A) ⧹ C)
  | binary :
      AtomRestrictedDerivable atomNames Γ A →
      AtomRestrictedDerivable atomNames Δ B →
      AtomRestrictedRule atomNames A B C →
      AtomRestrictedDerivable atomNames (Γ ++ Δ) C

namespace AtomRestrictedDerivable

/-- Forget atom-set bookkeeping from a derivation. -/
@[grind =>]
theorem toDerivable {atomNames : List String} {Γ : List Category} {A : Category}
    (h : AtomRestrictedDerivable atomNames Γ A) : Γ ⇒ccg A := by
  induction h with
  | leaf => exact Derivable.leaf
  | typeRaiseRight _ _ ih => exact Derivable.typeRaiseRight ih
  | typeRaiseLeft _ _ ih => exact Derivable.typeRaiseLeft ih
  | binary _ _ rule ih₁ ih₂ => exact Derivable.binary ih₁ ih₂ rule.toRule

end AtomRestrictedDerivable

/-- Homomorphic atom maps with image in `atomNames` turn a binary-rule instance into a
`AtomRestrictedRule` instance. -/
@[grind =>]
theorem Rule.mapAtoms_usesAtomsFrom {atomNames : List String} {A B C : Category} (f : String → String)
    (hf : ∀ name, f name ∈ atomNames) (h : Rule A B C) :
    AtomRestrictedRule atomNames (A.mapAtoms f) (B.mapAtoms f) (C.mapAtoms f) := by
  cases h
  case appRight =>
    exact AtomRestrictedRule.appRight (Category.usesAtomsFrom_mapAtoms hf _) (Category.usesAtomsFrom_mapAtoms hf _)
  case appLeft =>
    exact AtomRestrictedRule.appLeft (Category.usesAtomsFrom_mapAtoms hf _) (Category.usesAtomsFrom_mapAtoms hf _)
  case compRight C B A =>
    exact AtomRestrictedRule.compRight
      (Category.usesAtomsFrom_mapAtoms hf C) (Category.usesAtomsFrom_mapAtoms hf B) (Category.usesAtomsFrom_mapAtoms hf A)
  case compLeft A B C =>
    exact AtomRestrictedRule.compLeft
      (Category.usesAtomsFrom_mapAtoms hf A) (Category.usesAtomsFrom_mapAtoms hf B) (Category.usesAtomsFrom_mapAtoms hf C)
  case crossedRight C B A =>
    exact AtomRestrictedRule.crossedRight
      (Category.usesAtomsFrom_mapAtoms hf C) (Category.usesAtomsFrom_mapAtoms hf B) (Category.usesAtomsFrom_mapAtoms hf A)
  case crossedLeft B A C =>
    exact AtomRestrictedRule.crossedLeft
      (Category.usesAtomsFrom_mapAtoms hf B) (Category.usesAtomsFrom_mapAtoms hf A) (Category.usesAtomsFrom_mapAtoms hf C)

/-- Homomorphic atom maps with image in `atomNames` turn any derivation into one whose
intermediate atoms are all in `atomNames`. -/
@[grind =>]
theorem Derivable.mapAtoms_usesAtomsFrom {atomNames : List String} {Γ : List Category} {A : Category}
    (f : String → String) (hf : ∀ name, f name ∈ atomNames) (h : Γ ⇒ccg A) :
    AtomRestrictedDerivable atomNames (Γ.map (Category.mapAtoms f)) (A.mapAtoms f) := by
  induction h with
  | leaf => exact AtomRestrictedDerivable.leaf (Category.usesAtomsFrom_mapAtoms hf _)
  | typeRaiseRight h ih => exact AtomRestrictedDerivable.typeRaiseRight (Category.usesAtomsFrom_mapAtoms hf _) ih
  | typeRaiseLeft h ih => exact AtomRestrictedDerivable.typeRaiseLeft (Category.usesAtomsFrom_mapAtoms hf _) ih
  | binary h₁ h₂ rule ih₁ ih₂ =>
      simpa [List.map_append] using
        (AtomRestrictedDerivable.binary ih₁ ih₂ (rule.mapAtoms_usesAtomsFrom f hf))

/-- Derivable sequents have nonempty antecedents. -/
@[grind =>]
theorem Derivable.context_ne_nil {Γ : List Category} {A : Category} (h : Γ ⇒ccg A) : Γ ≠ [] := by
  induction h with
  | leaf => grind
  | typeRaiseRight _ ih => exact ih
  | typeRaiseLeft _ ih => exact ih
  | binary h₁ h₂ _ ih₁ ih₂ =>
      exact List.append_ne_nil_of_left_ne_nil ih₁ _

/-- If `Γ ⇒ccg A`, then the problem atom list is nonempty. -/
theorem Derivable.exists_mem_problemAtomNames {Γ : List Category} {A : Category} (h : Γ ⇒ccg A) :
    ∃ fallback, fallback ∈ problemAtomNames Γ A := by
  rcases exists_mem_contextAtoms_of_ne_nil h.context_ne_nil with ⟨fallback, hfallback⟩
  exact ⟨fallback, mem_problemAtomNames_of_mem_contextAtoms hfallback⟩

/-- Atom-erasure lemma: if `Γ ⇒ccg A`, then there is a derivation with the same
endpoints whose every intermediate category and binary-rule metavariable uses
only atoms from `problemAtomNames Γ A`. -/
theorem Derivable.toAtomRestrictedDerivableUsingProblemAtoms {Γ : List Category} {A : Category} (h : Γ ⇒ccg A) :
    AtomRestrictedDerivable (problemAtomNames Γ A) Γ A := by
  rcases h.exists_mem_problemAtomNames with ⟨fallback, hfallback⟩
  let f := collapseAtom (problemAtomNames Γ A) fallback
  have hfmem : ∀ name, f name ∈ problemAtomNames Γ A := by
    intro name
    exact collapseAtom_mem hfallback
  have hffix : ∀ name, name ∈ problemAtomNames Γ A → f name = name := by
    intro name hname
    exact collapseAtom_of_mem hname
  have hΓfix : Γ.map (Category.mapAtoms f) = Γ := by
    exact map_mapAtoms_eq_self_of_contextUsesOnlyAtoms (contextUsesOnlyProblemAtoms Γ A) hffix
  have hAfix : A.mapAtoms f = A := by
    exact Category.mapAtoms_eq_self_of_usesAtomsFrom (usesOnlyProblemAtoms_goal Γ A) hffix
  have hmapped := h.mapAtoms_usesAtomsFrom f hfmem
  simpa [hΓfix, hAfix] using hmapped

end Mathling.CCG
