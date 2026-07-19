import Mathling.CCG.Band

/-!
# The protected-skeleton case of boundary-free piece elimination

This file attacks the single remaining obligation of the decidability proof,
`BoundaryFreeProtectedSkeletonPieceContracts`: a derivation tree carrying a
boundary-free invisible trace piece that contains a type-raising skeleton
constructor admits a smaller derivation of the same sequent.

The strategy is structural induction on the derivation tree:

* **leaf** — a leaf tree has only visible occurrences, so no invisible piece
  exists at all (`Occurrence.visible_of_leaf`);
* **unary root** — a boundary-free piece cannot touch the premise root of the
  root type raise (the metavariable copy `A ↦ C/(A\C)` would link it to the
  visible tree root, `InvisiblePiece.not_premiseRoot_of_typeRaiseRight`), so
  the piece restricts to the premise subtree and the induction hypothesis
  applies;
* **binary root, non-crossing** — if the piece touches neither premise root it
  lives strictly inside one premise (trace edges cannot switch sides without
  passing a premise-root occurrence), restricts there, and the induction
  hypothesis applies;
* **binary root, crossing** — the piece touches a premise root of the root
  binary rule.  This is the genuinely hard remaining case, isolated below as
  `CrossingBoundaryFreeSkeletonPieceReduces`.

Everything except the crossing case is proved here, so the previous global
obligation is strictly reduced to the crossing case.

## Why the crossing conclusion is a size reduction, not a collapse redex

An earlier formulation of the crossing case concluded `HasBandRedex`
(a single `T>`-feeding-`>` or `T<`-feeding-`<` collapse step somewhere in the
tree).  That formulation is **false**.  Counterexample: with `A₀ = C₀ ⧸ A'`,

`t = appRight (compRight w₁ (typeRaiseRight C₀ u)) (typeRaiseLeft C₀ u₂)`

where `w₁ : C ⧸ C₀`, `u : A₀`, `u₂ : A'`.  The three occurrences

* inner `T>` skeleton `([left, right], [true])`,
* the `⧹` of the argument slot in the composed functor `([left], [true])`,
* outer `T<` skeleton `([right], [])`

form a boundary-free invisible piece (their full trace neighbourhoods are
exactly each other, via `compRight_A` and `appRight_B`), the piece crosses the
root and contains protected skeletons — yet no subtree matches either collapse
pattern: the type raise is separated from its application by a composition.
A smaller derivation still exists, namely
`appRight w₁ (appRight u u₂)`, but reaching it deletes the raised layer at
*three* nodes simultaneously.  This is precisely the composed cancellation
that band contraction was invented for.

Accordingly the crossing case below concludes `Nonempty (SizeReduction _)`
(same sequent, strictly smaller, no new atoms) rather than a one-step redex,
and this file proves the corrected conclusion for the whole family that
refutes the old one: composition spines ending in a type raise
(`CompSpineRight.collapse`).
-/

set_option linter.style.longLine false

namespace Mathling.CCG

open Category

/-! ## Size reductions

`ContractionWitness` fixes the problem-atom set of the ambient sequent, so it
does not compose under congruence (a subtree has a different sequent).  The
witness below carries the atom condition uniformly in the atom list, composes
under all four tree contexts, and specializes to `ContractionWitness`.
-/

/-- A smaller derivation of the same sequent that introduces no new atoms. -/
structure SizeReduction {Γ : List Category} {A : Category}
    (t : DerivationTree Γ A) where
  target : DerivationTree Γ A
  size_lt : target.size < t.size
  atoms : ∀ atomNames : List String,
    (∀ B ∈ t.nodeCategories, UsesOnlyAtoms atomNames B) →
      ∀ B ∈ target.nodeCategories, UsesOnlyAtoms atomNames B

namespace SizeReduction

/-- A single contraction step is a size reduction. -/
def ofContracts {Γ : List Category} {A : Category}
    {t t' : DerivationTree Γ A} (h : Contracts t t') : SizeReduction t where
  target := t'
  size_lt := h.size_lt
  atoms := fun _ => h.preserves_nodeCategoriesUseOnlyAtoms

/-- Size reductions specialize to contraction witnesses at the ambient
problem-atom set. -/
def toContractionWitness {Γ : List Category} {A : Category}
    {t : DerivationTree Γ A} (w : SizeReduction t) : ContractionWitness t where
  target := w.target
  size_lt := w.size_lt
  preserves_problem_atoms := fun h => w.atoms (problemAtomNames Γ A) h

/-- Congruence: reduce inside a forward type-raising context. -/
def underTypeRaiseRight {Γ : List Category} {A : Category} (C : Category)
    {t : DerivationTree Γ A} (w : SizeReduction t) :
    SizeReduction (DerivationTree.typeRaiseRight C t) where
  target := DerivationTree.typeRaiseRight C w.target
  size_lt := by
    have := w.size_lt
    simp only [DerivationTree.size_typeRaiseRight]
    omega
  atoms := by
    intro names h B hB
    simp only [DerivationTree.nodeCategories_typeRaiseRight, List.mem_cons] at hB
    rcases hB with hB | hB
    · exact h B (by simp [DerivationTree.nodeCategories_typeRaiseRight, hB])
    · exact w.atoms names
        (fun X hX => h X (by simp [DerivationTree.nodeCategories_typeRaiseRight, hX]))
        B hB

/-- Congruence: reduce inside a backward type-raising context. -/
def underTypeRaiseLeft {Γ : List Category} {A : Category} (C : Category)
    {t : DerivationTree Γ A} (w : SizeReduction t) :
    SizeReduction (DerivationTree.typeRaiseLeft C t) where
  target := DerivationTree.typeRaiseLeft C w.target
  size_lt := by
    have := w.size_lt
    simp only [DerivationTree.size_typeRaiseLeft]
    omega
  atoms := by
    intro names h B hB
    simp only [DerivationTree.nodeCategories_typeRaiseLeft, List.mem_cons] at hB
    rcases hB with hB | hB
    · exact h B (by simp [DerivationTree.nodeCategories_typeRaiseLeft, hB])
    · exact w.atoms names
        (fun X hX => h X (by simp [DerivationTree.nodeCategories_typeRaiseLeft, hX]))
        B hB

/-- Congruence: reduce inside the left premise of a binary rule. -/
def underBinaryLeft {Γ Δ : List Category} {A B C : Category}
    {t₁ : DerivationTree Γ A} (t₂ : DerivationTree Δ B) (r : Rule A B C)
    (w : SizeReduction t₁) :
    SizeReduction (DerivationTree.binary t₁ t₂ r) where
  target := DerivationTree.binary w.target t₂ r
  size_lt := by
    have := w.size_lt
    simp only [DerivationTree.size_binary]
    omega
  atoms := by
    intro names h X hX
    simp only [DerivationTree.nodeCategories_binary, List.mem_cons, List.mem_append] at hX
    rcases hX with hX | hX | hX
    · exact h X (by simp [DerivationTree.nodeCategories_binary, hX])
    · exact w.atoms names
        (fun Y hY => h Y (by simp [DerivationTree.nodeCategories_binary, hY]))
        X hX
    · exact h X (by simp [DerivationTree.nodeCategories_binary, hX])

/-- Congruence: reduce inside the right premise of a binary rule. -/
def underBinaryRight {Γ Δ : List Category} {A B C : Category}
    (t₁ : DerivationTree Γ A) {t₂ : DerivationTree Δ B} (r : Rule A B C)
    (w : SizeReduction t₂) :
    SizeReduction (DerivationTree.binary t₁ t₂ r) where
  target := DerivationTree.binary t₁ w.target r
  size_lt := by
    have := w.size_lt
    simp only [DerivationTree.size_binary]
    omega
  atoms := by
    intro names h X hX
    simp only [DerivationTree.nodeCategories_binary, List.mem_cons, List.mem_append] at hX
    rcases hX with hX | hX | hX
    · exact h X (by simp [DerivationTree.nodeCategories_binary, hX])
    · exact h X (by simp [DerivationTree.nodeCategories_binary, hX])
    · exact w.atoms names
        (fun Y hY => h Y (by simp [DerivationTree.nodeCategories_binary, hY]))
        X hX

end SizeReduction

/-! ## Leaf trees have only visible occurrences -/

/-- Every occurrence of a leaf tree is visible: its only valid node address is
the root. -/
theorem Occurrence.visible_of_leaf {A : Category}
    (o : Occurrence (DerivationTree.leaf A)) : o.Visible := by
  left
  change o.nodePath = []
  cases hnp : o.nodePath with
  | nil => rfl
  | cons d p =>
      have h := o.nodeAt
      rw [hnp] at h
      simp [DerivationTree.categoryAt?] at h

/-! ## Node-path shapes -/

/-- Occurrences of a unary-rooted tree live at the root or under the premise. -/
theorem Occurrence.nodePath_shape_typeRaiseRight
    {Γ : List Category} {A C : Category} {u : DerivationTree Γ A}
    (o : Occurrence (DerivationTree.typeRaiseRight C u)) :
    o.nodePath = [] ∨ ∃ p, o.nodePath = .unary :: p := by
  cases hnp : o.nodePath with
  | nil => exact Or.inl rfl
  | cons d p =>
      cases d with
      | unary => exact Or.inr ⟨p, rfl⟩
      | left =>
          have h := o.nodeAt
          rw [hnp] at h
          simp [DerivationTree.categoryAt?] at h
      | right =>
          have h := o.nodeAt
          rw [hnp] at h
          simp [DerivationTree.categoryAt?] at h

/-- Occurrences of a unary-rooted tree live at the root or under the premise. -/
theorem Occurrence.nodePath_shape_typeRaiseLeft
    {Γ : List Category} {A C : Category} {u : DerivationTree Γ A}
    (o : Occurrence (DerivationTree.typeRaiseLeft C u)) :
    o.nodePath = [] ∨ ∃ p, o.nodePath = .unary :: p := by
  cases hnp : o.nodePath with
  | nil => exact Or.inl rfl
  | cons d p =>
      cases d with
      | unary => exact Or.inr ⟨p, rfl⟩
      | left =>
          have h := o.nodeAt
          rw [hnp] at h
          simp [DerivationTree.categoryAt?] at h
      | right =>
          have h := o.nodeAt
          rw [hnp] at h
          simp [DerivationTree.categoryAt?] at h

/-- Occurrences of a binary-rooted tree live at the root or under a premise. -/
theorem Occurrence.nodePath_shape_binary
    {Γ Δ : List Category} {A B C : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ B} {r : Rule A B C}
    (o : Occurrence (DerivationTree.binary t₁ t₂ r)) :
    o.nodePath = [] ∨ (∃ p, o.nodePath = .left :: p) ∨ ∃ p, o.nodePath = .right :: p := by
  cases hnp : o.nodePath with
  | nil => exact Or.inl rfl
  | cons d p =>
      cases d with
      | unary =>
          have h := o.nodeAt
          rw [hnp] at h
          simp [DerivationTree.categoryAt?] at h
      | left => exact Or.inr (Or.inl ⟨p, rfl⟩)
      | right => exact Or.inr (Or.inr ⟨p, rfl⟩)

/-! ## Restriction of occurrences to a premise subtree -/

/-- Restrict an occurrence under a forward type raise to the premise. -/
def Occurrence.unUnaryRight
    {Γ : List Category} {A C : Category} {u : DerivationTree Γ A}
    (o : Occurrence (DerivationTree.typeRaiseRight C u)) (p : NodePath)
    (hnp : o.nodePath = .unary :: p) : Occurrence u where
  nodePath := p
  nodeCategory := o.nodeCategory
  nodeAt := by have h := o.nodeAt; rw [hnp] at h; exact h
  categoryPath := o.categoryPath
  isConstructor := o.isConstructor

@[simp]
theorem Occurrence.underUnaryRight_unUnaryRight
    {Γ : List Category} {A C : Category} {u : DerivationTree Γ A}
    (o : Occurrence (DerivationTree.typeRaiseRight C u)) (p : NodePath)
    (hnp : o.nodePath = .unary :: p) :
    (o.unUnaryRight p hnp).underUnaryRight C = o := by
  apply DerivationTree.CategoryOccurrence.eq_of_data
  · exact hnp.symm
  · rfl
  · rfl

/-- Restrict an occurrence under a backward type raise to the premise. -/
def Occurrence.unUnaryLeft
    {Γ : List Category} {A C : Category} {u : DerivationTree Γ A}
    (o : Occurrence (DerivationTree.typeRaiseLeft C u)) (p : NodePath)
    (hnp : o.nodePath = .unary :: p) : Occurrence u where
  nodePath := p
  nodeCategory := o.nodeCategory
  nodeAt := by have h := o.nodeAt; rw [hnp] at h; exact h
  categoryPath := o.categoryPath
  isConstructor := o.isConstructor

@[simp]
theorem Occurrence.underUnaryLeft_unUnaryLeft
    {Γ : List Category} {A C : Category} {u : DerivationTree Γ A}
    (o : Occurrence (DerivationTree.typeRaiseLeft C u)) (p : NodePath)
    (hnp : o.nodePath = .unary :: p) :
    (o.unUnaryLeft p hnp).underUnaryLeft C = o := by
  apply DerivationTree.CategoryOccurrence.eq_of_data
  · exact hnp.symm
  · rfl
  · rfl

/-- Restrict an occurrence under a binary rule to the left premise. -/
def Occurrence.unBinaryLeft
    {Γ Δ : List Category} {A B C : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ B} {r : Rule A B C}
    (o : Occurrence (DerivationTree.binary t₁ t₂ r)) (p : NodePath)
    (hnp : o.nodePath = .left :: p) : Occurrence t₁ where
  nodePath := p
  nodeCategory := o.nodeCategory
  nodeAt := by have h := o.nodeAt; rw [hnp] at h; exact h
  categoryPath := o.categoryPath
  isConstructor := o.isConstructor

@[simp]
theorem Occurrence.underBinaryLeft_unBinaryLeft
    {Γ Δ : List Category} {A B C : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ B} {r : Rule A B C}
    (o : Occurrence (DerivationTree.binary t₁ t₂ r)) (p : NodePath)
    (hnp : o.nodePath = .left :: p) :
    (o.unBinaryLeft p hnp).underBinaryLeft r = o := by
  apply DerivationTree.CategoryOccurrence.eq_of_data
  · exact hnp.symm
  · rfl
  · rfl

/-- Restrict an occurrence under a binary rule to the right premise. -/
def Occurrence.unBinaryRight
    {Γ Δ : List Category} {A B C : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ B} {r : Rule A B C}
    (o : Occurrence (DerivationTree.binary t₁ t₂ r)) (p : NodePath)
    (hnp : o.nodePath = .right :: p) : Occurrence t₂ where
  nodePath := p
  nodeCategory := o.nodeCategory
  nodeAt := by have h := o.nodeAt; rw [hnp] at h; exact h
  categoryPath := o.categoryPath
  isConstructor := o.isConstructor

@[simp]
theorem Occurrence.underBinaryRight_unBinaryRight
    {Γ Δ : List Category} {A B C : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ B} {r : Rule A B C}
    (o : Occurrence (DerivationTree.binary t₁ t₂ r)) (p : NodePath)
    (hnp : o.nodePath = .right :: p) :
    (o.unBinaryRight p hnp).underBinaryRight r = o := by
  apply DerivationTree.CategoryOccurrence.eq_of_data
  · exact hnp.symm
  · rfl
  · rfl

/-! ## Injectivity of the occurrence liftings -/

theorem Occurrence.underUnaryRight_inj
    {Γ : List Category} {A C : Category} {u : DerivationTree Γ A}
    {a b : Occurrence u}
    (h : a.underUnaryRight C = b.underUnaryRight C) : a = b := by
  apply Occurrence.eq_of_key_eq
  have hn := congrArg DerivationTree.CategoryOccurrence.nodePath h
  have hp := congrArg DerivationTree.CategoryOccurrence.categoryPath h
  simp [DerivationTree.CategoryOccurrence.underUnaryRight] at hn
  simp [DerivationTree.CategoryOccurrence.underUnaryRight] at hp
  simp [Occurrence.key, hn, hp]

theorem Occurrence.underUnaryLeft_inj
    {Γ : List Category} {A C : Category} {u : DerivationTree Γ A}
    {a b : Occurrence u}
    (h : a.underUnaryLeft C = b.underUnaryLeft C) : a = b := by
  apply Occurrence.eq_of_key_eq
  have hn := congrArg DerivationTree.CategoryOccurrence.nodePath h
  have hp := congrArg DerivationTree.CategoryOccurrence.categoryPath h
  simp [DerivationTree.CategoryOccurrence.underUnaryLeft] at hn
  simp [DerivationTree.CategoryOccurrence.underUnaryLeft] at hp
  simp [Occurrence.key, hn, hp]

theorem Occurrence.underBinaryLeft_inj
    {Γ Δ : List Category} {A B C : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ B} {r : Rule A B C}
    {a b : Occurrence t₁}
    (h : a.underBinaryLeft (t₂ := t₂) r = b.underBinaryLeft (t₂ := t₂) r) : a = b := by
  apply Occurrence.eq_of_key_eq
  have hn := congrArg DerivationTree.CategoryOccurrence.nodePath h
  have hp := congrArg DerivationTree.CategoryOccurrence.categoryPath h
  simp [DerivationTree.CategoryOccurrence.underBinaryLeft] at hn
  simp [DerivationTree.CategoryOccurrence.underBinaryLeft] at hp
  simp [Occurrence.key, hn, hp]

theorem Occurrence.underBinaryRight_inj
    {Γ Δ : List Category} {A B C : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ B} {r : Rule A B C}
    {a b : Occurrence t₂}
    (h : a.underBinaryRight (t₁ := t₁) r = b.underBinaryRight (t₁ := t₁) r) : a = b := by
  apply Occurrence.eq_of_key_eq
  have hn := congrArg DerivationTree.CategoryOccurrence.nodePath h
  have hp := congrArg DerivationTree.CategoryOccurrence.categoryPath h
  simp [DerivationTree.CategoryOccurrence.underBinaryRight] at hn
  simp [DerivationTree.CategoryOccurrence.underBinaryRight] at hp
  simp [Occurrence.key, hn, hp]

/-! ## Visibility transfer between a tree and its premise subtrees

Leaf-ness is definitional along `under*`; principal constructors lift by the
congruence constructors and invert by `cases`; the root disjunct is where the
two sides genuinely differ.
-/

/-- Visibility descends from a lifted occurrence to the premise occurrence. -/
theorem Occurrence.visible_of_underUnaryRight_visible
    {Γ : List Category} {A C : Category} {u : DerivationTree Γ A}
    {b : Occurrence u}
    (h : (b.underUnaryRight C).Visible) : b.Visible := by
  rcases h with hroot | hleaf | hprin
  · exact absurd hroot (List.cons_ne_nil _ _)
  · exact Or.inr (Or.inl hleaf)
  · cases hprin with
    | underUnaryRight C h' => exact Or.inr (Or.inr h')

/-- Visibility descends from a lifted occurrence to the premise occurrence. -/
theorem Occurrence.visible_of_underUnaryLeft_visible
    {Γ : List Category} {A C : Category} {u : DerivationTree Γ A}
    {b : Occurrence u}
    (h : (b.underUnaryLeft C).Visible) : b.Visible := by
  rcases h with hroot | hleaf | hprin
  · exact absurd hroot (List.cons_ne_nil _ _)
  · exact Or.inr (Or.inl hleaf)
  · cases hprin with
    | underUnaryLeft C h' => exact Or.inr (Or.inr h')

/-- Invisibility lifts from a premise occurrence to the lifted occurrence. -/
theorem Occurrence.invisible_underUnaryRight
    {Γ : List Category} {A C : Category} {u : DerivationTree Γ A}
    {b : Occurrence u} (h : b.Invisible) :
    (b.underUnaryRight C).Invisible :=
  fun hvis => h (Occurrence.visible_of_underUnaryRight_visible hvis)

/-- Invisibility lifts from a premise occurrence to the lifted occurrence. -/
theorem Occurrence.invisible_underUnaryLeft
    {Γ : List Category} {A C : Category} {u : DerivationTree Γ A}
    {b : Occurrence u} (h : b.Invisible) :
    (b.underUnaryLeft C).Invisible :=
  fun hvis => h (Occurrence.visible_of_underUnaryLeft_visible hvis)

/-- Invisibility descends to a premise occurrence away from the premise root. -/
theorem Occurrence.invisible_of_underUnaryRight_invisible
    {Γ : List Category} {A C : Category} {u : DerivationTree Γ A}
    {b : Occurrence u} (hnp : b.nodePath ≠ [])
    (h : (b.underUnaryRight C).Invisible) : b.Invisible := by
  intro hvis
  apply h
  rcases hvis with hroot | hleaf | hprin
  · exact absurd hroot hnp
  · exact Or.inr (Or.inl hleaf)
  · exact Or.inr (Or.inr (DerivationTree.PrincipalConstructor.underUnaryRight C hprin))

/-- Invisibility descends to a premise occurrence away from the premise root. -/
theorem Occurrence.invisible_of_underUnaryLeft_invisible
    {Γ : List Category} {A C : Category} {u : DerivationTree Γ A}
    {b : Occurrence u} (hnp : b.nodePath ≠ [])
    (h : (b.underUnaryLeft C).Invisible) : b.Invisible := by
  intro hvis
  apply h
  rcases hvis with hroot | hleaf | hprin
  · exact absurd hroot hnp
  · exact Or.inr (Or.inl hleaf)
  · exact Or.inr (Or.inr (DerivationTree.PrincipalConstructor.underUnaryLeft C hprin))

/-- Invisibility descends to a left-premise occurrence away from the premise root. -/
theorem Occurrence.invisible_of_underBinaryLeft_invisible
    {Γ Δ : List Category} {A B C : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ B} {r : Rule A B C}
    {b : Occurrence t₁} (hnp : b.nodePath ≠ [])
    (h : (b.underBinaryLeft (t₂ := t₂) r).Invisible) : b.Invisible := by
  intro hvis
  apply h
  rcases hvis with hroot | hleaf | hprin
  · exact absurd hroot hnp
  · exact Or.inr (Or.inl hleaf)
  · exact Or.inr (Or.inr (DerivationTree.PrincipalConstructor.underBinaryLeft r hprin))

/-- Invisibility descends to a right-premise occurrence away from the premise root. -/
theorem Occurrence.invisible_of_underBinaryRight_invisible
    {Γ Δ : List Category} {A B C : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ B} {r : Rule A B C}
    {b : Occurrence t₂} (hnp : b.nodePath ≠ [])
    (h : (b.underBinaryRight (t₁ := t₁) r).Invisible) : b.Invisible := by
  intro hvis
  apply h
  rcases hvis with hroot | hleaf | hprin
  · exact absurd hroot hnp
  · exact Or.inr (Or.inl hleaf)
  · exact Or.inr (Or.inr (DerivationTree.PrincipalConstructor.underBinaryRight r hprin))

/-! ## Local trace edges live near the top of the tree

Every rule-local metavariable-copy half-edge has both endpoints at node
addresses of length at most one.  This single general-tree fact replaces all
constructor-by-constructor inversions of `LocalTraceEdge` at specialized trees
(which would otherwise require dependent elimination on the appended leaf-list
index of a binary node).
-/

theorem LocalTraceEdge.nodePath_length_le
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ : Occurrence t} (h : LocalTraceEdge o₁ o₂) :
    o₁.nodePath.length ≤ 1 ∧ o₂.nodePath.length ≤ 1 := by
  cases h <;>
  · rename_i h₁n h₁p h₂n h₂p
    rw [h₁n, h₂n]
    simp

/-! ## Trace-edge descent to a premise subtree

A trace edge incident to an occurrence strictly inside a premise subtree is
the lift of a trace edge of that subtree.
-/

theorem TraceEdge.descend_unaryRight
    {Γ : List Category} {A C : Category} {u : DerivationTree Γ A}
    {x y : Occurrence (DerivationTree.typeRaiseRight C u)}
    {a : Occurrence u}
    (hx : x = a.underUnaryRight C) (ha : a.nodePath ≠ [])
    (hedge : TraceEdge x y) :
    ∃ b : Occurrence u, y = b.underUnaryRight C ∧ TraceEdge a b := by
  have hlen : 2 ≤ x.nodePath.length := by
    rw [hx]
    change 2 ≤ (TreeStep.unary :: a.nodePath).length
    cases hnp : a.nodePath with
    | nil => exact absurd hnp ha
    | cons _ _ => simp
  rcases hedge with hd | hd
  · rcases hd with hl | ⟨a', b', h', h1, h2⟩
    · have := hl.nodePath_length_le.1
      omega
    · have haa : a' = a :=
        Occurrence.underUnaryRight_inj (h1.symm.trans hx)
      subst haa
      exact ⟨b', h2, Or.inl h'⟩
  · rcases hd with hl | ⟨a', b', h', h1, h2⟩
    · have := hl.nodePath_length_le.2
      omega
    · have hbb : b' = a :=
        Occurrence.underUnaryRight_inj (h2.symm.trans hx)
      subst hbb
      exact ⟨a', h1, Or.inr h'⟩

theorem TraceEdge.descend_unaryLeft
    {Γ : List Category} {A C : Category} {u : DerivationTree Γ A}
    {x y : Occurrence (DerivationTree.typeRaiseLeft C u)}
    {a : Occurrence u}
    (hx : x = a.underUnaryLeft C) (ha : a.nodePath ≠ [])
    (hedge : TraceEdge x y) :
    ∃ b : Occurrence u, y = b.underUnaryLeft C ∧ TraceEdge a b := by
  have hlen : 2 ≤ x.nodePath.length := by
    rw [hx]
    change 2 ≤ (TreeStep.unary :: a.nodePath).length
    cases hnp : a.nodePath with
    | nil => exact absurd hnp ha
    | cons _ _ => simp
  rcases hedge with hd | hd
  · rcases hd with hl | ⟨a', b', h', h1, h2⟩
    · have := hl.nodePath_length_le.1
      omega
    · have haa : a' = a :=
        Occurrence.underUnaryLeft_inj (h1.symm.trans hx)
      subst haa
      exact ⟨b', h2, Or.inl h'⟩
  · rcases hd with hl | ⟨a', b', h', h1, h2⟩
    · have := hl.nodePath_length_le.2
      omega
    · have hbb : b' = a :=
        Occurrence.underUnaryLeft_inj (h2.symm.trans hx)
      subst hbb
      exact ⟨a', h1, Or.inr h'⟩

theorem TraceEdge.descend_binaryLeft
    {Γ Δ : List Category} {A B C : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ B} {r : Rule A B C}
    {x y : Occurrence (DerivationTree.binary t₁ t₂ r)}
    {a : Occurrence t₁}
    (hx : x = a.underBinaryLeft r) (ha : a.nodePath ≠ [])
    (hedge : TraceEdge x y) :
    ∃ b : Occurrence t₁, y = b.underBinaryLeft r ∧ TraceEdge a b := by
  have hlen : 2 ≤ x.nodePath.length := by
    rw [hx]
    change 2 ≤ (TreeStep.left :: a.nodePath).length
    cases hnp : a.nodePath with
    | nil => exact absurd hnp ha
    | cons _ _ => simp
  rcases hedge with hd | hd
  · rcases hd with hl | ⟨a', b', h', h1, h2⟩ | ⟨a', b', h', h1, h2⟩
    · have := hl.nodePath_length_le.1
      omega
    · have haa : a' = a :=
        Occurrence.underBinaryLeft_inj (h1.symm.trans hx)
      subst haa
      exact ⟨b', h2, Or.inl h'⟩
    · exfalso
      have hpaths := congrArg DerivationTree.CategoryOccurrence.nodePath (h1.symm.trans hx)
      simp [DerivationTree.CategoryOccurrence.underBinaryLeft,
        DerivationTree.CategoryOccurrence.underBinaryRight] at hpaths
  · rcases hd with hl | ⟨a', b', h', h1, h2⟩ | ⟨a', b', h', h1, h2⟩
    · have := hl.nodePath_length_le.2
      omega
    · have hbb : b' = a :=
        Occurrence.underBinaryLeft_inj (h2.symm.trans hx)
      subst hbb
      exact ⟨a', h1, Or.inr h'⟩
    · exfalso
      have hpaths := congrArg DerivationTree.CategoryOccurrence.nodePath (h2.symm.trans hx)
      simp [DerivationTree.CategoryOccurrence.underBinaryLeft,
        DerivationTree.CategoryOccurrence.underBinaryRight] at hpaths

theorem TraceEdge.descend_binaryRight
    {Γ Δ : List Category} {A B C : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ B} {r : Rule A B C}
    {x y : Occurrence (DerivationTree.binary t₁ t₂ r)}
    {a : Occurrence t₂}
    (hx : x = a.underBinaryRight r) (ha : a.nodePath ≠ [])
    (hedge : TraceEdge x y) :
    ∃ b : Occurrence t₂, y = b.underBinaryRight r ∧ TraceEdge a b := by
  have hlen : 2 ≤ x.nodePath.length := by
    rw [hx]
    change 2 ≤ (TreeStep.right :: a.nodePath).length
    cases hnp : a.nodePath with
    | nil => exact absurd hnp ha
    | cons _ _ => simp
  rcases hedge with hd | hd
  · rcases hd with hl | ⟨a', b', h', h1, h2⟩ | ⟨a', b', h', h1, h2⟩
    · have := hl.nodePath_length_le.1
      omega
    · exfalso
      have hpaths := congrArg DerivationTree.CategoryOccurrence.nodePath (h1.symm.trans hx)
      simp [DerivationTree.CategoryOccurrence.underBinaryLeft,
        DerivationTree.CategoryOccurrence.underBinaryRight] at hpaths
    · have haa : a' = a :=
        Occurrence.underBinaryRight_inj (h1.symm.trans hx)
      subst haa
      exact ⟨b', h2, Or.inl h'⟩
  · rcases hd with hl | ⟨a', b', h', h1, h2⟩ | ⟨a', b', h', h1, h2⟩
    · have := hl.nodePath_length_le.2
      omega
    · exfalso
      have hpaths := congrArg DerivationTree.CategoryOccurrence.nodePath (h2.symm.trans hx)
      simp [DerivationTree.CategoryOccurrence.underBinaryLeft,
        DerivationTree.CategoryOccurrence.underBinaryRight] at hpaths
    · have hbb : b' = a :=
        Occurrence.underBinaryRight_inj (h2.symm.trans hx)
      subst hbb
      exact ⟨a', h1, Or.inr h'⟩

/-! ## A recursive characterization of type-raising skeleton positions

`UnarySkeletonConstructor` is an inductive family over the tree; inverting it
at a binary node would require dependent elimination on the appended leaf-list
index.  The recursive `skeletonAt` below is definitionally invertible instead.
-/

/-- Skeleton positions, by recursion on the tree. -/
def DerivationTree.skeletonAt : {Γ : List Category} → {A : Category} →
    DerivationTree Γ A → NodePath → CategoryPath → Prop
  | _, _, .leaf _, _, _ => False
  | _, _, .typeRaiseRight _ _, [], cpos => cpos = [] ∨ cpos = [true]
  | _, _, .typeRaiseRight _ t, .unary :: p, cpos => t.skeletonAt p cpos
  | _, _, .typeRaiseRight _ _, .left :: _, _ => False
  | _, _, .typeRaiseRight _ _, .right :: _, _ => False
  | _, _, .typeRaiseLeft _ _, [], cpos => cpos = [] ∨ cpos = [false]
  | _, _, .typeRaiseLeft _ t, .unary :: p, cpos => t.skeletonAt p cpos
  | _, _, .typeRaiseLeft _ _, .left :: _, _ => False
  | _, _, .typeRaiseLeft _ _, .right :: _, _ => False
  | _, _, .binary t₁ _ _, .left :: p, cpos => t₁.skeletonAt p cpos
  | _, _, .binary _ t₂ _, .right :: p, cpos => t₂.skeletonAt p cpos
  | _, _, .binary _ _ _, [], _ => False
  | _, _, .binary _ _ _, .unary :: _, _ => False

theorem DerivationTree.skeletonAt_of_unarySkeletonConstructor
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {np : NodePath} {cpos : CategoryPath}
    (h : DerivationTree.UnarySkeletonConstructor t np cpos) :
    t.skeletonAt np cpos := by
  induction h with
  | trRight_outer t => exact Or.inl rfl
  | trRight_inner t => exact Or.inr rfl
  | trLeft_outer t => exact Or.inl rfl
  | trLeft_inner t => exact Or.inr rfl
  | underUnaryRight C h ih => exact ih
  | underUnaryLeft C h ih => exact ih
  | underBinaryLeft r h ih => exact ih
  | underBinaryRight r h ih => exact ih

theorem DerivationTree.unarySkeletonConstructor_of_skeletonAt :
    {Γ : List Category} → {A : Category} → (t : DerivationTree Γ A) →
      (np : NodePath) → (cpos : CategoryPath) → t.skeletonAt np cpos →
        DerivationTree.UnarySkeletonConstructor t np cpos
  | _, _, .leaf _, _, _, h => h.elim
  | _, _, .typeRaiseRight C t, [], _, h => by
      rcases h with h | h
      · subst h; exact .trRight_outer t
      · subst h; exact .trRight_inner t
  | _, _, .typeRaiseRight C t, .unary :: p, cpos, h =>
      .underUnaryRight C (unarySkeletonConstructor_of_skeletonAt t p cpos h)
  | _, _, .typeRaiseRight _ _, .left :: _, _, h => h.elim
  | _, _, .typeRaiseRight _ _, .right :: _, _, h => h.elim
  | _, _, .typeRaiseLeft C t, [], _, h => by
      rcases h with h | h
      · subst h; exact .trLeft_outer t
      · subst h; exact .trLeft_inner t
  | _, _, .typeRaiseLeft C t, .unary :: p, cpos, h =>
      .underUnaryLeft C (unarySkeletonConstructor_of_skeletonAt t p cpos h)
  | _, _, .typeRaiseLeft _ _, .left :: _, _, h => h.elim
  | _, _, .typeRaiseLeft _ _, .right :: _, _, h => h.elim
  | _, _, .binary t₁ _ r, .left :: p, cpos, h =>
      .underBinaryLeft r (unarySkeletonConstructor_of_skeletonAt t₁ p cpos h)
  | _, _, .binary _ t₂ r, .right :: p, cpos, h =>
      .underBinaryRight r (unarySkeletonConstructor_of_skeletonAt t₂ p cpos h)
  | _, _, .binary _ _ _, [], _, h => h.elim
  | _, _, .binary _ _ _, .unary :: _, _, h => h.elim

/-! ## A boundary-free piece cannot touch the premise root of a root type raise

The premise-root occurrences sit inside the `A`-metavariable copy of the root
instance `A ↦ C/(A\C)` (resp. `A ↦ (C/A)\C`), so they are trace-linked to the
corresponding occurrence inside the conclusion — which lives at the tree root
and is therefore visible.
-/

/-- A boundary-free piece of a `T>`-rooted tree does not touch the premise root. -/
theorem InvisiblePiece.not_premiseRoot_of_typeRaiseRight
    {Γ : List Category} {A C : Category} {u : DerivationTree Γ A}
    {P : InvisiblePiece (DerivationTree.typeRaiseRight C u)}
    (hfree : BoundaryFree P)
    {o : Occurrence (DerivationTree.typeRaiseRight C u)}
    (ho : o ∈ P.carrier) :
    o.nodePath ≠ [.unary] := by
  intro hnp
  have hcatA : o.nodeCategory = A := by
    have h := o.nodeAt
    rw [hnp] at h
    have h' : A = o.nodeCategory := by
      simpa [DerivationTree.categoryAt?] using h
    exact h'.symm
  obtain ⟨X, Y, hXY⟩ := o.isConstructor
  have hconsRoot : ∃ X Y,
      (C ⧸ (A ⧹ C)).subcategoryAt? (true :: false :: o.categoryPath) = some (X ⧸ Y) ∨
      (C ⧸ (A ⧹ C)).subcategoryAt? (true :: false :: o.categoryPath) = some (X ⧹ Y) := by
    refine ⟨X, Y, ?_⟩
    simpa [hcatA] using hXY
  let o' : Occurrence (DerivationTree.typeRaiseRight C u) :=
    { nodePath := []
      nodeCategory := C ⧸ (A ⧹ C)
      nodeAt := rfl
      categoryPath := true :: false :: o.categoryPath
      isConstructor := hconsRoot }
  have hedge : TraceEdge o o' :=
    Or.inl (Or.inl (LocalTraceEdge.trRight_A (p := o.categoryPath) hnp rfl rfl rfl))
  have hvis : o'.Visible := Or.inl rfl
  exact hfree o ho o' hvis hedge

/-- A boundary-free piece of a `T<`-rooted tree does not touch the premise root. -/
theorem InvisiblePiece.not_premiseRoot_of_typeRaiseLeft
    {Γ : List Category} {A C : Category} {u : DerivationTree Γ A}
    {P : InvisiblePiece (DerivationTree.typeRaiseLeft C u)}
    (hfree : BoundaryFree P)
    {o : Occurrence (DerivationTree.typeRaiseLeft C u)}
    (ho : o ∈ P.carrier) :
    o.nodePath ≠ [.unary] := by
  intro hnp
  have hcatA : o.nodeCategory = A := by
    have h := o.nodeAt
    rw [hnp] at h
    have h' : A = o.nodeCategory := by
      simpa [DerivationTree.categoryAt?] using h
    exact h'.symm
  obtain ⟨X, Y, hXY⟩ := o.isConstructor
  have hconsRoot : ∃ X Y,
      ((C ⧸ A) ⧹ C).subcategoryAt? (false :: true :: o.categoryPath) = some (X ⧸ Y) ∨
      ((C ⧸ A) ⧹ C).subcategoryAt? (false :: true :: o.categoryPath) = some (X ⧹ Y) := by
    refine ⟨X, Y, ?_⟩
    simpa [hcatA] using hXY
  let o' : Occurrence (DerivationTree.typeRaiseLeft C u) :=
    { nodePath := []
      nodeCategory := (C ⧸ A) ⧹ C
      nodeAt := rfl
      categoryPath := false :: true :: o.categoryPath
      isConstructor := hconsRoot }
  have hedge : TraceEdge o o' :=
    Or.inl (Or.inl (LocalTraceEdge.trLeft_A (p := o.categoryPath) hnp rfl rfl rfl))
  have hvis : o'.Visible := Or.inl rfl
  exact hfree o ho o' hvis hedge

/-! ## Restricting a boundary-free skeleton piece to the premise of a root type raise -/

/-- A boundary-free piece with a skeleton occurrence in a `T>`-rooted tree
restricts to a boundary-free piece with a skeleton occurrence in the premise
subtree. -/
theorem InvisiblePiece.restrict_typeRaiseRight
    {Γ : List Category} {A C : Category} {u : DerivationTree Γ A}
    (P : InvisiblePiece (DerivationTree.typeRaiseRight C u))
    (hfree : BoundaryFree P)
    {o₀ : Occurrence (DerivationTree.typeRaiseRight C u)}
    (ho₀ : o₀ ∈ P.carrier) (hsk₀ : o₀.ProtectedUnarySkeleton) :
    ∃ P' : InvisiblePiece u, BoundaryFree P' ∧
      ∃ b : Occurrence u, b ∈ P'.carrier ∧ b.ProtectedUnarySkeleton := by
  classical
  -- every carrier occurrence lies strictly inside the premise subtree
  have hshape : ∀ o : Occurrence (DerivationTree.typeRaiseRight C u), o ∈ P.carrier →
      ∃ p, o.nodePath = TreeStep.unary :: p ∧ p ≠ [] := by
    intro o ho
    rcases o.nodePath_shape_typeRaiseRight with hnil | ⟨p, hp⟩
    · exact absurd (Or.inl hnil) (P.all_invisible o ho)
    · refine ⟨p, hp, ?_⟩
      intro hpnil
      exact InvisiblePiece.not_premiseRoot_of_typeRaiseRight hfree ho (by rw [hp, hpnil])
  -- restricted carrier
  let carrier' : List (Occurrence u) :=
    u.occurrences.filter
      (fun b => decide (Occurrence.key (b.underUnaryRight C) ∈ P.carrier.map Occurrence.key))
  have hmem : ∀ b : Occurrence u, b ∈ carrier' ↔ b.underUnaryRight C ∈ P.carrier := by
    intro b
    constructor
    · intro hb
      have h2 := of_decide_eq_true (List.mem_filter.mp hb).2
      obtain ⟨o, ho, hok⟩ := List.mem_map.mp h2
      exact (Occurrence.eq_of_key_eq hok) ▸ ho
    · intro hb
      exact List.mem_filter.mpr ⟨DerivationTree.occurrence_mem_occurrences b,
        decide_eq_true (List.mem_map.mpr ⟨_, hb, rfl⟩)⟩
  -- restricted occurrences sit at nonempty premise node paths
  have hnp_ne : ∀ b : Occurrence u, b.underUnaryRight C ∈ P.carrier → b.nodePath ≠ [] := by
    intro b hb hnil
    obtain ⟨p, hp, hpne⟩ := hshape _ hb
    rw [show (b.underUnaryRight C).nodePath = TreeStep.unary :: b.nodePath from rfl, hnil] at hp
    injection hp with _ h2
    exact hpne h2.symm
  have hinv' : ∀ b : Occurrence u, b.underUnaryRight C ∈ P.carrier → b.Invisible := by
    intro b hb
    exact Occurrence.invisible_of_underUnaryRight_invisible (hnp_ne b hb)
      (P.all_invisible _ hb)
  -- invisible-edge descent along the carrier
  have hinvDescend : ∀ {x y : Occurrence (DerivationTree.typeRaiseRight C u)},
      x ∈ P.carrier → ∀ {a : Occurrence u}, x = a.underUnaryRight C →
        InvisibleTraceEdge x y →
        ∃ b, y = b.underUnaryRight C ∧ InvisibleTraceEdge a b ∧ y ∈ P.carrier := by
    intro x y hx a hxa hedge
    have hyP : y ∈ P.carrier := P.closed x hx y hedge
    have hanp : a.nodePath ≠ [] := by
      intro hnil
      exact hnp_ne a (hxa ▸ hx) hnil
    obtain ⟨b, hyb, hab⟩ := TraceEdge.descend_unaryRight hxa hanp hedge.traceEdge
    have hainv : a.Invisible := hinv' a (hxa ▸ hx)
    have hbinv : b.Invisible := hinv' b (hyb ▸ hyP)
    exact ⟨b, hyb, ⟨hainv, hbinv, hab⟩, hyP⟩
  -- component descent along the carrier
  have hcompDescend : ∀ {x y : Occurrence (DerivationTree.typeRaiseRight C u)},
      x ∈ P.carrier → SameInvisibleTraceComponent x y →
        ∀ {a : Occurrence u}, x = a.underUnaryRight C →
          ∃ b, y = b.underUnaryRight C ∧ SameInvisibleTraceComponent a b ∧ y ∈ P.carrier := by
    intro x y hx hpath
    induction hpath with
    | refl =>
        intro a hxa
        exact ⟨a, hxa, SameInvisibleTraceComponent.refl _, hx⟩
    | tail hp hedge ih =>
        intro a hxa
        obtain ⟨m, hym, hcomp, hmP⟩ := ih hxa
        obtain ⟨b, hyb, hedge', hyP⟩ := hinvDescend hmP hym hedge
        exact ⟨b, hyb, Relation.ReflTransGen.tail hcomp hedge', hyP⟩
  -- skeleton witness restricts
  obtain ⟨p₀, hp₀, _⟩ := hshape o₀ ho₀
  have hb₀mem : o₀.unUnaryRight p₀ hp₀ ∈ carrier' := by
    rw [hmem, Occurrence.underUnaryRight_unUnaryRight]
    exact ho₀
  have hskAt := DerivationTree.skeletonAt_of_unarySkeletonConstructor hsk₀
  rw [hp₀] at hskAt
  have hskb : DerivationTree.UnarySkeletonConstructor u p₀ o₀.categoryPath :=
    DerivationTree.unarySkeletonConstructor_of_skeletonAt u p₀ _ hskAt
  -- assemble the restricted piece
  refine ⟨{
    carrier := carrier'
    nonempty := List.ne_nil_of_mem hb₀mem
    all_invisible := by
      intro b hb
      exact hinv' b ((hmem b).mp hb)
    connected := by
      intro b₁ hb₁ b₂ hb₂
      have h₁ := (hmem b₁).mp hb₁
      have h₂ := (hmem b₂).mp hb₂
      obtain ⟨b, hyb, hcomp, _⟩ :=
        hcompDescend h₁ (P.connected _ h₁ _ h₂) rfl
      have : b = b₂ := Occurrence.underUnaryRight_inj hyb.symm
      exact this ▸ hcomp
    closed := by
      intro b₁ hb₁ b₂ hedge
      have h₁ := (hmem b₁).mp hb₁
      have hlift : TraceEdge (b₁.underUnaryRight C) (b₂.underUnaryRight C) :=
        TraceEdge.underUnaryRight C hedge.traceEdge
      by_cases hv : (b₂.underUnaryRight C).Visible
      · exact absurd hlift (hfree _ h₁ _ hv)
      · have h₂ : b₂.underUnaryRight C ∈ P.carrier :=
          P.closed _ h₁ _ ⟨P.all_invisible _ h₁, hv, hlift⟩
        exact (hmem b₂).mpr h₂ }, ?_, ?_⟩
  · -- boundary-freeness of the restriction
    intro b hb v hvis hedge
    have hbP := (hmem b).mp hb
    have hlift : TraceEdge (b.underUnaryRight C) (v.underUnaryRight C) :=
      TraceEdge.underUnaryRight C hedge
    by_cases hv : (v.underUnaryRight C).Visible
    · exact hfree _ hbP _ hv hlift
    · have hvP : v.underUnaryRight C ∈ P.carrier :=
        P.closed _ hbP _ ⟨P.all_invisible _ hbP, hv, hlift⟩
      have hvnp : v.nodePath ≠ [] := hnp_ne v hvP
      rcases hvis with hroot | hleaf | hprin
      · exact hvnp hroot
      · exact hv (Or.inr (Or.inl hleaf))
      · exact hv (Or.inr (Or.inr (DerivationTree.PrincipalConstructor.underUnaryRight C hprin)))
  · exact ⟨o₀.unUnaryRight p₀ hp₀, hb₀mem, hskb⟩

/-- A boundary-free piece with a skeleton occurrence in a `T<`-rooted tree
restricts to a boundary-free piece with a skeleton occurrence in the premise
subtree. -/
theorem InvisiblePiece.restrict_typeRaiseLeft
    {Γ : List Category} {A C : Category} {u : DerivationTree Γ A}
    (P : InvisiblePiece (DerivationTree.typeRaiseLeft C u))
    (hfree : BoundaryFree P)
    {o₀ : Occurrence (DerivationTree.typeRaiseLeft C u)}
    (ho₀ : o₀ ∈ P.carrier) (hsk₀ : o₀.ProtectedUnarySkeleton) :
    ∃ P' : InvisiblePiece u, BoundaryFree P' ∧
      ∃ b : Occurrence u, b ∈ P'.carrier ∧ b.ProtectedUnarySkeleton := by
  classical
  have hshape : ∀ o : Occurrence (DerivationTree.typeRaiseLeft C u), o ∈ P.carrier →
      ∃ p, o.nodePath = TreeStep.unary :: p ∧ p ≠ [] := by
    intro o ho
    rcases o.nodePath_shape_typeRaiseLeft with hnil | ⟨p, hp⟩
    · exact absurd (Or.inl hnil) (P.all_invisible o ho)
    · refine ⟨p, hp, ?_⟩
      intro hpnil
      exact InvisiblePiece.not_premiseRoot_of_typeRaiseLeft hfree ho (by rw [hp, hpnil])
  let carrier' : List (Occurrence u) :=
    u.occurrences.filter
      (fun b => decide (Occurrence.key (b.underUnaryLeft C) ∈ P.carrier.map Occurrence.key))
  have hmem : ∀ b : Occurrence u, b ∈ carrier' ↔ b.underUnaryLeft C ∈ P.carrier := by
    intro b
    constructor
    · intro hb
      have h2 := of_decide_eq_true (List.mem_filter.mp hb).2
      obtain ⟨o, ho, hok⟩ := List.mem_map.mp h2
      exact (Occurrence.eq_of_key_eq hok) ▸ ho
    · intro hb
      exact List.mem_filter.mpr ⟨DerivationTree.occurrence_mem_occurrences b,
        decide_eq_true (List.mem_map.mpr ⟨_, hb, rfl⟩)⟩
  have hnp_ne : ∀ b : Occurrence u, b.underUnaryLeft C ∈ P.carrier → b.nodePath ≠ [] := by
    intro b hb hnil
    obtain ⟨p, hp, hpne⟩ := hshape _ hb
    rw [show (b.underUnaryLeft C).nodePath = TreeStep.unary :: b.nodePath from rfl, hnil] at hp
    injection hp with _ h2
    exact hpne h2.symm
  have hinv' : ∀ b : Occurrence u, b.underUnaryLeft C ∈ P.carrier → b.Invisible := by
    intro b hb
    exact Occurrence.invisible_of_underUnaryLeft_invisible (hnp_ne b hb)
      (P.all_invisible _ hb)
  have hinvDescend : ∀ {x y : Occurrence (DerivationTree.typeRaiseLeft C u)},
      x ∈ P.carrier → ∀ {a : Occurrence u}, x = a.underUnaryLeft C →
        InvisibleTraceEdge x y →
        ∃ b, y = b.underUnaryLeft C ∧ InvisibleTraceEdge a b ∧ y ∈ P.carrier := by
    intro x y hx a hxa hedge
    have hyP : y ∈ P.carrier := P.closed x hx y hedge
    have hanp : a.nodePath ≠ [] := by
      intro hnil
      exact hnp_ne a (hxa ▸ hx) hnil
    obtain ⟨b, hyb, hab⟩ := TraceEdge.descend_unaryLeft hxa hanp hedge.traceEdge
    have hainv : a.Invisible := hinv' a (hxa ▸ hx)
    have hbinv : b.Invisible := hinv' b (hyb ▸ hyP)
    exact ⟨b, hyb, ⟨hainv, hbinv, hab⟩, hyP⟩
  have hcompDescend : ∀ {x y : Occurrence (DerivationTree.typeRaiseLeft C u)},
      x ∈ P.carrier → SameInvisibleTraceComponent x y →
        ∀ {a : Occurrence u}, x = a.underUnaryLeft C →
          ∃ b, y = b.underUnaryLeft C ∧ SameInvisibleTraceComponent a b ∧ y ∈ P.carrier := by
    intro x y hx hpath
    induction hpath with
    | refl =>
        intro a hxa
        exact ⟨a, hxa, SameInvisibleTraceComponent.refl _, hx⟩
    | tail hp hedge ih =>
        intro a hxa
        obtain ⟨m, hym, hcomp, hmP⟩ := ih hxa
        obtain ⟨b, hyb, hedge', hyP⟩ := hinvDescend hmP hym hedge
        exact ⟨b, hyb, Relation.ReflTransGen.tail hcomp hedge', hyP⟩
  obtain ⟨p₀, hp₀, _⟩ := hshape o₀ ho₀
  have hb₀mem : o₀.unUnaryLeft p₀ hp₀ ∈ carrier' := by
    rw [hmem, Occurrence.underUnaryLeft_unUnaryLeft]
    exact ho₀
  have hskAt := DerivationTree.skeletonAt_of_unarySkeletonConstructor hsk₀
  rw [hp₀] at hskAt
  have hskb : DerivationTree.UnarySkeletonConstructor u p₀ o₀.categoryPath :=
    DerivationTree.unarySkeletonConstructor_of_skeletonAt u p₀ _ hskAt
  refine ⟨{
    carrier := carrier'
    nonempty := List.ne_nil_of_mem hb₀mem
    all_invisible := by
      intro b hb
      exact hinv' b ((hmem b).mp hb)
    connected := by
      intro b₁ hb₁ b₂ hb₂
      have h₁ := (hmem b₁).mp hb₁
      have h₂ := (hmem b₂).mp hb₂
      obtain ⟨b, hyb, hcomp, _⟩ :=
        hcompDescend h₁ (P.connected _ h₁ _ h₂) rfl
      have : b = b₂ := Occurrence.underUnaryLeft_inj hyb.symm
      exact this ▸ hcomp
    closed := by
      intro b₁ hb₁ b₂ hedge
      have h₁ := (hmem b₁).mp hb₁
      have hlift : TraceEdge (b₁.underUnaryLeft C) (b₂.underUnaryLeft C) :=
        TraceEdge.underUnaryLeft C hedge.traceEdge
      by_cases hv : (b₂.underUnaryLeft C).Visible
      · exact absurd hlift (hfree _ h₁ _ hv)
      · have h₂ : b₂.underUnaryLeft C ∈ P.carrier :=
          P.closed _ h₁ _ ⟨P.all_invisible _ h₁, hv, hlift⟩
        exact (hmem b₂).mpr h₂ }, ?_, ?_⟩
  · intro b hb v hvis hedge
    have hbP := (hmem b).mp hb
    have hlift : TraceEdge (b.underUnaryLeft C) (v.underUnaryLeft C) :=
      TraceEdge.underUnaryLeft C hedge
    by_cases hv : (v.underUnaryLeft C).Visible
    · exact hfree _ hbP _ hv hlift
    · have hvP : v.underUnaryLeft C ∈ P.carrier :=
        P.closed _ hbP _ ⟨P.all_invisible _ hbP, hv, hlift⟩
      have hvnp : v.nodePath ≠ [] := hnp_ne v hvP
      rcases hvis with hroot | hleaf | hprin
      · exact hvnp hroot
      · exact hv (Or.inr (Or.inl hleaf))
      · exact hv (Or.inr (Or.inr (DerivationTree.PrincipalConstructor.underUnaryLeft C hprin)))
  · exact ⟨o₀.unUnaryLeft p₀ hp₀, hb₀mem, hskb⟩

/-! ## Restricting a non-crossing boundary-free skeleton piece to a binary premise -/

/-- A boundary-free skeleton piece of a binary-rooted tree that does not touch
either premise root restricts to the left premise, if its skeleton witness is
on the left. -/
theorem InvisiblePiece.restrict_binaryLeft
    {Γ Δ : List Category} {A B C : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ B} {r : Rule A B C}
    (P : InvisiblePiece (DerivationTree.binary t₁ t₂ r))
    (hfree : BoundaryFree P)
    (hnocross : ∀ o : Occurrence (DerivationTree.binary t₁ t₂ r), o ∈ P.carrier →
      o.nodePath ≠ [TreeStep.left] ∧ o.nodePath ≠ [TreeStep.right])
    {o₀ : Occurrence (DerivationTree.binary t₁ t₂ r)}
    (ho₀ : o₀ ∈ P.carrier) (hsk₀ : o₀.ProtectedUnarySkeleton)
    {p₀ : NodePath} (hp₀ : o₀.nodePath = TreeStep.left :: p₀) :
    ∃ P' : InvisiblePiece t₁, BoundaryFree P' ∧
      ∃ b : Occurrence t₁, b ∈ P'.carrier ∧ b.ProtectedUnarySkeleton := by
  classical
  let carrier' : List (Occurrence t₁) :=
    t₁.occurrences.filter
      (fun b => decide (Occurrence.key (b.underBinaryLeft (t₂ := t₂) r) ∈ P.carrier.map Occurrence.key))
  have hmem : ∀ b : Occurrence t₁, b ∈ carrier' ↔ b.underBinaryLeft (t₂ := t₂) r ∈ P.carrier := by
    intro b
    constructor
    · intro hb
      have h2 := of_decide_eq_true (List.mem_filter.mp hb).2
      obtain ⟨o, ho, hok⟩ := List.mem_map.mp h2
      exact (Occurrence.eq_of_key_eq hok) ▸ ho
    · intro hb
      exact List.mem_filter.mpr ⟨DerivationTree.occurrence_mem_occurrences b,
        decide_eq_true (List.mem_map.mpr ⟨_, hb, rfl⟩)⟩
  have hnp_ne : ∀ b : Occurrence t₁, b.underBinaryLeft (t₂ := t₂) r ∈ P.carrier → b.nodePath ≠ [] := by
    intro b hb hnil
    have h := (hnocross _ hb).1
    apply h
    rw [show (b.underBinaryLeft (t₂ := t₂) r).nodePath = TreeStep.left :: b.nodePath from rfl, hnil]
  have hinv' : ∀ b : Occurrence t₁, b.underBinaryLeft (t₂ := t₂) r ∈ P.carrier → b.Invisible := by
    intro b hb
    exact Occurrence.invisible_of_underBinaryLeft_invisible (hnp_ne b hb)
      (P.all_invisible _ hb)
  have hinvDescend : ∀ {x y : Occurrence (DerivationTree.binary t₁ t₂ r)},
      x ∈ P.carrier → ∀ {a : Occurrence t₁}, x = a.underBinaryLeft (t₂ := t₂) r →
        InvisibleTraceEdge x y →
        ∃ b, y = b.underBinaryLeft (t₂ := t₂) r ∧ InvisibleTraceEdge a b ∧ y ∈ P.carrier := by
    intro x y hx a hxa hedge
    have hyP : y ∈ P.carrier := P.closed x hx y hedge
    have hanp : a.nodePath ≠ [] := by
      intro hnil
      exact hnp_ne a (hxa ▸ hx) hnil
    obtain ⟨b, hyb, hab⟩ := TraceEdge.descend_binaryLeft hxa hanp hedge.traceEdge
    have hainv : a.Invisible := hinv' a (hxa ▸ hx)
    have hbinv : b.Invisible := hinv' b (hyb ▸ hyP)
    exact ⟨b, hyb, ⟨hainv, hbinv, hab⟩, hyP⟩
  have hcompDescend : ∀ {x y : Occurrence (DerivationTree.binary t₁ t₂ r)},
      x ∈ P.carrier → SameInvisibleTraceComponent x y →
        ∀ {a : Occurrence t₁}, x = a.underBinaryLeft (t₂ := t₂) r →
          ∃ b, y = b.underBinaryLeft (t₂ := t₂) r ∧ SameInvisibleTraceComponent a b ∧ y ∈ P.carrier := by
    intro x y hx hpath
    induction hpath with
    | refl =>
        intro a hxa
        exact ⟨a, hxa, SameInvisibleTraceComponent.refl _, hx⟩
    | tail hp hedge ih =>
        intro a hxa
        obtain ⟨m, hym, hcomp, hmP⟩ := ih hxa
        obtain ⟨b, hyb, hedge', hyP⟩ := hinvDescend hmP hym hedge
        exact ⟨b, hyb, Relation.ReflTransGen.tail hcomp hedge', hyP⟩
  have hb₀mem : o₀.unBinaryLeft p₀ hp₀ ∈ carrier' := by
    rw [hmem, Occurrence.underBinaryLeft_unBinaryLeft]
    exact ho₀
  have hskAt := DerivationTree.skeletonAt_of_unarySkeletonConstructor hsk₀
  rw [hp₀] at hskAt
  have hskb : DerivationTree.UnarySkeletonConstructor t₁ p₀ o₀.categoryPath :=
    DerivationTree.unarySkeletonConstructor_of_skeletonAt t₁ p₀ _ hskAt
  refine ⟨{
    carrier := carrier'
    nonempty := List.ne_nil_of_mem hb₀mem
    all_invisible := by
      intro b hb
      exact hinv' b ((hmem b).mp hb)
    connected := by
      intro b₁ hb₁ b₂ hb₂
      have h₁ := (hmem b₁).mp hb₁
      have h₂ := (hmem b₂).mp hb₂
      obtain ⟨b, hyb, hcomp, _⟩ :=
        hcompDescend h₁ (P.connected _ h₁ _ h₂) rfl
      have : b = b₂ := Occurrence.underBinaryLeft_inj hyb.symm
      exact this ▸ hcomp
    closed := by
      intro b₁ hb₁ b₂ hedge
      have h₁ := (hmem b₁).mp hb₁
      have hlift : TraceEdge (b₁.underBinaryLeft (t₂ := t₂) r) (b₂.underBinaryLeft (t₂ := t₂) r) :=
        TraceEdge.underBinaryLeft r hedge.traceEdge
      by_cases hv : (b₂.underBinaryLeft (t₂ := t₂) r).Visible
      · exact absurd hlift (hfree _ h₁ _ hv)
      · have h₂ : b₂.underBinaryLeft (t₂ := t₂) r ∈ P.carrier :=
          P.closed _ h₁ _ ⟨P.all_invisible _ h₁, hv, hlift⟩
        exact (hmem b₂).mpr h₂ }, ?_, ?_⟩
  · intro b hb v hvis hedge
    have hbP := (hmem b).mp hb
    have hlift : TraceEdge (b.underBinaryLeft (t₂ := t₂) r) (v.underBinaryLeft (t₂ := t₂) r) :=
      TraceEdge.underBinaryLeft r hedge
    by_cases hv : (v.underBinaryLeft (t₂ := t₂) r).Visible
    · exact hfree _ hbP _ hv hlift
    · have hvP : v.underBinaryLeft (t₂ := t₂) r ∈ P.carrier :=
        P.closed _ hbP _ ⟨P.all_invisible _ hbP, hv, hlift⟩
      have hvnp : v.nodePath ≠ [] := hnp_ne v hvP
      rcases hvis with hroot | hleaf | hprin
      · exact hvnp hroot
      · exact hv (Or.inr (Or.inl hleaf))
      · exact hv (Or.inr (Or.inr (DerivationTree.PrincipalConstructor.underBinaryLeft r hprin)))
  · exact ⟨o₀.unBinaryLeft p₀ hp₀, hb₀mem, hskb⟩

/-- A boundary-free skeleton piece of a binary-rooted tree that does not touch
either premise root restricts to the right premise, if its skeleton witness is
on the right. -/
theorem InvisiblePiece.restrict_binaryRight
    {Γ Δ : List Category} {A B C : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ B} {r : Rule A B C}
    (P : InvisiblePiece (DerivationTree.binary t₁ t₂ r))
    (hfree : BoundaryFree P)
    (hnocross : ∀ o : Occurrence (DerivationTree.binary t₁ t₂ r), o ∈ P.carrier →
      o.nodePath ≠ [TreeStep.left] ∧ o.nodePath ≠ [TreeStep.right])
    {o₀ : Occurrence (DerivationTree.binary t₁ t₂ r)}
    (ho₀ : o₀ ∈ P.carrier) (hsk₀ : o₀.ProtectedUnarySkeleton)
    {p₀ : NodePath} (hp₀ : o₀.nodePath = TreeStep.right :: p₀) :
    ∃ P' : InvisiblePiece t₂, BoundaryFree P' ∧
      ∃ b : Occurrence t₂, b ∈ P'.carrier ∧ b.ProtectedUnarySkeleton := by
  classical
  let carrier' : List (Occurrence t₂) :=
    t₂.occurrences.filter
      (fun b => decide (Occurrence.key (b.underBinaryRight (t₁ := t₁) r) ∈ P.carrier.map Occurrence.key))
  have hmem : ∀ b : Occurrence t₂, b ∈ carrier' ↔ b.underBinaryRight (t₁ := t₁) r ∈ P.carrier := by
    intro b
    constructor
    · intro hb
      have h2 := of_decide_eq_true (List.mem_filter.mp hb).2
      obtain ⟨o, ho, hok⟩ := List.mem_map.mp h2
      exact (Occurrence.eq_of_key_eq hok) ▸ ho
    · intro hb
      exact List.mem_filter.mpr ⟨DerivationTree.occurrence_mem_occurrences b,
        decide_eq_true (List.mem_map.mpr ⟨_, hb, rfl⟩)⟩
  have hnp_ne : ∀ b : Occurrence t₂, b.underBinaryRight (t₁ := t₁) r ∈ P.carrier → b.nodePath ≠ [] := by
    intro b hb hnil
    have h := (hnocross _ hb).2
    apply h
    rw [show (b.underBinaryRight (t₁ := t₁) r).nodePath = TreeStep.right :: b.nodePath from rfl, hnil]
  have hinv' : ∀ b : Occurrence t₂, b.underBinaryRight (t₁ := t₁) r ∈ P.carrier → b.Invisible := by
    intro b hb
    exact Occurrence.invisible_of_underBinaryRight_invisible (hnp_ne b hb)
      (P.all_invisible _ hb)
  have hinvDescend : ∀ {x y : Occurrence (DerivationTree.binary t₁ t₂ r)},
      x ∈ P.carrier → ∀ {a : Occurrence t₂}, x = a.underBinaryRight (t₁ := t₁) r →
        InvisibleTraceEdge x y →
        ∃ b, y = b.underBinaryRight (t₁ := t₁) r ∧ InvisibleTraceEdge a b ∧ y ∈ P.carrier := by
    intro x y hx a hxa hedge
    have hyP : y ∈ P.carrier := P.closed x hx y hedge
    have hanp : a.nodePath ≠ [] := by
      intro hnil
      exact hnp_ne a (hxa ▸ hx) hnil
    obtain ⟨b, hyb, hab⟩ := TraceEdge.descend_binaryRight hxa hanp hedge.traceEdge
    have hainv : a.Invisible := hinv' a (hxa ▸ hx)
    have hbinv : b.Invisible := hinv' b (hyb ▸ hyP)
    exact ⟨b, hyb, ⟨hainv, hbinv, hab⟩, hyP⟩
  have hcompDescend : ∀ {x y : Occurrence (DerivationTree.binary t₁ t₂ r)},
      x ∈ P.carrier → SameInvisibleTraceComponent x y →
        ∀ {a : Occurrence t₂}, x = a.underBinaryRight (t₁ := t₁) r →
          ∃ b, y = b.underBinaryRight (t₁ := t₁) r ∧ SameInvisibleTraceComponent a b ∧ y ∈ P.carrier := by
    intro x y hx hpath
    induction hpath with
    | refl =>
        intro a hxa
        exact ⟨a, hxa, SameInvisibleTraceComponent.refl _, hx⟩
    | tail hp hedge ih =>
        intro a hxa
        obtain ⟨m, hym, hcomp, hmP⟩ := ih hxa
        obtain ⟨b, hyb, hedge', hyP⟩ := hinvDescend hmP hym hedge
        exact ⟨b, hyb, Relation.ReflTransGen.tail hcomp hedge', hyP⟩
  have hb₀mem : o₀.unBinaryRight p₀ hp₀ ∈ carrier' := by
    rw [hmem, Occurrence.underBinaryRight_unBinaryRight]
    exact ho₀
  have hskAt := DerivationTree.skeletonAt_of_unarySkeletonConstructor hsk₀
  rw [hp₀] at hskAt
  have hskb : DerivationTree.UnarySkeletonConstructor t₂ p₀ o₀.categoryPath :=
    DerivationTree.unarySkeletonConstructor_of_skeletonAt t₂ p₀ _ hskAt
  refine ⟨{
    carrier := carrier'
    nonempty := List.ne_nil_of_mem hb₀mem
    all_invisible := by
      intro b hb
      exact hinv' b ((hmem b).mp hb)
    connected := by
      intro b₁ hb₁ b₂ hb₂
      have h₁ := (hmem b₁).mp hb₁
      have h₂ := (hmem b₂).mp hb₂
      obtain ⟨b, hyb, hcomp, _⟩ :=
        hcompDescend h₁ (P.connected _ h₁ _ h₂) rfl
      have : b = b₂ := Occurrence.underBinaryRight_inj hyb.symm
      exact this ▸ hcomp
    closed := by
      intro b₁ hb₁ b₂ hedge
      have h₁ := (hmem b₁).mp hb₁
      have hlift : TraceEdge (b₁.underBinaryRight (t₁ := t₁) r) (b₂.underBinaryRight (t₁ := t₁) r) :=
        TraceEdge.underBinaryRight r hedge.traceEdge
      by_cases hv : (b₂.underBinaryRight (t₁ := t₁) r).Visible
      · exact absurd hlift (hfree _ h₁ _ hv)
      · have h₂ : b₂.underBinaryRight (t₁ := t₁) r ∈ P.carrier :=
          P.closed _ h₁ _ ⟨P.all_invisible _ h₁, hv, hlift⟩
        exact (hmem b₂).mpr h₂ }, ?_, ?_⟩
  · intro b hb v hvis hedge
    have hbP := (hmem b).mp hb
    have hlift : TraceEdge (b.underBinaryRight (t₁ := t₁) r) (v.underBinaryRight (t₁ := t₁) r) :=
      TraceEdge.underBinaryRight r hedge
    by_cases hv : (v.underBinaryRight (t₁ := t₁) r).Visible
    · exact hfree _ hbP _ hv hlift
    · have hvP : v.underBinaryRight (t₁ := t₁) r ∈ P.carrier :=
        P.closed _ hbP _ ⟨P.all_invisible _ hbP, hv, hlift⟩
      have hvnp : v.nodePath ≠ [] := hnp_ne v hvP
      rcases hvis with hroot | hleaf | hprin
      · exact hvnp hroot
      · exact hv (Or.inr (Or.inl hleaf))
      · exact hv (Or.inr (Or.inr (DerivationTree.PrincipalConstructor.underBinaryRight r hprin)))
  · exact ⟨o₀.unBinaryRight p₀ hp₀, hb₀mem, hskb⟩

/-! ## The main reduction: everything except the crossing case -/

/-- **The remaining crossing case.**  A boundary-free skeleton-carrying piece
that touches a premise root of the root binary rule yields a strictly smaller
derivation of the same sequent.

The conclusion must be a `SizeReduction`, not a single collapse redex: the
counterexample in the module docstring exhibits a crossing boundary-free
skeleton piece in a tree with no collapse redex at all, because the raised
layer is separated from its application by a composition.  The
direct-cancellation instances (`T>` feeding `>`, `T<` feeding `<`) and, more
generally, every composition spine ending in a type raise
(`sizeReduction_appRight_of_compSpineRight`,
`sizeReduction_appLeft_of_compSpineLeft` below) are proved; the open content
is deriving the cancellation shape from the piece structure. -/
def CrossingBoundaryFreeSkeletonPieceReduces : Prop :=
  ∀ {Γ Δ : List Category} {A B C : Category}
    (t₁ : DerivationTree Γ A) (t₂ : DerivationTree Δ B) (r : Rule A B C)
    (P : InvisiblePiece (DerivationTree.binary t₁ t₂ r)),
    BoundaryFree P →
    (∃ o : Occurrence (DerivationTree.binary t₁ t₂ r), o ∈ P.carrier ∧ o.ProtectedUnarySkeleton) →
    (∃ o : Occurrence (DerivationTree.binary t₁ t₂ r), o ∈ P.carrier ∧
      (o.nodePath = [TreeStep.left] ∨ o.nodePath = [TreeStep.right])) →
    Nonempty (SizeReduction (DerivationTree.binary t₁ t₂ r))

/-- **Reduction to the crossing case.**  Assuming the crossing case, every
derivation tree carrying a boundary-free invisible piece that contains a
type-raising skeleton occurrence admits a size reduction. -/
theorem sizeReduction_of_boundaryFree_skeleton_piece
    (hcross : CrossingBoundaryFreeSkeletonPieceReduces) :
    ∀ {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
      (P : InvisiblePiece t), BoundaryFree P →
      (∃ o : Occurrence t, o ∈ P.carrier ∧ o.ProtectedUnarySkeleton) →
      Nonempty (SizeReduction t) := by
  intro Γ A t
  induction t with
  | leaf A =>
      intro P _ _
      obtain ⟨o, ho⟩ := List.exists_mem_of_ne_nil P.carrier P.nonempty
      exact absurd (Occurrence.visible_of_leaf o) (P.all_invisible o ho)
  | typeRaiseRight C u ih =>
      intro P hfree hsk
      obtain ⟨o₀, ho₀, hsk₀⟩ := hsk
      obtain ⟨P', hfree', b, hb, hskb⟩ := P.restrict_typeRaiseRight hfree ho₀ hsk₀
      obtain ⟨w⟩ := ih P' hfree' ⟨b, hb, hskb⟩
      exact ⟨w.underTypeRaiseRight C⟩
  | typeRaiseLeft C u ih =>
      intro P hfree hsk
      obtain ⟨o₀, ho₀, hsk₀⟩ := hsk
      obtain ⟨P', hfree', b, hb, hskb⟩ := P.restrict_typeRaiseLeft hfree ho₀ hsk₀
      obtain ⟨w⟩ := ih P' hfree' ⟨b, hb, hskb⟩
      exact ⟨w.underTypeRaiseLeft C⟩
  | binary t₁ t₂ r ih₁ ih₂ =>
      intro P hfree hsk
      by_cases hcrossing : ∃ o : Occurrence (DerivationTree.binary t₁ t₂ r),
          o ∈ P.carrier ∧ (o.nodePath = [TreeStep.left] ∨ o.nodePath = [TreeStep.right])
      · exact hcross t₁ t₂ r P hfree hsk hcrossing
      · have hnocross : ∀ o : Occurrence (DerivationTree.binary t₁ t₂ r), o ∈ P.carrier →
            o.nodePath ≠ [TreeStep.left] ∧ o.nodePath ≠ [TreeStep.right] := by
          intro o ho
          constructor
          · intro h
            exact hcrossing ⟨o, ho, Or.inl h⟩
          · intro h
            exact hcrossing ⟨o, ho, Or.inr h⟩
        obtain ⟨o₀, ho₀, hsk₀⟩ := hsk
        rcases o₀.nodePath_shape_binary with hnil | ⟨p₀, hp₀⟩ | ⟨p₀, hp₀⟩
        · exact absurd (Or.inl hnil) (P.all_invisible o₀ ho₀)
        · obtain ⟨P', hfree', b, hb, hskb⟩ :=
            P.restrict_binaryLeft hfree hnocross ho₀ hsk₀ hp₀
          obtain ⟨w⟩ := ih₁ P' hfree' ⟨b, hb, hskb⟩
          exact ⟨w.underBinaryLeft t₂ r⟩
        · obtain ⟨P', hfree', b, hb, hskb⟩ :=
            P.restrict_binaryRight hfree hnocross ho₀ hsk₀ hp₀
          obtain ⟨w⟩ := ih₂ P' hfree' ⟨b, hb, hskb⟩
          exact ⟨w.underBinaryRight t₁ r⟩

/-- **The protected-skeleton obligation, reduced to the crossing case.** -/
theorem boundaryFreeProtectedSkeletonPieceContracts_of_crossing
    (hcross : CrossingBoundaryFreeSkeletonPieceReduces) :
    BoundaryFreeProtectedSkeletonPieceContracts := by
  intro Γ A t hatoms P hfree hsk
  obtain ⟨w⟩ := sizeReduction_of_boundaryFree_skeleton_piece hcross P hfree hsk
  exact ⟨w.toContractionWitness⟩

/-! ## Composed cancellation: composition spines ending in a type raise

The family that refutes the collapse-redex formulation is proved here for the
corrected one.  A *forward composition spine* is a functor of the shape
`x₁ ∘ (x₂ ∘ ( … ∘ T>_{C₀}(u)))`; applying it forward to an argument of the
raised slot `A₀ ⧹ C₀` contracts to a cascade of plain applications, deleting
the raised layer at every spine node simultaneously.  This is the
transport-closed band deletion in the special case where the transported
positions lie along one composition spine.
-/

/-- Transport a derivation tree along an equality of leaf lists. -/
def DerivationTree.castLeaves {Γ Γ' : List Category} {A : Category}
    (h : Γ = Γ') (t : DerivationTree Γ A) : DerivationTree Γ' A :=
  h ▸ t

@[simp]
theorem DerivationTree.size_castLeaves {Γ Γ' : List Category} {A : Category}
    (h : Γ = Γ') (t : DerivationTree Γ A) :
    (t.castLeaves h).size = t.size := by
  subst h
  rfl

@[simp]
theorem DerivationTree.nodeCategories_castLeaves {Γ Γ' : List Category} {A : Category}
    (h : Γ = Γ') (t : DerivationTree Γ A) :
    (t.castLeaves h).nodeCategories = t.nodeCategories := by
  subst h
  rfl

/-- The root category of a tree is among its node categories. -/
private theorem root_mem_nodeCategories' {Γ : List Category} {A : Category}
    (t : DerivationTree Γ A) : A ∈ t.nodeCategories := by
  cases t <;> simp [DerivationTree.nodeCategories]

/-- A right spine of forward compositions ending in a forward type raise with
target `C₀` over raised category `A₀`.  Every category on the spine has the
raised argument slot `A₀ ⧹ C₀`. -/
inductive CompSpineRight (A₀ C₀ : Category) :
    {Γ : List Category} → {C : Category} →
      DerivationTree Γ (C ⧸ (A₀ ⧹ C₀)) → Prop where
  | raise {Γ : List Category} (u : DerivationTree Γ A₀) :
      CompSpineRight A₀ C₀ (DerivationTree.typeRaiseRight C₀ u)
  | comp {Γ₁ Γ₂ : List Category} {C' B : Category}
      (x : DerivationTree Γ₁ (C' ⧸ B)) {G : DerivationTree Γ₂ (B ⧸ (A₀ ⧹ C₀))}
      (hG : CompSpineRight A₀ C₀ G) :
      CompSpineRight A₀ C₀ (DerivationTree.binary x G Rule.compRight)

/-- **Spine collapse.**  Applying a forward composition spine to an argument of
its raised slot contracts to a cascade of applications: the contractum saves at
least the raised slot's constructors plus one, and introduces no new atoms. -/
theorem CompSpineRight.collapse {A₀ C₀ : Category} :
    ∀ {Γ : List Category} {C : Category} {F : DerivationTree Γ (C ⧸ (A₀ ⧹ C₀))},
      CompSpineRight A₀ C₀ F →
      ∀ {Δ : List Category} (z : DerivationTree Δ (A₀ ⧹ C₀)),
      ∃ t' : DerivationTree (Γ ++ Δ) C,
        t'.size + (A₀ ⧹ C₀).constructors + 1 ≤ F.size + z.size ∧
        ∀ atomNames : List String,
          (∀ B ∈ F.nodeCategories, UsesOnlyAtoms atomNames B) →
          (∀ B ∈ z.nodeCategories, UsesOnlyAtoms atomNames B) →
          ∀ B ∈ t'.nodeCategories, UsesOnlyAtoms atomNames B := by
  intro Γ C F h
  induction h with
  | raise u =>
      intro Δ z
      refine ⟨DerivationTree.binary u z Rule.appLeft, ?_, ?_⟩
      · simp only [DerivationTree.size_binary, DerivationTree.size_typeRaiseRight,
          Category.constructors]
        omega
      · intro names hF hz B hB
        simp only [DerivationTree.nodeCategories_binary, List.mem_cons,
          List.mem_append] at hB
        rcases hB with hB | hB | hB
        · -- the new application node carries the raise target, a subcategory of the raise output
          subst hB
          have hout := hF _ (by
            rw [DerivationTree.nodeCategories_typeRaiseRight]
            exact List.mem_cons_self)
          exact hout.rdiv_left
        · exact hF B (by simp [DerivationTree.nodeCategories_typeRaiseRight, hB])
        · exact hz B hB
  | @comp Γ₁ Γ₂ _ B₁ x G hG ih =>
      intro Δ z
      obtain ⟨G', hsize, hatoms⟩ := ih z
      refine ⟨(DerivationTree.binary x G' Rule.appRight).castLeaves
        (List.append_assoc Γ₁ Γ₂ Δ).symm, ?_, ?_⟩
      · rw [DerivationTree.size_castLeaves]
        simp only [DerivationTree.size_binary, Category.constructors] at hsize ⊢
        omega
      · intro names hF hz B hB
        rw [DerivationTree.nodeCategories_castLeaves] at hB
        simp only [DerivationTree.nodeCategories_binary, List.mem_cons,
          List.mem_append] at hB
        rcases hB with hB | hB | hB
        · -- the new application node carries `x`'s numerator, a subcategory of `x`'s root
          subst hB
          have hx := hF _ (by
            simp only [DerivationTree.nodeCategories_binary, List.mem_cons,
              List.mem_append]
            exact Or.inr (Or.inl (root_mem_nodeCategories' x)))
          exact hx.rdiv_left
        · exact hF B (by
            simp only [DerivationTree.nodeCategories_binary, List.mem_cons,
              List.mem_append]
            exact Or.inr (Or.inl hB))
        · refine hatoms names ?_ hz B hB
          intro Y hY
          exact hF Y (by
            simp only [DerivationTree.nodeCategories_binary, List.mem_cons,
              List.mem_append]
            exact Or.inr (Or.inr hY))


/-- Delete only the raised layer at the end of a forward composition spine whose
raised category is itself `C₀ ⧸ A₀`, preserving the spine leaves and changing
the final argument slot from `(C₀ ⧸ A₀) ⧹ C₀` to `A₀`.

This is the order-preserving component needed by crossed `appRight` diamonds:
the argument that cancels the lowered slot may occur after an intervening
`crossedLeft` premise, so the ordinary `CompSpineRight.collapse` would put the
leaves in the wrong order. -/
theorem CompSpineRight.lowerRaisedSlot {A₀ C₀ : Category} :
    ∀ {Γ : List Category} {C : Category}
      {F : DerivationTree Γ (C ⧸ ((C₀ ⧸ A₀) ⧹ C₀))},
      CompSpineRight (C₀ ⧸ A₀) C₀ F →
      ∃ F' : DerivationTree Γ (C ⧸ A₀),
        F'.size < F.size ∧
        ∀ atomNames : List String,
          (∀ B ∈ F.nodeCategories, UsesOnlyAtoms atomNames B) →
          ∀ B ∈ F'.nodeCategories, UsesOnlyAtoms atomNames B := by
  intro Γ C F h
  induction h with
  | raise u =>
      refine ⟨u, ?_, ?_⟩
      · simp only [DerivationTree.size_typeRaiseRight, Category.constructors]
        omega
      · intro names hF B hB
        exact hF B (by simp [DerivationTree.nodeCategories_typeRaiseRight, hB])
  | @comp Γ₁ Γ₂ C' B x G hG ih =>
      obtain ⟨G', hsize, hatoms⟩ := ih
      refine ⟨DerivationTree.binary x G' Rule.compRight, ?_, ?_⟩
      · simp only [DerivationTree.size_binary, Category.constructors] at hsize ⊢
        omega
      · intro names hF Y hY
        simp only [DerivationTree.nodeCategories_binary, List.mem_cons, List.mem_append] at hY
        rcases hY with hroot | hx | hG'
        · subst hroot
          have hxRoot : UsesOnlyAtoms names (C' ⧸ B) := hF (C' ⧸ B) (by
            simp only [DerivationTree.nodeCategories_binary, List.mem_cons, List.mem_append]
            exact Or.inr (Or.inl (root_mem_nodeCategories' x)))
          have hGRoot : UsesOnlyAtoms names (B ⧸ A₀) := hatoms names (by
            intro Z hZ
            exact hF Z (by
              simp only [DerivationTree.nodeCategories_binary, List.mem_cons, List.mem_append]
              exact Or.inr (Or.inr hZ))) (B ⧸ A₀) (root_mem_nodeCategories' G')
          exact UsesOnlyAtoms.rdiv hxRoot.rdiv_left hGRoot.rdiv_right
        · exact hF Y (by
            simp only [DerivationTree.nodeCategories_binary, List.mem_cons, List.mem_append]
            exact Or.inr (Or.inl hx))
        · refine hatoms names ?_ Y hG'
          intro Z hZ
          exact hF Z (by
            simp only [DerivationTree.nodeCategories_binary, List.mem_cons, List.mem_append]
            exact Or.inr (Or.inr hZ))

/-- Order-preserving crossed cancellation for a forward composition spine feeding
the left premise of `crossedLeft` and a backward type raise consumed by the
surrounding `appRight`.

This generalizes `sizeReduction_appRight_of_crossedLeft_typeRaises`: the
forward raise may be hidden under a `compRight` spine before it meets the
crossed rule, while the intervening crossed premise keeps its original position
in the leaf list. -/
theorem sizeReduction_appRight_of_crossedLeft_compSpineRight
    {A₀ C₀ C D : Category} {Γ Δ Θ : List Category}
    {F : DerivationTree Γ (D ⧸ ((C₀ ⧸ A₀) ⧹ C₀))}
    (hF : CompSpineRight (C₀ ⧸ A₀) C₀ F)
    (y : DerivationTree Δ (D ⧹ C)) (z : DerivationTree Θ A₀) :
    Nonempty (SizeReduction
      (DerivationTree.binary (DerivationTree.binary F y Rule.crossedLeft)
        (DerivationTree.typeRaiseLeft C₀ z) Rule.appRight)) := by
  obtain ⟨F', hsizeF, hatomsF⟩ := hF.lowerRaisedSlot
  refine ⟨{
    target := DerivationTree.binary (DerivationTree.binary F' y Rule.crossedLeft) z Rule.appRight
    size_lt := by
      simp only [DerivationTree.size_binary, DerivationTree.size_typeRaiseLeft,
        Category.constructors] at hsizeF ⊢
      omega
    atoms := ?_ }⟩
  intro names h X hX
  simp only [DerivationTree.nodeCategories_binary, List.mem_cons, List.mem_append] at hX
  rcases hX with hroot | hleft | hright
  · subst hroot
    exact h _ (by simp [DerivationTree.nodeCategories_binary])
  · rcases hleft with hinnerRoot | hF' | hy
    · subst hinnerRoot
      have hC : UsesOnlyAtoms names C := h C (by simp [DerivationTree.nodeCategories_binary])
      have hA₀ : UsesOnlyAtoms names A₀ := by
        have hzRoot : A₀ ∈ z.nodeCategories := by
          cases z <;> simp [DerivationTree.nodeCategories]
        exact h A₀ (by
          simp [DerivationTree.nodeCategories_binary, DerivationTree.nodeCategories_typeRaiseLeft,
            hzRoot])
      exact UsesOnlyAtoms.rdiv hC hA₀
    · refine hatomsF names ?_ X hF'
      intro W hW
      exact h W (by
        simp [DerivationTree.nodeCategories_binary, DerivationTree.nodeCategories_typeRaiseLeft, hW])
    · exact h X (by
        simp [DerivationTree.nodeCategories_binary, DerivationTree.nodeCategories_typeRaiseLeft, hy])
  · exact h X (by
      simp [DerivationTree.nodeCategories_binary, DerivationTree.nodeCategories_typeRaiseLeft, hright])

/-- The corrected crossing conclusion holds for every forward composition
spine applied to its raised slot.  For a spine of length zero this is exactly
the `collapseRight` redex; for longer spines no single collapse redex exists,
and the reduction deletes the raised layer along the whole spine. -/
theorem sizeReduction_appRight_of_compSpineRight
    {A₀ C₀ : Category} {Γ Δ : List Category} {C : Category}
    {F : DerivationTree Γ (C ⧸ (A₀ ⧹ C₀))}
    (hF : CompSpineRight A₀ C₀ F) (z : DerivationTree Δ (A₀ ⧹ C₀)) :
    Nonempty (SizeReduction (DerivationTree.binary F z Rule.appRight)) := by
  obtain ⟨t', hsize, hatoms⟩ := hF.collapse z
  refine ⟨{
    target := t'
    size_lt := by
      simp only [DerivationTree.size_binary]
      omega
    atoms := ?_ }⟩
  intro names h B hB
  refine hatoms names ?_ ?_ B hB
  · intro Y hY
    exact h Y (by
      simp only [DerivationTree.nodeCategories_binary, List.mem_cons, List.mem_append]
      exact Or.inr (Or.inl hY))
  · intro Y hY
    exact h Y (by
      simp only [DerivationTree.nodeCategories_binary, List.mem_cons, List.mem_append]
      exact Or.inr (Or.inr hY))

/-- A left spine of backward compositions ending in a backward type raise with
target `C₀` over raised category `A₀`.  Mirror of `CompSpineRight`. -/
inductive CompSpineLeft (A₀ C₀ : Category) :
    {Γ : List Category} → {C : Category} →
      DerivationTree Γ ((C₀ ⧸ A₀) ⧹ C) → Prop where
  | raise {Γ : List Category} (u : DerivationTree Γ A₀) :
      CompSpineLeft A₀ C₀ (DerivationTree.typeRaiseLeft C₀ u)
  | comp {Γ₁ Γ₂ : List Category} {C' B : Category}
      {G : DerivationTree Γ₁ ((C₀ ⧸ A₀) ⧹ B)} (y : DerivationTree Γ₂ (B ⧹ C'))
      (hG : CompSpineLeft A₀ C₀ G) :
      CompSpineLeft A₀ C₀ (DerivationTree.binary G y Rule.compLeft)

/-- **Spine collapse (mirror).**  Applying an argument of the raised slot to a
backward composition spine contracts to a cascade of applications. -/
theorem CompSpineLeft.collapse {A₀ C₀ : Category} :
    ∀ {Γ : List Category} {C : Category} {F : DerivationTree Γ ((C₀ ⧸ A₀) ⧹ C)},
      CompSpineLeft A₀ C₀ F →
      ∀ {Δ : List Category} (w : DerivationTree Δ (C₀ ⧸ A₀)),
      ∃ t' : DerivationTree (Δ ++ Γ) C,
        t'.size + (C₀ ⧸ A₀).constructors + 1 ≤ w.size + F.size ∧
        ∀ atomNames : List String,
          (∀ B ∈ F.nodeCategories, UsesOnlyAtoms atomNames B) →
          (∀ B ∈ w.nodeCategories, UsesOnlyAtoms atomNames B) →
          ∀ B ∈ t'.nodeCategories, UsesOnlyAtoms atomNames B := by
  intro Γ C F h
  induction h with
  | raise u =>
      intro Δ w
      refine ⟨DerivationTree.binary w u Rule.appRight, ?_, ?_⟩
      · simp only [DerivationTree.size_binary, DerivationTree.size_typeRaiseLeft,
          Category.constructors]
        omega
      · intro names hF hw B hB
        simp only [DerivationTree.nodeCategories_binary, List.mem_cons,
          List.mem_append] at hB
        rcases hB with hB | hB | hB
        · subst hB
          have hout := hF _ (by
            rw [DerivationTree.nodeCategories_typeRaiseLeft]
            exact List.mem_cons_self)
          exact hout.ldiv_right
        · exact hw B hB
        · exact hF B (by simp [DerivationTree.nodeCategories_typeRaiseLeft, hB])
  | @comp Γ₁ Γ₂ _ B₁ G y hG ih =>
      intro Δ w
      obtain ⟨G', hsize, hatoms⟩ := ih w
      refine ⟨(DerivationTree.binary G' y Rule.appLeft).castLeaves
        (List.append_assoc Δ Γ₁ Γ₂), ?_, ?_⟩
      · rw [DerivationTree.size_castLeaves]
        simp only [DerivationTree.size_binary, Category.constructors] at hsize ⊢
        omega
      · intro names hF hw B hB
        rw [DerivationTree.nodeCategories_castLeaves] at hB
        simp only [DerivationTree.nodeCategories_binary, List.mem_cons,
          List.mem_append] at hB
        rcases hB with hB | hB | hB
        · subst hB
          have hy := hF _ (by
            simp only [DerivationTree.nodeCategories_binary, List.mem_cons,
              List.mem_append]
            exact Or.inr (Or.inr (root_mem_nodeCategories' y)))
          exact hy.ldiv_right
        · refine hatoms names ?_ hw B hB
          intro Y hY
          exact hF Y (by
            simp only [DerivationTree.nodeCategories_binary, List.mem_cons,
              List.mem_append]
            exact Or.inr (Or.inl hY))
        · exact hF B (by
            simp only [DerivationTree.nodeCategories_binary, List.mem_cons,
              List.mem_append]
            exact Or.inr (Or.inr hB))


/-- Delete only the raised layer at the end of a backward composition spine
whose raised category is itself `A₀ ⧹ C₀`, preserving the spine leaves and
changing the fixed left slot from `C₀ ⧸ (A₀ ⧹ C₀)` to `A₀`.

This is the order-preserving mirror of `CompSpineRight.lowerRaisedSlot`, used
when a crossed `appLeft` diamond has an intervening `compLeft` spine. -/
theorem CompSpineLeft.lowerRaisedSlot {A₀ C₀ : Category} :
    ∀ {Γ : List Category} {C : Category}
      {F : DerivationTree Γ ((C₀ ⧸ (A₀ ⧹ C₀)) ⧹ C)},
      CompSpineLeft (A₀ ⧹ C₀) C₀ F →
      ∃ F' : DerivationTree Γ (A₀ ⧹ C),
        F'.size < F.size ∧
        ∀ atomNames : List String,
          (∀ B ∈ F.nodeCategories, UsesOnlyAtoms atomNames B) →
          ∀ B ∈ F'.nodeCategories, UsesOnlyAtoms atomNames B := by
  intro Γ C F h
  induction h with
  | raise u =>
      refine ⟨u, ?_, ?_⟩
      · simp only [DerivationTree.size_typeRaiseLeft, Category.constructors]
        omega
      · intro names hF B hB
        exact hF B (by simp [DerivationTree.nodeCategories_typeRaiseLeft, hB])
  | @comp Γ₁ Γ₂ C' B G y hG ih =>
      obtain ⟨G', hsize, hatoms⟩ := ih
      refine ⟨DerivationTree.binary G' y Rule.compLeft, ?_, ?_⟩
      · simp only [DerivationTree.size_binary, Category.constructors] at hsize ⊢
        omega
      · intro names hF Y hY
        simp only [DerivationTree.nodeCategories_binary, List.mem_cons, List.mem_append] at hY
        rcases hY with hroot | hG' | hy
        · subst hroot
          have hGRoot : UsesOnlyAtoms names (A₀ ⧹ B) := hatoms names (by
            intro Z hZ
            exact hF Z (by
              simp only [DerivationTree.nodeCategories_binary, List.mem_cons, List.mem_append]
              exact Or.inr (Or.inl hZ))) (A₀ ⧹ B) (root_mem_nodeCategories' G')
          have hyRoot : UsesOnlyAtoms names (B ⧹ C') := hF (B ⧹ C') (by
            simp only [DerivationTree.nodeCategories_binary, List.mem_cons, List.mem_append]
            exact Or.inr (Or.inr (root_mem_nodeCategories' y)))
          exact UsesOnlyAtoms.ldiv hGRoot.ldiv_left hyRoot.ldiv_right
        · refine hatoms names ?_ Y hG'
          intro Z hZ
          exact hF Z (by
            simp only [DerivationTree.nodeCategories_binary, List.mem_cons, List.mem_append]
            exact Or.inr (Or.inl hZ))
        · exact hF Y (by
            simp only [DerivationTree.nodeCategories_binary, List.mem_cons, List.mem_append]
            exact Or.inr (Or.inr hy))
/-- The corrected crossing conclusion holds for every backward composition
spine applied to its raised slot. -/
theorem sizeReduction_appLeft_of_compSpineLeft
    {A₀ C₀ : Category} {Γ Δ : List Category} {C : Category}
    {F : DerivationTree Γ ((C₀ ⧸ A₀) ⧹ C)}
    (hF : CompSpineLeft A₀ C₀ F) (w : DerivationTree Δ (C₀ ⧸ A₀)) :
    Nonempty (SizeReduction (DerivationTree.binary w F Rule.appLeft)) := by
  obtain ⟨t', hsize, hatoms⟩ := hF.collapse w
  refine ⟨{
    target := t'
    size_lt := by
      simp only [DerivationTree.size_binary]
      omega
    atoms := ?_ }⟩
  intro names h B hB
  refine hatoms names ?_ ?_ B hB
  · intro Y hY
    exact h Y (by
      simp only [DerivationTree.nodeCategories_binary, List.mem_cons, List.mem_append]
      exact Or.inr (Or.inr hY))
  · intro Y hY
    exact h Y (by
      simp only [DerivationTree.nodeCategories_binary, List.mem_cons, List.mem_append]
      exact Or.inr (Or.inl hY))

/-! ## Structure of a crossing piece under a root application

For a root forward application `C/B, B ⇒ C`, a boundary-free piece can enter
the premise roots only inside the canceled argument `B`: a left-premise
occurrence in the result part `false :: ·` is trace-linked to the visible tree
root, and the functor's root position `[]` is principal.  Moreover every
crossing occurrence carries its metavariable partner on the other premise
inside the piece.  Consequently:

* the canceled premise cannot be a leaf (its occurrences are visible);
* if the functor premise is a type raise, the root is a collapse redex
  (spine of length zero); the other type raise is impossible by typing.

So the crossing case of a root application is open **only when the functor
premise is binary-rooted**.  The mirror statements hold for `appLeft`.
-/

/-- Under a root `appRight`, a crossing occurrence on the functor side lies in
the argument part `true :: ·` of `C ⧸ B`. -/
theorem InvisiblePiece.appRight_left_in_argument
    {Γ Δ : List Category} {C B : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ B}
    {P : InvisiblePiece (DerivationTree.binary t₁ t₂ Rule.appRight)}
    (hfree : BoundaryFree P)
    {o : Occurrence (DerivationTree.binary t₁ t₂ Rule.appRight)}
    (ho : o ∈ P.carrier) (hnp : o.nodePath = [TreeStep.left]) :
    ∃ q, o.categoryPath = true :: q := by
  have hcat : o.nodeCategory = C ⧸ B := by
    have h := o.nodeAt
    rw [hnp] at h
    have h' : C ⧸ B = o.nodeCategory := by
      simpa [DerivationTree.categoryAt?] using h
    exact h'.symm
  cases hcp : o.categoryPath with
  | nil =>
      exfalso
      apply P.all_invisible o ho
      right; right
      rw [hnp, hcp]
      exact DerivationTree.PrincipalConstructor.appRight_left t₁ t₂
  | cons b q =>
      cases b with
      | true => exact ⟨q, rfl⟩
      | false =>
          exfalso
          obtain ⟨X, Y, hXY⟩ := o.isConstructor
          have hconsRoot : ∃ X Y,
              C.subcategoryAt? q = some (X ⧸ Y) ∨
              C.subcategoryAt? q = some (X ⧹ Y) := by
            refine ⟨X, Y, ?_⟩
            rw [hcat, hcp] at hXY
            simpa using hXY
          let o' : Occurrence (DerivationTree.binary t₁ t₂ Rule.appRight) :=
            { nodePath := []
              nodeCategory := C
              nodeAt := rfl
              categoryPath := q
              isConstructor := hconsRoot }
          have hedge : TraceEdge o o' :=
            Or.inl (Or.inl (LocalTraceEdge.appRight_C (p := q) hnp hcp rfl rfl))
          exact hfree o ho o' (Or.inl rfl) hedge

/-- Under a root `appRight`, a crossing occurrence on the argument side has its
metavariable partner on the functor side inside the piece. -/
theorem InvisiblePiece.appRight_partner_of_right
    {Γ Δ : List Category} {C B : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ B}
    {P : InvisiblePiece (DerivationTree.binary t₁ t₂ Rule.appRight)}
    (hfree : BoundaryFree P)
    {o : Occurrence (DerivationTree.binary t₁ t₂ Rule.appRight)}
    (ho : o ∈ P.carrier) (hnp : o.nodePath = [TreeStep.right]) :
    ∃ o' : Occurrence (DerivationTree.binary t₁ t₂ Rule.appRight),
      o' ∈ P.carrier ∧ o'.nodePath = [TreeStep.left] ∧
        o'.categoryPath = true :: o.categoryPath := by
  have hcat : o.nodeCategory = B := by
    have h := o.nodeAt
    rw [hnp] at h
    have h' : B = o.nodeCategory := by
      simpa [DerivationTree.categoryAt?] using h
    exact h'.symm
  obtain ⟨X, Y, hXY⟩ := o.isConstructor
  have hcons : ∃ X Y,
      (C ⧸ B).subcategoryAt? (true :: o.categoryPath) = some (X ⧸ Y) ∨
      (C ⧸ B).subcategoryAt? (true :: o.categoryPath) = some (X ⧹ Y) := by
    refine ⟨X, Y, ?_⟩
    rw [hcat] at hXY
    simpa using hXY
  let o' : Occurrence (DerivationTree.binary t₁ t₂ Rule.appRight) :=
    { nodePath := [TreeStep.left]
      nodeCategory := C ⧸ B
      nodeAt := by simp [DerivationTree.categoryAt?]
      categoryPath := true :: o.categoryPath
      isConstructor := hcons }
  have hedge : TraceEdge o o' :=
    Or.inr (Or.inl (LocalTraceEdge.appRight_B (p := o.categoryPath) rfl rfl hnp rfl))
  by_cases hv : o'.Visible
  · exact absurd hedge (hfree o ho o' hv)
  · exact ⟨o', P.closed o ho o' ⟨P.all_invisible o ho, hv, hedge⟩, rfl, rfl⟩

/-- Under a root `appRight`, a crossing occurrence on the functor side has its
metavariable partner on the argument side inside the piece. -/
theorem InvisiblePiece.appRight_partner_of_left
    {Γ Δ : List Category} {C B : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ B}
    {P : InvisiblePiece (DerivationTree.binary t₁ t₂ Rule.appRight)}
    (hfree : BoundaryFree P)
    {o : Occurrence (DerivationTree.binary t₁ t₂ Rule.appRight)}
    (ho : o ∈ P.carrier) (hnp : o.nodePath = [TreeStep.left]) :
    ∃ q, o.categoryPath = true :: q ∧
      ∃ o' : Occurrence (DerivationTree.binary t₁ t₂ Rule.appRight),
        o' ∈ P.carrier ∧ o'.nodePath = [TreeStep.right] ∧ o'.categoryPath = q := by
  obtain ⟨q, hq⟩ := InvisiblePiece.appRight_left_in_argument hfree ho hnp
  have hcat : o.nodeCategory = C ⧸ B := by
    have h := o.nodeAt
    rw [hnp] at h
    have h' : C ⧸ B = o.nodeCategory := by
      simpa [DerivationTree.categoryAt?] using h
    exact h'.symm
  obtain ⟨X, Y, hXY⟩ := o.isConstructor
  have hcons : ∃ X Y,
      B.subcategoryAt? q = some (X ⧸ Y) ∨ B.subcategoryAt? q = some (X ⧹ Y) := by
    refine ⟨X, Y, ?_⟩
    rw [hcat, hq] at hXY
    simpa using hXY
  let o' : Occurrence (DerivationTree.binary t₁ t₂ Rule.appRight) :=
    { nodePath := [TreeStep.right]
      nodeCategory := B
      nodeAt := by simp [DerivationTree.categoryAt?]
      categoryPath := q
      isConstructor := hcons }
  have hedge : TraceEdge o o' :=
    Or.inl (Or.inl (LocalTraceEdge.appRight_B (p := q) hnp hq rfl rfl))
  by_cases hv : o'.Visible
  · exact absurd hedge (hfree o ho o' hv)
  · exact ⟨q, hq, o', P.closed o ho o' ⟨P.all_invisible o ho, hv, hedge⟩, rfl, rfl⟩

/-- A boundary-free crossing piece is impossible under a root `appRight` with a
leaf functor premise. -/
theorem InvisiblePiece.crossing_appRight_functor_leaf_false
    {Δ : List Category} {C B : Category}
    {t₂ : DerivationTree Δ B}
    {P : InvisiblePiece (DerivationTree.binary (DerivationTree.leaf (C ⧸ B)) t₂ Rule.appRight)}
    (hfree : BoundaryFree P)
    (hcross : ∃ o : Occurrence (DerivationTree.binary (DerivationTree.leaf (C ⧸ B)) t₂ Rule.appRight),
      o ∈ P.carrier ∧ (o.nodePath = [TreeStep.left] ∨ o.nodePath = [TreeStep.right])) :
    False := by
  obtain ⟨o, ho, hside⟩ := hcross
  rcases hside with hnp | hnp
  · exact P.all_invisible o ho (Or.inr (Or.inl (by rw [hnp]; trivial)))
  · obtain ⟨o', ho', hnp', _⟩ := InvisiblePiece.appRight_partner_of_right hfree ho hnp
    exact P.all_invisible o' ho' (Or.inr (Or.inl (by rw [hnp']; trivial)))

/-! Mirror statements for a root backward application `A, A⧹C ⇒ C`. -/

/-- Under a root `appLeft`, a crossing occurrence on the argument-functor side
lies in the canceled part `false :: ·` of `A ⧹ C`. -/
theorem InvisiblePiece.appLeft_right_in_argument
    {Γ Δ : List Category} {A C : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ (A ⧹ C)}
    {P : InvisiblePiece (DerivationTree.binary t₁ t₂ Rule.appLeft)}
    (hfree : BoundaryFree P)
    {o : Occurrence (DerivationTree.binary t₁ t₂ Rule.appLeft)}
    (ho : o ∈ P.carrier) (hnp : o.nodePath = [TreeStep.right]) :
    ∃ q, o.categoryPath = false :: q := by
  have hcat : o.nodeCategory = A ⧹ C := by
    have h := o.nodeAt
    rw [hnp] at h
    have h' : A ⧹ C = o.nodeCategory := by
      simpa [DerivationTree.categoryAt?] using h
    exact h'.symm
  cases hcp : o.categoryPath with
  | nil =>
      exfalso
      apply P.all_invisible o ho
      right; right
      rw [hnp, hcp]
      exact DerivationTree.PrincipalConstructor.appLeft_right t₁ t₂
  | cons b q =>
      cases b with
      | false => exact ⟨q, rfl⟩
      | true =>
          exfalso
          obtain ⟨X, Y, hXY⟩ := o.isConstructor
          have hconsRoot : ∃ X Y,
              C.subcategoryAt? q = some (X ⧸ Y) ∨
              C.subcategoryAt? q = some (X ⧹ Y) := by
            refine ⟨X, Y, ?_⟩
            rw [hcat, hcp] at hXY
            simpa using hXY
          let o' : Occurrence (DerivationTree.binary t₁ t₂ Rule.appLeft) :=
            { nodePath := []
              nodeCategory := C
              nodeAt := rfl
              categoryPath := q
              isConstructor := hconsRoot }
          have hedge : TraceEdge o o' :=
            Or.inl (Or.inl (LocalTraceEdge.appLeft_C (p := q) hnp hcp rfl rfl))
          exact hfree o ho o' (Or.inl rfl) hedge

/-- Under a root `appLeft`, a crossing occurrence on the plain-argument side
has its metavariable partner on the argument-functor side inside the piece. -/
theorem InvisiblePiece.appLeft_partner_of_left
    {Γ Δ : List Category} {A C : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ (A ⧹ C)}
    {P : InvisiblePiece (DerivationTree.binary t₁ t₂ Rule.appLeft)}
    (hfree : BoundaryFree P)
    {o : Occurrence (DerivationTree.binary t₁ t₂ Rule.appLeft)}
    (ho : o ∈ P.carrier) (hnp : o.nodePath = [TreeStep.left]) :
    ∃ o' : Occurrence (DerivationTree.binary t₁ t₂ Rule.appLeft),
      o' ∈ P.carrier ∧ o'.nodePath = [TreeStep.right] ∧
        o'.categoryPath = false :: o.categoryPath := by
  have hcat : o.nodeCategory = A := by
    have h := o.nodeAt
    rw [hnp] at h
    have h' : A = o.nodeCategory := by
      simpa [DerivationTree.categoryAt?] using h
    exact h'.symm
  obtain ⟨X, Y, hXY⟩ := o.isConstructor
  have hcons : ∃ X Y,
      (A ⧹ C).subcategoryAt? (false :: o.categoryPath) = some (X ⧸ Y) ∨
      (A ⧹ C).subcategoryAt? (false :: o.categoryPath) = some (X ⧹ Y) := by
    refine ⟨X, Y, ?_⟩
    rw [hcat] at hXY
    simpa using hXY
  let o' : Occurrence (DerivationTree.binary t₁ t₂ Rule.appLeft) :=
    { nodePath := [TreeStep.right]
      nodeCategory := A ⧹ C
      nodeAt := by simp [DerivationTree.categoryAt?]
      categoryPath := false :: o.categoryPath
      isConstructor := hcons }
  have hedge : TraceEdge o o' :=
    Or.inl (Or.inl (LocalTraceEdge.appLeft_A (p := o.categoryPath) hnp rfl rfl rfl))
  by_cases hv : o'.Visible
  · exact absurd hedge (hfree o ho o' hv)
  · exact ⟨o', P.closed o ho o' ⟨P.all_invisible o ho, hv, hedge⟩, rfl, rfl⟩

/-- Under a root `appLeft`, a crossing occurrence on the argument-functor side
has its metavariable partner on the plain-argument side inside the piece. -/
theorem InvisiblePiece.appLeft_partner_of_right
    {Γ Δ : List Category} {A C : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ (A ⧹ C)}
    {P : InvisiblePiece (DerivationTree.binary t₁ t₂ Rule.appLeft)}
    (hfree : BoundaryFree P)
    {o : Occurrence (DerivationTree.binary t₁ t₂ Rule.appLeft)}
    (ho : o ∈ P.carrier) (hnp : o.nodePath = [TreeStep.right]) :
    ∃ q, o.categoryPath = false :: q ∧
      ∃ o' : Occurrence (DerivationTree.binary t₁ t₂ Rule.appLeft),
        o' ∈ P.carrier ∧ o'.nodePath = [TreeStep.left] ∧ o'.categoryPath = q := by
  obtain ⟨q, hq⟩ := InvisiblePiece.appLeft_right_in_argument hfree ho hnp
  have hcat : o.nodeCategory = A ⧹ C := by
    have h := o.nodeAt
    rw [hnp] at h
    have h' : A ⧹ C = o.nodeCategory := by
      simpa [DerivationTree.categoryAt?] using h
    exact h'.symm
  obtain ⟨X, Y, hXY⟩ := o.isConstructor
  have hcons : ∃ X Y,
      A.subcategoryAt? q = some (X ⧸ Y) ∨ A.subcategoryAt? q = some (X ⧹ Y) := by
    refine ⟨X, Y, ?_⟩
    rw [hcat, hq] at hXY
    simpa using hXY
  let o' : Occurrence (DerivationTree.binary t₁ t₂ Rule.appLeft) :=
    { nodePath := [TreeStep.left]
      nodeCategory := A
      nodeAt := by simp [DerivationTree.categoryAt?]
      categoryPath := q
      isConstructor := hcons }
  have hedge : TraceEdge o o' :=
    Or.inr (Or.inl (LocalTraceEdge.appLeft_A (p := q) rfl rfl hnp hq))
  by_cases hv : o'.Visible
  · exact absurd hedge (hfree o ho o' hv)
  · exact ⟨q, hq, o', P.closed o ho o' ⟨P.all_invisible o ho, hv, hedge⟩, rfl, rfl⟩

/-- A boundary-free crossing piece is impossible under a root `appLeft` with a
leaf argument-functor premise. -/
theorem InvisiblePiece.crossing_appLeft_argument_leaf_false
    {Γ : List Category} {A C : Category}
    {t₁ : DerivationTree Γ A}
    {P : InvisiblePiece (DerivationTree.binary t₁ (DerivationTree.leaf (A ⧹ C)) Rule.appLeft)}
    (hfree : BoundaryFree P)
    (hcross : ∃ o : Occurrence (DerivationTree.binary t₁ (DerivationTree.leaf (A ⧹ C)) Rule.appLeft),
      o ∈ P.carrier ∧ (o.nodePath = [TreeStep.left] ∨ o.nodePath = [TreeStep.right])) :
    False := by
  obtain ⟨o, ho, hside⟩ := hcross
  rcases hside with hnp | hnp
  · obtain ⟨o', ho', hnp', _⟩ := InvisiblePiece.appLeft_partner_of_left hfree ho hnp
    exact P.all_invisible o' ho' (Or.inr (Or.inl (by rw [hnp']; trivial)))
  · exact P.all_invisible o ho (Or.inr (Or.inl (by rw [hnp]; trivial)))

/-- The crossing case of a root `appRight` with a `T>` functor premise is the
collapse redex (spine of length zero). -/
theorem crossing_appRight_reduces_of_functor_typeRaise
    {Γ Δ : List Category} {A₀ C₀ : Category}
    (u : DerivationTree Γ A₀) (t₂ : DerivationTree Δ (A₀ ⧹ C₀)) :
    Nonempty (SizeReduction
      (DerivationTree.binary (DerivationTree.typeRaiseRight C₀ u) t₂ Rule.appRight)) :=
  sizeReduction_appRight_of_compSpineRight (CompSpineRight.raise u) t₂

/-- The crossing case of a root `appLeft` with a `T<` argument premise is the
mirror collapse redex. -/
theorem crossing_appLeft_reduces_of_argument_typeRaise
    {Γ Δ : List Category} {A₀ C₀ : Category}
    (w : DerivationTree Δ (C₀ ⧸ A₀)) (u : DerivationTree Γ A₀) :
    Nonempty (SizeReduction
      (DerivationTree.binary w (DerivationTree.typeRaiseLeft C₀ u) Rule.appLeft)) :=
  sizeReduction_appLeft_of_compSpineLeft (CompSpineLeft.raise u) w

/-- A local crossed cancellation that deletes the forward raise feeding the
left premise of `crossedLeft` together with the backward raise consumed by the
surrounding `appRight`.

Unlike `CompSpineRight`, this is not a linear composition-spine collapse: the
middle premise `y` remains between the two deleted raises in the leaf order.
The contractum preserves the original leaf order by first rebuilding the
`crossedLeft` node from the unraised functor and then applying it to the
unraised argument. -/
theorem sizeReduction_appRight_of_crossedLeft_typeRaises
    {A₀ C₀ C : Category} {Γ Δ Θ : List Category}
    (u : DerivationTree Γ (C₀ ⧸ A₀)) (y : DerivationTree Δ (C₀ ⧹ C))
    (z : DerivationTree Θ A₀) :
    Nonempty (SizeReduction
      (DerivationTree.binary
        (DerivationTree.binary (DerivationTree.typeRaiseRight C₀ u) y Rule.crossedLeft)
        (DerivationTree.typeRaiseLeft C₀ z) Rule.appRight)) := by
  refine ⟨{
    target := DerivationTree.binary (DerivationTree.binary u y Rule.crossedLeft) z Rule.appRight
    size_lt := by
      simp only [DerivationTree.size_binary, DerivationTree.size_typeRaiseRight,
        DerivationTree.size_typeRaiseLeft, Category.constructors]
      omega
    atoms := ?_ }⟩
  intro names h X hX
  simp only [DerivationTree.nodeCategories_binary, List.mem_cons, List.mem_append] at hX
  rcases hX with hroot | hleft | hright
  · subst hroot
    exact h _ (by simp [DerivationTree.nodeCategories_binary])
  · rcases hleft with hout | hu | hy
    · subst hout
      have hC : UsesOnlyAtoms names C := h C (by simp [DerivationTree.nodeCategories_binary])
      have hA₀ : UsesOnlyAtoms names A₀ := by
        have huRoot : C₀ ⧸ A₀ ∈ u.nodeCategories := by
          cases u <;> simp [DerivationTree.nodeCategories]
        have huAtoms : UsesOnlyAtoms names (C₀ ⧸ A₀) := h (C₀ ⧸ A₀) (by
          simp [DerivationTree.nodeCategories_binary, DerivationTree.nodeCategories_typeRaiseRight,
            huRoot])
        exact huAtoms.rdiv_right
      exact UsesOnlyAtoms.rdiv hC hA₀
    · exact h X (by
        simp [DerivationTree.nodeCategories_binary, DerivationTree.nodeCategories_typeRaiseRight, hu])
    · exact h X (by
        simp [DerivationTree.nodeCategories_binary, DerivationTree.nodeCategories_typeRaiseRight, hy])
  · exact h X (by
      simp [DerivationTree.nodeCategories_binary, DerivationTree.nodeCategories_typeRaiseLeft, hright])

/-- Mirror local crossed cancellation: a forward raise consumed by the
surrounding `appLeft` and a backward raise feeding the right premise of
`crossedRight` can be deleted simultaneously.

The contractum keeps the original leaf order by rebuilding `crossedRight` from
the unraised right premise before applying the unraised left argument. -/
theorem sizeReduction_appLeft_of_crossedRight_typeRaises
    {A₀ C₀ C : Category} {Θ Γ Δ : List Category}
    (z : DerivationTree Θ A₀) (y : DerivationTree Γ (C ⧸ C₀))
    (u : DerivationTree Δ (A₀ ⧹ C₀)) :
    Nonempty (SizeReduction
      (DerivationTree.binary
        (DerivationTree.typeRaiseRight C₀ z)
        (DerivationTree.binary y (DerivationTree.typeRaiseLeft C₀ u) Rule.crossedRight)
        Rule.appLeft)) := by
  refine ⟨{
    target := DerivationTree.binary z (DerivationTree.binary y u Rule.crossedRight) Rule.appLeft
    size_lt := by
      simp only [DerivationTree.size_binary, DerivationTree.size_typeRaiseRight,
        DerivationTree.size_typeRaiseLeft, Category.constructors]
      omega
    atoms := ?_ }⟩
  intro names h X hX
  simp only [DerivationTree.nodeCategories_binary, List.mem_cons, List.mem_append] at hX
  rcases hX with hroot | hleft | hright
  · subst hroot
    exact h _ (by simp [DerivationTree.nodeCategories_binary])
  · exact h X (by
      simp [DerivationTree.nodeCategories_binary, DerivationTree.nodeCategories_typeRaiseRight, hleft])
  · rcases hright with hinnerRoot | hy | hu
    · subst hinnerRoot
      have hA₀ : UsesOnlyAtoms names A₀ := by
        have hzRoot : A₀ ∈ z.nodeCategories := by
          cases z <;> simp [DerivationTree.nodeCategories]
        exact h A₀ (by
          simp [DerivationTree.nodeCategories_binary, DerivationTree.nodeCategories_typeRaiseRight,
            hzRoot])
      have hC : UsesOnlyAtoms names C := h C (by simp [DerivationTree.nodeCategories_binary])
      exact UsesOnlyAtoms.ldiv hA₀ hC
    · exact h X (by
        simp [DerivationTree.nodeCategories_binary, DerivationTree.nodeCategories_typeRaiseLeft, hy])
    · exact h X (by
        simp [DerivationTree.nodeCategories_binary, DerivationTree.nodeCategories_typeRaiseLeft, hu])

/-- Order-preserving crossed cancellation for a backward composition spine feeding
the right premise of `crossedRight` and a forward type raise consumed by the
surrounding `appLeft`.

This is the mirror of `sizeReduction_appRight_of_crossedLeft_compSpineRight`:
the backward raise may be hidden under a `compLeft` spine before it meets the
crossed rule. -/
theorem sizeReduction_appLeft_of_crossedRight_compSpineLeft
    {A₀ C₀ C D : Category} {Θ Γ Δ : List Category}
    (z : DerivationTree Θ A₀) (y : DerivationTree Γ (C ⧸ D))
    {F : DerivationTree Δ ((C₀ ⧸ (A₀ ⧹ C₀)) ⧹ D)}
    (hF : CompSpineLeft (A₀ ⧹ C₀) C₀ F) :
    Nonempty (SizeReduction
      (DerivationTree.binary (DerivationTree.typeRaiseRight C₀ z)
        (DerivationTree.binary y F Rule.crossedRight) Rule.appLeft)) := by
  obtain ⟨F', hsizeF, hatomsF⟩ := hF.lowerRaisedSlot
  refine ⟨{
    target := DerivationTree.binary z (DerivationTree.binary y F' Rule.crossedRight) Rule.appLeft
    size_lt := by
      simp only [DerivationTree.size_binary, DerivationTree.size_typeRaiseRight,
        Category.constructors] at hsizeF ⊢
      omega
    atoms := ?_ }⟩
  intro names h X hX
  simp only [DerivationTree.nodeCategories_binary, List.mem_cons, List.mem_append] at hX
  rcases hX with hroot | hleft | hright
  · subst hroot
    exact h _ (by simp [DerivationTree.nodeCategories_binary])
  · exact h X (by
      simp [DerivationTree.nodeCategories_binary, DerivationTree.nodeCategories_typeRaiseRight, hleft])
  · rcases hright with hinnerRoot | hy | hF'
    · subst hinnerRoot
      have hA₀ : UsesOnlyAtoms names A₀ := by
        have hzRoot : A₀ ∈ z.nodeCategories := by
          cases z <;> simp [DerivationTree.nodeCategories]
        exact h A₀ (by
          simp [DerivationTree.nodeCategories_binary, DerivationTree.nodeCategories_typeRaiseRight,
            hzRoot])
      have hC : UsesOnlyAtoms names C := h C (by simp [DerivationTree.nodeCategories_binary])
      exact UsesOnlyAtoms.ldiv hA₀ hC
    · exact h X (by
        simp [DerivationTree.nodeCategories_binary, DerivationTree.nodeCategories_typeRaiseRight, hy])
    · refine hatomsF names ?_ X hF'
      intro W hW
      exact h W (by
        simp [DerivationTree.nodeCategories_binary, DerivationTree.nodeCategories_typeRaiseRight, hW])


/-! ## Application-root branch reducers

The binary-root application branches are concrete dependent cases rather than a
single negative "other rule" family.  When the inner application branch supplies
a recursive size reduction, the outer application reduces by congruence; when
the inner composition/crossed-composition branch has already been forced into
the appropriate spine/type-raise shape, the existing local spine reducers apply
directly. -/

/-- Forward-application functor branch whose functor root is another forward
application.  This is a recursive branch: reducing the inner application reduces
the outer one by congruence on the functor premise. -/
theorem crossing_appRight_functor_appRight_reduces_of_inner
    {Γ₁ Γ₂ Δ : List Category} {C B X : Category}
    {l : DerivationTree Γ₁ ((C ⧸ B) ⧸ X)} {r : DerivationTree Γ₂ X}
    (t₂ : DerivationTree Δ B)
    (hinner : Nonempty (SizeReduction (DerivationTree.binary l r Rule.appRight))) :
    Nonempty (SizeReduction
      (DerivationTree.binary (DerivationTree.binary l r Rule.appRight) t₂ Rule.appRight)) := by
  obtain ⟨w⟩ := hinner
  exact ⟨w.underBinaryLeft t₂ Rule.appRight⟩

/-- Forward-application functor branch whose functor root is a backward
application.  This is the second concrete application-root functor case. -/
theorem crossing_appRight_functor_appLeft_reduces_of_inner
    {Γ₁ Γ₂ Δ : List Category} {C B X : Category}
    {l : DerivationTree Γ₁ X} {r : DerivationTree Γ₂ (X ⧹ (C ⧸ B))}
    (t₂ : DerivationTree Δ B)
    (hinner : Nonempty (SizeReduction (DerivationTree.binary l r Rule.appLeft))) :
    Nonempty (SizeReduction
      (DerivationTree.binary (DerivationTree.binary l r Rule.appLeft) t₂ Rule.appRight)) := by
  obtain ⟨w⟩ := hinner
  exact ⟨w.underBinaryLeft t₂ Rule.appRight⟩

/-- Forward-application functor branch whose functor root is forward
composition, after the boundary-free chase has forced a right composition spine. -/
theorem crossing_appRight_functor_compRight_reduces_of_spine
    {Γ Δ : List Category} {A₀ C₀ C : Category}
    {F : DerivationTree Γ (C ⧸ (A₀ ⧹ C₀))}
    (hF : CompSpineRight A₀ C₀ F) (t₂ : DerivationTree Δ (A₀ ⧹ C₀)) :
    Nonempty (SizeReduction (DerivationTree.binary F t₂ Rule.appRight)) :=
  sizeReduction_appRight_of_compSpineRight hF t₂

/-- Forward-application functor branch whose functor root is crossed-left,
after the boundary-free chase has forced the crossed diamond/spine shape. -/
theorem crossing_appRight_functor_crossedLeft_reduces_of_spine
    {A₀ C₀ C D : Category} {Γ Δ Θ : List Category}
    {F : DerivationTree Γ (D ⧸ ((C₀ ⧸ A₀) ⧹ C₀))}
    (hF : CompSpineRight (C₀ ⧸ A₀) C₀ F)
    (y : DerivationTree Δ (D ⧹ C)) (z : DerivationTree Θ A₀) :
    Nonempty (SizeReduction
      (DerivationTree.binary (DerivationTree.binary F y Rule.crossedLeft)
        (DerivationTree.typeRaiseLeft C₀ z) Rule.appRight)) :=
  sizeReduction_appRight_of_crossedLeft_compSpineRight hF y z

/-- Backward-application argument branch whose argument-functor root is a
forward application.  This is a recursive branch: reducing the inner application
reduces the outer one by congruence on the argument premise. -/
theorem crossing_appLeft_argument_appRight_reduces_of_inner
    {Θ Γ₁ Γ₂ : List Category} {A C X : Category}
    (t₁ : DerivationTree Θ A)
    {l : DerivationTree Γ₁ ((A ⧹ C) ⧸ X)} {r : DerivationTree Γ₂ X}
    (hinner : Nonempty (SizeReduction (DerivationTree.binary l r Rule.appRight))) :
    Nonempty (SizeReduction
      (DerivationTree.binary t₁ (DerivationTree.binary l r Rule.appRight) Rule.appLeft)) := by
  obtain ⟨w⟩ := hinner
  exact ⟨w.underBinaryRight t₁ Rule.appLeft⟩

/-- Backward-application argument branch whose argument-functor root is another
backward application.  This is the second concrete application-root argument
case. -/
theorem crossing_appLeft_argument_appLeft_reduces_of_inner
    {Θ Γ₁ Γ₂ : List Category} {A C X : Category}
    (t₁ : DerivationTree Θ A)
    {l : DerivationTree Γ₁ X} {r : DerivationTree Γ₂ (X ⧹ (A ⧹ C))}
    (hinner : Nonempty (SizeReduction (DerivationTree.binary l r Rule.appLeft))) :
    Nonempty (SizeReduction
      (DerivationTree.binary t₁ (DerivationTree.binary l r Rule.appLeft) Rule.appLeft)) := by
  obtain ⟨w⟩ := hinner
  exact ⟨w.underBinaryRight t₁ Rule.appLeft⟩

/-- Backward-application argument branch whose argument-functor root is backward
composition, after the boundary-free chase has forced a left composition spine. -/
theorem crossing_appLeft_argument_compLeft_reduces_of_spine
    {Γ Δ : List Category} {A₀ C₀ C : Category}
    (t₁ : DerivationTree Δ (C₀ ⧸ A₀))
    {F : DerivationTree Γ ((C₀ ⧸ A₀) ⧹ C)}
    (hF : CompSpineLeft A₀ C₀ F) :
    Nonempty (SizeReduction (DerivationTree.binary t₁ F Rule.appLeft)) :=
  sizeReduction_appLeft_of_compSpineLeft hF t₁

/-- Backward-application argument branch whose argument-functor root is
crossed-right, after the boundary-free chase has forced the crossed
diamond/spine shape. -/
theorem crossing_appLeft_argument_crossedRight_reduces_of_spine
    {A₀ C₀ C D : Category} {Θ Γ Δ : List Category}
    (z : DerivationTree Θ A₀) (y : DerivationTree Γ (C ⧸ D))
    {F : DerivationTree Δ ((C₀ ⧸ (A₀ ⧹ C₀)) ⧹ D)}
    (hF : CompSpineLeft (A₀ ⧹ C₀) C₀ F) :
    Nonempty (SizeReduction
      (DerivationTree.binary (DerivationTree.typeRaiseRight C₀ z)
        (DerivationTree.binary y F Rule.crossedRight) Rule.appLeft)) :=
  sizeReduction_appLeft_of_crossedRight_compSpineLeft z y hF


/-- Carrier membership is closed along the same invisible trace component. -/
theorem InvisiblePiece.mem_of_sameInvisible
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} {o p : Occurrence t}
    (hcomp : SameInvisibleTraceComponent o p) (ho : o ∈ P.carrier) :
    p ∈ P.carrier := by
  induction hcomp with
  | refl => exact ho
  | tail _ hstep ih => exact P.closed _ ih _ hstep

/-- A boundary-free invisible piece has no visible boundary at any of its
members. -/
theorem InvisiblePiece.not_hasVisibleBoundary_of_mem
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (hfree : BoundaryFree P)
    {o : Occurrence t} (ho : o ∈ P.carrier) : ¬ HasVisibleBoundary o := by
  intro hb
  obtain ⟨p, v, hcomp, _hpInv, hv, hedge⟩ := hb
  have hp : p ∈ P.carrier := P.mem_of_sameInvisible hcomp ho
  exact hfree p hp v hv hedge


/-- A finite trace route from an occurrence to a visible occurrence.  This
separates graph reachability from the boundary-free contradiction used by the
slot-escape lemmas. -/
inductive VisibleTraceRoute {Γ : List Category} {A : Category}
    {t : DerivationTree Γ A} : Occurrence t → Prop where
  | here {o : Occurrence t} (hv : o.Visible) : VisibleTraceRoute o
  | step {o o' : Occurrence t} (h : TraceEdge o o')
      (r : VisibleTraceRoute o') : VisibleTraceRoute o

namespace VisibleTraceRoute

/-- A boundary-free piece cannot contain the start of a route to a visible
occurrence. -/
theorem mem_false_of_boundaryFree
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (hfree : BoundaryFree P)
    {o : Occurrence t} (ho : o ∈ P.carrier)
    (hr : VisibleTraceRoute o) : False := by
  induction hr with
  | here hv => exact P.all_invisible _ ho hv
  | @step o oNext hedge _ ih =>
      have hoNext : oNext ∈ P.carrier := P.closed_traceEdge_of_boundaryFree hfree ho hedge
      exact ih hoNext

/-- A continuation slot says that every occurrence at subtree address `π` whose
category path is produced by `κ` already routes to a visible occurrence. -/
def SlotContinuation {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (π : NodePath) (κ : CategoryPath → CategoryPath) : Prop :=
  ∀ {o : Occurrence t} {p : CategoryPath},
    o.nodePath = π → o.categoryPath = κ p → VisibleTraceRoute o


/-- Under a root `compRight`, a right-premise denominator slot routes directly
to the visible root by `compRight_A`. -/
theorem compRight_right_den_route
    {Γ Δ : List Category} {C B A : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (B ⧸ A)}
    {o : Occurrence (DerivationTree.binary t₁ t₂ Rule.compRight)}
    (hn : o.nodePath = [TreeStep.right]) (hp : ∃ p, o.categoryPath = true :: p) :
    VisibleTraceRoute o := by
  obtain ⟨p, hp⟩ := hp
  have hcat : o.nodeCategory = B ⧸ A := by
    have h := o.nodeAt
    rw [hn] at h
    have h' : B ⧸ A = o.nodeCategory := by
      simpa [DerivationTree.categoryAt?] using h
    exact h'.symm
  obtain ⟨X, Y, hXY⟩ := o.isConstructor
  have hconsRoot : ∃ X Y,
      (C ⧸ A).subcategoryAt? (true :: p) = some (X ⧸ Y) ∨
      (C ⧸ A).subcategoryAt? (true :: p) = some (X ⧹ Y) := by
    refine ⟨X, Y, ?_⟩
    rw [hcat, hp] at hXY
    simpa using hXY
  let v : Occurrence (DerivationTree.binary t₁ t₂ Rule.compRight) :=
    { nodePath := []
      nodeCategory := C ⧸ A
      nodeAt := rfl
      categoryPath := true :: p
      isConstructor := hconsRoot }
  have hedge : TraceEdge o v :=
    Or.inl (Or.inl (LocalTraceEdge.compRight_A (p := p) hn hp rfl rfl))
  exact VisibleTraceRoute.step hedge (VisibleTraceRoute.here (o := v) (Or.inl rfl))

/-- Under a root `compLeft`, a left-premise numerator slot routes directly to
the visible root by `compLeft_A`. -/
theorem compLeft_left_num_route
    {Γ Δ : List Category} {A B C : Category}
    {t₁ : DerivationTree Γ (A ⧹ B)} {t₂ : DerivationTree Δ (B ⧹ C)}
    {o : Occurrence (DerivationTree.binary t₁ t₂ Rule.compLeft)}
    (hn : o.nodePath = [TreeStep.left]) (hp : ∃ p, o.categoryPath = false :: p) :
    VisibleTraceRoute o := by
  obtain ⟨p, hp⟩ := hp
  have hcat : o.nodeCategory = A ⧹ B := by
    have h := o.nodeAt
    rw [hn] at h
    have h' : A ⧹ B = o.nodeCategory := by
      simpa [DerivationTree.categoryAt?] using h
    exact h'.symm
  obtain ⟨X, Y, hXY⟩ := o.isConstructor
  have hconsRoot : ∃ X Y,
      (A ⧹ C).subcategoryAt? (false :: p) = some (X ⧸ Y) ∨
      (A ⧹ C).subcategoryAt? (false :: p) = some (X ⧹ Y) := by
    refine ⟨X, Y, ?_⟩
    rw [hcat, hp] at hXY
    simpa using hXY
  let v : Occurrence (DerivationTree.binary t₁ t₂ Rule.compLeft) :=
    { nodePath := []
      nodeCategory := A ⧹ C
      nodeAt := rfl
      categoryPath := false :: p
      isConstructor := hconsRoot }
  have hedge : TraceEdge o v :=
    Or.inl (Or.inl (LocalTraceEdge.compLeft_A (p := p) hn hp rfl rfl))
  exact VisibleTraceRoute.step hedge (VisibleTraceRoute.here (o := v) (Or.inl rfl))

/-- Under a root `crossedRight`, a right-premise numerator slot routes directly
to the visible root by `crossedRight_A`. -/
theorem crossedRight_right_num_route
    {Γ Δ : List Category} {C B A : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (A ⧹ B)}
    {o : Occurrence (DerivationTree.binary t₁ t₂ Rule.crossedRight)}
    (hn : o.nodePath = [TreeStep.right]) (hp : ∃ p, o.categoryPath = false :: p) :
    VisibleTraceRoute o := by
  obtain ⟨p, hp⟩ := hp
  have hcat : o.nodeCategory = A ⧹ B := by
    have h := o.nodeAt
    rw [hn] at h
    have h' : A ⧹ B = o.nodeCategory := by
      simpa [DerivationTree.categoryAt?] using h
    exact h'.symm
  obtain ⟨X, Y, hXY⟩ := o.isConstructor
  have hconsRoot : ∃ X Y,
      (A ⧹ C).subcategoryAt? (false :: p) = some (X ⧸ Y) ∨
      (A ⧹ C).subcategoryAt? (false :: p) = some (X ⧹ Y) := by
    refine ⟨X, Y, ?_⟩
    rw [hcat, hp] at hXY
    simpa using hXY
  let v : Occurrence (DerivationTree.binary t₁ t₂ Rule.crossedRight) :=
    { nodePath := []
      nodeCategory := A ⧹ C
      nodeAt := rfl
      categoryPath := false :: p
      isConstructor := hconsRoot }
  have hedge : TraceEdge o v :=
    Or.inl (Or.inl (LocalTraceEdge.crossedRight_A (p := p) hn hp rfl rfl))
  exact VisibleTraceRoute.step hedge (VisibleTraceRoute.here (o := v) (Or.inl rfl))

/-- Under a root `crossedLeft`, a left-premise argument slot routes directly to
the visible root by `crossedLeft_A`. -/
theorem crossedLeft_left_arg_route
    {Γ Δ : List Category} {B A C : Category}
    {t₁ : DerivationTree Γ (B ⧸ A)} {t₂ : DerivationTree Δ (B ⧹ C)}
    {o : Occurrence (DerivationTree.binary t₁ t₂ Rule.crossedLeft)}
    (hn : o.nodePath = [TreeStep.left]) (hp : ∃ p, o.categoryPath = true :: p) :
    VisibleTraceRoute o := by
  obtain ⟨p, hp⟩ := hp
  have hcat : o.nodeCategory = B ⧸ A := by
    have h := o.nodeAt
    rw [hn] at h
    have h' : B ⧸ A = o.nodeCategory := by
      simpa [DerivationTree.categoryAt?] using h
    exact h'.symm
  obtain ⟨X, Y, hXY⟩ := o.isConstructor
  have hconsRoot : ∃ X Y,
      (C ⧸ A).subcategoryAt? (true :: p) = some (X ⧸ Y) ∨
      (C ⧸ A).subcategoryAt? (true :: p) = some (X ⧹ Y) := by
    refine ⟨X, Y, ?_⟩
    rw [hcat, hp] at hXY
    simpa using hXY
  let v : Occurrence (DerivationTree.binary t₁ t₂ Rule.crossedLeft) :=
    { nodePath := []
      nodeCategory := C ⧸ A
      nodeAt := rfl
      categoryPath := true :: p
      isConstructor := hconsRoot }
  have hedge : TraceEdge o v :=
    Or.inl (Or.inl (LocalTraceEdge.crossedLeft_A (p := p) hn hp rfl rfl))
  exact VisibleTraceRoute.step hedge (VisibleTraceRoute.here (o := v) (Or.inl rfl))

/-- Immediate `compRight`/`T>` base for the right-canceled-slot route: the
canceled numerator copy routes to the sibling target copy by `trRight_C`, then
the root continuation closes by `compRight_A`. -/
theorem compRight_right_typeRaiseRight_num_route
    {Γ Δ : List Category} {C C₀ A₀ : Category}
    {t₁ : DerivationTree Γ (C ⧸ C₀)} {u : DerivationTree Δ A₀}
    {o : Occurrence (DerivationTree.binary t₁ (DerivationTree.typeRaiseRight C₀ u) Rule.compRight)}
    (hn : o.nodePath = [TreeStep.right]) (hp : ∃ p, o.categoryPath = false :: p) :
    VisibleTraceRoute o := by
  obtain ⟨p, hp⟩ := hp
  have hcat : o.nodeCategory = C₀ ⧸ (A₀ ⧹ C₀) := by
    have h := o.nodeAt
    rw [hn] at h
    have h' : C₀ ⧸ (A₀ ⧹ C₀) = o.nodeCategory := by
      simpa [DerivationTree.categoryAt?] using h
    exact h'.symm
  obtain ⟨X, Y, hXY⟩ := o.isConstructor
  have hconsFalse : ∃ X Y,
      (C₀ ⧸ (A₀ ⧹ C₀)).subcategoryAt? (false :: p) = some (X ⧸ Y) ∨
      (C₀ ⧸ (A₀ ⧹ C₀)).subcategoryAt? (false :: p) = some (X ⧹ Y) := by
    refine ⟨X, Y, ?_⟩
    rwa [hcat, hp] at hXY
  have hconsTrueTrue : ∃ X Y,
      (C₀ ⧸ (A₀ ⧹ C₀)).subcategoryAt? (true :: true :: p) = some (X ⧸ Y) ∨
      (C₀ ⧸ (A₀ ⧹ C₀)).subcategoryAt? (true :: true :: p) = some (X ⧹ Y) := by
    refine ⟨X, Y, ?_⟩
    rw [hcat, hp] at hXY
    simpa [Category.subcategoryAt?] using hXY
  let e : Occurrence (DerivationTree.typeRaiseRight C₀ u) :=
    { nodePath := []
      nodeCategory := C₀ ⧸ (A₀ ⧹ C₀)
      nodeAt := rfl
      categoryPath := false :: p
      isConstructor := hconsFalse }
  let eC : Occurrence (DerivationTree.typeRaiseRight C₀ u) :=
    { nodePath := []
      nodeCategory := C₀ ⧸ (A₀ ⧹ C₀)
      nodeAt := rfl
      categoryPath := true :: true :: p
      isConstructor := hconsTrueTrue }
  have ho_eq : o = e.underBinaryRight (t₁ := t₁) Rule.compRight := by
    apply DerivationTree.CategoryOccurrence.eq_of_data
    · simp [DerivationTree.CategoryOccurrence.underBinaryRight, e, hn]
    · simp [DerivationTree.CategoryOccurrence.underBinaryRight, e, hcat]
    · simp [DerivationTree.CategoryOccurrence.underBinaryRight, e, hp]
  let oC : Occurrence (DerivationTree.binary t₁ (DerivationTree.typeRaiseRight C₀ u) Rule.compRight) :=
    eC.underBinaryRight (t₁ := t₁) Rule.compRight
  have hedge : TraceEdge o oC := by
    have hloc : LocalTraceEdge e eC :=
      LocalTraceEdge.trRight_C (p := p) rfl rfl rfl rfl
    have htr : TraceEdge (e.underBinaryRight (t₁ := t₁) Rule.compRight)
        (eC.underBinaryRight (t₁ := t₁) Rule.compRight) :=
      TraceEdge.underBinaryRight (t₁ := t₁) Rule.compRight
        (Or.inl (Or.inl hloc) : TraceEdge e eC)
    simpa [oC, ho_eq] using htr
  exact VisibleTraceRoute.step hedge
    (compRight_right_den_route (o := oC) rfl ⟨true :: p, rfl⟩)

/-- Immediate `compLeft`/`T<` base for the left-canceled-slot route: the
canceled denominator copy routes to the sibling target copy by `trLeft_C`, then
the root continuation closes by `compLeft_A`. -/
theorem compLeft_left_typeRaiseLeft_den_route
    {Γ Δ : List Category} {C C₀ A₀ : Category}
    {u : DerivationTree Γ A₀} {t₂ : DerivationTree Δ (C₀ ⧹ C)}
    {o : Occurrence (DerivationTree.binary (DerivationTree.typeRaiseLeft C₀ u) t₂ Rule.compLeft)}
    (hn : o.nodePath = [TreeStep.left]) (hp : ∃ p, o.categoryPath = true :: p) :
    VisibleTraceRoute o := by
  obtain ⟨p, hp⟩ := hp
  have hcat : o.nodeCategory = (C₀ ⧸ A₀) ⧹ C₀ := by
    have h := o.nodeAt
    rw [hn] at h
    have h' : (C₀ ⧸ A₀) ⧹ C₀ = o.nodeCategory := by
      simpa [DerivationTree.categoryAt?] using h
    exact h'.symm
  obtain ⟨X, Y, hXY⟩ := o.isConstructor
  have hconsTrue : ∃ X Y,
      ((C₀ ⧸ A₀) ⧹ C₀).subcategoryAt? (true :: p) = some (X ⧸ Y) ∨
      ((C₀ ⧸ A₀) ⧹ C₀).subcategoryAt? (true :: p) = some (X ⧹ Y) := by
    refine ⟨X, Y, ?_⟩
    rwa [hcat, hp] at hXY
  have hconsFalseFalse : ∃ X Y,
      ((C₀ ⧸ A₀) ⧹ C₀).subcategoryAt? (false :: false :: p) = some (X ⧸ Y) ∨
      ((C₀ ⧸ A₀) ⧹ C₀).subcategoryAt? (false :: false :: p) = some (X ⧹ Y) := by
    refine ⟨X, Y, ?_⟩
    rw [hcat, hp] at hXY
    simpa [Category.subcategoryAt?] using hXY
  let e : Occurrence (DerivationTree.typeRaiseLeft C₀ u) :=
    { nodePath := []
      nodeCategory := (C₀ ⧸ A₀) ⧹ C₀
      nodeAt := rfl
      categoryPath := true :: p
      isConstructor := hconsTrue }
  let eC : Occurrence (DerivationTree.typeRaiseLeft C₀ u) :=
    { nodePath := []
      nodeCategory := (C₀ ⧸ A₀) ⧹ C₀
      nodeAt := rfl
      categoryPath := false :: false :: p
      isConstructor := hconsFalseFalse }
  have ho_eq : o = e.underBinaryLeft (t₂ := t₂) Rule.compLeft := by
    apply DerivationTree.CategoryOccurrence.eq_of_data
    · simp [DerivationTree.CategoryOccurrence.underBinaryLeft, e, hn]
    · simp [DerivationTree.CategoryOccurrence.underBinaryLeft, e, hcat]
    · simp [DerivationTree.CategoryOccurrence.underBinaryLeft, e, hp]
  let oC : Occurrence (DerivationTree.binary (DerivationTree.typeRaiseLeft C₀ u) t₂ Rule.compLeft) :=
    eC.underBinaryLeft (t₂ := t₂) Rule.compLeft
  have hedge : TraceEdge o oC := by
    have hloc : LocalTraceEdge eC e :=
      LocalTraceEdge.trLeft_C (p := p) rfl rfl rfl rfl
    have htr : TraceEdge (e.underBinaryLeft (t₂ := t₂) Rule.compLeft)
        (eC.underBinaryLeft (t₂ := t₂) Rule.compLeft) :=
      TraceEdge.underBinaryLeft (t₂ := t₂) Rule.compLeft
        (Or.inr (Or.inl hloc) : TraceEdge e eC)
    simpa [oC, ho_eq] using htr
  exact VisibleTraceRoute.step hedge
    (compLeft_left_num_route (o := oC) rfl ⟨false :: p, rfl⟩)

/-- Immediate `crossedLeft`/`T>` base for the left-canceled-slot route. -/
theorem crossedLeft_left_typeRaiseRight_num_route
    {Γ Δ : List Category} {C C₀ A₀ : Category}
    {u : DerivationTree Γ A₀} {t₂ : DerivationTree Δ (C₀ ⧹ C)}
    {o : Occurrence (DerivationTree.binary (DerivationTree.typeRaiseRight C₀ u) t₂ Rule.crossedLeft)}
    (hn : o.nodePath = [TreeStep.left]) (hp : ∃ p, o.categoryPath = false :: p) :
    VisibleTraceRoute o := by
  obtain ⟨p, hp⟩ := hp
  have hcat : o.nodeCategory = C₀ ⧸ (A₀ ⧹ C₀) := by
    have h := o.nodeAt
    rw [hn] at h
    have h' : C₀ ⧸ (A₀ ⧹ C₀) = o.nodeCategory := by
      simpa [DerivationTree.categoryAt?] using h
    exact h'.symm
  obtain ⟨X, Y, hXY⟩ := o.isConstructor
  have hconsFalse : ∃ X Y,
      (C₀ ⧸ (A₀ ⧹ C₀)).subcategoryAt? (false :: p) = some (X ⧸ Y) ∨
      (C₀ ⧸ (A₀ ⧹ C₀)).subcategoryAt? (false :: p) = some (X ⧹ Y) := by
    refine ⟨X, Y, ?_⟩
    rwa [hcat, hp] at hXY
  have hconsTrueTrue : ∃ X Y,
      (C₀ ⧸ (A₀ ⧹ C₀)).subcategoryAt? (true :: true :: p) = some (X ⧸ Y) ∨
      (C₀ ⧸ (A₀ ⧹ C₀)).subcategoryAt? (true :: true :: p) = some (X ⧹ Y) := by
    refine ⟨X, Y, ?_⟩
    rw [hcat, hp] at hXY
    simpa [Category.subcategoryAt?] using hXY
  let e : Occurrence (DerivationTree.typeRaiseRight C₀ u) :=
    { nodePath := []
      nodeCategory := C₀ ⧸ (A₀ ⧹ C₀)
      nodeAt := rfl
      categoryPath := false :: p
      isConstructor := hconsFalse }
  let eC : Occurrence (DerivationTree.typeRaiseRight C₀ u) :=
    { nodePath := []
      nodeCategory := C₀ ⧸ (A₀ ⧹ C₀)
      nodeAt := rfl
      categoryPath := true :: true :: p
      isConstructor := hconsTrueTrue }
  have ho_eq : o = e.underBinaryLeft (t₂ := t₂) Rule.crossedLeft := by
    apply DerivationTree.CategoryOccurrence.eq_of_data
    · simp [DerivationTree.CategoryOccurrence.underBinaryLeft, e, hn]
    · simp [DerivationTree.CategoryOccurrence.underBinaryLeft, e, hcat]
    · simp [DerivationTree.CategoryOccurrence.underBinaryLeft, e, hp]
  let oC : Occurrence (DerivationTree.binary (DerivationTree.typeRaiseRight C₀ u) t₂ Rule.crossedLeft) :=
    eC.underBinaryLeft (t₂ := t₂) Rule.crossedLeft
  have hedge : TraceEdge o oC := by
    have hloc : LocalTraceEdge e eC := LocalTraceEdge.trRight_C (p := p) rfl rfl rfl rfl
    have htr : TraceEdge (e.underBinaryLeft (t₂ := t₂) Rule.crossedLeft)
        (eC.underBinaryLeft (t₂ := t₂) Rule.crossedLeft) :=
      TraceEdge.underBinaryLeft (t₂ := t₂) Rule.crossedLeft
        (Or.inl (Or.inl hloc) : TraceEdge e eC)
    simpa [oC, ho_eq] using htr
  exact VisibleTraceRoute.step hedge
    (crossedLeft_left_arg_route (o := oC) rfl ⟨true :: p, rfl⟩)

/-- Immediate `crossedRight`/`T<` base for the right-canceled-slot route. -/
theorem crossedRight_right_typeRaiseLeft_den_route
    {Γ Δ : List Category} {C C₀ A₀ : Category}
    {t₁ : DerivationTree Γ (C ⧸ C₀)} {u : DerivationTree Δ A₀}
    {o : Occurrence (DerivationTree.binary t₁ (DerivationTree.typeRaiseLeft C₀ u) Rule.crossedRight)}
    (hn : o.nodePath = [TreeStep.right]) (hp : ∃ p, o.categoryPath = true :: p) :
    VisibleTraceRoute o := by
  obtain ⟨p, hp⟩ := hp
  have hcat : o.nodeCategory = (C₀ ⧸ A₀) ⧹ C₀ := by
    have h := o.nodeAt
    rw [hn] at h
    have h' : (C₀ ⧸ A₀) ⧹ C₀ = o.nodeCategory := by
      simpa [DerivationTree.categoryAt?] using h
    exact h'.symm
  obtain ⟨X, Y, hXY⟩ := o.isConstructor
  have hconsTrue : ∃ X Y,
      ((C₀ ⧸ A₀) ⧹ C₀).subcategoryAt? (true :: p) = some (X ⧸ Y) ∨
      ((C₀ ⧸ A₀) ⧹ C₀).subcategoryAt? (true :: p) = some (X ⧹ Y) := by
    refine ⟨X, Y, ?_⟩
    rwa [hcat, hp] at hXY
  have hconsFalseFalse : ∃ X Y,
      ((C₀ ⧸ A₀) ⧹ C₀).subcategoryAt? (false :: false :: p) = some (X ⧸ Y) ∨
      ((C₀ ⧸ A₀) ⧹ C₀).subcategoryAt? (false :: false :: p) = some (X ⧹ Y) := by
    refine ⟨X, Y, ?_⟩
    rw [hcat, hp] at hXY
    simpa [Category.subcategoryAt?] using hXY
  let e : Occurrence (DerivationTree.typeRaiseLeft C₀ u) :=
    { nodePath := []
      nodeCategory := (C₀ ⧸ A₀) ⧹ C₀
      nodeAt := rfl
      categoryPath := true :: p
      isConstructor := hconsTrue }
  let eC : Occurrence (DerivationTree.typeRaiseLeft C₀ u) :=
    { nodePath := []
      nodeCategory := (C₀ ⧸ A₀) ⧹ C₀
      nodeAt := rfl
      categoryPath := false :: false :: p
      isConstructor := hconsFalseFalse }
  have ho_eq : o = e.underBinaryRight (t₁ := t₁) Rule.crossedRight := by
    apply DerivationTree.CategoryOccurrence.eq_of_data
    · simp [DerivationTree.CategoryOccurrence.underBinaryRight, e, hn]
    · simp [DerivationTree.CategoryOccurrence.underBinaryRight, e, hcat]
    · simp [DerivationTree.CategoryOccurrence.underBinaryRight, e, hp]
  let oC : Occurrence (DerivationTree.binary t₁ (DerivationTree.typeRaiseLeft C₀ u) Rule.crossedRight) :=
    eC.underBinaryRight (t₁ := t₁) Rule.crossedRight
  have hedge : TraceEdge o oC := by
    have hloc : LocalTraceEdge eC e := LocalTraceEdge.trLeft_C (p := p) rfl rfl rfl rfl
    have htr : TraceEdge (e.underBinaryRight (t₁ := t₁) Rule.crossedRight)
        (eC.underBinaryRight (t₁ := t₁) Rule.crossedRight) :=
      TraceEdge.underBinaryRight (t₁ := t₁) Rule.crossedRight
        (Or.inr (Or.inl hloc) : TraceEdge e eC)
    simpa [oC, ho_eq] using htr
  exact VisibleTraceRoute.step hedge
    (crossedRight_right_num_route (o := oC) rfl ⟨false :: p, rfl⟩)
end VisibleTraceRoute
/-- Leaf terminal case for the `compRight` right-canceled-slot chase. -/
theorem InvisiblePiece.compRight_rightCanceledSlot_leaf_false
    {Γ : List Category} {C B A : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)}
    {P : InvisiblePiece (DerivationTree.binary t₁ (DerivationTree.leaf (B ⧸ A)) Rule.compRight)}
    {o : Occurrence (DerivationTree.binary t₁ (DerivationTree.leaf (B ⧸ A)) Rule.compRight)}
    (ho : o ∈ P.carrier) (hn : o.nodePath = [TreeStep.right]) : False := by
  exact P.all_invisible o ho (Or.inr (Or.inl (by rw [hn]; trivial)))

/-- Leaf terminal case for the `compLeft` left-canceled-slot chase. -/
theorem InvisiblePiece.compLeft_leftCanceledSlot_leaf_false
    {Δ : List Category} {A B C : Category}
    {t₂ : DerivationTree Δ (B ⧹ C)}
    {P : InvisiblePiece (DerivationTree.binary (DerivationTree.leaf (A ⧹ B)) t₂ Rule.compLeft)}
    {o : Occurrence (DerivationTree.binary (DerivationTree.leaf (A ⧹ B)) t₂ Rule.compLeft)}
    (ho : o ∈ P.carrier) (hn : o.nodePath = [TreeStep.left]) : False := by
  exact P.all_invisible o ho (Or.inr (Or.inl (by rw [hn]; trivial)))

/-- Leaf terminal case for the `crossedRight` left canceled-slot chase. -/
theorem InvisiblePiece.crossedRight_leftCanceledSlot_leaf_false
    {Δ : List Category} {C B A : Category} {t₂ : DerivationTree Δ (A ⧹ B)}
    {P : InvisiblePiece (DerivationTree.binary (DerivationTree.leaf (C ⧸ B)) t₂ Rule.crossedRight)}
    {o : Occurrence (DerivationTree.binary (DerivationTree.leaf (C ⧸ B)) t₂ Rule.crossedRight)}
    (ho : o ∈ P.carrier) (hn : o.nodePath = [TreeStep.left]) : False := by
  exact P.all_invisible o ho (Or.inr (Or.inl (by rw [hn]; trivial)))

/-- Leaf terminal case for the `crossedRight` right canceled-slot chase. -/
theorem InvisiblePiece.crossedRight_rightCanceledSlot_leaf_false
    {Γ : List Category} {C B A : Category} {t₁ : DerivationTree Γ (C ⧸ B)}
    {P : InvisiblePiece (DerivationTree.binary t₁ (DerivationTree.leaf (A ⧹ B)) Rule.crossedRight)}
    {o : Occurrence (DerivationTree.binary t₁ (DerivationTree.leaf (A ⧹ B)) Rule.crossedRight)}
    (ho : o ∈ P.carrier) (hn : o.nodePath = [TreeStep.right]) : False := by
  exact P.all_invisible o ho (Or.inr (Or.inl (by rw [hn]; trivial)))

/-- Leaf terminal case for the `crossedLeft` left canceled-slot chase. -/
theorem InvisiblePiece.crossedLeft_leftCanceledSlot_leaf_false
    {Δ : List Category} {B A C : Category} {t₂ : DerivationTree Δ (B ⧹ C)}
    {P : InvisiblePiece (DerivationTree.binary (DerivationTree.leaf (B ⧸ A)) t₂ Rule.crossedLeft)}
    {o : Occurrence (DerivationTree.binary (DerivationTree.leaf (B ⧸ A)) t₂ Rule.crossedLeft)}
    (ho : o ∈ P.carrier) (hn : o.nodePath = [TreeStep.left]) : False := by
  exact P.all_invisible o ho (Or.inr (Or.inl (by rw [hn]; trivial)))

/-- Leaf terminal case for the `crossedLeft` right canceled-slot chase. -/
theorem InvisiblePiece.crossedLeft_rightCanceledSlot_leaf_false
    {Γ : List Category} {B A C : Category} {t₁ : DerivationTree Γ (B ⧸ A)}
    {P : InvisiblePiece (DerivationTree.binary t₁ (DerivationTree.leaf (B ⧹ C)) Rule.crossedLeft)}
    {o : Occurrence (DerivationTree.binary t₁ (DerivationTree.leaf (B ⧹ C)) Rule.crossedLeft)}
    (ho : o ∈ P.carrier) (hn : o.nodePath = [TreeStep.right]) : False := by
  exact P.all_invisible o ho (Or.inr (Or.inl (by rw [hn]; trivial)))
/-- Base escape for the `compRight` root slot chase: if the right premise is a
forward type raise, a boundary-free piece cannot contain the numerator copy of
the premise-root category.  The local `T>` target-copy edge moves the occurrence
to the sibling target copy, and the root `compRight_A` edge then reaches the
visible root occurrence. -/
theorem InvisiblePiece.compRight_rightCanceledSlot_typeRaiseRight_false
    {Γ Δ : List Category} {C C₀ A₀ : Category}
    {t₁ : DerivationTree Γ (C ⧸ C₀)} {u : DerivationTree Δ A₀}
    {P : InvisiblePiece (DerivationTree.binary t₁ (DerivationTree.typeRaiseRight C₀ u) Rule.compRight)}
    (hfree : BoundaryFree P)
    {o : Occurrence (DerivationTree.binary t₁ (DerivationTree.typeRaiseRight C₀ u) Rule.compRight)}
    (ho : o ∈ P.carrier) (hn : o.nodePath = [TreeStep.right])
    (hp : ∃ p, o.categoryPath = false :: p) : False := by
  obtain ⟨p, hp⟩ := hp
  have hcat : o.nodeCategory = C₀ ⧸ (A₀ ⧹ C₀) := by
    have h := o.nodeAt
    rw [hn] at h
    have h' : C₀ ⧸ (A₀ ⧹ C₀) = o.nodeCategory := by
      simpa [DerivationTree.categoryAt?] using h
    exact h'.symm
  obtain ⟨X, Y, hXY⟩ := o.isConstructor
  have hconsFalse : ∃ X Y,
      (C₀ ⧸ (A₀ ⧹ C₀)).subcategoryAt? (false :: p) = some (X ⧸ Y) ∨
      (C₀ ⧸ (A₀ ⧹ C₀)).subcategoryAt? (false :: p) = some (X ⧹ Y) := by
    refine ⟨X, Y, ?_⟩
    rwa [hcat, hp] at hXY
  have hconsTrueTrue : ∃ X Y,
      (C₀ ⧸ (A₀ ⧹ C₀)).subcategoryAt? (true :: true :: p) = some (X ⧸ Y) ∨
      (C₀ ⧸ (A₀ ⧹ C₀)).subcategoryAt? (true :: true :: p) = some (X ⧹ Y) := by
    refine ⟨X, Y, ?_⟩
    rw [hcat, hp] at hXY
    simpa [Category.subcategoryAt?] using hXY
  let e : Occurrence (DerivationTree.typeRaiseRight C₀ u) :=
    { nodePath := []
      nodeCategory := C₀ ⧸ (A₀ ⧹ C₀)
      nodeAt := rfl
      categoryPath := false :: p
      isConstructor := hconsFalse }
  let eC : Occurrence (DerivationTree.typeRaiseRight C₀ u) :=
    { nodePath := []
      nodeCategory := C₀ ⧸ (A₀ ⧹ C₀)
      nodeAt := rfl
      categoryPath := true :: true :: p
      isConstructor := hconsTrueTrue }
  have ho_eq : o = e.underBinaryRight (t₁ := t₁) Rule.compRight := by
    apply DerivationTree.CategoryOccurrence.eq_of_data
    · simp [DerivationTree.CategoryOccurrence.underBinaryRight, e, hn]
    · simp [DerivationTree.CategoryOccurrence.underBinaryRight, e, hcat]
    · simp [DerivationTree.CategoryOccurrence.underBinaryRight, e, hp]
  let oC : Occurrence (DerivationTree.binary t₁ (DerivationTree.typeRaiseRight C₀ u) Rule.compRight) :=
    eC.underBinaryRight (t₁ := t₁) Rule.compRight
  have hedge₁ : TraceEdge o oC := by
    have hloc : LocalTraceEdge e eC :=
      LocalTraceEdge.trRight_C (p := p) rfl rfl rfl rfl
    have htr : TraceEdge (e.underBinaryRight (t₁ := t₁) Rule.compRight)
        (eC.underBinaryRight (t₁ := t₁) Rule.compRight) :=
      TraceEdge.underBinaryRight (t₁ := t₁) Rule.compRight
        (Or.inl (Or.inl hloc) : TraceEdge e eC)
    simpa [oC, ho_eq] using htr
  have hoC : oC ∈ P.carrier := P.closed_traceEdge_of_boundaryFree hfree ho hedge₁
  let v : Occurrence (DerivationTree.binary t₁ (DerivationTree.typeRaiseRight C₀ u) Rule.compRight) :=
    { nodePath := []
      nodeCategory := C ⧸ (A₀ ⧹ C₀)
      nodeAt := rfl
      categoryPath := true :: true :: p
      isConstructor := by
        exact hconsTrueTrue }
  have hedge₂ : TraceEdge oC v := by
    have hloc : LocalTraceEdge oC v :=
      LocalTraceEdge.compRight_A (p := true :: p) rfl rfl rfl rfl
    exact Or.inl (Or.inl hloc)
  exact hfree oC hoC v (Or.inl rfl) hedge₂

/-- Mirror base escape for the `compLeft` root slot chase: if the left premise
is a backward type raise, a boundary-free piece cannot contain the denominator
copy of the premise-root category.  The local `T<` target-copy edge moves the
occurrence to the sibling target copy, and the root `compLeft_A` edge then
reaches the visible root occurrence. -/
theorem InvisiblePiece.compLeft_leftCanceledSlot_typeRaiseLeft_false
    {Γ Δ : List Category} {C C₀ A₀ : Category}
    {u : DerivationTree Γ A₀} {t₂ : DerivationTree Δ (C₀ ⧹ C)}
    {P : InvisiblePiece (DerivationTree.binary (DerivationTree.typeRaiseLeft C₀ u) t₂ Rule.compLeft)}
    (hfree : BoundaryFree P)
    {o : Occurrence (DerivationTree.binary (DerivationTree.typeRaiseLeft C₀ u) t₂ Rule.compLeft)}
    (ho : o ∈ P.carrier) (hn : o.nodePath = [TreeStep.left])
    (hp : ∃ p, o.categoryPath = true :: p) : False := by
  obtain ⟨p, hp⟩ := hp
  have hcat : o.nodeCategory = (C₀ ⧸ A₀) ⧹ C₀ := by
    have h := o.nodeAt
    rw [hn] at h
    have h' : (C₀ ⧸ A₀) ⧹ C₀ = o.nodeCategory := by
      simpa [DerivationTree.categoryAt?] using h
    exact h'.symm
  obtain ⟨X, Y, hXY⟩ := o.isConstructor
  have hconsTrue : ∃ X Y,
      ((C₀ ⧸ A₀) ⧹ C₀).subcategoryAt? (true :: p) = some (X ⧸ Y) ∨
      ((C₀ ⧸ A₀) ⧹ C₀).subcategoryAt? (true :: p) = some (X ⧹ Y) := by
    refine ⟨X, Y, ?_⟩
    rwa [hcat, hp] at hXY
  have hconsFalseFalse : ∃ X Y,
      ((C₀ ⧸ A₀) ⧹ C₀).subcategoryAt? (false :: false :: p) = some (X ⧸ Y) ∨
      ((C₀ ⧸ A₀) ⧹ C₀).subcategoryAt? (false :: false :: p) = some (X ⧹ Y) := by
    refine ⟨X, Y, ?_⟩
    rw [hcat, hp] at hXY
    simpa [Category.subcategoryAt?] using hXY
  let e : Occurrence (DerivationTree.typeRaiseLeft C₀ u) :=
    { nodePath := []
      nodeCategory := (C₀ ⧸ A₀) ⧹ C₀
      nodeAt := rfl
      categoryPath := true :: p
      isConstructor := hconsTrue }
  let eC : Occurrence (DerivationTree.typeRaiseLeft C₀ u) :=
    { nodePath := []
      nodeCategory := (C₀ ⧸ A₀) ⧹ C₀
      nodeAt := rfl
      categoryPath := false :: false :: p
      isConstructor := hconsFalseFalse }
  have ho_eq : o = e.underBinaryLeft (t₂ := t₂) Rule.compLeft := by
    apply DerivationTree.CategoryOccurrence.eq_of_data
    · simp [DerivationTree.CategoryOccurrence.underBinaryLeft, e, hn]
    · simp [DerivationTree.CategoryOccurrence.underBinaryLeft, e, hcat]
    · simp [DerivationTree.CategoryOccurrence.underBinaryLeft, e, hp]
  let oC : Occurrence (DerivationTree.binary (DerivationTree.typeRaiseLeft C₀ u) t₂ Rule.compLeft) :=
    eC.underBinaryLeft (t₂ := t₂) Rule.compLeft
  have hedge₁ : TraceEdge o oC := by
    have hloc : LocalTraceEdge eC e :=
      LocalTraceEdge.trLeft_C (p := p) rfl rfl rfl rfl
    have htr : TraceEdge (e.underBinaryLeft (t₂ := t₂) Rule.compLeft)
        (eC.underBinaryLeft (t₂ := t₂) Rule.compLeft) :=
      TraceEdge.underBinaryLeft (t₂ := t₂) Rule.compLeft
        (Or.inr (Or.inl hloc) : TraceEdge e eC)
    simpa [oC, ho_eq] using htr
  have hoC : oC ∈ P.carrier := P.closed_traceEdge_of_boundaryFree hfree ho hedge₁
  let v : Occurrence (DerivationTree.binary (DerivationTree.typeRaiseLeft C₀ u) t₂ Rule.compLeft) :=
    { nodePath := []
      nodeCategory := (C₀ ⧸ A₀) ⧹ C
      nodeAt := rfl
      categoryPath := false :: false :: p
      isConstructor := by
        exact hconsFalseFalse }
  have hedge₂ : TraceEdge oC v := by
    have hloc : LocalTraceEdge oC v :=
      LocalTraceEdge.compLeft_A (p := false :: p) rfl rfl rfl rfl
    exact Or.inl (Or.inl hloc)
  exact hfree oC hoC v (Or.inl rfl) hedge₂
/-! ## Crossing pieces under root compositions

For each of the four composition rules the same analysis pins a boundary-free
crossing piece to the canceled middle category `B`: the result- and
argument-part positions of each premise root trace-link to the visible tree
root, the premise-root positions are principal, and the `B`-metavariable local
edge forces a matched pair of occurrences on the two premises into the piece.
-/

/-- Under a root `compRight` (`C/B, B/A => C/A`), a boundary-free crossing
piece contains a matched pair inside the canceled middle `B`. -/
theorem InvisiblePiece.crossing_compRight_pair
    {Γ Δ : List Category} {C B A : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (B ⧸ A)}
    {P : InvisiblePiece (DerivationTree.binary t₁ t₂ Rule.compRight)}
    (hfree : BoundaryFree P)
    (hcross : ∃ o : Occurrence (DerivationTree.binary t₁ t₂ Rule.compRight),
      o ∈ P.carrier ∧ (o.nodePath = [TreeStep.left] ∨ o.nodePath = [TreeStep.right])) :
    ∃ p, ∃ o₁ o₂ : Occurrence (DerivationTree.binary t₁ t₂ Rule.compRight),
      o₁ ∈ P.carrier ∧ o₂ ∈ P.carrier ∧
      o₁.nodePath = [TreeStep.left] ∧ o₁.categoryPath = true :: p ∧
      o₂.nodePath = [TreeStep.right] ∧ o₂.categoryPath = false :: p := by
  obtain ⟨o, ho, hside⟩ := hcross
  rcases hside with hnp | hnp
  · have hcat : o.nodeCategory = C ⧸ B := by
      have h := o.nodeAt
      rw [hnp] at h
      have h' : C ⧸ B = o.nodeCategory := by
        simpa [DerivationTree.categoryAt?] using h
      exact h'.symm
    cases hcp : o.categoryPath with
    | nil =>
        exfalso
        apply P.all_invisible o ho
        right; right
        rw [hnp, hcp]
        exact DerivationTree.PrincipalConstructor.compRight_left t₁ t₂
    | cons b q =>
        cases b with
        | false =>
            exfalso
            obtain ⟨X, Y, hXY⟩ := o.isConstructor
            have hconsRoot : ∃ X Y,
                (C ⧸ A).subcategoryAt? (false :: q) = some (X ⧸ Y) ∨
                (C ⧸ A).subcategoryAt? (false :: q) = some (X ⧹ Y) := by
              refine ⟨X, Y, ?_⟩
              rw [hcat, hcp] at hXY
              simpa using hXY
            let o' : Occurrence (DerivationTree.binary t₁ t₂ Rule.compRight) :=
              { nodePath := []
                nodeCategory := C ⧸ A
                nodeAt := rfl
                categoryPath := false :: q
                isConstructor := hconsRoot }
            have hedge : TraceEdge o o' :=
              Or.inl (Or.inl (LocalTraceEdge.compRight_C (p := q) hnp hcp rfl rfl))
            exact hfree o ho o' (Or.inl rfl) hedge
        | true =>
            obtain ⟨X, Y, hXY⟩ := o.isConstructor
            have hcons : ∃ X Y,
                (B ⧸ A).subcategoryAt? (false :: q) = some (X ⧸ Y) ∨
                (B ⧸ A).subcategoryAt? (false :: q) = some (X ⧹ Y) := by
              refine ⟨X, Y, ?_⟩
              rw [hcat, hcp] at hXY
              simpa using hXY
            let o' : Occurrence (DerivationTree.binary t₁ t₂ Rule.compRight) :=
              { nodePath := [TreeStep.right]
                nodeCategory := B ⧸ A
                nodeAt := by simp [DerivationTree.categoryAt?]
                categoryPath := false :: q
                isConstructor := hcons }
            have hedge : TraceEdge o o' :=
              Or.inl (Or.inl (LocalTraceEdge.compRight_B (p := q) hnp hcp rfl rfl))
            by_cases hv : o'.Visible
            · exact absurd hedge (hfree o ho o' hv)
            · exact ⟨q, o, o',
                ho, P.closed o ho o' ⟨P.all_invisible o ho, hv, hedge⟩,
                hnp, hcp, rfl, rfl⟩
  · have hcat : o.nodeCategory = B ⧸ A := by
      have h := o.nodeAt
      rw [hnp] at h
      have h' : B ⧸ A = o.nodeCategory := by
        simpa [DerivationTree.categoryAt?] using h
      exact h'.symm
    cases hcp : o.categoryPath with
    | nil =>
        exfalso
        apply P.all_invisible o ho
        right; right
        rw [hnp, hcp]
        exact DerivationTree.PrincipalConstructor.compRight_right t₁ t₂
    | cons b q =>
        cases b with
        | true =>
            exfalso
            obtain ⟨X, Y, hXY⟩ := o.isConstructor
            have hconsRoot : ∃ X Y,
                (C ⧸ A).subcategoryAt? (true :: q) = some (X ⧸ Y) ∨
                (C ⧸ A).subcategoryAt? (true :: q) = some (X ⧹ Y) := by
              refine ⟨X, Y, ?_⟩
              rw [hcat, hcp] at hXY
              simpa using hXY
            let o' : Occurrence (DerivationTree.binary t₁ t₂ Rule.compRight) :=
              { nodePath := []
                nodeCategory := C ⧸ A
                nodeAt := rfl
                categoryPath := true :: q
                isConstructor := hconsRoot }
            have hedge : TraceEdge o o' :=
              Or.inl (Or.inl (LocalTraceEdge.compRight_A (p := q) hnp hcp rfl rfl))
            exact hfree o ho o' (Or.inl rfl) hedge
        | false =>
            obtain ⟨X, Y, hXY⟩ := o.isConstructor
            have hcons : ∃ X Y,
                (C ⧸ B).subcategoryAt? (true :: q) = some (X ⧸ Y) ∨
                (C ⧸ B).subcategoryAt? (true :: q) = some (X ⧹ Y) := by
              refine ⟨X, Y, ?_⟩
              rw [hcat, hcp] at hXY
              simpa using hXY
            let o' : Occurrence (DerivationTree.binary t₁ t₂ Rule.compRight) :=
              { nodePath := [TreeStep.left]
                nodeCategory := C ⧸ B
                nodeAt := by simp [DerivationTree.categoryAt?]
                categoryPath := true :: q
                isConstructor := hcons }
            have hedge : TraceEdge o o' :=
              Or.inr (Or.inl (LocalTraceEdge.compRight_B (p := q) rfl rfl hnp hcp))
            by_cases hv : o'.Visible
            · exact absurd hedge (hfree o ho o' hv)
            · exact ⟨q, o', o,
                P.closed o ho o' ⟨P.all_invisible o ho, hv, hedge⟩, ho,
                rfl, rfl, hnp, hcp⟩


/-- Under a root `compLeft` (`A⧹B, B⧹C => A⧹C`), a boundary-free crossing
piece contains a matched pair inside the canceled middle `B`. -/
theorem InvisiblePiece.crossing_compLeft_pair
    {Γ Δ : List Category} {A B C : Category}
    {t₁ : DerivationTree Γ (A ⧹ B)} {t₂ : DerivationTree Δ (B ⧹ C)}
    {P : InvisiblePiece (DerivationTree.binary t₁ t₂ Rule.compLeft)}
    (hfree : BoundaryFree P)
    (hcross : ∃ o : Occurrence (DerivationTree.binary t₁ t₂ Rule.compLeft),
      o ∈ P.carrier ∧ (o.nodePath = [TreeStep.left] ∨ o.nodePath = [TreeStep.right])) :
    ∃ p, ∃ o₁ o₂ : Occurrence (DerivationTree.binary t₁ t₂ Rule.compLeft),
      o₁ ∈ P.carrier ∧ o₂ ∈ P.carrier ∧
      o₁.nodePath = [TreeStep.left] ∧ o₁.categoryPath = true :: p ∧
      o₂.nodePath = [TreeStep.right] ∧ o₂.categoryPath = false :: p := by
  obtain ⟨o, ho, hside⟩ := hcross
  rcases hside with hnp | hnp
  · have hcat : o.nodeCategory = A ⧹ B := by
      have h := o.nodeAt
      rw [hnp] at h
      have h' : A ⧹ B = o.nodeCategory := by
        simpa [DerivationTree.categoryAt?] using h
      exact h'.symm
    cases hcp : o.categoryPath with
    | nil =>
        exfalso
        apply P.all_invisible o ho
        right; right
        rw [hnp, hcp]
        exact DerivationTree.PrincipalConstructor.compLeft_left t₁ t₂
    | cons b q =>
        cases b with
        | false =>
            exfalso
            obtain ⟨X, Y, hXY⟩ := o.isConstructor
            have hconsRoot : ∃ X Y,
                (A ⧹ C).subcategoryAt? (false :: q) = some (X ⧸ Y) ∨
                (A ⧹ C).subcategoryAt? (false :: q) = some (X ⧹ Y) := by
              refine ⟨X, Y, ?_⟩
              rw [hcat, hcp] at hXY
              simpa using hXY
            let o' : Occurrence (DerivationTree.binary t₁ t₂ Rule.compLeft) :=
              { nodePath := []
                nodeCategory := A ⧹ C
                nodeAt := rfl
                categoryPath := false :: q
                isConstructor := hconsRoot }
            have hedge : TraceEdge o o' :=
              Or.inl (Or.inl (LocalTraceEdge.compLeft_A (p := q) hnp hcp rfl rfl))
            exact hfree o ho o' (Or.inl rfl) hedge
        | true =>
            obtain ⟨X, Y, hXY⟩ := o.isConstructor
            have hcons : ∃ X Y,
                (B ⧹ C).subcategoryAt? (false :: q) = some (X ⧸ Y) ∨
                (B ⧹ C).subcategoryAt? (false :: q) = some (X ⧹ Y) := by
              refine ⟨X, Y, ?_⟩
              rw [hcat, hcp] at hXY
              simpa using hXY
            let o' : Occurrence (DerivationTree.binary t₁ t₂ Rule.compLeft) :=
              { nodePath := [TreeStep.right]
                nodeCategory := B ⧹ C
                nodeAt := by simp [DerivationTree.categoryAt?]
                categoryPath := false :: q
                isConstructor := hcons }
            have hedge : TraceEdge o o' :=
              Or.inl (Or.inl (LocalTraceEdge.compLeft_B (p := q) hnp hcp rfl rfl))
            by_cases hv : o'.Visible
            · exact absurd hedge (hfree o ho o' hv)
            · exact ⟨q, o, o',
                ho, P.closed o ho o' ⟨P.all_invisible o ho, hv, hedge⟩,
                hnp, hcp, rfl, rfl⟩
  · have hcat : o.nodeCategory = B ⧹ C := by
      have h := o.nodeAt
      rw [hnp] at h
      have h' : B ⧹ C = o.nodeCategory := by
        simpa [DerivationTree.categoryAt?] using h
      exact h'.symm
    cases hcp : o.categoryPath with
    | nil =>
        exfalso
        apply P.all_invisible o ho
        right; right
        rw [hnp, hcp]
        exact DerivationTree.PrincipalConstructor.compLeft_right t₁ t₂
    | cons b q =>
        cases b with
        | true =>
            exfalso
            obtain ⟨X, Y, hXY⟩ := o.isConstructor
            have hconsRoot : ∃ X Y,
                (A ⧹ C).subcategoryAt? (true :: q) = some (X ⧸ Y) ∨
                (A ⧹ C).subcategoryAt? (true :: q) = some (X ⧹ Y) := by
              refine ⟨X, Y, ?_⟩
              rw [hcat, hcp] at hXY
              simpa using hXY
            let o' : Occurrence (DerivationTree.binary t₁ t₂ Rule.compLeft) :=
              { nodePath := []
                nodeCategory := A ⧹ C
                nodeAt := rfl
                categoryPath := true :: q
                isConstructor := hconsRoot }
            have hedge : TraceEdge o o' :=
              Or.inl (Or.inl (LocalTraceEdge.compLeft_C (p := q) hnp hcp rfl rfl))
            exact hfree o ho o' (Or.inl rfl) hedge
        | false =>
            obtain ⟨X, Y, hXY⟩ := o.isConstructor
            have hcons : ∃ X Y,
                (A ⧹ B).subcategoryAt? (true :: q) = some (X ⧸ Y) ∨
                (A ⧹ B).subcategoryAt? (true :: q) = some (X ⧹ Y) := by
              refine ⟨X, Y, ?_⟩
              rw [hcat, hcp] at hXY
              simpa using hXY
            let o' : Occurrence (DerivationTree.binary t₁ t₂ Rule.compLeft) :=
              { nodePath := [TreeStep.left]
                nodeCategory := A ⧹ B
                nodeAt := by simp [DerivationTree.categoryAt?]
                categoryPath := true :: q
                isConstructor := hcons }
            have hedge : TraceEdge o o' :=
              Or.inr (Or.inl (LocalTraceEdge.compLeft_B (p := q) rfl rfl hnp hcp))
            by_cases hv : o'.Visible
            · exact absurd hedge (hfree o ho o' hv)
            · exact ⟨q, o', o,
                P.closed o ho o' ⟨P.all_invisible o ho, hv, hedge⟩, ho,
                rfl, rfl, hnp, hcp⟩

/-- Under a root `crossedRight` (`C/B, A⧹B => A⧹C`), a boundary-free crossing
piece contains a matched pair inside the canceled middle `B`. -/
theorem InvisiblePiece.crossing_crossedRight_pair
    {Γ Δ : List Category} {C B A : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (A ⧹ B)}
    {P : InvisiblePiece (DerivationTree.binary t₁ t₂ Rule.crossedRight)}
    (hfree : BoundaryFree P)
    (hcross : ∃ o : Occurrence (DerivationTree.binary t₁ t₂ Rule.crossedRight),
      o ∈ P.carrier ∧ (o.nodePath = [TreeStep.left] ∨ o.nodePath = [TreeStep.right])) :
    ∃ p, ∃ o₁ o₂ : Occurrence (DerivationTree.binary t₁ t₂ Rule.crossedRight),
      o₁ ∈ P.carrier ∧ o₂ ∈ P.carrier ∧
      o₁.nodePath = [TreeStep.left] ∧ o₁.categoryPath = true :: p ∧
      o₂.nodePath = [TreeStep.right] ∧ o₂.categoryPath = true :: p := by
  obtain ⟨o, ho, hside⟩ := hcross
  rcases hside with hnp | hnp
  · have hcat : o.nodeCategory = C ⧸ B := by
      have h := o.nodeAt
      rw [hnp] at h
      have h' : C ⧸ B = o.nodeCategory := by
        simpa [DerivationTree.categoryAt?] using h
      exact h'.symm
    cases hcp : o.categoryPath with
    | nil =>
        exfalso
        apply P.all_invisible o ho
        right; right
        rw [hnp, hcp]
        exact DerivationTree.PrincipalConstructor.crossedRight_left t₁ t₂
    | cons b q =>
        cases b with
        | false =>
            exfalso
            obtain ⟨X, Y, hXY⟩ := o.isConstructor
            have hconsRoot : ∃ X Y,
                (A ⧹ C).subcategoryAt? (true :: q) = some (X ⧸ Y) ∨
                (A ⧹ C).subcategoryAt? (true :: q) = some (X ⧹ Y) := by
              refine ⟨X, Y, ?_⟩
              rw [hcat, hcp] at hXY
              simpa using hXY
            let o' : Occurrence (DerivationTree.binary t₁ t₂ Rule.crossedRight) :=
              { nodePath := []
                nodeCategory := A ⧹ C
                nodeAt := rfl
                categoryPath := true :: q
                isConstructor := hconsRoot }
            have hedge : TraceEdge o o' :=
              Or.inl (Or.inl (LocalTraceEdge.crossedRight_C (p := q) hnp hcp rfl rfl))
            exact hfree o ho o' (Or.inl rfl) hedge
        | true =>
            obtain ⟨X, Y, hXY⟩ := o.isConstructor
            have hcons : ∃ X Y,
                (A ⧹ B).subcategoryAt? (true :: q) = some (X ⧸ Y) ∨
                (A ⧹ B).subcategoryAt? (true :: q) = some (X ⧹ Y) := by
              refine ⟨X, Y, ?_⟩
              rw [hcat, hcp] at hXY
              simpa using hXY
            let o' : Occurrence (DerivationTree.binary t₁ t₂ Rule.crossedRight) :=
              { nodePath := [TreeStep.right]
                nodeCategory := A ⧹ B
                nodeAt := by simp [DerivationTree.categoryAt?]
                categoryPath := true :: q
                isConstructor := hcons }
            have hedge : TraceEdge o o' :=
              Or.inl (Or.inl (LocalTraceEdge.crossedRight_B (p := q) hnp hcp rfl rfl))
            by_cases hv : o'.Visible
            · exact absurd hedge (hfree o ho o' hv)
            · exact ⟨q, o, o',
                ho, P.closed o ho o' ⟨P.all_invisible o ho, hv, hedge⟩,
                hnp, hcp, rfl, rfl⟩
  · have hcat : o.nodeCategory = A ⧹ B := by
      have h := o.nodeAt
      rw [hnp] at h
      have h' : A ⧹ B = o.nodeCategory := by
        simpa [DerivationTree.categoryAt?] using h
      exact h'.symm
    cases hcp : o.categoryPath with
    | nil =>
        exfalso
        apply P.all_invisible o ho
        right; right
        rw [hnp, hcp]
        exact DerivationTree.PrincipalConstructor.crossedRight_right t₁ t₂
    | cons b q =>
        cases b with
        | false =>
            exfalso
            obtain ⟨X, Y, hXY⟩ := o.isConstructor
            have hconsRoot : ∃ X Y,
                (A ⧹ C).subcategoryAt? (false :: q) = some (X ⧸ Y) ∨
                (A ⧹ C).subcategoryAt? (false :: q) = some (X ⧹ Y) := by
              refine ⟨X, Y, ?_⟩
              rw [hcat, hcp] at hXY
              simpa using hXY
            let o' : Occurrence (DerivationTree.binary t₁ t₂ Rule.crossedRight) :=
              { nodePath := []
                nodeCategory := A ⧹ C
                nodeAt := rfl
                categoryPath := false :: q
                isConstructor := hconsRoot }
            have hedge : TraceEdge o o' :=
              Or.inl (Or.inl (LocalTraceEdge.crossedRight_A (p := q) hnp hcp rfl rfl))
            exact hfree o ho o' (Or.inl rfl) hedge
        | true =>
            obtain ⟨X, Y, hXY⟩ := o.isConstructor
            have hcons : ∃ X Y,
                (C ⧸ B).subcategoryAt? (true :: q) = some (X ⧸ Y) ∨
                (C ⧸ B).subcategoryAt? (true :: q) = some (X ⧹ Y) := by
              refine ⟨X, Y, ?_⟩
              rw [hcat, hcp] at hXY
              simpa using hXY
            let o' : Occurrence (DerivationTree.binary t₁ t₂ Rule.crossedRight) :=
              { nodePath := [TreeStep.left]
                nodeCategory := C ⧸ B
                nodeAt := by simp [DerivationTree.categoryAt?]
                categoryPath := true :: q
                isConstructor := hcons }
            have hedge : TraceEdge o o' :=
              Or.inr (Or.inl (LocalTraceEdge.crossedRight_B (p := q) rfl rfl hnp hcp))
            by_cases hv : o'.Visible
            · exact absurd hedge (hfree o ho o' hv)
            · exact ⟨q, o', o,
                P.closed o ho o' ⟨P.all_invisible o ho, hv, hedge⟩, ho,
                rfl, rfl, hnp, hcp⟩

/-- Under a root `crossedLeft` (`B/A, B⧹C => C/A`), a boundary-free crossing
piece contains a matched pair inside the canceled middle `B`. -/
theorem InvisiblePiece.crossing_crossedLeft_pair
    {Γ Δ : List Category} {B A C : Category}
    {t₁ : DerivationTree Γ (B ⧸ A)} {t₂ : DerivationTree Δ (B ⧹ C)}
    {P : InvisiblePiece (DerivationTree.binary t₁ t₂ Rule.crossedLeft)}
    (hfree : BoundaryFree P)
    (hcross : ∃ o : Occurrence (DerivationTree.binary t₁ t₂ Rule.crossedLeft),
      o ∈ P.carrier ∧ (o.nodePath = [TreeStep.left] ∨ o.nodePath = [TreeStep.right])) :
    ∃ p, ∃ o₁ o₂ : Occurrence (DerivationTree.binary t₁ t₂ Rule.crossedLeft),
      o₁ ∈ P.carrier ∧ o₂ ∈ P.carrier ∧
      o₁.nodePath = [TreeStep.left] ∧ o₁.categoryPath = false :: p ∧
      o₂.nodePath = [TreeStep.right] ∧ o₂.categoryPath = false :: p := by
  obtain ⟨o, ho, hside⟩ := hcross
  rcases hside with hnp | hnp
  · have hcat : o.nodeCategory = B ⧸ A := by
      have h := o.nodeAt
      rw [hnp] at h
      have h' : B ⧸ A = o.nodeCategory := by
        simpa [DerivationTree.categoryAt?] using h
      exact h'.symm
    cases hcp : o.categoryPath with
    | nil =>
        exfalso
        apply P.all_invisible o ho
        right; right
        rw [hnp, hcp]
        exact DerivationTree.PrincipalConstructor.crossedLeft_left t₁ t₂
    | cons b q =>
        cases b with
        | true =>
            exfalso
            obtain ⟨X, Y, hXY⟩ := o.isConstructor
            have hconsRoot : ∃ X Y,
                (C ⧸ A).subcategoryAt? (true :: q) = some (X ⧸ Y) ∨
                (C ⧸ A).subcategoryAt? (true :: q) = some (X ⧹ Y) := by
              refine ⟨X, Y, ?_⟩
              rw [hcat, hcp] at hXY
              simpa using hXY
            let o' : Occurrence (DerivationTree.binary t₁ t₂ Rule.crossedLeft) :=
              { nodePath := []
                nodeCategory := C ⧸ A
                nodeAt := rfl
                categoryPath := true :: q
                isConstructor := hconsRoot }
            have hedge : TraceEdge o o' :=
              Or.inl (Or.inl (LocalTraceEdge.crossedLeft_A (p := q) hnp hcp rfl rfl))
            exact hfree o ho o' (Or.inl rfl) hedge
        | false =>
            obtain ⟨X, Y, hXY⟩ := o.isConstructor
            have hcons : ∃ X Y,
                (B ⧹ C).subcategoryAt? (false :: q) = some (X ⧸ Y) ∨
                (B ⧹ C).subcategoryAt? (false :: q) = some (X ⧹ Y) := by
              refine ⟨X, Y, ?_⟩
              rw [hcat, hcp] at hXY
              simpa using hXY
            let o' : Occurrence (DerivationTree.binary t₁ t₂ Rule.crossedLeft) :=
              { nodePath := [TreeStep.right]
                nodeCategory := B ⧹ C
                nodeAt := by simp [DerivationTree.categoryAt?]
                categoryPath := false :: q
                isConstructor := hcons }
            have hedge : TraceEdge o o' :=
              Or.inl (Or.inl (LocalTraceEdge.crossedLeft_B (p := q) hnp hcp rfl rfl))
            by_cases hv : o'.Visible
            · exact absurd hedge (hfree o ho o' hv)
            · exact ⟨q, o, o',
                ho, P.closed o ho o' ⟨P.all_invisible o ho, hv, hedge⟩,
                hnp, hcp, rfl, rfl⟩
  · have hcat : o.nodeCategory = B ⧹ C := by
      have h := o.nodeAt
      rw [hnp] at h
      have h' : B ⧹ C = o.nodeCategory := by
        simpa [DerivationTree.categoryAt?] using h
      exact h'.symm
    cases hcp : o.categoryPath with
    | nil =>
        exfalso
        apply P.all_invisible o ho
        right; right
        rw [hnp, hcp]
        exact DerivationTree.PrincipalConstructor.crossedLeft_right t₁ t₂
    | cons b q =>
        cases b with
        | true =>
            exfalso
            obtain ⟨X, Y, hXY⟩ := o.isConstructor
            have hconsRoot : ∃ X Y,
                (C ⧸ A).subcategoryAt? (false :: q) = some (X ⧸ Y) ∨
                (C ⧸ A).subcategoryAt? (false :: q) = some (X ⧹ Y) := by
              refine ⟨X, Y, ?_⟩
              rw [hcat, hcp] at hXY
              simpa using hXY
            let o' : Occurrence (DerivationTree.binary t₁ t₂ Rule.crossedLeft) :=
              { nodePath := []
                nodeCategory := C ⧸ A
                nodeAt := rfl
                categoryPath := false :: q
                isConstructor := hconsRoot }
            have hedge : TraceEdge o o' :=
              Or.inl (Or.inl (LocalTraceEdge.crossedLeft_C (p := q) hnp hcp rfl rfl))
            exact hfree o ho o' (Or.inl rfl) hedge
        | false =>
            obtain ⟨X, Y, hXY⟩ := o.isConstructor
            have hcons : ∃ X Y,
                (B ⧸ A).subcategoryAt? (false :: q) = some (X ⧸ Y) ∨
                (B ⧸ A).subcategoryAt? (false :: q) = some (X ⧹ Y) := by
              refine ⟨X, Y, ?_⟩
              rw [hcat, hcp] at hXY
              simpa using hXY
            let o' : Occurrence (DerivationTree.binary t₁ t₂ Rule.crossedLeft) :=
              { nodePath := [TreeStep.left]
                nodeCategory := B ⧸ A
                nodeAt := by simp [DerivationTree.categoryAt?]
                categoryPath := false :: q
                isConstructor := hcons }
            have hedge : TraceEdge o o' :=
              Or.inr (Or.inl (LocalTraceEdge.crossedLeft_B (p := q) rfl rfl hnp hcp))
            by_cases hv : o'.Visible
            · exact absurd hedge (hfree o ho o' hv)
            · exact ⟨q, o', o,
                P.closed o ho o' ⟨P.all_invisible o ho, hv, hedge⟩, ho,
                rfl, rfl, hnp, hcp⟩


/-! ## Subtree addressing

Groundwork for chasing a crossing piece into arbitrary-depth premises:
`SubtreeAt t π w` says `w` is the subtree of `t` at node address `π`.
Occurrences and trace edges of the subtree lift to `t` along the address, so
piece-membership facts can be transported between a subtree's local rule
instance and the global piece.
-/

/-- `w` is the subtree of `t` at node address `π`. -/
inductive DerivationTree.SubtreeAt :
    {Γ : List Category} → {A : Category} → DerivationTree Γ A →
      NodePath → {Δ : List Category} → {B : Category} → DerivationTree Δ B → Prop where
  | refl {Γ : List Category} {A : Category} (t : DerivationTree Γ A) :
      DerivationTree.SubtreeAt t [] t
  | underUnaryRight {Γ Δ : List Category} {A B C : Category}
      {u : DerivationTree Γ A} {π : NodePath} {w : DerivationTree Δ B}
      (h : DerivationTree.SubtreeAt u π w) :
      DerivationTree.SubtreeAt (DerivationTree.typeRaiseRight C u) (TreeStep.unary :: π) w
  | underUnaryLeft {Γ Δ : List Category} {A B C : Category}
      {u : DerivationTree Γ A} {π : NodePath} {w : DerivationTree Δ B}
      (h : DerivationTree.SubtreeAt u π w) :
      DerivationTree.SubtreeAt (DerivationTree.typeRaiseLeft C u) (TreeStep.unary :: π) w
  | underBinaryLeft {Γ₁ Γ₂ Δ : List Category} {A B C X : Category}
      {t₁ : DerivationTree Γ₁ A} {t₂ : DerivationTree Γ₂ B} {r : Rule A B C}
      {π : NodePath} {w : DerivationTree Δ X}
      (h : DerivationTree.SubtreeAt t₁ π w) :
      DerivationTree.SubtreeAt (DerivationTree.binary t₁ t₂ r) (TreeStep.left :: π) w
  | underBinaryRight {Γ₁ Γ₂ Δ : List Category} {A B C X : Category}
      {t₁ : DerivationTree Γ₁ A} {t₂ : DerivationTree Γ₂ B} {r : Rule A B C}
      {π : NodePath} {w : DerivationTree Δ X}
      (h : DerivationTree.SubtreeAt t₂ π w) :
      DerivationTree.SubtreeAt (DerivationTree.binary t₁ t₂ r) (TreeStep.right :: π) w

namespace DerivationTree.SubtreeAt

/-- Subtree addresses compose. -/
theorem trans {Γ A Δ B Θ X : _} {t : DerivationTree Γ A} {π : NodePath}
    {w : DerivationTree Δ B} {ρ : NodePath} {v : DerivationTree Θ X}
    (h₁ : DerivationTree.SubtreeAt t π w) (h₂ : DerivationTree.SubtreeAt w ρ v) :
    DerivationTree.SubtreeAt t (π ++ ρ) v := by
  induction h₁ with
  | refl t => exact h₂
  | underUnaryRight h ih => exact .underUnaryRight (ih h₂)
  | underUnaryLeft h ih => exact .underUnaryLeft (ih h₂)
  | underBinaryLeft h ih => exact .underBinaryLeft (ih h₂)
  | underBinaryRight h ih => exact .underBinaryRight (ih h₂)

/-- Category lookup below a subtree address factors through the subtree. -/
theorem categoryAt?_append {Γ A Δ B : _} {t : DerivationTree Γ A} {π : NodePath}
    {w : DerivationTree Δ B} (h : DerivationTree.SubtreeAt t π w) (p : NodePath) :
    t.categoryAt? (π ++ p) = w.categoryAt? p := by
  induction h with
  | refl t => rfl
  | underUnaryRight h ih => exact ih
  | underUnaryLeft h ih => exact ih
  | underBinaryLeft h ih => exact ih
  | underBinaryRight h ih => exact ih

/-- Lift an occurrence of the subtree at `π` to an occurrence of `t`. -/
def lift {Γ A Δ B : _} {t : DerivationTree Γ A} {π : NodePath}
    {w : DerivationTree Δ B} (h : DerivationTree.SubtreeAt t π w)
    (o : Occurrence w) : Occurrence t where
  nodePath := π ++ o.nodePath
  nodeCategory := o.nodeCategory
  nodeAt := by rw [h.categoryAt?_append]; exact o.nodeAt
  categoryPath := o.categoryPath
  isConstructor := o.isConstructor

@[simp]
theorem lift_nodePath {Γ A Δ B : _} {t : DerivationTree Γ A} {π : NodePath}
    {w : DerivationTree Δ B} (h : DerivationTree.SubtreeAt t π w) (o : Occurrence w) :
    (h.lift o).nodePath = π ++ o.nodePath := rfl

@[simp]
theorem lift_categoryPath {Γ A Δ B : _} {t : DerivationTree Γ A} {π : NodePath}
    {w : DerivationTree Δ B} (h : DerivationTree.SubtreeAt t π w) (o : Occurrence w) :
    (h.lift o).categoryPath = o.categoryPath := rfl

theorem lift_refl {Γ A : _} {t : DerivationTree Γ A} (o : Occurrence t) :
    (DerivationTree.SubtreeAt.refl t).lift o = o :=
  DerivationTree.CategoryOccurrence.eq_of_data rfl rfl rfl

theorem lift_underUnaryRight {Γ Δ : List Category} {A B C : Category}
    {u : DerivationTree Γ A} {π : NodePath} {w : DerivationTree Δ B}
    (h : DerivationTree.SubtreeAt u π w) (o : Occurrence w) :
    (DerivationTree.SubtreeAt.underUnaryRight (C := C) h).lift o =
      (h.lift o).underUnaryRight C :=
  DerivationTree.CategoryOccurrence.eq_of_data rfl rfl rfl

theorem lift_underUnaryLeft {Γ Δ : List Category} {A B C : Category}
    {u : DerivationTree Γ A} {π : NodePath} {w : DerivationTree Δ B}
    (h : DerivationTree.SubtreeAt u π w) (o : Occurrence w) :
    (DerivationTree.SubtreeAt.underUnaryLeft (C := C) h).lift o =
      (h.lift o).underUnaryLeft C :=
  DerivationTree.CategoryOccurrence.eq_of_data rfl rfl rfl

theorem lift_underBinaryLeft {Γ₁ Γ₂ Δ : List Category} {A B C X : Category}
    {t₁ : DerivationTree Γ₁ A} {t₂ : DerivationTree Γ₂ B} {r : Rule A B C}
    {π : NodePath} {w : DerivationTree Δ X}
    (h : DerivationTree.SubtreeAt t₁ π w) (o : Occurrence w) :
    (DerivationTree.SubtreeAt.underBinaryLeft (t₂ := t₂) (r := r) h).lift o =
      (h.lift o).underBinaryLeft r :=
  DerivationTree.CategoryOccurrence.eq_of_data rfl rfl rfl

theorem lift_underBinaryRight {Γ₁ Γ₂ Δ : List Category} {A B C X : Category}
    {t₁ : DerivationTree Γ₁ A} {t₂ : DerivationTree Γ₂ B} {r : Rule A B C}
    {π : NodePath} {w : DerivationTree Δ X}
    (h : DerivationTree.SubtreeAt t₂ π w) (o : Occurrence w) :
    (DerivationTree.SubtreeAt.underBinaryRight (t₁ := t₁) (r := r) h).lift o =
      (h.lift o).underBinaryRight r :=
  DerivationTree.CategoryOccurrence.eq_of_data rfl rfl rfl

/-- Trace edges of a subtree lift to trace edges of the whole tree. -/
theorem lift_traceEdge {Γ A Δ B : _} {t : DerivationTree Γ A} {π : NodePath}
    {w : DerivationTree Δ B} (h : DerivationTree.SubtreeAt t π w) :
    ∀ {o₁ o₂ : Occurrence w}, TraceEdge o₁ o₂ →
      TraceEdge (h.lift o₁) (h.lift o₂) := by
  induction h with
  | refl t =>
      intro o₁ o₂ he
      rw [lift_refl o₁, lift_refl o₂]
      exact he
  | underUnaryRight h ih =>
      intro o₁ o₂ he
      rw [lift_underUnaryRight h o₁, lift_underUnaryRight h o₂]
      exact TraceEdge.underUnaryRight _ (ih he)
  | underUnaryLeft h ih =>
      intro o₁ o₂ he
      rw [lift_underUnaryLeft h o₁, lift_underUnaryLeft h o₂]
      exact TraceEdge.underUnaryLeft _ (ih he)
  | underBinaryLeft h ih =>
      intro o₁ o₂ he
      rw [lift_underBinaryLeft h o₁, lift_underBinaryLeft h o₂]
      exact TraceEdge.underBinaryLeft _ (ih he)
  | underBinaryRight h ih =>
      intro o₁ o₂ he
      rw [lift_underBinaryRight h o₁, lift_underBinaryRight h o₂]
      exact TraceEdge.underBinaryRight _ (ih he)

/-- A subtree whose own root is a leaf node sits at a leaf node of the whole
tree.  In particular a leaf subtree does. -/
theorem isLeafNode_of_isLeafNode {Γ A Δ B : _} {t : DerivationTree Γ A}
    {π : NodePath} {w : DerivationTree Δ B}
    (h : DerivationTree.SubtreeAt t π w) (hw : w.isLeafNode []) :
    t.isLeafNode π := by
  induction h with
  | refl t => exact hw
  | underUnaryRight h ih => exact ih hw
  | underUnaryLeft h ih => exact ih hw
  | underBinaryLeft h ih => exact ih hw
  | underBinaryRight h ih => exact ih hw

/-- A leaf subtree sits at a leaf node of the whole tree. -/
theorem isLeafNode_of_leaf {Γ : List Category} {A X : Category}
    {t : DerivationTree Γ A} {π : NodePath}
    (h : DerivationTree.SubtreeAt t π (DerivationTree.leaf X)) :
    t.isLeafNode π :=
  h.isLeafNode_of_isLeafNode trivial

/-- The category at a subtree address is the subtree's root category. -/
theorem categoryAt?_self {Γ A Δ B : _} {t : DerivationTree Γ A} {π : NodePath}
    {w : DerivationTree Δ B} (h : DerivationTree.SubtreeAt t π w) :
    t.categoryAt? π = some B := by
  have h2 := h.categoryAt?_append []
  rw [List.append_nil] at h2
  rw [h2]
  exact DerivationTree.categoryAt?_root w

/-- An occurrence of `t` at a subtree address corresponds to a root-node
occurrence of the subtree. -/
theorem exists_rootOcc {Γ A Δ B : _} {t : DerivationTree Γ A} {π : NodePath}
    {w : DerivationTree Δ B} (hw : DerivationTree.SubtreeAt t π w)
    (o : Occurrence t) (hnp : o.nodePath = π) :
    ∃ e : Occurrence w, e.nodePath = [] ∧ e.nodeCategory = B ∧
      e.categoryPath = o.categoryPath ∧ hw.lift e = o := by
  have hcat : o.nodeCategory = B := by
    have h := o.nodeAt
    rw [hnp, hw.categoryAt?_self] at h
    exact (Option.some.inj h).symm
  refine ⟨{ nodePath := []
            nodeCategory := B
            nodeAt := by simp
            categoryPath := o.categoryPath
            isConstructor := by rw [← hcat]; exact o.isConstructor },
    rfl, rfl, rfl, ?_⟩
  exact Occurrence.eq_of_key_eq (by simp [Occurrence.key, hnp])

/-- Principal constructors of a subtree lift to principal constructors of the
whole tree. -/
theorem principal_lift {Γ A Δ B : _} {t : DerivationTree Γ A} {π : NodePath}
    {w : DerivationTree Δ B} (h : DerivationTree.SubtreeAt t π w) :
    ∀ {np : NodePath} {cpos : CategoryPath},
      DerivationTree.PrincipalConstructor w np cpos →
        DerivationTree.PrincipalConstructor t (π ++ np) cpos := by
  induction h with
  | refl t =>
      intro np cpos hp
      exact hp
  | underUnaryRight h ih =>
      intro np cpos hp
      exact .underUnaryRight _ (ih hp)
  | underUnaryLeft h ih =>
      intro np cpos hp
      exact .underUnaryLeft _ (ih hp)
  | underBinaryLeft h ih =>
      intro np cpos hp
      exact .underBinaryLeft _ (ih hp)
  | underBinaryRight h ih =>
      intro np cpos hp
      exact .underBinaryRight _ (ih hp)

end DerivationTree.SubtreeAt


/-! ## The chase: every boundary-free piece is anchored at a type raise

Starting from any occurrence of a boundary-free piece and descending through
the conclusion metavariable copies of the rules below it, the trace must end
at a type-raise node — at its skeleton or inside one of its target copies —
because every other case either descends strictly (binary conclusions, type
raise premise copies) or is visible (leaves, composition-principal roots) and
contradicts boundary-freeness.  This locates the creation site of the traced
material: only type raises create invisible category material.
-/

/-- The piece touches a type-raise node at its skeleton or a target-copy
position. -/
def InvisiblePiece.TypeRaiseAnchor {Γ : List Category} {A : Category}
    {t : DerivationTree Γ A} (P : InvisiblePiece t) : Prop :=
  ∃ (π : NodePath) (o : Occurrence t), o ∈ P.carrier ∧ o.nodePath = π ∧
    ((∃ (Γ' : List Category) (A₀ C₀ : Category) (u : DerivationTree Γ' A₀),
        DerivationTree.SubtreeAt t π (DerivationTree.typeRaiseRight C₀ u) ∧
        (o.categoryPath = [] ∨ o.categoryPath = [true] ∨
         (∃ p, o.categoryPath = false :: p) ∨ (∃ p, o.categoryPath = true :: true :: p))) ∨
     (∃ (Γ' : List Category) (A₀ C₀ : Category) (u : DerivationTree Γ' A₀),
        DerivationTree.SubtreeAt t π (DerivationTree.typeRaiseLeft C₀ u) ∧
        (o.categoryPath = [] ∨ o.categoryPath = [false] ∨
         (∃ p, o.categoryPath = true :: p) ∨ (∃ p, o.categoryPath = false :: false :: p))))

/-- **The chase.**  Any occurrence of a boundary-free piece, viewed at the
root of the subtree containing it, leads the piece to a type-raise anchor. -/
theorem InvisiblePiece.typeRaiseAnchor_of_subtree
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (P : InvisiblePiece t) (hfree : BoundaryFree P) :
    ∀ {Δ : List Category} {B : Category} (w : DerivationTree Δ B) (π : NodePath),
      DerivationTree.SubtreeAt t π w →
      ∀ o : Occurrence t, o ∈ P.carrier → o.nodePath = π →
      P.TypeRaiseAnchor := by
  intro Δ B w
  induction w with
  | leaf X =>
      intro π hw o ho hnp
      exact absurd (Or.inr (Or.inl (by rw [hnp]; exact hw.isLeafNode_of_leaf)))
        (P.all_invisible o ho)
  | @typeRaiseRight C₀ Γu Au u ih =>
      intro π hw o ho hnp
      obtain ⟨e, henp, hecat, hecp, helift⟩ := hw.exists_rootOcc o hnp
      cases hcp : o.categoryPath with
      | nil =>
          exact ⟨π, o, ho, hnp, Or.inl ⟨_, _, _, u, hw, Or.inl hcp⟩⟩
      | cons b q =>
          cases b with
          | false =>
              exact ⟨π, o, ho, hnp, Or.inl ⟨_, _, _, u, hw,
                Or.inr (Or.inr (Or.inl ⟨q, hcp⟩))⟩⟩
          | true =>
              cases hq : q with
              | nil =>
                  exact ⟨π, o, ho, hnp, Or.inl ⟨_, _, _, u, hw,
                    Or.inr (Or.inl (by rw [hcp, hq]))⟩⟩
              | cons b2 q2 =>
                  cases b2 with
                  | true =>
                      exact ⟨π, o, ho, hnp, Or.inl ⟨_, _, _, u, hw,
                        Or.inr (Or.inr (Or.inr ⟨q2, by rw [hcp, hq]⟩))⟩⟩
                  | false =>
                      have hcat : o.nodeCategory = C₀ ⧸ (Au ⧹ C₀) := by
                        have h := o.nodeAt
                        rw [hnp, hw.categoryAt?_self] at h
                        exact (Option.some.inj h).symm
                      obtain ⟨X, Y, hXY⟩ := o.isConstructor
                      have hcons : ∃ X Y,
                          Au.subcategoryAt? q2 = some (X ⧸ Y) ∨
                          Au.subcategoryAt? q2 = some (X ⧹ Y) := by
                        refine ⟨X, Y, ?_⟩
                        rw [hcat, hcp, hq] at hXY
                        simpa using hXY
                      let e₁ : Occurrence (DerivationTree.typeRaiseRight C₀ u) :=
                        { nodePath := [TreeStep.unary]
                          nodeCategory := Au
                          nodeAt := by simp [DerivationTree.categoryAt?]
                          categoryPath := q2
                          isConstructor := hcons }
                      have hloc : LocalTraceEdge e₁ e :=
                        LocalTraceEdge.trRight_A (p := q2) rfl rfl henp
                          (by rw [hecp, hcp, hq])
                      have hedge : TraceEdge o (hw.lift e₁) := by
                        have h2 := hw.lift_traceEdge (Or.inr (Or.inl hloc) : TraceEdge e e₁)
                        rwa [helift] at h2
                      by_cases hv : (hw.lift e₁).Visible
                      · exact absurd hedge (hfree o ho _ hv)
                      · exact ih (π ++ [TreeStep.unary])
                          (hw.trans (DerivationTree.SubtreeAt.underUnaryRight
                            (DerivationTree.SubtreeAt.refl _)))
                          (hw.lift e₁)
                          (P.closed o ho _ ⟨P.all_invisible o ho, hv, hedge⟩)
                          rfl
  | @typeRaiseLeft C₀ Γu Au u ih =>
      intro π hw o ho hnp
      obtain ⟨e, henp, hecat, hecp, helift⟩ := hw.exists_rootOcc o hnp
      cases hcp : o.categoryPath with
      | nil =>
          exact ⟨π, o, ho, hnp, Or.inr ⟨_, _, _, u, hw, Or.inl hcp⟩⟩
      | cons b q =>
          cases b with
          | true =>
              exact ⟨π, o, ho, hnp, Or.inr ⟨_, _, _, u, hw,
                Or.inr (Or.inr (Or.inl ⟨q, hcp⟩))⟩⟩
          | false =>
              cases hq : q with
              | nil =>
                  exact ⟨π, o, ho, hnp, Or.inr ⟨_, _, _, u, hw,
                    Or.inr (Or.inl (by rw [hcp, hq]))⟩⟩
              | cons b2 q2 =>
                  cases b2 with
                  | false =>
                      exact ⟨π, o, ho, hnp, Or.inr ⟨_, _, _, u, hw,
                        Or.inr (Or.inr (Or.inr ⟨q2, by rw [hcp, hq]⟩))⟩⟩
                  | true =>
                      have hcat : o.nodeCategory = (C₀ ⧸ Au) ⧹ C₀ := by
                        have h := o.nodeAt
                        rw [hnp, hw.categoryAt?_self] at h
                        exact (Option.some.inj h).symm
                      obtain ⟨X, Y, hXY⟩ := o.isConstructor
                      have hcons : ∃ X Y,
                          Au.subcategoryAt? q2 = some (X ⧸ Y) ∨
                          Au.subcategoryAt? q2 = some (X ⧹ Y) := by
                        refine ⟨X, Y, ?_⟩
                        rw [hcat, hcp, hq] at hXY
                        simpa using hXY
                      let e₁ : Occurrence (DerivationTree.typeRaiseLeft C₀ u) :=
                        { nodePath := [TreeStep.unary]
                          nodeCategory := Au
                          nodeAt := by simp [DerivationTree.categoryAt?]
                          categoryPath := q2
                          isConstructor := hcons }
                      have hloc : LocalTraceEdge e₁ e :=
                        LocalTraceEdge.trLeft_A (p := q2) rfl rfl henp
                          (by rw [hecp, hcp, hq])
                      have hedge : TraceEdge o (hw.lift e₁) := by
                        have h2 := hw.lift_traceEdge (Or.inr (Or.inl hloc) : TraceEdge e e₁)
                        rwa [helift] at h2
                      by_cases hv : (hw.lift e₁).Visible
                      · exact absurd hedge (hfree o ho _ hv)
                      · exact ih (π ++ [TreeStep.unary])
                          (hw.trans (DerivationTree.SubtreeAt.underUnaryLeft
                            (DerivationTree.SubtreeAt.refl _)))
                          (hw.lift e₁)
                          (P.closed o ho _ ⟨P.all_invisible o ho, hv, hedge⟩)
                          rfl
  | @binary Γ₁ Γ₂ Ab Bb Cb w₁ w₂ ρ ih₁ ih₂ =>
      intro π hw o ho hnp
      obtain ⟨e, henp, hecat, hecp, helift⟩ := hw.exists_rootOcc o hnp
      cases ρ with
        | appRight =>
            have hcat : o.nodeCategory = Cb := by
              have h := o.nodeAt
              rw [hnp, hw.categoryAt?_self] at h
              exact (Option.some.inj h).symm
            obtain ⟨X, Y, hXY⟩ := o.isConstructor
            have hcons : ∃ X Y,
                (Cb ⧸ Bb).subcategoryAt? (false :: o.categoryPath) = some (X ⧸ Y) ∨
                (Cb ⧸ Bb).subcategoryAt? (false :: o.categoryPath) = some (X ⧹ Y) := by
              refine ⟨X, Y, ?_⟩
              rw [hcat] at hXY
              simpa using hXY
            let e₁ : Occurrence (DerivationTree.binary w₁ w₂ Rule.appRight) :=
              { nodePath := [TreeStep.left]
                nodeCategory := Cb ⧸ Bb
                nodeAt := by simp [DerivationTree.categoryAt?]
                categoryPath := false :: o.categoryPath
                isConstructor := hcons }
            have hloc : LocalTraceEdge e₁ e :=
              LocalTraceEdge.appRight_C (p := o.categoryPath) rfl rfl henp (hecp)
            have hedge : TraceEdge o (hw.lift e₁) := by
              have h2 := hw.lift_traceEdge (Or.inr (Or.inl hloc) : TraceEdge e e₁)
              rwa [helift] at h2
            by_cases hv : (hw.lift e₁).Visible
            · exact absurd hedge (hfree o ho _ hv)
            · exact ih₁ (π ++ [TreeStep.left])
                (hw.trans (DerivationTree.SubtreeAt.underBinaryLeft (DerivationTree.SubtreeAt.refl _)))
                (hw.lift e₁)
                (P.closed o ho _ ⟨P.all_invisible o ho, hv, hedge⟩)
                rfl
        | appLeft =>
            have hcat : o.nodeCategory = Cb := by
              have h := o.nodeAt
              rw [hnp, hw.categoryAt?_self] at h
              exact (Option.some.inj h).symm
            obtain ⟨X, Y, hXY⟩ := o.isConstructor
            have hcons : ∃ X Y,
                (Ab ⧹ Cb).subcategoryAt? (true :: o.categoryPath) = some (X ⧸ Y) ∨
                (Ab ⧹ Cb).subcategoryAt? (true :: o.categoryPath) = some (X ⧹ Y) := by
              refine ⟨X, Y, ?_⟩
              rw [hcat] at hXY
              simpa using hXY
            let e₁ : Occurrence (DerivationTree.binary w₁ w₂ Rule.appLeft) :=
              { nodePath := [TreeStep.right]
                nodeCategory := Ab ⧹ Cb
                nodeAt := by simp [DerivationTree.categoryAt?]
                categoryPath := true :: o.categoryPath
                isConstructor := hcons }
            have hloc : LocalTraceEdge e₁ e :=
              LocalTraceEdge.appLeft_C (p := o.categoryPath) rfl rfl henp (hecp)
            have hedge : TraceEdge o (hw.lift e₁) := by
              have h2 := hw.lift_traceEdge (Or.inr (Or.inl hloc) : TraceEdge e e₁)
              rwa [helift] at h2
            by_cases hv : (hw.lift e₁).Visible
            · exact absurd hedge (hfree o ho _ hv)
            · exact ih₂ (π ++ [TreeStep.right])
                (hw.trans (DerivationTree.SubtreeAt.underBinaryRight (DerivationTree.SubtreeAt.refl _)))
                (hw.lift e₁)
                (P.closed o ho _ ⟨P.all_invisible o ho, hv, hedge⟩)
                rfl
        | compRight =>
            rename_i Cc Bc Ac
            cases hcp : o.categoryPath with
            | nil =>
                exfalso
                apply P.all_invisible o ho
                right; right
                have hpr := hw.principal_lift (DerivationTree.PrincipalConstructor.compRight_out w₁ w₂)
                rw [List.append_nil] at hpr
                rw [hnp, hcp]
                exact hpr
            | cons b q =>
                cases b with
                | false =>
                    have hcat : o.nodeCategory = Cc ⧸ Ac := by
                      have h := o.nodeAt
                      rw [hnp, hw.categoryAt?_self] at h
                      exact (Option.some.inj h).symm
                    obtain ⟨X, Y, hXY⟩ := o.isConstructor
                    have hcons : ∃ X Y,
                        (Cc ⧸ Bc).subcategoryAt? (false :: q) = some (X ⧸ Y) ∨
                        (Cc ⧸ Bc).subcategoryAt? (false :: q) = some (X ⧹ Y) := by
                      refine ⟨X, Y, ?_⟩
                      rw [hcat, hcp] at hXY
                      simpa using hXY
                    let e₁ : Occurrence (DerivationTree.binary w₁ w₂ Rule.compRight) :=
                      { nodePath := [TreeStep.left]
                        nodeCategory := Cc ⧸ Bc
                        nodeAt := by simp [DerivationTree.categoryAt?]
                        categoryPath := false :: q
                        isConstructor := hcons }
                    have hloc : LocalTraceEdge e₁ e :=
                      LocalTraceEdge.compRight_C (p := q) rfl rfl henp (by rw [hecp]; exact hcp)
                    have hedge : TraceEdge o (hw.lift e₁) := by
                      have h2 := hw.lift_traceEdge (Or.inr (Or.inl hloc) : TraceEdge e e₁)
                      rwa [helift] at h2
                    by_cases hv : (hw.lift e₁).Visible
                    · exact absurd hedge (hfree o ho _ hv)
                    · exact ih₁ (π ++ [TreeStep.left])
                        (hw.trans (DerivationTree.SubtreeAt.underBinaryLeft (DerivationTree.SubtreeAt.refl _)))
                        (hw.lift e₁)
                        (P.closed o ho _ ⟨P.all_invisible o ho, hv, hedge⟩)
                        rfl
                | true =>
                    have hcat : o.nodeCategory = Cc ⧸ Ac := by
                      have h := o.nodeAt
                      rw [hnp, hw.categoryAt?_self] at h
                      exact (Option.some.inj h).symm
                    obtain ⟨X, Y, hXY⟩ := o.isConstructor
                    have hcons : ∃ X Y,
                        (Bc ⧸ Ac).subcategoryAt? (true :: q) = some (X ⧸ Y) ∨
                        (Bc ⧸ Ac).subcategoryAt? (true :: q) = some (X ⧹ Y) := by
                      refine ⟨X, Y, ?_⟩
                      rw [hcat, hcp] at hXY
                      simpa using hXY
                    let e₁ : Occurrence (DerivationTree.binary w₁ w₂ Rule.compRight) :=
                      { nodePath := [TreeStep.right]
                        nodeCategory := Bc ⧸ Ac
                        nodeAt := by simp [DerivationTree.categoryAt?]
                        categoryPath := true :: q
                        isConstructor := hcons }
                    have hloc : LocalTraceEdge e₁ e :=
                      LocalTraceEdge.compRight_A (p := q) rfl rfl henp (by rw [hecp]; exact hcp)
                    have hedge : TraceEdge o (hw.lift e₁) := by
                      have h2 := hw.lift_traceEdge (Or.inr (Or.inl hloc) : TraceEdge e e₁)
                      rwa [helift] at h2
                    by_cases hv : (hw.lift e₁).Visible
                    · exact absurd hedge (hfree o ho _ hv)
                    · exact ih₂ (π ++ [TreeStep.right])
                        (hw.trans (DerivationTree.SubtreeAt.underBinaryRight (DerivationTree.SubtreeAt.refl _)))
                        (hw.lift e₁)
                        (P.closed o ho _ ⟨P.all_invisible o ho, hv, hedge⟩)
                        rfl
        | compLeft =>
            rename_i Ac Bc Cc
            cases hcp : o.categoryPath with
            | nil =>
                exfalso
                apply P.all_invisible o ho
                right; right
                have hpr := hw.principal_lift (DerivationTree.PrincipalConstructor.compLeft_out w₁ w₂)
                rw [List.append_nil] at hpr
                rw [hnp, hcp]
                exact hpr
            | cons b q =>
                cases b with
                | false =>
                    have hcat : o.nodeCategory = Ac ⧹ Cc := by
                      have h := o.nodeAt
                      rw [hnp, hw.categoryAt?_self] at h
                      exact (Option.some.inj h).symm
                    obtain ⟨X, Y, hXY⟩ := o.isConstructor
                    have hcons : ∃ X Y,
                        (Ac ⧹ Bc).subcategoryAt? (false :: q) = some (X ⧸ Y) ∨
                        (Ac ⧹ Bc).subcategoryAt? (false :: q) = some (X ⧹ Y) := by
                      refine ⟨X, Y, ?_⟩
                      rw [hcat, hcp] at hXY
                      simpa using hXY
                    let e₁ : Occurrence (DerivationTree.binary w₁ w₂ Rule.compLeft) :=
                      { nodePath := [TreeStep.left]
                        nodeCategory := Ac ⧹ Bc
                        nodeAt := by simp [DerivationTree.categoryAt?]
                        categoryPath := false :: q
                        isConstructor := hcons }
                    have hloc : LocalTraceEdge e₁ e :=
                      LocalTraceEdge.compLeft_A (p := q) rfl rfl henp (by rw [hecp]; exact hcp)
                    have hedge : TraceEdge o (hw.lift e₁) := by
                      have h2 := hw.lift_traceEdge (Or.inr (Or.inl hloc) : TraceEdge e e₁)
                      rwa [helift] at h2
                    by_cases hv : (hw.lift e₁).Visible
                    · exact absurd hedge (hfree o ho _ hv)
                    · exact ih₁ (π ++ [TreeStep.left])
                        (hw.trans (DerivationTree.SubtreeAt.underBinaryLeft (DerivationTree.SubtreeAt.refl _)))
                        (hw.lift e₁)
                        (P.closed o ho _ ⟨P.all_invisible o ho, hv, hedge⟩)
                        rfl
                | true =>
                    have hcat : o.nodeCategory = Ac ⧹ Cc := by
                      have h := o.nodeAt
                      rw [hnp, hw.categoryAt?_self] at h
                      exact (Option.some.inj h).symm
                    obtain ⟨X, Y, hXY⟩ := o.isConstructor
                    have hcons : ∃ X Y,
                        (Bc ⧹ Cc).subcategoryAt? (true :: q) = some (X ⧸ Y) ∨
                        (Bc ⧹ Cc).subcategoryAt? (true :: q) = some (X ⧹ Y) := by
                      refine ⟨X, Y, ?_⟩
                      rw [hcat, hcp] at hXY
                      simpa using hXY
                    let e₁ : Occurrence (DerivationTree.binary w₁ w₂ Rule.compLeft) :=
                      { nodePath := [TreeStep.right]
                        nodeCategory := Bc ⧹ Cc
                        nodeAt := by simp [DerivationTree.categoryAt?]
                        categoryPath := true :: q
                        isConstructor := hcons }
                    have hloc : LocalTraceEdge e₁ e :=
                      LocalTraceEdge.compLeft_C (p := q) rfl rfl henp (by rw [hecp]; exact hcp)
                    have hedge : TraceEdge o (hw.lift e₁) := by
                      have h2 := hw.lift_traceEdge (Or.inr (Or.inl hloc) : TraceEdge e e₁)
                      rwa [helift] at h2
                    by_cases hv : (hw.lift e₁).Visible
                    · exact absurd hedge (hfree o ho _ hv)
                    · exact ih₂ (π ++ [TreeStep.right])
                        (hw.trans (DerivationTree.SubtreeAt.underBinaryRight (DerivationTree.SubtreeAt.refl _)))
                        (hw.lift e₁)
                        (P.closed o ho _ ⟨P.all_invisible o ho, hv, hedge⟩)
                        rfl
        | crossedRight =>
            rename_i Cc Bc Ac
            cases hcp : o.categoryPath with
            | nil =>
                exfalso
                apply P.all_invisible o ho
                right; right
                have hpr := hw.principal_lift (DerivationTree.PrincipalConstructor.crossedRight_out w₁ w₂)
                rw [List.append_nil] at hpr
                rw [hnp, hcp]
                exact hpr
            | cons b q =>
                cases b with
                | false =>
                    have hcat : o.nodeCategory = Ac ⧹ Cc := by
                      have h := o.nodeAt
                      rw [hnp, hw.categoryAt?_self] at h
                      exact (Option.some.inj h).symm
                    obtain ⟨X, Y, hXY⟩ := o.isConstructor
                    have hcons : ∃ X Y,
                        (Ac ⧹ Bc).subcategoryAt? (false :: q) = some (X ⧸ Y) ∨
                        (Ac ⧹ Bc).subcategoryAt? (false :: q) = some (X ⧹ Y) := by
                      refine ⟨X, Y, ?_⟩
                      rw [hcat, hcp] at hXY
                      simpa using hXY
                    let e₁ : Occurrence (DerivationTree.binary w₁ w₂ Rule.crossedRight) :=
                      { nodePath := [TreeStep.right]
                        nodeCategory := Ac ⧹ Bc
                        nodeAt := by simp [DerivationTree.categoryAt?]
                        categoryPath := false :: q
                        isConstructor := hcons }
                    have hloc : LocalTraceEdge e₁ e :=
                      LocalTraceEdge.crossedRight_A (p := q) rfl rfl henp (by rw [hecp]; exact hcp)
                    have hedge : TraceEdge o (hw.lift e₁) := by
                      have h2 := hw.lift_traceEdge (Or.inr (Or.inl hloc) : TraceEdge e e₁)
                      rwa [helift] at h2
                    by_cases hv : (hw.lift e₁).Visible
                    · exact absurd hedge (hfree o ho _ hv)
                    · exact ih₂ (π ++ [TreeStep.right])
                        (hw.trans (DerivationTree.SubtreeAt.underBinaryRight (DerivationTree.SubtreeAt.refl _)))
                        (hw.lift e₁)
                        (P.closed o ho _ ⟨P.all_invisible o ho, hv, hedge⟩)
                        rfl
                | true =>
                    have hcat : o.nodeCategory = Ac ⧹ Cc := by
                      have h := o.nodeAt
                      rw [hnp, hw.categoryAt?_self] at h
                      exact (Option.some.inj h).symm
                    obtain ⟨X, Y, hXY⟩ := o.isConstructor
                    have hcons : ∃ X Y,
                        (Cc ⧸ Bc).subcategoryAt? (false :: q) = some (X ⧸ Y) ∨
                        (Cc ⧸ Bc).subcategoryAt? (false :: q) = some (X ⧹ Y) := by
                      refine ⟨X, Y, ?_⟩
                      rw [hcat, hcp] at hXY
                      simpa using hXY
                    let e₁ : Occurrence (DerivationTree.binary w₁ w₂ Rule.crossedRight) :=
                      { nodePath := [TreeStep.left]
                        nodeCategory := Cc ⧸ Bc
                        nodeAt := by simp [DerivationTree.categoryAt?]
                        categoryPath := false :: q
                        isConstructor := hcons }
                    have hloc : LocalTraceEdge e₁ e :=
                      LocalTraceEdge.crossedRight_C (p := q) rfl rfl henp (by rw [hecp]; exact hcp)
                    have hedge : TraceEdge o (hw.lift e₁) := by
                      have h2 := hw.lift_traceEdge (Or.inr (Or.inl hloc) : TraceEdge e e₁)
                      rwa [helift] at h2
                    by_cases hv : (hw.lift e₁).Visible
                    · exact absurd hedge (hfree o ho _ hv)
                    · exact ih₁ (π ++ [TreeStep.left])
                        (hw.trans (DerivationTree.SubtreeAt.underBinaryLeft (DerivationTree.SubtreeAt.refl _)))
                        (hw.lift e₁)
                        (P.closed o ho _ ⟨P.all_invisible o ho, hv, hedge⟩)
                        rfl
        | crossedLeft =>
            rename_i Bc Ac Cc
            cases hcp : o.categoryPath with
            | nil =>
                exfalso
                apply P.all_invisible o ho
                right; right
                have hpr := hw.principal_lift (DerivationTree.PrincipalConstructor.crossedLeft_out w₁ w₂)
                rw [List.append_nil] at hpr
                rw [hnp, hcp]
                exact hpr
            | cons b q =>
                cases b with
                | false =>
                    have hcat : o.nodeCategory = Cc ⧸ Ac := by
                      have h := o.nodeAt
                      rw [hnp, hw.categoryAt?_self] at h
                      exact (Option.some.inj h).symm
                    obtain ⟨X, Y, hXY⟩ := o.isConstructor
                    have hcons : ∃ X Y,
                        (Bc ⧹ Cc).subcategoryAt? (true :: q) = some (X ⧸ Y) ∨
                        (Bc ⧹ Cc).subcategoryAt? (true :: q) = some (X ⧹ Y) := by
                      refine ⟨X, Y, ?_⟩
                      rw [hcat, hcp] at hXY
                      simpa using hXY
                    let e₁ : Occurrence (DerivationTree.binary w₁ w₂ Rule.crossedLeft) :=
                      { nodePath := [TreeStep.right]
                        nodeCategory := Bc ⧹ Cc
                        nodeAt := by simp [DerivationTree.categoryAt?]
                        categoryPath := true :: q
                        isConstructor := hcons }
                    have hloc : LocalTraceEdge e₁ e :=
                      LocalTraceEdge.crossedLeft_C (p := q) rfl rfl henp (by rw [hecp]; exact hcp)
                    have hedge : TraceEdge o (hw.lift e₁) := by
                      have h2 := hw.lift_traceEdge (Or.inr (Or.inl hloc) : TraceEdge e e₁)
                      rwa [helift] at h2
                    by_cases hv : (hw.lift e₁).Visible
                    · exact absurd hedge (hfree o ho _ hv)
                    · exact ih₂ (π ++ [TreeStep.right])
                        (hw.trans (DerivationTree.SubtreeAt.underBinaryRight (DerivationTree.SubtreeAt.refl _)))
                        (hw.lift e₁)
                        (P.closed o ho _ ⟨P.all_invisible o ho, hv, hedge⟩)
                        rfl
                | true =>
                    have hcat : o.nodeCategory = Cc ⧸ Ac := by
                      have h := o.nodeAt
                      rw [hnp, hw.categoryAt?_self] at h
                      exact (Option.some.inj h).symm
                    obtain ⟨X, Y, hXY⟩ := o.isConstructor
                    have hcons : ∃ X Y,
                        (Bc ⧸ Ac).subcategoryAt? (true :: q) = some (X ⧸ Y) ∨
                        (Bc ⧸ Ac).subcategoryAt? (true :: q) = some (X ⧹ Y) := by
                      refine ⟨X, Y, ?_⟩
                      rw [hcat, hcp] at hXY
                      simpa using hXY
                    let e₁ : Occurrence (DerivationTree.binary w₁ w₂ Rule.crossedLeft) :=
                      { nodePath := [TreeStep.left]
                        nodeCategory := Bc ⧸ Ac
                        nodeAt := by simp [DerivationTree.categoryAt?]
                        categoryPath := true :: q
                        isConstructor := hcons }
                    have hloc : LocalTraceEdge e₁ e :=
                      LocalTraceEdge.crossedLeft_A (p := q) rfl rfl henp (by rw [hecp]; exact hcp)
                    have hedge : TraceEdge o (hw.lift e₁) := by
                      have h2 := hw.lift_traceEdge (Or.inr (Or.inl hloc) : TraceEdge e e₁)
                      rwa [helift] at h2
                    by_cases hv : (hw.lift e₁).Visible
                    · exact absurd hedge (hfree o ho _ hv)
                    · exact ih₁ (π ++ [TreeStep.left])
                        (hw.trans (DerivationTree.SubtreeAt.underBinaryLeft (DerivationTree.SubtreeAt.refl _)))
                        (hw.lift e₁)
                        (P.closed o ho _ ⟨P.all_invisible o ho, hv, hedge⟩)
                        rfl

/-- Every valid node address of a derivation tree addresses a subtree. -/
theorem DerivationTree.exists_subtreeAt :
    {Γ : List Category} → {A : Category} → (t : DerivationTree Γ A) → (π : NodePath) →
      {B : Category} → t.categoryAt? π = some B →
      ∃ (Δ : List Category) (w : DerivationTree Δ B), DerivationTree.SubtreeAt t π w
  | _, _, t, [], _, h => by
      rw [DerivationTree.categoryAt?_root] at h
      obtain rfl := Option.some.inj h
      exact ⟨_, t, .refl t⟩
  | _, _, .leaf _, _ :: _, _, h => by
      simp [DerivationTree.categoryAt?] at h
  | _, _, .typeRaiseRight C u, .unary :: π', _, h => by
      obtain ⟨Δ, w, hw⟩ := DerivationTree.exists_subtreeAt u π' h
      exact ⟨Δ, w, .underUnaryRight hw⟩
  | _, _, .typeRaiseRight _ _, .left :: _, _, h => by
      simp [DerivationTree.categoryAt?] at h
  | _, _, .typeRaiseRight _ _, .right :: _, _, h => by
      simp [DerivationTree.categoryAt?] at h
  | _, _, .typeRaiseLeft C u, .unary :: π', _, h => by
      obtain ⟨Δ, w, hw⟩ := DerivationTree.exists_subtreeAt u π' h
      exact ⟨Δ, w, .underUnaryLeft hw⟩
  | _, _, .typeRaiseLeft _ _, .left :: _, _, h => by
      simp [DerivationTree.categoryAt?] at h
  | _, _, .typeRaiseLeft _ _, .right :: _, _, h => by
      simp [DerivationTree.categoryAt?] at h
  | _, _, .binary t₁ _ _, .left :: π', _, h => by
      obtain ⟨Δ, w, hw⟩ := DerivationTree.exists_subtreeAt t₁ π' h
      exact ⟨Δ, w, .underBinaryLeft hw⟩
  | _, _, .binary _ t₂ _, .right :: π', _, h => by
      obtain ⟨Δ, w, hw⟩ := DerivationTree.exists_subtreeAt t₂ π' h
      exact ⟨Δ, w, .underBinaryRight hw⟩
  | _, _, .binary _ _ _, .unary :: _, _, h => by
      simp [DerivationTree.categoryAt?] at h

/-- **Anchor theorem.**  Every nonempty boundary-free invisible piece is
anchored at a type raise: type raises are the only creation sites of invisible
category material. -/
theorem InvisiblePiece.typeRaiseAnchor
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (P : InvisiblePiece t) (hfree : BoundaryFree P) :
    P.TypeRaiseAnchor := by
  obtain ⟨o, ho⟩ := List.exists_mem_of_ne_nil P.carrier P.nonempty
  obtain ⟨Δ, w, hw⟩ := DerivationTree.exists_subtreeAt t o.nodePath o.nodeAt
  exact P.typeRaiseAnchor_of_subtree hfree w o.nodePath hw o ho rfl

end Mathling.CCG
