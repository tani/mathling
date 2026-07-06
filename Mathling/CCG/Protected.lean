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

end Mathling.CCG
