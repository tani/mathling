import Mathling.CCG.Atoms
import Mathling.CCG.Band
import Mathling.CCG.Finite
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod

/-!
# Depth-counting layer for CCG derivation trees

This file proves the branch-counting theorem: in any derivation tree whose
invisible trace pieces all have a visible boundary, every node category has
depth at most `H = V + V*r` (`depthBound`), where `V` is the visible budget
and `r` the trace-degree constant.

The counting is a pigeonhole along one constructor branch of one node
category:

* visible occurrences on the branch: at most `V` (`visibleSlots`);
* invisible occurrences: coded injectively by
  `(visible-boundary slot, trace-neighbour slot)` — injective because equal
  codes force the same trace piece, and one piece never meets a branch twice
  (`sameInvisibleTraceComponent_forbids_strictPrefix_branch`).

The only remaining input is boundary elimination for size-minimal trees
(`BoundaryFreeInvisiblePieceElimination`); everything downstream of it here is
proved.
-/

set_option linter.style.longLine false
set_option linter.unnecessarySimpa false

namespace Mathling.CCG

open Category

namespace DerivationTree

/-- Categories of a derivation tree are all contained in a finite candidate set. -/
def NodeCategoriesContainedIn (K : List Category) {Γ : List Category} {A : Category} (t : DerivationTree Γ A) : Prop :=
  ∀ B, B ∈ t.nodeCategories → B ∈ K

/-- Number of binary-rule nodes in a derivation tree.  Unary type raising does
not change the leaf frontier; each binary node combines two neighbouring
frontiers. -/
def binaryRuleCount : {Γ : List Category} → {A : Category} → DerivationTree Γ A → Nat
  | _, _, .leaf _ => 0
  | _, _, .typeRaiseRight _ t => t.binaryRuleCount
  | _, _, .typeRaiseLeft _ t => t.binaryRuleCount
  | _, _, .binary t₁ t₂ _ => t₁.binaryRuleCount + t₂.binaryRuleCount + 1

/-- Every derivation tree has at least one leaf category. -/
theorem leaves_length_pos : {Γ : List Category} → {A : Category} → (t : DerivationTree Γ A) →
    0 < Γ.length
  | _, _, .leaf _ => by simp
  | _, _, .typeRaiseRight _ t => leaves_length_pos t
  | _, _, .typeRaiseLeft _ t => leaves_length_pos t
  | _, _, .binary t₁ t₂ _ => by
      have h₁ := leaves_length_pos t₁
      have h₂ := leaves_length_pos t₂
      simp [List.length_append]
      omega

/-- A binary CCG derivation tree with `n` leaves has exactly `n - 1`
binary-rule nodes.  This is the counting fact behind the `3 * (Γ.length - 1)`
visible-principal-constructor budget. -/
theorem binaryRuleCount_eq_length_sub_one :
    {Γ : List Category} → {A : Category} → (t : DerivationTree Γ A) →
      t.binaryRuleCount = Γ.length - 1
  | _, _, .leaf _ => by simp [binaryRuleCount]
  | _, _, .typeRaiseRight _ t => by
      simpa [binaryRuleCount] using binaryRuleCount_eq_length_sub_one t
  | _, _, .typeRaiseLeft _ t => by
      simpa [binaryRuleCount] using binaryRuleCount_eq_length_sub_one t
  | _, _, .binary (Γ := Γ) (Δ := Δ) t₁ t₂ _ => by
      have h₁ := binaryRuleCount_eq_length_sub_one t₁
      have h₂ := binaryRuleCount_eq_length_sub_one t₂
      have hΓ := leaves_length_pos t₁
      have hΔ := leaves_length_pos t₂
      simp [binaryRuleCount, List.length_append, h₁, h₂]
      omega

/-- Three over-approximating principal-constructor slots for the root of one
binary rule.  Depending on the concrete rule, one, two, or three of these slots
are actually principal; the uniform list is what contributes the factor `3` in
`visibleBound`. -/
def rootPrincipalSlots : List Occurrence.Key :=
  [ { nodePath := [], categoryPath := [] },
    { nodePath := [.left], categoryPath := [] },
    { nodePath := [.right], categoryPath := [] } ]

/-- Constructor slots at the root category of a derivation tree. -/
def rootConstructorSlots {Γ : List Category} {A : Category}
    (_t : DerivationTree Γ A) : List Occurrence.Key :=
  A.constructorPositions.map fun p => { nodePath := [], categoryPath := p }

/-- Constructor slots at leaf categories, transported through the derivation
tree context. -/
def leafConstructorSlots : {Γ : List Category} → {A : Category} →
    DerivationTree Γ A → List Occurrence.Key
  | _, A, .leaf _ =>
      A.constructorPositions.map fun p => { nodePath := [], categoryPath := p }
  | _, _, .typeRaiseRight _ t =>
      t.leafConstructorSlots.map (Occurrence.Key.rebase [.unary])
  | _, _, .typeRaiseLeft _ t =>
      t.leafConstructorSlots.map (Occurrence.Key.rebase [.unary])
  | _, _, .binary t₁ t₂ _ =>
      t₁.leafConstructorSlots.map (Occurrence.Key.rebase [.left]) ++
        t₂.leafConstructorSlots.map (Occurrence.Key.rebase [.right])

/-- Root constructor slots are counted by the goal category constructors. -/
theorem length_rootConstructorSlots {Γ : List Category} {A : Category}
    (t : DerivationTree Γ A) :
    t.rootConstructorSlots.length = A.constructors := by
  simp [rootConstructorSlots, Category.length_constructorPositions]

/-- Root-visible occurrences are covered by the root-constructor slots. -/
theorem root_visible_mem_rootConstructorSlots {Γ : List Category} {A : Category}
    {t : DerivationTree Γ A} {o : Occurrence t}
    (hroot : DerivationTree.isRootNode o.nodePath) :
    o.key ∈ t.rootConstructorSlots := by
  rw [DerivationTree.isRootNode] at hroot
  have hnode : o.nodeCategory = A := by
    have h : A = o.nodeCategory := by
      simpa [hroot] using o.nodeAt
    exact h.symm
  have hpos : o.categoryPath ∈ A.constructorPositions := by
    simpa [hnode] using
      (Category.mem_constructorPositions_of_isConstructor o.nodeCategory o.isConstructor)
  simp [rootConstructorSlots, Occurrence.key, hroot, hpos]

/-- Leaf constructor slots are counted by the constructor count of the input
context. -/
theorem length_leafConstructorSlots :
    {Γ : List Category} → {A : Category} → (t : DerivationTree Γ A) →
      t.leafConstructorSlots.length = contextConstructors Γ
  | _, _, .leaf A => by
      simp [leafConstructorSlots, contextConstructors, Category.length_constructorPositions]
  | _, _, .typeRaiseRight _ t => by
      simpa [leafConstructorSlots] using length_leafConstructorSlots t
  | _, _, .typeRaiseLeft _ t => by
      simpa [leafConstructorSlots] using length_leafConstructorSlots t
  | _, _, .binary t₁ t₂ _ => by
      have h₁ := length_leafConstructorSlots t₁
      have h₂ := length_leafConstructorSlots t₂
      simp [leafConstructorSlots, contextConstructors_append, h₁, h₂]

/-- Leaf-visible occurrences are covered by the leaf-constructor slots. -/
theorem leaf_visible_mem_leafConstructorSlots :
    {Γ : List Category} → {A : Category} → {t : DerivationTree Γ A} →
      (o : Occurrence t) → t.isLeafNode o.nodePath → o.key ∈ t.leafConstructorSlots
  | _, _, .leaf A, o, hleaf => by
      cases hnodePath : o.nodePath with
      | nil =>
          have hnode : o.nodeCategory = A := by
            have h : A = o.nodeCategory := by simpa [hnodePath] using o.nodeAt
            exact h.symm
          have hpos : o.categoryPath ∈ A.constructorPositions := by
            simpa [hnode] using
              (Category.mem_constructorPositions_of_isConstructor o.nodeCategory o.isConstructor)
          simp [leafConstructorSlots, Occurrence.key, hnodePath, hpos]
      | cons step rest => simp [DerivationTree.isLeafNode, hnodePath] at hleaf
  | _, _, .typeRaiseRight _ t, o, hleaf => by
      cases hnode : o.nodePath with
      | nil => simp [DerivationTree.isLeafNode, hnode] at hleaf
      | cons step rest =>
          cases step with
          | unary =>
              let o' : Occurrence t :=
                { nodePath := rest
                  nodeCategory := o.nodeCategory
                  nodeAt := by simpa [DerivationTree.categoryAt?, hnode] using o.nodeAt
                  categoryPath := o.categoryPath
                  isConstructor := o.isConstructor }
              have hleaf' : t.isLeafNode o'.nodePath := by
                simpa [DerivationTree.isLeafNode, hnode, o'] using hleaf
              have hmem := leaf_visible_mem_leafConstructorSlots o' hleaf'
              exact List.mem_map.mpr ⟨o'.key, hmem, by
                simp [Occurrence.key, Occurrence.Key.rebase, o', hnode]⟩
          | left => simp [DerivationTree.isLeafNode, hnode] at hleaf
          | right => simp [DerivationTree.isLeafNode, hnode] at hleaf
  | _, _, .typeRaiseLeft _ t, o, hleaf => by
      cases hnode : o.nodePath with
      | nil => simp [DerivationTree.isLeafNode, hnode] at hleaf
      | cons step rest =>
          cases step with
          | unary =>
              let o' : Occurrence t :=
                { nodePath := rest
                  nodeCategory := o.nodeCategory
                  nodeAt := by simpa [DerivationTree.categoryAt?, hnode] using o.nodeAt
                  categoryPath := o.categoryPath
                  isConstructor := o.isConstructor }
              have hleaf' : t.isLeafNode o'.nodePath := by
                simpa [DerivationTree.isLeafNode, hnode, o'] using hleaf
              have hmem := leaf_visible_mem_leafConstructorSlots o' hleaf'
              exact List.mem_map.mpr ⟨o'.key, hmem, by
                simp [Occurrence.key, Occurrence.Key.rebase, o', hnode]⟩
          | left => simp [DerivationTree.isLeafNode, hnode] at hleaf
          | right => simp [DerivationTree.isLeafNode, hnode] at hleaf
  | _, _, .binary t₁ t₂ _, o, hleaf => by
      cases hnode : o.nodePath with
      | nil => simp [DerivationTree.isLeafNode, hnode] at hleaf
      | cons step rest =>
          cases step with
          | unary => simp [DerivationTree.isLeafNode, hnode] at hleaf
          | left =>
              let o' : Occurrence t₁ :=
                { nodePath := rest
                  nodeCategory := o.nodeCategory
                  nodeAt := by simpa [DerivationTree.categoryAt?, hnode] using o.nodeAt
                  categoryPath := o.categoryPath
                  isConstructor := o.isConstructor }
              have hleaf' : t₁.isLeafNode o'.nodePath := by
                simpa [DerivationTree.isLeafNode, hnode, o'] using hleaf
              have hmem := leaf_visible_mem_leafConstructorSlots o' hleaf'
              exact List.mem_append_left _ (List.mem_map.mpr ⟨o'.key, hmem, by
                simp [Occurrence.key, Occurrence.Key.rebase, o', hnode]⟩)
          | right =>
              let o' : Occurrence t₂ :=
                { nodePath := rest
                  nodeCategory := o.nodeCategory
                  nodeAt := by simpa [DerivationTree.categoryAt?, hnode] using o.nodeAt
                  categoryPath := o.categoryPath
                  isConstructor := o.isConstructor }
              have hleaf' : t₂.isLeafNode o'.nodePath := by
                simpa [DerivationTree.isLeafNode, hnode, o'] using hleaf
              have hmem := leaf_visible_mem_leafConstructorSlots o' hleaf'
              exact List.mem_append_right _ (List.mem_map.mpr ⟨o'.key, hmem, by
                simp [Occurrence.key, Occurrence.Key.rebase, o', hnode]⟩)

/-- All principal-constructor slots below a derivation tree.  The list is an
over-approximation by rule node: every binary rule contributes exactly the three
root-local slots above, transported through the surrounding derivation context. -/
def principalVisibleSlots : {Γ : List Category} → {A : Category} →
    DerivationTree Γ A → List Occurrence.Key
  | _, _, .leaf _ => []
  | _, _, .typeRaiseRight _ t =>
      t.principalVisibleSlots.map (Occurrence.Key.rebase [.unary])
  | _, _, .typeRaiseLeft _ t =>
      t.principalVisibleSlots.map (Occurrence.Key.rebase [.unary])
  | _, _, .binary t₁ t₂ _ =>
      rootPrincipalSlots ++
        t₁.principalVisibleSlots.map (Occurrence.Key.rebase [.left]) ++
          t₂.principalVisibleSlots.map (Occurrence.Key.rebase [.right])

@[simp]
theorem length_rootPrincipalSlots : rootPrincipalSlots.length = 3 := rfl

/-- The principal-slot over-approximation has exactly three slots per binary
rule node. -/
theorem length_principalVisibleSlots :
    {Γ : List Category} → {A : Category} → (t : DerivationTree Γ A) →
      t.principalVisibleSlots.length = 3 * t.binaryRuleCount
  | _, _, .leaf _ => by simp [principalVisibleSlots, binaryRuleCount]
  | _, _, .typeRaiseRight _ t => by
      simpa [principalVisibleSlots, binaryRuleCount] using length_principalVisibleSlots t
  | _, _, .typeRaiseLeft _ t => by
      simpa [principalVisibleSlots, binaryRuleCount] using length_principalVisibleSlots t
  | _, _, .binary t₁ t₂ _ => by
      have h₁ := length_principalVisibleSlots t₁
      have h₂ := length_principalVisibleSlots t₂
      simp [principalVisibleSlots, binaryRuleCount, rootPrincipalSlots, h₁, h₂]
      omega

/-- Principal-constructor slots are bounded by the `3 * (Γ.length - 1)` term of
the paper visible bound. -/
theorem length_principalVisibleSlots_eq_visible_principal_budget
    {Γ : List Category} {A : Category} (t : DerivationTree Γ A) :
    t.principalVisibleSlots.length = 3 * (Γ.length - 1) := by
  rw [length_principalVisibleSlots, binaryRuleCount_eq_length_sub_one]

/-- Every actual principal-constructor position is covered by the three-slot
over-approximation assigned to its binary rule node. -/
theorem principalSlot_mem_principalVisibleSlots :
    {Γ : List Category} → {A : Category} → {t : DerivationTree Γ A} →
      {p : NodePath} → {cpos : CategoryPath} →
        DerivationTree.PrincipalConstructor t p cpos →
          ({ nodePath := p, categoryPath := cpos } : Occurrence.Key) ∈
            t.principalVisibleSlots := by
  intro Γ A t p cpos h
  induction h with
  | appRight_left t₁ t₂ => simp [principalVisibleSlots, rootPrincipalSlots]
  | appLeft_right t₁ t₂ => simp [principalVisibleSlots, rootPrincipalSlots]
  | compRight_left t₁ t₂ => simp [principalVisibleSlots, rootPrincipalSlots]
  | compRight_right t₁ t₂ => simp [principalVisibleSlots, rootPrincipalSlots]
  | compRight_out t₁ t₂ => simp [principalVisibleSlots, rootPrincipalSlots]
  | compLeft_left t₁ t₂ => simp [principalVisibleSlots, rootPrincipalSlots]
  | compLeft_right t₁ t₂ => simp [principalVisibleSlots, rootPrincipalSlots]
  | compLeft_out t₁ t₂ => simp [principalVisibleSlots, rootPrincipalSlots]
  | crossedRight_left t₁ t₂ => simp [principalVisibleSlots, rootPrincipalSlots]
  | crossedRight_right t₁ t₂ => simp [principalVisibleSlots, rootPrincipalSlots]
  | crossedRight_out t₁ t₂ => simp [principalVisibleSlots, rootPrincipalSlots]
  | crossedLeft_left t₁ t₂ => simp [principalVisibleSlots, rootPrincipalSlots]
  | crossedLeft_right t₁ t₂ => simp [principalVisibleSlots, rootPrincipalSlots]
  | crossedLeft_out t₁ t₂ => simp [principalVisibleSlots, rootPrincipalSlots]
  | underUnaryRight C h ih =>
      exact List.mem_map.mpr ⟨_, ih, rfl⟩
  | underUnaryLeft C h ih =>
      exact List.mem_map.mpr ⟨_, ih, rfl⟩
  | underBinaryLeft r h ih =>
      exact List.mem_append_left _
        (List.mem_append_right _ (List.mem_map.mpr ⟨_, ih, rfl⟩))
  | underBinaryRight r h ih =>
      exact List.mem_append_right _ (List.mem_map.mpr ⟨_, ih, rfl⟩)

/-- Principal-visible occurrences are covered by the principal-constructor
slots. -/
theorem principal_visible_mem_principalVisibleSlots
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o : Occurrence t}
    (hprincipal : DerivationTree.PrincipalConstructor t o.nodePath o.categoryPath) :
    o.key ∈ t.principalVisibleSlots := by
  simpa [Occurrence.key] using
    (principalSlot_mem_principalVisibleSlots hprincipal)

/-- The full visible-slot over-approximation used by the paper count: root
constructors, leaf constructors, and up to three principal constructors for
each binary rule. -/
def visibleSlots {Γ : List Category} {A : Category}
    (t : DerivationTree Γ A) : List Occurrence.Key :=
  t.rootConstructorSlots ++ t.leafConstructorSlots ++ t.principalVisibleSlots

/-- The visible-slot over-approximation has exactly the paper size
`visibleBound Γ A`. -/
theorem length_visibleSlots {Γ : List Category} {A : Category}
    (t : DerivationTree Γ A) :
    t.visibleSlots.length = visibleBound Γ A := by
  simp [visibleSlots, visibleBound, length_rootConstructorSlots,
    length_leafConstructorSlots, length_principalVisibleSlots_eq_visible_principal_budget,
    Nat.add_assoc]
  omega

end DerivationTree

namespace Category

/-- If every constructor position of a category lies on a branch of length at
most `H`, then the category depth is at most `H`.  This is the pure category
bridge from branch counting to the node-depth bound used by the parser. -/
theorem depth_le_of_constructorPosition_length :
    ∀ (C : Category) (H : Nat),
      (∀ p, p ∈ C.constructorPositions → p.length + 1 ≤ H) → C.depth ≤ H
  | atom _, H, _ => by simp [Category.depth]
  | ldiv L R, H, h => by
      have hroot : 1 ≤ H := h [] (by simp [Category.constructorPositions])
      have hL : L.depth ≤ H - 1 := by
        apply depth_le_of_constructorPosition_length
        intro p hp
        have hp' : false :: p ∈ (L ⧹ R).constructorPositions := by
          simp [Category.constructorPositions, hp]
        have := h (false :: p) hp'
        simp at this
        omega
      have hR : R.depth ≤ H - 1 := by
        apply depth_le_of_constructorPosition_length
        intro p hp
        have hp' : true :: p ∈ (L ⧹ R).constructorPositions := by
          simp [Category.constructorPositions, hp]
        have := h (true :: p) hp'
        simp at this
        omega
      have hmax : Nat.max L.depth R.depth ≤ H - 1 := Nat.max_le.mpr ⟨hL, hR⟩
      simp [Category.depth]
      omega
  | rdiv L R, H, h => by
      have hroot : 1 ≤ H := h [] (by simp [Category.constructorPositions])
      have hL : L.depth ≤ H - 1 := by
        apply depth_le_of_constructorPosition_length
        intro p hp
        have hp' : false :: p ∈ (L ⧸ R).constructorPositions := by
          simp [Category.constructorPositions, hp]
        have := h (false :: p) hp'
        simp at this
        omega
      have hR : R.depth ≤ H - 1 := by
        apply depth_le_of_constructorPosition_length
        intro p hp
        have hp' : true :: p ∈ (L ⧸ R).constructorPositions := by
          simp [Category.constructorPositions, hp]
        have := h (true :: p) hp'
        simp at this
        omega
      have hmax : Nat.max L.depth R.depth ≤ H - 1 := Nat.max_le.mpr ⟨hL, hR⟩
      simp [Category.depth]
      omega

end Category

/-! ## Soundness of generated finite categories -/

/-- Every category generated by `categoriesWithDepthAtMost n atoms` has depth at most `n`. -/
theorem depth_le_of_mem_categoriesWithDepthAtMost :
    ∀ (n : Nat) (atoms : List String) {C : Category}, C ∈ categoriesWithDepthAtMost n atoms → C.depth ≤ n := by
  intro n
  induction n with
  | zero =>
      intro atoms C hC
      rw [categoriesWithDepthAtMost, mem_eraseDups_iff, List.mem_map] at hC
      obtain ⟨name, _hname, rfl⟩ := hC
      grind [Category.depth]
  | succ n ih =>
      intro atoms C hC
      rw [categoriesWithDepthAtMost, mem_closeOnce] at hC
      rcases hC with hprev | ⟨A, hA, B, hB, hCeq | hCeq⟩
      · have := ih atoms hprev
        omega
      · subst hCeq
        have hAd := ih atoms hA
        have hBd := ih atoms hB
        grind [Category.depth]
      · subst hCeq
        have hAd := ih atoms hA
        have hBd := ih atoms hB
        grind [Category.depth]

/-- Every category in `categoryPool` respects its depth limit. -/
theorem depth_le_of_mem_categoryPool
    {Γ : List Category} {goal : Category} {depthLimit : Nat} {C : Category}
    (hC : C ∈ categoryPool Γ goal depthLimit) : C.depth ≤ depthLimit :=
  depth_le_of_mem_categoriesWithDepthAtMost depthLimit (problemAtomNames Γ goal) hC

/-- Every atom of a generated category belongs to the generator atom list. -/
theorem atoms_of_mem_categoriesWithDepthAtMost :
    ∀ (n : Nat) (atoms : List String) {C : Category}, C ∈ categoriesWithDepthAtMost n atoms →
      ∀ name ∈ C.atoms, name ∈ atoms := by
  intro n
  induction n with
  | zero =>
      intro atoms C hC name hname
      rw [categoriesWithDepthAtMost, mem_eraseDups_iff, List.mem_map] at hC
      obtain ⟨atomName, hatom, rfl⟩ := hC
      simp only [Category.atoms, List.mem_singleton] at hname
      subst hname
      rwa [mem_eraseDups_iff] at hatom
  | succ n ih =>
      intro atoms C hC name hname
      rw [categoriesWithDepthAtMost, mem_closeOnce] at hC
      rcases hC with hprev | ⟨A, hA, B, hB, hCeq | hCeq⟩
      · exact ih atoms hprev name hname
      · subst hCeq
        simp only [Category.atoms, List.mem_append] at hname
        rcases hname with hname | hname
        · exact ih atoms hA name hname
        · exact ih atoms hB name hname
      · subst hCeq
        simp only [Category.atoms, List.mem_append] at hname
        rcases hname with hname | hname
        · exact ih atoms hA name hname
        · exact ih atoms hB name hname

/-- Every atom of a candidate category belongs to the problem atom list. -/
theorem atoms_of_mem_categoryPool
    {Γ : List Category} {goal : Category} {depthLimit : Nat} {C : Category}
    (hC : C ∈ categoryPool Γ goal depthLimit) :
    ∀ name ∈ C.atoms, name ∈ problemAtomNames Γ goal :=
  atoms_of_mem_categoriesWithDepthAtMost depthLimit (problemAtomNames Γ goal) hC

@[grind =>]
theorem depth_left_le_ldiv (A B : Category) : A.depth ≤ (A ⧹ B).depth := by
  exact le_trans (Nat.le_max_left A.depth B.depth) (Nat.le_succ _)

@[grind =>]
theorem depth_right_le_ldiv (A B : Category) : B.depth ≤ (A ⧹ B).depth := by
  exact le_trans (Nat.le_max_right A.depth B.depth) (Nat.le_succ _)

@[grind =>]
theorem depth_left_le_rdiv (A B : Category) : A.depth ≤ (A ⧸ B).depth := by
  exact le_trans (Nat.le_max_left A.depth B.depth) (Nat.le_succ _)

@[grind =>]
theorem depth_right_le_rdiv (A B : Category) : B.depth ≤ (A ⧸ B).depth := by
  exact le_trans (Nat.le_max_right A.depth B.depth) (Nat.le_succ _)

/-- Candidate sets are closed under taking the left subcategory of `A\B`. -/
theorem candidate_ldiv_left_of_mem
    {Γ : List Category} {goal A B : Category} {depthLimit : Nat}
    (h : A ⧹ B ∈ categoryPool Γ goal depthLimit) :
    A ∈ categoryPool Γ goal depthLimit := by
  refine mem_categoryPool_of_atoms_depth ?_ ?_
  · intro name hname
    exact atoms_of_mem_categoryPool h name (by simp [Category.atoms, hname])
  · exact le_trans (depth_left_le_ldiv A B) (depth_le_of_mem_categoryPool h)

/-- Candidate sets are closed under taking the right subcategory of `A\B`. -/
theorem candidate_ldiv_right_of_mem
    {Γ : List Category} {goal A B : Category} {depthLimit : Nat}
    (h : A ⧹ B ∈ categoryPool Γ goal depthLimit) :
    B ∈ categoryPool Γ goal depthLimit := by
  refine mem_categoryPool_of_atoms_depth ?_ ?_
  · intro name hname
    exact atoms_of_mem_categoryPool h name (by simp [Category.atoms, hname])
  · exact le_trans (depth_right_le_ldiv A B) (depth_le_of_mem_categoryPool h)

/-- Candidate sets are closed under taking the left subcategory of `A/B`. -/
theorem candidate_rdiv_left_of_mem
    {Γ : List Category} {goal A B : Category} {depthLimit : Nat}
    (h : A ⧸ B ∈ categoryPool Γ goal depthLimit) :
    A ∈ categoryPool Γ goal depthLimit := by
  refine mem_categoryPool_of_atoms_depth ?_ ?_
  · intro name hname
    exact atoms_of_mem_categoryPool h name (by simp [Category.atoms, hname])
  · exact le_trans (depth_left_le_rdiv A B) (depth_le_of_mem_categoryPool h)

/-- Candidate sets are closed under taking the right subcategory of `A/B`. -/
theorem candidate_rdiv_right_of_mem
    {Γ : List Category} {goal A B : Category} {depthLimit : Nat}
    (h : A ⧸ B ∈ categoryPool Γ goal depthLimit) :
    B ∈ categoryPool Γ goal depthLimit := by
  refine mem_categoryPool_of_atoms_depth ?_ ?_
  · intro name hname
    exact atoms_of_mem_categoryPool h name (by simp [Category.atoms, hname])
  · exact le_trans (depth_right_le_rdiv A B) (depth_le_of_mem_categoryPool h)

/-- If the displayed categories of a binary rule are in the paper candidate set,
then the rule can be upgraded to the finite-candidate-aware `ChartRule`.
Hidden metavariables are recovered by subcategory closure of candidates. -/
theorem Rule.toChartRule_of_candidate
    {Γ : List Category} {goal X Y Z : Category} {depthLimit : Nat}
    (rule : Rule X Y Z)
    (hX : X ∈ categoryPool Γ goal depthLimit)
    (hY : Y ∈ categoryPool Γ goal depthLimit)
    (hZ : Z ∈ categoryPool Γ goal depthLimit) :
    ChartRule (categoryPool Γ goal depthLimit) X Y Z := by
  cases rule
  case appRight =>
    exact ChartRule.appRight hZ hY hX
  case appLeft =>
    exact ChartRule.appLeft hX hZ hY
  case compRight C B A =>
    have hC := candidate_rdiv_left_of_mem hZ
    have hA := candidate_rdiv_right_of_mem hZ
    have hB := candidate_rdiv_right_of_mem hX
    exact ChartRule.compRight hC hB hA hX hY hZ
  case compLeft A B C =>
    have hA := candidate_ldiv_left_of_mem hZ
    have hC := candidate_ldiv_right_of_mem hZ
    have hB := candidate_ldiv_right_of_mem hX
    exact ChartRule.compLeft hA hB hC hX hY hZ
  case crossedRight C B A =>
    have hA := candidate_ldiv_left_of_mem hZ
    have hC := candidate_ldiv_right_of_mem hZ
    have hB := candidate_rdiv_right_of_mem hX
    exact ChartRule.crossedRight hC hB hA hX hY hZ
  case crossedLeft B A C =>
    have hC := candidate_rdiv_left_of_mem hZ
    have hA := candidate_rdiv_right_of_mem hZ
    have hB := candidate_rdiv_left_of_mem hX
    exact ChartRule.crossedLeft hB hA hC hX hY hZ

/-! ## Depth-counting theorem from a finite-candidate certificate -/

/-- Placeholder-free statement of the branch-counting conclusion used by the
paper: if every node category of a tree has already been shown to lie in the
paper candidate set, then every node category has depth at most the paper bound. -/
theorem DerivationTree.depth_counting_of_candidate_categories
    {r : Nat} {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (hcat : t.NodeCategoriesContainedIn (categoryPool Γ A (depthBound r Γ A))) :
    ∀ B ∈ t.nodeCategories, B.depth ≤ depthBound r Γ A := by
  intro B hB
  exact depth_le_of_mem_categoryPool (hcat B hB)

/-! ## The pigeonhole core of the depth count

The sharp depth bound

`H = V + V * r`

comes from a finite pigeonhole argument along a single root-to-leaf constructor
branch of one node category:

* at most `V` visible occurrences occur on the branch;
* every invisible occurrence lies in an invisible trace piece with a visible
  boundary (this is the boundary-elimination theorem for size-minimal trees),
  so it is classified by the pair
  `(visible-boundary slot, trace-neighbour slot)`, giving `V * r` codes;
* the code is injective on one branch: equal codes force the two occurrences
  into the *same* invisible trace piece, but trace components preserve the
  addressed subcategory while strict descent along a branch strictly decreases
  constructor count (`sameInvisibleTraceComponent_forbids_strictPrefix_branch`),
  so two distinct branch positions can never share a piece.

The last point is why no interface-state factor `q`, no zone factor `V+1`, and
no repeatable-pair contraction are needed: the draft paper's repeatable pairs
(two same-piece occurrences on one branch) cannot exist at all.
-/

/-- The finite code used by the branch-counting argument.

The components are, in order:

* visible-boundary code (`V` choices),
* trace-neighbour/degree code (`r` choices).
-/
abbrev BranchCode (r V : Nat) :=
  Fin V × Fin r

@[simp]
theorem card_BranchCode (r V : Nat) :
    Fintype.card (BranchCode r V) = V * r := by
  simp [BranchCode, Fintype.card_prod, Fintype.card_fin]

/-- Invisible branch occurrences are bounded by the number of paper codes, once
the code assignment is injective.

If two invisible occurrences on one branch had the same code, they would lie
in the same invisible trace piece — which is impossible for distinct branch
positions, so the code is injective and the count is bounded by `V * r`. -/
theorem branch_invisible_count_le_code {α : Type} {r V : Nat}
    (xs : List α) (visible : α → Bool) (hnodup : xs.Nodup)
    (code : {x // x ∈ xs.filter (fun a => !visible a)} → BranchCode r V)
    (hinj : Function.Injective code) :
    (xs.filter (fun a => !visible a)).length ≤ V * r := by
  let inv := xs.filter (fun a => !visible a)
  have hinvNodup : inv.Nodup := hnodup.filter (fun a => !visible a)
  have hattach : inv.attach.Nodup := (List.nodup_attach).2 hinvNodup
  have hmap : (inv.attach.map code).Nodup := hattach.map hinj
  have hle := hmap.length_le_card
  simpa [inv, List.length_attach, card_BranchCode] using hle

/-- **Depth-counting pigeonhole bound.**  A branch with at most `V` visible
occurrences and injectively coded invisible occurrences has length at most the
sharp bound `V + V*r`. -/
theorem branch_depth_counting_from_codes {α : Type} {r V : Nat}
    (xs : List α) (visible : α → Bool) (hnodup : xs.Nodup)
    (hvisible : (xs.filter visible).length ≤ V)
    (code : {x // x ∈ xs.filter (fun a => !visible a)} → BranchCode r V)
    (hinj : Function.Injective code) :
    xs.length ≤ V + V * r := by
  have hsplit := List.length_eq_length_filter_add (l := xs) visible
  have hinv := branch_invisible_count_le_code xs visible hnodup code hinj
  omega

/-- Every invisible occurrence has a visible boundary in its trace piece.  This
is the paper's “no boundary-free invisible piece” condition. -/
def NoBoundarylessInvisibleComponents {Γ : List Category} {A : Category} (t : DerivationTree Γ A) : Prop :=
  ∀ o : Occurrence t, o.Invisible → HasVisibleBoundary o

/-- A trace-degree bound: every occurrence has at most `r` explicitly listed
trace-neighbours. -/
def TraceDegreeLimit (r : Nat) : Prop :=
  ∀ {Γ : List Category} {A : Category} {t : DerivationTree Γ A} (o : Occurrence t),
    ∃ neighbours : List (Occurrence t),
      neighbours.length ≤ r ∧ ∀ o' : Occurrence t, TraceEdge o o' → o' ∈ neighbours

/-- **Trace-degree bound (proved).** Every occurrence of every derivation tree
has at most `64` trace neighbours (`traceNeighborLimit` is defined to be `64`).

The neighbour list is built executably: take the finite key-candidate list of
`o` (size `≤ 64` by `traceNeighborKeyCandidates_length_le`) and, for each
candidate key, pick the unique occurrence carrying that key out of the finite
occurrence enumeration `t.occurrences`.  Coverage is exactly
`TraceEdge.key_mem_traceNeighborKeyCandidates`, and uniqueness uses
`Occurrence.eq_of_key_eq`.  This discharges the paper's "trace degree is a
rule-system constant `r`" with a concrete `r = 64`, with no axioms or classical
choice. -/
theorem traceDegreeLimit : TraceDegreeLimit 64 := by
  intro Γ A t o
  refine ⟨(traceNeighborKeyCandidates o.key).filterMap
      (fun k => t.occurrences.find? (fun o' => decide (Occurrence.key o' = k))), ?_, ?_⟩
  · refine le_trans (List.length_filterMap_le _ _) ?_
    exact traceNeighborKeyCandidates_length_le o.key
  · intro o' hedge
    have hkey : o'.key ∈ traceNeighborKeyCandidates o.key :=
      hedge.key_mem_traceNeighborKeyCandidates
    have hmem : o' ∈ t.occurrences := DerivationTree.occurrence_mem_occurrences o'
    have hfind : t.occurrences.find? (fun o'' => decide (Occurrence.key o'' = o'.key)) = some o' := by
      have hsome : (t.occurrences.find? (fun o'' => decide (Occurrence.key o'' = o'.key))).isSome := by
        rw [List.find?_isSome]; exact ⟨o', hmem, by simp⟩
      obtain ⟨o'', ho''⟩ := Option.isSome_iff_exists.mp hsome
      have hpred := List.find?_some ho''
      have hk : Occurrence.key o'' = o'.key := by simpa using hpred
      have hoeq : o'' = o' := Occurrence.eq_of_key_eq hk
      rw [ho'', hoeq]
    exact List.mem_filterMap.mpr ⟨o'.key, hkey, hfind⟩

/-- The explicit certificate produced by the branch-counting argument.  It
states exactly the finite-candidate membership needed for the safe
depth-counting theorem above. -/
def NodeCategoryBoundCertificate (r : Nat) {Γ : List Category} {A : Category} (t : DerivationTree Γ A) : Prop :=
  t.NodeCategoriesContainedIn (categoryPool Γ A (depthBound r Γ A))

/-- Boundary-free invisible-piece elimination target for atom-minimal trees.
This is the paper step showing that a size-minimal derivation cannot contain an
invisible trace piece with no visible boundary. -/
def BoundaryFreeInvisiblePieceElimination : Prop :=
  ∀ {Γ : List Category} {A : Category} {t : DerivationTree Γ A},
    t.NodeCategoriesUseProblemAtoms →
      (∀ t' : DerivationTree Γ A, t'.NodeCategoriesUseProblemAtoms → t.size ≤ t'.size) →
        NoBoundarylessInvisibleComponents t

/-- Local contraction target for the boundary-free invisible-piece step: a
problem-atom tree containing an invisible occurrence with no visible boundary
can be contracted.  Minimality then rules such pieces out. -/
def BoundaryFreeInvisiblePieceContracts : Prop :=
  ∀ {Γ : List Category} {A : Category} {t : DerivationTree Γ A},
    t.NodeCategoriesUseProblemAtoms →
      ∀ o : Occurrence t, o.Invisible → ¬ HasVisibleBoundary o →
        Nonempty (ContractionWitness t)

/-- Finite-list counting helper: a duplicate-free list whose members all occur
in another list has length at most the other list. -/
theorem List.Nodup.length_le_of_subset_list {α : Type} {xs ys : List α}
    (hnd : xs.Nodup) (hsub : ∀ a ∈ xs, a ∈ ys) :
    xs.length ≤ ys.length := by
  classical
  have hfinSub : xs.toFinset ⊆ ys.toFinset := by
    intro a ha
    rw [List.mem_toFinset] at ha ⊢
    exact hsub a ha
  have hcard := Finset.card_le_card hfinSub
  have hxs : xs.toFinset.card = xs.length := by
    rw [List.card_toFinset, hnd.dedup]
  have hys : ys.toFinset.card ≤ ys.length := by
    rw [List.card_toFinset]
    exact List.Sublist.length_le (List.dedup_sublist ys)
  omega

/-- Finite index of an element known to occur in a list. -/
def List.finIndexOfMem {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) (x : α) (hx : x ∈ xs) : Fin xs.length :=
  ⟨xs.idxOf x, List.idxOf_lt_length_iff.mpr hx⟩

/-- Equality of list-membership indices recovers equality of elements. -/
theorem List.finIndexOfMem_eq_iff {α : Type} [BEq α] [LawfulBEq α]
    {xs : List α} {x y : α} {hx : x ∈ xs} {hy : y ∈ xs} :
    List.finIndexOfMem xs x hx = List.finIndexOfMem xs y hy ↔ x = y := by
  constructor
  · intro h
    have hidx : xs.idxOf x = xs.idxOf y :=
      congrArg Fin.val h
    exact (List.idxOf_inj hx).mp hidx
  · intro h
    subst h
    rfl

/-- Finite index of a visible slot key in the explicit visible-slot list. -/
def visibleSlotIndex {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (k : Occurrence.Key) (h : k ∈ t.visibleSlots) :
    Fin t.visibleSlots.length :=
  List.finIndexOfMem t.visibleSlots k h

/-- Equality of visible-slot indices recovers equality of visible-slot keys. -/
theorem visibleSlotIndex_eq_iff {Γ : List Category} {A : Category}
    {t : DerivationTree Γ A} {k₁ k₂ : Occurrence.Key}
    {h₁ : k₁ ∈ t.visibleSlots} {h₂ : k₂ ∈ t.visibleSlots} :
    visibleSlotIndex k₁ h₁ = visibleSlotIndex k₂ h₂ ↔ k₁ = k₂ := by
  exact List.finIndexOfMem_eq_iff

/-- Finite index of a member of a length-bounded list, lifted into the external
budget `r`. -/
def List.finIndexOfMemBounded {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) (x : α) (hx : x ∈ xs) {r : Nat} (hlen : xs.length ≤ r) :
    Fin r :=
  ⟨xs.idxOf x, lt_of_lt_of_le (List.idxOf_lt_length_iff.mpr hx) hlen⟩

/-- Equality of lifted bounded-list indices recovers equality of elements,
provided both indices were taken in the same carrier list. -/
theorem List.finIndexOfMemBounded_eq_iff {α : Type} [BEq α] [LawfulBEq α]
    {xs : List α} {x y : α} {hx : x ∈ xs} {hy : y ∈ xs}
    {r : Nat} {hlen : xs.length ≤ r} :
    List.finIndexOfMemBounded xs x hx hlen =
        List.finIndexOfMemBounded xs y hy hlen ↔ x = y := by
  constructor
  · intro h
    have hidx : xs.idxOf x = xs.idxOf y :=
      congrArg Fin.val h
    exact (List.idxOf_inj hx).mp hidx
  · intro h
    subst h
    rfl

/-- A functional choice of trace-neighbour lists satisfying a fixed degree
budget.  Final branch-code construction must use one such choice uniformly, so
equal visible-boundary occurrences compare neighbour slots in the same list. -/
structure TraceNeighbourChoice {Γ : List Category} {A : Category}
    (t : DerivationTree Γ A) (r : Nat) where
  neighbours : Occurrence t → List (Occurrence t)
  length_le : ∀ o : Occurrence t, (neighbours o).length ≤ r
  contains : ∀ o o' : Occurrence t, TraceEdge o o' → o' ∈ neighbours o

/-- Any existential trace-degree bound can be read as a uniform neighbour-list
choice.  The proof uses choice internally; the resulting structure is only used
inside proofs of finite branch codes. -/
theorem traceDegreeLimit_nonempty_choice
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A} {r : Nat}
    (htrace : TraceDegreeLimit r) :
    Nonempty (TraceNeighbourChoice t r) := by
  classical
  choose neighbours hprops using
    (fun o : Occurrence t => htrace o)
  exact ⟨{
    neighbours := neighbours
    length_le := fun o => (hprops o).1
    contains := fun o o' h => (hprops o).2 o' h }⟩

/-- Boundary data for coding one invisible branch occurrence: an invisible
component representative `p`, a visible boundary `v`, and the fixed trace
neighbour choice used to index `p` from `v`. -/
structure BoundaryCodeWitness {Γ : List Category} {A : Category}
    {t : DerivationTree Γ A} {r : Nat}
    (N : TraceNeighbourChoice t r) (o : Occurrence t) where
  p : Occurrence t
  v : Occurrence t
  same_piece : SameInvisibleTraceComponent o p
  p_invisible : p.Invisible
  v_visible : v.Visible
  edge : TraceEdge p v

/-- Coverage target for the concrete visible-slot enumeration: every visible
occurrence key is one of the root, leaf, or principal slots counted by
`DerivationTree.visibleSlots`. -/
def VisibleSlotsComplete : Prop :=
  ∀ {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (o : Occurrence t), o.Visible → o.key ∈ t.visibleSlots

/-- The concrete visible-slot enumeration covers every visible occurrence. -/
theorem visibleSlotsComplete : VisibleSlotsComplete := by
  intro Γ A t o hvisible
  rw [Occurrence.visible_iff, DerivationTree.CategoryOccurrence.visible_iff] at hvisible
  rcases hvisible with hroot | hleaf | hprincipal
  · exact List.mem_append_left _
      (List.mem_append_left _ (DerivationTree.root_visible_mem_rootConstructorSlots hroot))
  · exact List.mem_append_left _
      (List.mem_append_right _ (DerivationTree.leaf_visible_mem_leafConstructorSlots o hleaf))
  · exact List.mem_append_right _
      (DerivationTree.principal_visible_mem_principalVisibleSlots hprincipal)

namespace BoundaryCodeWitness

/-- A visible-boundary proof supplies the boundary-code witness for any fixed
trace-neighbour choice. -/
theorem nonempty_of_hasVisibleBoundary {Γ : List Category} {A : Category}
    {t : DerivationTree Γ A} {r : Nat} {N : TraceNeighbourChoice t r}
    {o : Occurrence t} (hboundary : HasVisibleBoundary o) :
    Nonempty (BoundaryCodeWitness N o) := by
  obtain ⟨p, v, hpiece, hpInv, hvVis, hedge⟩ := hboundary
  exact ⟨{
    p := p
    v := v
    same_piece := hpiece
    p_invisible := hpInv
    v_visible := hvVis
    edge := hedge }⟩

/-- Visible-boundary slot in the global visible-slot budget. -/
def visibleIndex {Γ : List Category} {A : Category}
    {t : DerivationTree Γ A} {r : Nat}
    {N : TraceNeighbourChoice t r} {o : Occurrence t}
    (W : BoundaryCodeWitness N o) :
    Fin (visibleBound Γ A) :=
  let hslot : W.v.key ∈ t.visibleSlots := visibleSlotsComplete W.v W.v_visible
  ⟨(visibleSlotIndex W.v.key hslot).val, by
    have hlt := (visibleSlotIndex W.v.key hslot).isLt
    simpa [DerivationTree.length_visibleSlots] using hlt⟩

/-- Trace-neighbour slot of the invisible boundary representative, indexed
from its visible boundary. -/
def neighbourIndex {Γ : List Category} {A : Category}
    {t : DerivationTree Γ A} {r : Nat}
    {N : TraceNeighbourChoice t r} {o : Occurrence t}
    (W : BoundaryCodeWitness N o) :
    Fin r :=
  let hp : W.p ∈ N.neighbours W.v := N.contains W.v W.p W.edge.symm
  let keys := (N.neighbours W.v).map Occurrence.key
  let hpKey : W.p.key ∈ keys := List.mem_map.mpr ⟨W.p, hp, rfl⟩
  have hlen : keys.length ≤ r := by
    simpa [keys] using N.length_le W.v
  List.finIndexOfMemBounded keys W.p.key hpKey hlen

/-- Equality of visible-boundary indices recovers equality of boundary keys. -/
theorem visibleIndex_eq_key_eq {Γ : List Category} {A : Category}
    {t : DerivationTree Γ A} {r : Nat} {N : TraceNeighbourChoice t r}
    {o₁ o₂ : Occurrence t}
    (W₁ : BoundaryCodeWitness N o₁) (W₂ : BoundaryCodeWitness N o₂)
    (h : W₁.visibleIndex = W₂.visibleIndex) :
    W₁.v.key = W₂.v.key := by
  have hidx : t.visibleSlots.idxOf W₁.v.key = t.visibleSlots.idxOf W₂.v.key := by
    have hval := congrArg Fin.val h
    simpa [visibleIndex, visibleSlotIndex, List.finIndexOfMem] using hval
  exact (List.idxOf_inj (visibleSlotsComplete W₁.v W₁.v_visible)).mp hidx

/-- Equality of visible-boundary indices recovers equality of boundary
occurrences. -/
theorem visibleIndex_eq_occurrence_eq {Γ : List Category} {A : Category}
    {t : DerivationTree Γ A} {r : Nat} {N : TraceNeighbourChoice t r}
    {o₁ o₂ : Occurrence t}
    (W₁ : BoundaryCodeWitness N o₁) (W₂ : BoundaryCodeWitness N o₂)
    (h : W₁.visibleIndex = W₂.visibleIndex) :
    W₁.v = W₂.v :=
  Occurrence.eq_of_key_eq (visibleIndex_eq_key_eq W₁ W₂ h)

/-- Once the visible boundary is known to be the same occurrence, equality of
trace-neighbour indices recovers equality of the invisible boundary
representatives. -/
theorem neighbourIndex_eq_boundary_eq {Γ : List Category} {A : Category}
    {t : DerivationTree Γ A} {r : Nat} {N : TraceNeighbourChoice t r}
    {o₁ o₂ : Occurrence t}
    (W₁ : BoundaryCodeWitness N o₁) (W₂ : BoundaryCodeWitness N o₂)
    (hv : W₁.v = W₂.v)
    (h : W₁.neighbourIndex = W₂.neighbourIndex) :
    W₁.p = W₂.p := by
  apply Occurrence.eq_of_key_eq
  have hidx :
      ((N.neighbours W₁.v).map Occurrence.key).idxOf W₁.p.key =
        ((N.neighbours W₂.v).map Occurrence.key).idxOf W₂.p.key := by
    have hval := congrArg Fin.val h
    simpa [neighbourIndex, List.finIndexOfMemBounded] using hval
  have hidxSame :
      ((N.neighbours W₁.v).map Occurrence.key).idxOf W₁.p.key =
        ((N.neighbours W₁.v).map Occurrence.key).idxOf W₂.p.key := by
    simpa [hv] using hidx
  have hp₁ : W₁.p ∈ N.neighbours W₁.v := N.contains W₁.v W₁.p W₁.edge.symm
  have hkey₁ : W₁.p.key ∈ (N.neighbours W₁.v).map Occurrence.key :=
    List.mem_map.mpr ⟨W₁.p, hp₁, rfl⟩
  exact (List.idxOf_inj hkey₁).mp hidxSame

/-- Equal visible-boundary and neighbour slots put the coded invisible
occurrences in the same invisible trace component. -/
theorem same_piece_of_same_indices {Γ : List Category} {A : Category}
    {t : DerivationTree Γ A} {r : Nat} {N : TraceNeighbourChoice t r}
    {o₁ o₂ : Occurrence t}
    (W₁ : BoundaryCodeWitness N o₁) (W₂ : BoundaryCodeWitness N o₂)
    (hvisible : W₁.visibleIndex = W₂.visibleIndex)
    (hneighbour : W₁.neighbourIndex = W₂.neighbourIndex) :
    SameInvisibleTraceComponent o₁ o₂ := by
  have hv : W₁.v = W₂.v := visibleIndex_eq_occurrence_eq W₁ W₂ hvisible
  have hp : W₁.p = W₂.p := neighbourIndex_eq_boundary_eq W₁ W₂ hv hneighbour
  have htail : SameInvisibleTraceComponent W₁.p o₂ := by
    rw [hp]
    exact W₂.same_piece.symm
  exact SameInvisibleTraceComponent.trans W₁.same_piece htail

end BoundaryCodeWitness

/-- Faithful visible-occurrence counting target.  It avoids choosing a
decidable Boolean for `Visible`: every duplicate-free list containing only
visible occurrences is bounded by the paper's `V = visibleBound Γ A`. -/
def VisibleOccurrenceCountBound : Prop :=
  ∀ {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (xs : List (Occurrence t)),
      xs.Nodup → (∀ o ∈ xs, o.Visible) → xs.length ≤ visibleBound Γ A

/-- Named theorem form of the visible-occurrence bound used by the branch
counting argument. -/
theorem visible_count_le_visibleBound
    (hvisible : VisibleOccurrenceCountBound)
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (xs : List (Occurrence t))
    (hnodup : xs.Nodup) (hallVisible : ∀ o ∈ xs, o.Visible) :
    xs.length ≤ visibleBound Γ A :=
  hvisible xs hnodup hallVisible

/-- Slot coverage implies the visible-count bound.  This isolates the remaining
case analysis on `Visible` from the purely finite counting argument. -/
theorem visibleOccurrenceCountBound_of_visibleSlotsComplete
    (hslots : VisibleSlotsComplete) : VisibleOccurrenceCountBound := by
  intro Γ A t xs hnodup hallVisible
  have hkeyNodup : (xs.map Occurrence.key).Nodup := by
    exact hnodup.map (by
      intro o₁ o₂ hkey
      exact Occurrence.eq_of_key_eq hkey)
  have hkeySub : ∀ k ∈ xs.map Occurrence.key, k ∈ t.visibleSlots := by
    intro k hk
    obtain ⟨o, hoMem, rfl⟩ := List.mem_map.mp hk
    exact hslots o (hallVisible o hoMem)
  have hle : (xs.map Occurrence.key).length ≤ t.visibleSlots.length :=
    List.Nodup.length_le_of_subset_list hkeyNodup hkeySub
  rw [List.length_map, DerivationTree.length_visibleSlots] at hle
  exact hle

/-- **Visible occurrence count.**  Every duplicate-free family of visible
occurrences in a derivation tree is bounded by `visibleBound Γ A`. -/
theorem visibleOccurrenceCountBound : VisibleOccurrenceCountBound :=
  visibleOccurrenceCountBound_of_visibleSlotsComplete visibleSlotsComplete

/-! ## Branch-spine bookkeeping

The final branch-counting proof works along one root-to-constructor branch in a
single derivation-tree node.  The following executable key list is the precise
spine that will be populated by actual occurrences once a node address/category
membership witness is chosen.
-/

/-- Constructor-position keys on one node-addressed branch, represented only by
their proof-irrelevant occurrence keys. -/
def branchConstructorKeys (nodePath : NodePath) (p : CategoryPath) :
    List Occurrence.Key :=
  (CategoryPath.prefixes p).map fun q =>
    ({ nodePath := nodePath, categoryPath := q } : Occurrence.Key)

/-- A branch key spine has exactly one entry for every prefix of the endpoint. -/
theorem length_branchConstructorKeys (nodePath : NodePath) (p : CategoryPath) :
    (branchConstructorKeys nodePath p).length = p.length + 1 := by
  simp [branchConstructorKeys, CategoryPath.length_prefixes]

/-- Branch key spines contain no duplicate occurrence keys. -/
theorem branchConstructorKeys_nodup (nodePath : NodePath) (p : CategoryPath) :
    (branchConstructorKeys nodePath p).Nodup := by
  unfold branchConstructorKeys
  exact CategoryPath.prefixes_nodup p |>.map (by
    intro q₁ q₂ h
    have hcat := congrArg Occurrence.Key.categoryPath h
    simpa using hcat)

/-- The endpoint constructor key is present in its own branch key spine. -/
theorem endpoint_mem_branchConstructorKeys (nodePath : NodePath) (p : CategoryPath) :
    ({ nodePath := nodePath, categoryPath := p } : Occurrence.Key) ∈
      branchConstructorKeys nodePath p := by
  exact List.mem_map.mpr ⟨p, CategoryPath.self_mem_prefixes p, rfl⟩

/-- The occurrence at one constructor prefix of a fixed node-category branch. -/
def branchPrefixOccurrence {Γ : List Category} {A : Category}
    {t : DerivationTree Γ A} (e : DerivationTree.TreeNode t) {p : CategoryPath}
    (hend : p ∈ e.nodeCategory.constructorPositions)
    (q : {q : CategoryPath // q ∈ CategoryPath.prefixes p}) :
    Occurrence t where
  nodePath := e.nodePath
  nodeCategory := e.nodeCategory
  nodeAt := e.nodeAt
  categoryPath := q.1
  isConstructor :=
    Category.isConstructor_of_mem_constructorPositions e.nodeCategory
      (Category.constructorPositions_prefix_closed e.nodeCategory hend q.2)

@[simp]
theorem branchPrefixOccurrence_key {Γ : List Category} {A : Category}
    {t : DerivationTree Γ A} (e : DerivationTree.TreeNode t) {p : CategoryPath}
    (hend : p ∈ e.nodeCategory.constructorPositions)
    (q : {q : CategoryPath // q ∈ CategoryPath.prefixes p}) :
    (branchPrefixOccurrence e hend q).key =
      ({ nodePath := e.nodePath, categoryPath := q.1 } : Occurrence.Key) :=
  rfl

/-- Prefixes as actual occurrences along one node-category branch. -/
def branchPrefixOccurrences {Γ : List Category} {A : Category}
    {t : DerivationTree Γ A} (e : DerivationTree.TreeNode t) {p : CategoryPath}
    (hend : p ∈ e.nodeCategory.constructorPositions) :
    List (Occurrence t) :=
  (CategoryPath.prefixes p).attach.map (branchPrefixOccurrence e hend)

/-- The occurrence spine has one entry for every prefix of the endpoint. -/
theorem length_branchPrefixOccurrences {Γ : List Category} {A : Category}
    {t : DerivationTree Γ A} (e : DerivationTree.TreeNode t) {p : CategoryPath}
    (hend : p ∈ e.nodeCategory.constructorPositions) :
    (branchPrefixOccurrences e hend).length = p.length + 1 := by
  simp [branchPrefixOccurrences, CategoryPath.length_prefixes]

/-- The occurrence spine is duplicate-free because occurrence keys are
duplicate-free along a branch. -/
theorem branchPrefixOccurrences_nodup {Γ : List Category} {A : Category}
    {t : DerivationTree Γ A} (e : DerivationTree.TreeNode t) {p : CategoryPath}
    (hend : p ∈ e.nodeCategory.constructorPositions) :
    (branchPrefixOccurrences e hend).Nodup := by
  unfold branchPrefixOccurrences
  refine (CategoryPath.prefixes_nodup p |>.attach.map ?_)
  intro q₁ q₂ hocc
  apply Subtype.ext
  have hkey := congrArg Occurrence.key hocc
  exact congrArg Occurrence.Key.categoryPath hkey

/-- The keys of the actual branch-prefix occurrences are exactly the
proof-irrelevant branch constructor keys. -/
theorem branchPrefixOccurrences_keys_eq_branchConstructorKeys
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (e : DerivationTree.TreeNode t) {p : CategoryPath}
    (hend : p ∈ e.nodeCategory.constructorPositions) :
    (branchPrefixOccurrences e hend).map Occurrence.key =
      branchConstructorKeys e.nodePath p := by
  unfold branchPrefixOccurrences branchConstructorKeys
  simp

/-- Slot-classified visible branch-prefix occurrences are bounded by the paper
visible budget. -/
theorem branchPrefixOccurrences_visibleSlot_count_le_visibleBound
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (e : DerivationTree.TreeNode t) {p : CategoryPath}
    (hend : p ∈ e.nodeCategory.constructorPositions) :
    ((branchPrefixOccurrences e hend).filter
      (fun o => decide (o.key ∈ t.visibleSlots))).length ≤ visibleBound Γ A := by
  have hkeys := branchPrefixOccurrences_keys_eq_branchConstructorKeys e hend
  have hlen :
      ((branchPrefixOccurrences e hend).filter
        (fun o => decide (o.key ∈ t.visibleSlots))).length =
        ((branchConstructorKeys e.nodePath p).filter
          (fun k => decide (k ∈ t.visibleSlots))).length := by
    rw [← hkeys]
    generalize branchPrefixOccurrences e hend = xs
    induction xs with
    | nil => simp
    | cons o os ih =>
        by_cases hmem : o.key ∈ t.visibleSlots <;> simp [hmem, ih]
  rw [hlen]
  have hnodup :
      ((branchConstructorKeys e.nodePath p).filter
        (fun k => decide (k ∈ t.visibleSlots))).Nodup :=
    (branchConstructorKeys_nodup e.nodePath p).filter _
  have hsub :
      ∀ k ∈ ((branchConstructorKeys e.nodePath p).filter
        (fun k => decide (k ∈ t.visibleSlots))), k ∈ t.visibleSlots := by
    intro k hk
    exact of_decide_eq_true (List.mem_filter.mp hk).2
  have hle :=
    List.Nodup.length_le_of_subset_list hnodup hsub
  rw [DerivationTree.length_visibleSlots] at hle
  exact hle

/-- The concrete branch code attached to one prefix occurrence, once a visible
boundary witness has been chosen for that invisible occurrence. -/
def branchPrefixCodeOfPrefix
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {r : Nat} {N : TraceNeighbourChoice t r}
    (e : DerivationTree.TreeNode t)
    {p : CategoryPath} (hend : p ∈ e.nodeCategory.constructorPositions)
    (q : {q : CategoryPath // q ∈ CategoryPath.prefixes p})
    (W : BoundaryCodeWitness N (branchPrefixOccurrence e hend q)) :
    BranchCode r (visibleBound Γ A) :=
  (W.visibleIndex, W.neighbourIndex)

/-- Equal branch codes put the two prefix occurrences in the same invisible
trace component. -/
theorem branchPrefixCodeOfPrefix_eq_same_piece
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {r : Nat} {N : TraceNeighbourChoice t r}
    (e : DerivationTree.TreeNode t)
    {p : CategoryPath} (hend : p ∈ e.nodeCategory.constructorPositions)
    (q₁ q₂ : {q : CategoryPath // q ∈ CategoryPath.prefixes p})
    (W₁ : BoundaryCodeWitness N (branchPrefixOccurrence e hend q₁))
    (W₂ : BoundaryCodeWitness N (branchPrefixOccurrence e hend q₂))
    (hcode :
      branchPrefixCodeOfPrefix e hend q₁ W₁ =
        branchPrefixCodeOfPrefix e hend q₂ W₂) :
    SameInvisibleTraceComponent
      (branchPrefixOccurrence e hend q₁)
      (branchPrefixOccurrence e hend q₂) := by
  have hvisible : W₁.visibleIndex = W₂.visibleIndex :=
    congrArg (fun c : BranchCode r (visibleBound Γ A) => c.1) hcode
  have hneighbour : W₁.neighbourIndex = W₂.neighbourIndex :=
    congrArg (fun c : BranchCode r (visibleBound Γ A) => c.2) hcode
  exact BoundaryCodeWitness.same_piece_of_same_indices W₁ W₂ hvisible hneighbour

/-- If an occurrence key is outside the visible-slot over-approximation, then
the occurrence is actually invisible. -/
theorem invisible_of_key_not_mem_visibleSlots
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (o : Occurrence t) (hnot : o.key ∉ t.visibleSlots) :
    o.Invisible := by
  intro hvisible
  exact hnot (visibleSlotsComplete o hvisible)

/-- Every branch-prefix occurrence classified as non-visible by the visible-slot
over-approximation has boundary-code data, once boundaryless invisible
components have been eliminated. -/
theorem branchPrefixBoundaryCodeWitness_nonempty
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {r : Nat} {N : TraceNeighbourChoice t r}
    (hboundary : NoBoundarylessInvisibleComponents t)
    (e : DerivationTree.TreeNode t)
    {p : CategoryPath} (hend : p ∈ e.nodeCategory.constructorPositions)
    (x : {o // o ∈ (branchPrefixOccurrences e hend).filter
      (fun a => !decide (a.key ∈ t.visibleSlots))}) :
    Nonempty (BoundaryCodeWitness N x.1) := by
  have hnotBool := (List.mem_filter.mp x.2).2
  have hnot : x.1.key ∉ t.visibleSlots := by
    intro hmem
    simp [hmem] at hnotBool
  have hinv : x.1.Invisible := invisible_of_key_not_mem_visibleSlots x.1 hnot
  exact BoundaryCodeWitness.nonempty_of_hasVisibleBoundary (hboundary x.1 hinv)

/-- Branch-prefix occurrence length bound, once the paper-specific invisible
branch occurrences have been injectively coded by interface state, trace
neighbour, visible boundary, and visible-free zone. -/
theorem branchPrefixOccurrences_length_le_depthBound_of_code
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {r : Nat} (e : DerivationTree.TreeNode t)
    {p : CategoryPath} (hend : p ∈ e.nodeCategory.constructorPositions)
    (code :
      {o // o ∈ (branchPrefixOccurrences e hend).filter
        (fun a => !decide (a.key ∈ t.visibleSlots))} →
        BranchCode r (visibleBound Γ A))
    (hinj : Function.Injective code) :
    (branchPrefixOccurrences e hend).length ≤ depthBound r Γ A := by
  have hcount := branch_depth_counting_from_codes
    (xs := branchPrefixOccurrences e hend)
    (visible := fun o => decide (o.key ∈ t.visibleSlots))
    (r := r) (V := visibleBound Γ A)
    (branchPrefixOccurrences_nodup e hend)
    (branchPrefixOccurrences_visibleSlot_count_le_visibleBound e hend)
    code hinj
  simpa [depthBound] using hcount

/-- Slot-classified visible prefixes in the proof-relevant prefix domain are
bounded by the paper visible budget. -/
theorem branchPrefixAttach_visibleSlot_count_le_visibleBound
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (e : DerivationTree.TreeNode t) {p : CategoryPath}
    (hend : p ∈ e.nodeCategory.constructorPositions) :
    ((((CategoryPath.prefixes p).attach).filter
      (fun q => decide ((branchPrefixOccurrence e hend q).key ∈ t.visibleSlots))).length ≤
        visibleBound Γ A) := by
  let xs := ((CategoryPath.prefixes p).attach).filter
    (fun q => decide ((branchPrefixOccurrence e hend q).key ∈ t.visibleSlots))
  let ks := xs.map (fun q => (branchPrefixOccurrence e hend q).key)
  have hattachNodup : ((CategoryPath.prefixes p).attach).Nodup := by
    exact (List.nodup_attach).mpr (CategoryPath.prefixes_nodup p)
  have hxsNodup : xs.Nodup := hattachNodup.filter _
  have hksNodup : ks.Nodup := by
    refine hxsNodup.map_on ?_
    intro q₁ _ q₂ _ hkey
    apply Subtype.ext
    have hcat := congrArg Occurrence.Key.categoryPath hkey
    simpa [branchPrefixOccurrence_key] using hcat
  have hsub : ∀ k ∈ ks, k ∈ t.visibleSlots := by
    intro k hk
    rcases List.mem_map.mp hk with ⟨q, hq, rfl⟩
    exact of_decide_eq_true (List.mem_filter.mp hq).2
  have hle := List.Nodup.length_le_of_subset_list hksNodup hsub
  simpa [xs, ks, DerivationTree.length_visibleSlots] using hle

/-- Prefix-domain depth counting: an injective paper code for invisible
prefixes bounds the length of the whole constructor branch. -/
theorem branchPrefixAttach_length_le_depthBound_of_code
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {r : Nat} (e : DerivationTree.TreeNode t)
    {p : CategoryPath} (hend : p ∈ e.nodeCategory.constructorPositions)
    (code :
      {x // x ∈ ((CategoryPath.prefixes p).attach).filter
        (fun q => !decide ((branchPrefixOccurrence e hend q).key ∈ t.visibleSlots))} →
        BranchCode r (visibleBound Γ A))
    (hinj : Function.Injective code) :
    p.length + 1 ≤ depthBound r Γ A := by
  have hcount := branch_depth_counting_from_codes
    (xs := (CategoryPath.prefixes p).attach)
    (visible := fun q => decide ((branchPrefixOccurrence e hend q).key ∈ t.visibleSlots))
    (r := r) (V := visibleBound Γ A)
    ((List.nodup_attach).mpr (CategoryPath.prefixes_nodup p))
    (branchPrefixAttach_visibleSlot_count_le_visibleBound e hend)
    code hinj
  simpa [depthBound, CategoryPath.length_prefixes] using hcount

/-- Prefix-domain form of non-visible-slot invisibility. -/
theorem branchPrefixOccurrence_invisible_of_not_visibleSlot
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (e : DerivationTree.TreeNode t)
    {p : CategoryPath} (hend : p ∈ e.nodeCategory.constructorPositions)
    (q : {q : CategoryPath // q ∈ CategoryPath.prefixes p})
    (hnot : (branchPrefixOccurrence e hend q).key ∉ t.visibleSlots) :
    (branchPrefixOccurrence e hend q).Invisible :=
  invisible_of_key_not_mem_visibleSlots (branchPrefixOccurrence e hend q) hnot

/-- Prefix-domain boundary-code data for any invisible prefix selected by the
visible-slot filter. -/
theorem branchPrefixBoundaryCodeWitness_nonempty_of_prefix
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {r : Nat} {N : TraceNeighbourChoice t r}
    (hboundary : NoBoundarylessInvisibleComponents t)
    (e : DerivationTree.TreeNode t)
    {p : CategoryPath} (hend : p ∈ e.nodeCategory.constructorPositions)
    (x : {q // q ∈ ((CategoryPath.prefixes p).attach).filter
      (fun q => !decide ((branchPrefixOccurrence e hend q).key ∈ t.visibleSlots))}) :
    Nonempty (BoundaryCodeWitness N (branchPrefixOccurrence e hend x.1)) := by
  have hnotBool := (List.mem_filter.mp x.2).2
  have hnot : (branchPrefixOccurrence e hend x.1).key ∉ t.visibleSlots := by
    simpa using hnotBool
  have hinv := branchPrefixOccurrence_invisible_of_not_visibleSlot e hend x.1 hnot
  exact BoundaryCodeWitness.nonempty_of_hasVisibleBoundary
    (hboundary (branchPrefixOccurrence e hend x.1) hinv)

/-- An invisible trace component cannot connect two strict-prefix endpoints on
the same category branch: trace components preserve the addressed subcategory,
while strict descent strictly decreases constructor count. -/
theorem sameInvisibleTraceComponent_forbids_strictPrefix_branch
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (e : DerivationTree.TreeNode t)
    {p : CategoryPath} (hend : p ∈ e.nodeCategory.constructorPositions)
    (q₁ q₂ : {q : CategoryPath // q ∈ CategoryPath.prefixes p})
    (hstrict : q₁.1.StrictPrefix q₂.1)
    (hpiece :
      SameInvisibleTraceComponent
        (branchPrefixOccurrence e hend q₁)
        (branchPrefixOccurrence e hend q₂)) :
    False := by
  obtain ⟨S, hS⟩ : ∃ S, e.nodeCategory.subcategoryAt? q₁.1 = some S := by
    obtain ⟨X, Y, h | h⟩ :=
      Category.isConstructor_of_mem_constructorPositions e.nodeCategory
        (Category.constructorPositions_prefix_closed e.nodeCategory hend q₁.2)
    · exact ⟨X ⧸ Y, h⟩
    · exact ⟨X ⧹ Y, h⟩
  obtain ⟨T, hT⟩ : ∃ T, e.nodeCategory.subcategoryAt? q₂.1 = some T := by
    obtain ⟨X, Y, h | h⟩ :=
      Category.isConstructor_of_mem_constructorPositions e.nodeCategory
        (Category.constructorPositions_prefix_closed e.nodeCategory hend q₂.2)
    · exact ⟨X ⧸ Y, h⟩
    · exact ⟨X ⧹ Y, h⟩
  have hlt : T.constructors < S.constructors :=
    Category.constructors_lt_of_strictPrefix_subcategoryAt? hS hT hstrict
  have hsame :
      e.nodeCategory.subcategoryAt? q₁.1 =
        e.nodeCategory.subcategoryAt? q₂.1 := by
    simpa [branchPrefixOccurrence] using hpiece.sameSub
  have hST : S = T := by
    rw [hS, hT] at hsame
    simpa using hsame
  have hconstr : S.constructors = T.constructors := congrArg Category.constructors hST
  omega

/-- Construct an injective paper branch code for invisible prefixes.  The code
uses boundaryless-piece elimination for visible-boundary data and the
trace-degree bound for the neighbour slot. -/
theorem branchPrefixCode_injective
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {r : Nat}
    (hboundary : NoBoundarylessInvisibleComponents t)
    (htrace : TraceDegreeLimit r)
    (e : DerivationTree.TreeNode t)
    {p : CategoryPath} (hend : p ∈ e.nodeCategory.constructorPositions) :
    ∃ code :
      {x // x ∈ ((CategoryPath.prefixes p).attach).filter
        (fun q => !decide ((branchPrefixOccurrence e hend q).key ∈ t.visibleSlots))} →
        BranchCode r (visibleBound Γ A),
      Function.Injective code := by
  classical
  obtain ⟨N⟩ := traceDegreeLimit_nonempty_choice (t := t) htrace
  let domain := ((CategoryPath.prefixes p).attach).filter
    (fun q => !decide ((branchPrefixOccurrence e hend q).key ∈ t.visibleSlots))
  have hW :
      ∀ x : {x // x ∈ domain},
        Nonempty (BoundaryCodeWitness N (branchPrefixOccurrence e hend x.1)) := by
    intro x
    exact branchPrefixBoundaryCodeWitness_nonempty_of_prefix hboundary e hend x
  let W := fun x : {x // x ∈ domain} => Classical.choice (hW x)
  let code : {x // x ∈ domain} → BranchCode r (visibleBound Γ A) :=
    fun x => branchPrefixCodeOfPrefix e hend x.1 (W x)
  refine ⟨code, ?_⟩
  intro x y hcode
  change branchPrefixCodeOfPrefix e hend x.1 (W x) =
      branchPrefixCodeOfPrefix e hend y.1 (W y) at hcode
  rcases CategoryPath.mem_prefixes_comparable x.1.2 y.1.2 with hprefix | hprefix
  · by_cases hpath : x.1.1 = y.1.1
    · apply Subtype.ext
      apply Subtype.ext
      exact hpath
    · have hstrict : x.1.1.StrictPrefix y.1.1 := hprefix.strict_of_ne hpath
      have hpiece :=
        branchPrefixCodeOfPrefix_eq_same_piece e hend x.1 y.1 (W x) (W y) hcode
      exact False.elim
        (sameInvisibleTraceComponent_forbids_strictPrefix_branch e hend x.1 y.1 hstrict hpiece)
  · by_cases hpath : y.1.1 = x.1.1
    · apply Subtype.ext
      apply Subtype.ext
      exact hpath.symm
    · have hstrict : y.1.1.StrictPrefix x.1.1 := hprefix.strict_of_ne hpath
      have hpiece :=
        branchPrefixCodeOfPrefix_eq_same_piece e hend x.1 y.1 (W x) (W y) hcode
      exact False.elim
        (sameInvisibleTraceComponent_forbids_strictPrefix_branch e hend y.1 x.1
          hstrict hpiece.symm)

/-- Branch-length bound for one constructor position, obtained from the
injective prefix code. -/
theorem branchPrefix_length_le_depthBound
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {r : Nat}
    (hboundary : NoBoundarylessInvisibleComponents t)
    (htrace : TraceDegreeLimit r)
    (e : DerivationTree.TreeNode t)
    {p : CategoryPath} (hend : p ∈ e.nodeCategory.constructorPositions) :
    p.length + 1 ≤ depthBound r Γ A := by
  obtain ⟨code, hinj⟩ := branchPrefixCode_injective hboundary htrace e hend
  exact branchPrefixAttach_length_le_depthBound_of_code e hend code hinj

/-- Slot-classified visible branch keys are bounded by the paper visible
budget.  This uses the executable `visibleSlots` over-approximation rather than
deciding the `Visible` proposition. -/
theorem branch_visibleSlot_count_le_visibleBound
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (nodePath : NodePath) (p : CategoryPath) :
    ((branchConstructorKeys nodePath p).filter
      (fun k => decide (k ∈ t.visibleSlots))).length ≤ visibleBound Γ A := by
  have hnodup :
      ((branchConstructorKeys nodePath p).filter
        (fun k => decide (k ∈ t.visibleSlots))).Nodup :=
    (branchConstructorKeys_nodup nodePath p).filter _
  have hsub :
      ∀ k ∈ ((branchConstructorKeys nodePath p).filter
        (fun k => decide (k ∈ t.visibleSlots))), k ∈ t.visibleSlots := by
    intro k hk
    exact of_decide_eq_true (List.mem_filter.mp hk).2
  have hle :=
    List.Nodup.length_le_of_subset_list hnodup hsub
  rw [DerivationTree.length_visibleSlots] at hle
  exact hle

/-- Every node category of `t` has depth at most the bound `H = V + V*r`. -/
def DerivationTree.NodeCategoriesDepthBounded (r : Nat) {Γ : List Category} {A : Category} (t : DerivationTree Γ A) : Prop :=
  ∀ B ∈ t.nodeCategories, B.depth ≤ depthBound r Γ A

/-- Constructor-position branch lengths in every node category are bounded by
the depth bound.  This is the local form naturally produced by the
branch-counting argument. -/
def DerivationTree.NodeConstructorPositionsBounded (r : Nat)
    {Γ : List Category} {A : Category} (t : DerivationTree Γ A) : Prop :=
  ∀ B ∈ t.nodeCategories, ∀ p, p ∈ B.constructorPositions →
    p.length + 1 ≤ depthBound r Γ A

/-- Bounded constructor-position branch lengths imply bounded node-category
depths. -/
theorem DerivationTree.nodeCategoriesDepthBounded_of_constructorPositionsBounded
    {r : Nat} {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (hbranches : t.NodeConstructorPositionsBounded r) :
    t.NodeCategoriesDepthBounded r := by
  intro B hB
  exact Category.depth_le_of_constructorPosition_length B (depthBound r Γ A)
    (hbranches B hB)

/-- The concrete normal-form output needed from the counting proof:
an explicit derivation tree using only problem atoms and whose node categories
are bounded by `H`. -/
def DepthBoundedNormalForm (r : Nat) : Prop :=
  ∀ {Γ : List Category} {A : Category}, Γ ⇒ccg A →
    ∃ t : DerivationTree Γ A, t.NodeCategoriesUseProblemAtoms ∧ t.NodeCategoriesDepthBounded r

/-- Problem-atom and depth bounds on every node category imply the finite
candidate-set certificate. -/
theorem DerivationTree.nodeCategoryBoundCertificate_of_atoms_depth
    {r : Nat} {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (hatoms : t.NodeCategoriesUseProblemAtoms)
    (hdepth : t.NodeCategoriesDepthBounded r) :
    NodeCategoryBoundCertificate r t := by
  intro B hB
  exact mem_categoryPool_of_atoms_depth (hatoms B hB) (hdepth B hB)

/-- A bounded normal-form tree theorem finalizes `NodeCategoryBoundComplete`. -/
theorem nodeCategoryBoundComplete_of_depthBoundedNormalForm
    {r : Nat} (hbounded : DepthBoundedNormalForm r) :
    ∀ {Γ : List Category} {A : Category}, Γ ⇒ccg A →
      ∃ t : DerivationTree Γ A, NodeCategoryBoundCertificate r t := by
  intro Γ A hDerives
  obtain ⟨t, hatoms, hdepth⟩ := hbounded hDerives
  exact ⟨t, t.nodeCategoryBoundCertificate_of_atoms_depth hatoms hdepth⟩

namespace DerivationTree

theorem root_mem_nodeCategories {Γ : List Category} {A : Category} (t : DerivationTree Γ A) :
    A ∈ t.nodeCategories := by
  cases t <;> simp [DerivationTree.nodeCategories]

/-- Every category listed in `nodeCategories` is represented by some executable
node entry with the same category. -/
theorem nodeCategory_mem_nodeEntries :
    {Γ : List Category} → {A B : Category} → (t : DerivationTree Γ A) →
      B ∈ t.nodeCategories → ∃ e : TreeNode t, e ∈ t.nodeEntries ∧ e.nodeCategory = B
  | _, _, B, .leaf A, hB => by
      simp only [DerivationTree.nodeCategories_leaf, List.mem_singleton] at hB
      subst B
      refine ⟨{ nodePath := [], nodeCategory := _, nodeAt := rfl }, ?_, rfl⟩
      simp [DerivationTree.nodeEntries]
  | _, _, B, .typeRaiseRight C t, hB => by
      simp only [DerivationTree.nodeCategories_typeRaiseRight, List.mem_cons] at hB
      rcases hB with hB | hB
      · subst B
        refine ⟨{ nodePath := [], nodeCategory := _, nodeAt := rfl }, ?_, rfl⟩
        simp [DerivationTree.nodeEntries]
      · obtain ⟨e, heMem, heCat⟩ := nodeCategory_mem_nodeEntries t hB
        refine ⟨TreeNode.underUnaryRight C e, ?_, ?_⟩
        · exact List.mem_cons_of_mem _
            (List.mem_map.mpr ⟨e, heMem, rfl⟩)
        · simpa [TreeNode.underUnaryRight] using heCat
  | _, _, B, .typeRaiseLeft C t, hB => by
      simp only [DerivationTree.nodeCategories_typeRaiseLeft, List.mem_cons] at hB
      rcases hB with hB | hB
      · subst B
        refine ⟨{ nodePath := [], nodeCategory := _, nodeAt := rfl }, ?_, rfl⟩
        simp [DerivationTree.nodeEntries]
      · obtain ⟨e, heMem, heCat⟩ := nodeCategory_mem_nodeEntries t hB
        refine ⟨TreeNode.underUnaryLeft C e, ?_, ?_⟩
        · exact List.mem_cons_of_mem _
            (List.mem_map.mpr ⟨e, heMem, rfl⟩)
        · simpa [TreeNode.underUnaryLeft] using heCat
  | _, _, B, .binary t₁ t₂ rule, hB => by
      simp only [DerivationTree.nodeCategories_binary, List.mem_cons, List.mem_append] at hB
      rcases hB with hB | hB | hB
      · subst B
        let e : TreeNode (DerivationTree.binary t₁ t₂ rule) :=
          { nodePath := [], nodeCategory := (DerivationTree.binary t₁ t₂ rule).root,
            nodeAt := rfl }
        refine ⟨e, ?_, rfl⟩
        simp [DerivationTree.nodeEntries, e]
      · obtain ⟨e, heMem, heCat⟩ := nodeCategory_mem_nodeEntries t₁ hB
        refine ⟨TreeNode.underBinaryLeft rule e, ?_, ?_⟩
        · exact List.mem_cons_of_mem _
            (List.mem_append_left _
              (List.mem_map.mpr ⟨e, heMem, rfl⟩))
        · simpa [TreeNode.underBinaryLeft] using heCat
      · obtain ⟨e, heMem, heCat⟩ := nodeCategory_mem_nodeEntries t₂ hB
        refine ⟨TreeNode.underBinaryRight rule e, ?_, ?_⟩
        · exact List.mem_cons_of_mem _
            (List.mem_append_right _
              (List.mem_map.mpr ⟨e, heMem, rfl⟩))
        · simpa [TreeNode.underBinaryRight] using heCat

theorem nodeCategoriesContainedIn_of_typeRaiseRight
    {K : List Category} {Γ : List Category} {A C : Category} {t : DerivationTree Γ A}
    (h : (DerivationTree.typeRaiseRight C t).NodeCategoriesContainedIn K) :
    t.NodeCategoriesContainedIn K := by
  intro B hB
  exact h B (by simp [DerivationTree.nodeCategories, hB])

theorem nodeCategoriesContainedIn_of_typeRaiseLeft
    {K : List Category} {Γ : List Category} {A C : Category} {t : DerivationTree Γ A}
    (h : (DerivationTree.typeRaiseLeft C t).NodeCategoriesContainedIn K) :
    t.NodeCategoriesContainedIn K := by
  intro B hB
  exact h B (by simp [DerivationTree.nodeCategories, hB])

theorem nodeCategoriesContainedIn_left_of_binary
    {K : List Category} {Γ Δ : List Category} {A B C : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ B} {rule : Rule A B C}
    (h : (DerivationTree.binary t₁ t₂ rule).NodeCategoriesContainedIn K) :
    t₁.NodeCategoriesContainedIn K := by
  intro X hX
  exact h X (by simp [DerivationTree.nodeCategories, hX])

theorem nodeCategoriesContainedIn_right_of_binary
    {K : List Category} {Γ Δ : List Category} {A B C : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ B} {rule : Rule A B C}
    (h : (DerivationTree.binary t₁ t₂ rule).NodeCategoriesContainedIn K) :
    t₂.NodeCategoriesContainedIn K := by
  intro Y hY
  exact h Y (by simp [DerivationTree.nodeCategories, hY])

end DerivationTree

/-- **Branch counting.**  The counting argument needs no repeatable-pair
elimination: boundaryless-invisible-component elimination plus the fixed
trace-degree bound already bound every constructor-position branch by
`H = V + V*r`. -/
theorem nodeConstructorPositionsBounded_of_boundary_trace
    {r : Nat} {Γ : List Category} {A : Category}
    {t : DerivationTree Γ A}
    (hboundary : NoBoundarylessInvisibleComponents t)
    (htrace : TraceDegreeLimit r) :
    t.NodeConstructorPositionsBounded r := by
  intro B hB p hp
  obtain ⟨e, _heMem, heCat⟩ := DerivationTree.nodeCategory_mem_nodeEntries t hB
  have hp' : p ∈ e.nodeCategory.constructorPositions := by
    simpa [heCat] using hp
  exact branchPrefix_length_le_depthBound hboundary htrace e hp'

namespace AtomRestrictedDerivable

/-- Atom-restricted derivations can be represented by explicit derivation trees
whose every node category uses only the same tracked atoms. -/
theorem exists_derivationTree_with_nodeCategoriesUseOnlyAtoms
    {atomNames : List String} {Γ : List Category} {A : Category}
    (h : AtomRestrictedDerivable atomNames Γ A) :
    ∃ t : DerivationTree Γ A, ∀ B ∈ t.nodeCategories, UsesOnlyAtoms atomNames B := by
  induction h with
  | leaf hA =>
      exact ⟨.leaf _, by simp [DerivationTree.nodeCategories_leaf, hA]⟩
  | typeRaiseRight hC _ ih =>
      obtain ⟨t, ht⟩ := ih
      have hRoot : UsesOnlyAtoms atomNames t.root := by
        exact ht t.root (DerivationTree.root_mem_nodeCategories t)
      refine ⟨.typeRaiseRight _ t, ?_⟩
      intro B hB
      simp only [DerivationTree.nodeCategories_typeRaiseRight, List.mem_cons] at hB
      rcases hB with hB | hB
      · subst hB
        exact UsesOnlyAtoms.rdiv hC (UsesOnlyAtoms.ldiv hRoot hC)
      · exact ht B hB
  | typeRaiseLeft hC _ ih =>
      obtain ⟨t, ht⟩ := ih
      have hRoot : UsesOnlyAtoms atomNames t.root := by
        exact ht t.root (DerivationTree.root_mem_nodeCategories t)
      refine ⟨.typeRaiseLeft _ t, ?_⟩
      intro B hB
      simp only [DerivationTree.nodeCategories_typeRaiseLeft, List.mem_cons] at hB
      rcases hB with hB | hB
      · subst hB
        exact UsesOnlyAtoms.ldiv (UsesOnlyAtoms.rdiv hC hRoot) hC
      · exact ht B hB
  | binary _ _ rule ih₁ ih₂ =>
      obtain ⟨t₁, ht₁⟩ := ih₁
      obtain ⟨t₂, ht₂⟩ := ih₂
      refine ⟨.binary t₁ t₂ rule.toRule, ?_⟩
      intro B hB
      simp only [DerivationTree.nodeCategories_binary, List.mem_cons, List.mem_append] at hB
      rcases hB with hB | hB | hB
      · subst hB
        exact rule.result_usesOnlyAtoms
      · exact ht₁ B hB
      · exact ht₂ B hB

end AtomRestrictedDerivable

/-- Every derivable sequent has an explicit tree whose node categories use only
atoms from the original recognition problem. -/
theorem Derivable.exists_problemAtomDerivationTree
    {Γ : List Category} {A : Category} (h : Γ ⇒ccg A) :
    ∃ t : DerivationTree Γ A, t.NodeCategoriesUseProblemAtoms := by
  exact h.toAtomRestrictedDerivableUsingProblemAtoms
    |>.exists_derivationTree_with_nodeCategoriesUseOnlyAtoms

/-- Among problem-atom trees for a derivable sequent, one has minimal `size`. -/
theorem Derivable.exists_minimalProblemAtomDerivationTree
    {Γ : List Category} {A : Category} (h : Γ ⇒ccg A) :
    ∃ t : DerivationTree Γ A,
      t.NodeCategoriesUseProblemAtoms ∧
      ∀ t' : DerivationTree Γ A, t'.NodeCategoriesUseProblemAtoms → t.size ≤ t'.size := by
  classical
  obtain ⟨t₀, ht₀⟩ := h.exists_problemAtomDerivationTree
  let P : Nat → Prop :=
    fun n => ∃ t : DerivationTree Γ A, t.NodeCategoriesUseProblemAtoms ∧ t.size = n
  have hP : ∃ n, P n := ⟨t₀.size, t₀, ht₀, rfl⟩
  obtain ⟨t, hatoms, hsize⟩ := Nat.find_spec hP
  refine ⟨t, hatoms, ?_⟩
  intro t' ht'
  have hfind_le : Nat.find hP ≤ t'.size := Nat.find_le ⟨t', ht', rfl⟩
  omega

/-- If boundary-free invisible pieces have been eliminated for atom-minimal
trees, every derivable sequent has an atom-minimal tree satisfying that
boundary condition. -/
theorem Derivable.exists_minimalProblemAtom_noBoundarylessInvisibleComponents
    (hboundary : BoundaryFreeInvisiblePieceElimination)
    {Γ : List Category} {A : Category} (h : Γ ⇒ccg A) :
    ∃ t : DerivationTree Γ A,
      t.NodeCategoriesUseProblemAtoms ∧ NoBoundarylessInvisibleComponents t := by
  obtain ⟨t, hatoms, hmin⟩ := h.exists_minimalProblemAtomDerivationTree
  exact ⟨t, hatoms, hboundary hatoms hmin⟩

/-- If every boundary-free invisible piece contracts, then atom-minimal trees
have no boundary-free invisible pieces. -/
theorem boundaryFreeInvisiblePieceElimination_of_contracts
    (hcontract : BoundaryFreeInvisiblePieceContracts) :
    BoundaryFreeInvisiblePieceElimination := by
  intro Γ A t hatoms hmin o hinvisible
  by_contra hnoBoundary
  obtain ⟨w⟩ := hcontract hatoms o hinvisible hnoBoundary
  have ht'Atoms : w.target.NodeCategoriesUseProblemAtoms :=
    w.preserves_problem_atoms hatoms
  have hle := hmin w.target ht'Atoms
  have hlt := w.size_lt
  omega

/-- A piece-level boundary-free contraction theorem implies the occurrence-level
target used by the minimality argument: an invisible occurrence with no visible
boundary generates a finite boundary-free invisible piece. -/
theorem boundaryFreeInvisiblePieceContracts_of_pieces
    (hpieces : BoundaryFreeInvisiblePieceContractsFromPieces) :
    BoundaryFreeInvisiblePieceContracts := by
  intro Γ A t hatoms o hinvisible hnoBoundary
  obtain ⟨P, _hoMem, hfree⟩ :=
    exists_boundaryFreeInvisiblePieceOfOccurrence o hinvisible hnoBoundary
  exact hpieces hatoms P hfree

/-- Piece-level boundary-free contraction is enough to eliminate boundary-free
invisible components from atom-minimal derivation trees. -/
theorem boundaryFreeInvisiblePieceElimination_of_piece_contracts
    (hpieces : BoundaryFreeInvisiblePieceContractsFromPieces) :
    BoundaryFreeInvisiblePieceElimination :=
  boundaryFreeInvisiblePieceElimination_of_contracts
    (boundaryFreeInvisiblePieceContracts_of_pieces hpieces)

/-- Boundary-free elimination from the repaired two-case architecture: safe
pieces are handled by node-local atom replacement, while pieces containing a
protected unary type-raising skeleton are handled by a separate band/protected
case. -/
theorem boundaryFreeInvisiblePieceElimination_of_replaceable_or_protected_piece_contracts
    (hreplace : BoundaryFreeReplaceableInvisiblePieceContractsFromPieces)
    (hprotected : BoundaryFreeProtectedSkeletonPieceContracts) :
    BoundaryFreeInvisiblePieceElimination :=
  boundaryFreeInvisiblePieceElimination_of_piece_contracts
    (boundaryFreeInvisiblePieceContractsFromPieces_of_replaceable_or_protected
      hreplace hprotected)

/-- Boundary-free-piece elimination, together with a trace-degree bound,
gives the depth-bounded normal form.  The branch-counting proof does not use
repeatable-pair elimination: repeatable pairs cannot occur at all, because two
occurrences on one branch never share a trace piece. -/
theorem depthBoundedNormalForm_of_boundaryElimination_and_trace
    {r : Nat}
    (hboundary : BoundaryFreeInvisiblePieceElimination)
    (htrace : TraceDegreeLimit r) :
    DepthBoundedNormalForm r := by
  intro Γ A hDerives
  obtain ⟨t, hatoms, hmin⟩ := hDerives.exists_minimalProblemAtomDerivationTree
  have hnoBoundary : NoBoundarylessInvisibleComponents t :=
    hboundary hatoms hmin
  refine ⟨t, hatoms, ?_⟩
  exact t.nodeCategoriesDepthBounded_of_constructorPositionsBounded
    (nodeConstructorPositionsBounded_of_boundary_trace hnoBoundary htrace)

/-- Piece-level boundary-free contraction plus trace-degree boundedness gives
the depth-bounded normal form directly. -/
theorem depthBoundedNormalForm_of_pieceContracts_and_trace
    {r : Nat}
    (hpieces : BoundaryFreeInvisiblePieceContractsFromPieces)
    (htrace : TraceDegreeLimit r) :
    DepthBoundedNormalForm r :=
  depthBoundedNormalForm_of_boundaryElimination_and_trace
    (boundaryFreeInvisiblePieceElimination_of_piece_contracts hpieces)
    htrace

/-- Depth-bounded normal form from the repaired two-case boundary-free
architecture and the trace-degree bound. -/
theorem depthBoundedNormalForm_of_replaceable_or_protected_piece_contracts_and_trace
    {r : Nat}
    (hreplace : BoundaryFreeReplaceableInvisiblePieceContractsFromPieces)
    (hprotected : BoundaryFreeProtectedSkeletonPieceContracts)
    (htrace : TraceDegreeLimit r) :
    DepthBoundedNormalForm r :=
  depthBoundedNormalForm_of_boundaryElimination_and_trace
    (boundaryFreeInvisiblePieceElimination_of_replaceable_or_protected_piece_contracts
      hreplace hprotected)
    htrace

/-- If every node category of a tree lies in a fixed candidate set, then the
tree can be read as a `ChartDerivable` derivation over that same candidate set.
The fixed candidate set is crucial: subtrees are parsed inside the global chart,
not inside their own local input/goal problem. -/
theorem DerivationTree.toChartDerivable_of_containedNodeCategories
    {Ω : List Category} {goal : Category} {depthLimit : Nat} :
    ∀ {Γ : List Category} {A : Category} (t : DerivationTree Γ A),
      t.NodeCategoriesContainedIn (categoryPool Ω goal depthLimit) →
      ChartDerivable (categoryPool Ω goal depthLimit) Γ A
  | _, _, .leaf A, hcat => by
      exact ChartDerivable.leaf (hcat A (by simp [DerivationTree.nodeCategories]))
  | _, _, .typeRaiseRight C t, hcat => by
      have hOut : C ⧸ (t.root ⧹ C) ∈ categoryPool Ω goal depthLimit :=
        hcat _ (by simp [DerivationTree.nodeCategories])
      have hC : C ∈ categoryPool Ω goal depthLimit :=
        candidate_rdiv_left_of_mem hOut
      have hsub : t.NodeCategoriesContainedIn (categoryPool Ω goal depthLimit) := by
        intro B hB
        exact hcat B (by simp [DerivationTree.nodeCategories, hB])
      exact ChartDerivable.typeRaiseRight hC hOut
        (DerivationTree.toChartDerivable_of_containedNodeCategories t hsub)
  | _, _, .typeRaiseLeft C t, hcat => by
      have hOut : (C ⧸ t.root) ⧹ C ∈ categoryPool Ω goal depthLimit :=
        hcat _ (by simp [DerivationTree.nodeCategories])
      have hC : C ∈ categoryPool Ω goal depthLimit :=
        candidate_ldiv_right_of_mem hOut
      have hsub : t.NodeCategoriesContainedIn (categoryPool Ω goal depthLimit) := by
        intro B hB
        exact hcat B (by simp [DerivationTree.nodeCategories, hB])
      exact ChartDerivable.typeRaiseLeft hC hOut
        (DerivationTree.toChartDerivable_of_containedNodeCategories t hsub)
  | _, _, .binary t₁ t₂ rule, hcat => by
      have hOut : (DerivationTree.binary t₁ t₂ rule).root ∈ categoryPool Ω goal depthLimit :=
        hcat _ (by simp [DerivationTree.nodeCategories])
      have hleftRoot : t₁.root ∈ categoryPool Ω goal depthLimit :=
        hcat _ (by simp [DerivationTree.nodeCategories, DerivationTree.root_mem_nodeCategories t₁])
      have hrightRoot : t₂.root ∈ categoryPool Ω goal depthLimit :=
        hcat _ (by simp [DerivationTree.nodeCategories, DerivationTree.root_mem_nodeCategories t₂])
      have hleftCert : t₁.NodeCategoriesContainedIn (categoryPool Ω goal depthLimit) := by
        intro B hB
        exact hcat B (by simp [DerivationTree.nodeCategories, hB])
      have hrightCert : t₂.NodeCategoriesContainedIn (categoryPool Ω goal depthLimit) := by
        intro B hB
        exact hcat B (by simp [DerivationTree.nodeCategories, hB])
      exact ChartDerivable.binary
        (DerivationTree.toChartDerivable_of_containedNodeCategories t₁ hleftCert)
        (DerivationTree.toChartDerivable_of_containedNodeCategories t₂ hrightCert)
        (rule.toChartRule_of_candidate hleftRoot hrightRoot hOut)

/-- A depth-counting certificate upgrades an explicit derivation tree to a
finite-candidate-aware derivation over the paper candidate set for the whole
problem. -/
theorem DerivationTree.toChartDerivable_of_nodeCategoryBoundCertificate
    {Γ : List Category} {A : Category} (t : DerivationTree Γ A) {r : Nat}
    (hcert : NodeCategoryBoundCertificate r t) :
    ChartDerivable (categoryPool Γ A (depthBound r Γ A)) Γ A :=
  DerivationTree.toChartDerivable_of_containedNodeCategories t hcert

end Mathling.CCG
