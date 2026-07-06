import Mathling.CCG.Tree
import Mathling.CCG.Occurrence
import Mathlib.Data.Nat.Find
import Mathlib.Logic.Relation

/-!
# Node occurrences, trace edges, visibility, and size-minimal derivations

This module records the structural data the band-contraction argument of
`ccg_decidability_proof_3-1.pdf` reasons about, on top of the explicit trees of
`Mathling.CCG.Tree`:

* `DerivationTree.nodeCategories`, the multiset of every node category, and the identity
  `DerivationTree.size = (nodeCategories.map constructors).sum` tying the size measure to it;
* `Occurrence`, a node-addressed constructor occurrence `(node address, category position)`;
* `Visible` / `Invisible`, the paper's visibility classification of occurrences;
* `Derivable.exists_minimalDerivationTree`, the existence of a `size`-minimal derivation tree
  `D_min` for a derivable sequent (the paper's `cor:minimal` precondition).

The size-minimal tree is the object on which `Band` performs contraction.
-/

set_option linter.style.longLine false

namespace Mathling.CCG

open Category

/-- Local Nat-list lemma: a member of a list of naturals is bounded by the
list sum.  Kept local to avoid importing a large ordered-monoid API here. -/
theorem Nat.le_sum_of_mem_list {n : Nat} :
    ∀ {xs : List Nat}, n ∈ xs → n ≤ xs.sum
  | [], h => by simp at h
  | x :: xs, h => by
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact Nat.le_add_right n xs.sum
      · exact le_trans (Nat.le_sum_of_mem_list h) (Nat.le_add_left xs.sum x)

namespace DerivationTree

/-- Every node category of a derivation tree, as a multiset (with repetition). -/
def nodeCategories : {Γ : List Category} → {A : Category} → DerivationTree Γ A → List Category
  | _, _, .leaf A => [A]
  | _, _, .typeRaiseRight C t => (C ⧸ (t.root ⧹ C)) :: t.nodeCategories
  | _, _, .typeRaiseLeft C t => ((C ⧸ t.root) ⧹ C) :: t.nodeCategories
  | _, _, .binary (C := C) t₁ t₂ _ => C :: (t₁.nodeCategories ++ t₂.nodeCategories)

@[simp, grind =]
theorem nodeCategories_leaf (A : Category) : (DerivationTree.leaf A).nodeCategories = [A] := rfl

@[simp, grind =]
theorem nodeCategories_typeRaiseRight (C : Category) {Γ : List Category} {A : Category} (t : DerivationTree Γ A) :
    (DerivationTree.typeRaiseRight C t).nodeCategories = (C ⧸ (A ⧹ C)) :: t.nodeCategories := rfl

@[simp, grind =]
theorem nodeCategories_typeRaiseLeft (C : Category) {Γ : List Category} {A : Category} (t : DerivationTree Γ A) :
    (DerivationTree.typeRaiseLeft C t).nodeCategories = ((C ⧸ A) ⧹ C) :: t.nodeCategories := rfl

@[simp, grind =]
theorem nodeCategories_binary {Γ Δ : List Category} {A B C : Category}
    (t₁ : DerivationTree Γ A) (t₂ : DerivationTree Δ B) (r : Rule A B C) :
    (DerivationTree.binary t₁ t₂ r).nodeCategories = C :: (t₁.nodeCategories ++ t₂.nodeCategories) := rfl

/-- The size measure `size` is the sum of constructor counts over all node
categories.  This is the bridge between the recursive `size` and the occurrence
view used by the trace-graph argument. -/
theorem size_eq_sum_nodeCategories :
    {Γ : List Category} → {A : Category} → (t : DerivationTree Γ A) →
      t.size = (t.nodeCategories.map Category.constructors).sum
  | _, _, .leaf A => by simp
  | _, _, .typeRaiseRight C t => by
      simp [size_typeRaiseRight, nodeCategories_typeRaiseRight, size_eq_sum_nodeCategories t]
  | _, _, .typeRaiseLeft C t => by
      simp [size_typeRaiseLeft, nodeCategories_typeRaiseLeft, size_eq_sum_nodeCategories t]
  | _, _, .binary t₁ t₂ r => by
      simp [size_binary, nodeCategories_binary, size_eq_sum_nodeCategories t₁,
        size_eq_sum_nodeCategories t₂, Nat.add_assoc]

end DerivationTree

/-! ## Node addresses, constructor occurrences, visibility, and trace edges -/

/-- A step in a derivation-tree address. -/
inductive TreeStep where
  | unary
  | left
  | right
  deriving DecidableEq, Repr

/-- A node address in an explicit derivation tree. -/
abbrev NodePath := List TreeStep

namespace DerivationTree

/-- Category at a node address, if the address is valid. -/
def categoryAt? : {Γ : List Category} → {A : Category} → DerivationTree Γ A → NodePath → Option Category
  | _, A, _, [] => some A
  | _, _, .leaf _, _ :: _ => none
  | _, _, .typeRaiseRight _ t, .unary :: p => t.categoryAt? p
  | _, _, .typeRaiseRight _ _, .left :: _ => none
  | _, _, .typeRaiseRight _ _, .right :: _ => none
  | _, _, .typeRaiseLeft _ t, .unary :: p => t.categoryAt? p
  | _, _, .typeRaiseLeft _ _, .left :: _ => none
  | _, _, .typeRaiseLeft _ _, .right :: _ => none
  | _, _, .binary t₁ _ _, .left :: p => t₁.categoryAt? p
  | _, _, .binary _ t₂ _, .right :: p => t₂.categoryAt? p
  | _, _, .binary _ _ _, .unary :: _ => none

@[simp, grind =]
theorem categoryAt?_root {Γ : List Category} {A : Category} (t : DerivationTree Γ A) : t.categoryAt? [] = some A := by
  cases t <;> rfl

/-- A node address is the root address. -/
@[grind =]
def isRootNode (p : NodePath) : Prop := p = []

/-- Whether an address names a leaf node of the tree. -/
def isLeafNode : {Γ : List Category} → {A : Category} → DerivationTree Γ A → NodePath → Prop
  | _, _, .leaf _, [] => True
  | _, _, .leaf _, _ :: _ => False
  | _, _, .typeRaiseRight _ t, .unary :: p => t.isLeafNode p
  | _, _, .typeRaiseRight _ _, [] => False
  | _, _, .typeRaiseRight _ _, .left :: _ => False
  | _, _, .typeRaiseRight _ _, .right :: _ => False
  | _, _, .typeRaiseLeft _ t, .unary :: p => t.isLeafNode p
  | _, _, .typeRaiseLeft _ _, [] => False
  | _, _, .typeRaiseLeft _ _, .left :: _ => False
  | _, _, .typeRaiseLeft _ _, .right :: _ => False
  | _, _, .binary t₁ _ _, .left :: p => t₁.isLeafNode p
  | _, _, .binary _ t₂ _, .right :: p => t₂.isLeafNode p
  | _, _, .binary _ _ _, [] => False
  | _, _, .binary _ _ _, .unary :: _ => False

/-- Principal constructor occurrences of binary rules, addressed by node and
category position.  Unary type-raising constructors are intentionally not
principal/visible here, matching the paper. -/
inductive PrincipalConstructor : {Γ : List Category} → {A : Category} →
    DerivationTree Γ A → NodePath → CategoryPath → Prop where
  | appRight_left {Γ Δ : List Category} {C B : Category}
      (t₁ : DerivationTree Γ (C ⧸ B)) (t₂ : DerivationTree Δ B) :
      PrincipalConstructor (DerivationTree.binary t₁ t₂ Rule.appRight) [.left] []
  | appLeft_right {Γ Δ : List Category} {A C : Category}
      (t₁ : DerivationTree Γ A) (t₂ : DerivationTree Δ (A ⧹ C)) :
      PrincipalConstructor (DerivationTree.binary t₁ t₂ Rule.appLeft) [.right] []
  | compRight_left {Γ Δ : List Category} {C B A : Category}
      (t₁ : DerivationTree Γ (C ⧸ B)) (t₂ : DerivationTree Δ (B ⧸ A)) :
      PrincipalConstructor (DerivationTree.binary t₁ t₂ Rule.compRight) [.left] []
  | compRight_right {Γ Δ : List Category} {C B A : Category}
      (t₁ : DerivationTree Γ (C ⧸ B)) (t₂ : DerivationTree Δ (B ⧸ A)) :
      PrincipalConstructor (DerivationTree.binary t₁ t₂ Rule.compRight) [.right] []
  | compRight_out {Γ Δ : List Category} {C B A : Category}
      (t₁ : DerivationTree Γ (C ⧸ B)) (t₂ : DerivationTree Δ (B ⧸ A)) :
      PrincipalConstructor (DerivationTree.binary t₁ t₂ Rule.compRight) [] []
  | compLeft_left {Γ Δ : List Category} {A B C : Category}
      (t₁ : DerivationTree Γ (A ⧹ B)) (t₂ : DerivationTree Δ (B ⧹ C)) :
      PrincipalConstructor (DerivationTree.binary t₁ t₂ Rule.compLeft) [.left] []
  | compLeft_right {Γ Δ : List Category} {A B C : Category}
      (t₁ : DerivationTree Γ (A ⧹ B)) (t₂ : DerivationTree Δ (B ⧹ C)) :
      PrincipalConstructor (DerivationTree.binary t₁ t₂ Rule.compLeft) [.right] []
  | compLeft_out {Γ Δ : List Category} {A B C : Category}
      (t₁ : DerivationTree Γ (A ⧹ B)) (t₂ : DerivationTree Δ (B ⧹ C)) :
      PrincipalConstructor (DerivationTree.binary t₁ t₂ Rule.compLeft) [] []
  | crossedRight_left {Γ Δ : List Category} {C B A : Category}
      (t₁ : DerivationTree Γ (C ⧸ B)) (t₂ : DerivationTree Δ (A ⧹ B)) :
      PrincipalConstructor (DerivationTree.binary t₁ t₂ Rule.crossedRight) [.left] []
  | crossedRight_right {Γ Δ : List Category} {C B A : Category}
      (t₁ : DerivationTree Γ (C ⧸ B)) (t₂ : DerivationTree Δ (A ⧹ B)) :
      PrincipalConstructor (DerivationTree.binary t₁ t₂ Rule.crossedRight) [.right] []
  | crossedRight_out {Γ Δ : List Category} {C B A : Category}
      (t₁ : DerivationTree Γ (C ⧸ B)) (t₂ : DerivationTree Δ (A ⧹ B)) :
      PrincipalConstructor (DerivationTree.binary t₁ t₂ Rule.crossedRight) [] []
  | crossedLeft_left {Γ Δ : List Category} {B A C : Category}
      (t₁ : DerivationTree Γ (B ⧸ A)) (t₂ : DerivationTree Δ (B ⧹ C)) :
      PrincipalConstructor (DerivationTree.binary t₁ t₂ Rule.crossedLeft) [.left] []
  | crossedLeft_right {Γ Δ : List Category} {B A C : Category}
      (t₁ : DerivationTree Γ (B ⧸ A)) (t₂ : DerivationTree Δ (B ⧹ C)) :
      PrincipalConstructor (DerivationTree.binary t₁ t₂ Rule.crossedLeft) [.right] []
  | crossedLeft_out {Γ Δ : List Category} {B A C : Category}
      (t₁ : DerivationTree Γ (B ⧸ A)) (t₂ : DerivationTree Δ (B ⧹ C)) :
      PrincipalConstructor (DerivationTree.binary t₁ t₂ Rule.crossedLeft) [] []
  | underUnaryRight {Γ : List Category} {A : Category} (C : Category) {t : DerivationTree Γ A} {p : NodePath} {cpos : CategoryPath}
      (h : PrincipalConstructor t p cpos) :
      PrincipalConstructor (DerivationTree.typeRaiseRight C t) (.unary :: p) cpos
  | underUnaryLeft {Γ : List Category} {A : Category} (C : Category) {t : DerivationTree Γ A} {p : NodePath} {cpos : CategoryPath}
      (h : PrincipalConstructor t p cpos) :
      PrincipalConstructor (DerivationTree.typeRaiseLeft C t) (.unary :: p) cpos
  | underBinaryLeft {Γ Δ : List Category} {A B C : Category}
      {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ B} (r : Rule A B C) {p : NodePath} {cpos : CategoryPath}
      (h : PrincipalConstructor t₁ p cpos) :
      PrincipalConstructor (DerivationTree.binary t₁ t₂ r) (.left :: p) cpos
  | underBinaryRight {Γ Δ : List Category} {A B C : Category}
      {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ B} (r : Rule A B C) {p : NodePath} {cpos : CategoryPath}
      (h : PrincipalConstructor t₂ p cpos) :
      PrincipalConstructor (DerivationTree.binary t₁ t₂ r) (.right :: p) cpos

/-- Constructor occurrences that are part of the *skeleton introduced by a
unary type-raising rule*.

For forward type raising `A ↦ C/(A\C)`, the skeleton constructors introduced at
the output node are the outer `/` at path `[]` and the inner `\` at path
`[true]`.  For backward type raising `A ↦ (C/A)\C`, they are the outer `\` at
path `[]` and the inner `/` at path `[false]`.

These constructors are intentionally **not** `PrincipalConstructor`s in the
paper's visibility definition: making them visible would give no finite visible
budget before the band-contraction argument.  They are also not metavariable
copy endpoints of the type-raising trace edges.  Consequently, node-local atom
replacement must treat them as protected unless a separate argument shows that
the whole component can be contracted by a band. -/
inductive UnarySkeletonConstructor : {Γ : List Category} → {A : Category} →
    DerivationTree Γ A → NodePath → CategoryPath → Prop where
  | trRight_outer {Γ : List Category} {A C : Category}
      (t : DerivationTree Γ A) :
      UnarySkeletonConstructor (DerivationTree.typeRaiseRight C t) [] []
  | trRight_inner {Γ : List Category} {A C : Category}
      (t : DerivationTree Γ A) :
      UnarySkeletonConstructor (DerivationTree.typeRaiseRight C t) [] [true]
  | trLeft_outer {Γ : List Category} {A C : Category}
      (t : DerivationTree Γ A) :
      UnarySkeletonConstructor (DerivationTree.typeRaiseLeft C t) [] []
  | trLeft_inner {Γ : List Category} {A C : Category}
      (t : DerivationTree Γ A) :
      UnarySkeletonConstructor (DerivationTree.typeRaiseLeft C t) [] [false]
  | underUnaryRight {Γ : List Category} {A : Category} (C : Category)
      {t : DerivationTree Γ A} {p : NodePath} {cpos : CategoryPath}
      (h : UnarySkeletonConstructor t p cpos) :
      UnarySkeletonConstructor (DerivationTree.typeRaiseRight C t) (.unary :: p) cpos
  | underUnaryLeft {Γ : List Category} {A : Category} (C : Category)
      {t : DerivationTree Γ A} {p : NodePath} {cpos : CategoryPath}
      (h : UnarySkeletonConstructor t p cpos) :
      UnarySkeletonConstructor (DerivationTree.typeRaiseLeft C t) (.unary :: p) cpos
  | underBinaryLeft {Γ Δ : List Category} {A B C : Category}
      {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ B} (r : Rule A B C)
      {p : NodePath} {cpos : CategoryPath}
      (h : UnarySkeletonConstructor t₁ p cpos) :
      UnarySkeletonConstructor (DerivationTree.binary t₁ t₂ r) (.left :: p) cpos
  | underBinaryRight {Γ Δ : List Category} {A B C : Category}
      {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ B} (r : Rule A B C)
      {p : NodePath} {cpos : CategoryPath}
      (h : UnarySkeletonConstructor t₂ p cpos) :
      UnarySkeletonConstructor (DerivationTree.binary t₁ t₂ r) (.right :: p) cpos

/-- Node-addressed constructor occurrence. -/
structure CategoryOccurrence {Γ : List Category} {A : Category} (t : DerivationTree Γ A) where
  nodePath : NodePath
  nodeCategory : Category
  nodeAt : t.categoryAt? nodePath = some nodeCategory
  categoryPath : CategoryPath
  isConstructor : ∃ X Y, nodeCategory.subcategoryAt? categoryPath = some (X ⧸ Y) ∨ nodeCategory.subcategoryAt? categoryPath = some (X ⧹ Y)

namespace CategoryOccurrence

variable {Γ : List Category} {A : Category} {t : DerivationTree Γ A}

/-- Node-addressed visibility: root occurrence, leaf occurrence, or binary-rule
principal constructor. -/
def Visible (o : CategoryOccurrence t) : Prop :=
  DerivationTree.isRootNode o.nodePath ∨
    t.isLeafNode o.nodePath ∨
      DerivationTree.PrincipalConstructor t o.nodePath o.categoryPath

/-- Node-addressed invisibility. -/
def Invisible (o : CategoryOccurrence t) : Prop := ¬ o.Visible

/-- Protected unary-skeleton occurrence alias at the occurrence level.  This is
the formal marker for the boundary-free atom-replacement blocker: replacing
such a node-local subcategory by an atom may destroy the local type-raising
rule shape. -/
def ProtectedUnarySkeleton (o : CategoryOccurrence t) : Prop :=
  DerivationTree.UnarySkeletonConstructor t o.nodePath o.categoryPath

@[grind =]
theorem visible_iff (o : CategoryOccurrence t) :
    o.Visible ↔ DerivationTree.isRootNode o.nodePath ∨ t.isLeafNode o.nodePath ∨
      DerivationTree.PrincipalConstructor t o.nodePath o.categoryPath := Iff.rfl

@[grind =]
theorem invisible_iff (o : CategoryOccurrence t) : o.Invisible ↔ ¬ o.Visible := Iff.rfl

/-- Node occurrences are proof-irrelevant once their data fields agree. -/
theorem eq_of_data {o₁ o₂ : CategoryOccurrence t}
    (hnode : o₁.nodePath = o₂.nodePath) (hcat : o₁.nodeCategory = o₂.nodeCategory)
    (hpos : o₁.categoryPath = o₂.categoryPath) : o₁ = o₂ := by
  cases o₁ with
  | mk n₁ c₁ at₁ p₁ is₁ =>
  cases o₂ with
  | mk n₂ c₂ at₂ p₂ is₂ =>
      simp only at hnode hcat hpos
      subst n₂
      subst c₂
      subst p₂
      simp

/-- Lift an occurrence under a forward type-raising context. -/
def underUnaryRight (C : Category) {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (o : CategoryOccurrence t) : CategoryOccurrence (DerivationTree.typeRaiseRight C t) where
  nodePath := .unary :: o.nodePath
  nodeCategory := o.nodeCategory
  nodeAt := by simp [DerivationTree.categoryAt?, o.nodeAt]
  categoryPath := o.categoryPath
  isConstructor := o.isConstructor

/-- Lift an occurrence under a backward type-raising context. -/
def underUnaryLeft (C : Category) {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (o : CategoryOccurrence t) : CategoryOccurrence (DerivationTree.typeRaiseLeft C t) where
  nodePath := .unary :: o.nodePath
  nodeCategory := o.nodeCategory
  nodeAt := by simp [DerivationTree.categoryAt?, o.nodeAt]
  categoryPath := o.categoryPath
  isConstructor := o.isConstructor

/-- Lift an occurrence under the left premise of a binary context. -/
def underBinaryLeft {Γ Δ : List Category} {A B C : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ B} (r : Rule A B C)
    (o : CategoryOccurrence t₁) : CategoryOccurrence (DerivationTree.binary t₁ t₂ r) where
  nodePath := .left :: o.nodePath
  nodeCategory := o.nodeCategory
  nodeAt := by simp [DerivationTree.categoryAt?, o.nodeAt]
  categoryPath := o.categoryPath
  isConstructor := o.isConstructor

/-- Lift an occurrence under the right premise of a binary context. -/
def underBinaryRight {Γ Δ : List Category} {A B C : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ B} (r : Rule A B C)
    (o : CategoryOccurrence t₂) : CategoryOccurrence (DerivationTree.binary t₁ t₂ r) where
  nodePath := .right :: o.nodePath
  nodeCategory := o.nodeCategory
  nodeAt := by simp [DerivationTree.categoryAt?, o.nodeAt]
  categoryPath := o.categoryPath
  isConstructor := o.isConstructor

end CategoryOccurrence

/-- A valid derivation-tree node address together with its category.  This is
the node-level half of finite occurrence enumeration. -/
structure TreeNode {Γ : List Category} {A : Category} (t : DerivationTree Γ A) where
  nodePath : NodePath
  nodeCategory : Category
  nodeAt : t.categoryAt? nodePath = some nodeCategory

namespace TreeNode

/-- Lift a node entry under a forward type-raising context. -/
def underUnaryRight (C : Category) {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (e : TreeNode t) : TreeNode (DerivationTree.typeRaiseRight C t) where
  nodePath := .unary :: e.nodePath
  nodeCategory := e.nodeCategory
  nodeAt := by simp [DerivationTree.categoryAt?, e.nodeAt]

@[simp, grind =]
theorem underUnaryRight_nodeCat (C : Category) {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (e : TreeNode t) : (underUnaryRight C e).nodeCategory = e.nodeCategory := rfl

/-- Lift a node entry under a backward type-raising context. -/
def underUnaryLeft (C : Category) {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (e : TreeNode t) : TreeNode (DerivationTree.typeRaiseLeft C t) where
  nodePath := .unary :: e.nodePath
  nodeCategory := e.nodeCategory
  nodeAt := by simp [DerivationTree.categoryAt?, e.nodeAt]

@[simp, grind =]
theorem underUnaryLeft_nodeCat (C : Category) {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (e : TreeNode t) : (underUnaryLeft C e).nodeCategory = e.nodeCategory := rfl

/-- Lift a node entry under the left premise of a binary context. -/
def underBinaryLeft {Γ Δ : List Category} {A B C : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ B} (r : Rule A B C)
    (e : TreeNode t₁) : TreeNode (DerivationTree.binary t₁ t₂ r) where
  nodePath := .left :: e.nodePath
  nodeCategory := e.nodeCategory
  nodeAt := by simp [DerivationTree.categoryAt?, e.nodeAt]

@[simp, grind =]
theorem underBinaryLeft_nodeCat {Γ Δ : List Category} {A B C : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ B} (r : Rule A B C)
    (e : TreeNode t₁) :
    (@underBinaryLeft Γ Δ A B C t₁ t₂ r e).nodeCategory = e.nodeCategory := rfl

/-- Lift a node entry under the right premise of a binary context. -/
def underBinaryRight {Γ Δ : List Category} {A B C : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ B} (r : Rule A B C)
    (e : TreeNode t₂) : TreeNode (DerivationTree.binary t₁ t₂ r) where
  nodePath := .right :: e.nodePath
  nodeCategory := e.nodeCategory
  nodeAt := by simp [DerivationTree.categoryAt?, e.nodeAt]

@[simp, grind =]
theorem underBinaryRight_nodeCat {Γ Δ : List Category} {A B C : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ B} (r : Rule A B C)
    (e : TreeNode t₂) :
    (@underBinaryRight Γ Δ A B C t₁ t₂ r e).nodeCategory = e.nodeCategory := rfl

end TreeNode

/-- Executable finite enumeration of all valid node addresses/categories in a
derivation tree. -/
def nodeEntries : {Γ : List Category} → {A : Category} → (t : DerivationTree Γ A) → List (TreeNode t)
  | _, A, .leaf _ => [{ nodePath := [], nodeCategory := A, nodeAt := rfl }]
  | _, _, .typeRaiseRight C t =>
      { nodePath := [], nodeCategory := C ⧸ (t.root ⧹ C), nodeAt := rfl } ::
        t.nodeEntries.map (TreeNode.underUnaryRight C)
  | _, _, .typeRaiseLeft C t =>
      { nodePath := [], nodeCategory := (C ⧸ t.root) ⧹ C, nodeAt := rfl } ::
        t.nodeEntries.map (TreeNode.underUnaryLeft C)
  | _, _, .binary (C := C) t₁ t₂ r =>
      { nodePath := [], nodeCategory := C, nodeAt := rfl } ::
        (t₁.nodeEntries.map (TreeNode.underBinaryLeft r) ++
          t₂.nodeEntries.map (TreeNode.underBinaryRight r))

/-- Turn one node entry into all constructor occurrences at that node. -/
def occurrencesAtEntry {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (e : TreeNode t) : List (CategoryOccurrence t) :=
  e.nodeCategory.constructorPositions.attach.map fun p =>
    { nodePath := e.nodePath
      nodeCategory := e.nodeCategory
      nodeAt := e.nodeAt
      categoryPath := p.1
      isConstructor := Category.isConstructor_of_mem_constructorPositions e.nodeCategory p.2 }

/-- Executable finite enumeration of all constructor occurrences of a
derivation tree.  This is the finite set over which the later visible-bound,
trace-degree, and invisible-piece counting lemmas quantify. -/
def occurrences {Γ : List Category} {A : Category} (t : DerivationTree Γ A) : List (CategoryOccurrence t) :=
  t.nodeEntries.flatMap occurrencesAtEntry

/-- Completeness of `nodeEntries` at the data level: every valid node address is
represented by some listed entry with the same address and category. -/
theorem nodeEntries_complete :
    {Γ : List Category} → {A : Category} → (t : DerivationTree Γ A) → (p : NodePath) → (C : Category) →
      t.categoryAt? p = some C →
        ∃ e : TreeNode t, e ∈ t.nodeEntries ∧ e.nodePath = p ∧ e.nodeCategory = C
  | _, _, .leaf A, p, C, h => by
      cases p with
      | nil =>
          simp only [categoryAt?_root, Option.some.injEq] at h
          subst h
          exact ⟨{ nodePath := [], nodeCategory := A, nodeAt := rfl }, by simp [nodeEntries]⟩
      | cons step rest =>
          simp [categoryAt?] at h
  | _, _, .typeRaiseRight C₀ t, p, C, h => by
      cases p with
      | nil =>
          simp only [categoryAt?_root, Option.some.injEq] at h
          subst h
          exact ⟨{ nodePath := [], nodeCategory := C₀ ⧸ (t.root ⧹ C₀), nodeAt := rfl },
            by simp [nodeEntries]⟩
      | cons step rest =>
          cases step with
          | unary =>
              simp only [categoryAt?] at h
              obtain ⟨e, heMem, hePos, heCat⟩ := nodeEntries_complete t rest C h
              refine ⟨TreeNode.underUnaryRight C₀ e, ?_, ?_, ?_⟩
              · exact List.mem_cons_of_mem _
                  (List.mem_map.mpr ⟨e, heMem, rfl⟩)
              · simp [TreeNode.underUnaryRight, hePos]
              · exact heCat
          | left => simp [categoryAt?] at h
          | right => simp [categoryAt?] at h
  | _, _, .typeRaiseLeft C₀ t, p, C, h => by
      cases p with
      | nil =>
          simp only [categoryAt?_root, Option.some.injEq] at h
          subst h
          exact ⟨{ nodePath := [], nodeCategory := (C₀ ⧸ t.root) ⧹ C₀, nodeAt := rfl },
            by simp [nodeEntries]⟩
      | cons step rest =>
          cases step with
          | unary =>
              simp only [categoryAt?] at h
              obtain ⟨e, heMem, hePos, heCat⟩ := nodeEntries_complete t rest C h
              refine ⟨TreeNode.underUnaryLeft C₀ e, ?_, ?_, ?_⟩
              · exact List.mem_cons_of_mem _
                  (List.mem_map.mpr ⟨e, heMem, rfl⟩)
              · simp [TreeNode.underUnaryLeft, hePos]
              · exact heCat
          | left => simp [categoryAt?] at h
          | right => simp [categoryAt?] at h
  | _, _, .binary (C := C₀) t₁ t₂ r, p, C, h => by
      cases p with
      | nil =>
          simp only [categoryAt?_root, Option.some.injEq] at h
          subst h
          exact ⟨{ nodePath := [], nodeCategory := C₀, nodeAt := rfl }, by simp [nodeEntries]⟩
      | cons step rest =>
          cases step with
          | unary => simp [categoryAt?] at h
          | left =>
              simp only [categoryAt?] at h
              obtain ⟨e, heMem, hePos, heCat⟩ := nodeEntries_complete t₁ rest C h
              refine ⟨TreeNode.underBinaryLeft r e, ?_, ?_, ?_⟩
              · exact List.mem_cons_of_mem _
                  (List.mem_append_left _
                    (List.mem_map.mpr ⟨e, heMem, rfl⟩))
              · simp [TreeNode.underBinaryLeft, hePos]
              · exact heCat
          | right =>
              simp only [categoryAt?] at h
              obtain ⟨e, heMem, hePos, heCat⟩ := nodeEntries_complete t₂ rest C h
              refine ⟨TreeNode.underBinaryRight r e, ?_, ?_, ?_⟩
              · exact List.mem_cons_of_mem _
                  (List.mem_append_right _
                    (List.mem_map.mpr ⟨e, heMem, rfl⟩))
              · simp [TreeNode.underBinaryRight, hePos]
              · exact heCat

/-- Every occurrence is represented in the executable occurrence enumeration,
up to proof-irrelevant fields.  The listed occurrence has the same node
address, node category, and category position as the input occurrence. -/
theorem occurrence_data_mem_occurrences {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (o : CategoryOccurrence t) :
    ∃ o' : CategoryOccurrence t,
      o' ∈ t.occurrences ∧ o'.nodePath = o.nodePath ∧
        o'.nodeCategory = o.nodeCategory ∧ o'.categoryPath = o.categoryPath := by
  obtain ⟨e, heMem, hePos, heCat⟩ :=
    nodeEntries_complete t o.nodePath o.nodeCategory o.nodeAt
  have hposMem : o.categoryPath ∈ e.nodeCategory.constructorPositions := by
    simpa [heCat] using
      (Category.mem_constructorPositions_of_isConstructor o.nodeCategory o.isConstructor)
  let p : { p : CategoryPath // p ∈ e.nodeCategory.constructorPositions } := ⟨o.categoryPath, hposMem⟩
  let o' : CategoryOccurrence t :=
    { nodePath := e.nodePath
      nodeCategory := e.nodeCategory
      nodeAt := e.nodeAt
      categoryPath := p.1
      isConstructor := Category.isConstructor_of_mem_constructorPositions e.nodeCategory p.2 }
  refine ⟨o', ?_, ?_, ?_, ?_⟩
  · unfold occurrences occurrencesAtEntry o' p
    refine List.mem_flatMap.mpr ⟨e, heMem, ?_⟩
    exact List.mem_map_of_mem (by simp)
  · exact hePos
  · exact heCat
  · rfl

/-- Completeness of the executable occurrence enumeration. -/
theorem occurrence_mem_occurrences {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (o : CategoryOccurrence t) : o ∈ t.occurrences := by
  obtain ⟨o', hmem, hnode, hcat, hpos⟩ := occurrence_data_mem_occurrences o
  have hEq : o' = o := CategoryOccurrence.eq_of_data hnode hcat hpos
  rwa [hEq] at hmem

/-- Constructor occurrences of a fixed derivation tree form an explicitly
finite list. -/
theorem finite_occurrences {Γ : List Category} {A : Category} (t : DerivationTree Γ A) :
    ∃ xs : List (CategoryOccurrence t), ∀ o : CategoryOccurrence t, o ∈ xs :=
  ⟨t.occurrences, occurrence_mem_occurrences⟩

/-- Occurrences listed at one node are exactly the slash constructors of that
node category. -/
theorem length_occurrencesAtEntry {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (e : TreeNode t) : (occurrencesAtEntry e).length = e.nodeCategory.constructors := by
  simp [occurrencesAtEntry, Category.length_constructorPositions]

/-- Constructor sums are unchanged when node entries are lifted under forward
type raising. -/
theorem sum_nodeEntries_underUnaryRight {Γ : List Category} {A C : Category} (t : DerivationTree Γ A) :
    (List.map
        ((fun e : TreeNode (DerivationTree.typeRaiseRight C t) => e.nodeCategory.constructors) ∘
          TreeNode.underUnaryRight C) t.nodeEntries).sum =
      (List.map (fun e : TreeNode t => e.nodeCategory.constructors) t.nodeEntries).sum := by
  simp [Function.comp_def, TreeNode.underUnaryRight]

/-- Constructor sums are unchanged when node entries are lifted under backward
type raising. -/
theorem sum_nodeEntries_underUnaryLeft {Γ : List Category} {A C : Category} (t : DerivationTree Γ A) :
    (List.map
        ((fun e : TreeNode (DerivationTree.typeRaiseLeft C t) => e.nodeCategory.constructors) ∘
          TreeNode.underUnaryLeft C) t.nodeEntries).sum =
      (List.map (fun e : TreeNode t => e.nodeCategory.constructors) t.nodeEntries).sum := by
  simp [Function.comp_def, TreeNode.underUnaryLeft]

/-- Constructor sums are unchanged when node entries are lifted under a binary
left premise. -/
theorem sum_nodeEntries_underBinaryLeft {Γ Δ : List Category} {A B C : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ B} (r : Rule A B C) :
    (List.map
        ((fun e : TreeNode (DerivationTree.binary t₁ t₂ r) => e.nodeCategory.constructors) ∘
          TreeNode.underBinaryLeft r) t₁.nodeEntries).sum =
      (List.map (fun e : TreeNode t₁ => e.nodeCategory.constructors) t₁.nodeEntries).sum := by
  simp [Function.comp_def, TreeNode.underBinaryLeft]

/-- Constructor sums are unchanged when node entries are lifted under a binary
right premise. -/
theorem sum_nodeEntries_underBinaryRight {Γ Δ : List Category} {A B C : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ B} (r : Rule A B C) :
    (List.map
        ((fun e : TreeNode (DerivationTree.binary t₁ t₂ r) => e.nodeCategory.constructors) ∘
          TreeNode.underBinaryRight r) t₂.nodeEntries).sum =
      (List.map (fun e : TreeNode t₂ => e.nodeCategory.constructors) t₂.nodeEntries).sum := by
  simp [Function.comp_def, TreeNode.underBinaryRight]

/-- The executable node-entry enumeration has the same constructor-count sum as
`nodeCategories`. -/
theorem sum_nodeEntries_constructors :
    {Γ : List Category} → {A : Category} → (t : DerivationTree Γ A) →
      ((t.nodeEntries.map fun e => e.nodeCategory.constructors).sum =
        (t.nodeCategories.map Category.constructors).sum)
  | _, _, .leaf A => by simp [nodeEntries, nodeCategories]
  | _, _, .typeRaiseRight C t => by
      simp [nodeEntries, nodeCategories, sum_nodeEntries_underUnaryRight t,
        sum_nodeEntries_constructors t]
  | _, _, .typeRaiseLeft C t => by
      simp [nodeEntries, nodeCategories, sum_nodeEntries_underUnaryLeft t,
        sum_nodeEntries_constructors t]
  | _, _, .binary t₁ t₂ r => by
      simp [nodeEntries, nodeCategories, sum_nodeEntries_underBinaryLeft r,
        sum_nodeEntries_underBinaryRight r, sum_nodeEntries_constructors t₁,
        sum_nodeEntries_constructors t₂]

/-- The finite occurrence enumeration has cardinality exactly `DerivationTree.size`, the
paper's total constructor-occurrence measure. -/
theorem length_occurrences_eq_size {Γ : List Category} {A : Category} (t : DerivationTree Γ A) :
    t.occurrences.length = t.size := by
  unfold occurrences
  rw [List.length_flatMap]
  simp only [length_occurrencesAtEntry]
  rw [sum_nodeEntries_constructors, ← DerivationTree.size_eq_sum_nodeCategories t]

/-- Any listed node category contributes at most the total size measure. -/
theorem constructors_le_size_of_mem_nodeCategories {Γ : List Category} {A B : Category}
    {t : DerivationTree Γ A} (hB : B ∈ t.nodeCategories) : B.constructors ≤ t.size := by
  rw [DerivationTree.size_eq_sum_nodeCategories t]
  exact Nat.le_sum_of_mem_list (by
    exact List.mem_map.mpr ⟨B, hB, rfl⟩)

/-- Consequently, every node category depth is bounded by the tree's size. -/
theorem depth_le_size_of_mem_nodeCategories {Γ : List Category} {A B : Category}
    {t : DerivationTree Γ A} (hB : B ∈ t.nodeCategories) : B.depth ≤ t.size :=
  le_trans (Category.depth_le_constructors B) (constructors_le_size_of_mem_nodeCategories hB)

end DerivationTree

/-- Compatibility abbreviation used by the existing band/depth interfaces.  It
is now node-addressed; the earlier category-only occurrence API has been
replaced by `DerivationTree.CategoryOccurrence`. -/
abbrev Occurrence {Γ : List Category} {A : Category} (t : DerivationTree Γ A) := DerivationTree.CategoryOccurrence t

namespace Occurrence

variable {Γ : List Category} {A : Category} {t : DerivationTree Γ A}

/-- Node-addressed visibility alias. -/
def Visible (o : Occurrence t) : Prop := DerivationTree.CategoryOccurrence.Visible o

/-- Node-addressed invisibility alias. -/
def Invisible (o : Occurrence t) : Prop := DerivationTree.CategoryOccurrence.Invisible o

/-- Occurrence-level alias for constructors introduced as the skeleton of a
unary type-raising rule. -/
def ProtectedUnarySkeleton (o : Occurrence t) : Prop :=
  DerivationTree.CategoryOccurrence.ProtectedUnarySkeleton o

@[grind =]
theorem visible_iff (o : Occurrence t) : o.Visible ↔ DerivationTree.CategoryOccurrence.Visible o := Iff.rfl

@[grind =]
theorem invisible_iff (o : Occurrence t) : o.Invisible ↔ DerivationTree.CategoryOccurrence.Invisible o := Iff.rfl

@[grind =]
theorem protectedUnarySkeleton_iff (o : Occurrence t) :
    o.ProtectedUnarySkeleton ↔ DerivationTree.CategoryOccurrence.ProtectedUnarySkeleton o := Iff.rfl

/-- Proof-irrelevant key of an occurrence.  The category at a valid node is
unique, so the node path together with the category path identifies an
occurrence; the proof fields in `CategoryOccurrence` carry no extra data. -/
structure Key where
  nodePath : NodePath
  categoryPath : CategoryPath
  deriving DecidableEq, Repr

/-- The finite key attached to an occurrence. -/
def key (o : Occurrence t) : Key :=
  { nodePath := o.nodePath, categoryPath := o.categoryPath }

@[simp, grind =]
theorem key_nodePath (o : Occurrence t) : o.key.nodePath = o.nodePath := rfl

@[simp, grind =]
theorem key_categoryPath (o : Occurrence t) : o.key.categoryPath = o.categoryPath := rfl

/-- Occurrences with the same key are equal.  This is the uniqueness fact needed
when a finite list of trace-neighbour keys is later turned into a finite list of
neighbour occurrences. -/
theorem eq_of_key_eq {o₁ o₂ : Occurrence t} (h : o₁.key = o₂.key) : o₁ = o₂ := by
  have hnode : o₁.nodePath = o₂.nodePath := by
    exact congrArg Key.nodePath h
  have hpos : o₁.categoryPath = o₂.categoryPath := by
    exact congrArg Key.categoryPath h
  have hcat : o₁.nodeCategory = o₂.nodeCategory := by
    have h₁ := o₁.nodeAt
    have h₂ := o₂.nodeAt
    rw [hnode, h₂] at h₁
    simpa using h₁.symm
  exact DerivationTree.CategoryOccurrence.eq_of_data hnode hcat hpos

end Occurrence

/-! ## Rule-local metavariable-copy trace graph -/

/-- A directed half-edge of the trace graph.  Each constructor links two copies
of the same schematic metavariable inside one local rule instance; context
constructors transport those local links through surrounding derivation
contexts.  The public `TraceEdge` below is the undirected version. -/
inductive LocalTraceEdge : {Γ : List Category} → {A : Category} → {t : DerivationTree Γ A} →
    Occurrence t → Occurrence t → Prop where
  /- Type raising, forward: `A ↦ C/(A\C)`. -/
  | trRight_A {Γ : List Category} {A C : Category} {t : DerivationTree Γ A}
      {o₁ o₂ : Occurrence (DerivationTree.typeRaiseRight C t)} {p : CategoryPath}
      (h₁n : o₁.nodePath = [.unary]) (h₁p : o₁.categoryPath = p)
      (h₂n : o₂.nodePath = []) (h₂p : o₂.categoryPath = true :: false :: p) :
      LocalTraceEdge o₁ o₂
  | trRight_C {Γ : List Category} {A C : Category} {t : DerivationTree Γ A}
      {o₁ o₂ : Occurrence (DerivationTree.typeRaiseRight C t)} {p : CategoryPath}
      (h₁n : o₁.nodePath = []) (h₁p : o₁.categoryPath = false :: p)
      (h₂n : o₂.nodePath = []) (h₂p : o₂.categoryPath = true :: true :: p) :
      LocalTraceEdge o₁ o₂
  /- Type raising, backward: `A ↦ (C/A)\C`. -/
  | trLeft_A {Γ : List Category} {A C : Category} {t : DerivationTree Γ A}
      {o₁ o₂ : Occurrence (DerivationTree.typeRaiseLeft C t)} {p : CategoryPath}
      (h₁n : o₁.nodePath = [.unary]) (h₁p : o₁.categoryPath = p)
      (h₂n : o₂.nodePath = []) (h₂p : o₂.categoryPath = false :: true :: p) :
      LocalTraceEdge o₁ o₂
  | trLeft_C {Γ : List Category} {A C : Category} {t : DerivationTree Γ A}
      {o₁ o₂ : Occurrence (DerivationTree.typeRaiseLeft C t)} {p : CategoryPath}
      (h₁n : o₁.nodePath = []) (h₁p : o₁.categoryPath = false :: false :: p)
      (h₂n : o₂.nodePath = []) (h₂p : o₂.categoryPath = true :: p) :
      LocalTraceEdge o₁ o₂
  /- Application rules. -/
  | appRight_C {Γ Δ : List Category} {C B : Category}
      {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ B}
      {o₁ o₂ : Occurrence (DerivationTree.binary t₁ t₂ Rule.appRight)} {p : CategoryPath}
      (h₁n : o₁.nodePath = [.left]) (h₁p : o₁.categoryPath = false :: p)
      (h₂n : o₂.nodePath = []) (h₂p : o₂.categoryPath = p) :
      LocalTraceEdge o₁ o₂
  | appRight_B {Γ Δ : List Category} {C B : Category}
      {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ B}
      {o₁ o₂ : Occurrence (DerivationTree.binary t₁ t₂ Rule.appRight)} {p : CategoryPath}
      (h₁n : o₁.nodePath = [.left]) (h₁p : o₁.categoryPath = true :: p)
      (h₂n : o₂.nodePath = [.right]) (h₂p : o₂.categoryPath = p) :
      LocalTraceEdge o₁ o₂
  | appLeft_A {Γ Δ : List Category} {A C : Category}
      {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ (A ⧹ C)}
      {o₁ o₂ : Occurrence (DerivationTree.binary t₁ t₂ Rule.appLeft)} {p : CategoryPath}
      (h₁n : o₁.nodePath = [.left]) (h₁p : o₁.categoryPath = p)
      (h₂n : o₂.nodePath = [.right]) (h₂p : o₂.categoryPath = false :: p) :
      LocalTraceEdge o₁ o₂
  | appLeft_C {Γ Δ : List Category} {A C : Category}
      {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ (A ⧹ C)}
      {o₁ o₂ : Occurrence (DerivationTree.binary t₁ t₂ Rule.appLeft)} {p : CategoryPath}
      (h₁n : o₁.nodePath = [.right]) (h₁p : o₁.categoryPath = true :: p)
      (h₂n : o₂.nodePath = []) (h₂p : o₂.categoryPath = p) :
      LocalTraceEdge o₁ o₂
  /- Forward composition `C/B, B/A ↦ C/A`. -/
  | compRight_C {Γ Δ : List Category} {C B A : Category}
      {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (B ⧸ A)}
      {o₁ o₂ : Occurrence (DerivationTree.binary t₁ t₂ Rule.compRight)} {p : CategoryPath}
      (h₁n : o₁.nodePath = [.left]) (h₁p : o₁.categoryPath = false :: p)
      (h₂n : o₂.nodePath = []) (h₂p : o₂.categoryPath = false :: p) :
      LocalTraceEdge o₁ o₂
  | compRight_B {Γ Δ : List Category} {C B A : Category}
      {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (B ⧸ A)}
      {o₁ o₂ : Occurrence (DerivationTree.binary t₁ t₂ Rule.compRight)} {p : CategoryPath}
      (h₁n : o₁.nodePath = [.left]) (h₁p : o₁.categoryPath = true :: p)
      (h₂n : o₂.nodePath = [.right]) (h₂p : o₂.categoryPath = false :: p) :
      LocalTraceEdge o₁ o₂
  | compRight_A {Γ Δ : List Category} {C B A : Category}
      {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (B ⧸ A)}
      {o₁ o₂ : Occurrence (DerivationTree.binary t₁ t₂ Rule.compRight)} {p : CategoryPath}
      (h₁n : o₁.nodePath = [.right]) (h₁p : o₁.categoryPath = true :: p)
      (h₂n : o₂.nodePath = []) (h₂p : o₂.categoryPath = true :: p) :
      LocalTraceEdge o₁ o₂
  /- Backward composition `A\B, B\C ↦ A\C`. -/
  | compLeft_A {Γ Δ : List Category} {A B C : Category}
      {t₁ : DerivationTree Γ (A ⧹ B)} {t₂ : DerivationTree Δ (B ⧹ C)}
      {o₁ o₂ : Occurrence (DerivationTree.binary t₁ t₂ Rule.compLeft)} {p : CategoryPath}
      (h₁n : o₁.nodePath = [.left]) (h₁p : o₁.categoryPath = false :: p)
      (h₂n : o₂.nodePath = []) (h₂p : o₂.categoryPath = false :: p) :
      LocalTraceEdge o₁ o₂
  | compLeft_B {Γ Δ : List Category} {A B C : Category}
      {t₁ : DerivationTree Γ (A ⧹ B)} {t₂ : DerivationTree Δ (B ⧹ C)}
      {o₁ o₂ : Occurrence (DerivationTree.binary t₁ t₂ Rule.compLeft)} {p : CategoryPath}
      (h₁n : o₁.nodePath = [.left]) (h₁p : o₁.categoryPath = true :: p)
      (h₂n : o₂.nodePath = [.right]) (h₂p : o₂.categoryPath = false :: p) :
      LocalTraceEdge o₁ o₂
  | compLeft_C {Γ Δ : List Category} {A B C : Category}
      {t₁ : DerivationTree Γ (A ⧹ B)} {t₂ : DerivationTree Δ (B ⧹ C)}
      {o₁ o₂ : Occurrence (DerivationTree.binary t₁ t₂ Rule.compLeft)} {p : CategoryPath}
      (h₁n : o₁.nodePath = [.right]) (h₁p : o₁.categoryPath = true :: p)
      (h₂n : o₂.nodePath = []) (h₂p : o₂.categoryPath = true :: p) :
      LocalTraceEdge o₁ o₂
  /- Forward crossed composition `C/B, A\B ↦ A\C`. -/
  | crossedRight_C {Γ Δ : List Category} {C B A : Category}
      {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (A ⧹ B)}
      {o₁ o₂ : Occurrence (DerivationTree.binary t₁ t₂ Rule.crossedRight)} {p : CategoryPath}
      (h₁n : o₁.nodePath = [.left]) (h₁p : o₁.categoryPath = false :: p)
      (h₂n : o₂.nodePath = []) (h₂p : o₂.categoryPath = true :: p) :
      LocalTraceEdge o₁ o₂
  | crossedRight_B {Γ Δ : List Category} {C B A : Category}
      {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (A ⧹ B)}
      {o₁ o₂ : Occurrence (DerivationTree.binary t₁ t₂ Rule.crossedRight)} {p : CategoryPath}
      (h₁n : o₁.nodePath = [.left]) (h₁p : o₁.categoryPath = true :: p)
      (h₂n : o₂.nodePath = [.right]) (h₂p : o₂.categoryPath = true :: p) :
      LocalTraceEdge o₁ o₂
  | crossedRight_A {Γ Δ : List Category} {C B A : Category}
      {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (A ⧹ B)}
      {o₁ o₂ : Occurrence (DerivationTree.binary t₁ t₂ Rule.crossedRight)} {p : CategoryPath}
      (h₁n : o₁.nodePath = [.right]) (h₁p : o₁.categoryPath = false :: p)
      (h₂n : o₂.nodePath = []) (h₂p : o₂.categoryPath = false :: p) :
      LocalTraceEdge o₁ o₂
  /- Backward crossed composition `B/A, B\C ↦ C/A`. -/
  | crossedLeft_B {Γ Δ : List Category} {B A C : Category}
      {t₁ : DerivationTree Γ (B ⧸ A)} {t₂ : DerivationTree Δ (B ⧹ C)}
      {o₁ o₂ : Occurrence (DerivationTree.binary t₁ t₂ Rule.crossedLeft)} {p : CategoryPath}
      (h₁n : o₁.nodePath = [.left]) (h₁p : o₁.categoryPath = false :: p)
      (h₂n : o₂.nodePath = [.right]) (h₂p : o₂.categoryPath = false :: p) :
      LocalTraceEdge o₁ o₂
  | crossedLeft_A {Γ Δ : List Category} {B A C : Category}
      {t₁ : DerivationTree Γ (B ⧸ A)} {t₂ : DerivationTree Δ (B ⧹ C)}
      {o₁ o₂ : Occurrence (DerivationTree.binary t₁ t₂ Rule.crossedLeft)} {p : CategoryPath}
      (h₁n : o₁.nodePath = [.left]) (h₁p : o₁.categoryPath = true :: p)
      (h₂n : o₂.nodePath = []) (h₂p : o₂.categoryPath = true :: p) :
      LocalTraceEdge o₁ o₂
  | crossedLeft_C {Γ Δ : List Category} {B A C : Category}
      {t₁ : DerivationTree Γ (B ⧸ A)} {t₂ : DerivationTree Δ (B ⧹ C)}
      {o₁ o₂ : Occurrence (DerivationTree.binary t₁ t₂ Rule.crossedLeft)} {p : CategoryPath}
      (h₁n : o₁.nodePath = [.right]) (h₁p : o₁.categoryPath = true :: p)
      (h₂n : o₂.nodePath = []) (h₂p : o₂.categoryPath = false :: p) :
      LocalTraceEdge o₁ o₂

/-- Directed trace half-edge, closed under all derivation contexts.  Local
metavariable-copy links are generated by `LocalTraceEdge`; the recursive
clauses below transport those links through unary and binary tree contexts. -/
def DirectedTraceEdge : {Γ : List Category} → {A : Category} → {t : DerivationTree Γ A} →
    Occurrence t → Occurrence t → Prop
  | _, _, .leaf _, _, _ => False
  | _, _, .typeRaiseRight C t, o₁, o₂ =>
      LocalTraceEdge o₁ o₂ ∨
        ∃ a b : Occurrence t,
          DirectedTraceEdge a b ∧
            o₁ = DerivationTree.CategoryOccurrence.underUnaryRight C a ∧
            o₂ = DerivationTree.CategoryOccurrence.underUnaryRight C b
  | _, _, .typeRaiseLeft C t, o₁, o₂ =>
      LocalTraceEdge o₁ o₂ ∨
        ∃ a b : Occurrence t,
          DirectedTraceEdge a b ∧
            o₁ = DerivationTree.CategoryOccurrence.underUnaryLeft C a ∧
            o₂ = DerivationTree.CategoryOccurrence.underUnaryLeft C b
  | _, _, .binary t₁ t₂ r, o₁, o₂ =>
      LocalTraceEdge o₁ o₂ ∨
        (∃ a b : Occurrence t₁,
          DirectedTraceEdge a b ∧
            o₁ = DerivationTree.CategoryOccurrence.underBinaryLeft r a ∧
            o₂ = DerivationTree.CategoryOccurrence.underBinaryLeft r b) ∨
        (∃ a b : Occurrence t₂,
          DirectedTraceEdge a b ∧
            o₁ = DerivationTree.CategoryOccurrence.underBinaryRight r a ∧
            o₂ = DerivationTree.CategoryOccurrence.underBinaryRight r b)

/-- Public trace edge relation: the undirected graph generated by the rule-local
metavariable-copy half-edges. -/
def TraceEdge {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (o₁ o₂ : Occurrence t) : Prop :=
  DirectedTraceEdge o₁ o₂ ∨ DirectedTraceEdge o₂ o₁

@[grind =>]
theorem TraceEdge.symm {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ : Occurrence t} (h : TraceEdge o₁ o₂) : TraceEdge o₂ o₁ := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

namespace DirectedTraceEdge

/-- Directed trace edges lift through a forward type-raising context. -/
theorem underUnaryRight
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ : Occurrence t} (C : Category)
    (h : DirectedTraceEdge o₁ o₂) :
    DirectedTraceEdge
      (DerivationTree.CategoryOccurrence.underUnaryRight C o₁)
      (DerivationTree.CategoryOccurrence.underUnaryRight C o₂) :=
  Or.inr ⟨o₁, o₂, h, rfl, rfl⟩

/-- Directed trace edges lift through a backward type-raising context. -/
theorem underUnaryLeft
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ : Occurrence t} (C : Category)
    (h : DirectedTraceEdge o₁ o₂) :
    DirectedTraceEdge
      (DerivationTree.CategoryOccurrence.underUnaryLeft C o₁)
      (DerivationTree.CategoryOccurrence.underUnaryLeft C o₂) :=
  Or.inr ⟨o₁, o₂, h, rfl, rfl⟩

/-- Directed trace edges lift through the left premise of a binary context. -/
theorem underBinaryLeft
    {Γ Δ : List Category} {A B C : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ B}
    {o₁ o₂ : Occurrence t₁} (r : Rule A B C)
    (h : DirectedTraceEdge o₁ o₂) :
    DirectedTraceEdge
      (DerivationTree.CategoryOccurrence.underBinaryLeft (t₂ := t₂) r o₁)
      (DerivationTree.CategoryOccurrence.underBinaryLeft (t₂ := t₂) r o₂) :=
  Or.inr (Or.inl ⟨o₁, o₂, h, rfl, rfl⟩)

/-- Directed trace edges lift through the right premise of a binary context. -/
theorem underBinaryRight
    {Γ Δ : List Category} {A B C : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ B}
    {o₁ o₂ : Occurrence t₂} (r : Rule A B C)
    (h : DirectedTraceEdge o₁ o₂) :
    DirectedTraceEdge
      (DerivationTree.CategoryOccurrence.underBinaryRight (t₁ := t₁) r o₁)
      (DerivationTree.CategoryOccurrence.underBinaryRight (t₁ := t₁) r o₂) :=
  Or.inr (Or.inr ⟨o₁, o₂, h, rfl, rfl⟩)

end DirectedTraceEdge

namespace TraceEdge

/-- Trace edges lift through a forward type-raising context. -/
theorem underUnaryRight
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ : Occurrence t} (C : Category)
    (h : TraceEdge o₁ o₂) :
    TraceEdge
      (DerivationTree.CategoryOccurrence.underUnaryRight C o₁)
      (DerivationTree.CategoryOccurrence.underUnaryRight C o₂) := by
  rcases h with h | h
  · exact Or.inl (DirectedTraceEdge.underUnaryRight C h)
  · exact Or.inr (DirectedTraceEdge.underUnaryRight C h)

/-- Trace edges lift through a backward type-raising context. -/
theorem underUnaryLeft
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ : Occurrence t} (C : Category)
    (h : TraceEdge o₁ o₂) :
    TraceEdge
      (DerivationTree.CategoryOccurrence.underUnaryLeft C o₁)
      (DerivationTree.CategoryOccurrence.underUnaryLeft C o₂) := by
  rcases h with h | h
  · exact Or.inl (DirectedTraceEdge.underUnaryLeft C h)
  · exact Or.inr (DirectedTraceEdge.underUnaryLeft C h)

/-- Trace edges lift through the left premise of a binary context. -/
theorem underBinaryLeft
    {Γ Δ : List Category} {A B C : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ B}
    {o₁ o₂ : Occurrence t₁} (r : Rule A B C)
    (h : TraceEdge o₁ o₂) :
    TraceEdge
      (DerivationTree.CategoryOccurrence.underBinaryLeft (t₂ := t₂) r o₁)
      (DerivationTree.CategoryOccurrence.underBinaryLeft (t₂ := t₂) r o₂) := by
  rcases h with h | h
  · exact Or.inl (DirectedTraceEdge.underBinaryLeft (t₂ := t₂) r h)
  · exact Or.inr (DirectedTraceEdge.underBinaryLeft (t₂ := t₂) r h)

/-- Trace edges lift through the right premise of a binary context. -/
theorem underBinaryRight
    {Γ Δ : List Category} {A B C : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ B}
    {o₁ o₂ : Occurrence t₂} (r : Rule A B C)
    (h : TraceEdge o₁ o₂) :
    TraceEdge
      (DerivationTree.CategoryOccurrence.underBinaryRight (t₁ := t₁) r o₁)
      (DerivationTree.CategoryOccurrence.underBinaryRight (t₁ := t₁) r o₂) := by
  rcases h with h | h
  · exact Or.inl (DirectedTraceEdge.underBinaryRight (t₁ := t₁) r h)
  · exact Or.inr (DirectedTraceEdge.underBinaryRight (t₁ := t₁) r h)

end TraceEdge

/-! ## Typed derivation contexts for trace lifting -/

/-- A typed derivation context with one hole.  The fields package the plug
operation together with occurrence and trace lifting, avoiding later ad-hoc
reasoning about raw `NodePath` prefixes. -/
structure DerivationContext
    (Γ : List Category) (A : Category) (Δ : List Category) (B : Category) where
  plug : DerivationTree Γ A → DerivationTree Δ B
  nodePrefix : NodePath
  liftOccurrence :
    {t : DerivationTree Γ A} → Occurrence t → Occurrence (plug t)
  liftOccurrence_nodePath :
    ∀ {t : DerivationTree Γ A} (o : Occurrence t),
      (liftOccurrence o).nodePath = nodePrefix ++ o.nodePath
  liftOccurrence_nodeCategory :
    ∀ {t : DerivationTree Γ A} (o : Occurrence t),
      (liftOccurrence o).nodeCategory = o.nodeCategory
  liftOccurrence_categoryPath :
    ∀ {t : DerivationTree Γ A} (o : Occurrence t),
      (liftOccurrence o).categoryPath = o.categoryPath
  categoryAt?_local :
    ∀ {t : DerivationTree Γ A} {p : NodePath} {C : Category},
      t.categoryAt? p = some C →
        (plug t).categoryAt? (nodePrefix ++ p) = some C
  categoryAt?_reflect :
    ∀ {t : DerivationTree Γ A} {p : NodePath} {C : Category},
      (plug t).categoryAt? (nodePrefix ++ p) = some C →
        t.categoryAt? p = some C
  liftLeafNode :
    ∀ {t : DerivationTree Γ A} {p : NodePath},
      t.isLeafNode p → (plug t).isLeafNode (nodePrefix ++ p)
  liftPrincipalConstructor :
    ∀ {t : DerivationTree Γ A} {p : NodePath} {cpos : CategoryPath},
      DerivationTree.PrincipalConstructor t p cpos →
        DerivationTree.PrincipalConstructor (plug t) (nodePrefix ++ p) cpos
  liftUnarySkeletonConstructor :
    ∀ {t : DerivationTree Γ A} {p : NodePath} {cpos : CategoryPath},
      DerivationTree.UnarySkeletonConstructor t p cpos →
        DerivationTree.UnarySkeletonConstructor (plug t) (nodePrefix ++ p) cpos
  liftTraceEdge :
    ∀ {t : DerivationTree Γ A} {o₁ o₂ : Occurrence t},
      TraceEdge o₁ o₂ → TraceEdge (liftOccurrence o₁) (liftOccurrence o₂)

namespace DerivationContext

/-- An occurrence in a plugged tree is the context-lift of a local occurrence
once the node path, node category, and category path agree. -/
theorem occurrence_eq_lift
    {Γ : List Category} {A : Category} {Δ : List Category} {B : Category}
    (ctx : DerivationContext Γ A Δ B)
    {t : DerivationTree Γ A} {o : Occurrence (ctx.plug t)} {a : Occurrence t}
    (hnode : o.nodePath = ctx.nodePrefix ++ a.nodePath)
    (hcat : o.nodeCategory = a.nodeCategory)
    (hpos : o.categoryPath = a.categoryPath) :
    o = ctx.liftOccurrence a := by
  apply DerivationTree.CategoryOccurrence.eq_of_data
  · rw [hnode, ctx.liftOccurrence_nodePath a]
  · rw [hcat, ctx.liftOccurrence_nodeCategory a]
  · rw [hpos, ctx.liftOccurrence_categoryPath a]

/-- Protected unary-skeleton occurrences lift through any packaged derivation
context. -/
theorem liftProtectedUnarySkeleton
    {Γ : List Category} {A : Category} {Δ : List Category} {B : Category}
    (ctx : DerivationContext Γ A Δ B)
    {t : DerivationTree Γ A} {o : Occurrence t}
    (h : o.ProtectedUnarySkeleton) :
    (ctx.liftOccurrence o).ProtectedUnarySkeleton := by
  change DerivationTree.UnarySkeletonConstructor
    (ctx.plug t) (ctx.liftOccurrence o).nodePath
      (ctx.liftOccurrence o).categoryPath
  rw [ctx.liftOccurrence_nodePath o, ctx.liftOccurrence_categoryPath o]
  exact ctx.liftUnarySkeletonConstructor h

/-- The empty context. -/
def hole (Γ : List Category) (A : Category) :
    DerivationContext Γ A Γ A where
  plug := fun t => t
  nodePrefix := []
  liftOccurrence := fun o => o
  liftOccurrence_nodePath := by
    intro t o
    rfl
  liftOccurrence_nodeCategory := by
    intro t o
    rfl
  liftOccurrence_categoryPath := by
    intro t o
    rfl
  categoryAt?_local := by
    intro t p C h
    exact h
  categoryAt?_reflect := by
    intro t p C h
    exact h
  liftLeafNode := by
    intro t p h
    simpa using h
  liftPrincipalConstructor := by
    intro t p cpos h
    exact h
  liftUnarySkeletonConstructor := by
    intro t p cpos h
    exact h
  liftTraceEdge := by
    intro t o₁ o₂ h
    exact h

/-- Add a forward type-raising frame around a context. -/
def typeRaiseRight
    {Γ : List Category} {A : Category} {Δ : List Category} {B : Category}
    (C : Category) (ctx : DerivationContext Γ A Δ B) :
    DerivationContext Γ A Δ (C ⧸ (B ⧹ C)) where
  plug := fun t => DerivationTree.typeRaiseRight C (ctx.plug t)
  nodePrefix := .unary :: ctx.nodePrefix
  liftOccurrence := fun o =>
    DerivationTree.CategoryOccurrence.underUnaryRight C (ctx.liftOccurrence o)
  liftOccurrence_nodePath := by
    intro t o
    change TreeStep.unary :: (ctx.liftOccurrence o).nodePath =
      TreeStep.unary :: (ctx.nodePrefix ++ o.nodePath)
    rw [ctx.liftOccurrence_nodePath o]
  liftOccurrence_nodeCategory := by
    intro t o
    exact ctx.liftOccurrence_nodeCategory o
  liftOccurrence_categoryPath := by
    intro t o
    change (ctx.liftOccurrence o).categoryPath = o.categoryPath
    exact ctx.liftOccurrence_categoryPath o
  categoryAt?_local := by
    intro t p D h
    change (ctx.plug t).categoryAt? (ctx.nodePrefix ++ p) = some D
    exact ctx.categoryAt?_local h
  categoryAt?_reflect := by
    intro t p D h
    change (ctx.plug t).categoryAt? (ctx.nodePrefix ++ p) = some D at h
    exact ctx.categoryAt?_reflect h
  liftLeafNode := by
    intro t p h
    change (ctx.plug t).isLeafNode (ctx.nodePrefix ++ p)
    exact ctx.liftLeafNode h
  liftPrincipalConstructor := by
    intro t p cpos h
    exact DerivationTree.PrincipalConstructor.underUnaryRight C
      (ctx.liftPrincipalConstructor h)
  liftUnarySkeletonConstructor := by
    intro t p cpos h
    exact DerivationTree.UnarySkeletonConstructor.underUnaryRight C
      (ctx.liftUnarySkeletonConstructor h)
  liftTraceEdge := by
    intro t o₁ o₂ h
    exact TraceEdge.underUnaryRight C (ctx.liftTraceEdge h)

/-- Add a backward type-raising frame around a context. -/
def typeRaiseLeft
    {Γ : List Category} {A : Category} {Δ : List Category} {B : Category}
    (C : Category) (ctx : DerivationContext Γ A Δ B) :
    DerivationContext Γ A Δ ((C ⧸ B) ⧹ C) where
  plug := fun t => DerivationTree.typeRaiseLeft C (ctx.plug t)
  nodePrefix := .unary :: ctx.nodePrefix
  liftOccurrence := fun o =>
    DerivationTree.CategoryOccurrence.underUnaryLeft C (ctx.liftOccurrence o)
  liftOccurrence_nodePath := by
    intro t o
    change TreeStep.unary :: (ctx.liftOccurrence o).nodePath =
      TreeStep.unary :: (ctx.nodePrefix ++ o.nodePath)
    rw [ctx.liftOccurrence_nodePath o]
  liftOccurrence_nodeCategory := by
    intro t o
    exact ctx.liftOccurrence_nodeCategory o
  liftOccurrence_categoryPath := by
    intro t o
    change (ctx.liftOccurrence o).categoryPath = o.categoryPath
    exact ctx.liftOccurrence_categoryPath o
  categoryAt?_local := by
    intro t p D h
    change (ctx.plug t).categoryAt? (ctx.nodePrefix ++ p) = some D
    exact ctx.categoryAt?_local h
  categoryAt?_reflect := by
    intro t p D h
    change (ctx.plug t).categoryAt? (ctx.nodePrefix ++ p) = some D at h
    exact ctx.categoryAt?_reflect h
  liftLeafNode := by
    intro t p h
    change (ctx.plug t).isLeafNode (ctx.nodePrefix ++ p)
    exact ctx.liftLeafNode h
  liftPrincipalConstructor := by
    intro t p cpos h
    exact DerivationTree.PrincipalConstructor.underUnaryLeft C
      (ctx.liftPrincipalConstructor h)
  liftUnarySkeletonConstructor := by
    intro t p cpos h
    exact DerivationTree.UnarySkeletonConstructor.underUnaryLeft C
      (ctx.liftUnarySkeletonConstructor h)
  liftTraceEdge := by
    intro t o₁ o₂ h
    exact TraceEdge.underUnaryLeft C (ctx.liftTraceEdge h)

/-- Add a binary-left frame around a context. -/
def binaryLeft
    {Γ : List Category} {A : Category} {Δ Ξ : List Category}
    {B D E : Category}
    (ctx : DerivationContext Γ A Δ B)
    (right : DerivationTree Ξ D) (r : Rule B D E) :
    DerivationContext Γ A (Δ ++ Ξ) E where
  plug := fun t => DerivationTree.binary (ctx.plug t) right r
  nodePrefix := .left :: ctx.nodePrefix
  liftOccurrence := fun o =>
    DerivationTree.CategoryOccurrence.underBinaryLeft r (ctx.liftOccurrence o)
  liftOccurrence_nodePath := by
    intro t o
    change TreeStep.left :: (ctx.liftOccurrence o).nodePath =
      TreeStep.left :: (ctx.nodePrefix ++ o.nodePath)
    rw [ctx.liftOccurrence_nodePath o]
  liftOccurrence_nodeCategory := by
    intro t o
    exact ctx.liftOccurrence_nodeCategory o
  liftOccurrence_categoryPath := by
    intro t o
    change (ctx.liftOccurrence o).categoryPath = o.categoryPath
    exact ctx.liftOccurrence_categoryPath o
  categoryAt?_local := by
    intro t p X h
    change (ctx.plug t).categoryAt? (ctx.nodePrefix ++ p) = some X
    exact ctx.categoryAt?_local h
  categoryAt?_reflect := by
    intro t p X h
    change (ctx.plug t).categoryAt? (ctx.nodePrefix ++ p) = some X at h
    exact ctx.categoryAt?_reflect h
  liftLeafNode := by
    intro t p h
    change (ctx.plug t).isLeafNode (ctx.nodePrefix ++ p)
    exact ctx.liftLeafNode h
  liftPrincipalConstructor := by
    intro t p cpos h
    exact DerivationTree.PrincipalConstructor.underBinaryLeft r
      (ctx.liftPrincipalConstructor h)
  liftUnarySkeletonConstructor := by
    intro t p cpos h
    exact DerivationTree.UnarySkeletonConstructor.underBinaryLeft r
      (ctx.liftUnarySkeletonConstructor h)
  liftTraceEdge := by
    intro t o₁ o₂ h
    exact TraceEdge.underBinaryLeft (t₂ := right) r (ctx.liftTraceEdge h)

/-- Add a binary-right frame around a context. -/
def binaryRight
    {Γ : List Category} {A : Category} {Δ Ξ : List Category}
    {B D E : Category}
    (left : DerivationTree Δ B)
    (ctx : DerivationContext Γ A Ξ D) (r : Rule B D E) :
    DerivationContext Γ A (Δ ++ Ξ) E where
  plug := fun t => DerivationTree.binary left (ctx.plug t) r
  nodePrefix := .right :: ctx.nodePrefix
  liftOccurrence := fun o =>
    DerivationTree.CategoryOccurrence.underBinaryRight r (ctx.liftOccurrence o)
  liftOccurrence_nodePath := by
    intro t o
    change TreeStep.right :: (ctx.liftOccurrence o).nodePath =
      TreeStep.right :: (ctx.nodePrefix ++ o.nodePath)
    rw [ctx.liftOccurrence_nodePath o]
  liftOccurrence_nodeCategory := by
    intro t o
    exact ctx.liftOccurrence_nodeCategory o
  liftOccurrence_categoryPath := by
    intro t o
    change (ctx.liftOccurrence o).categoryPath = o.categoryPath
    exact ctx.liftOccurrence_categoryPath o
  categoryAt?_local := by
    intro t p X h
    change (ctx.plug t).categoryAt? (ctx.nodePrefix ++ p) = some X
    exact ctx.categoryAt?_local h
  categoryAt?_reflect := by
    intro t p X h
    change (ctx.plug t).categoryAt? (ctx.nodePrefix ++ p) = some X at h
    exact ctx.categoryAt?_reflect h
  liftLeafNode := by
    intro t p h
    change (ctx.plug t).isLeafNode (ctx.nodePrefix ++ p)
    exact ctx.liftLeafNode h
  liftPrincipalConstructor := by
    intro t p cpos h
    exact DerivationTree.PrincipalConstructor.underBinaryRight r
      (ctx.liftPrincipalConstructor h)
  liftUnarySkeletonConstructor := by
    intro t p cpos h
    exact DerivationTree.UnarySkeletonConstructor.underBinaryRight r
      (ctx.liftUnarySkeletonConstructor h)
  liftTraceEdge := by
    intro t o₁ o₂ h
    exact TraceEdge.underBinaryRight (t₁ := left) r (ctx.liftTraceEdge h)

end DerivationContext

/-! ## Local trace-neighbour key enumeration

The degree bound in the paper is rule-local: a trace edge is always generated
by one of the finitely many schematic metavariable-copy links of the eight
rules, transported through an outer tree context.  The following key-level
enumerator is the first finite object needed for a non-vacuous proof of
`TraceDegreeLimit`: it lists all possible *local* neighbours of one local
endpoint key, including both orientations of each rule-local trace half-edge.
-/

namespace Occurrence.Key

/-- Rebase a local occurrence key under a derivation-node context. -/
def rebase (ctx : NodePath) (k : Occurrence.Key) : Occurrence.Key :=
  { nodePath := ctx ++ k.nodePath, categoryPath := k.categoryPath }

@[simp, grind =]
theorem rebase_nodePath (ctx : NodePath) (k : Occurrence.Key) :
    (k.rebase ctx).nodePath = ctx ++ k.nodePath := rfl

@[simp, grind =]
theorem rebase_categoryPath (ctx : NodePath) (k : Occurrence.Key) :
    (k.rebase ctx).categoryPath = k.categoryPath := rfl

end Occurrence.Key

namespace NodePath

/-- Split a nonempty node path into its parent context and final step. -/
def unsnoc? : NodePath → Option (NodePath × TreeStep)
  | [] => none
  | [step] => some ([], step)
  | step :: rest =>
      match unsnoc? rest with
      | some (ctx, last) => some (step :: ctx, last)
      | none => none

end NodePath

/-- All local trace-neighbour endpoint keys for a local endpoint key.  The node
path component is relative to the root of the local rule instance, so only
`[]`, `[unary]`, `[left]`, and `[right]` can participate in a local trace edge.
The list deliberately over-approximates by rule schema only; actual existence
of the returned endpoint in a concrete tree is checked later by the occurrence
proof carried by `Occurrence`. -/
def localTraceNeighborKeys (k : Occurrence.Key) : List Occurrence.Key :=
  let K (n : NodePath) (p : CategoryPath) : Occurrence.Key :=
    { nodePath := n, categoryPath := p }
  match k.nodePath with
  | [] =>
      let p := k.categoryPath
      let invTRightA :=
        match p with
        | true :: false :: q => [K [.unary] q]
        | _ => []
      let invTRightC :=
        match p with
        | false :: q => [K [] (true :: true :: q)]
        | true :: true :: q => [K [] (false :: q)]
        | _ => []
      let invTLeftA :=
        match p with
        | false :: true :: q => [K [.unary] q]
        | _ => []
      let invTLeftC :=
        match p with
        | false :: false :: q => [K [] (true :: q)]
        | true :: q => [K [] (false :: false :: q)]
        | _ => []
      let binaryTargets :=
        [ K [.left] (false :: p),  -- `>` C-copy target
          K [.right] (true :: p) ] -- `<` C-copy target
      let outputPrefixed :=
        match p with
        | false :: q =>
            [ K [.left] (false :: q),  -- `B>`/`B<` left A/C copies
              K [.right] (false :: q), -- crossed-right A / crossed-left C
              K [.right] (true :: q) ] -- crossed-left C
        | true :: q =>
            [ K [.right] (true :: q),  -- `B>`/`B<` right A/C copies
              K [.left] (false :: q),  -- crossed-right C
              K [.left] (true :: q) ]  -- crossed-left A
        | [] => []
      invTRightA ++ invTRightC ++ invTLeftA ++ invTLeftC ++ binaryTargets ++ outputPrefixed
  | [.unary] =>
      let p := k.categoryPath
      [ K [] (true :: false :: p),  -- `T>` A-copy
        K [] (false :: true :: p) ] -- `T<` A-copy
  | [.left] =>
      let p := k.categoryPath
      let direct :=
        [ K [.right] (false :: p) ] -- `<` A-copy target
      let prefixed :=
        match p with
        | false :: q =>
            [ K [] q,              -- `>` C-copy source
              K [] (false :: q),   -- `B>` C / `B<` A
              K [] (true :: q),    -- crossed-right C
              K [.right] (false :: q) ] -- crossed-left B
        | true :: q =>
            [ K [.right] q,              -- `>` B-copy source
              K [.right] (false :: q),   -- `B>`/`B<` B-copy
              K [.right] (true :: q),    -- crossed-right B
              K [] (true :: q) ]         -- crossed-left A
        | [] => []
      direct ++ prefixed
  | [.right] =>
      let p := k.categoryPath
      let direct :=
        [ K [.left] (true :: p) ] -- `>` B-copy target
      let prefixed :=
        match p with
        | false :: q =>
            [ K [.left] q,              -- `<` A-copy target
              K [.left] (true :: q),    -- `B>`/`B<` B-copy target
              K [] (false :: q),        -- crossed-right A
              K [.left] (false :: q) ]  -- crossed-left B
        | true :: q =>
            [ K [] q,                  -- `<` C-copy source
              K [] (true :: q),        -- `B>`/`B<` A/C source
              K [.left] (true :: q),   -- crossed-right B
              K [] (false :: q) ]      -- crossed-left C
        | [] => []
      direct ++ prefixed
  | _ => []

/-- The rule-local key enumerator covers every directed local trace half-edge. -/
theorem LocalTraceEdge.key_mem_localTraceNeighborKeys
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ : Occurrence t} (h : LocalTraceEdge o₁ o₂) :
    o₂.key ∈ localTraceNeighborKeys o₁.key := by
  cases h <;>
  · rename_i h₁n h₁p h₂n h₂p
    rw [Occurrence.key, Occurrence.key, h₁n, h₁p, h₂n, h₂p]
    simp [localTraceNeighborKeys]

/-- The same key enumerator also covers the reverse orientation of a directed
local half-edge; this is the local ingredient for the public undirected
`TraceEdge`. -/
theorem LocalTraceEdge.reverse_key_mem_localTraceNeighborKeys
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ : Occurrence t} (h : LocalTraceEdge o₁ o₂) :
    o₁.key ∈ localTraceNeighborKeys o₂.key := by
  cases h <;>
  · rename_i h₁n h₁p h₂n h₂p
    rw [Occurrence.key, Occurrence.key, h₁n, h₁p, h₂n, h₂p]
    simp [localTraceNeighborKeys]

/-- A conservative rule-local trace-degree bound at the key level.  The actual
global `traceNeighborLimit = 64` leaves room for both orientations and the two
possible local rule contexts adjacent to a node occurrence. -/
theorem localTraceNeighborKeys_length_le (k : Occurrence.Key) :
    (localTraceNeighborKeys k).length ≤ 16 := by
  rcases k with ⟨n, p⟩
  cases n with
  | nil =>
      cases p with
      | nil => simp [localTraceNeighborKeys]
      | cons b p =>
          cases b <;>
          cases p with
          | nil => simp [localTraceNeighborKeys]
          | cons b' q =>
              cases b' <;> simp [localTraceNeighborKeys]
  | cons s rest =>
      cases rest with
      | nil =>
          cases s <;>
          cases p with
          | nil => simp [localTraceNeighborKeys]
          | cons b q =>
              cases b <;> simp [localTraceNeighborKeys]
      | cons s' rest' =>
          cases s <;> simp [localTraceNeighborKeys]

/-- Candidate global neighbour keys for one occurrence key.  A concrete trace
edge involving a node occurrence can only be generated by a rule instance at
the occurrence's own node (where the local endpoint is `[]`) or at its immediate
parent (where the local endpoint is `[unary]`, `[left]`, or `[right]`). -/
def traceNeighborKeyCandidates (k : Occurrence.Key) : List Occurrence.Key :=
  let self : List Occurrence.Key :=
    (localTraceNeighborKeys { nodePath := [], categoryPath := k.categoryPath }).map
      (Occurrence.Key.rebase k.nodePath)
  let parent : List Occurrence.Key :=
    match NodePath.unsnoc? k.nodePath with
    | none => []
    | some (ctx, step) =>
        (localTraceNeighborKeys { nodePath := [step], categoryPath := k.categoryPath }).map
          (Occurrence.Key.rebase ctx)
  self ++ parent

/-- Conservative key-level global trace-neighbour budget. -/
theorem traceNeighborKeyCandidates_length_le (k : Occurrence.Key) :
    (traceNeighborKeyCandidates k).length ≤ 64 := by
  unfold traceNeighborKeyCandidates
  have hself :
      (localTraceNeighborKeys ({ nodePath := [], categoryPath := k.categoryPath } : Occurrence.Key)).length ≤ 16 :=
    localTraceNeighborKeys_length_le _
  cases hparent : NodePath.unsnoc? k.nodePath with
  | none =>
      simp
      omega
  | some pair =>
      rcases pair with ⟨ctx, step⟩
      have hpar :
          (localTraceNeighborKeys ({ nodePath := [step], categoryPath := k.categoryPath } : Occurrence.Key)).length ≤ 16 :=
        localTraceNeighborKeys_length_le _
      simp
      omega

/-- Local trace half-edges are covered by the global key candidates. -/
theorem LocalTraceEdge.key_mem_traceNeighborKeyCandidates
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ : Occurrence t} (h : LocalTraceEdge o₁ o₂) :
    o₂.key ∈ traceNeighborKeyCandidates o₁.key := by
  cases h <;>
  · rename_i h₁n h₁p h₂n h₂p
    rw [Occurrence.key, Occurrence.key, h₁n, h₁p, h₂n, h₂p]
    simp [traceNeighborKeyCandidates, localTraceNeighborKeys, NodePath.unsnoc?,
      Occurrence.Key.rebase]

/-- Reverse local trace half-edges are covered by the global key candidates. -/
theorem LocalTraceEdge.reverse_key_mem_traceNeighborKeyCandidates
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ : Occurrence t} (h : LocalTraceEdge o₁ o₂) :
    o₁.key ∈ traceNeighborKeyCandidates o₂.key := by
  cases h <;>
  · rename_i h₁n h₁p h₂n h₂p
    rw [Occurrence.key, Occurrence.key, h₁n, h₁p, h₂n, h₂p]
    simp [traceNeighborKeyCandidates, localTraceNeighborKeys, NodePath.unsnoc?,
      Occurrence.Key.rebase]

/-- **Trace-edge soundness (local).** Every rule-local metavariable-copy
half-edge connects two occurrences that address the *same* subcategory.  This is
the defining invariant of the trace graph: an edge links two copies of one
schematic metavariable, so the subterms they point at are syntactically equal.
It is what makes the rule-by-rule edge positions of `LocalTraceEdge`
meaningful rather than arbitrary, and it is the seed of the transport argument
used by the band-contraction proof. -/
theorem LocalTraceEdge.sameSub {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ : Occurrence t} (h : LocalTraceEdge o₁ o₂) :
    o₁.nodeCategory.subcategoryAt? o₁.categoryPath = o₂.nodeCategory.subcategoryAt? o₂.categoryPath := by
  have e1 := o₁.nodeAt
  have e2 := o₂.nodeAt
  cases h <;>
  · rename_i h₁n h₁p h₂n h₂p
    rw [h₁n] at e1
    rw [h₂n] at e2
    simp only [DerivationTree.categoryAt?, DerivationTree.categoryAt?_root, Option.some.injEq] at e1 e2
    rw [h₁p, h₂p, ← e1, ← e2]
    simp [Category.subcategoryAt?]

/-- **Trace-edge soundness (transport-closed).** The same-subcategory invariant
is preserved by transport through every derivation context, so it holds for the
full directed trace relation `DirectedTraceEdge`. -/
theorem DirectedTraceEdge.sameSub :
    {Γ : List Category} → {A : Category} → {t : DerivationTree Γ A} → {o₁ o₂ : Occurrence t} →
      DirectedTraceEdge o₁ o₂ → o₁.nodeCategory.subcategoryAt? o₁.categoryPath = o₂.nodeCategory.subcategoryAt? o₂.categoryPath
  | _, _, .leaf _, _, _, h => (h : False).elim
  | _, _, .typeRaiseRight _ _, _, _, h => by
      rcases h with hloc | ⟨a, b, hab, rfl, rfl⟩
      · exact hloc.sameSub
      · exact (DirectedTraceEdge.sameSub hab :
          a.nodeCategory.subcategoryAt? a.categoryPath = b.nodeCategory.subcategoryAt? b.categoryPath)
  | _, _, .typeRaiseLeft _ _, _, _, h => by
      rcases h with hloc | ⟨a, b, hab, rfl, rfl⟩
      · exact hloc.sameSub
      · exact (DirectedTraceEdge.sameSub hab :
          a.nodeCategory.subcategoryAt? a.categoryPath = b.nodeCategory.subcategoryAt? b.categoryPath)
  | _, _, .binary _ _ _, _, _, h => by
      rcases h with hloc | ⟨a, b, hab, rfl, rfl⟩ | ⟨a, b, hab, rfl, rfl⟩
      · exact hloc.sameSub
      · exact (DirectedTraceEdge.sameSub hab :
          a.nodeCategory.subcategoryAt? a.categoryPath = b.nodeCategory.subcategoryAt? b.categoryPath)
      · exact (DirectedTraceEdge.sameSub hab :
          a.nodeCategory.subcategoryAt? a.categoryPath = b.nodeCategory.subcategoryAt? b.categoryPath)

/-- **Trace-edge soundness (public).** Both endpoints of a public undirected
trace edge address the same subcategory. -/
theorem TraceEdge.sameSub {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ : Occurrence t} (h : TraceEdge o₁ o₂) :
    o₁.nodeCategory.subcategoryAt? o₁.categoryPath = o₂.nodeCategory.subcategoryAt? o₂.categoryPath := by
  rcases h with h | h
  · exact h.sameSub
  · exact h.sameSub.symm

/-! ## Global trace-degree transport

The rule-local key coverage lemmas (`LocalTraceEdge.key_mem_traceNeighborKeyCandidates`
and its reverse) only describe edges generated at the root of a local rule
instance.  The transport lemmas below push that coverage through every unary and
binary derivation context, so that *every* directed trace edge — local or
transported — keeps its target inside the finite key budget of its source.
This is the non-vacuous heart of the trace-degree bound: it turns the
rule-local `≤ 64` key count into a global degree bound on the trace graph.
-/

/-- Soundness of `NodePath.unsnoc?`: a successful split reconstructs the path. -/
theorem NodePath.unsnoc?_eq_some :
    ∀ {p : NodePath} {ctx : NodePath} {step : TreeStep},
      NodePath.unsnoc? p = some (ctx, step) → p = ctx ++ [step]
  | [], _, _, h => by simp [NodePath.unsnoc?] at h
  | [s], ctx, step, h => by
      simp only [NodePath.unsnoc?, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hctx, hstep⟩ := h
      subst hctx; subst hstep; rfl
  | s :: a :: rest, ctx, step, h => by
      simp only [NodePath.unsnoc?] at h
      cases hu : NodePath.unsnoc? (a :: rest) with
      | none => rw [hu] at h; simp at h
      | some pair =>
          rw [hu] at h
          obtain ⟨ctx', step'⟩ := pair
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hctx, hstep⟩ := h
          subst hctx; subst hstep
          have ih := NodePath.unsnoc?_eq_some hu
          rw [ih]; rfl

/-- `NodePath.unsnoc?` splits an explicitly snoc-shaped path. -/
theorem NodePath.unsnoc?_concat (ctx : NodePath) (step : TreeStep) :
    NodePath.unsnoc? (ctx ++ [step]) = some (ctx, step) := by
  induction ctx with
  | nil => rfl
  | cons a as ih =>
      cases as with
      | nil => rfl
      | cons b bs =>
          change (match NodePath.unsnoc? ((b :: bs) ++ [step]) with
                | some (c, l) => some (a :: c, l)
                | none => none) = some (a :: b :: bs, step)
          rw [ih]

/-- Rebasing keys composes: rebasing by `q` then by `pre` rebases by `pre ++ q`. -/
theorem Occurrence.Key.rebase_rebase (pre q : NodePath) (m : Occurrence.Key) :
    (m.rebase q).rebase pre = m.rebase (pre ++ q) := by
  unfold Occurrence.Key.rebase
  simp [List.append_assoc]

/-- **Candidate transport.** Rebasing both an occurrence key and a member of its
candidate-neighbour set by a context keeps the member inside the rebased
candidate set.  Because `traceNeighborKeyCandidates` only inspects the final
node step and the category path, prepending a context is functorial. -/
theorem traceNeighborKeyCandidates_rebase_mem (ctx : NodePath) {k1 k2 : Occurrence.Key}
    (h : k2 ∈ traceNeighborKeyCandidates k1) :
    k2.rebase ctx ∈ traceNeighborKeyCandidates (k1.rebase ctx) := by
  unfold traceNeighborKeyCandidates at h ⊢
  simp only [List.mem_append, List.mem_map] at h ⊢
  rcases h with ⟨m, hm, hmk⟩ | hpar
  · left
    refine ⟨m, ?_, ?_⟩
    · simpa [Occurrence.Key.rebase] using hm
    · rw [← hmk, Occurrence.Key.rebase_nodePath, Occurrence.Key.rebase_rebase]
  · cases hu : NodePath.unsnoc? k1.nodePath with
    | none =>
        rw [hu] at hpar
        simp at hpar
    | some pair =>
        obtain ⟨ctx', step⟩ := pair
        rw [hu] at hpar
        simp only [List.mem_map] at hpar
        obtain ⟨m, hm, hmk⟩ := hpar
        right
        have hnp : k1.nodePath = ctx' ++ [step] := NodePath.unsnoc?_eq_some hu
        have hrebnp : (k1.rebase ctx).nodePath = (ctx ++ ctx') ++ [step] := by
          simp [Occurrence.Key.rebase, hnp, List.append_assoc]
        rw [hrebnp, NodePath.unsnoc?_concat]
        simp only [List.mem_map]
        refine ⟨m, ?_, ?_⟩
        · simpa [Occurrence.Key.rebase] using hm
        · rw [← hmk, Occurrence.Key.rebase_rebase]

namespace DerivationTree

/-- Lifting an occurrence under forward type raising rebases its key by `unary`. -/
theorem key_underUnaryRight (C : Category) {Γ : List Category} {A : Category}
    {t : DerivationTree Γ A} (a : Occurrence t) :
    Occurrence.key (CategoryOccurrence.underUnaryRight C a) = a.key.rebase [TreeStep.unary] := rfl

/-- Lifting an occurrence under backward type raising rebases its key by `unary`. -/
theorem key_underUnaryLeft (C : Category) {Γ : List Category} {A : Category}
    {t : DerivationTree Γ A} (a : Occurrence t) :
    Occurrence.key (CategoryOccurrence.underUnaryLeft C a) = a.key.rebase [TreeStep.unary] := rfl

/-- Lifting an occurrence under a binary left premise rebases its key by `left`. -/
theorem key_underBinaryLeft {Γ Δ : List Category} {A B C : Category}
    {t₁ : DerivationTree Γ A} (t₂ : DerivationTree Δ B) (r : Rule A B C)
    (a : Occurrence t₁) :
    Occurrence.key (CategoryOccurrence.underBinaryLeft (t₂ := t₂) r a) = a.key.rebase [TreeStep.left] := rfl

/-- Lifting an occurrence under a binary right premise rebases its key by `right`. -/
theorem key_underBinaryRight {Γ Δ : List Category} {A B C : Category}
    (t₁ : DerivationTree Γ A) {t₂ : DerivationTree Δ B} (r : Rule A B C)
    (a : Occurrence t₂) :
    Occurrence.key (CategoryOccurrence.underBinaryRight (t₁ := t₁) r a) = a.key.rebase [TreeStep.right] := rfl

end DerivationTree

open DerivationTree in
/-- **Global trace-degree coverage (forward).** Every directed trace edge keeps
its target's key inside the finite candidate-neighbour set of its source's key,
after transport through every derivation context. -/
theorem DirectedTraceEdge.key_mem_traceNeighborKeyCandidates :
    {Γ : List Category} → {A : Category} → {t : DerivationTree Γ A} → {o₁ o₂ : Occurrence t} →
      DirectedTraceEdge o₁ o₂ → o₂.key ∈ traceNeighborKeyCandidates o₁.key
  | _, _, .leaf _, _, _, h => (h : False).elim
  | _, _, .typeRaiseRight C t, o₁, o₂, h => by
      rcases h with hloc | ⟨a, b, hab, rfl, rfl⟩
      · exact hloc.key_mem_traceNeighborKeyCandidates
      · rw [key_underUnaryRight, key_underUnaryRight]
        exact traceNeighborKeyCandidates_rebase_mem [TreeStep.unary]
          (DirectedTraceEdge.key_mem_traceNeighborKeyCandidates hab)
  | _, _, .typeRaiseLeft C t, o₁, o₂, h => by
      rcases h with hloc | ⟨a, b, hab, rfl, rfl⟩
      · exact hloc.key_mem_traceNeighborKeyCandidates
      · rw [key_underUnaryLeft, key_underUnaryLeft]
        exact traceNeighborKeyCandidates_rebase_mem [TreeStep.unary]
          (DirectedTraceEdge.key_mem_traceNeighborKeyCandidates hab)
  | _, _, .binary t₁ t₂ r, o₁, o₂, h => by
      rcases h with hloc | ⟨a, b, hab, rfl, rfl⟩ | ⟨a, b, hab, rfl, rfl⟩
      · exact hloc.key_mem_traceNeighborKeyCandidates
      · rw [key_underBinaryLeft t₂, key_underBinaryLeft t₂]
        exact traceNeighborKeyCandidates_rebase_mem [TreeStep.left]
          (DirectedTraceEdge.key_mem_traceNeighborKeyCandidates hab)
      · rw [key_underBinaryRight t₁, key_underBinaryRight t₁]
        exact traceNeighborKeyCandidates_rebase_mem [TreeStep.right]
          (DirectedTraceEdge.key_mem_traceNeighborKeyCandidates hab)

open DerivationTree in
/-- **Global trace-degree coverage (reverse).** A directed edge `o₁ → o₂` also
keeps `o₁` inside the candidate set of `o₂`, transported through every context. -/
theorem DirectedTraceEdge.reverse_key_mem_traceNeighborKeyCandidates :
    {Γ : List Category} → {A : Category} → {t : DerivationTree Γ A} → {o₁ o₂ : Occurrence t} →
      DirectedTraceEdge o₁ o₂ → o₁.key ∈ traceNeighborKeyCandidates o₂.key
  | _, _, .leaf _, _, _, h => (h : False).elim
  | _, _, .typeRaiseRight C t, o₁, o₂, h => by
      rcases h with hloc | ⟨a, b, hab, rfl, rfl⟩
      · exact hloc.reverse_key_mem_traceNeighborKeyCandidates
      · rw [key_underUnaryRight, key_underUnaryRight]
        exact traceNeighborKeyCandidates_rebase_mem [TreeStep.unary]
          (DirectedTraceEdge.reverse_key_mem_traceNeighborKeyCandidates hab)
  | _, _, .typeRaiseLeft C t, o₁, o₂, h => by
      rcases h with hloc | ⟨a, b, hab, rfl, rfl⟩
      · exact hloc.reverse_key_mem_traceNeighborKeyCandidates
      · rw [key_underUnaryLeft, key_underUnaryLeft]
        exact traceNeighborKeyCandidates_rebase_mem [TreeStep.unary]
          (DirectedTraceEdge.reverse_key_mem_traceNeighborKeyCandidates hab)
  | _, _, .binary t₁ t₂ r, o₁, o₂, h => by
      rcases h with hloc | ⟨a, b, hab, rfl, rfl⟩ | ⟨a, b, hab, rfl, rfl⟩
      · exact hloc.reverse_key_mem_traceNeighborKeyCandidates
      · rw [key_underBinaryLeft t₂, key_underBinaryLeft t₂]
        exact traceNeighborKeyCandidates_rebase_mem [TreeStep.left]
          (DirectedTraceEdge.reverse_key_mem_traceNeighborKeyCandidates hab)
      · rw [key_underBinaryRight t₁, key_underBinaryRight t₁]
        exact traceNeighborKeyCandidates_rebase_mem [TreeStep.right]
          (DirectedTraceEdge.reverse_key_mem_traceNeighborKeyCandidates hab)

/-- **Undirected trace-degree coverage.** Both endpoints of a public trace edge
place the second key inside the candidate set of the first. -/
theorem TraceEdge.key_mem_traceNeighborKeyCandidates
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ : Occurrence t} (h : TraceEdge o₁ o₂) :
    o₂.key ∈ traceNeighborKeyCandidates o₁.key := by
  rcases h with h | h
  · exact DirectedTraceEdge.key_mem_traceNeighborKeyCandidates h
  · exact DirectedTraceEdge.reverse_key_mem_traceNeighborKeyCandidates h

/-- Two occurrences are in the same trace piece when they are connected by the
reflexive-transitive closure of undirected trace edges. -/
def SameTraceComponent {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (o₁ o₂ : Occurrence t) : Prop :=
  Relation.ReflTransGen TraceEdge o₁ o₂

namespace SameTraceComponent

@[refl]
theorem refl {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (o : Occurrence t) : SameTraceComponent o o :=
  Relation.ReflTransGen.refl

theorem trans {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ o₃ : Occurrence t}
    (h₁₂ : SameTraceComponent o₁ o₂) (h₂₃ : SameTraceComponent o₂ o₃) :
    SameTraceComponent o₁ o₃ :=
  Relation.ReflTransGen.trans h₁₂ h₂₃

theorem symm {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ : Occurrence t} (h : SameTraceComponent o₁ o₂) :
    SameTraceComponent o₂ o₁ := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hpath hedge ih =>
      exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single hedge.symm) ih

end SameTraceComponent

/-- **Trace-piece soundness.** Occurrences in the same trace piece all address
the same subcategory.  This lifts `TraceEdge.sameSub` along the reflexive
transitive closure, so an entire connected component of the trace graph carries
one common subterm — the formal content of "a trace piece tracks a single
metavariable". -/
theorem SameTraceComponent.sameSub {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ : Occurrence t} (h : SameTraceComponent o₁ o₂) :
    o₁.nodeCategory.subcategoryAt? o₁.categoryPath = o₂.nodeCategory.subcategoryAt? o₂.categoryPath := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans hstep.sameSub

/-! ## Invisible trace pieces

The paper's "invisible trace pieces" are connected components after deleting
visible vertices from the trace graph.  The older `SameTraceComponent` relation
is the full trace component; the relation below is the faithful invisible-only
variant used by the boundary and depth-counting arguments.
-/

/-- Trace edge restricted to invisible endpoints. -/
def InvisibleTraceEdge {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (o₁ o₂ : Occurrence t) : Prop :=
  o₁.Invisible ∧ o₂.Invisible ∧ TraceEdge o₁ o₂

@[grind =>]
theorem InvisibleTraceEdge.traceEdge {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ : Occurrence t} (h : InvisibleTraceEdge o₁ o₂) : TraceEdge o₁ o₂ :=
  h.2.2

@[grind =>]
theorem InvisibleTraceEdge.left_invisible {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ : Occurrence t} (h : InvisibleTraceEdge o₁ o₂) : o₁.Invisible :=
  h.1

@[grind =>]
theorem InvisibleTraceEdge.right_invisible {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ : Occurrence t} (h : InvisibleTraceEdge o₁ o₂) : o₂.Invisible :=
  h.2.1

@[grind =>]
theorem InvisibleTraceEdge.symm {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ : Occurrence t} (h : InvisibleTraceEdge o₁ o₂) : InvisibleTraceEdge o₂ o₁ :=
  ⟨h.right_invisible, h.left_invisible, h.traceEdge.symm⟩

/-- Same connected component in the invisible-only trace graph. -/
def SameInvisibleTraceComponent {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (o₁ o₂ : Occurrence t) : Prop :=
  Relation.ReflTransGen InvisibleTraceEdge o₁ o₂

namespace SameInvisibleTraceComponent

@[refl]
theorem refl {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (o : Occurrence t) : SameInvisibleTraceComponent o o :=
  Relation.ReflTransGen.refl

theorem trans {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ o₃ : Occurrence t}
    (h₁₂ : SameInvisibleTraceComponent o₁ o₂) (h₂₃ : SameInvisibleTraceComponent o₂ o₃) :
    SameInvisibleTraceComponent o₁ o₃ :=
  Relation.ReflTransGen.trans h₁₂ h₂₃

theorem symm {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ : Occurrence t} (h : SameInvisibleTraceComponent o₁ o₂) :
    SameInvisibleTraceComponent o₂ o₁ := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hpath hedge ih =>
      exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single hedge.symm) ih

/-- Forgetting invisible-only connectivity gives ordinary trace connectivity. -/
theorem toSameTraceComponent {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ : Occurrence t} (h : SameInvisibleTraceComponent o₁ o₂) :
    SameTraceComponent o₁ o₂ := by
  induction h with
  | refl => exact SameTraceComponent.refl _
  | tail _ hedge ih =>
      exact SameTraceComponent.trans ih (Relation.ReflTransGen.single hedge.traceEdge)

/-- Invisible pieces inherit the same-subcategory invariant of trace pieces. -/
theorem sameSub {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ : Occurrence t} (h : SameInvisibleTraceComponent o₁ o₂) :
    o₁.nodeCategory.subcategoryAt? o₁.categoryPath = o₂.nodeCategory.subcategoryAt? o₂.categoryPath :=
  h.toSameTraceComponent.sameSub

end SameInvisibleTraceComponent

/-- A visible boundary of an invisible trace piece: one invisible occurrence in
the piece is adjacent by a trace edge to a visible occurrence. -/
def HasVisibleBoundary {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (o : Occurrence t) : Prop :=
  ∃ p v : Occurrence t, SameInvisibleTraceComponent o p ∧ p.Invisible ∧ v.Visible ∧ TraceEdge p v

/-- Exact finite carrier for an invisible trace component: every member of the
component is among the executable finite occurrence enumeration of the tree.
This is the list-level finiteness fact used before the later trace-degree bound
turns visible boundaries into the `r * V` component count. -/
theorem sameInvisibleTraceComponent_mem_occurrences {Γ : List Category} {A : Category}
    {t : DerivationTree Γ A} {o p : Occurrence t}
    (_h : SameInvisibleTraceComponent o p) : p ∈ t.occurrences :=
  DerivationTree.occurrence_mem_occurrences p

/-! ## Interface states -/

/-- Slash kind of a constructor occurrence. -/
inductive SlashKind where
  | ldiv
  | rdiv
  deriving DecidableEq, Repr

/-- Coarse port kind used by the interface state `(ℓ, δ, π⁻, π⁺)` from the
paper.  The current computable approximation records whether the node is a
leaf/root, a unary child, or a binary left/right child. -/
inductive PortKind where
  | leaf
  | root
  | unaryIn
  | unaryOut
  | binaryLeft
  | binaryRight
  | binaryOut
  deriving DecidableEq, Repr

/-- The finite interface-state data used in the paper's repeatability test. -/
structure InterfaceState where
  slash : SlashKind
  branchDir : Bool
  lowerPort : PortKind
  upperPort : PortKind
  deriving DecidableEq, Repr

/-- Enumeration of all slash kinds. -/
def allSlashKinds : List SlashKind := [.ldiv, .rdiv]

/-- Enumeration of the two branch directions. -/
def allBranchDirs : List Bool := [false, true]

/-- Enumeration of all coarse port kinds. -/
def allPortKinds : List PortKind :=
  [.leaf, .root, .unaryIn, .unaryOut, .binaryLeft, .binaryRight, .binaryOut]

/-- Enumeration of all interface states. -/
def allInterfaceStates : List InterfaceState :=
  allSlashKinds.flatMap fun s =>
    allBranchDirs.flatMap fun d =>
      allPortKinds.flatMap fun lo =>
        allPortKinds.map fun hi =>
          { slash := s, branchDir := d, lowerPort := lo, upperPort := hi }

/-- Number of interface states in the finite enumeration. -/
def InterfaceStateCount : Nat := allInterfaceStates.length

set_option maxRecDepth 10000 in
theorem allInterfaceStates_nodup : allInterfaceStates.Nodup := by
  decide

namespace InterfaceState

/-- Finite code of an interface state, using its position in the explicit
duplicate-free enumeration. -/
def code (s : InterfaceState) (h : s ∈ allInterfaceStates) : Fin InterfaceStateCount :=
  ⟨allInterfaceStates.idxOf s, by
    simpa [InterfaceStateCount] using List.idxOf_lt_length_iff.mpr h⟩

theorem code_eq_iff {s₁ s₂ : InterfaceState}
    {h₁ : s₁ ∈ allInterfaceStates} {h₂ : s₂ ∈ allInterfaceStates} :
    code s₁ h₁ = code s₂ h₂ ↔ s₁ = s₂ := by
  constructor
  · intro h
    have hidx : allInterfaceStates.idxOf s₁ = allInterfaceStates.idxOf s₂ :=
      congrArg Fin.val h
    exact (List.idxOf_inj h₁).mp hidx
  · intro h
    subst h
    rfl

end InterfaceState

/-- Slash kind read from a category position.  Invalid positions cannot occur
for genuine occurrences, but defaulting keeps the state total and executable. -/
def slashKindAt (A : Category) (p : CategoryPath) : SlashKind :=
  match A.subcategoryAt? p with
  | some (_ ⧹ _) => .ldiv
  | some (_ ⧸ _) => .rdiv
  | _ => .rdiv

/-- The branch direction component.  A full branch-indexed interface state will
refine this; for now it records the next category-position direction when one
is available. -/
def branchDirAt (p : CategoryPath) : Bool :=
  match p with
  | [] => false
  | b :: _ => b

/-- Coarse node port computed from a node address. -/
def lowerPortAt {Γ : List Category} {A : Category} {t : DerivationTree Γ A} (o : Occurrence t) : PortKind :=
  match o.nodePath with
  | [] => .root
  | .unary :: _ => .unaryOut
  | .left :: _ => .binaryLeft
  | .right :: _ => .binaryRight

/-- Coarse consuming port computed from a node address. -/
def upperPortAt {Γ : List Category} {A : Category} {t : DerivationTree Γ A} (o : Occurrence t) : PortKind :=
  match o.nodePath with
  | [] => .root
  | .unary :: _ => .unaryIn
  | .left :: _ => .binaryOut
  | .right :: _ => .binaryOut

/-- The current computable interface state of an occurrence.  This replaces the
previous constant placeholder with data read from the actual slash occurrence
and its node address. -/
def interfaceState {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (o : Occurrence t) : InterfaceState :=
  { slash := slashKindAt o.nodeCategory o.categoryPath
    branchDir := branchDirAt o.categoryPath
    lowerPort := lowerPortAt o
    upperPort := upperPortAt o }

/-- The computed interface state is a member of the finite enumeration. -/
theorem interfaceState_mem_all {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (o : Occurrence t) : interfaceState o ∈ allInterfaceStates := by
  unfold interfaceState allInterfaceStates allSlashKinds allBranchDirs allPortKinds
  generalize slashKindAt o.nodeCategory o.categoryPath = sk
  generalize branchDirAt o.categoryPath = bd
  generalize lowerPortAt o = lo
  generalize upperPortAt o = hi
  cases sk <;> cases bd <;> cases lo <;> cases hi <;> decide

/-! ## size-minimal derivation trees (`D_min`) -/

/-- Among all derivation trees for a fixed derivable sequent there is one of
minimal size `size`.  This is the `D_min` of the paper: the object on which band
contraction is shown to have no repeatable pair.

The proof uses well-founded `Nat`-minimization over the (nonempty) family of
trees, witnessed by `Derivable.exists_derivationTree`. -/
theorem Derivable.exists_minimalDerivationTree {Γ : List Category} {A : Category} (h : Γ ⇒ccg A) :
    ∃ t : DerivationTree Γ A, ∀ t' : DerivationTree Γ A, t.size ≤ t'.size := by
  classical
  obtain ⟨t₀, _⟩ := h.exists_derivationTree
  -- The achievable size-values form a nonempty set of naturals; take its minimum.
  let P : Nat → Prop := fun n => ∃ t : DerivationTree Γ A, t.size = n
  have hP : ∃ n, P n := ⟨t₀.size, t₀, rfl⟩
  obtain ⟨tm, htm⟩ := Nat.find_spec hP
  refine ⟨tm, ?_⟩
  intro t'
  have hle : Nat.find hP ≤ t'.size := Nat.find_le ⟨t', rfl⟩
  omega

end Mathling.CCG
