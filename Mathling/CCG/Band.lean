module

public import Mathling.CCG.Atoms
public import Mathling.CCG.Trace
public import Mathlib.Data.Fintype.Card

@[expose] public section

/-!
# Contraction and boundary-free invisible-piece elimination

This module formalizes the contraction core of
`ccg_decidability_proof_3-1.pdf` used by the depth-counting argument in
`Mathling.CCG.Depth`.

We formalize contraction as a rewrite relation `Contracts` on explicit
derivation trees (`Mathling.CCG.Tree`):

* two **band redexes** that each delete one type-raising step feeding an
  application (`Contracts.collapseRight` / `collapseLeft`), and
* **congruence** closing the redexes under every tree context (the transport of
  a deletion through the derivation).

On top of the contraction relation the module develops:

* `Contracts.size_lt` — every contraction strictly decreases `size` — and the
  common exit object `ContractionWitness` (size decrease plus preservation of
  the problem-atom invariant);
* **invisible pieces** (`InvisiblePiece`, `BoundaryFree`,
  `InvisiblePiece.ProtectedSkeletonFree`) — finite carriers of invisible trace
  components, and `exists_boundaryFreeInvisiblePieceOfOccurrence` producing one
  from a boundaryless invisible occurrence;
* **replacement families** (`PieceReplacementTarget`,
  `PieceReplacementFamilyCore`, the `RewrittenTree` reconstruction) — the
  node-local atom-replacement machinery, culminating in the proved theorem
  `boundaryFreeReplaceableInvisiblePieceContractsFromPieces`: every
  boundary-free, protected-skeleton-free invisible piece yields a
  `ContractionWitness`;
* the **open protected-skeleton case**: the named Prop
  `BoundaryFreeProtectedSkeletonPieceContracts` together with the case split
  `boundaryFreeInvisiblePieceContractsFromPieces_of_replaceable_or_protected`
  recovering the full boundary-free target from the replaceable case plus the
  protected case;
* the `ProtectedSkeletonCounterexample` namespace — a concrete tree showing
  that protected unary-skeleton occurrences cannot be dispatched by a blanket
  visible-boundary lemma and must be handled by band contraction;
* a worked example (`Example`) of the paper's `long ↝ short` contraction.
-/

set_option linter.style.longLine false
set_option linter.unnecessarySimpa false

namespace Mathling.CCG

open Category

namespace DerivationContext

/-- Descend from a context whose hole contains a forward type-raising node to
the child of that local node.  This is the context needed for recursive
rewriting under `T>`. -/
def inTypeRaiseRight
    {Γ Ω : List Category} {A C Z : Category}
    (ctx : DerivationContext Γ (C ⧸ (A ⧹ C)) Ω Z) :
    DerivationContext Γ A Ω Z where
  plug := fun t => ctx.plug (DerivationTree.typeRaiseRight C t)
  nodePrefix := ctx.nodePrefix ++ [.unary]
  liftOccurrence := fun {t} o =>
    ctx.liftOccurrence
      (DerivationTree.CategoryOccurrence.underUnaryRight C o)
  liftOccurrence_nodePath := by
    intro t o
    rw [ctx.liftOccurrence_nodePath]
    simp [DerivationTree.CategoryOccurrence.underUnaryRight, List.append_assoc]
  liftOccurrence_nodeCategory := by
    intro t o
    rw [ctx.liftOccurrence_nodeCategory]
    rfl
  liftOccurrence_categoryPath := by
    intro t o
    rw [ctx.liftOccurrence_categoryPath]
    rfl
  categoryAt?_local := by
    intro t p D h
    have hlocal :
        (DerivationTree.typeRaiseRight C t).categoryAt? (.unary :: p) = some D := by
      simpa [DerivationTree.categoryAt?] using h
    simpa [List.append_assoc] using ctx.categoryAt?_local hlocal
  categoryAt?_reflect := by
    intro t p D h
    have hlocal :
        (DerivationTree.typeRaiseRight C t).categoryAt? (.unary :: p) = some D := by
      have h' := ctx.categoryAt?_reflect (t := DerivationTree.typeRaiseRight C t)
        (p := .unary :: p) (C := D) (by simpa [List.append_assoc] using h)
      simpa [DerivationTree.categoryAt?] using h'
    simpa [DerivationTree.categoryAt?] using hlocal
  liftLeafNode := by
    intro t p h
    have hlocal :
        (DerivationTree.typeRaiseRight C t).isLeafNode (.unary :: p) := by
      simpa [DerivationTree.isLeafNode] using h
    simpa [List.append_assoc] using ctx.liftLeafNode hlocal
  liftPrincipalConstructor := by
    intro t p cpos h
    simpa [List.append_assoc] using
      ctx.liftPrincipalConstructor
        (DerivationTree.PrincipalConstructor.underUnaryRight C h)
  liftUnarySkeletonConstructor := by
    intro t p cpos h
    simpa [List.append_assoc] using
      ctx.liftUnarySkeletonConstructor
        (DerivationTree.UnarySkeletonConstructor.underUnaryRight C h)
  liftTraceEdge := by
    intro t o₁ o₂ h
    exact ctx.liftTraceEdge (TraceEdge.underUnaryRight C h)

/-- Descend from a context whose hole contains a backward type-raising node to
the child of that local node. -/
def inTypeRaiseLeft
    {Γ Ω : List Category} {A C Z : Category}
    (ctx : DerivationContext Γ ((C ⧸ A) ⧹ C) Ω Z) :
    DerivationContext Γ A Ω Z where
  plug := fun t => ctx.plug (DerivationTree.typeRaiseLeft C t)
  nodePrefix := ctx.nodePrefix ++ [.unary]
  liftOccurrence := fun {t} o =>
    ctx.liftOccurrence
      (DerivationTree.CategoryOccurrence.underUnaryLeft C o)
  liftOccurrence_nodePath := by
    intro t o
    rw [ctx.liftOccurrence_nodePath]
    simp [DerivationTree.CategoryOccurrence.underUnaryLeft, List.append_assoc]
  liftOccurrence_nodeCategory := by
    intro t o
    rw [ctx.liftOccurrence_nodeCategory]
    rfl
  liftOccurrence_categoryPath := by
    intro t o
    rw [ctx.liftOccurrence_categoryPath]
    rfl
  categoryAt?_local := by
    intro t p D h
    have hlocal :
        (DerivationTree.typeRaiseLeft C t).categoryAt? (.unary :: p) = some D := by
      simpa [DerivationTree.categoryAt?] using h
    simpa [List.append_assoc] using ctx.categoryAt?_local hlocal
  categoryAt?_reflect := by
    intro t p D h
    have hlocal :
        (DerivationTree.typeRaiseLeft C t).categoryAt? (.unary :: p) = some D := by
      have h' := ctx.categoryAt?_reflect (t := DerivationTree.typeRaiseLeft C t)
        (p := .unary :: p) (C := D) (by simpa [List.append_assoc] using h)
      simpa [DerivationTree.categoryAt?] using h'
    simpa [DerivationTree.categoryAt?] using hlocal
  liftLeafNode := by
    intro t p h
    have hlocal :
        (DerivationTree.typeRaiseLeft C t).isLeafNode (.unary :: p) := by
      simpa [DerivationTree.isLeafNode] using h
    simpa [List.append_assoc] using ctx.liftLeafNode hlocal
  liftPrincipalConstructor := by
    intro t p cpos h
    simpa [List.append_assoc] using
      ctx.liftPrincipalConstructor
        (DerivationTree.PrincipalConstructor.underUnaryLeft C h)
  liftUnarySkeletonConstructor := by
    intro t p cpos h
    simpa [List.append_assoc] using
      ctx.liftUnarySkeletonConstructor
        (DerivationTree.UnarySkeletonConstructor.underUnaryLeft C h)
  liftTraceEdge := by
    intro t o₁ o₂ h
    exact ctx.liftTraceEdge (TraceEdge.underUnaryLeft C h)

/-- Descend from a context whose hole contains a binary node to that node's
left premise. -/
def inBinaryLeft
    {Γ Δ Ω : List Category} {A B C Z : Category}
    (ctx : DerivationContext (Γ ++ Δ) C Ω Z)
    (right : DerivationTree Δ B) (r : Rule A B C) :
    DerivationContext Γ A Ω Z where
  plug := fun t => ctx.plug (DerivationTree.binary t right r)
  nodePrefix := ctx.nodePrefix ++ [.left]
  liftOccurrence := fun {t} o =>
    ctx.liftOccurrence
      (DerivationTree.CategoryOccurrence.underBinaryLeft (t₂ := right) r o)
  liftOccurrence_nodePath := by
    intro t o
    rw [ctx.liftOccurrence_nodePath]
    simp [DerivationTree.CategoryOccurrence.underBinaryLeft, List.append_assoc]
  liftOccurrence_nodeCategory := by
    intro t o
    rw [ctx.liftOccurrence_nodeCategory]
    rfl
  liftOccurrence_categoryPath := by
    intro t o
    rw [ctx.liftOccurrence_categoryPath]
    rfl
  categoryAt?_local := by
    intro t p D h
    have hlocal :
        (DerivationTree.binary t right r).categoryAt? (.left :: p) = some D := by
      simpa [DerivationTree.categoryAt?] using h
    simpa [List.append_assoc] using ctx.categoryAt?_local hlocal
  categoryAt?_reflect := by
    intro t p D h
    have hlocal :
        (DerivationTree.binary t right r).categoryAt? (.left :: p) = some D := by
      have h' := ctx.categoryAt?_reflect (t := DerivationTree.binary t right r)
        (p := .left :: p) (C := D) (by simpa [List.append_assoc] using h)
      simpa [DerivationTree.categoryAt?] using h'
    simpa [DerivationTree.categoryAt?] using hlocal
  liftLeafNode := by
    intro t p h
    have hlocal :
        (DerivationTree.binary t right r).isLeafNode (.left :: p) := by
      simpa [DerivationTree.isLeafNode] using h
    simpa [List.append_assoc] using ctx.liftLeafNode hlocal
  liftPrincipalConstructor := by
    intro t p cpos h
    simpa [List.append_assoc] using
      ctx.liftPrincipalConstructor
        (DerivationTree.PrincipalConstructor.underBinaryLeft (t₂ := right) r h)
  liftUnarySkeletonConstructor := by
    intro t p cpos h
    simpa [List.append_assoc] using
      ctx.liftUnarySkeletonConstructor
        (DerivationTree.UnarySkeletonConstructor.underBinaryLeft (t₂ := right) r h)
  liftTraceEdge := by
    intro t o₁ o₂ h
    exact ctx.liftTraceEdge
      (TraceEdge.underBinaryLeft (t₂ := right) r h)

/-- Descend from a context whose hole contains a binary node to that node's
right premise. -/
def inBinaryRight
    {Γ Δ Ω : List Category} {A B C Z : Category}
    (ctx : DerivationContext (Γ ++ Δ) C Ω Z)
    (left : DerivationTree Γ A) (r : Rule A B C) :
    DerivationContext Δ B Ω Z where
  plug := fun t => ctx.plug (DerivationTree.binary left t r)
  nodePrefix := ctx.nodePrefix ++ [.right]
  liftOccurrence := fun {t} o =>
    ctx.liftOccurrence
      (DerivationTree.CategoryOccurrence.underBinaryRight (t₁ := left) r o)
  liftOccurrence_nodePath := by
    intro t o
    rw [ctx.liftOccurrence_nodePath]
    simp [DerivationTree.CategoryOccurrence.underBinaryRight, List.append_assoc]
  liftOccurrence_nodeCategory := by
    intro t o
    rw [ctx.liftOccurrence_nodeCategory]
    rfl
  liftOccurrence_categoryPath := by
    intro t o
    rw [ctx.liftOccurrence_categoryPath]
    rfl
  categoryAt?_local := by
    intro t p D h
    have hlocal :
        (DerivationTree.binary left t r).categoryAt? (.right :: p) = some D := by
      simpa [DerivationTree.categoryAt?] using h
    simpa [List.append_assoc] using ctx.categoryAt?_local hlocal
  categoryAt?_reflect := by
    intro t p D h
    have hlocal :
        (DerivationTree.binary left t r).categoryAt? (.right :: p) = some D := by
      have h' := ctx.categoryAt?_reflect (t := DerivationTree.binary left t r)
        (p := .right :: p) (C := D) (by simpa [List.append_assoc] using h)
      simpa [DerivationTree.categoryAt?] using h'
    simpa [DerivationTree.categoryAt?] using hlocal
  liftLeafNode := by
    intro t p h
    have hlocal :
        (DerivationTree.binary left t r).isLeafNode (.right :: p) := by
      simpa [DerivationTree.isLeafNode] using h
    simpa [List.append_assoc] using ctx.liftLeafNode hlocal
  liftPrincipalConstructor := by
    intro t p cpos h
    simpa [List.append_assoc] using
      ctx.liftPrincipalConstructor
        (DerivationTree.PrincipalConstructor.underBinaryRight (t₁ := left) r h)
  liftUnarySkeletonConstructor := by
    intro t p cpos h
    simpa [List.append_assoc] using
      ctx.liftUnarySkeletonConstructor
        (DerivationTree.UnarySkeletonConstructor.underBinaryRight (t₁ := left) r h)
  liftTraceEdge := by
    intro t o₁ o₂ h
    exact ctx.liftTraceEdge
      (TraceEdge.underBinaryRight (t₁ := left) r h)

end DerivationContext

/-- Every node category of `t` uses only atoms from the original recognition
problem.  This lives at the contraction layer because contraction witnesses
must preserve exactly this invariant before the depth-counting layer can use
minimality. -/
def DerivationTree.NodeCategoriesUseProblemAtoms {Γ : List Category} {A : Category}
    (t : DerivationTree Γ A) : Prop :=
  ∀ B ∈ t.nodeCategories, ∀ name ∈ B.atoms, name ∈ problemAtomNames Γ A

/-- Common exit object for every contraction argument.  The target has the same
typed sequent by construction; the witness additionally records strict size
decrease and preservation of the problem-atom invariant used by minimality. -/
structure ContractionWitness {Γ : List Category} {A : Category}
    (t : DerivationTree Γ A) where
  target : DerivationTree Γ A
  size_lt : target.size < t.size
  preserves_problem_atoms :
    t.NodeCategoriesUseProblemAtoms → target.NodeCategoriesUseProblemAtoms

/-- The band-contraction rewrite relation on explicit derivation trees.

`Contracts t t'` means `t` reduces to `t'` by deleting one transport-closed
type-raising segment.  Because both sides share the leaves `Γ` and root `A`,
contraction preserves the derived sequent by construction. -/
inductive Contracts : {Γ : List Category} → {A : Category} → DerivationTree Γ A → DerivationTree Γ A → Prop where
  /-- Forward band redex: a forward type raising feeding a forward application,
  `(T>) then (>)`, collapses to a backward application `(<)`.
  Concretely `appRight (typeRaiseRight C s) w` ↝ `appLeft s w`, deleting the
  introduced layer `C/([·]\C)`. -/
  | collapseRight {Γ Δ : List Category} {A C : Category}
      (s : DerivationTree Γ A) (w : DerivationTree Δ (A ⧹ C)) :
      Contracts
        (DerivationTree.binary (DerivationTree.typeRaiseRight C s) w Rule.appRight)
        (DerivationTree.binary s w Rule.appLeft)
  /-- Backward band redex: a backward type raising feeding a backward
  application, `(T<) then (<)`, collapses to a forward application `(>)`.
  Concretely `appLeft w (typeRaiseLeft C s)` ↝ `appRight w s`. -/
  | collapseLeft {Γ Δ : List Category} {A C : Category}
      (w : DerivationTree Δ (C ⧸ A)) (s : DerivationTree Γ A) :
      Contracts
        (DerivationTree.binary w (DerivationTree.typeRaiseLeft C s) Rule.appLeft)
        (DerivationTree.binary w s Rule.appRight)
  /-- Congruence: contraction under a left type-raising context. -/
  | typeRaiseRight {Γ : List Category} {A : Category} (C : Category) {s s' : DerivationTree Γ A}
      (h : Contracts s s') :
      Contracts (DerivationTree.typeRaiseRight C s) (DerivationTree.typeRaiseRight C s')
  /-- Congruence: contraction under a right type-raising context. -/
  | typeRaiseLeft {Γ : List Category} {A : Category} (C : Category) {s s' : DerivationTree Γ A}
      (h : Contracts s s') :
      Contracts (DerivationTree.typeRaiseLeft C s) (DerivationTree.typeRaiseLeft C s')
  /-- Congruence: contraction in the left premise of a binary rule. -/
  | binaryLeft {Γ Δ : List Category} {A B C : Category}
      {t₁ t₁' : DerivationTree Γ A} (t₂ : DerivationTree Δ B) (r : Rule A B C)
      (h : Contracts t₁ t₁') :
      Contracts (DerivationTree.binary t₁ t₂ r) (DerivationTree.binary t₁' t₂ r)
  /-- Congruence: contraction in the right premise of a binary rule. -/
  | binaryRight {Γ Δ : List Category} {A B C : Category}
      (t₁ : DerivationTree Γ A) {t₂ t₂' : DerivationTree Δ B} (r : Rule A B C)
      (h : Contracts t₂ t₂') :
      Contracts (DerivationTree.binary t₁ t₂ r) (DerivationTree.binary t₁ t₂' r)

namespace Contracts

/-- Every contraction strictly decreases the constructor-occurrence measure `size`.
This is the paper's `size(D/B) < size(D)` (Lemma `band-correct`). -/
theorem size_lt {Γ : List Category} {A : Category} {t t' : DerivationTree Γ A} (h : Contracts t t') :
    t'.size < t.size := by
  induction h with
  | collapseRight s w =>
      -- the deleted layer `C/(A\C)` carries at least one constructor
      simp only [DerivationTree.size_binary, DerivationTree.size_typeRaiseRight, Category.constructors]
      omega
  | collapseLeft w s =>
      simp only [DerivationTree.size_binary, DerivationTree.size_typeRaiseLeft, Category.constructors]
      omega
  | typeRaiseRight C h ih =>
      simp only [DerivationTree.size_typeRaiseRight]; omega
  | typeRaiseLeft C h ih =>
      simp only [DerivationTree.size_typeRaiseLeft]; omega
  | binaryLeft t₂ r h ih =>
      simp only [DerivationTree.size_binary]; omega
  | binaryRight t₁ r h ih =>
      simp only [DerivationTree.size_binary]; omega

/-- Band contraction does not introduce new node categories, hence it preserves
any fixed atom-set invariant over all node categories. -/
theorem preserves_nodeCategoriesUseOnlyAtoms
    {atomNames : List String} {Γ : List Category} {A : Category}
    {t t' : DerivationTree Γ A} (h : Contracts t t') :
    (∀ B ∈ t.nodeCategories, UsesOnlyAtoms atomNames B) →
      ∀ B ∈ t'.nodeCategories, UsesOnlyAtoms atomNames B := by
  induction h with
  | collapseRight s w =>
      intro hatoms B hB name hname
      exact hatoms B (by
        simp only [DerivationTree.nodeCategories_binary,
          DerivationTree.nodeCategories_typeRaiseRight, List.mem_cons,
          List.mem_append] at hB ⊢
        aesop) name hname
  | collapseLeft w s =>
      intro hatoms B hB name hname
      exact hatoms B (by
        simp only [DerivationTree.nodeCategories_binary,
          DerivationTree.nodeCategories_typeRaiseLeft, List.mem_cons,
          List.mem_append] at hB ⊢
        aesop) name hname
  | typeRaiseRight C h ih =>
      intro hatoms B hB name hname
      simp only [DerivationTree.nodeCategories_typeRaiseRight, List.mem_cons] at hB
      rcases hB with hB | hB
      · exact hatoms B (by simpa [DerivationTree.nodeCategories_typeRaiseRight, hB]) name hname
      · exact ih (by
          intro X hX
          exact hatoms X (by simp [DerivationTree.nodeCategories_typeRaiseRight, hX])) B hB name hname
  | typeRaiseLeft C h ih =>
      intro hatoms B hB name hname
      simp only [DerivationTree.nodeCategories_typeRaiseLeft, List.mem_cons] at hB
      rcases hB with hB | hB
      · exact hatoms B (by simpa [DerivationTree.nodeCategories_typeRaiseLeft, hB]) name hname
      · exact ih (by
          intro X hX
          exact hatoms X (by simp [DerivationTree.nodeCategories_typeRaiseLeft, hX])) B hB name hname
  | binaryLeft t₂ r h ih =>
      intro hatoms B hB name hname
      simp only [DerivationTree.nodeCategories_binary, List.mem_cons, List.mem_append] at hB
      rcases hB with hB | hB | hB
      · exact hatoms B (by simpa [DerivationTree.nodeCategories_binary, hB]) name hname
      · exact ih (by
          intro X hX
          exact hatoms X (by simp [DerivationTree.nodeCategories_binary, hX])) B hB name hname
      · exact hatoms B (by simp [DerivationTree.nodeCategories_binary, hB]) name hname
  | binaryRight t₁ r h ih =>
      intro hatoms B hB name hname
      simp only [DerivationTree.nodeCategories_binary, List.mem_cons, List.mem_append] at hB
      rcases hB with hB | hB | hB
      · exact hatoms B (by simpa [DerivationTree.nodeCategories_binary, hB]) name hname
      · exact hatoms B (by simp [DerivationTree.nodeCategories_binary, hB]) name hname
      · exact ih (by
          intro X hX
          exact hatoms X (by simp [DerivationTree.nodeCategories_binary, hX])) B hB name hname

/-- Band contraction preserves the property that every node category uses only
atoms from the original recognition problem. -/
theorem preserves_nodeCategoriesUseProblemAtoms
    {Γ : List Category} {A : Category} {t t' : DerivationTree Γ A}
    (h : Contracts t t') :
    t.NodeCategoriesUseProblemAtoms → t'.NodeCategoriesUseProblemAtoms := by
  exact h.preserves_nodeCategoriesUseOnlyAtoms

end Contracts

/-- Strict prefix relation between category positions along one root-to-leaf
branch.  `s.StrictPrefix t` means that `s` is a proper ancestor of `t`. -/
def CategoryPath.StrictPrefix (s t : CategoryPath) : Prop :=
  ∃ rest : CategoryPath, rest ≠ [] ∧ t = s ++ rest

/-- Non-strict prefix relation between category positions along one branch. -/
def CategoryPath.Prefix (s t : CategoryPath) : Prop :=
  ∃ rest : CategoryPath, t = s ++ rest

/-- Two category positions overlap when one is a prefix of the other. -/
def CategoryPath.Overlaps (p q : CategoryPath) : Prop :=
  p.Prefix q ∨ q.Prefix p

/-- Two category positions are disjoint when neither is a prefix of the other. -/
def CategoryPath.Disjoint (p q : CategoryPath) : Prop :=
  ¬ p.Overlaps q

/-- Pairwise disjointness for category-level replacement positions. -/
def CategoryReplacementTargetsDisjoint (targets : List (CategoryPath × Category)) : Prop :=
  ∀ target₁ ∈ targets, ∀ target₂ ∈ targets,
    target₁.1 ≠ target₂.1 → target₁.1.Disjoint target₂.1

@[refl]
theorem CategoryPath.Prefix.refl (s : CategoryPath) : s.Prefix s :=
  ⟨[], by simp⟩

theorem CategoryPath.Prefix.trans {p q r : CategoryPath}
    (hpq : p.Prefix q) (hqr : q.Prefix r) : p.Prefix r := by
  obtain ⟨u, rfl⟩ := hpq
  obtain ⟨v, rfl⟩ := hqr
  exact ⟨u ++ v, by simp [List.append_assoc]⟩

theorem CategoryPath.Prefix.cons (b : Bool) {p q : CategoryPath}
    (h : p.Prefix q) : CategoryPath.Prefix (b :: p) (b :: q) := by
  obtain ⟨rest, hq⟩ := h
  exact ⟨rest, by simp [hq]⟩

theorem CategoryPath.Disjoint.tail_of_cons_same
    {b : Bool} {p q : CategoryPath}
    (h : CategoryPath.Disjoint (b :: p) (b :: q)) : p.Disjoint q := by
  intro hoverlap
  apply h
  rcases hoverlap with hpq | hqp
  · exact Or.inl (CategoryPath.Prefix.cons b hpq)
  · exact Or.inr (CategoryPath.Prefix.cons b hqp)

theorem CategoryPath.Disjoint.symm {p q : CategoryPath}
    (h : p.Disjoint q) : q.Disjoint p := by
  intro hoverlap
  apply h
  rcases hoverlap with hqp | hpq
  · exact Or.inr hqp
  · exact Or.inl hpq

theorem CategoryPath.Prefix.strict_of_ne {p q : CategoryPath}
    (hpq : p.Prefix q) (hne : p ≠ q) : p.StrictPrefix q := by
  obtain ⟨rest, hq⟩ := hpq
  refine ⟨rest, ?_, hq⟩
  intro hrest
  apply hne
  simp [hq, hrest]

/-- All prefixes of one category path, ordered from the root prefix to the path
itself.  This is the executable branch spine used by the depth-counting
argument. -/
def CategoryPath.prefixes : CategoryPath → List CategoryPath
  | [] => [[]]
  | b :: p => [] :: (CategoryPath.prefixes p).map fun q => b :: q

@[simp]
theorem CategoryPath.prefixes_nil : CategoryPath.prefixes [] = [[]] := rfl

@[simp]
theorem CategoryPath.prefixes_cons (b : Bool) (p : CategoryPath) :
    CategoryPath.prefixes (b :: p) =
      [] :: ((CategoryPath.prefixes p).map fun q => b :: q) := rfl

/-- The prefix spine of `p` has exactly `p.length + 1` nodes. -/
theorem CategoryPath.length_prefixes : ∀ p : CategoryPath,
    (CategoryPath.prefixes p).length = p.length + 1
  | [] => by simp
  | _ :: p => by
      simp [CategoryPath.length_prefixes p]

/-- The endpoint path is a member of its own prefix spine. -/
theorem CategoryPath.self_mem_prefixes : ∀ p : CategoryPath, p ∈ CategoryPath.prefixes p
  | [] => by simp
  | b :: p => by
      simp [CategoryPath.self_mem_prefixes p]

/-- Every listed prefix is a genuine non-strict prefix of the endpoint path. -/
theorem CategoryPath.mem_prefixes_prefix :
    ∀ {q p : CategoryPath}, q ∈ CategoryPath.prefixes p → q.Prefix p
  | q, [], h => by
      simp only [CategoryPath.prefixes_nil, List.mem_singleton] at h
      subst q
      exact CategoryPath.Prefix.refl []
  | q, b :: p, h => by
      simp only [CategoryPath.prefixes_cons, List.mem_cons, List.mem_map] at h
      rcases h with hq | ⟨r, hr, rfl⟩
      · subst q
        exact ⟨b :: p, by simp⟩
      · obtain ⟨rest, hrest⟩ := CategoryPath.mem_prefixes_prefix hr
        exact ⟨rest, by simp [hrest]⟩

/-- The executable prefix spine contains every non-strict prefix. -/
theorem CategoryPath.mem_prefixes_of_prefix :
    ∀ {q p : CategoryPath}, q.Prefix p → q ∈ CategoryPath.prefixes p
  | [], p, _h => by
      cases p <;> simp
  | _ :: _, [], h => by
      obtain ⟨rest, hp⟩ := h
      simp at hp
  | bq :: q, bp :: p, h => by
      obtain ⟨rest, hp⟩ := h
      cases bp <;> cases bq
      · simp only [CategoryPath.prefixes_cons, List.mem_cons, List.mem_map]
        right
        refine ⟨q, ?_, rfl⟩
        apply CategoryPath.mem_prefixes_of_prefix
        exact ⟨rest, by simpa using hp⟩
      · simp at hp
      · simp at hp
      · simp only [CategoryPath.prefixes_cons, List.mem_cons, List.mem_map]
        right
        refine ⟨q, ?_, rfl⟩
        apply CategoryPath.mem_prefixes_of_prefix
        exact ⟨rest, by simpa using hp⟩

/-- Prefixes of one branch are comparable. -/
theorem CategoryPath.mem_prefixes_comparable :
    ∀ {q r p : CategoryPath}, q ∈ CategoryPath.prefixes p →
      r ∈ CategoryPath.prefixes p → q.Prefix r ∨ r.Prefix q
  | q, r, [], hq, hr => by
      simp only [CategoryPath.prefixes_nil, List.mem_singleton] at hq hr
      subst q
      subst r
      exact Or.inl (CategoryPath.Prefix.refl [])
  | q, r, b :: p, hq, hr => by
      simp only [CategoryPath.prefixes_cons, List.mem_cons, List.mem_map] at hq hr
      rcases hq with hq | hq
      · subst q
        exact Or.inl ⟨r, by simp⟩
      rcases hr with hr | hr
      · subst r
        exact Or.inr ⟨q, by simp⟩
      obtain ⟨q', hq', rfl⟩ := hq
      obtain ⟨r', hr', rfl⟩ := hr
      rcases CategoryPath.mem_prefixes_comparable hq' hr' with h | h
      · obtain ⟨rest, hrest⟩ := h
        exact Or.inl ⟨rest, by simp [hrest]⟩
      · obtain ⟨rest, hrest⟩ := h
        exact Or.inr ⟨rest, by simp [hrest]⟩

/-- Prefix spines contain no duplicate positions. -/
theorem CategoryPath.prefixes_nodup : ∀ p : CategoryPath, (CategoryPath.prefixes p).Nodup
  | [] => by simp
  | b :: p => by
      have ih := CategoryPath.prefixes_nodup p
      simp only [CategoryPath.prefixes_cons]
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        rcases List.mem_map.mp hmem with ⟨q, _hq, hqeq⟩
        cases hqeq
      · exact List.Nodup.map (f := fun q : CategoryPath => b :: q) (by
          intro q₁ q₂ h
          simpa using h) ih

namespace Category

/-- Constructor-position lists are closed upward along a branch: every prefix of
a constructor position is again a constructor position. -/
theorem constructorPositions_prefix_closed :
    ∀ (C : Category) {p q : CategoryPath},
      p ∈ C.constructorPositions → q ∈ CategoryPath.prefixes p →
        q ∈ C.constructorPositions
  | # _, p, _q, hp, _hq => by
      simp at hp
  | L ⧹ R, p, q, hp, hq => by
      simp only [Category.constructorPositions_ldiv, List.mem_cons, List.mem_append,
        List.mem_map] at hp
      rcases hp with hp | ⟨pL, hpL, rfl⟩ | ⟨pR, hpR, rfl⟩
      · subst p
        simp only [CategoryPath.prefixes_nil, List.mem_singleton] at hq
        subst q
        simp [Category.constructorPositions_ldiv]
      · simp only [CategoryPath.prefixes_cons, List.mem_cons, List.mem_map] at hq
        rcases hq with hq | ⟨qL, hqL, rfl⟩
        · subst q
          simp [Category.constructorPositions_ldiv]
        · have hclosed := constructorPositions_prefix_closed L hpL hqL
          simp [Category.constructorPositions_ldiv, hclosed]
      · simp only [CategoryPath.prefixes_cons, List.mem_cons, List.mem_map] at hq
        rcases hq with hq | ⟨qR, hqR, rfl⟩
        · subst q
          simp [Category.constructorPositions_ldiv]
        · have hclosed := constructorPositions_prefix_closed R hpR hqR
          simp [Category.constructorPositions_ldiv, hclosed]
  | L ⧸ R, p, q, hp, hq => by
      simp only [Category.constructorPositions_rdiv, List.mem_cons, List.mem_append,
        List.mem_map] at hp
      rcases hp with hp | ⟨pL, hpL, rfl⟩ | ⟨pR, hpR, rfl⟩
      · subst p
        simp only [CategoryPath.prefixes_nil, List.mem_singleton] at hq
        subst q
        simp [Category.constructorPositions_rdiv]
      · simp only [CategoryPath.prefixes_cons, List.mem_cons, List.mem_map] at hq
        rcases hq with hq | ⟨qL, hqL, rfl⟩
        · subst q
          simp [Category.constructorPositions_rdiv]
        · have hclosed := constructorPositions_prefix_closed L hpL hqL
          simp [Category.constructorPositions_rdiv, hclosed]
      · simp only [CategoryPath.prefixes_cons, List.mem_cons, List.mem_map] at hq
        rcases hq with hq | ⟨qR, hqR, rfl⟩
        · subst q
          simp [Category.constructorPositions_rdiv]
        · have hclosed := constructorPositions_prefix_closed R hpR hqR
          simp [Category.constructorPositions_rdiv, hclosed]

end Category

/-- A strict prefix is in particular a non-strict prefix. -/
theorem CategoryPath.StrictPrefix.prefix {s t : CategoryPath}
    (h : s.StrictPrefix t) : s.Prefix t := by
  obtain ⟨rest, _hrest, ht⟩ := h
  exact ⟨rest, ht⟩

/-! ## Boundary-free invisible pieces and replacement families -/

/-- A finite carrier for one invisible trace piece.  It is represented as a
list of invisible occurrences, connected in the invisible-only trace graph and
closed under invisible trace edges. -/
structure InvisiblePiece {Γ : List Category} {A : Category}
    (t : DerivationTree Γ A) where
  carrier : List (Occurrence t)
  nonempty : carrier ≠ []
  all_invisible : ∀ o : Occurrence t, o ∈ carrier → o.Invisible
  connected :
    ∀ o₁ : Occurrence t, o₁ ∈ carrier →
      ∀ o₂ : Occurrence t, o₂ ∈ carrier →
        SameInvisibleTraceComponent o₁ o₂
  closed :
    ∀ o₁ : Occurrence t, o₁ ∈ carrier →
      ∀ o₂ : Occurrence t, InvisibleTraceEdge o₁ o₂ → o₂ ∈ carrier

/-- A piece is boundary-free when no invisible occurrence in its carrier has a
trace edge to a visible occurrence. -/
def BoundaryFree {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (P : InvisiblePiece t) : Prop :=
  ∀ o : Occurrence t, o ∈ P.carrier →
    ∀ v : Occurrence t, v.Visible → ¬ TraceEdge o v

namespace InvisiblePiece

/-- A piece is safe for the current node-local atom-replacement construction
only when it contains no constructor introduced as a unary type-raising
skeleton.

This predicate records the architectural blocker explicitly.  A protected
skeleton such as the inner `\` in `C/(A\C)` cannot be replaced by an atom at the
type-raising output node without destroying the local rule shape.  Such pieces
must instead be ruled out by a separate argument, or handled by band
contraction. -/
def ProtectedSkeletonFree
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (P : InvisiblePiece t) : Prop :=
  ∀ o : Occurrence t, o ∈ P.carrier → ¬ o.ProtectedUnarySkeleton

/-- Boundary-freeness upgrades invisible-edge closure to full trace-edge
closure: an edge from the piece cannot leave through a visible endpoint, and if
the other endpoint is invisible then it is included by `P.closed`. -/
theorem closed_traceEdge_of_boundaryFree
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (P : InvisiblePiece t) (hfree : BoundaryFree P)
    {o₁ o₂ : Occurrence t} (ho₁ : o₁ ∈ P.carrier)
    (hedge : TraceEdge o₁ o₂) :
    o₂ ∈ P.carrier := by
  have hinv₁ : o₁.Invisible := P.all_invisible o₁ ho₁
  by_cases hvis₂ : o₂.Visible
  · exact False.elim (hfree o₁ ho₁ o₂ hvis₂ hedge)
  · exact P.closed o₁ ho₁ o₂ ⟨hinv₁, hvis₂, hedge⟩

end InvisiblePiece

/-- Every recognition problem has at least one problem atom, namely an atom
from the goal category. -/
theorem exists_mem_problemAtomNames_goal
    (Γ : List Category) (A : Category) :
    ∃ atomName, atomName ∈ problemAtomNames Γ A := by
  obtain ⟨atomName, hatom⟩ := A.exists_mem_atoms
  exact ⟨atomName, mem_problemAtomNames_of_mem_goal hatom⟩

/-- If the generating invisible occurrence has no visible boundary, the finite
invisible component containing it is boundary-free. -/
theorem exists_boundaryFreeInvisiblePieceOfOccurrence
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (o : Occurrence t) (hinv : o.Invisible) (hnoBoundary : ¬ HasVisibleBoundary o) :
    ∃ P : InvisiblePiece t, o ∈ P.carrier ∧ BoundaryFree P := by
  classical
  let carrier : List (Occurrence t) :=
    t.occurrences.filter
      (fun p => decide (SameInvisibleTraceComponent o p ∧ p.Invisible))
  have hcarrier_data :
      ∀ p : Occurrence t, p ∈ carrier →
        SameInvisibleTraceComponent o p ∧ p.Invisible := by
    intro p hp
    exact of_decide_eq_true (List.mem_filter.mp hp).2
  have hself : o ∈ carrier := by
    exact List.mem_filter.mpr
      ⟨DerivationTree.occurrence_mem_occurrences o, by
        simp [SameInvisibleTraceComponent.refl o, hinv]⟩
  let P : InvisiblePiece t := {
    carrier := carrier
    nonempty := by
      intro hnil
      rw [hnil] at hself
      cases hself
    all_invisible := by
      intro p hp
      exact (hcarrier_data p hp).2
    connected := by
      intro p hp q hq
      exact SameInvisibleTraceComponent.trans
        (SameInvisibleTraceComponent.symm (hcarrier_data p hp).1)
        (hcarrier_data q hq).1
    closed := by
      intro p hp q hedge
      have hcomp : SameInvisibleTraceComponent o q :=
        SameInvisibleTraceComponent.trans (hcarrier_data p hp).1
          (Relation.ReflTransGen.single hedge)
      exact List.mem_filter.mpr
        ⟨DerivationTree.occurrence_mem_occurrences q, by
          simp [hcomp, hedge.right_invisible]⟩
  }
  refine ⟨P, hself, ?_⟩
  intro p hp v hvis hedge
  exact hnoBoundary ⟨p, v, (hcarrier_data p hp).1, (hcarrier_data p hp).2, hvis, hedge⟩

namespace Category

/-- If a category position can be read, then replacing the subcategory at that
position succeeds.  This is the small totality fact needed when turning
occurrence-indexed replacement targets into actual category rewrites. -/
theorem replaceSubcategoryAt?_exists_of_subcategoryAt? :
    ∀ (A : Category) (p : CategoryPath) (old new : Category),
      A.subcategoryAt? p = some old → ∃ A', A.replaceSubcategoryAt? p new = some A'
  | _, [], _, new, _ => by
      exact ⟨new, by simp⟩
  | # _, _ :: _, _, _, h => by
      simp at h
  | L ⧹ R, b :: p, old, new, h => by
      cases b
      · simp only [subcategoryAt?_ldiv_false] at h
        obtain ⟨L', hL'⟩ := replaceSubcategoryAt?_exists_of_subcategoryAt? L p old new h
        exact ⟨L' ⧹ R, by simp [hL']⟩
      · simp only [subcategoryAt?_ldiv_true] at h
        obtain ⟨R', hR'⟩ := replaceSubcategoryAt?_exists_of_subcategoryAt? R p old new h
        exact ⟨L ⧹ R', by simp [hR']⟩
  | L ⧸ R, b :: p, old, new, h => by
      cases b
      · simp only [subcategoryAt?_rdiv_false] at h
        obtain ⟨L', hL'⟩ := replaceSubcategoryAt?_exists_of_subcategoryAt? L p old new h
        exact ⟨L' ⧸ R, by simp [hL']⟩
      · simp only [subcategoryAt?_rdiv_true] at h
        obtain ⟨R', hR'⟩ := replaceSubcategoryAt?_exists_of_subcategoryAt? R p old new h
        exact ⟨L ⧸ R', by simp [hR']⟩

end Category

/-- A replacement target says that one subcategory occurrence inside one tree
node will be replaced by `new`. -/
structure ReplacementTarget {Γ : List Category} {A : Category}
    (t : DerivationTree Γ A) where
  nodePath : NodePath
  nodeCategory : Category
  nodeAt : t.categoryAt? nodePath = some nodeCategory
  pos : CategoryPath
  old : Category
  old_at : nodeCategory.subcategoryAt? pos = some old
  new : Category

namespace ReplacementTarget

/-- Apply one replacement target to its owning node category. -/
def apply? {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (R : ReplacementTarget t) : Option Category :=
  R.nodeCategory.replaceSubcategoryAt? R.pos R.new

/-- If a replacement target comes from an invisible occurrence, then it is not
at the derivation root. -/
theorem root_free_of_occurrence
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (R : ReplacementTarget t) (o : Occurrence t)
    (hnode : R.nodePath = o.nodePath) (hinv : o.Invisible) :
    R.nodePath ≠ [] := by
  intro hroot
  apply hinv
  exact Or.inl (by simpa [DerivationTree.isRootNode, hnode] using hroot)

/-- If a replacement target comes from an invisible occurrence, then it is not
inside a leaf node. -/
theorem leaf_free_of_occurrence
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (R : ReplacementTarget t) (o : Occurrence t)
    (hnode : R.nodePath = o.nodePath) (hinv : o.Invisible) :
    ¬ t.isLeafNode R.nodePath := by
  intro hleaf
  apply hinv
  exact Or.inr (Or.inl (by simpa [hnode] using hleaf))

/-- If a replacement target comes from an invisible occurrence, then it is not
a binary-rule principal constructor. -/
theorem principal_free_of_occurrence
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (R : ReplacementTarget t) (o : Occurrence t)
    (hnode : R.nodePath = o.nodePath) (hpos : R.pos = o.categoryPath)
    (hinv : o.Invisible) :
    ¬ DerivationTree.PrincipalConstructor t R.nodePath R.pos := by
  intro hprincipal
  apply hinv
  exact Or.inr (Or.inr (by simpa [hnode, hpos] using hprincipal))

/-- Applying a replacement whose inserted category is smaller than the replaced
subcategory strictly decreases the owning node category. -/
theorem apply?_constructors_lt
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (R : ReplacementTarget t) {C' : Category}
    (happly : R.apply? = some C')
    (hdecrease : R.new.constructors < R.old.constructors) :
    C'.constructors < R.nodeCategory.constructors :=
  Category.replaceSubcategoryAt?_constructors_lt
    R.nodeCategory R.pos R.old R.new C' R.old_at happly hdecrease

/-- If the host node category and inserted category use only problem atoms, then
the category produced by applying the replacement also uses only problem atoms. -/
theorem apply?_atoms_preserved
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (R : ReplacementTarget t) {C' : Category}
    (happly : R.apply? = some C')
    (hnodeAtoms : ∀ name ∈ R.nodeCategory.atoms, name ∈ problemAtomNames Γ A)
    (hnewAtoms : ∀ name ∈ R.new.atoms, name ∈ problemAtomNames Γ A) :
    ∀ name ∈ C'.atoms, name ∈ problemAtomNames Γ A := by
  intro name hname
  have hmem :=
    Category.mem_atoms_replaceSubcategoryAt?
      R.nodeCategory R.pos R.new C' happly name hname
  rcases hmem with hnode | hnew
  · exact hnodeAtoms name hnode
  · exact hnewAtoms name hnew

/-- A constructor occurrence admits a replacement target that sends exactly that
subcategory to a fixed atom, strictly decreasing the local constructor count. -/
theorem exists_ofOccurrenceToAtom
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (o : Occurrence t) {atomName : String}
    (hatom : atomName ∈ problemAtomNames Γ A) :
    ∃ R : ReplacementTarget t,
      R.nodePath = o.nodePath ∧
        R.nodeCategory = o.nodeCategory ∧
        R.pos = o.categoryPath ∧
        R.new = # atomName ∧
        R.new.constructors < R.old.constructors ∧
        (∀ name ∈ R.new.atoms, name ∈ problemAtomNames Γ A) := by
  rcases o.isConstructor with ⟨L, R, hslash | hslash⟩
  · refine ⟨{
      nodePath := o.nodePath
      nodeCategory := o.nodeCategory
      nodeAt := o.nodeAt
      pos := o.categoryPath
      old := L ⧸ R
      old_at := hslash
      new := # atomName
    }, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · simp [Category.constructors]
    · intro name hname
      simp only [Category.atoms, List.mem_singleton] at hname
      subst name
      exact hatom
  · refine ⟨{
      nodePath := o.nodePath
      nodeCategory := o.nodeCategory
      nodeAt := o.nodeAt
      pos := o.categoryPath
      old := L ⧹ R
      old_at := hslash
      new := # atomName
    }, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · simp [Category.constructors]
    · intro name hname
      simp only [Category.atoms, List.mem_singleton] at hname
      subst name
      exact hatom

end ReplacementTarget

/-- A replacement target whose source occurrence is explicitly recorded as a
member of a boundary-free invisible piece.  The equalities connect the inherited
`ReplacementTarget` fields to that origin occurrence, which is what later rule
preservation and non-overlap arguments use. -/
structure PieceReplacementTarget {Γ : List Category} {A : Category}
    {t : DerivationTree Γ A} (P : InvisiblePiece t)
    extends ReplacementTarget t where
  origin : Occurrence t
  origin_mem : origin ∈ P.carrier
  node_eq : nodePath = origin.nodePath
  cat_eq : nodeCategory = origin.nodeCategory
  pos_eq : pos = origin.categoryPath

namespace PieceReplacementTarget

/-- The origin of a piece replacement is invisible. -/
theorem origin_invisible
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (R : PieceReplacementTarget P) :
    R.origin.Invisible :=
  P.all_invisible R.origin R.origin_mem

/-- Replacing the constructor occurrence recorded by a piece target by an atom
strictly shrinks the stored old subcategory. -/
theorem new_constructors_lt_old_of_atom
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (R : PieceReplacementTarget P)
    {atomName : String} (hnew : R.new = #atomName) :
    R.new.constructors < R.old.constructors := by
  rcases R.origin.isConstructor with ⟨L, S, hslash | hslash⟩
  · have hold : R.old = L ⧸ S := by
      apply Option.some.inj
      have htarget :
          R.nodeCategory.subcategoryAt? R.pos = some (L ⧸ S) := by
        simpa [R.cat_eq, R.pos_eq] using hslash
      exact R.old_at.symm.trans htarget
    simp [hnew, hold, Category.constructors]
  · have hold : R.old = L ⧹ S := by
      apply Option.some.inj
      have htarget :
          R.nodeCategory.subcategoryAt? R.pos = some (L ⧹ S) := by
        simpa [R.cat_eq, R.pos_eq] using hslash
      exact R.old_at.symm.trans htarget
    simp [hnew, hold, Category.constructors]

/-- A constructor occurrence in a piece admits a piece-tagged target replacing
it by a fixed problem atom. -/
theorem exists_ofOccurrenceToAtom
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} {o : Occurrence t}
    (ho : o ∈ P.carrier) {atomName : String}
    (hatom : atomName ∈ problemAtomNames Γ A) :
    ∃ R : PieceReplacementTarget P,
      R.origin = o ∧
        R.new = # atomName ∧
        R.new.constructors < R.old.constructors ∧
        (∀ name ∈ R.new.atoms, name ∈ problemAtomNames Γ A) := by
  obtain ⟨R, hnode, hcat, hpos, hnew, hdecrease, hatoms⟩ :=
    ReplacementTarget.exists_ofOccurrenceToAtom o hatom
  refine ⟨{
    toReplacementTarget := R
    origin := o
    origin_mem := ho
    node_eq := hnode
    cat_eq := hcat
    pos_eq := hpos
  }, rfl, ?_, ?_, ?_⟩
  · exact hnew
  · simpa [hnew] using hdecrease
  · simpa [hnew] using hatoms

/-- Piece replacements inherit root-freeness from invisibility of their origin. -/
theorem root_free
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (R : PieceReplacementTarget P) :
    R.nodePath ≠ [] :=
  ReplacementTarget.root_free_of_occurrence
    R.toReplacementTarget R.origin R.node_eq R.origin_invisible

/-- Piece replacements inherit leaf-freeness from invisibility of their origin. -/
theorem leaf_free
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (R : PieceReplacementTarget P) :
    ¬ t.isLeafNode R.nodePath :=
  ReplacementTarget.leaf_free_of_occurrence
    R.toReplacementTarget R.origin R.node_eq R.origin_invisible

/-- Piece replacements inherit principal-constructor freeness from invisibility
of their origin. -/
theorem principal_free
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (R : PieceReplacementTarget P) :
    ¬ DerivationTree.PrincipalConstructor t R.nodePath R.pos :=
  ReplacementTarget.principal_free_of_occurrence
    R.toReplacementTarget R.origin R.node_eq R.pos_eq R.origin_invisible

end PieceReplacementTarget

namespace PieceReplacementTargets

/-- Every occurrence in the invisible piece has a replacement target in the
list. -/
def Complete {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (targets : List (PieceReplacementTarget P)) : Prop :=
  ∀ o : Occurrence t, o ∈ P.carrier → ∃ R ∈ targets, R.origin = o

/-- Concrete trace closure for piece replacement targets: following a trace edge
from a target origin lands at another target origin. -/
def TraceClosed {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (targets : List (PieceReplacementTarget P)) : Prop :=
  ∀ R : PieceReplacementTarget P, R ∈ targets →
    ∀ o' : Occurrence t, TraceEdge R.origin o' →
      ∃ R' ∈ targets, R'.origin = o'

/-- Same-node targets form an antichain with respect to strict category-prefix
ordering. -/
def SameNodeAntichain {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (targets : List (PieceReplacementTarget P)) : Prop :=
  ∀ R₁ : PieceReplacementTarget P, R₁ ∈ targets →
    ∀ R₂ : PieceReplacementTarget P, R₂ ∈ targets →
      R₁.nodePath = R₂.nodePath →
        ¬ R₁.pos.StrictPrefix R₂.pos ∧ ¬ R₂.pos.StrictPrefix R₁.pos

/-- Complete target lists are trace-closed for a boundary-free piece. -/
theorem traceClosed_of_complete
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (hfree : BoundaryFree P)
    {targets : List (PieceReplacementTarget P)}
    (hcomplete : Complete targets) :
    TraceClosed targets := by
  intro R _hR o' hedge
  have ho' : o' ∈ P.carrier :=
    P.closed_traceEdge_of_boundaryFree hfree R.origin_mem hedge
  exact hcomplete o' ho'

/-- Construct a piece target for every attached carrier occurrence. -/
theorem exists_for_attached
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} {atomName : String}
    (hatom : atomName ∈ problemAtomNames Γ A) :
    ∀ xs : List {o : Occurrence t // o ∈ P.carrier},
      ∃ targets : List (PieceReplacementTarget P),
        (∀ x, x ∈ xs → ∃ R ∈ targets, R.origin = x.1) ∧
          (∀ R : PieceReplacementTarget P, R ∈ targets →
            R.new = # atomName ∧
              R.new.constructors < R.old.constructors ∧
              ∀ name ∈ R.new.atoms, name ∈ problemAtomNames Γ A)
  | [] => by
      exact ⟨[], by simp, by simp⟩
  | x :: xs => by
      obtain ⟨R, horigin, hnew, hdecrease, hatoms⟩ :=
        PieceReplacementTarget.exists_ofOccurrenceToAtom x.2 hatom
      obtain ⟨targets, hcomplete, hprops⟩ := exists_for_attached hatom xs
      refine ⟨R :: targets, ?_, ?_⟩
      · intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with hy | hy
        · subst hy
          exact ⟨R, by simp, horigin⟩
        · obtain ⟨R', hR', hR'origin⟩ := hcomplete y hy
          exact ⟨R', by simp [hR'], hR'origin⟩
      · intro R' hR'
        simp only [List.mem_cons] at hR'
        rcases hR' with hR' | hR'
        · subst hR'
          exact ⟨hnew, hdecrease, hatoms⟩
        · exact hprops R' hR'

end PieceReplacementTargets

/-- Concrete core replacement family generated by one boundary-free invisible
piece.  The closure fields are explicit predicates over the origin
occurrences. -/
structure PieceReplacementFamilyCore {Γ : List Category} {A : Category}
    {t : DerivationTree Γ A} (P : InvisiblePiece t) where
  atomName : String
  atom_mem : atomName ∈ problemAtomNames Γ A
  targets : List (PieceReplacementTarget P)
  nonempty : targets ≠ []
  target_new : ∀ R : PieceReplacementTarget P, R ∈ targets → R.new = # atomName
  complete : PieceReplacementTargets.Complete targets
  trace_closed : PieceReplacementTargets.TraceClosed targets
  same_node_antichain : PieceReplacementTargets.SameNodeAntichain targets
  root_free : ∀ R : PieceReplacementTarget P, R ∈ targets → R.nodePath ≠ []
  leaf_free : ∀ R : PieceReplacementTarget P, R ∈ targets → ¬ t.isLeafNode R.nodePath
  principal_free :
    ∀ R : PieceReplacementTarget P, R ∈ targets →
      ¬ DerivationTree.PrincipalConstructor t R.nodePath R.pos
  size_decreasing :
    ∃ R : PieceReplacementTarget P, R ∈ targets ∧ R.new.constructors < R.old.constructors
  atoms_preserved :
    ∀ R : PieceReplacementTarget P, R ∈ targets →
      ∀ name ∈ R.new.atoms, name ∈ problemAtomNames Γ A

namespace PieceReplacementFamilyCore

/-- Piece replacement targets located at one derivation node. -/
def targetsAt
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    (nodePath : NodePath) : List (PieceReplacementTarget P) :=
  F.targets.filter (fun R => decide (R.nodePath = nodePath))

/-- Category-level `(position, replacement)` data for one derivation node. -/
def categoryTargetsAt
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    (nodePath : NodePath) : List (CategoryPath × Category) :=
  (F.targetsAt nodePath).map (fun R => (R.pos, R.new))

/-- Duplicate-free category positions targeted at one derivation node. -/
def categoryTargetPathsAt
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    (nodePath : NodePath) : List CategoryPath :=
  ((F.targetsAt nodePath).map (fun R => R.pos)).dedup

/-- Category-level replacement data at one node, deduplicated by category
position.  Since a piece family replaces every target by the same fixed atom,
one representative per path is enough. -/
def dedupCategoryTargetsAt
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    (nodePath : NodePath) : List (CategoryPath × Category) :=
  (F.categoryTargetPathsAt nodePath).map (fun p => (p, # F.atomName))

/-- Membership in `targetsAt` is exactly membership in the family with the
requested node path. -/
theorem mem_targetsAt_iff
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    (nodePath : NodePath) (R : PieceReplacementTarget P) :
    R ∈ F.targetsAt nodePath ↔ R ∈ F.targets ∧ R.nodePath = nodePath := by
  simp [targetsAt]

/-- Membership in `categoryTargetsAt` is exactly projection of a piece
replacement target at the requested node. -/
theorem mem_categoryTargetsAt_iff
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    (nodePath : NodePath) (target : CategoryPath × Category) :
    target ∈ F.categoryTargetsAt nodePath ↔
      ∃ R : PieceReplacementTarget P,
        R ∈ F.targets ∧ R.nodePath = nodePath ∧ target = (R.pos, R.new) := by
  constructor
  · intro h
    rw [categoryTargetsAt] at h
    obtain ⟨R, hR, htarget⟩ := List.mem_map.mp h
    have hR' := (F.mem_targetsAt_iff nodePath R).mp hR
    exact ⟨R, hR'.1, hR'.2, htarget.symm⟩
  · rintro ⟨R, hR, hnode, htarget⟩
    rw [categoryTargetsAt]
    exact List.mem_map.mpr
      ⟨R, (F.mem_targetsAt_iff nodePath R).mpr ⟨hR, hnode⟩, htarget.symm⟩

/-- Membership in the deduplicated path list is exactly the existence of a
piece replacement target at that node and position. -/
theorem mem_categoryTargetPathsAt_iff
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    (nodePath : NodePath) (p : CategoryPath) :
    p ∈ F.categoryTargetPathsAt nodePath ↔
      ∃ R : PieceReplacementTarget P,
        R ∈ F.targets ∧ R.nodePath = nodePath ∧ R.pos = p := by
  rw [categoryTargetPathsAt, List.mem_dedup]
  constructor
  · intro hp
    obtain ⟨R, hR, hpos⟩ := List.mem_map.mp hp
    have hR' := (F.mem_targetsAt_iff nodePath R).mp hR
    exact ⟨R, hR'.1, hR'.2, hpos⟩
  · rintro ⟨R, hR, hnode, hpos⟩
    exact List.mem_map.mpr
      ⟨R, (F.mem_targetsAt_iff nodePath R).mpr ⟨hR, hnode⟩, hpos⟩

/-- If the carrier is protected-skeleton-free, the outer skeleton constructor
introduced by a forward type-raising output node cannot be a replacement target. -/
theorem typeRaiseRight_outer_path_not_target_at_of_protectedSkeletonFree
    {Γ Ω : List Category} {A C Z : Category} {t : DerivationTree Γ A}
    (ctx : DerivationContext Γ (C ⧸ (A ⧹ C)) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.typeRaiseRight C t))}
    (F : PieceReplacementFamilyCore P)
    (hsafe : P.ProtectedSkeletonFree) :
    [] ∉ F.categoryTargetPathsAt ctx.nodePrefix := by
  intro hmem
  obtain ⟨R, _hR, hnode, hpos⟩ :=
    (F.mem_categoryTargetPathsAt_iff ctx.nodePrefix ([] : CategoryPath)).mp hmem
  have hprot : R.origin.ProtectedUnarySkeleton := by
    change DerivationTree.UnarySkeletonConstructor
      (ctx.plug (DerivationTree.typeRaiseRight C t))
        R.origin.nodePath R.origin.categoryPath
    rw [← R.node_eq, ← R.pos_eq, hnode, hpos]
    simpa using
      (ctx.liftUnarySkeletonConstructor
        (DerivationTree.UnarySkeletonConstructor.trRight_outer (C := C) t))
  exact hsafe R.origin R.origin_mem hprot

/-- If the carrier is protected-skeleton-free, the inner skeleton constructor
introduced by a forward type-raising output node cannot be a replacement target.
This is the formal version of the blocker `[true] ∉ ...` needed before proving
honest `T>` rule-shape preservation by atom replacement. -/
theorem typeRaiseRight_inner_path_not_target_at_of_protectedSkeletonFree
    {Γ Ω : List Category} {A C Z : Category} {t : DerivationTree Γ A}
    (ctx : DerivationContext Γ (C ⧸ (A ⧹ C)) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.typeRaiseRight C t))}
    (F : PieceReplacementFamilyCore P)
    (hsafe : P.ProtectedSkeletonFree) :
    [true] ∉ F.categoryTargetPathsAt ctx.nodePrefix := by
  intro hmem
  obtain ⟨R, _hR, hnode, hpos⟩ :=
    (F.mem_categoryTargetPathsAt_iff ctx.nodePrefix [true]).mp hmem
  have hprot : R.origin.ProtectedUnarySkeleton := by
    change DerivationTree.UnarySkeletonConstructor
      (ctx.plug (DerivationTree.typeRaiseRight C t))
        R.origin.nodePath R.origin.categoryPath
    rw [← R.node_eq, ← R.pos_eq, hnode, hpos]
    simpa using
      (ctx.liftUnarySkeletonConstructor
        (DerivationTree.UnarySkeletonConstructor.trRight_inner (C := C) t))
  exact hsafe R.origin R.origin_mem hprot

/-- If the carrier is protected-skeleton-free, the outer skeleton constructor
introduced by a backward type-raising output node cannot be a replacement target. -/
theorem typeRaiseLeft_outer_path_not_target_at_of_protectedSkeletonFree
    {Γ Ω : List Category} {A C Z : Category} {t : DerivationTree Γ A}
    (ctx : DerivationContext Γ ((C ⧸ A) ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.typeRaiseLeft C t))}
    (F : PieceReplacementFamilyCore P)
    (hsafe : P.ProtectedSkeletonFree) :
    [] ∉ F.categoryTargetPathsAt ctx.nodePrefix := by
  intro hmem
  obtain ⟨R, _hR, hnode, hpos⟩ :=
    (F.mem_categoryTargetPathsAt_iff ctx.nodePrefix ([] : CategoryPath)).mp hmem
  have hprot : R.origin.ProtectedUnarySkeleton := by
    change DerivationTree.UnarySkeletonConstructor
      (ctx.plug (DerivationTree.typeRaiseLeft C t))
        R.origin.nodePath R.origin.categoryPath
    rw [← R.node_eq, ← R.pos_eq, hnode, hpos]
    simpa using
      (ctx.liftUnarySkeletonConstructor
        (DerivationTree.UnarySkeletonConstructor.trLeft_outer (C := C) t))
  exact hsafe R.origin R.origin_mem hprot

/-- If the carrier is protected-skeleton-free, the inner skeleton constructor
introduced by a backward type-raising output node cannot be a replacement target.
This is the formal version of the blocker `[false] ∉ ...` for `T<`. -/
theorem typeRaiseLeft_inner_path_not_target_at_of_protectedSkeletonFree
    {Γ Ω : List Category} {A C Z : Category} {t : DerivationTree Γ A}
    (ctx : DerivationContext Γ ((C ⧸ A) ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.typeRaiseLeft C t))}
    (F : PieceReplacementFamilyCore P)
    (hsafe : P.ProtectedSkeletonFree) :
    [false] ∉ F.categoryTargetPathsAt ctx.nodePrefix := by
  intro hmem
  obtain ⟨R, _hR, hnode, hpos⟩ :=
    (F.mem_categoryTargetPathsAt_iff ctx.nodePrefix [false]).mp hmem
  have hprot : R.origin.ProtectedUnarySkeleton := by
    change DerivationTree.UnarySkeletonConstructor
      (ctx.plug (DerivationTree.typeRaiseLeft C t))
        R.origin.nodePath R.origin.categoryPath
    rw [← R.node_eq, ← R.pos_eq, hnode, hpos]
    simpa using
      (ctx.liftUnarySkeletonConstructor
        (DerivationTree.UnarySkeletonConstructor.trLeft_inner (C := C) t))
  exact hsafe R.origin R.origin_mem hprot

/-- Deduplicated target paths are duplicate-free. -/
theorem categoryTargetPathsAt_nodup
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    (nodePath : NodePath) :
    (F.categoryTargetPathsAt nodePath).Nodup :=
  List.nodup_dedup _

/-- The positions of deduplicated category targets are duplicate-free. -/
theorem dedupCategoryTargetsAt_positions_nodup
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    (nodePath : NodePath) :
    ((F.dedupCategoryTargetsAt nodePath).map Prod.fst).Nodup := by
  have hmap :
      ((F.categoryTargetPathsAt nodePath).map (fun p => (p, # F.atomName))).map Prod.fst =
        F.categoryTargetPathsAt nodePath := by
    simp [List.map_map, Function.comp_def]
  rw [dedupCategoryTargetsAt, hmap]
  exact F.categoryTargetPathsAt_nodup nodePath

/-- Membership in deduplicated category targets is path membership with the
family's fixed replacement atom. -/
theorem mem_dedupCategoryTargetsAt_iff
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    (nodePath : NodePath) (target : CategoryPath × Category) :
    target ∈ F.dedupCategoryTargetsAt nodePath ↔
      target.1 ∈ F.categoryTargetPathsAt nodePath ∧ target.2 = # F.atomName := by
  constructor
  · intro h
    rw [dedupCategoryTargetsAt] at h
    obtain ⟨p, hp, htarget⟩ := List.mem_map.mp h
    subst htarget
    exact ⟨hp, rfl⟩
  · intro h
    rw [dedupCategoryTargetsAt]
    exact List.mem_map.mpr ⟨target.1, h.1, by ext <;> simp [h.2]⟩

/-- Every original piece target at the node is represented in the deduplicated
category-target list. -/
theorem mem_dedupCategoryTargetsAt_of_target
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    {nodePath : NodePath} {R : PieceReplacementTarget P}
    (hR : R ∈ F.targets) (hnode : R.nodePath = nodePath) :
    (R.pos, R.new) ∈ F.dedupCategoryTargetsAt nodePath := by
  rw [F.mem_dedupCategoryTargetsAt_iff nodePath (R.pos, R.new)]
  constructor
  · rw [F.mem_categoryTargetPathsAt_iff nodePath R.pos]
    exact ⟨R, hR, hnode, rfl⟩
  · exact F.target_new R hR

/-- Deduplicated category targets are still members of the original projected
category-target list. -/
theorem mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    {nodePath : NodePath} {target : CategoryPath × Category}
    (htarget : target ∈ F.dedupCategoryTargetsAt nodePath) :
    target ∈ F.categoryTargetsAt nodePath := by
  have hdedup := (F.mem_dedupCategoryTargetsAt_iff nodePath target).mp htarget
  obtain ⟨R, hR, hnode, hpos⟩ :=
    (F.mem_categoryTargetPathsAt_iff nodePath target.1).mp hdedup.1
  rw [F.mem_categoryTargetsAt_iff nodePath target]
  refine ⟨R, hR, hnode, ?_⟩
  ext <;> simp [hpos, hdedup.2, F.target_new R hR]

/-- Deduplicated category targets at one node are pairwise disjoint. -/
theorem dedupCategoryTargetsAt_disjoint
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    (nodePath : NodePath) :
    CategoryReplacementTargetsDisjoint (F.dedupCategoryTargetsAt nodePath) := by
  intro target₁ htarget₁ target₂ htarget₂ hne hoverlap
  obtain ⟨hpath₁, _hnew₁⟩ :=
    (F.mem_dedupCategoryTargetsAt_iff nodePath target₁).mp htarget₁
  obtain ⟨hpath₂, _hnew₂⟩ :=
    (F.mem_dedupCategoryTargetsAt_iff nodePath target₂).mp htarget₂
  obtain ⟨R₁, hR₁, hnode₁, hpos₁⟩ :=
    (F.mem_categoryTargetPathsAt_iff nodePath target₁.1).mp hpath₁
  obtain ⟨R₂, hR₂, hnode₂, hpos₂⟩ :=
    (F.mem_categoryTargetPathsAt_iff nodePath target₂.1).mp hpath₂
  have hnode : R₁.nodePath = R₂.nodePath := by rw [hnode₁, hnode₂]
  have hanti := F.same_node_antichain R₁ hR₁ R₂ hR₂ hnode
  rcases hoverlap with hp₁₂ | hp₂₁
  · have hprefix : R₁.pos.Prefix R₂.pos := by
      simpa [hpos₁, hpos₂] using hp₁₂
    have hpos_ne : R₁.pos ≠ R₂.pos := by
      intro hsame
      apply hne
      ext
      simp [← hpos₁, ← hpos₂, hsame]
    exact hanti.1 (CategoryPath.Prefix.strict_of_ne hprefix hpos_ne)
  · have hprefix : R₂.pos.Prefix R₁.pos := by
      simpa [hpos₁, hpos₂] using hp₂₁
    have hpos_ne : R₂.pos ≠ R₁.pos := by
      intro hsame
      apply hne
      ext
      simp [← hpos₁, ← hpos₂, hsame.symm]
    exact hanti.2 (CategoryPath.Prefix.strict_of_ne hprefix hpos_ne)

end PieceReplacementFamilyCore

/-- Paper-facing boundary-free piece contraction target in its faithful
piece-based form.  The existing occurrence-based elimination target in
`Depth.lean` can be bridged to this once finite component carriers are
constructed.

Important architectural note: this is deliberately the *strong* target from the
paper interface.  The current node-local atom-replacement construction should
not try to prove it directly, because a boundary-free carrier might contain a
protected unary type-raising skeleton occurrence.  Replacing that occurrence by
an atom would not preserve the local `T>`/`T<` rule shape.  For the
replacement-only subproblem, use the protected-skeleton-free target below. -/
def BoundaryFreeInvisiblePieceContractsFromPieces : Prop :=
  ∀ {Γ : List Category} {A : Category} {t : DerivationTree Γ A},
    t.NodeCategoriesUseProblemAtoms →
      ∀ P : InvisiblePiece t, BoundaryFree P → Nonempty (ContractionWitness t)

/-- Replacement-only boundary-free contraction target.  This is the honest
scope of the node-local atom-replacement method: it may target only invisible
pieces that are both boundary-free and free of protected unary type-raising
skeleton constructors.

The remaining global proof must either show that protected-skeleton-free is
automatic for the relevant boundary-free pieces, or dispatch the protected
skeleton case through repeatable-pair/band contraction. -/
def BoundaryFreeReplaceableInvisiblePieceContractsFromPieces : Prop :=
  ∀ {Γ : List Category} {A : Category} {t : DerivationTree Γ A},
    t.NodeCategoriesUseProblemAtoms →
      ∀ P : InvisiblePiece t,
        BoundaryFree P →
          P.ProtectedSkeletonFree →
            Nonempty (ContractionWitness t)

/-- Complementary target for the protected-skeleton case.  If a boundary-free
invisible piece contains one of the unary type-raising skeleton constructors,
then atom replacement is the wrong local operation; the proof must supply a
contraction by a band/protected-skeleton argument instead. -/
def BoundaryFreeProtectedSkeletonPieceContracts : Prop :=
  ∀ {Γ : List Category} {A : Category} {t : DerivationTree Γ A},
    t.NodeCategoriesUseProblemAtoms →
      ∀ P : InvisiblePiece t,
        BoundaryFree P →
          (∃ o : Occurrence t, o ∈ P.carrier ∧ o.ProtectedUnarySkeleton) →
            Nonempty (ContractionWitness t)

/-- The strong paper-facing target is recovered by splitting boundary-free
pieces into the replacement-safe case and the protected unary-skeleton case. -/
theorem boundaryFreeInvisiblePieceContractsFromPieces_of_replaceable_or_protected
    (hreplace : BoundaryFreeReplaceableInvisiblePieceContractsFromPieces)
    (hprotected : BoundaryFreeProtectedSkeletonPieceContracts) :
    BoundaryFreeInvisiblePieceContractsFromPieces := by
  intro Γ A t hatoms P hfree
  classical
  by_cases hsafe : P.ProtectedSkeletonFree
  · exact hreplace hatoms P hfree hsafe
  · exact hprotected hatoms P hfree (by
      by_contra hnone
      apply hsafe
      intro o ho hprot
      exact hnone ⟨o, ho, hprot⟩)

namespace Category

/-- Sequentially apply a finite list of subcategory replacements.  The later
tree-surgery proof will use non-overlap hypotheses to show this sequential
operation realizes the intended simultaneous replacement. -/
def replaceManySubcategories? (C : Category) :
    List (CategoryPath × Category) → Option Category
  | [] => some C
  | (p, new) :: rest => do
      let C' ← C.replaceSubcategoryAt? p new
      replaceManySubcategories? C' rest

@[simp]
theorem replaceManySubcategories?_nil (C : Category) :
    C.replaceManySubcategories? [] = some C := rfl

@[simp]
theorem replaceManySubcategories?_cons
    (C : Category) (p : CategoryPath) (new : Category)
    (rest : List (CategoryPath × Category)) :
    C.replaceManySubcategories? ((p, new) :: rest) =
      (C.replaceSubcategoryAt? p new).bind
        (fun C' => C'.replaceManySubcategories? rest) := rfl

/-- Atoms in a category produced by many replacements come either from the
original host category or from one of the inserted categories. -/
theorem mem_atoms_replaceManySubcategories? :
    ∀ {C : Category} {targets : List (CategoryPath × Category)} {C' : Category},
      C.replaceManySubcategories? targets = some C' →
        ∀ name ∈ C'.atoms,
          name ∈ C.atoms ∨ ∃ target ∈ targets, name ∈ target.2.atoms
  | C, [], C', hrep => by
      intro name hname
      simp only [replaceManySubcategories?_nil, Option.some.injEq] at hrep
      subst C'
      exact Or.inl hname
  | C, (p, new) :: rest, C', hrep => by
      intro name hname
      simp only [replaceManySubcategories?_cons] at hrep
      cases hfirst : C.replaceSubcategoryAt? p new with
      | none =>
          have hnone : (none : Option Category) = some C' := by
            simpa [hfirst] using hrep
          cases hnone
      | some C₁ =>
          have hrepTail : C₁.replaceManySubcategories? rest = some C' := by
            simpa [hfirst] using hrep
          have htail :=
            mem_atoms_replaceManySubcategories? hrepTail name hname
          rcases htail with hC₁ | htarget
          · have hsingle :=
              Category.mem_atoms_replaceSubcategoryAt? C p new C₁ hfirst name hC₁
            rcases hsingle with hhost | hnew
            · exact Or.inl hhost
            · exact Or.inr ⟨(p, new), by simp, hnew⟩
          · rcases htarget with ⟨target, hmem, htargetAtoms⟩
            exact Or.inr ⟨target, by simp [hmem], htargetAtoms⟩

/-- If the host category and every inserted category use only a fixed atom set,
then a successful many-replacement result uses only that atom set. -/
theorem replaceManySubcategories?_atoms_preserved
    {atomNames : List String} {C C' : Category}
    {targets : List (CategoryPath × Category)}
    (hrep : C.replaceManySubcategories? targets = some C')
    (hhost : ∀ name ∈ C.atoms, name ∈ atomNames)
    (htargets :
      ∀ target ∈ targets, ∀ name ∈ target.2.atoms, name ∈ atomNames) :
    ∀ name ∈ C'.atoms, name ∈ atomNames := by
  intro name hname
  have hmem := mem_atoms_replaceManySubcategories? hrep name hname
  rcases hmem with hhostAtom | htarget
  · exact hhost name hhostAtom
  · rcases htarget with ⟨target, htargetMem, htargetAtom⟩
    exact htargets target htargetMem name htargetAtom

/-- Replacing a disjoint subcategory leaves a read at `q` unchanged. -/
theorem replaceSubcategoryAt?_subcategoryAt?_of_disjoint :
    ∀ (C : Category) (p q : CategoryPath) (new C' : Category),
      C.replaceSubcategoryAt? p new = some C' →
      p.Disjoint q →
      C'.subcategoryAt? q = C.subcategoryAt? q
  | C, [], q, new, C', hrep, hdisjoint => by
      exact False.elim (hdisjoint (Or.inl ⟨q, by simp⟩))
  | C, p, [], new, C', hrep, hdisjoint => by
      exact False.elim (hdisjoint (Or.inr ⟨p, by simp⟩))
  | # name, _ :: _, _ :: _, new, C', hrep, _ => by
      simp at hrep
  | L ⧹ R, bp :: p, bq :: q, new, C', hrep, hdisjoint => by
      cases bp <;> cases bq
      · simp only [Category.replaceSubcategoryAt?_ldiv_false, Option.map_eq_some_iff] at hrep
        obtain ⟨L', hL', rfl⟩ := hrep
        simp only [Category.subcategoryAt?_ldiv_false]
        exact replaceSubcategoryAt?_subcategoryAt?_of_disjoint
          L p q new L' hL' (CategoryPath.Disjoint.tail_of_cons_same hdisjoint)
      · simp only [Category.replaceSubcategoryAt?_ldiv_false, Option.map_eq_some_iff] at hrep
        obtain ⟨L', _hL', rfl⟩ := hrep
        simp only [Category.subcategoryAt?_ldiv_true]
      · simp only [Category.replaceSubcategoryAt?_ldiv_true, Option.map_eq_some_iff] at hrep
        obtain ⟨R', _hR', rfl⟩ := hrep
        simp only [Category.subcategoryAt?_ldiv_false]
      · simp only [Category.replaceSubcategoryAt?_ldiv_true, Option.map_eq_some_iff] at hrep
        obtain ⟨R', hR', rfl⟩ := hrep
        simp only [Category.subcategoryAt?_ldiv_true]
        exact replaceSubcategoryAt?_subcategoryAt?_of_disjoint
          R p q new R' hR' (CategoryPath.Disjoint.tail_of_cons_same hdisjoint)
  | L ⧸ R, bp :: p, bq :: q, new, C', hrep, hdisjoint => by
      cases bp <;> cases bq
      · simp only [Category.replaceSubcategoryAt?_rdiv_false, Option.map_eq_some_iff] at hrep
        obtain ⟨L', hL', rfl⟩ := hrep
        simp only [Category.subcategoryAt?_rdiv_false]
        exact replaceSubcategoryAt?_subcategoryAt?_of_disjoint
          L p q new L' hL' (CategoryPath.Disjoint.tail_of_cons_same hdisjoint)
      · simp only [Category.replaceSubcategoryAt?_rdiv_false, Option.map_eq_some_iff] at hrep
        obtain ⟨L', _hL', rfl⟩ := hrep
        simp only [Category.subcategoryAt?_rdiv_true]
      · simp only [Category.replaceSubcategoryAt?_rdiv_true, Option.map_eq_some_iff] at hrep
        obtain ⟨R', _hR', rfl⟩ := hrep
        simp only [Category.subcategoryAt?_rdiv_false]
      · simp only [Category.replaceSubcategoryAt?_rdiv_true, Option.map_eq_some_iff] at hrep
        obtain ⟨R', hR', rfl⟩ := hrep
        simp only [Category.subcategoryAt?_rdiv_true]
        exact replaceSubcategoryAt?_subcategoryAt?_of_disjoint
          R p q new R' hR' (CategoryPath.Disjoint.tail_of_cons_same hdisjoint)

/-- A list of pairwise-disjoint, duplicate-free, valid replacement positions
can be applied sequentially.  Disjointness makes earlier replacements preserve
the validity of all later positions. -/
theorem replaceManySubcategories?_exists_of_disjoint
    (C : Category) :
    ∀ targets : List (CategoryPath × Category),
      (∀ target ∈ targets, ∃ old, C.subcategoryAt? target.1 = some old) →
      (targets.map Prod.fst).Nodup →
      CategoryReplacementTargetsDisjoint targets →
      ∃ C', C.replaceManySubcategories? targets = some C' := by
  intro targets
  induction targets generalizing C with
  | nil =>
      intro _ _ _
      exact ⟨C, rfl⟩
  | cons target rest ih =>
      intro hvalid hnodup hdisjoint
      rcases target with ⟨p, new⟩
      obtain ⟨old, hold⟩ := hvalid (p, new) (by simp)
      obtain ⟨C₁, hfirst⟩ :=
        Category.replaceSubcategoryAt?_exists_of_subcategoryAt? C p old new hold
      have hnodupRest : (rest.map Prod.fst).Nodup := by
        simpa using (List.nodup_cons.mp hnodup).2
      have hp_not_mem_rest : p ∉ rest.map Prod.fst := by
        simpa using (List.nodup_cons.mp hnodup).1
      have hvalidRest :
          ∀ target ∈ rest, ∃ old, C₁.subcategoryAt? target.1 = some old := by
        intro target htarget
        have hneq : p ≠ target.1 := by
          intro hsame
          apply hp_not_mem_rest
          have hmap : target.1 ∈ rest.map Prod.fst :=
            List.mem_map.mpr ⟨target, htarget, rfl⟩
          simpa [hsame] using hmap
        have hstable :
            C₁.subcategoryAt? target.1 = C.subcategoryAt? target.1 :=
          Category.replaceSubcategoryAt?_subcategoryAt?_of_disjoint
            C p target.1 new C₁ hfirst
              (hdisjoint (p, new) (by simp) target (by simp [htarget]) hneq)
        obtain ⟨old', hold'⟩ := hvalid target (by simp [htarget])
        exact ⟨old', by rw [hstable]; exact hold'⟩
      have hdisjointRest : CategoryReplacementTargetsDisjoint rest := by
        intro target₁ htarget₁ target₂ htarget₂ hneq
        exact hdisjoint target₁ (by simp [htarget₁]) target₂ (by simp [htarget₂]) hneq
      obtain ⟨C', hrest⟩ := ih C₁ hvalidRest hnodupRest hdisjointRest
      exact ⟨C', by simp [replaceManySubcategories?_cons, hfirst, hrest]⟩

/-- If every disjoint replacement strictly shrinks the subcategory it replaces,
then sequential many-replacement does not increase constructor count. -/
theorem replaceManySubcategories?_constructors_le_of_disjoint
    (C : Category) :
    ∀ {targets : List (CategoryPath × Category)} {C' : Category},
      (∀ target ∈ targets,
        ∃ old, C.subcategoryAt? target.1 = some old ∧
          target.2.constructors < old.constructors) →
      (targets.map Prod.fst).Nodup →
      CategoryReplacementTargetsDisjoint targets →
      C.replaceManySubcategories? targets = some C' →
      C'.constructors ≤ C.constructors := by
  intro targets
  induction targets generalizing C with
  | nil =>
      intro C' _ _ _ hrep
      simp only [replaceManySubcategories?_nil, Option.some.injEq] at hrep
      subst C'
      exact Nat.le_refl _
  | cons target rest ih =>
      intro C' hvalid hnodup hdisjoint hrep
      rcases target with ⟨p, new⟩
      simp only [replaceManySubcategories?_cons] at hrep
      cases hfirst : C.replaceSubcategoryAt? p new with
      | none =>
          simp [hfirst] at hrep
      | some C₁ =>
          have hrepRest : C₁.replaceManySubcategories? rest = some C' := by
            simpa [hfirst] using hrep
          obtain ⟨old, hold, hlt⟩ := hvalid (p, new) (by simp)
          have hfirstLt : C₁.constructors < C.constructors :=
            Category.replaceSubcategoryAt?_constructors_lt
              C p old new C₁ hold hfirst hlt
          have hnodupRest : (rest.map Prod.fst).Nodup := by
            simpa using (List.nodup_cons.mp hnodup).2
          have hp_not_mem_rest : p ∉ rest.map Prod.fst := by
            simpa using (List.nodup_cons.mp hnodup).1
          have hvalidRest :
              ∀ target ∈ rest,
                ∃ old, C₁.subcategoryAt? target.1 = some old ∧
                  target.2.constructors < old.constructors := by
            intro target htarget
            have hneq : p ≠ target.1 := by
              intro hsame
              apply hp_not_mem_rest
              have hmap : target.1 ∈ rest.map Prod.fst :=
                List.mem_map.mpr ⟨target, htarget, rfl⟩
              simpa [hsame] using hmap
            have hstable :
                C₁.subcategoryAt? target.1 = C.subcategoryAt? target.1 :=
              Category.replaceSubcategoryAt?_subcategoryAt?_of_disjoint
                C p target.1 new C₁ hfirst
                  (hdisjoint (p, new) (by simp) target (by simp [htarget]) hneq)
            obtain ⟨old', hold', hlt'⟩ := hvalid target (by simp [htarget])
            exact ⟨old', by rw [hstable]; exact hold', hlt'⟩
          have hdisjointRest : CategoryReplacementTargetsDisjoint rest := by
            intro target₁ htarget₁ target₂ htarget₂ hneq
            exact hdisjoint target₁ (by simp [htarget₁]) target₂ (by simp [htarget₂]) hneq
          have htailLe :=
            ih C₁ hvalidRest hnodupRest hdisjointRest hrepRest
          omega

/-- A nonempty list of disjoint shrinking replacements strictly decreases
constructor count. -/
theorem replaceManySubcategories?_constructors_lt_of_nonempty_disjoint
    {C : Category} {targets : List (CategoryPath × Category)} {C' : Category}
    (hvalid :
      ∀ target ∈ targets,
        ∃ old, C.subcategoryAt? target.1 = some old ∧
          target.2.constructors < old.constructors)
    (hnodup : (targets.map Prod.fst).Nodup)
    (hdisjoint : CategoryReplacementTargetsDisjoint targets)
    (hnonempty : targets ≠ [])
    (hrep : C.replaceManySubcategories? targets = some C') :
    C'.constructors < C.constructors := by
  cases targets with
  | nil =>
      exact False.elim (hnonempty rfl)
  | cons target rest =>
      rcases target with ⟨p, new⟩
      simp only [replaceManySubcategories?_cons] at hrep
      cases hfirst : C.replaceSubcategoryAt? p new with
      | none =>
          simp [hfirst] at hrep
      | some C₁ =>
          have hrepRest : C₁.replaceManySubcategories? rest = some C' := by
            simpa [hfirst] using hrep
          obtain ⟨old, hold, hlt⟩ := hvalid (p, new) (by simp)
          have hfirstLt : C₁.constructors < C.constructors :=
            Category.replaceSubcategoryAt?_constructors_lt
              C p old new C₁ hold hfirst hlt
          have hnodupRest : (rest.map Prod.fst).Nodup := by
            simpa using (List.nodup_cons.mp hnodup).2
          have hp_not_mem_rest : p ∉ rest.map Prod.fst := by
            simpa using (List.nodup_cons.mp hnodup).1
          have hvalidRest :
              ∀ target ∈ rest,
                ∃ old, C₁.subcategoryAt? target.1 = some old ∧
                  target.2.constructors < old.constructors := by
            intro target htarget
            have hneq : p ≠ target.1 := by
              intro hsame
              apply hp_not_mem_rest
              have hmap : target.1 ∈ rest.map Prod.fst :=
                List.mem_map.mpr ⟨target, htarget, rfl⟩
              simpa [hsame] using hmap
            have hstable :
                C₁.subcategoryAt? target.1 = C.subcategoryAt? target.1 :=
              Category.replaceSubcategoryAt?_subcategoryAt?_of_disjoint
                C p target.1 new C₁ hfirst
                  (hdisjoint (p, new) (by simp) target (by simp [htarget]) hneq)
            obtain ⟨old', hold', hlt'⟩ := hvalid target (by simp [htarget])
            exact ⟨old', by rw [hstable]; exact hold', hlt'⟩
          have hdisjointRest : CategoryReplacementTargetsDisjoint rest := by
            intro target₁ htarget₁ target₂ htarget₂ hneq
            exact hdisjoint target₁ (by simp [htarget₁]) target₂ (by simp [htarget₂]) hneq
          have htailLe :=
            replaceManySubcategories?_constructors_le_of_disjoint
              C₁ hvalidRest hnodupRest hdisjointRest hrepRest
          omega

/-- Root-level replacement in a canonical simultaneous replacement target
list.  All targets generated by `PieceReplacementFamilyCore` are deduplicated
by path, so the first root entry, if any, is the unique root entry. -/
def simulRootTarget? : List (CategoryPath × Category) → Option Category
  | [] => none
  | ([], new) :: _ => some new
  | (_ :: _, _) :: rest => simulRootTarget? rest

/-- Targets transported to one child of a slash category. -/
def simulChildTargets (b : Bool) : List (CategoryPath × Category) →
    List (CategoryPath × Category)
  | [] => []
  | ([], _) :: rest => simulChildTargets b rest
  | (b' :: p, new) :: rest =>
      if b' = b then (p, new) :: simulChildTargets b rest
      else simulChildTargets b rest

/-- Canonical simultaneous subcategory replacement.  Unlike
`replaceManySubcategories?`, this function descends structurally through the
category, so sibling replacement order is irrelevant to rule-shape proofs. -/
def replaceSimul? : Category → List (CategoryPath × Category) → Option Category
  | A, targets =>
      match simulRootTarget? targets with
      | some new => some new
      | none =>
          match A with
          | #name =>
              match targets with
              | [] => some (#name)
              | _ :: _ => none
          | L ⧹ R => do
              let L' ← replaceSimul? L (simulChildTargets false targets)
              let R' ← replaceSimul? R (simulChildTargets true targets)
              some (L' ⧹ R')
          | L ⧸ R => do
              let L' ← replaceSimul? L (simulChildTargets false targets)
              let R' ← replaceSimul? R (simulChildTargets true targets)
              some (L' ⧸ R')

@[simp]
theorem replaceSimul?_nil (C : Category) :
    C.replaceSimul? [] = some C := by
  induction C with
  | atom name => rfl
  | ldiv L R ihL ihR =>
      simp [replaceSimul?, simulRootTarget?, simulChildTargets, ihL, ihR]
  | rdiv L R ihL ihR =>
      simp [replaceSimul?, simulRootTarget?, simulChildTargets, ihL, ihR]

@[simp]
theorem simulChildTargets_nil (b : Bool) :
    simulChildTargets b [] = [] := rfl

theorem simulChildTargets_eq_nil_of_no_child
    (b : Bool) :
    ∀ targets : List (CategoryPath × Category),
      (∀ p new, (b :: p, new) ∉ targets) →
      simulChildTargets b targets = []
  | [], _ => rfl
  | ([], new) :: rest, hno => by
      simp [simulChildTargets, simulChildTargets_eq_nil_of_no_child b rest
        (by
          intro p new hmem
          exact hno p new (by simp [hmem]))]
  | (b' :: p, new) :: rest, hno => by
      by_cases hb : b' = b
      · subst b'
        exact False.elim (hno p new (by simp))
      · simp [simulChildTargets, hb, simulChildTargets_eq_nil_of_no_child b rest
          (by
            intro q new' hmem
            exact hno q new' (by simp [hmem]))]

/-- Path-only child projection for canonical simultaneous replacement by one
fixed atom. -/
def simulChildPaths (b : Bool) : List CategoryPath → List CategoryPath
  | [] => []
  | [] :: rest => simulChildPaths b rest
  | (b' :: p) :: rest =>
      if b' = b then p :: simulChildPaths b rest
      else simulChildPaths b rest

/-- Canonical simultaneous replacement by a fixed atom at a set of category
paths.  This path-only version is useful for rule-shape proofs because it is
insensitive to the order in which the replacement paths were enumerated. -/
def replaceSimulAtPaths? (atomName : String) : Category → List CategoryPath → Option Category
  | A, paths =>
      if [] ∈ paths then
        some (# atomName)
      else
        match A with
        | #name => if paths = [] then some (#name) else none
        | L ⧹ R => do
            let L' ← replaceSimulAtPaths? atomName L (simulChildPaths false paths)
            let R' ← replaceSimulAtPaths? atomName R (simulChildPaths true paths)
            some (L' ⧹ R')
        | L ⧸ R => do
            let L' ← replaceSimulAtPaths? atomName L (simulChildPaths false paths)
            let R' ← replaceSimulAtPaths? atomName R (simulChildPaths true paths)
            some (L' ⧸ R')

@[simp]
theorem replaceSimulAtPaths?_nil (atomName : String) (C : Category) :
    replaceSimulAtPaths? atomName C [] = some C := by
  induction C with
  | atom name => rfl
  | ldiv L R ihL ihR =>
      simp [replaceSimulAtPaths?, simulChildPaths, ihL, ihR]
  | rdiv L R ihL ihR =>
      simp [replaceSimulAtPaths?, simulChildPaths, ihL, ihR]

@[simp]
theorem simulChildPaths_nil (b : Bool) :
    simulChildPaths b [] = [] := rfl

set_option linter.flexible false in
theorem mem_simulChildPaths_iff
    (b : Bool) :
    ∀ (paths : List CategoryPath) (p : CategoryPath),
      p ∈ simulChildPaths b paths ↔ b :: p ∈ paths
  | [], p => by
      simp [simulChildPaths]
  | [] :: rest, p => by
      simp [simulChildPaths, mem_simulChildPaths_iff b rest p]
  | (b' :: q) :: rest, p => by
      by_cases hb : b' = b
      · subst b'
        simp [simulChildPaths, mem_simulChildPaths_iff b rest p]
      · simp [simulChildPaths, hb, mem_simulChildPaths_iff b rest p]
        intro hbb _
        exact False.elim (hb hbb.symm)

theorem simulChildPaths_eq_nil_of_no_child
    (b : Bool) :
    ∀ paths : List CategoryPath,
      (∀ p, b :: p ∉ paths) →
        simulChildPaths b paths = []
  | [], _ => rfl
  | [] :: rest, hno => by
      simp [simulChildPaths, simulChildPaths_eq_nil_of_no_child b rest
        (by
          intro p hmem
          exact hno p (by simp [hmem]))]
  | (b' :: p) :: rest, hno => by
      by_cases hb : b' = b
      · subst b'
        exact False.elim (hno p (by simp))
      · simp [simulChildPaths, hb, simulChildPaths_eq_nil_of_no_child b rest
          (by
            intro q hmem
            exact hno q (by simp [hmem]))]

set_option linter.flexible false in
theorem replaceSimulAtPaths?_eq_of_same_members
    (atomName : String) :
    ∀ (C : Category) {paths₁ paths₂ : List CategoryPath} {C₁ C₂ : Category},
      (∀ p, p ∈ paths₁ ↔ p ∈ paths₂) →
      replaceSimulAtPaths? atomName C paths₁ = some C₁ →
      replaceSimulAtPaths? atomName C paths₂ = some C₂ →
      C₁ = C₂
  | #name, paths₁, paths₂, C₁, C₂, hmem, h₁, h₂ => by
      by_cases hroot₁ : [] ∈ paths₁
      · have hroot₂ : [] ∈ paths₂ := (hmem []).mp hroot₁
        simp [replaceSimulAtPaths?, hroot₁] at h₁
        simp [replaceSimulAtPaths?, hroot₂] at h₂
        subst C₁
        subst C₂
        rfl
      · have hroot₂ : [] ∉ paths₂ := by
          intro h
          exact hroot₁ ((hmem []).mpr h)
        simp [replaceSimulAtPaths?, hroot₁] at h₁
        simp [replaceSimulAtPaths?, hroot₂] at h₂
        rcases h₁ with ⟨_, hC₁⟩
        rcases h₂ with ⟨_, hC₂⟩
        subst C₁
        subst C₂
        rfl
  | L ⧹ R, paths₁, paths₂, C₁, C₂, hmem, h₁, h₂ => by
      by_cases hroot₁ : [] ∈ paths₁
      · have hroot₂ : [] ∈ paths₂ := (hmem []).mp hroot₁
        simp [replaceSimulAtPaths?, hroot₁] at h₁
        simp [replaceSimulAtPaths?, hroot₂] at h₂
        subst C₁
        subst C₂
        rfl
      · have hroot₂ : [] ∉ paths₂ := by
          intro h
          exact hroot₁ ((hmem []).mpr h)
        simp [replaceSimulAtPaths?, hroot₁] at h₁
        simp [replaceSimulAtPaths?, hroot₂] at h₂
        cases hL₁ : replaceSimulAtPaths? atomName L (simulChildPaths false paths₁)
          <;> simp [hL₁] at h₁
        cases hR₁ : replaceSimulAtPaths? atomName R (simulChildPaths true paths₁)
          <;> simp [hR₁] at h₁
        cases hL₂ : replaceSimulAtPaths? atomName L (simulChildPaths false paths₂)
          <;> simp [hL₂] at h₂
        cases hR₂ : replaceSimulAtPaths? atomName R (simulChildPaths true paths₂)
          <;> simp [hR₂] at h₂
        subst C₁
        subst C₂
        have hmemL :
            ∀ p, p ∈ simulChildPaths false paths₁ ↔
              p ∈ simulChildPaths false paths₂ := by
          intro p
          rw [mem_simulChildPaths_iff, mem_simulChildPaths_iff]
          exact hmem (false :: p)
        have hmemR :
            ∀ p, p ∈ simulChildPaths true paths₁ ↔
              p ∈ simulChildPaths true paths₂ := by
          intro p
          rw [mem_simulChildPaths_iff, mem_simulChildPaths_iff]
          exact hmem (true :: p)
        have hLeq :=
          replaceSimulAtPaths?_eq_of_same_members atomName L hmemL hL₁ hL₂
        have hReq :=
          replaceSimulAtPaths?_eq_of_same_members atomName R hmemR hR₁ hR₂
        rw [hLeq, hReq]
  | L ⧸ R, paths₁, paths₂, C₁, C₂, hmem, h₁, h₂ => by
      by_cases hroot₁ : [] ∈ paths₁
      · have hroot₂ : [] ∈ paths₂ := (hmem []).mp hroot₁
        simp [replaceSimulAtPaths?, hroot₁] at h₁
        simp [replaceSimulAtPaths?, hroot₂] at h₂
        subst C₁
        subst C₂
        rfl
      · have hroot₂ : [] ∉ paths₂ := by
          intro h
          exact hroot₁ ((hmem []).mpr h)
        simp [replaceSimulAtPaths?, hroot₁] at h₁
        simp [replaceSimulAtPaths?, hroot₂] at h₂
        cases hL₁ : replaceSimulAtPaths? atomName L (simulChildPaths false paths₁)
          <;> simp [hL₁] at h₁
        cases hR₁ : replaceSimulAtPaths? atomName R (simulChildPaths true paths₁)
          <;> simp [hR₁] at h₁
        cases hL₂ : replaceSimulAtPaths? atomName L (simulChildPaths false paths₂)
          <;> simp [hL₂] at h₂
        cases hR₂ : replaceSimulAtPaths? atomName R (simulChildPaths true paths₂)
          <;> simp [hR₂] at h₂
        subst C₁
        subst C₂
        have hmemL :
            ∀ p, p ∈ simulChildPaths false paths₁ ↔
              p ∈ simulChildPaths false paths₂ := by
          intro p
          rw [mem_simulChildPaths_iff, mem_simulChildPaths_iff]
          exact hmem (false :: p)
        have hmemR :
            ∀ p, p ∈ simulChildPaths true paths₁ ↔
              p ∈ simulChildPaths true paths₂ := by
          intro p
          rw [mem_simulChildPaths_iff, mem_simulChildPaths_iff]
          exact hmem (true :: p)
        have hLeq :=
          replaceSimulAtPaths?_eq_of_same_members atomName L hmemL hL₁ hL₂
        have hReq :=
          replaceSimulAtPaths?_eq_of_same_members atomName R hmemR hR₁ hR₂
        rw [hLeq, hReq]

/-- Canonical simultaneous path replacement succeeds when every requested path
points to a slash constructor. -/
theorem replaceSimulAtPaths?_exists_of_constructor_positions
    (atomName : String) :
    ∀ (C : Category) (paths : List CategoryPath),
      (∀ p ∈ paths,
        ∃ X Y, C.subcategoryAt? p = some (X ⧸ Y) ∨
          C.subcategoryAt? p = some (X ⧹ Y)) →
        ∃ C', replaceSimulAtPaths? atomName C paths = some C'
  | #name, paths, hvalid => by
      by_cases hroot : [] ∈ paths
      · exact ⟨#atomName, by simp [replaceSimulAtPaths?, hroot]⟩
      · have hnil : paths = [] := by
          cases hpaths : paths with
          | nil => rfl
          | cons p ps =>
              cases p with
              | nil =>
                  exact False.elim (hroot (by simp [hpaths]))
              | cons b q =>
                  obtain ⟨X, Y, hslash⟩ := hvalid (b :: q) (by simp [hpaths])
                  simp at hslash
        subst paths
        exact ⟨#name, by simp [replaceSimulAtPaths?]⟩
  | L ⧹ R, paths, hvalid => by
      by_cases hroot : [] ∈ paths
      · exact ⟨#atomName, by simp [replaceSimulAtPaths?, hroot]⟩
      · have hvalidL :
            ∀ p ∈ simulChildPaths false paths,
              ∃ X Y, L.subcategoryAt? p = some (X ⧸ Y) ∨
                L.subcategoryAt? p = some (X ⧹ Y) := by
          intro p hp
          have h := hvalid (false :: p)
            ((mem_simulChildPaths_iff false paths p).mp hp)
          simpa [Category.subcategoryAt?_ldiv_false] using h
        have hvalidR :
            ∀ p ∈ simulChildPaths true paths,
              ∃ X Y, R.subcategoryAt? p = some (X ⧸ Y) ∨
                R.subcategoryAt? p = some (X ⧹ Y) := by
          intro p hp
          have h := hvalid (true :: p)
            ((mem_simulChildPaths_iff true paths p).mp hp)
          simpa [Category.subcategoryAt?_ldiv_true] using h
        obtain ⟨L', hL⟩ :=
          replaceSimulAtPaths?_exists_of_constructor_positions atomName L
            (simulChildPaths false paths) hvalidL
        obtain ⟨R', hR⟩ :=
          replaceSimulAtPaths?_exists_of_constructor_positions atomName R
            (simulChildPaths true paths) hvalidR
        exact ⟨L' ⧹ R', by simp [replaceSimulAtPaths?, hroot, hL, hR]⟩
  | L ⧸ R, paths, hvalid => by
      by_cases hroot : [] ∈ paths
      · exact ⟨#atomName, by simp [replaceSimulAtPaths?, hroot]⟩
      · have hvalidL :
            ∀ p ∈ simulChildPaths false paths,
              ∃ X Y, L.subcategoryAt? p = some (X ⧸ Y) ∨
                L.subcategoryAt? p = some (X ⧹ Y) := by
          intro p hp
          have h := hvalid (false :: p)
            ((mem_simulChildPaths_iff false paths p).mp hp)
          simpa [Category.subcategoryAt?_rdiv_false] using h
        have hvalidR :
            ∀ p ∈ simulChildPaths true paths,
              ∃ X Y, R.subcategoryAt? p = some (X ⧸ Y) ∨
                R.subcategoryAt? p = some (X ⧹ Y) := by
          intro p hp
          have h := hvalid (true :: p)
            ((mem_simulChildPaths_iff true paths p).mp hp)
          simpa [Category.subcategoryAt?_rdiv_true] using h
        obtain ⟨L', hL⟩ :=
          replaceSimulAtPaths?_exists_of_constructor_positions atomName L
            (simulChildPaths false paths) hvalidL
        obtain ⟨R', hR⟩ :=
          replaceSimulAtPaths?_exists_of_constructor_positions atomName R
            (simulChildPaths true paths) hvalidR
        exact ⟨L' ⧸ R', by simp [replaceSimulAtPaths?, hroot, hL, hR]⟩

/-- Canonical simultaneous replacement by atoms does not increase constructor
count when every requested path points to a slash constructor. -/
theorem replaceSimulAtPaths?_constructors_le_of_constructor_positions
    (atomName : String) :
    ∀ (C : Category) {paths : List CategoryPath} {C' : Category},
      (∀ p ∈ paths,
        ∃ X Y, C.subcategoryAt? p = some (X ⧸ Y) ∨
          C.subcategoryAt? p = some (X ⧹ Y)) →
        replaceSimulAtPaths? atomName C paths = some C' →
          C'.constructors ≤ C.constructors
  | #name, paths, C', hvalid, hrep => by
      by_cases hroot : [] ∈ paths
      · simp [replaceSimulAtPaths?, hroot] at hrep
        subst C'
        simp [Category.constructors]
      · have hnil : paths = [] := by
          cases hpaths : paths with
          | nil => rfl
          | cons p ps =>
              cases p with
              | nil => exact False.elim (hroot (by simp [hpaths]))
              | cons b q =>
                  obtain ⟨X, Y, hslash⟩ := hvalid (b :: q) (by simp [hpaths])
                  simp at hslash
        subst paths
        simp [replaceSimulAtPaths?] at hrep
        subst C'
        omega
  | L ⧹ R, paths, C', hvalid, hrep => by
      by_cases hroot : [] ∈ paths
      · simp [replaceSimulAtPaths?, hroot] at hrep
        subst C'
        simp [Category.constructors]
      · have hvalidL :
            ∀ p ∈ simulChildPaths false paths,
              ∃ X Y, L.subcategoryAt? p = some (X ⧸ Y) ∨
                L.subcategoryAt? p = some (X ⧹ Y) := by
          intro p hp
          have h := hvalid (false :: p)
            ((mem_simulChildPaths_iff false paths p).mp hp)
          simpa [Category.subcategoryAt?_ldiv_false] using h
        have hvalidR :
            ∀ p ∈ simulChildPaths true paths,
              ∃ X Y, R.subcategoryAt? p = some (X ⧸ Y) ∨
                R.subcategoryAt? p = some (X ⧹ Y) := by
          intro p hp
          have h := hvalid (true :: p)
            ((mem_simulChildPaths_iff true paths p).mp hp)
          simpa [Category.subcategoryAt?_ldiv_true] using h
        simp [replaceSimulAtPaths?, hroot] at hrep
        cases hL : replaceSimulAtPaths? atomName L (simulChildPaths false paths)
          <;> simp [hL] at hrep
        cases hR : replaceSimulAtPaths? atomName R (simulChildPaths true paths)
          <;> simp [hR] at hrep
        subst C'
        have hLle :=
          replaceSimulAtPaths?_constructors_le_of_constructor_positions
            atomName L hvalidL hL
        have hRle :=
          replaceSimulAtPaths?_constructors_le_of_constructor_positions
            atomName R hvalidR hR
        simp [Category.constructors]
        omega
  | L ⧸ R, paths, C', hvalid, hrep => by
      by_cases hroot : [] ∈ paths
      · simp [replaceSimulAtPaths?, hroot] at hrep
        subst C'
        simp [Category.constructors]
      · have hvalidL :
            ∀ p ∈ simulChildPaths false paths,
              ∃ X Y, L.subcategoryAt? p = some (X ⧸ Y) ∨
                L.subcategoryAt? p = some (X ⧹ Y) := by
          intro p hp
          have h := hvalid (false :: p)
            ((mem_simulChildPaths_iff false paths p).mp hp)
          simpa [Category.subcategoryAt?_rdiv_false] using h
        have hvalidR :
            ∀ p ∈ simulChildPaths true paths,
              ∃ X Y, R.subcategoryAt? p = some (X ⧸ Y) ∨
                R.subcategoryAt? p = some (X ⧹ Y) := by
          intro p hp
          have h := hvalid (true :: p)
            ((mem_simulChildPaths_iff true paths p).mp hp)
          simpa [Category.subcategoryAt?_rdiv_true] using h
        simp [replaceSimulAtPaths?, hroot] at hrep
        cases hL : replaceSimulAtPaths? atomName L (simulChildPaths false paths)
          <;> simp [hL] at hrep
        cases hR : replaceSimulAtPaths? atomName R (simulChildPaths true paths)
          <;> simp [hR] at hrep
        subst C'
        have hLle :=
          replaceSimulAtPaths?_constructors_le_of_constructor_positions
            atomName L hvalidL hL
        have hRle :=
          replaceSimulAtPaths?_constructors_le_of_constructor_positions
            atomName R hvalidR hR
        simp [Category.constructors]
        omega

set_option linter.flexible false in
/-- Canonical simultaneous replacement by atoms strictly decreases constructor
count when at least one valid slash-constructor path is replaced. -/
theorem replaceSimulAtPaths?_constructors_lt_of_nonempty_constructor_positions
    (atomName : String) :
    ∀ (C : Category) {paths : List CategoryPath} {C' : Category},
      (∀ p ∈ paths,
        ∃ X Y, C.subcategoryAt? p = some (X ⧸ Y) ∨
          C.subcategoryAt? p = some (X ⧹ Y)) →
        paths ≠ [] →
          replaceSimulAtPaths? atomName C paths = some C' →
            C'.constructors < C.constructors
  | #name, paths, C', hvalid, hnonempty, hrep => by
      by_cases hroot : [] ∈ paths
      · obtain ⟨X, Y, hslash⟩ := hvalid [] hroot
        simp at hslash
      · cases hpaths : paths with
        | nil => exact False.elim (hnonempty hpaths)
        | cons p ps =>
            cases p with
            | nil => exact False.elim (hroot (by simp [hpaths]))
            | cons b q =>
                obtain ⟨X, Y, hslash⟩ := hvalid (b :: q) (by simp [hpaths])
                simp at hslash
  | L ⧹ R, paths, C', hvalid, hnonempty, hrep => by
      by_cases hroot : [] ∈ paths
      · simp [replaceSimulAtPaths?, hroot] at hrep
        subst C'
        simp [Category.constructors]
      · have hvalidL :
            ∀ p ∈ simulChildPaths false paths,
              ∃ X Y, L.subcategoryAt? p = some (X ⧸ Y) ∨
                L.subcategoryAt? p = some (X ⧹ Y) := by
          intro p hp
          have h := hvalid (false :: p)
            ((mem_simulChildPaths_iff false paths p).mp hp)
          simpa [Category.subcategoryAt?_ldiv_false] using h
        have hvalidR :
            ∀ p ∈ simulChildPaths true paths,
              ∃ X Y, R.subcategoryAt? p = some (X ⧸ Y) ∨
                R.subcategoryAt? p = some (X ⧹ Y) := by
          intro p hp
          have h := hvalid (true :: p)
            ((mem_simulChildPaths_iff true paths p).mp hp)
          simpa [Category.subcategoryAt?_ldiv_true] using h
        have hchildNonempty :
            simulChildPaths false paths ≠ [] ∨
              simulChildPaths true paths ≠ [] := by
          cases hpaths : paths with
          | nil => exact False.elim (hnonempty hpaths)
          | cons p ps =>
              cases p with
              | nil => exact False.elim (hroot (by simp [hpaths]))
              | cons b q =>
                  cases b
                  · left
                    intro hnil
                    have hq : q ∈ simulChildPaths false paths := by
                      rw [mem_simulChildPaths_iff]
                      simp [hpaths]
                    rw [hpaths] at hq
                    rw [hnil] at hq
                    cases hq
                  · right
                    intro hnil
                    have hq : q ∈ simulChildPaths true paths := by
                      rw [mem_simulChildPaths_iff]
                      simp [hpaths]
                    rw [hpaths] at hq
                    rw [hnil] at hq
                    cases hq
        simp [replaceSimulAtPaths?, hroot] at hrep
        cases hL : replaceSimulAtPaths? atomName L (simulChildPaths false paths)
          <;> simp [hL] at hrep
        cases hR : replaceSimulAtPaths? atomName R (simulChildPaths true paths)
          <;> simp [hR] at hrep
        subst C'
        rcases hchildNonempty with hleftNonempty | hrightNonempty
        · have hLlt :=
            replaceSimulAtPaths?_constructors_lt_of_nonempty_constructor_positions
              atomName L hvalidL hleftNonempty hL
          have hRle :=
            replaceSimulAtPaths?_constructors_le_of_constructor_positions
              atomName R hvalidR hR
          simp [Category.constructors]
          omega
        · have hLle :=
            replaceSimulAtPaths?_constructors_le_of_constructor_positions
              atomName L hvalidL hL
          have hRlt :=
            replaceSimulAtPaths?_constructors_lt_of_nonempty_constructor_positions
              atomName R hvalidR hrightNonempty hR
          simp [Category.constructors]
          omega
  | L ⧸ R, paths, C', hvalid, hnonempty, hrep => by
      by_cases hroot : [] ∈ paths
      · simp [replaceSimulAtPaths?, hroot] at hrep
        subst C'
        simp [Category.constructors]
      · have hvalidL :
            ∀ p ∈ simulChildPaths false paths,
              ∃ X Y, L.subcategoryAt? p = some (X ⧸ Y) ∨
                L.subcategoryAt? p = some (X ⧹ Y) := by
          intro p hp
          have h := hvalid (false :: p)
            ((mem_simulChildPaths_iff false paths p).mp hp)
          simpa [Category.subcategoryAt?_rdiv_false] using h
        have hvalidR :
            ∀ p ∈ simulChildPaths true paths,
              ∃ X Y, R.subcategoryAt? p = some (X ⧸ Y) ∨
                R.subcategoryAt? p = some (X ⧹ Y) := by
          intro p hp
          have h := hvalid (true :: p)
            ((mem_simulChildPaths_iff true paths p).mp hp)
          simpa [Category.subcategoryAt?_rdiv_true] using h
        have hchildNonempty :
            simulChildPaths false paths ≠ [] ∨
              simulChildPaths true paths ≠ [] := by
          cases hpaths : paths with
          | nil => exact False.elim (hnonempty hpaths)
          | cons p ps =>
              cases p with
              | nil => exact False.elim (hroot (by simp [hpaths]))
              | cons b q =>
                  cases b
                  · left
                    intro hnil
                    have hq : q ∈ simulChildPaths false paths := by
                      rw [mem_simulChildPaths_iff]
                      simp [hpaths]
                    rw [hpaths] at hq
                    rw [hnil] at hq
                    cases hq
                  · right
                    intro hnil
                    have hq : q ∈ simulChildPaths true paths := by
                      rw [mem_simulChildPaths_iff]
                      simp [hpaths]
                    rw [hpaths] at hq
                    rw [hnil] at hq
                    cases hq
        simp [replaceSimulAtPaths?, hroot] at hrep
        cases hL : replaceSimulAtPaths? atomName L (simulChildPaths false paths)
          <;> simp [hL] at hrep
        cases hR : replaceSimulAtPaths? atomName R (simulChildPaths true paths)
          <;> simp [hR] at hrep
        subst C'
        rcases hchildNonempty with hleftNonempty | hrightNonempty
        · have hLlt :=
            replaceSimulAtPaths?_constructors_lt_of_nonempty_constructor_positions
              atomName L hvalidL hleftNonempty hL
          have hRle :=
            replaceSimulAtPaths?_constructors_le_of_constructor_positions
              atomName R hvalidR hR
          simp [Category.constructors]
          omega
        · have hLle :=
            replaceSimulAtPaths?_constructors_le_of_constructor_positions
              atomName L hvalidL hL
          have hRlt :=
            replaceSimulAtPaths?_constructors_lt_of_nonempty_constructor_positions
              atomName R hvalidR hrightNonempty hR
          simp [Category.constructors]
          omega

set_option linter.flexible false in
/-- Atoms in a canonical simultaneous replacement result are inherited from
the host category, except for the fixed inserted atom. -/
theorem replaceSimulAtPaths?_atoms_preserved
    (atomName : String) :
    ∀ (C : Category) {paths : List CategoryPath} {C' : Category}
      {atomNames : List String},
        replaceSimulAtPaths? atomName C paths = some C' →
          (∀ name ∈ C.atoms, name ∈ atomNames) →
            atomName ∈ atomNames →
              ∀ name ∈ C'.atoms, name ∈ atomNames
  | #name, paths, C', atomNames, hrep, hhost, hatom => by
      by_cases hroot : [] ∈ paths
      · simp [replaceSimulAtPaths?, hroot] at hrep
        subst C'
        intro name hname
        simp [Category.atoms] at hname
        subst name
        exact hatom
      · simp [replaceSimulAtPaths?, hroot] at hrep
        rcases hrep with ⟨_, hC'⟩
        subst C'
        exact hhost
  | L ⧹ R, paths, C', atomNames, hrep, hhost, hatom => by
      by_cases hroot : [] ∈ paths
      · simp [replaceSimulAtPaths?, hroot] at hrep
        subst C'
        intro name hname
        simp [Category.atoms] at hname
        subst name
        exact hatom
      · simp [replaceSimulAtPaths?, hroot] at hrep
        cases hL : replaceSimulAtPaths? atomName L (simulChildPaths false paths)
          <;> simp [hL] at hrep
        cases hR : replaceSimulAtPaths? atomName R (simulChildPaths true paths)
          <;> simp [hR] at hrep
        subst C'
        intro name hname
        simp [Category.atoms] at hname
        rcases hname with hname | hname
        · exact replaceSimulAtPaths?_atoms_preserved atomName L hL
            (by
              intro nm hnm
              exact hhost nm (by simp [Category.atoms, hnm]))
            hatom name hname
        · exact replaceSimulAtPaths?_atoms_preserved atomName R hR
            (by
              intro nm hnm
              exact hhost nm (by simp [Category.atoms, hnm]))
            hatom name hname
  | L ⧸ R, paths, C', atomNames, hrep, hhost, hatom => by
      by_cases hroot : [] ∈ paths
      · simp [replaceSimulAtPaths?, hroot] at hrep
        subst C'
        intro name hname
        simp [Category.atoms] at hname
        subst name
        exact hatom
      · simp [replaceSimulAtPaths?, hroot] at hrep
        cases hL : replaceSimulAtPaths? atomName L (simulChildPaths false paths)
          <;> simp [hL] at hrep
        cases hR : replaceSimulAtPaths? atomName R (simulChildPaths true paths)
          <;> simp [hR] at hrep
        subst C'
        intro name hname
        simp [Category.atoms] at hname
        rcases hname with hname | hname
        · exact replaceSimulAtPaths?_atoms_preserved atomName L hL
            (by
              intro nm hnm
              exact hhost nm (by simp [Category.atoms, hnm]))
            hatom name hname
        · exact replaceSimulAtPaths?_atoms_preserved atomName R hR
            (by
              intro nm hnm
              exact hhost nm (by simp [Category.atoms, hnm]))
            hatom name hname

/-- If every target in `C ⧸ B` lies in the right child and those right-child
paths describe the same replacement set as `pathsRight`, canonical replacement
preserves the forward-application left-premise shape. -/
theorem replaceSimulAtPaths?_rdiv_right_only
    {atomName : String} {C B B' L' : Category}
    {pathsLeft pathsRight : List CategoryPath}
    (hleft :
      ∀ p, p ∈ pathsLeft → ∃ q, p = true :: q)
    (hright :
      ∀ p, true :: p ∈ pathsLeft ↔ p ∈ pathsRight)
    (hR :
      replaceSimulAtPaths? atomName B pathsRight = some B')
    (hL :
      replaceSimulAtPaths? atomName (C ⧸ B) pathsLeft = some L') :
    L' = C ⧸ B' := by
  have hroot : [] ∉ pathsLeft := by
    intro hmem
    obtain ⟨q, hq⟩ := hleft [] hmem
    cases hq
  have hfalse :
      simulChildPaths false pathsLeft = [] := by
    apply simulChildPaths_eq_nil_of_no_child
    intro p hmem
    obtain ⟨q, hq⟩ := hleft (false :: p) hmem
    cases hq
  have hC :
      replaceSimulAtPaths? atomName C (simulChildPaths false pathsLeft) = some C := by
    rw [hfalse]
    simp
  simp [replaceSimulAtPaths?, hroot, hC] at hL
  cases hBchild :
      replaceSimulAtPaths? atomName B (simulChildPaths true pathsLeft)
    <;> simp [hBchild] at hL
  subst L'
  have hmem :
      ∀ p, p ∈ simulChildPaths true pathsLeft ↔ p ∈ pathsRight := by
    intro p
    rw [mem_simulChildPaths_iff]
    exact hright p
  have hBeq :=
    replaceSimulAtPaths?_eq_of_same_members atomName B hmem hBchild hR
  subst hBeq
  rfl

/-- Contextual forward-application shape preservation for canonical path-set
replacement: the left premise `C ⧸ B` rewrites componentwise to `O' ⧸ R'`
when its left-child paths match the output paths and its right-child paths
match the right-premise paths. -/
theorem replaceSimulAtPaths?_rdiv_components
    {atomName : String} {C B O' R' L' : Category}
    {pathsLeft pathsOut pathsRight : List CategoryPath}
    (hroot : [] ∉ pathsLeft)
    (hout :
      ∀ p, false :: p ∈ pathsLeft ↔ p ∈ pathsOut)
    (hright :
      ∀ p, true :: p ∈ pathsLeft ↔ p ∈ pathsRight)
    (hO :
      replaceSimulAtPaths? atomName C pathsOut = some O')
    (hR :
      replaceSimulAtPaths? atomName B pathsRight = some R')
    (hL :
      replaceSimulAtPaths? atomName (C ⧸ B) pathsLeft = some L') :
    L' = O' ⧸ R' := by
  simp [replaceSimulAtPaths?, hroot] at hL
  cases hCchild :
      replaceSimulAtPaths? atomName C (simulChildPaths false pathsLeft)
    <;> simp [hCchild] at hL
  cases hBchild :
      replaceSimulAtPaths? atomName B (simulChildPaths true pathsLeft)
    <;> simp [hBchild] at hL
  subst L'
  have hmemOut :
      ∀ p, p ∈ simulChildPaths false pathsLeft ↔ p ∈ pathsOut := by
    intro p
    rw [mem_simulChildPaths_iff]
    exact hout p
  have hmemRight :
      ∀ p, p ∈ simulChildPaths true pathsLeft ↔ p ∈ pathsRight := by
    intro p
    rw [mem_simulChildPaths_iff]
    exact hright p
  have hOeq :=
    replaceSimulAtPaths?_eq_of_same_members atomName C hmemOut hCchild hO
  have hReq :=
    replaceSimulAtPaths?_eq_of_same_members atomName B hmemRight hBchild hR
  subst hOeq
  subst hReq
  rfl

/-- Contextual backward-application shape preservation for canonical path-set
replacement: the right premise `A ⧹ C` rewrites componentwise to `L' ⧹ O'`
when its left-child paths match the left-premise paths and its right-child
paths match the output paths. -/
theorem replaceSimulAtPaths?_ldiv_components
    {atomName : String} {A C L' O' R' : Category}
    {pathsRight pathsLeft pathsOut : List CategoryPath}
    (hroot : [] ∉ pathsRight)
    (hleft :
      ∀ p, false :: p ∈ pathsRight ↔ p ∈ pathsLeft)
    (hout :
      ∀ p, true :: p ∈ pathsRight ↔ p ∈ pathsOut)
    (hL :
      replaceSimulAtPaths? atomName A pathsLeft = some L')
    (hO :
      replaceSimulAtPaths? atomName C pathsOut = some O')
    (hR :
      replaceSimulAtPaths? atomName (A ⧹ C) pathsRight = some R') :
    R' = L' ⧹ O' := by
  simp [replaceSimulAtPaths?, hroot] at hR
  cases hAchild :
      replaceSimulAtPaths? atomName A (simulChildPaths false pathsRight)
    <;> simp [hAchild] at hR
  cases hCchild :
      replaceSimulAtPaths? atomName C (simulChildPaths true pathsRight)
    <;> simp [hCchild] at hR
  subst R'
  have hmemLeft :
      ∀ p, p ∈ simulChildPaths false pathsRight ↔ p ∈ pathsLeft := by
    intro p
    rw [mem_simulChildPaths_iff]
    exact hleft p
  have hmemOut :
      ∀ p, p ∈ simulChildPaths true pathsRight ↔ p ∈ pathsOut := by
    intro p
    rw [mem_simulChildPaths_iff]
    exact hout p
  have hLeq :=
    replaceSimulAtPaths?_eq_of_same_members atomName A hmemLeft hAchild hL
  have hOeq :=
    replaceSimulAtPaths?_eq_of_same_members atomName C hmemOut hCchild hO
  subst hLeq
  subst hOeq
  rfl

set_option linter.flexible false in
/-- Contextual forward-composition shape preservation for canonical path-set
replacement.  The three copied metavariables in `C/B, B/A ↦ C/A` must be
rewritten by matching child path sets. -/
theorem replaceSimulAtPaths?_compRight_components
    {atomName : String} {C B A L' R' O' : Category}
    {pathsLeft pathsRight pathsOut : List CategoryPath}
    (hleftRoot : [] ∉ pathsLeft)
    (hrightRoot : [] ∉ pathsRight)
    (houtRoot : [] ∉ pathsOut)
    (hC :
      ∀ p, false :: p ∈ pathsLeft ↔ false :: p ∈ pathsOut)
    (hB :
      ∀ p, true :: p ∈ pathsLeft ↔ false :: p ∈ pathsRight)
    (hA :
      ∀ p, true :: p ∈ pathsRight ↔ true :: p ∈ pathsOut)
    (hL :
      replaceSimulAtPaths? atomName (C ⧸ B) pathsLeft = some L')
    (hR :
      replaceSimulAtPaths? atomName (B ⧸ A) pathsRight = some R')
    (hO :
      replaceSimulAtPaths? atomName (C ⧸ A) pathsOut = some O') :
    Rule L' R' O' := by
  simp [replaceSimulAtPaths?, hleftRoot] at hL
  cases hLC :
      replaceSimulAtPaths? atomName C (simulChildPaths false pathsLeft)
    <;> simp [hLC] at hL
  cases hLB :
      replaceSimulAtPaths? atomName B (simulChildPaths true pathsLeft)
    <;> simp [hLB] at hL
  subst L'
  simp [replaceSimulAtPaths?, hrightRoot] at hR
  cases hRB :
      replaceSimulAtPaths? atomName B (simulChildPaths false pathsRight)
    <;> simp [hRB] at hR
  cases hRA :
      replaceSimulAtPaths? atomName A (simulChildPaths true pathsRight)
    <;> simp [hRA] at hR
  subst R'
  simp [replaceSimulAtPaths?, houtRoot] at hO
  cases hOC :
      replaceSimulAtPaths? atomName C (simulChildPaths false pathsOut)
    <;> simp [hOC] at hO
  cases hOA :
      replaceSimulAtPaths? atomName A (simulChildPaths true pathsOut)
    <;> simp [hOA] at hO
  subst O'
  have hCmem :
      ∀ p, p ∈ simulChildPaths false pathsLeft ↔
        p ∈ simulChildPaths false pathsOut := by
    intro p
    rw [mem_simulChildPaths_iff, mem_simulChildPaths_iff]
    exact hC p
  have hBmem :
      ∀ p, p ∈ simulChildPaths true pathsLeft ↔
        p ∈ simulChildPaths false pathsRight := by
    intro p
    rw [mem_simulChildPaths_iff, mem_simulChildPaths_iff]
    exact hB p
  have hAmem :
      ∀ p, p ∈ simulChildPaths true pathsRight ↔
        p ∈ simulChildPaths true pathsOut := by
    intro p
    rw [mem_simulChildPaths_iff, mem_simulChildPaths_iff]
    exact hA p
  have hCeq :=
    replaceSimulAtPaths?_eq_of_same_members atomName C hCmem hLC hOC
  have hBeq :=
    replaceSimulAtPaths?_eq_of_same_members atomName B hBmem hLB hRB
  have hAeq :=
    replaceSimulAtPaths?_eq_of_same_members atomName A hAmem hRA hOA
  subst hCeq
  subst hBeq
  subst hAeq
  exact Rule.compRight

set_option linter.flexible false in
/-- Contextual backward-composition shape preservation for canonical path-set
replacement.  The three copied metavariables in `A\B, B\C ↦ A\C` must be
rewritten by matching child path sets. -/
theorem replaceSimulAtPaths?_compLeft_components
    {atomName : String} {A B C L' R' O' : Category}
    {pathsLeft pathsRight pathsOut : List CategoryPath}
    (hleftRoot : [] ∉ pathsLeft)
    (hrightRoot : [] ∉ pathsRight)
    (houtRoot : [] ∉ pathsOut)
    (hA :
      ∀ p, false :: p ∈ pathsLeft ↔ false :: p ∈ pathsOut)
    (hB :
      ∀ p, true :: p ∈ pathsLeft ↔ false :: p ∈ pathsRight)
    (hC :
      ∀ p, true :: p ∈ pathsRight ↔ true :: p ∈ pathsOut)
    (hL :
      replaceSimulAtPaths? atomName (A ⧹ B) pathsLeft = some L')
    (hR :
      replaceSimulAtPaths? atomName (B ⧹ C) pathsRight = some R')
    (hO :
      replaceSimulAtPaths? atomName (A ⧹ C) pathsOut = some O') :
    Rule L' R' O' := by
  simp [replaceSimulAtPaths?, hleftRoot] at hL
  cases hLA :
      replaceSimulAtPaths? atomName A (simulChildPaths false pathsLeft)
    <;> simp [hLA] at hL
  cases hLB :
      replaceSimulAtPaths? atomName B (simulChildPaths true pathsLeft)
    <;> simp [hLB] at hL
  subst L'
  simp [replaceSimulAtPaths?, hrightRoot] at hR
  cases hRB :
      replaceSimulAtPaths? atomName B (simulChildPaths false pathsRight)
    <;> simp [hRB] at hR
  cases hRC :
      replaceSimulAtPaths? atomName C (simulChildPaths true pathsRight)
    <;> simp [hRC] at hR
  subst R'
  simp [replaceSimulAtPaths?, houtRoot] at hO
  cases hOA :
      replaceSimulAtPaths? atomName A (simulChildPaths false pathsOut)
    <;> simp [hOA] at hO
  cases hOC :
      replaceSimulAtPaths? atomName C (simulChildPaths true pathsOut)
    <;> simp [hOC] at hO
  subst O'
  have hAmem :
      ∀ p, p ∈ simulChildPaths false pathsLeft ↔
        p ∈ simulChildPaths false pathsOut := by
    intro p
    rw [mem_simulChildPaths_iff, mem_simulChildPaths_iff]
    exact hA p
  have hBmem :
      ∀ p, p ∈ simulChildPaths true pathsLeft ↔
        p ∈ simulChildPaths false pathsRight := by
    intro p
    rw [mem_simulChildPaths_iff, mem_simulChildPaths_iff]
    exact hB p
  have hCmem :
      ∀ p, p ∈ simulChildPaths true pathsRight ↔
        p ∈ simulChildPaths true pathsOut := by
    intro p
    rw [mem_simulChildPaths_iff, mem_simulChildPaths_iff]
    exact hC p
  have hAeq :=
    replaceSimulAtPaths?_eq_of_same_members atomName A hAmem hLA hOA
  have hBeq :=
    replaceSimulAtPaths?_eq_of_same_members atomName B hBmem hLB hRB
  have hCeq :=
    replaceSimulAtPaths?_eq_of_same_members atomName C hCmem hRC hOC
  subst hAeq
  subst hBeq
  subst hCeq
  exact Rule.compLeft

set_option linter.flexible false in
/-- Contextual forward crossed-composition shape preservation for canonical
path-set replacement.  The copied variables in `C/B, A\B ↦ A\C` must be
rewritten by matching child path sets. -/
theorem replaceSimulAtPaths?_crossedRight_components
    {atomName : String} {C B A L' R' O' : Category}
    {pathsLeft pathsRight pathsOut : List CategoryPath}
    (hleftRoot : [] ∉ pathsLeft)
    (hrightRoot : [] ∉ pathsRight)
    (houtRoot : [] ∉ pathsOut)
    (hC :
      ∀ p, false :: p ∈ pathsLeft ↔ true :: p ∈ pathsOut)
    (hB :
      ∀ p, true :: p ∈ pathsLeft ↔ true :: p ∈ pathsRight)
    (hA :
      ∀ p, false :: p ∈ pathsRight ↔ false :: p ∈ pathsOut)
    (hL :
      replaceSimulAtPaths? atomName (C ⧸ B) pathsLeft = some L')
    (hR :
      replaceSimulAtPaths? atomName (A ⧹ B) pathsRight = some R')
    (hO :
      replaceSimulAtPaths? atomName (A ⧹ C) pathsOut = some O') :
    Rule L' R' O' := by
  simp [replaceSimulAtPaths?, hleftRoot] at hL
  cases hLC :
      replaceSimulAtPaths? atomName C (simulChildPaths false pathsLeft)
    <;> simp [hLC] at hL
  cases hLB :
      replaceSimulAtPaths? atomName B (simulChildPaths true pathsLeft)
    <;> simp [hLB] at hL
  subst L'
  simp [replaceSimulAtPaths?, hrightRoot] at hR
  cases hRA :
      replaceSimulAtPaths? atomName A (simulChildPaths false pathsRight)
    <;> simp [hRA] at hR
  cases hRB :
      replaceSimulAtPaths? atomName B (simulChildPaths true pathsRight)
    <;> simp [hRB] at hR
  subst R'
  simp [replaceSimulAtPaths?, houtRoot] at hO
  cases hOA :
      replaceSimulAtPaths? atomName A (simulChildPaths false pathsOut)
    <;> simp [hOA] at hO
  cases hOC :
      replaceSimulAtPaths? atomName C (simulChildPaths true pathsOut)
    <;> simp [hOC] at hO
  subst O'
  have hCmem :
      ∀ p, p ∈ simulChildPaths false pathsLeft ↔
        p ∈ simulChildPaths true pathsOut := by
    intro p
    rw [mem_simulChildPaths_iff, mem_simulChildPaths_iff]
    exact hC p
  have hBmem :
      ∀ p, p ∈ simulChildPaths true pathsLeft ↔
        p ∈ simulChildPaths true pathsRight := by
    intro p
    rw [mem_simulChildPaths_iff, mem_simulChildPaths_iff]
    exact hB p
  have hAmem :
      ∀ p, p ∈ simulChildPaths false pathsRight ↔
        p ∈ simulChildPaths false pathsOut := by
    intro p
    rw [mem_simulChildPaths_iff, mem_simulChildPaths_iff]
    exact hA p
  have hCeq :=
    replaceSimulAtPaths?_eq_of_same_members atomName C hCmem hLC hOC
  have hBeq :=
    replaceSimulAtPaths?_eq_of_same_members atomName B hBmem hLB hRB
  have hAeq :=
    replaceSimulAtPaths?_eq_of_same_members atomName A hAmem hRA hOA
  subst hCeq
  subst hBeq
  subst hAeq
  exact Rule.crossedRight

set_option linter.flexible false in
/-- Contextual backward crossed-composition shape preservation for canonical
path-set replacement.  The copied variables in `B/A, B\C ↦ C/A` must be
rewritten by matching child path sets. -/
theorem replaceSimulAtPaths?_crossedLeft_components
    {atomName : String} {B A C L' R' O' : Category}
    {pathsLeft pathsRight pathsOut : List CategoryPath}
    (hleftRoot : [] ∉ pathsLeft)
    (hrightRoot : [] ∉ pathsRight)
    (houtRoot : [] ∉ pathsOut)
    (hB :
      ∀ p, false :: p ∈ pathsLeft ↔ false :: p ∈ pathsRight)
    (hA :
      ∀ p, true :: p ∈ pathsLeft ↔ true :: p ∈ pathsOut)
    (hC :
      ∀ p, true :: p ∈ pathsRight ↔ false :: p ∈ pathsOut)
    (hL :
      replaceSimulAtPaths? atomName (B ⧸ A) pathsLeft = some L')
    (hR :
      replaceSimulAtPaths? atomName (B ⧹ C) pathsRight = some R')
    (hO :
      replaceSimulAtPaths? atomName (C ⧸ A) pathsOut = some O') :
    Rule L' R' O' := by
  simp [replaceSimulAtPaths?, hleftRoot] at hL
  cases hLB :
      replaceSimulAtPaths? atomName B (simulChildPaths false pathsLeft)
    <;> simp [hLB] at hL
  cases hLA :
      replaceSimulAtPaths? atomName A (simulChildPaths true pathsLeft)
    <;> simp [hLA] at hL
  subst L'
  simp [replaceSimulAtPaths?, hrightRoot] at hR
  cases hRB :
      replaceSimulAtPaths? atomName B (simulChildPaths false pathsRight)
    <;> simp [hRB] at hR
  cases hRC :
      replaceSimulAtPaths? atomName C (simulChildPaths true pathsRight)
    <;> simp [hRC] at hR
  subst R'
  simp [replaceSimulAtPaths?, houtRoot] at hO
  cases hOC :
      replaceSimulAtPaths? atomName C (simulChildPaths false pathsOut)
    <;> simp [hOC] at hO
  cases hOA :
      replaceSimulAtPaths? atomName A (simulChildPaths true pathsOut)
    <;> simp [hOA] at hO
  subst O'
  have hBmem :
      ∀ p, p ∈ simulChildPaths false pathsLeft ↔
        p ∈ simulChildPaths false pathsRight := by
    intro p
    rw [mem_simulChildPaths_iff, mem_simulChildPaths_iff]
    exact hB p
  have hAmem :
      ∀ p, p ∈ simulChildPaths true pathsLeft ↔
        p ∈ simulChildPaths true pathsOut := by
    intro p
    rw [mem_simulChildPaths_iff, mem_simulChildPaths_iff]
    exact hA p
  have hCmem :
      ∀ p, p ∈ simulChildPaths true pathsRight ↔
        p ∈ simulChildPaths false pathsOut := by
    intro p
    rw [mem_simulChildPaths_iff, mem_simulChildPaths_iff]
    exact hC p
  have hBeq :=
    replaceSimulAtPaths?_eq_of_same_members atomName B hBmem hLB hRB
  have hAeq :=
    replaceSimulAtPaths?_eq_of_same_members atomName A hAmem hLA hOA
  have hCeq :=
    replaceSimulAtPaths?_eq_of_same_members atomName C hCmem hRC hOC
  subst hBeq
  subst hAeq
  subst hCeq
  exact Rule.crossedLeft

set_option linter.flexible false in
/-- Forward type-raising shape preservation for canonical path-set
replacement.  The protected skeleton paths `[]` and `[true]` are assumed
target-free; the remaining paths must synchronize the child `A` copy with the
output `A` copy and the two output `C` copies with each other. -/
theorem replaceSimulAtPaths?_typeRaiseRight_shape
    {atomName : String} {A C A' O' : Category}
    {pathsOut pathsChild : List CategoryPath}
    (houter : [] ∉ pathsOut)
    (hinner : [true] ∉ pathsOut)
    (hA :
      ∀ p, true :: false :: p ∈ pathsOut ↔ p ∈ pathsChild)
    (hC :
      ∀ p, false :: p ∈ pathsOut ↔ true :: true :: p ∈ pathsOut)
    (hChild :
      replaceSimulAtPaths? atomName A pathsChild = some A')
    (hOut :
      replaceSimulAtPaths? atomName (C ⧸ (A ⧹ C)) pathsOut = some O') :
    ∃ C', O' = C' ⧸ (A' ⧹ C') := by
  simp [replaceSimulAtPaths?, houter] at hOut
  cases hCleft :
      replaceSimulAtPaths? atomName C (simulChildPaths false pathsOut)
    <;> simp [hCleft] at hOut
  have hinnerRoot :
      [] ∉ simulChildPaths true pathsOut := by
    intro hmem
    exact hinner ((mem_simulChildPaths_iff true pathsOut []).mp hmem)
  simp [hinnerRoot] at hOut
  cases hAchild :
      replaceSimulAtPaths? atomName A
        (simulChildPaths false (simulChildPaths true pathsOut))
    <;> simp [hAchild] at hOut
  cases hCright :
      replaceSimulAtPaths? atomName C
        (simulChildPaths true (simulChildPaths true pathsOut))
    <;> simp [hCright] at hOut
  subst O'
  have hmemA :
      ∀ p, p ∈ simulChildPaths false (simulChildPaths true pathsOut) ↔
        p ∈ pathsChild := by
    intro p
    rw [mem_simulChildPaths_iff, mem_simulChildPaths_iff]
    exact hA p
  have hAeq :=
    replaceSimulAtPaths?_eq_of_same_members atomName A hmemA hAchild hChild
  have hmemC :
      ∀ p, p ∈ simulChildPaths false pathsOut ↔
        p ∈ simulChildPaths true (simulChildPaths true pathsOut) := by
    intro p
    rw [mem_simulChildPaths_iff, mem_simulChildPaths_iff,
      mem_simulChildPaths_iff]
    exact hC p
  have hCeq :=
    replaceSimulAtPaths?_eq_of_same_members atomName C hmemC hCleft hCright
  subst hAeq
  subst hCeq
  exact ⟨_, rfl⟩

set_option linter.flexible false in
/-- Backward type-raising shape preservation for canonical path-set
replacement.  The protected skeleton paths `[]` and `[false]` are assumed
target-free; the remaining paths synchronize the child `A` copy with the
output `A` copy and the two output `C` copies with each other. -/
theorem replaceSimulAtPaths?_typeRaiseLeft_shape
    {atomName : String} {A C A' O' : Category}
    {pathsOut pathsChild : List CategoryPath}
    (houter : [] ∉ pathsOut)
    (hinner : [false] ∉ pathsOut)
    (hA :
      ∀ p, false :: true :: p ∈ pathsOut ↔ p ∈ pathsChild)
    (hC :
      ∀ p, false :: false :: p ∈ pathsOut ↔ true :: p ∈ pathsOut)
    (hChild :
      replaceSimulAtPaths? atomName A pathsChild = some A')
    (hOut :
      replaceSimulAtPaths? atomName ((C ⧸ A) ⧹ C) pathsOut = some O') :
    ∃ C', O' = (C' ⧸ A') ⧹ C' := by
  simp [replaceSimulAtPaths?, houter] at hOut
  have hinnerRoot :
      [] ∉ simulChildPaths false pathsOut := by
    intro hmem
    exact hinner ((mem_simulChildPaths_iff false pathsOut []).mp hmem)
  simp [hinnerRoot] at hOut
  cases hCleft :
      replaceSimulAtPaths? atomName C
        (simulChildPaths false (simulChildPaths false pathsOut))
    <;> simp [hCleft] at hOut
  cases hAchild :
      replaceSimulAtPaths? atomName A
        (simulChildPaths true (simulChildPaths false pathsOut))
    <;> simp [hAchild] at hOut
  cases hCright :
      replaceSimulAtPaths? atomName C (simulChildPaths true pathsOut)
    <;> simp [hCright] at hOut
  subst O'
  have hmemA :
      ∀ p, p ∈ simulChildPaths true (simulChildPaths false pathsOut) ↔
        p ∈ pathsChild := by
    intro p
    rw [mem_simulChildPaths_iff, mem_simulChildPaths_iff]
    exact hA p
  have hAeq :=
    replaceSimulAtPaths?_eq_of_same_members atomName A hmemA hAchild hChild
  have hmemC :
      ∀ p, p ∈ simulChildPaths false (simulChildPaths false pathsOut) ↔
        p ∈ simulChildPaths true pathsOut := by
    intro p
    rw [mem_simulChildPaths_iff, mem_simulChildPaths_iff,
      mem_simulChildPaths_iff]
    exact hC p
  have hCeq :=
    replaceSimulAtPaths?_eq_of_same_members atomName C hmemC hCleft hCright
  subst hAeq
  subst hCeq
  exact ⟨_, rfl⟩

/-- Reading a subcategory after an appended position is the same as first
reading the prefix subcategory and then reading the suffix inside it. -/
theorem subcategoryAt?_append : ∀ (A : Category) (p q : CategoryPath) (B : Category),
    A.subcategoryAt? p = some B → A.subcategoryAt? (p ++ q) = B.subcategoryAt? q := by
  intro A
  induction A with
  | atom _ =>
      intro p q B h
      cases p with
      | nil =>
          simp only [Category.subcategoryAt?_nil, Option.some.injEq] at h
          subst B
          rfl
      | cons _ _ => simp only [Category.subcategoryAt?_atom_cons, reduceCtorEq] at h
  | ldiv L R ihL ihR =>
      intro p q B h
      cases p with
      | nil =>
          simp only [Category.subcategoryAt?_nil, Option.some.injEq] at h
          subst B
          rfl
      | cons b p =>
          cases b
          · simp only [List.cons_append, Category.subcategoryAt?_ldiv_false] at h ⊢
            exact ihL p q B h
          · simp only [List.cons_append, Category.subcategoryAt?_ldiv_true] at h ⊢
            exact ihR p q B h
  | rdiv L R ihL ihR =>
      intro p q B h
      cases p with
      | nil =>
          simp only [Category.subcategoryAt?_nil, Option.some.injEq] at h
          subst B
          rfl
      | cons b p =>
          cases b
          · simp only [List.cons_append, Category.subcategoryAt?_rdiv_false] at h ⊢
            exact ihL p q B h
          · simp only [List.cons_append, Category.subcategoryAt?_rdiv_true] at h ⊢
            exact ihR p q B h

/-- A subcategory never has more slash constructors than the category that
contains it. -/
theorem constructors_le_of_subcategoryAt? : ∀ (A : Category) (p : CategoryPath) (B : Category),
    A.subcategoryAt? p = some B → B.constructors ≤ A.constructors := by
  intro A
  induction A with
  | atom _ =>
      intro p B h
      cases p with
      | nil =>
          simp only [Category.subcategoryAt?_nil, Option.some.injEq] at h
          subst B
          simp
      | cons _ _ => simp only [Category.subcategoryAt?_atom_cons, reduceCtorEq] at h
  | ldiv L R ihL ihR =>
      intro p B h
      cases p with
      | nil =>
          simp only [Category.subcategoryAt?_nil, Option.some.injEq] at h
          subst B
          simp
      | cons b p =>
          cases b
          · simp only [Category.subcategoryAt?_ldiv_false] at h
            have := ihL p B h
            simp [Category.constructors]; omega
          · simp only [Category.subcategoryAt?_ldiv_true] at h
            have := ihR p B h
            simp [Category.constructors]; omega
  | rdiv L R ihL ihR =>
      intro p B h
      cases p with
      | nil =>
          simp only [Category.subcategoryAt?_nil, Option.some.injEq] at h
          subst B
          simp
      | cons b p =>
          cases b
          · simp only [Category.subcategoryAt?_rdiv_false] at h
            have := ihL p B h
            simp [Category.constructors]; omega
          · simp only [Category.subcategoryAt?_rdiv_true] at h
            have := ihR p B h
            simp [Category.constructors]; omega

/-- A proper subcategory has strictly fewer slash constructors than the category
that contains it. -/
theorem constructors_lt_of_subcategoryAt?_nonempty : ∀ (A : Category) (p : CategoryPath) (B : Category),
    p ≠ [] → A.subcategoryAt? p = some B → B.constructors < A.constructors := by
  intro A
  induction A with
  | atom _ =>
      intro p B hp h
      cases p with
      | nil => contradiction
      | cons _ _ => simp only [Category.subcategoryAt?_atom_cons, reduceCtorEq] at h
  | ldiv L R _ _ =>
      intro p B hp h
      cases p with
      | nil => contradiction
      | cons b p =>
          cases b
          · simp only [Category.subcategoryAt?_ldiv_false] at h
            have := constructors_le_of_subcategoryAt? L p B h
            simp [Category.constructors]; omega
          · simp only [Category.subcategoryAt?_ldiv_true] at h
            have := constructors_le_of_subcategoryAt? R p B h
            simp [Category.constructors]; omega
  | rdiv L R _ _ =>
      intro p B hp h
      cases p with
      | nil => contradiction
      | cons b p =>
          cases b
          · simp only [Category.subcategoryAt?_rdiv_false] at h
            have := constructors_le_of_subcategoryAt? L p B h
            simp [Category.constructors]; omega
          · simp only [Category.subcategoryAt?_rdiv_true] at h
            have := constructors_le_of_subcategoryAt? R p B h
            simp [Category.constructors]; omega

/-- If `p` is a strict prefix of `q`, the subcategory at `q` is strictly smaller
than the subcategory at `p`. -/
theorem constructors_lt_of_strictPrefix_subcategoryAt?
    {A S T : Category} {p q : CategoryPath}
    (hp : A.subcategoryAt? p = some S) (hq : A.subcategoryAt? q = some T)
    (hprefix : CategoryPath.StrictPrefix p q) : T.constructors < S.constructors := by
  rcases hprefix with ⟨rest, hrest, rfl⟩
  have hsub : S.subcategoryAt? rest = some T := by
    rw [← Category.subcategoryAt?_append A p rest S hp]
    simpa using hq
  exact constructors_lt_of_subcategoryAt?_nonempty S rest T hrest hsub

end Category

namespace PieceReplacementFamilyCore

/-- Rewrite one node category by applying the deduplicated piece replacements
assigned to that node. -/
def rewriteNodeCategory?
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    (nodePath : NodePath) (C : Category) : Option Category :=
  C.replaceManySubcategories? (F.dedupCategoryTargetsAt nodePath)

/-- Canonical path-set rewrite used for rule-shape preservation experiments.
It uses the same node-local replacement paths as `rewriteNodeCategory?`, but
applies the fixed piece atom simultaneously rather than sequentially. -/
def rewriteNodeCategorySimul?
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    (nodePath : NodePath) (C : Category) : Option Category :=
  Category.replaceSimulAtPaths? F.atomName C (F.categoryTargetPathsAt nodePath)

/-- Node-local rewrites succeed at actual derivation nodes. -/
theorem rewriteNodeCategory?_success
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    {nodePath : NodePath} {C : Category}
    (hnode : t.categoryAt? nodePath = some C) :
    ∃ C', F.rewriteNodeCategory? nodePath C = some C' := by
  unfold rewriteNodeCategory?
  apply Category.replaceManySubcategories?_exists_of_disjoint
  · intro target htarget
    have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
    obtain ⟨R, _hR, hRnode, htargetEq⟩ :=
      (F.mem_categoryTargetsAt_iff nodePath target).mp hprojected
    have hnodeAtC : t.categoryAt? R.nodePath = some C := by
      simpa [hRnode] using hnode
    have hcat : R.nodeCategory = C :=
      Option.some.inj (R.nodeAt.symm.trans hnodeAtC)
    refine ⟨R.old, ?_⟩
    simpa [htargetEq, hcat]
      using R.old_at
  · exact F.dedupCategoryTargetsAt_positions_nodup nodePath
  · exact F.dedupCategoryTargetsAt_disjoint nodePath

/-- Every deduplicated node-local target is valid in the original node category
and strictly shrinks the subcategory it replaces. -/
theorem dedupCategoryTargetsAt_valid_decreasing
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    {nodePath : NodePath} {C : Category}
    (hnode : t.categoryAt? nodePath = some C) :
    ∀ target ∈ F.dedupCategoryTargetsAt nodePath,
      ∃ old, C.subcategoryAt? target.1 = some old ∧
        target.2.constructors < old.constructors := by
  intro target htarget
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff nodePath target).mp hprojected
  have hnodeAtC : t.categoryAt? R.nodePath = some C := by
    simpa [hRnode] using hnode
  have hcat : R.nodeCategory = C :=
    Option.some.inj (R.nodeAt.symm.trans hnodeAtC)
  refine ⟨R.old, ?_, ?_⟩
  · simpa [htargetEq, hcat] using R.old_at
  · simpa [htargetEq] using
      PieceReplacementTarget.new_constructors_lt_old_of_atom R (F.target_new R hR)

/-- Node-local rewrites do not increase constructor count. -/
theorem rewriteNodeCategory?_constructors_le
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    {nodePath : NodePath} {C C' : Category}
    (hnode : t.categoryAt? nodePath = some C)
    (hrep : F.rewriteNodeCategory? nodePath C = some C') :
    C'.constructors ≤ C.constructors := by
  unfold rewriteNodeCategory? at hrep
  exact Category.replaceManySubcategories?_constructors_le_of_disjoint C
    (F.dedupCategoryTargetsAt_valid_decreasing hnode)
    (F.dedupCategoryTargetsAt_positions_nodup nodePath)
    (F.dedupCategoryTargetsAt_disjoint nodePath)
    hrep

/-- Node-local rewrites strictly decrease constructor count at nodes that have
at least one replacement target. -/
theorem rewriteNodeCategory?_constructors_lt_of_target
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    {nodePath : NodePath} {C C' : Category}
    (hnode : t.categoryAt? nodePath = some C)
    (hrep : F.rewriteNodeCategory? nodePath C = some C')
    {R : PieceReplacementTarget P}
    (hR : R ∈ F.targets) (hRnode : R.nodePath = nodePath) :
    C'.constructors < C.constructors := by
  unfold rewriteNodeCategory? at hrep
  have hnonempty : F.dedupCategoryTargetsAt nodePath ≠ [] := by
    intro hnil
    have hmem := F.mem_dedupCategoryTargetsAt_of_target hR hRnode
    simpa [hnil] using hmem
  exact Category.replaceManySubcategories?_constructors_lt_of_nonempty_disjoint
    (F.dedupCategoryTargetsAt_valid_decreasing hnode)
    (F.dedupCategoryTargetsAt_positions_nodup nodePath)
    (F.dedupCategoryTargetsAt_disjoint nodePath)
    hnonempty
    hrep

/-- Node-local rewrites preserve the problem-atom invariant when the original
node category satisfies it. -/
theorem rewriteNodeCategory?_atoms_preserved
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    {nodePath : NodePath} {C C' : Category}
    (hrep : F.rewriteNodeCategory? nodePath C = some C')
    (hhost : ∀ name ∈ C.atoms, name ∈ problemAtomNames Γ A) :
    ∀ name ∈ C'.atoms, name ∈ problemAtomNames Γ A := by
  unfold rewriteNodeCategory? at hrep
  apply Category.replaceManySubcategories?_atoms_preserved hrep hhost
  intro target htarget name hname
  have htargetInfo :=
    (F.mem_dedupCategoryTargetsAt_iff nodePath target).mp htarget
  simp only [htargetInfo.2, Category.atoms, List.mem_singleton] at hname
  subst name
  exact F.atom_mem

/-- Every canonical path target at an actual derivation node is a valid slash
constructor position in the original node category. -/
theorem categoryTargetPathsAt_valid
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    {nodePath : NodePath} {C : Category}
    (hnode : t.categoryAt? nodePath = some C) :
    ∀ p ∈ F.categoryTargetPathsAt nodePath,
      ∃ X Y, C.subcategoryAt? p = some (X ⧸ Y) ∨
        C.subcategoryAt? p = some (X ⧹ Y) := by
  intro p hp
  obtain ⟨R, _hR, hRnode, hpos⟩ :=
    (F.mem_categoryTargetPathsAt_iff nodePath p).mp hp
  have hnodeAtC : t.categoryAt? R.nodePath = some C := by
    simpa [hRnode] using hnode
  have hcat : R.nodeCategory = C :=
    Option.some.inj (R.nodeAt.symm.trans hnodeAtC)
  rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
  · refine ⟨X, Y, Or.inl ?_⟩
    have hslash' : R.nodeCategory.subcategoryAt? R.pos = some (X ⧸ Y) := by
      simpa [R.cat_eq, R.pos_eq] using hslash
    simpa [hcat, hpos] using hslash'
  · refine ⟨X, Y, Or.inr ?_⟩
    have hslash' : R.nodeCategory.subcategoryAt? R.pos = some (X ⧹ Y) := by
      simpa [R.cat_eq, R.pos_eq] using hslash
    simpa [hcat, hpos] using hslash'

/-- Canonical node-local rewrites succeed at actual derivation nodes. -/
theorem rewriteNodeCategorySimul?_success
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    {nodePath : NodePath} {C : Category}
    (hnode : t.categoryAt? nodePath = some C) :
    ∃ C', F.rewriteNodeCategorySimul? nodePath C = some C' := by
  unfold rewriteNodeCategorySimul?
  exact Category.replaceSimulAtPaths?_exists_of_constructor_positions
    F.atomName C (F.categoryTargetPathsAt nodePath)
      (F.categoryTargetPathsAt_valid hnode)

/-- Canonical node-local rewrites do not increase constructor count. -/
theorem rewriteNodeCategorySimul?_constructors_le
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    {nodePath : NodePath} {C C' : Category}
    (hnode : t.categoryAt? nodePath = some C)
    (hrep : F.rewriteNodeCategorySimul? nodePath C = some C') :
    C'.constructors ≤ C.constructors := by
  unfold rewriteNodeCategorySimul? at hrep
  exact Category.replaceSimulAtPaths?_constructors_le_of_constructor_positions
    F.atomName C (F.categoryTargetPathsAt_valid hnode) hrep

/-- Canonical node-local rewrites strictly decrease constructor count at nodes
that have at least one replacement target. -/
theorem rewriteNodeCategorySimul?_constructors_lt_of_target
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    {nodePath : NodePath} {C C' : Category}
    (hnode : t.categoryAt? nodePath = some C)
    (hrep : F.rewriteNodeCategorySimul? nodePath C = some C')
    {R : PieceReplacementTarget P}
    (hR : R ∈ F.targets) (hRnode : R.nodePath = nodePath) :
    C'.constructors < C.constructors := by
  unfold rewriteNodeCategorySimul? at hrep
  have hpath : R.pos ∈ F.categoryTargetPathsAt nodePath := by
    rw [F.mem_categoryTargetPathsAt_iff nodePath R.pos]
    exact ⟨R, hR, hRnode, rfl⟩
  have hnonempty : F.categoryTargetPathsAt nodePath ≠ [] := by
    intro hnil
    simpa [hnil] using hpath
  exact Category.replaceSimulAtPaths?_constructors_lt_of_nonempty_constructor_positions
    F.atomName C (F.categoryTargetPathsAt_valid hnode) hnonempty hrep

/-- Canonical node-local rewrites preserve the problem-atom invariant when the
original node category satisfies it. -/
theorem rewriteNodeCategorySimul?_atoms_preserved
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    {nodePath : NodePath} {C C' : Category}
    (hrep : F.rewriteNodeCategorySimul? nodePath C = some C')
    (hhost : ∀ name ∈ C.atoms, name ∈ problemAtomNames Γ A) :
    ∀ name ∈ C'.atoms, name ∈ problemAtomNames Γ A := by
  unfold rewriteNodeCategorySimul? at hrep
  exact Category.replaceSimulAtPaths?_atoms_preserved
    F.atomName C hrep hhost F.atom_mem

/-- If the family has no target at a node, the deduplicated category target list
for that node is empty. -/
theorem dedupCategoryTargetsAt_eq_nil_of_no_targets
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    {nodePath : NodePath}
    (hno : ∀ R : PieceReplacementTarget P, R ∈ F.targets → R.nodePath ≠ nodePath) :
    F.dedupCategoryTargetsAt nodePath = [] := by
  cases htargets : F.dedupCategoryTargetsAt nodePath with
  | nil => rfl
  | cons target rest =>
      have hmem : target ∈ F.dedupCategoryTargetsAt nodePath := by
        simp [htargets]
      have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt hmem
      obtain ⟨R, hR, hRnode, _htargetEq⟩ :=
        (F.mem_categoryTargetsAt_iff nodePath target).mp hprojected
      exact False.elim ((hno R hR) hRnode)

/-- Rewriting a node with no assigned targets is the identity rewrite. -/
theorem rewriteNodeCategory?_eq_self_of_no_targets
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    {nodePath : NodePath} {C : Category}
    (hno : ∀ R : PieceReplacementTarget P, R ∈ F.targets → R.nodePath ≠ nodePath) :
    F.rewriteNodeCategory? nodePath C = some C := by
  unfold rewriteNodeCategory?
  rw [F.dedupCategoryTargetsAt_eq_nil_of_no_targets hno]
  simp

/-- If the family has no target at a node, the canonical path-target list for
that node is empty. -/
theorem categoryTargetPathsAt_eq_nil_of_no_targets
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    {nodePath : NodePath}
    (hno : ∀ R : PieceReplacementTarget P, R ∈ F.targets → R.nodePath ≠ nodePath) :
    F.categoryTargetPathsAt nodePath = [] := by
  have h := F.dedupCategoryTargetsAt_eq_nil_of_no_targets hno
  cases hpaths : F.categoryTargetPathsAt nodePath with
  | nil => rfl
  | cons p ps =>
      rw [dedupCategoryTargetsAt, hpaths] at h
      simp at h

/-- Canonical node-local rewriting is also the identity when no replacement
target is assigned to the node. -/
theorem rewriteNodeCategorySimul?_eq_self_of_no_targets
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    {nodePath : NodePath} {C : Category}
    (hno : ∀ R : PieceReplacementTarget P, R ∈ F.targets → R.nodePath ≠ nodePath) :
    F.rewriteNodeCategorySimul? nodePath C = some C := by
  unfold rewriteNodeCategorySimul?
  rw [F.categoryTargetPathsAt_eq_nil_of_no_targets hno]
  simp

/-- The derivation root has no replacement targets. -/
theorem dedupCategoryTargetsAt_root_eq_nil
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P) :
    F.dedupCategoryTargetsAt ([] : NodePath) = [] :=
  F.dedupCategoryTargetsAt_eq_nil_of_no_targets
    (by
      intro R hR hnode
      exact F.root_free R hR hnode)

/-- Rewriting the derivation root category is the identity rewrite. -/
theorem rewriteNodeCategory?_root
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    (C : Category) :
    F.rewriteNodeCategory? ([] : NodePath) C = some C := by
  unfold rewriteNodeCategory?
  rw [F.dedupCategoryTargetsAt_root_eq_nil]
  simp

/-- Canonical path-set rewriting also leaves the derivation root category
unchanged. -/
theorem rewriteNodeCategorySimul?_root
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    (C : Category) :
    F.rewriteNodeCategorySimul? ([] : NodePath) C = some C :=
  F.rewriteNodeCategorySimul?_eq_self_of_no_targets
    (by
      intro R hR hnode
      exact F.root_free R hR hnode)

/-- Leaf nodes have no replacement targets. -/
theorem dedupCategoryTargetsAt_leaf_eq_nil
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    {nodePath : NodePath}
    (hleaf : t.isLeafNode nodePath) :
    F.dedupCategoryTargetsAt nodePath = [] :=
  F.dedupCategoryTargetsAt_eq_nil_of_no_targets
    (by
      intro R hR hnode
      exact F.leaf_free R hR (by simpa [hnode] using hleaf))

/-- Rewriting a leaf node category is the identity rewrite. -/
theorem rewriteNodeCategory?_leaf
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    {nodePath : NodePath} {C : Category}
    (hleaf : t.isLeafNode nodePath) :
    F.rewriteNodeCategory? nodePath C = some C := by
  unfold rewriteNodeCategory?
  rw [F.dedupCategoryTargetsAt_leaf_eq_nil hleaf]
  simp

/-- Canonical path-set rewriting leaves leaf node categories unchanged. -/
theorem rewriteNodeCategorySimul?_leaf
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    {nodePath : NodePath} {C : Category}
    (hleaf : t.isLeafNode nodePath) :
    F.rewriteNodeCategorySimul? nodePath C = some C :=
  F.rewriteNodeCategorySimul?_eq_self_of_no_targets
    (by
      intro R hR hnode
      exact F.leaf_free R hR (by simpa [hnode] using hleaf))

/-- A deduplicated node-local target is never a binary-rule principal
constructor. -/
theorem not_principal_of_mem_dedupCategoryTargetsAt
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    {nodePath : NodePath} {target : CategoryPath × Category}
    (htarget : target ∈ F.dedupCategoryTargetsAt nodePath) :
    ¬ DerivationTree.PrincipalConstructor t nodePath target.1 := by
  intro hprincipal
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff nodePath target).mp hprojected
  exact F.principal_free R hR (by simpa [hRnode, htargetEq] using hprincipal)

/-- No deduplicated target can have the path of a principal constructor at its
node. -/
theorem target_path_ne_of_principal
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    {nodePath : NodePath} {cpos : CategoryPath}
    (hprincipal : DerivationTree.PrincipalConstructor t nodePath cpos)
    {target : CategoryPath × Category}
    (htarget : target ∈ F.dedupCategoryTargetsAt nodePath) :
    target.1 ≠ cpos := by
  intro hsame
  exact F.not_principal_of_mem_dedupCategoryTargetsAt htarget (by simpa [hsame])

/-- Trace closure projected to the deduplicated node-local category targets. -/
theorem mem_dedupCategoryTargetsAt_of_traceEdge
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    {R : PieceReplacementTarget P} (hR : R ∈ F.targets)
    {o' : Occurrence t} (hedge : TraceEdge R.origin o') :
    (o'.categoryPath, #F.atomName) ∈ F.dedupCategoryTargetsAt o'.nodePath := by
  obtain ⟨R', hR', hR'origin⟩ := F.trace_closed R hR o' hedge
  have hnode : R'.nodePath = o'.nodePath := by
    simpa [hR'origin] using R'.node_eq
  have hmem := F.mem_dedupCategoryTargetsAt_of_target hR' hnode
  have hpos : R'.pos = o'.categoryPath := by
    simpa [hR'origin] using R'.pos_eq
  simpa [hpos, F.target_new R' hR'] using hmem

/-- Trace closure transported through a packaged derivation context, projected
to the deduplicated node-local target list. -/
theorem mem_dedupCategoryTargetsAt_of_lifted_traceEdge
    {Γ : List Category} {A : Category} {Ω : List Category} {Z : Category}
    {localTree : DerivationTree Γ A}
    (ctx : DerivationContext Γ A Ω Z)
    {P : InvisiblePiece (ctx.plug localTree)}
    (F : PieceReplacementFamilyCore P)
    {R : PieceReplacementTarget P} (hR : R ∈ F.targets)
    {o₁ o₂ : Occurrence localTree}
    (hnode : R.origin.nodePath = ctx.nodePrefix ++ o₁.nodePath)
    (hcat : R.origin.nodeCategory = o₁.nodeCategory)
    (hpos : R.origin.categoryPath = o₁.categoryPath)
    (hedge : TraceEdge o₁ o₂) :
    (o₂.categoryPath, #F.atomName) ∈
      F.dedupCategoryTargetsAt (ctx.nodePrefix ++ o₂.nodePath) := by
  have horiginEq : R.origin = ctx.liftOccurrence o₁ := by
    exact DerivationContext.occurrence_eq_lift ctx hnode hcat hpos
  have hedgeCtx := ctx.liftTraceEdge hedge
  have htarget :=
    F.mem_dedupCategoryTargetsAt_of_traceEdge hR
      (by simpa [horiginEq] using hedgeCtx)
  have hnode₂ : (ctx.liftOccurrence o₂).nodePath = ctx.nodePrefix ++ o₂.nodePath :=
    ctx.liftOccurrence_nodePath o₂
  have hpos₂ : (ctx.liftOccurrence o₂).categoryPath = o₂.categoryPath :=
    ctx.liftOccurrence_categoryPath o₂
  simpa [hnode₂, hpos₂] using htarget

/-- In a contextual forward application, the principal slash at the left child
is still target-free. -/
theorem appRight_left_root_not_target_at
    {Γ Δ Ω : List Category} {C B A : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ B}
    (ctx : DerivationContext (Γ ++ Δ) C Ω A)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.appRight))}
    (F : PieceReplacementFamilyCore P) :
    ([], #F.atomName) ∉ F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left]) := by
  intro htarget
  have hprincipalLocal :
      DerivationTree.PrincipalConstructor
        (DerivationTree.binary t₁ t₂ Rule.appRight) [.left] [] :=
    DerivationTree.PrincipalConstructor.appRight_left t₁ t₂
  have hprincipal :
      DerivationTree.PrincipalConstructor
        (ctx.plug (DerivationTree.binary t₁ t₂ Rule.appRight))
        (ctx.nodePrefix ++ [.left]) [] :=
    ctx.liftPrincipalConstructor hprincipalLocal
  have hne := F.target_path_ne_of_principal hprincipal htarget
  exact hne rfl

/-- In a contextual forward application, replacing the left-premise result copy
forces the matching output copy to be replaced. -/
theorem appRight_left_result_copy_target_to_output_at
    {Γ Δ Ω : List Category} {C B A : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ B}
    (ctx : DerivationContext (Γ ++ Δ) C Ω A)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.appRight))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget :
      (false :: p, #F.atomName) ∈
        F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left])) :
    (p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix := by
  let localTree := DerivationTree.binary t₁ t₂ Rule.appRight
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
      (false :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = false :: p :=
    (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? (ctx.nodePrefix ++ [.left]) = some (C ⧸ B) :=
    ctx.categoryAt?_local (by simp [localTree, DerivationTree.categoryAt?])
  have hRcat : R.nodeCategory = C ⧸ B := by
    have hnodeAtR : (ctx.plug localTree).categoryAt? R.nodePath = some (C ⧸ B) := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix ++ [.left] := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = false :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = C ⧸ B := by
    rw [← R.cat_eq]
    exact hRcat
  let oLeftLocal : Occurrence localTree := {
    nodePath := [.left]
    nodeCategory := C ⧸ B
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := false :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · refine ⟨X, Y, Or.inl ?_⟩
        have hslash' : (C ⧸ B).subcategoryAt? (false :: p) = some (X ⧸ Y) := by
          simpa [horiginCat, horiginPos] using hslash
        simpa [Category.subcategoryAt?_rdiv_false] using hslash'
      · refine ⟨X, Y, Or.inr ?_⟩
        have hslash' : (C ⧸ B).subcategoryAt? (false :: p) = some (X ⧹ Y) := by
          simpa [horiginCat, horiginPos] using hslash
        simpa [Category.subcategoryAt?_rdiv_false] using hslash'
  }
  let oOutLocal : Occurrence localTree := {
    nodePath := []
    nodeCategory := C
    nodeAt := DerivationTree.categoryAt?_root localTree
    categoryPath := p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · refine ⟨X, Y, Or.inl ?_⟩
        have hslash' : (C ⧸ B).subcategoryAt? (false :: p) = some (X ⧸ Y) := by
          simpa [horiginCat, horiginPos] using hslash
        simpa [Category.subcategoryAt?_rdiv_false] using hslash'
      · refine ⟨X, Y, Or.inr ?_⟩
        have hslash' : (C ⧸ B).subcategoryAt? (false :: p) = some (X ⧹ Y) := by
          simpa [horiginCat, horiginPos] using hslash
        simpa [Category.subcategoryAt?_rdiv_false] using hslash'
  }
  have horiginEq : R.origin = ctx.liftOccurrence oLeftLocal := by
    apply DerivationContext.occurrence_eq_lift ctx
    · simpa [oLeftLocal] using horiginNode
    · simpa [oLeftLocal] using horiginCat
    · simpa [oLeftLocal] using horiginPos
  have hlocal : LocalTraceEdge oLeftLocal oOutLocal :=
    LocalTraceEdge.appRight_C rfl rfl rfl rfl
  have hedgeLocal : TraceEdge oLeftLocal oOutLocal := Or.inl (Or.inl hlocal)
  have hedgeCtx := ctx.liftTraceEdge hedgeLocal
  have hedge : TraceEdge R.origin (ctx.liftOccurrence oOutLocal) := by
    simpa [horiginEq] using hedgeCtx
  have houtTarget := F.mem_dedupCategoryTargetsAt_of_traceEdge hR hedge
  have houtNode : (ctx.liftOccurrence oOutLocal).nodePath = ctx.nodePrefix := by
    simpa [oOutLocal] using ctx.liftOccurrence_nodePath oOutLocal
  have houtPos : (ctx.liftOccurrence oOutLocal).categoryPath = p := by
    simpa [oOutLocal] using ctx.liftOccurrence_categoryPath oOutLocal
  simpa [houtNode, houtPos] using houtTarget

/-- In a contextual forward application, replacing the output copy forces the
matching left-premise result copy to be replaced. -/
theorem appRight_output_copy_target_to_left_result_at
    {Γ Δ Ω : List Category} {C B A : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ B}
    (ctx : DerivationContext (Γ ++ Δ) C Ω A)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.appRight))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget : (p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix) :
    (false :: p, #F.atomName) ∈
      F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left]) := by
  let localTree := DerivationTree.binary t₁ t₂ Rule.appRight
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff ctx.nodePrefix (p, #F.atomName)).mp hprojected
  have hRpos : R.pos = p :=
    (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? ctx.nodePrefix = some C :=
    by simpa using ctx.categoryAt?_local (DerivationTree.categoryAt?_root localTree)
  have hRcat : R.nodeCategory = C := by
    have hnodeAtR : (ctx.plug localTree).categoryAt? R.nodePath = some C := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = C := by
    rw [← R.cat_eq]
    exact hRcat
  let oOutLocal : Occurrence localTree := {
    nodePath := []
    nodeCategory := C
    nodeAt := DerivationTree.categoryAt?_root localTree
    categoryPath := p
    isConstructor := by
      simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oLeftLocal : Occurrence localTree := {
    nodePath := [.left]
    nodeCategory := C ⧸ B
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := false :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by simpa [Category.subcategoryAt?_rdiv_false, horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by simpa [Category.subcategoryAt?_rdiv_false, horiginCat, horiginPos] using hslash)⟩
  }
  have horiginEq : R.origin = ctx.liftOccurrence oOutLocal := by
    apply DerivationContext.occurrence_eq_lift ctx
    · simpa [oOutLocal] using horiginNode
    · simpa [oOutLocal] using horiginCat
    · simpa [oOutLocal] using horiginPos
  have hlocal : LocalTraceEdge oLeftLocal oOutLocal :=
    LocalTraceEdge.appRight_C rfl rfl rfl rfl
  have hedgeLocal : TraceEdge oOutLocal oLeftLocal := Or.inr (Or.inl hlocal)
  have hedgeCtx := ctx.liftTraceEdge hedgeLocal
  have hedge : TraceEdge R.origin (ctx.liftOccurrence oLeftLocal) := by
    simpa [horiginEq] using hedgeCtx
  have hleftTarget := F.mem_dedupCategoryTargetsAt_of_traceEdge hR hedge
  have hleftNode :
      (ctx.liftOccurrence oLeftLocal).nodePath = ctx.nodePrefix ++ [.left] := by
    simpa [oLeftLocal] using ctx.liftOccurrence_nodePath oLeftLocal
  have hleftPos : (ctx.liftOccurrence oLeftLocal).categoryPath = false :: p := by
    simpa [oLeftLocal] using ctx.liftOccurrence_categoryPath oLeftLocal
  simpa [hleftNode, hleftPos] using hleftTarget

/-- In a contextual forward application, replacing the left-premise argument
copy forces the matching right-premise copy to be replaced. -/
theorem appRight_left_arg_copy_target_to_right_at
    {Γ Δ Ω : List Category} {C B A : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ B}
    (ctx : DerivationContext (Γ ++ Δ) C Ω A)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.appRight))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget :
      (true :: p, #F.atomName) ∈
        F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left])) :
    (p, #F.atomName) ∈ F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right]) := by
  let localTree := DerivationTree.binary t₁ t₂ Rule.appRight
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
      (true :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = true :: p :=
    (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? (ctx.nodePrefix ++ [.left]) = some (C ⧸ B) :=
    ctx.categoryAt?_local (by simp [localTree, DerivationTree.categoryAt?])
  have hRcat : R.nodeCategory = C ⧸ B := by
    have hnodeAtR : (ctx.plug localTree).categoryAt? R.nodePath = some (C ⧸ B) := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix ++ [.left] := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = true :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = C ⧸ B := by
    rw [← R.cat_eq]
    exact hRcat
  let oLeftLocal : Occurrence localTree := {
    nodePath := [.left]
    nodeCategory := C ⧸ B
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := true :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by simpa [Category.subcategoryAt?_rdiv_true, horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by simpa [Category.subcategoryAt?_rdiv_true, horiginCat, horiginPos] using hslash)⟩
  }
  let oRightLocal : Occurrence localTree := {
    nodePath := [.right]
    nodeCategory := B
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by simpa [Category.subcategoryAt?_rdiv_true, horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by simpa [Category.subcategoryAt?_rdiv_true, horiginCat, horiginPos] using hslash)⟩
  }
  have horiginEq : R.origin = ctx.liftOccurrence oLeftLocal := by
    apply DerivationContext.occurrence_eq_lift ctx
    · simpa [oLeftLocal] using horiginNode
    · simpa [oLeftLocal] using horiginCat
    · simpa [oLeftLocal] using horiginPos
  have hlocal : LocalTraceEdge oLeftLocal oRightLocal :=
    LocalTraceEdge.appRight_B rfl rfl rfl rfl
  have hedgeLocal : TraceEdge oLeftLocal oRightLocal := Or.inl (Or.inl hlocal)
  have hedgeCtx := ctx.liftTraceEdge hedgeLocal
  have hedge : TraceEdge R.origin (ctx.liftOccurrence oRightLocal) := by
    simpa [horiginEq] using hedgeCtx
  have hrightTarget := F.mem_dedupCategoryTargetsAt_of_traceEdge hR hedge
  have hrightNode :
      (ctx.liftOccurrence oRightLocal).nodePath = ctx.nodePrefix ++ [.right] := by
    simpa [oRightLocal] using ctx.liftOccurrence_nodePath oRightLocal
  have hrightPos : (ctx.liftOccurrence oRightLocal).categoryPath = p := by
    simpa [oRightLocal] using ctx.liftOccurrence_categoryPath oRightLocal
  simpa [hrightNode, hrightPos] using hrightTarget

/-- In a contextual forward application, replacing the right-premise copy
forces the matching left-premise argument copy to be replaced. -/
theorem appRight_right_arg_copy_target_to_left_at
    {Γ Δ Ω : List Category} {C B A : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ B}
    (ctx : DerivationContext (Γ ++ Δ) C Ω A)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.appRight))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget :
      (p, #F.atomName) ∈
        F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right])) :
    (true :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left]) := by
  let localTree := DerivationTree.binary t₁ t₂ Rule.appRight
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
      (p, #F.atomName)).mp hprojected
  have hRpos : R.pos = p :=
    (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? (ctx.nodePrefix ++ [.right]) = some B :=
    ctx.categoryAt?_local (by simp [localTree, DerivationTree.categoryAt?])
  have hRcat : R.nodeCategory = B := by
    have hnodeAtR : (ctx.plug localTree).categoryAt? R.nodePath = some B := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix ++ [.right] := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = B := by
    rw [← R.cat_eq]
    exact hRcat
  let oRightLocal : Occurrence localTree := {
    nodePath := [.right]
    nodeCategory := B
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := p
    isConstructor := by
      simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oLeftLocal : Occurrence localTree := {
    nodePath := [.left]
    nodeCategory := C ⧸ B
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := true :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by simpa [Category.subcategoryAt?_rdiv_true, horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by simpa [Category.subcategoryAt?_rdiv_true, horiginCat, horiginPos] using hslash)⟩
  }
  have horiginEq : R.origin = ctx.liftOccurrence oRightLocal := by
    apply DerivationContext.occurrence_eq_lift ctx
    · simpa [oRightLocal] using horiginNode
    · simpa [oRightLocal] using horiginCat
    · simpa [oRightLocal] using horiginPos
  have hlocal : LocalTraceEdge oLeftLocal oRightLocal :=
    LocalTraceEdge.appRight_B rfl rfl rfl rfl
  have hedgeLocal : TraceEdge oRightLocal oLeftLocal := Or.inr (Or.inl hlocal)
  have hedgeCtx := ctx.liftTraceEdge hedgeLocal
  have hedge : TraceEdge R.origin (ctx.liftOccurrence oLeftLocal) := by
    simpa [horiginEq] using hedgeCtx
  have hleftTarget := F.mem_dedupCategoryTargetsAt_of_traceEdge hR hedge
  have hleftNode :
      (ctx.liftOccurrence oLeftLocal).nodePath = ctx.nodePrefix ++ [.left] := by
    simpa [oLeftLocal] using ctx.liftOccurrence_nodePath oLeftLocal
  have hleftPos : (ctx.liftOccurrence oLeftLocal).categoryPath = true :: p := by
    simpa [oLeftLocal] using ctx.liftOccurrence_categoryPath oLeftLocal
  simpa [hleftNode, hleftPos] using hleftTarget

/-- Path-only form of contextual appRight principal-freeness. -/
theorem appRight_left_root_path_not_target_at
    {Γ Δ Ω : List Category} {C B A : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ B}
    (ctx : DerivationContext (Γ ++ Δ) C Ω A)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.appRight))}
    (F : PieceReplacementFamilyCore P) :
    [] ∉ F.categoryTargetPathsAt (ctx.nodePrefix ++ [.left]) := by
  intro hp
  have htarget :
      ([], #F.atomName) ∈ F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left]) := by
    exact (F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
      ([], #F.atomName)).mpr ⟨hp, rfl⟩
  exact F.appRight_left_root_not_target_at ctx htarget

/-- Path-only synchronization between the left-premise result copy and the
contextual output copy of appRight. -/
theorem appRight_left_false_path_iff_output_path_at
    {Γ Δ Ω : List Category} {C B A : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ B}
    (ctx : DerivationContext (Γ ++ Δ) C Ω A)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.appRight))}
    (F : PieceReplacementFamilyCore P) (p : CategoryPath) :
    false :: p ∈ F.categoryTargetPathsAt (ctx.nodePrefix ++ [.left]) ↔
      p ∈ F.categoryTargetPathsAt ctx.nodePrefix := by
  constructor
  · intro hp
    have htarget :
        (false :: p, #F.atomName) ∈
          F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left]) := by
      exact (F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
        (false :: p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hout := F.appRight_left_result_copy_target_to_output_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
      (p, #F.atomName)).mp hout).1
  · intro hp
    have htarget :
        (p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix := by
      rw [F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix (p, #F.atomName)]
      exact ⟨hp, rfl⟩
    have hleft := F.appRight_output_copy_target_to_left_result_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
      (false :: p, #F.atomName)).mp hleft).1

/-- Path-only synchronization between the left-premise argument copy and the
right-premise copy of appRight. -/
theorem appRight_left_true_path_iff_right_path_at
    {Γ Δ Ω : List Category} {C B A : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ B}
    (ctx : DerivationContext (Γ ++ Δ) C Ω A)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.appRight))}
    (F : PieceReplacementFamilyCore P) (p : CategoryPath) :
    true :: p ∈ F.categoryTargetPathsAt (ctx.nodePrefix ++ [.left]) ↔
      p ∈ F.categoryTargetPathsAt (ctx.nodePrefix ++ [.right]) := by
  constructor
  · intro hp
    have htarget :
        (true :: p, #F.atomName) ∈
          F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left]) := by
      exact (F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
        (true :: p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hright := F.appRight_left_arg_copy_target_to_right_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
      (p, #F.atomName)).mp hright).1
  · intro hp
    have htarget :
        (p, #F.atomName) ∈ F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right]) := by
      exact (F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
        (p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hleft := F.appRight_right_arg_copy_target_to_left_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
      (true :: p, #F.atomName)).mp hleft).1

/-- Context-parametric forward-application preservation for canonical
node-local rewriting.  Unlike the root-only theorem, the `C` copy may be
rewritten at the contextual output node; trace closure ensures the left result
copy is rewritten by the same path set. -/
theorem rewrite_preserves_appRight_at
    {Γ Δ Ω : List Category} {C B A : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)}
    {t₂ : DerivationTree Δ B}
    (ctx : DerivationContext (Γ ++ Δ) C Ω A)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.appRight))}
    (F : PieceReplacementFamilyCore P)
    {L' R' O' : Category}
    (hL :
      F.rewriteNodeCategorySimul? (ctx.nodePrefix ++ [.left]) (C ⧸ B) = some L')
    (hR :
      F.rewriteNodeCategorySimul? (ctx.nodePrefix ++ [.right]) B = some R')
    (hO :
      F.rewriteNodeCategorySimul? ctx.nodePrefix C = some O') :
    Rule L' R' O' := by
  have hLeq : L' = O' ⧸ R' := by
    unfold rewriteNodeCategorySimul? at hL hR hO
    exact Category.replaceSimulAtPaths?_rdiv_components
      (F.appRight_left_root_path_not_target_at ctx)
      (F.appRight_left_false_path_iff_output_path_at ctx)
      (F.appRight_left_true_path_iff_right_path_at ctx)
      hO
      hR
      hL
  subst L'
  exact Rule.appRight

/-- In a contextual backward application, the principal slash at the right
child is still target-free. -/
theorem appLeft_right_root_not_target_at
    {Γ Δ Ω : List Category} {A C Z : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ (A ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) C Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.appLeft))}
    (F : PieceReplacementFamilyCore P) :
    ([], #F.atomName) ∉ F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right]) := by
  intro htarget
  have hprincipalLocal :
      DerivationTree.PrincipalConstructor
        (DerivationTree.binary t₁ t₂ Rule.appLeft) [.right] [] :=
    DerivationTree.PrincipalConstructor.appLeft_right t₁ t₂
  have hprincipal :
      DerivationTree.PrincipalConstructor
        (ctx.plug (DerivationTree.binary t₁ t₂ Rule.appLeft))
        (ctx.nodePrefix ++ [.right]) [] :=
    ctx.liftPrincipalConstructor hprincipalLocal
  have hne := F.target_path_ne_of_principal hprincipal htarget
  exact hne rfl

/-- In a contextual backward application, replacing the right-premise `A` copy
forces the matching left-premise copy to be replaced. -/
theorem appLeft_right_arg_copy_target_to_left_at
    {Γ Δ Ω : List Category} {A C Z : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ (A ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) C Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.appLeft))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget :
      (false :: p, #F.atomName) ∈
        F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right])) :
    (p, #F.atomName) ∈ F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left]) := by
  let localTree := DerivationTree.binary t₁ t₂ Rule.appLeft
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
      (false :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = false :: p :=
    (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? (ctx.nodePrefix ++ [.right]) =
        some (A ⧹ C) :=
    ctx.categoryAt?_local (by simp [localTree, DerivationTree.categoryAt?])
  have hRcat : R.nodeCategory = A ⧹ C := by
    have hnodeAtR :
        (ctx.plug localTree).categoryAt? R.nodePath = some (A ⧹ C) := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix ++ [.right] := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = false :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = A ⧹ C := by
    rw [← R.cat_eq]
    exact hRcat
  let oRightLocal : Occurrence localTree := {
    nodePath := [.right]
    nodeCategory := A ⧹ C
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := false :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_ldiv_false, horiginCat, horiginPos]
            using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_ldiv_false, horiginCat, horiginPos]
            using hslash)⟩
  }
  let oLeftLocal : Occurrence localTree := {
    nodePath := [.left]
    nodeCategory := A
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_ldiv_false, horiginCat, horiginPos]
            using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_ldiv_false, horiginCat, horiginPos]
            using hslash)⟩
  }
  have horiginEq : R.origin = ctx.liftOccurrence oRightLocal := by
    apply DerivationContext.occurrence_eq_lift ctx
    · simpa [oRightLocal] using horiginNode
    · simpa [oRightLocal] using horiginCat
    · simpa [oRightLocal] using horiginPos
  have hlocal : LocalTraceEdge oLeftLocal oRightLocal :=
    LocalTraceEdge.appLeft_A rfl rfl rfl rfl
  have hedgeLocal : TraceEdge oRightLocal oLeftLocal := Or.inr (Or.inl hlocal)
  have hedgeCtx := ctx.liftTraceEdge hedgeLocal
  have hedge : TraceEdge R.origin (ctx.liftOccurrence oLeftLocal) := by
    simpa [horiginEq] using hedgeCtx
  have hleftTarget := F.mem_dedupCategoryTargetsAt_of_traceEdge hR hedge
  have hleftNode :
      (ctx.liftOccurrence oLeftLocal).nodePath = ctx.nodePrefix ++ [.left] := by
    simpa [oLeftLocal] using ctx.liftOccurrence_nodePath oLeftLocal
  have hleftPos : (ctx.liftOccurrence oLeftLocal).categoryPath = p := by
    simpa [oLeftLocal] using ctx.liftOccurrence_categoryPath oLeftLocal
  simpa [hleftNode, hleftPos] using hleftTarget

/-- In a contextual backward application, replacing the left-premise `A` copy
forces the matching right-premise `A` copy to be replaced. -/
theorem appLeft_left_arg_copy_target_to_right_at
    {Γ Δ Ω : List Category} {A C Z : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ (A ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) C Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.appLeft))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget :
      (p, #F.atomName) ∈ F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left])) :
    (false :: p, #F.atomName) ∈
      F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right]) := by
  let localTree := DerivationTree.binary t₁ t₂ Rule.appLeft
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
      (p, #F.atomName)).mp hprojected
  have hRpos : R.pos = p :=
    (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? (ctx.nodePrefix ++ [.left]) = some A :=
    ctx.categoryAt?_local (by simp [localTree, DerivationTree.categoryAt?])
  have hRcat : R.nodeCategory = A := by
    have hnodeAtR : (ctx.plug localTree).categoryAt? R.nodePath = some A := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix ++ [.left] := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = A := by
    rw [← R.cat_eq]
    exact hRcat
  let oLeftLocal : Occurrence localTree := {
    nodePath := [.left]
    nodeCategory := A
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := p
    isConstructor := by
      simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oRightLocal : Occurrence localTree := {
    nodePath := [.right]
    nodeCategory := A ⧹ C
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := false :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_ldiv_false, horiginCat, horiginPos]
            using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_ldiv_false, horiginCat, horiginPos]
            using hslash)⟩
  }
  have horiginEq : R.origin = ctx.liftOccurrence oLeftLocal := by
    apply DerivationContext.occurrence_eq_lift ctx
    · simpa [oLeftLocal] using horiginNode
    · simpa [oLeftLocal] using horiginCat
    · simpa [oLeftLocal] using horiginPos
  have hlocal : LocalTraceEdge oLeftLocal oRightLocal :=
    LocalTraceEdge.appLeft_A rfl rfl rfl rfl
  have hedgeLocal : TraceEdge oLeftLocal oRightLocal := Or.inl (Or.inl hlocal)
  have hedgeCtx := ctx.liftTraceEdge hedgeLocal
  have hedge : TraceEdge R.origin (ctx.liftOccurrence oRightLocal) := by
    simpa [horiginEq] using hedgeCtx
  have hrightTarget := F.mem_dedupCategoryTargetsAt_of_traceEdge hR hedge
  have hrightNode :
      (ctx.liftOccurrence oRightLocal).nodePath = ctx.nodePrefix ++ [.right] := by
    simpa [oRightLocal] using ctx.liftOccurrence_nodePath oRightLocal
  have hrightPos : (ctx.liftOccurrence oRightLocal).categoryPath = false :: p := by
    simpa [oRightLocal] using ctx.liftOccurrence_categoryPath oRightLocal
  simpa [hrightNode, hrightPos] using hrightTarget

/-- In a contextual backward application, replacing the right-premise `C` copy
forces the matching output copy to be replaced. -/
theorem appLeft_right_result_copy_target_to_output_at
    {Γ Δ Ω : List Category} {A C Z : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ (A ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) C Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.appLeft))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget :
      (true :: p, #F.atomName) ∈
        F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right])) :
    (p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix := by
  let localTree := DerivationTree.binary t₁ t₂ Rule.appLeft
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
      (true :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = true :: p :=
    (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? (ctx.nodePrefix ++ [.right]) =
        some (A ⧹ C) :=
    ctx.categoryAt?_local (by simp [localTree, DerivationTree.categoryAt?])
  have hRcat : R.nodeCategory = A ⧹ C := by
    have hnodeAtR :
        (ctx.plug localTree).categoryAt? R.nodePath = some (A ⧹ C) := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix ++ [.right] := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = true :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = A ⧹ C := by
    rw [← R.cat_eq]
    exact hRcat
  let oRightLocal : Occurrence localTree := {
    nodePath := [.right]
    nodeCategory := A ⧹ C
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := true :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_ldiv_true, horiginCat, horiginPos]
            using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_ldiv_true, horiginCat, horiginPos]
            using hslash)⟩
  }
  let oOutLocal : Occurrence localTree := {
    nodePath := []
    nodeCategory := C
    nodeAt := DerivationTree.categoryAt?_root localTree
    categoryPath := p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_ldiv_true, horiginCat, horiginPos]
            using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_ldiv_true, horiginCat, horiginPos]
            using hslash)⟩
  }
  have horiginEq : R.origin = ctx.liftOccurrence oRightLocal := by
    apply DerivationContext.occurrence_eq_lift ctx
    · simpa [oRightLocal] using horiginNode
    · simpa [oRightLocal] using horiginCat
    · simpa [oRightLocal] using horiginPos
  have hlocal : LocalTraceEdge oRightLocal oOutLocal :=
    LocalTraceEdge.appLeft_C rfl rfl rfl rfl
  have hedgeLocal : TraceEdge oRightLocal oOutLocal := Or.inl (Or.inl hlocal)
  have hedgeCtx := ctx.liftTraceEdge hedgeLocal
  have hedge : TraceEdge R.origin (ctx.liftOccurrence oOutLocal) := by
    simpa [horiginEq] using hedgeCtx
  have houtTarget := F.mem_dedupCategoryTargetsAt_of_traceEdge hR hedge
  have houtNode : (ctx.liftOccurrence oOutLocal).nodePath = ctx.nodePrefix := by
    simpa [oOutLocal] using ctx.liftOccurrence_nodePath oOutLocal
  have houtPos : (ctx.liftOccurrence oOutLocal).categoryPath = p := by
    simpa [oOutLocal] using ctx.liftOccurrence_categoryPath oOutLocal
  simpa [houtNode, houtPos] using houtTarget

/-- In a contextual backward application, replacing the output copy forces the
matching right-premise `C` copy to be replaced. -/
theorem appLeft_output_copy_target_to_right_result_at
    {Γ Δ Ω : List Category} {A C Z : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ (A ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) C Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.appLeft))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget : (p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix) :
    (true :: p, #F.atomName) ∈
      F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right]) := by
  let localTree := DerivationTree.binary t₁ t₂ Rule.appLeft
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff ctx.nodePrefix (p, #F.atomName)).mp hprojected
  have hRpos : R.pos = p :=
    (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? ctx.nodePrefix = some C :=
    by simpa using ctx.categoryAt?_local (DerivationTree.categoryAt?_root localTree)
  have hRcat : R.nodeCategory = C := by
    have hnodeAtR : (ctx.plug localTree).categoryAt? R.nodePath = some C := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = C := by
    rw [← R.cat_eq]
    exact hRcat
  let oOutLocal : Occurrence localTree := {
    nodePath := []
    nodeCategory := C
    nodeAt := DerivationTree.categoryAt?_root localTree
    categoryPath := p
    isConstructor := by
      simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oRightLocal : Occurrence localTree := {
    nodePath := [.right]
    nodeCategory := A ⧹ C
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := true :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_ldiv_true, horiginCat, horiginPos]
            using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_ldiv_true, horiginCat, horiginPos]
            using hslash)⟩
  }
  have horiginEq : R.origin = ctx.liftOccurrence oOutLocal := by
    apply DerivationContext.occurrence_eq_lift ctx
    · simpa [oOutLocal] using horiginNode
    · simpa [oOutLocal] using horiginCat
    · simpa [oOutLocal] using horiginPos
  have hlocal : LocalTraceEdge oRightLocal oOutLocal :=
    LocalTraceEdge.appLeft_C rfl rfl rfl rfl
  have hedgeLocal : TraceEdge oOutLocal oRightLocal := Or.inr (Or.inl hlocal)
  have hedgeCtx := ctx.liftTraceEdge hedgeLocal
  have hedge : TraceEdge R.origin (ctx.liftOccurrence oRightLocal) := by
    simpa [horiginEq] using hedgeCtx
  have hrightTarget := F.mem_dedupCategoryTargetsAt_of_traceEdge hR hedge
  have hrightNode :
      (ctx.liftOccurrence oRightLocal).nodePath = ctx.nodePrefix ++ [.right] := by
    simpa [oRightLocal] using ctx.liftOccurrence_nodePath oRightLocal
  have hrightPos : (ctx.liftOccurrence oRightLocal).categoryPath = true :: p := by
    simpa [oRightLocal] using ctx.liftOccurrence_categoryPath oRightLocal
  simpa [hrightNode, hrightPos] using hrightTarget

/-- Path-only form of contextual appLeft principal-freeness. -/
theorem appLeft_right_root_path_not_target_at
    {Γ Δ Ω : List Category} {A C Z : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ (A ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) C Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.appLeft))}
    (F : PieceReplacementFamilyCore P) :
    [] ∉ F.categoryTargetPathsAt (ctx.nodePrefix ++ [.right]) := by
  intro hp
  have htarget :
      ([], #F.atomName) ∈ F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right]) := by
    exact (F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
      ([], #F.atomName)).mpr ⟨hp, rfl⟩
  exact F.appLeft_right_root_not_target_at ctx htarget

/-- Path-only synchronization between the right-premise `A` copy and the
left-premise copy of appLeft. -/
theorem appLeft_right_false_path_iff_left_path_at
    {Γ Δ Ω : List Category} {A C Z : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ (A ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) C Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.appLeft))}
    (F : PieceReplacementFamilyCore P) (p : CategoryPath) :
    false :: p ∈ F.categoryTargetPathsAt (ctx.nodePrefix ++ [.right]) ↔
      p ∈ F.categoryTargetPathsAt (ctx.nodePrefix ++ [.left]) := by
  constructor
  · intro hp
    have htarget :
        (false :: p, #F.atomName) ∈
          F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right]) := by
      exact (F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
        (false :: p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hleft := F.appLeft_right_arg_copy_target_to_left_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
      (p, #F.atomName)).mp hleft).1
  · intro hp
    have htarget :
        (p, #F.atomName) ∈ F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left]) := by
      exact (F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
        (p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hright := F.appLeft_left_arg_copy_target_to_right_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
      (false :: p, #F.atomName)).mp hright).1

/-- Path-only synchronization between the right-premise `C` copy and the
contextual output copy of appLeft. -/
theorem appLeft_right_true_path_iff_output_path_at
    {Γ Δ Ω : List Category} {A C Z : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ (A ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) C Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.appLeft))}
    (F : PieceReplacementFamilyCore P) (p : CategoryPath) :
    true :: p ∈ F.categoryTargetPathsAt (ctx.nodePrefix ++ [.right]) ↔
      p ∈ F.categoryTargetPathsAt ctx.nodePrefix := by
  constructor
  · intro hp
    have htarget :
        (true :: p, #F.atomName) ∈
          F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right]) := by
      exact (F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
        (true :: p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hout := F.appLeft_right_result_copy_target_to_output_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
      (p, #F.atomName)).mp hout).1
  · intro hp
    have htarget :
        (p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix := by
      exact (F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
        (p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hright := F.appLeft_output_copy_target_to_right_result_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
      (true :: p, #F.atomName)).mp hright).1

/-- Context-parametric backward-application preservation for canonical
node-local rewriting. -/
theorem rewrite_preserves_appLeft_at
    {Γ Δ Ω : List Category} {A C Z : Category}
    {t₁ : DerivationTree Γ A}
    {t₂ : DerivationTree Δ (A ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) C Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.appLeft))}
    (F : PieceReplacementFamilyCore P)
    {L' R' O' : Category}
    (hL :
      F.rewriteNodeCategorySimul? (ctx.nodePrefix ++ [.left]) A = some L')
    (hR :
      F.rewriteNodeCategorySimul? (ctx.nodePrefix ++ [.right]) (A ⧹ C) = some R')
    (hO :
      F.rewriteNodeCategorySimul? ctx.nodePrefix C = some O') :
    Rule L' R' O' := by
  have hReq : R' = L' ⧹ O' := by
    unfold rewriteNodeCategorySimul? at hL hR hO
    exact Category.replaceSimulAtPaths?_ldiv_components
      (F.appLeft_right_root_path_not_target_at ctx)
      (F.appLeft_right_false_path_iff_left_path_at ctx)
      (F.appLeft_right_true_path_iff_output_path_at ctx)
      hL
      hO
      hR
  subst R'
  exact Rule.appLeft

/-- In contextual forward composition, the principal slash at the left child is
target-free. -/
theorem compRight_left_root_path_not_target_at
    {Γ Δ Ω : List Category} {C B A Z : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (B ⧸ A)}
    (ctx : DerivationContext (Γ ++ Δ) (C ⧸ A) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compRight))}
    (F : PieceReplacementFamilyCore P) :
    [] ∉ F.categoryTargetPathsAt (ctx.nodePrefix ++ [.left]) := by
  intro hp
  have htarget :
      ([], #F.atomName) ∈ F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left]) := by
    exact (F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
      ([], #F.atomName)).mpr ⟨hp, rfl⟩
  have hprincipalLocal :
      DerivationTree.PrincipalConstructor
        (DerivationTree.binary t₁ t₂ Rule.compRight) [.left] [] :=
    DerivationTree.PrincipalConstructor.compRight_left t₁ t₂
  have hprincipal :
      DerivationTree.PrincipalConstructor
        (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compRight))
        (ctx.nodePrefix ++ [.left]) [] :=
    ctx.liftPrincipalConstructor hprincipalLocal
  have hne := F.target_path_ne_of_principal hprincipal htarget
  exact hne rfl

/-- In contextual forward composition, the principal slash at the right child is
target-free. -/
theorem compRight_right_root_path_not_target_at
    {Γ Δ Ω : List Category} {C B A Z : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (B ⧸ A)}
    (ctx : DerivationContext (Γ ++ Δ) (C ⧸ A) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compRight))}
    (F : PieceReplacementFamilyCore P) :
    [] ∉ F.categoryTargetPathsAt (ctx.nodePrefix ++ [.right]) := by
  intro hp
  have htarget :
      ([], #F.atomName) ∈ F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right]) := by
    exact (F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
      ([], #F.atomName)).mpr ⟨hp, rfl⟩
  have hprincipalLocal :
      DerivationTree.PrincipalConstructor
        (DerivationTree.binary t₁ t₂ Rule.compRight) [.right] [] :=
    DerivationTree.PrincipalConstructor.compRight_right t₁ t₂
  have hprincipal :
      DerivationTree.PrincipalConstructor
        (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compRight))
        (ctx.nodePrefix ++ [.right]) [] :=
    ctx.liftPrincipalConstructor hprincipalLocal
  have hne := F.target_path_ne_of_principal hprincipal htarget
  exact hne rfl

/-- In contextual forward composition, the principal slash at the output node is
target-free. -/
theorem compRight_output_root_path_not_target_at
    {Γ Δ Ω : List Category} {C B A Z : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (B ⧸ A)}
    (ctx : DerivationContext (Γ ++ Δ) (C ⧸ A) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compRight))}
    (F : PieceReplacementFamilyCore P) :
    [] ∉ F.categoryTargetPathsAt ctx.nodePrefix := by
  intro hp
  have htarget :
      ([], #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix := by
    exact (F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
      ([], #F.atomName)).mpr ⟨hp, rfl⟩
  have hprincipalLocal :
      DerivationTree.PrincipalConstructor
        (DerivationTree.binary t₁ t₂ Rule.compRight) [] [] :=
    DerivationTree.PrincipalConstructor.compRight_out t₁ t₂
  have hprincipal :
      DerivationTree.PrincipalConstructor
        (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compRight))
        ctx.nodePrefix [] :=
    by simpa using ctx.liftPrincipalConstructor hprincipalLocal
  have hne := F.target_path_ne_of_principal hprincipal htarget
  exact hne rfl

/-- In contextual forward composition, replacing the left-premise `C` copy
forces the matching output `C` copy to be replaced. -/
theorem compRight_left_C_copy_target_to_output_at
    {Γ Δ Ω : List Category} {C B A Z : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (B ⧸ A)}
    (ctx : DerivationContext (Γ ++ Δ) (C ⧸ A) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compRight))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget :
      (false :: p, #F.atomName) ∈
        F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left])) :
    (false :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix := by
  let localTree := DerivationTree.binary t₁ t₂ Rule.compRight
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
      (false :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = false :: p := (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? (ctx.nodePrefix ++ [.left]) = some (C ⧸ B) :=
    ctx.categoryAt?_local (by simp [localTree, DerivationTree.categoryAt?])
  have hRcat : R.nodeCategory = C ⧸ B := by
    have hnodeAtR : (ctx.plug localTree).categoryAt? R.nodePath = some (C ⧸ B) := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix ++ [.left] := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = false :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = C ⧸ B := by
    rw [← R.cat_eq]
    exact hRcat
  let oLeft : Occurrence localTree := {
    nodePath := [.left]
    nodeCategory := C ⧸ B
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := false :: p
    isConstructor := by simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oOut : Occurrence localTree := {
    nodePath := []
    nodeCategory := C ⧸ A
    nodeAt := DerivationTree.categoryAt?_root localTree
    categoryPath := false :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_rdiv_false, horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_rdiv_false, horiginCat, horiginPos] using hslash)⟩
  }
  have hedge : TraceEdge oLeft oOut :=
    Or.inl (Or.inl (LocalTraceEdge.compRight_C rfl rfl rfl rfl))
  simpa [oLeft, oOut] using
    F.mem_dedupCategoryTargetsAt_of_lifted_traceEdge ctx hR
      (by simpa [oLeft] using horiginNode)
      (by simpa [oLeft] using horiginCat)
      (by simpa [oLeft] using horiginPos)
      hedge

/-- In contextual forward composition, replacing the output `C` copy forces the
matching left-premise `C` copy to be replaced. -/
theorem compRight_output_C_copy_target_to_left_at
    {Γ Δ Ω : List Category} {C B A Z : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (B ⧸ A)}
    (ctx : DerivationContext (Γ ++ Δ) (C ⧸ A) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compRight))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget : (false :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix) :
    (false :: p, #F.atomName) ∈
      F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left]) := by
  let localTree := DerivationTree.binary t₁ t₂ Rule.compRight
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff ctx.nodePrefix
      (false :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = false :: p := (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? ctx.nodePrefix = some (C ⧸ A) :=
    by simpa using ctx.categoryAt?_local (DerivationTree.categoryAt?_root localTree)
  have hRcat : R.nodeCategory = C ⧸ A := by
    have hnodeAtR : (ctx.plug localTree).categoryAt? R.nodePath = some (C ⧸ A) := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = false :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = C ⧸ A := by
    rw [← R.cat_eq]
    exact hRcat
  let oOut : Occurrence localTree := {
    nodePath := []
    nodeCategory := C ⧸ A
    nodeAt := DerivationTree.categoryAt?_root localTree
    categoryPath := false :: p
    isConstructor := by simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oLeft : Occurrence localTree := {
    nodePath := [.left]
    nodeCategory := C ⧸ B
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := false :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_rdiv_false, horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_rdiv_false, horiginCat, horiginPos] using hslash)⟩
  }
  have hedge : TraceEdge oOut oLeft :=
    Or.inr (Or.inl (LocalTraceEdge.compRight_C rfl rfl rfl rfl))
  simpa [oOut, oLeft] using
    F.mem_dedupCategoryTargetsAt_of_lifted_traceEdge ctx hR
      (by simpa [oOut] using horiginNode)
      (by simpa [oOut] using horiginCat)
      (by simpa [oOut] using horiginPos)
      hedge

/-- In contextual forward composition, replacing the left-premise `B` copy
forces the matching right-premise `B` copy to be replaced. -/
theorem compRight_left_B_copy_target_to_right_at
    {Γ Δ Ω : List Category} {C B A Z : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (B ⧸ A)}
    (ctx : DerivationContext (Γ ++ Δ) (C ⧸ A) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compRight))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget :
      (true :: p, #F.atomName) ∈
        F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left])) :
    (false :: p, #F.atomName) ∈
      F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right]) := by
  let localTree := DerivationTree.binary t₁ t₂ Rule.compRight
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
      (true :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = true :: p := (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? (ctx.nodePrefix ++ [.left]) = some (C ⧸ B) :=
    ctx.categoryAt?_local (by simp [localTree, DerivationTree.categoryAt?])
  have hRcat : R.nodeCategory = C ⧸ B := by
    have hnodeAtR : (ctx.plug localTree).categoryAt? R.nodePath = some (C ⧸ B) := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix ++ [.left] := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = true :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = C ⧸ B := by
    rw [← R.cat_eq]
    exact hRcat
  let oLeft : Occurrence localTree := {
    nodePath := [.left]
    nodeCategory := C ⧸ B
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := true :: p
    isConstructor := by simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oRight : Occurrence localTree := {
    nodePath := [.right]
    nodeCategory := B ⧸ A
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := false :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_rdiv_true, Category.subcategoryAt?_rdiv_false,
            horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_rdiv_true, Category.subcategoryAt?_rdiv_false,
            horiginCat, horiginPos] using hslash)⟩
  }
  have hedge : TraceEdge oLeft oRight :=
    Or.inl (Or.inl (LocalTraceEdge.compRight_B rfl rfl rfl rfl))
  simpa [oLeft, oRight] using
    F.mem_dedupCategoryTargetsAt_of_lifted_traceEdge ctx hR
      (by simpa [oLeft] using horiginNode)
      (by simpa [oLeft] using horiginCat)
      (by simpa [oLeft] using horiginPos)
      hedge

/-- In contextual forward composition, replacing the right-premise `B` copy
forces the matching left-premise `B` copy to be replaced. -/
theorem compRight_right_B_copy_target_to_left_at
    {Γ Δ Ω : List Category} {C B A Z : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (B ⧸ A)}
    (ctx : DerivationContext (Γ ++ Δ) (C ⧸ A) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compRight))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget :
      (false :: p, #F.atomName) ∈
        F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right])) :
    (true :: p, #F.atomName) ∈
      F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left]) := by
  let localTree := DerivationTree.binary t₁ t₂ Rule.compRight
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
      (false :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = false :: p := (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? (ctx.nodePrefix ++ [.right]) = some (B ⧸ A) :=
    ctx.categoryAt?_local (by simp [localTree, DerivationTree.categoryAt?])
  have hRcat : R.nodeCategory = B ⧸ A := by
    have hnodeAtR : (ctx.plug localTree).categoryAt? R.nodePath = some (B ⧸ A) := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix ++ [.right] := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = false :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = B ⧸ A := by
    rw [← R.cat_eq]
    exact hRcat
  let oRight : Occurrence localTree := {
    nodePath := [.right]
    nodeCategory := B ⧸ A
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := false :: p
    isConstructor := by simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oLeft : Occurrence localTree := {
    nodePath := [.left]
    nodeCategory := C ⧸ B
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := true :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_rdiv_false, Category.subcategoryAt?_rdiv_true,
            horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_rdiv_false, Category.subcategoryAt?_rdiv_true,
            horiginCat, horiginPos] using hslash)⟩
  }
  have hedge : TraceEdge oRight oLeft :=
    Or.inr (Or.inl (LocalTraceEdge.compRight_B rfl rfl rfl rfl))
  simpa [oRight, oLeft] using
    F.mem_dedupCategoryTargetsAt_of_lifted_traceEdge ctx hR
      (by simpa [oRight] using horiginNode)
      (by simpa [oRight] using horiginCat)
      (by simpa [oRight] using horiginPos)
      hedge

/-- In contextual forward composition, replacing the right-premise `A` copy
forces the matching output `A` copy to be replaced. -/
theorem compRight_right_A_copy_target_to_output_at
    {Γ Δ Ω : List Category} {C B A Z : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (B ⧸ A)}
    (ctx : DerivationContext (Γ ++ Δ) (C ⧸ A) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compRight))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget :
      (true :: p, #F.atomName) ∈
        F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right])) :
    (true :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix := by
  let localTree := DerivationTree.binary t₁ t₂ Rule.compRight
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
      (true :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = true :: p := (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? (ctx.nodePrefix ++ [.right]) = some (B ⧸ A) :=
    ctx.categoryAt?_local (by simp [localTree, DerivationTree.categoryAt?])
  have hRcat : R.nodeCategory = B ⧸ A := by
    have hnodeAtR : (ctx.plug localTree).categoryAt? R.nodePath = some (B ⧸ A) := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix ++ [.right] := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = true :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = B ⧸ A := by
    rw [← R.cat_eq]
    exact hRcat
  let oRight : Occurrence localTree := {
    nodePath := [.right]
    nodeCategory := B ⧸ A
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := true :: p
    isConstructor := by simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oOut : Occurrence localTree := {
    nodePath := []
    nodeCategory := C ⧸ A
    nodeAt := DerivationTree.categoryAt?_root localTree
    categoryPath := true :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_rdiv_true, horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_rdiv_true, horiginCat, horiginPos] using hslash)⟩
  }
  have hedge : TraceEdge oRight oOut :=
    Or.inl (Or.inl (LocalTraceEdge.compRight_A rfl rfl rfl rfl))
  simpa [oRight, oOut] using
    F.mem_dedupCategoryTargetsAt_of_lifted_traceEdge ctx hR
      (by simpa [oRight] using horiginNode)
      (by simpa [oRight] using horiginCat)
      (by simpa [oRight] using horiginPos)
      hedge

/-- In contextual forward composition, replacing the output `A` copy forces the
matching right-premise `A` copy to be replaced. -/
theorem compRight_output_A_copy_target_to_right_at
    {Γ Δ Ω : List Category} {C B A Z : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (B ⧸ A)}
    (ctx : DerivationContext (Γ ++ Δ) (C ⧸ A) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compRight))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget : (true :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix) :
    (true :: p, #F.atomName) ∈
      F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right]) := by
  let localTree := DerivationTree.binary t₁ t₂ Rule.compRight
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff ctx.nodePrefix
      (true :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = true :: p := (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? ctx.nodePrefix = some (C ⧸ A) :=
    by simpa using ctx.categoryAt?_local (DerivationTree.categoryAt?_root localTree)
  have hRcat : R.nodeCategory = C ⧸ A := by
    have hnodeAtR : (ctx.plug localTree).categoryAt? R.nodePath = some (C ⧸ A) := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = true :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = C ⧸ A := by
    rw [← R.cat_eq]
    exact hRcat
  let oOut : Occurrence localTree := {
    nodePath := []
    nodeCategory := C ⧸ A
    nodeAt := DerivationTree.categoryAt?_root localTree
    categoryPath := true :: p
    isConstructor := by simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oRight : Occurrence localTree := {
    nodePath := [.right]
    nodeCategory := B ⧸ A
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := true :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_rdiv_true, horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_rdiv_true, horiginCat, horiginPos] using hslash)⟩
  }
  have hedge : TraceEdge oOut oRight :=
    Or.inr (Or.inl (LocalTraceEdge.compRight_A rfl rfl rfl rfl))
  simpa [oOut, oRight] using
    F.mem_dedupCategoryTargetsAt_of_lifted_traceEdge ctx hR
      (by simpa [oOut] using horiginNode)
      (by simpa [oOut] using horiginCat)
      (by simpa [oOut] using horiginPos)
      hedge

/-- Path-only synchronization between the left-premise and output `C` copies in
contextual forward composition. -/
theorem compRight_left_false_path_iff_output_false_path_at
    {Γ Δ Ω : List Category} {C B A Z : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (B ⧸ A)}
    (ctx : DerivationContext (Γ ++ Δ) (C ⧸ A) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compRight))}
    (F : PieceReplacementFamilyCore P) (p : CategoryPath) :
    false :: p ∈ F.categoryTargetPathsAt (ctx.nodePrefix ++ [.left]) ↔
      false :: p ∈ F.categoryTargetPathsAt ctx.nodePrefix := by
  constructor
  · intro hp
    have htarget :
        (false :: p, #F.atomName) ∈
          F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left]) :=
      (F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
        (false :: p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hout := F.compRight_left_C_copy_target_to_output_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
      (false :: p, #F.atomName)).mp hout).1
  · intro hp
    have htarget :
        (false :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix :=
      (F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
        (false :: p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hleft := F.compRight_output_C_copy_target_to_left_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
      (false :: p, #F.atomName)).mp hleft).1

/-- Path-only synchronization between the two `B` copies in contextual forward
composition. -/
theorem compRight_left_true_path_iff_right_false_path_at
    {Γ Δ Ω : List Category} {C B A Z : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (B ⧸ A)}
    (ctx : DerivationContext (Γ ++ Δ) (C ⧸ A) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compRight))}
    (F : PieceReplacementFamilyCore P) (p : CategoryPath) :
    true :: p ∈ F.categoryTargetPathsAt (ctx.nodePrefix ++ [.left]) ↔
      false :: p ∈ F.categoryTargetPathsAt (ctx.nodePrefix ++ [.right]) := by
  constructor
  · intro hp
    have htarget :
        (true :: p, #F.atomName) ∈
          F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left]) :=
      (F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
        (true :: p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hright := F.compRight_left_B_copy_target_to_right_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
      (false :: p, #F.atomName)).mp hright).1
  · intro hp
    have htarget :
        (false :: p, #F.atomName) ∈
          F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right]) :=
      (F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
        (false :: p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hleft := F.compRight_right_B_copy_target_to_left_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
      (true :: p, #F.atomName)).mp hleft).1

/-- Path-only synchronization between the right-premise and output `A` copies
in contextual forward composition. -/
theorem compRight_right_true_path_iff_output_true_path_at
    {Γ Δ Ω : List Category} {C B A Z : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (B ⧸ A)}
    (ctx : DerivationContext (Γ ++ Δ) (C ⧸ A) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compRight))}
    (F : PieceReplacementFamilyCore P) (p : CategoryPath) :
    true :: p ∈ F.categoryTargetPathsAt (ctx.nodePrefix ++ [.right]) ↔
      true :: p ∈ F.categoryTargetPathsAt ctx.nodePrefix := by
  constructor
  · intro hp
    have htarget :
        (true :: p, #F.atomName) ∈
          F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right]) :=
      (F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
        (true :: p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hout := F.compRight_right_A_copy_target_to_output_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
      (true :: p, #F.atomName)).mp hout).1
  · intro hp
    have htarget :
        (true :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix :=
      (F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
        (true :: p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hright := F.compRight_output_A_copy_target_to_right_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
      (true :: p, #F.atomName)).mp hright).1

/-- Context-parametric forward-composition preservation for canonical
node-local rewriting. -/
theorem rewrite_preserves_compRight_at
    {Γ Δ Ω : List Category} {C B A Z : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)}
    {t₂ : DerivationTree Δ (B ⧸ A)}
    (ctx : DerivationContext (Γ ++ Δ) (C ⧸ A) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compRight))}
    (F : PieceReplacementFamilyCore P)
    {L' R' O' : Category}
    (hL :
      F.rewriteNodeCategorySimul? (ctx.nodePrefix ++ [.left]) (C ⧸ B) = some L')
    (hR :
      F.rewriteNodeCategorySimul? (ctx.nodePrefix ++ [.right]) (B ⧸ A) = some R')
    (hO :
      F.rewriteNodeCategorySimul? ctx.nodePrefix (C ⧸ A) = some O') :
    Rule L' R' O' := by
  unfold rewriteNodeCategorySimul? at hL hR hO
  exact Category.replaceSimulAtPaths?_compRight_components
    (F.compRight_left_root_path_not_target_at ctx)
    (F.compRight_right_root_path_not_target_at ctx)
    (F.compRight_output_root_path_not_target_at ctx)
    (F.compRight_left_false_path_iff_output_false_path_at ctx)
    (F.compRight_left_true_path_iff_right_false_path_at ctx)
    (F.compRight_right_true_path_iff_output_true_path_at ctx)
    hL
    hR
    hO

/-- In contextual backward composition, the principal slash at the left child is
target-free. -/
theorem compLeft_left_root_path_not_target_at
    {Γ Δ Ω : List Category} {A B C Z : Category}
    {t₁ : DerivationTree Γ (A ⧹ B)} {t₂ : DerivationTree Δ (B ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) (A ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compLeft))}
    (F : PieceReplacementFamilyCore P) :
    [] ∉ F.categoryTargetPathsAt (ctx.nodePrefix ++ [.left]) := by
  intro hp
  have htarget :
      ([], #F.atomName) ∈ F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left]) := by
    exact (F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
      ([], #F.atomName)).mpr ⟨hp, rfl⟩
  have hprincipalLocal :
      DerivationTree.PrincipalConstructor
        (DerivationTree.binary t₁ t₂ Rule.compLeft) [.left] [] :=
    DerivationTree.PrincipalConstructor.compLeft_left t₁ t₂
  have hprincipal :
      DerivationTree.PrincipalConstructor
        (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compLeft))
        (ctx.nodePrefix ++ [.left]) [] :=
    ctx.liftPrincipalConstructor hprincipalLocal
  have hne := F.target_path_ne_of_principal hprincipal htarget
  exact hne rfl

/-- In contextual backward composition, the principal slash at the right child
is target-free. -/
theorem compLeft_right_root_path_not_target_at
    {Γ Δ Ω : List Category} {A B C Z : Category}
    {t₁ : DerivationTree Γ (A ⧹ B)} {t₂ : DerivationTree Δ (B ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) (A ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compLeft))}
    (F : PieceReplacementFamilyCore P) :
    [] ∉ F.categoryTargetPathsAt (ctx.nodePrefix ++ [.right]) := by
  intro hp
  have htarget :
      ([], #F.atomName) ∈ F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right]) := by
    exact (F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
      ([], #F.atomName)).mpr ⟨hp, rfl⟩
  have hprincipalLocal :
      DerivationTree.PrincipalConstructor
        (DerivationTree.binary t₁ t₂ Rule.compLeft) [.right] [] :=
    DerivationTree.PrincipalConstructor.compLeft_right t₁ t₂
  have hprincipal :
      DerivationTree.PrincipalConstructor
        (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compLeft))
        (ctx.nodePrefix ++ [.right]) [] :=
    ctx.liftPrincipalConstructor hprincipalLocal
  have hne := F.target_path_ne_of_principal hprincipal htarget
  exact hne rfl

/-- In contextual backward composition, the principal slash at the output node
is target-free. -/
theorem compLeft_output_root_path_not_target_at
    {Γ Δ Ω : List Category} {A B C Z : Category}
    {t₁ : DerivationTree Γ (A ⧹ B)} {t₂ : DerivationTree Δ (B ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) (A ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compLeft))}
    (F : PieceReplacementFamilyCore P) :
    [] ∉ F.categoryTargetPathsAt ctx.nodePrefix := by
  intro hp
  have htarget :
      ([], #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix := by
    exact (F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
      ([], #F.atomName)).mpr ⟨hp, rfl⟩
  have hprincipalLocal :
      DerivationTree.PrincipalConstructor
        (DerivationTree.binary t₁ t₂ Rule.compLeft) [] [] :=
    DerivationTree.PrincipalConstructor.compLeft_out t₁ t₂
  have hprincipal :
      DerivationTree.PrincipalConstructor
        (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compLeft))
        ctx.nodePrefix [] :=
    by simpa using ctx.liftPrincipalConstructor hprincipalLocal
  have hne := F.target_path_ne_of_principal hprincipal htarget
  exact hne rfl

/-- In contextual backward composition, replacing the left-premise `A` copy
forces the matching output `A` copy to be replaced. -/
theorem compLeft_left_A_copy_target_to_output_at
    {Γ Δ Ω : List Category} {A B C Z : Category}
    {t₁ : DerivationTree Γ (A ⧹ B)} {t₂ : DerivationTree Δ (B ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) (A ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compLeft))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget :
      (false :: p, #F.atomName) ∈
        F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left])) :
    (false :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix := by
  let localTree := DerivationTree.binary t₁ t₂ Rule.compLeft
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
      (false :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = false :: p := (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? (ctx.nodePrefix ++ [.left]) = some (A ⧹ B) :=
    ctx.categoryAt?_local (by simp [localTree, DerivationTree.categoryAt?])
  have hRcat : R.nodeCategory = A ⧹ B := by
    have hnodeAtR : (ctx.plug localTree).categoryAt? R.nodePath = some (A ⧹ B) := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix ++ [.left] := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = false :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = A ⧹ B := by
    rw [← R.cat_eq]
    exact hRcat
  let oLeft : Occurrence localTree := {
    nodePath := [.left]
    nodeCategory := A ⧹ B
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := false :: p
    isConstructor := by simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oOut : Occurrence localTree := {
    nodePath := []
    nodeCategory := A ⧹ C
    nodeAt := DerivationTree.categoryAt?_root localTree
    categoryPath := false :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_ldiv_false, horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_ldiv_false, horiginCat, horiginPos] using hslash)⟩
  }
  have hedge : TraceEdge oLeft oOut :=
    Or.inl (Or.inl (LocalTraceEdge.compLeft_A rfl rfl rfl rfl))
  simpa [oLeft, oOut] using
    F.mem_dedupCategoryTargetsAt_of_lifted_traceEdge ctx hR
      (by simpa [oLeft] using horiginNode)
      (by simpa [oLeft] using horiginCat)
      (by simpa [oLeft] using horiginPos)
      hedge

/-- In contextual backward composition, replacing the output `A` copy forces
the matching left-premise `A` copy to be replaced. -/
theorem compLeft_output_A_copy_target_to_left_at
    {Γ Δ Ω : List Category} {A B C Z : Category}
    {t₁ : DerivationTree Γ (A ⧹ B)} {t₂ : DerivationTree Δ (B ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) (A ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compLeft))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget : (false :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix) :
    (false :: p, #F.atomName) ∈
      F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left]) := by
  let localTree := DerivationTree.binary t₁ t₂ Rule.compLeft
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff ctx.nodePrefix
      (false :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = false :: p := (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? ctx.nodePrefix = some (A ⧹ C) :=
    by simpa using ctx.categoryAt?_local (DerivationTree.categoryAt?_root localTree)
  have hRcat : R.nodeCategory = A ⧹ C := by
    have hnodeAtR : (ctx.plug localTree).categoryAt? R.nodePath = some (A ⧹ C) := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = false :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = A ⧹ C := by
    rw [← R.cat_eq]
    exact hRcat
  let oOut : Occurrence localTree := {
    nodePath := []
    nodeCategory := A ⧹ C
    nodeAt := DerivationTree.categoryAt?_root localTree
    categoryPath := false :: p
    isConstructor := by simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oLeft : Occurrence localTree := {
    nodePath := [.left]
    nodeCategory := A ⧹ B
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := false :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_ldiv_false, horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_ldiv_false, horiginCat, horiginPos] using hslash)⟩
  }
  have hedge : TraceEdge oOut oLeft :=
    Or.inr (Or.inl (LocalTraceEdge.compLeft_A rfl rfl rfl rfl))
  simpa [oOut, oLeft] using
    F.mem_dedupCategoryTargetsAt_of_lifted_traceEdge ctx hR
      (by simpa [oOut] using horiginNode)
      (by simpa [oOut] using horiginCat)
      (by simpa [oOut] using horiginPos)
      hedge

/-- In contextual backward composition, replacing the left-premise `B` copy
forces the matching right-premise `B` copy to be replaced. -/
theorem compLeft_left_B_copy_target_to_right_at
    {Γ Δ Ω : List Category} {A B C Z : Category}
    {t₁ : DerivationTree Γ (A ⧹ B)} {t₂ : DerivationTree Δ (B ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) (A ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compLeft))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget :
      (true :: p, #F.atomName) ∈
        F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left])) :
    (false :: p, #F.atomName) ∈
      F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right]) := by
  let localTree := DerivationTree.binary t₁ t₂ Rule.compLeft
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
      (true :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = true :: p := (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? (ctx.nodePrefix ++ [.left]) = some (A ⧹ B) :=
    ctx.categoryAt?_local (by simp [localTree, DerivationTree.categoryAt?])
  have hRcat : R.nodeCategory = A ⧹ B := by
    have hnodeAtR : (ctx.plug localTree).categoryAt? R.nodePath = some (A ⧹ B) := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix ++ [.left] := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = true :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = A ⧹ B := by
    rw [← R.cat_eq]
    exact hRcat
  let oLeft : Occurrence localTree := {
    nodePath := [.left]
    nodeCategory := A ⧹ B
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := true :: p
    isConstructor := by simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oRight : Occurrence localTree := {
    nodePath := [.right]
    nodeCategory := B ⧹ C
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := false :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_ldiv_true, Category.subcategoryAt?_ldiv_false,
            horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_ldiv_true, Category.subcategoryAt?_ldiv_false,
            horiginCat, horiginPos] using hslash)⟩
  }
  have hedge : TraceEdge oLeft oRight :=
    Or.inl (Or.inl (LocalTraceEdge.compLeft_B rfl rfl rfl rfl))
  simpa [oLeft, oRight] using
    F.mem_dedupCategoryTargetsAt_of_lifted_traceEdge ctx hR
      (by simpa [oLeft] using horiginNode)
      (by simpa [oLeft] using horiginCat)
      (by simpa [oLeft] using horiginPos)
      hedge

/-- In contextual backward composition, replacing the right-premise `B` copy
forces the matching left-premise `B` copy to be replaced. -/
theorem compLeft_right_B_copy_target_to_left_at
    {Γ Δ Ω : List Category} {A B C Z : Category}
    {t₁ : DerivationTree Γ (A ⧹ B)} {t₂ : DerivationTree Δ (B ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) (A ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compLeft))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget :
      (false :: p, #F.atomName) ∈
        F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right])) :
    (true :: p, #F.atomName) ∈
      F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left]) := by
  let localTree := DerivationTree.binary t₁ t₂ Rule.compLeft
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
      (false :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = false :: p := (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? (ctx.nodePrefix ++ [.right]) = some (B ⧹ C) :=
    ctx.categoryAt?_local (by simp [localTree, DerivationTree.categoryAt?])
  have hRcat : R.nodeCategory = B ⧹ C := by
    have hnodeAtR : (ctx.plug localTree).categoryAt? R.nodePath = some (B ⧹ C) := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix ++ [.right] := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = false :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = B ⧹ C := by
    rw [← R.cat_eq]
    exact hRcat
  let oRight : Occurrence localTree := {
    nodePath := [.right]
    nodeCategory := B ⧹ C
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := false :: p
    isConstructor := by simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oLeft : Occurrence localTree := {
    nodePath := [.left]
    nodeCategory := A ⧹ B
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := true :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_ldiv_false, Category.subcategoryAt?_ldiv_true,
            horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_ldiv_false, Category.subcategoryAt?_ldiv_true,
            horiginCat, horiginPos] using hslash)⟩
  }
  have hedge : TraceEdge oRight oLeft :=
    Or.inr (Or.inl (LocalTraceEdge.compLeft_B rfl rfl rfl rfl))
  simpa [oRight, oLeft] using
    F.mem_dedupCategoryTargetsAt_of_lifted_traceEdge ctx hR
      (by simpa [oRight] using horiginNode)
      (by simpa [oRight] using horiginCat)
      (by simpa [oRight] using horiginPos)
      hedge

/-- In contextual backward composition, replacing the right-premise `C` copy
forces the matching output `C` copy to be replaced. -/
theorem compLeft_right_C_copy_target_to_output_at
    {Γ Δ Ω : List Category} {A B C Z : Category}
    {t₁ : DerivationTree Γ (A ⧹ B)} {t₂ : DerivationTree Δ (B ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) (A ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compLeft))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget :
      (true :: p, #F.atomName) ∈
        F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right])) :
    (true :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix := by
  let localTree := DerivationTree.binary t₁ t₂ Rule.compLeft
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
      (true :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = true :: p := (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? (ctx.nodePrefix ++ [.right]) = some (B ⧹ C) :=
    ctx.categoryAt?_local (by simp [localTree, DerivationTree.categoryAt?])
  have hRcat : R.nodeCategory = B ⧹ C := by
    have hnodeAtR : (ctx.plug localTree).categoryAt? R.nodePath = some (B ⧹ C) := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix ++ [.right] := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = true :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = B ⧹ C := by
    rw [← R.cat_eq]
    exact hRcat
  let oRight : Occurrence localTree := {
    nodePath := [.right]
    nodeCategory := B ⧹ C
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := true :: p
    isConstructor := by simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oOut : Occurrence localTree := {
    nodePath := []
    nodeCategory := A ⧹ C
    nodeAt := DerivationTree.categoryAt?_root localTree
    categoryPath := true :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_ldiv_true, horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_ldiv_true, horiginCat, horiginPos] using hslash)⟩
  }
  have hedge : TraceEdge oRight oOut :=
    Or.inl (Or.inl (LocalTraceEdge.compLeft_C rfl rfl rfl rfl))
  simpa [oRight, oOut] using
    F.mem_dedupCategoryTargetsAt_of_lifted_traceEdge ctx hR
      (by simpa [oRight] using horiginNode)
      (by simpa [oRight] using horiginCat)
      (by simpa [oRight] using horiginPos)
      hedge

/-- In contextual backward composition, replacing the output `C` copy forces
the matching right-premise `C` copy to be replaced. -/
theorem compLeft_output_C_copy_target_to_right_at
    {Γ Δ Ω : List Category} {A B C Z : Category}
    {t₁ : DerivationTree Γ (A ⧹ B)} {t₂ : DerivationTree Δ (B ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) (A ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compLeft))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget : (true :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix) :
    (true :: p, #F.atomName) ∈
      F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right]) := by
  let localTree := DerivationTree.binary t₁ t₂ Rule.compLeft
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff ctx.nodePrefix
      (true :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = true :: p := (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? ctx.nodePrefix = some (A ⧹ C) :=
    by simpa using ctx.categoryAt?_local (DerivationTree.categoryAt?_root localTree)
  have hRcat : R.nodeCategory = A ⧹ C := by
    have hnodeAtR : (ctx.plug localTree).categoryAt? R.nodePath = some (A ⧹ C) := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = true :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = A ⧹ C := by
    rw [← R.cat_eq]
    exact hRcat
  let oOut : Occurrence localTree := {
    nodePath := []
    nodeCategory := A ⧹ C
    nodeAt := DerivationTree.categoryAt?_root localTree
    categoryPath := true :: p
    isConstructor := by simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oRight : Occurrence localTree := {
    nodePath := [.right]
    nodeCategory := B ⧹ C
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := true :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_ldiv_true, horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_ldiv_true, horiginCat, horiginPos] using hslash)⟩
  }
  have hedge : TraceEdge oOut oRight :=
    Or.inr (Or.inl (LocalTraceEdge.compLeft_C rfl rfl rfl rfl))
  simpa [oOut, oRight] using
    F.mem_dedupCategoryTargetsAt_of_lifted_traceEdge ctx hR
      (by simpa [oOut] using horiginNode)
      (by simpa [oOut] using horiginCat)
      (by simpa [oOut] using horiginPos)
      hedge

/-- Path-only synchronization between the left-premise and output `A` copies in
contextual backward composition. -/
theorem compLeft_left_false_path_iff_output_false_path_at
    {Γ Δ Ω : List Category} {A B C Z : Category}
    {t₁ : DerivationTree Γ (A ⧹ B)} {t₂ : DerivationTree Δ (B ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) (A ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compLeft))}
    (F : PieceReplacementFamilyCore P) (p : CategoryPath) :
    false :: p ∈ F.categoryTargetPathsAt (ctx.nodePrefix ++ [.left]) ↔
      false :: p ∈ F.categoryTargetPathsAt ctx.nodePrefix := by
  constructor
  · intro hp
    have htarget :
        (false :: p, #F.atomName) ∈
          F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left]) :=
      (F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
        (false :: p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hout := F.compLeft_left_A_copy_target_to_output_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
      (false :: p, #F.atomName)).mp hout).1
  · intro hp
    have htarget :
        (false :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix :=
      (F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
        (false :: p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hleft := F.compLeft_output_A_copy_target_to_left_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
      (false :: p, #F.atomName)).mp hleft).1

/-- Path-only synchronization between the two `B` copies in contextual backward
composition. -/
theorem compLeft_left_true_path_iff_right_false_path_at
    {Γ Δ Ω : List Category} {A B C Z : Category}
    {t₁ : DerivationTree Γ (A ⧹ B)} {t₂ : DerivationTree Δ (B ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) (A ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compLeft))}
    (F : PieceReplacementFamilyCore P) (p : CategoryPath) :
    true :: p ∈ F.categoryTargetPathsAt (ctx.nodePrefix ++ [.left]) ↔
      false :: p ∈ F.categoryTargetPathsAt (ctx.nodePrefix ++ [.right]) := by
  constructor
  · intro hp
    have htarget :
        (true :: p, #F.atomName) ∈
          F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left]) :=
      (F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
        (true :: p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hright := F.compLeft_left_B_copy_target_to_right_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
      (false :: p, #F.atomName)).mp hright).1
  · intro hp
    have htarget :
        (false :: p, #F.atomName) ∈
          F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right]) :=
      (F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
        (false :: p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hleft := F.compLeft_right_B_copy_target_to_left_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
      (true :: p, #F.atomName)).mp hleft).1

/-- Path-only synchronization between the right-premise and output `C` copies in
contextual backward composition. -/
theorem compLeft_right_true_path_iff_output_true_path_at
    {Γ Δ Ω : List Category} {A B C Z : Category}
    {t₁ : DerivationTree Γ (A ⧹ B)} {t₂ : DerivationTree Δ (B ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) (A ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compLeft))}
    (F : PieceReplacementFamilyCore P) (p : CategoryPath) :
    true :: p ∈ F.categoryTargetPathsAt (ctx.nodePrefix ++ [.right]) ↔
      true :: p ∈ F.categoryTargetPathsAt ctx.nodePrefix := by
  constructor
  · intro hp
    have htarget :
        (true :: p, #F.atomName) ∈
          F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right]) :=
      (F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
        (true :: p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hout := F.compLeft_right_C_copy_target_to_output_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
      (true :: p, #F.atomName)).mp hout).1
  · intro hp
    have htarget :
        (true :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix :=
      (F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
        (true :: p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hright := F.compLeft_output_C_copy_target_to_right_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
      (true :: p, #F.atomName)).mp hright).1

/-- Context-parametric backward-composition preservation for canonical
node-local rewriting. -/
theorem rewrite_preserves_compLeft_at
    {Γ Δ Ω : List Category} {A B C Z : Category}
    {t₁ : DerivationTree Γ (A ⧹ B)}
    {t₂ : DerivationTree Δ (B ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) (A ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compLeft))}
    (F : PieceReplacementFamilyCore P)
    {L' R' O' : Category}
    (hL :
      F.rewriteNodeCategorySimul? (ctx.nodePrefix ++ [.left]) (A ⧹ B) = some L')
    (hR :
      F.rewriteNodeCategorySimul? (ctx.nodePrefix ++ [.right]) (B ⧹ C) = some R')
    (hO :
      F.rewriteNodeCategorySimul? ctx.nodePrefix (A ⧹ C) = some O') :
    Rule L' R' O' := by
  unfold rewriteNodeCategorySimul? at hL hR hO
  exact Category.replaceSimulAtPaths?_compLeft_components
    (F.compLeft_left_root_path_not_target_at ctx)
    (F.compLeft_right_root_path_not_target_at ctx)
    (F.compLeft_output_root_path_not_target_at ctx)
    (F.compLeft_left_false_path_iff_output_false_path_at ctx)
    (F.compLeft_left_true_path_iff_right_false_path_at ctx)
    (F.compLeft_right_true_path_iff_output_true_path_at ctx)
    hL
    hR
    hO

/-- In contextual forward crossed composition, the principal slash at the left
child is target-free. -/
theorem crossedRight_left_root_path_not_target_at
    {Γ Δ Ω : List Category} {C B A Z : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (A ⧹ B)}
    (ctx : DerivationContext (Γ ++ Δ) (A ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedRight))}
    (F : PieceReplacementFamilyCore P) :
    [] ∉ F.categoryTargetPathsAt (ctx.nodePrefix ++ [.left]) := by
  intro hp
  have htarget :
      ([], #F.atomName) ∈ F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left]) := by
    exact (F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
      ([], #F.atomName)).mpr ⟨hp, rfl⟩
  have hprincipalLocal :
      DerivationTree.PrincipalConstructor
        (DerivationTree.binary t₁ t₂ Rule.crossedRight) [.left] [] :=
    DerivationTree.PrincipalConstructor.crossedRight_left t₁ t₂
  have hprincipal :
      DerivationTree.PrincipalConstructor
        (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedRight))
        (ctx.nodePrefix ++ [.left]) [] :=
    ctx.liftPrincipalConstructor hprincipalLocal
  have hne := F.target_path_ne_of_principal hprincipal htarget
  exact hne rfl

/-- In contextual forward crossed composition, the principal slash at the right
child is target-free. -/
theorem crossedRight_right_root_path_not_target_at
    {Γ Δ Ω : List Category} {C B A Z : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (A ⧹ B)}
    (ctx : DerivationContext (Γ ++ Δ) (A ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedRight))}
    (F : PieceReplacementFamilyCore P) :
    [] ∉ F.categoryTargetPathsAt (ctx.nodePrefix ++ [.right]) := by
  intro hp
  have htarget :
      ([], #F.atomName) ∈ F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right]) := by
    exact (F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
      ([], #F.atomName)).mpr ⟨hp, rfl⟩
  have hprincipalLocal :
      DerivationTree.PrincipalConstructor
        (DerivationTree.binary t₁ t₂ Rule.crossedRight) [.right] [] :=
    DerivationTree.PrincipalConstructor.crossedRight_right t₁ t₂
  have hprincipal :
      DerivationTree.PrincipalConstructor
        (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedRight))
        (ctx.nodePrefix ++ [.right]) [] :=
    ctx.liftPrincipalConstructor hprincipalLocal
  have hne := F.target_path_ne_of_principal hprincipal htarget
  exact hne rfl

/-- In contextual forward crossed composition, the principal slash at the output
node is target-free. -/
theorem crossedRight_output_root_path_not_target_at
    {Γ Δ Ω : List Category} {C B A Z : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (A ⧹ B)}
    (ctx : DerivationContext (Γ ++ Δ) (A ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedRight))}
    (F : PieceReplacementFamilyCore P) :
    [] ∉ F.categoryTargetPathsAt ctx.nodePrefix := by
  intro hp
  have htarget :
      ([], #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix := by
    exact (F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
      ([], #F.atomName)).mpr ⟨hp, rfl⟩
  have hprincipalLocal :
      DerivationTree.PrincipalConstructor
        (DerivationTree.binary t₁ t₂ Rule.crossedRight) [] [] :=
    DerivationTree.PrincipalConstructor.crossedRight_out t₁ t₂
  have hprincipal :
      DerivationTree.PrincipalConstructor
        (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedRight))
        ctx.nodePrefix [] :=
    by simpa using ctx.liftPrincipalConstructor hprincipalLocal
  have hne := F.target_path_ne_of_principal hprincipal htarget
  exact hne rfl

/-- In contextual forward crossed composition, replacing the left-premise `C`
copy forces the matching output `C` copy to be replaced. -/
theorem crossedRight_left_C_copy_target_to_output_at
    {Γ Δ Ω : List Category} {C B A Z : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (A ⧹ B)}
    (ctx : DerivationContext (Γ ++ Δ) (A ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedRight))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget :
      (false :: p, #F.atomName) ∈
        F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left])) :
    (true :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix := by
  let localTree := DerivationTree.binary t₁ t₂ Rule.crossedRight
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
      (false :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = false :: p := (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? (ctx.nodePrefix ++ [.left]) = some (C ⧸ B) :=
    ctx.categoryAt?_local (by simp [localTree, DerivationTree.categoryAt?])
  have hRcat : R.nodeCategory = C ⧸ B := by
    have hnodeAtR : (ctx.plug localTree).categoryAt? R.nodePath = some (C ⧸ B) := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix ++ [.left] := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = false :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = C ⧸ B := by
    rw [← R.cat_eq]
    exact hRcat
  let oLeft : Occurrence localTree := {
    nodePath := [.left]
    nodeCategory := C ⧸ B
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := false :: p
    isConstructor := by simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oOut : Occurrence localTree := {
    nodePath := []
    nodeCategory := A ⧹ C
    nodeAt := DerivationTree.categoryAt?_root localTree
    categoryPath := true :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_rdiv_false, Category.subcategoryAt?_ldiv_true,
            horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_rdiv_false, Category.subcategoryAt?_ldiv_true,
            horiginCat, horiginPos] using hslash)⟩
  }
  have hedge : TraceEdge oLeft oOut :=
    Or.inl (Or.inl (LocalTraceEdge.crossedRight_C rfl rfl rfl rfl))
  simpa [oLeft, oOut] using
    F.mem_dedupCategoryTargetsAt_of_lifted_traceEdge ctx hR
      (by simpa [oLeft] using horiginNode)
      (by simpa [oLeft] using horiginCat)
      (by simpa [oLeft] using horiginPos)
      hedge

/-- In contextual forward crossed composition, replacing the output `C` copy
forces the matching left-premise `C` copy to be replaced. -/
theorem crossedRight_output_C_copy_target_to_left_at
    {Γ Δ Ω : List Category} {C B A Z : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (A ⧹ B)}
    (ctx : DerivationContext (Γ ++ Δ) (A ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedRight))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget : (true :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix) :
    (false :: p, #F.atomName) ∈
      F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left]) := by
  let localTree := DerivationTree.binary t₁ t₂ Rule.crossedRight
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff ctx.nodePrefix
      (true :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = true :: p := (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? ctx.nodePrefix = some (A ⧹ C) :=
    by simpa using ctx.categoryAt?_local (DerivationTree.categoryAt?_root localTree)
  have hRcat : R.nodeCategory = A ⧹ C := by
    have hnodeAtR : (ctx.plug localTree).categoryAt? R.nodePath = some (A ⧹ C) := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = true :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = A ⧹ C := by
    rw [← R.cat_eq]
    exact hRcat
  let oOut : Occurrence localTree := {
    nodePath := []
    nodeCategory := A ⧹ C
    nodeAt := DerivationTree.categoryAt?_root localTree
    categoryPath := true :: p
    isConstructor := by simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oLeft : Occurrence localTree := {
    nodePath := [.left]
    nodeCategory := C ⧸ B
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := false :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_ldiv_true, Category.subcategoryAt?_rdiv_false,
            horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_ldiv_true, Category.subcategoryAt?_rdiv_false,
            horiginCat, horiginPos] using hslash)⟩
  }
  have hedge : TraceEdge oOut oLeft :=
    Or.inr (Or.inl (LocalTraceEdge.crossedRight_C rfl rfl rfl rfl))
  simpa [oOut, oLeft] using
    F.mem_dedupCategoryTargetsAt_of_lifted_traceEdge ctx hR
      (by simpa [oOut] using horiginNode)
      (by simpa [oOut] using horiginCat)
      (by simpa [oOut] using horiginPos)
      hedge

/-- In contextual forward crossed composition, replacing the left-premise `B`
copy forces the matching right-premise `B` copy to be replaced. -/
theorem crossedRight_left_B_copy_target_to_right_at
    {Γ Δ Ω : List Category} {C B A Z : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (A ⧹ B)}
    (ctx : DerivationContext (Γ ++ Δ) (A ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedRight))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget :
      (true :: p, #F.atomName) ∈
        F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left])) :
    (true :: p, #F.atomName) ∈
      F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right]) := by
  let localTree := DerivationTree.binary t₁ t₂ Rule.crossedRight
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
      (true :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = true :: p := (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? (ctx.nodePrefix ++ [.left]) = some (C ⧸ B) :=
    ctx.categoryAt?_local (by simp [localTree, DerivationTree.categoryAt?])
  have hRcat : R.nodeCategory = C ⧸ B := by
    have hnodeAtR : (ctx.plug localTree).categoryAt? R.nodePath = some (C ⧸ B) := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix ++ [.left] := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = true :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = C ⧸ B := by
    rw [← R.cat_eq]
    exact hRcat
  let oLeft : Occurrence localTree := {
    nodePath := [.left]
    nodeCategory := C ⧸ B
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := true :: p
    isConstructor := by simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oRight : Occurrence localTree := {
    nodePath := [.right]
    nodeCategory := A ⧹ B
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := true :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_rdiv_true, Category.subcategoryAt?_ldiv_true,
            horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_rdiv_true, Category.subcategoryAt?_ldiv_true,
            horiginCat, horiginPos] using hslash)⟩
  }
  have hedge : TraceEdge oLeft oRight :=
    Or.inl (Or.inl (LocalTraceEdge.crossedRight_B rfl rfl rfl rfl))
  simpa [oLeft, oRight] using
    F.mem_dedupCategoryTargetsAt_of_lifted_traceEdge ctx hR
      (by simpa [oLeft] using horiginNode)
      (by simpa [oLeft] using horiginCat)
      (by simpa [oLeft] using horiginPos)
      hedge

/-- In contextual forward crossed composition, replacing the right-premise `B`
copy forces the matching left-premise `B` copy to be replaced. -/
theorem crossedRight_right_B_copy_target_to_left_at
    {Γ Δ Ω : List Category} {C B A Z : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (A ⧹ B)}
    (ctx : DerivationContext (Γ ++ Δ) (A ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedRight))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget :
      (true :: p, #F.atomName) ∈
        F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right])) :
    (true :: p, #F.atomName) ∈
      F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left]) := by
  let localTree := DerivationTree.binary t₁ t₂ Rule.crossedRight
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
      (true :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = true :: p := (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? (ctx.nodePrefix ++ [.right]) = some (A ⧹ B) :=
    ctx.categoryAt?_local (by simp [localTree, DerivationTree.categoryAt?])
  have hRcat : R.nodeCategory = A ⧹ B := by
    have hnodeAtR : (ctx.plug localTree).categoryAt? R.nodePath = some (A ⧹ B) := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix ++ [.right] := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = true :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = A ⧹ B := by
    rw [← R.cat_eq]
    exact hRcat
  let oRight : Occurrence localTree := {
    nodePath := [.right]
    nodeCategory := A ⧹ B
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := true :: p
    isConstructor := by simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oLeft : Occurrence localTree := {
    nodePath := [.left]
    nodeCategory := C ⧸ B
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := true :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_ldiv_true, Category.subcategoryAt?_rdiv_true,
            horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_ldiv_true, Category.subcategoryAt?_rdiv_true,
            horiginCat, horiginPos] using hslash)⟩
  }
  have hedge : TraceEdge oRight oLeft :=
    Or.inr (Or.inl (LocalTraceEdge.crossedRight_B rfl rfl rfl rfl))
  simpa [oRight, oLeft] using
    F.mem_dedupCategoryTargetsAt_of_lifted_traceEdge ctx hR
      (by simpa [oRight] using horiginNode)
      (by simpa [oRight] using horiginCat)
      (by simpa [oRight] using horiginPos)
      hedge

/-- In contextual forward crossed composition, replacing the right-premise `A`
copy forces the matching output `A` copy to be replaced. -/
theorem crossedRight_right_A_copy_target_to_output_at
    {Γ Δ Ω : List Category} {C B A Z : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (A ⧹ B)}
    (ctx : DerivationContext (Γ ++ Δ) (A ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedRight))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget :
      (false :: p, #F.atomName) ∈
        F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right])) :
    (false :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix := by
  let localTree := DerivationTree.binary t₁ t₂ Rule.crossedRight
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
      (false :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = false :: p := (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? (ctx.nodePrefix ++ [.right]) = some (A ⧹ B) :=
    ctx.categoryAt?_local (by simp [localTree, DerivationTree.categoryAt?])
  have hRcat : R.nodeCategory = A ⧹ B := by
    have hnodeAtR : (ctx.plug localTree).categoryAt? R.nodePath = some (A ⧹ B) := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix ++ [.right] := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = false :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = A ⧹ B := by
    rw [← R.cat_eq]
    exact hRcat
  let oRight : Occurrence localTree := {
    nodePath := [.right]
    nodeCategory := A ⧹ B
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := false :: p
    isConstructor := by simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oOut : Occurrence localTree := {
    nodePath := []
    nodeCategory := A ⧹ C
    nodeAt := DerivationTree.categoryAt?_root localTree
    categoryPath := false :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_ldiv_false, horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_ldiv_false, horiginCat, horiginPos] using hslash)⟩
  }
  have hedge : TraceEdge oRight oOut :=
    Or.inl (Or.inl (LocalTraceEdge.crossedRight_A rfl rfl rfl rfl))
  simpa [oRight, oOut] using
    F.mem_dedupCategoryTargetsAt_of_lifted_traceEdge ctx hR
      (by simpa [oRight] using horiginNode)
      (by simpa [oRight] using horiginCat)
      (by simpa [oRight] using horiginPos)
      hedge

/-- In contextual forward crossed composition, replacing the output `A` copy
forces the matching right-premise `A` copy to be replaced. -/
theorem crossedRight_output_A_copy_target_to_right_at
    {Γ Δ Ω : List Category} {C B A Z : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (A ⧹ B)}
    (ctx : DerivationContext (Γ ++ Δ) (A ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedRight))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget : (false :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix) :
    (false :: p, #F.atomName) ∈
      F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right]) := by
  let localTree := DerivationTree.binary t₁ t₂ Rule.crossedRight
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff ctx.nodePrefix
      (false :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = false :: p := (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? ctx.nodePrefix = some (A ⧹ C) :=
    by simpa using ctx.categoryAt?_local (DerivationTree.categoryAt?_root localTree)
  have hRcat : R.nodeCategory = A ⧹ C := by
    have hnodeAtR : (ctx.plug localTree).categoryAt? R.nodePath = some (A ⧹ C) := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = false :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = A ⧹ C := by
    rw [← R.cat_eq]
    exact hRcat
  let oOut : Occurrence localTree := {
    nodePath := []
    nodeCategory := A ⧹ C
    nodeAt := DerivationTree.categoryAt?_root localTree
    categoryPath := false :: p
    isConstructor := by simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oRight : Occurrence localTree := {
    nodePath := [.right]
    nodeCategory := A ⧹ B
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := false :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_ldiv_false, horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_ldiv_false, horiginCat, horiginPos] using hslash)⟩
  }
  have hedge : TraceEdge oOut oRight :=
    Or.inr (Or.inl (LocalTraceEdge.crossedRight_A rfl rfl rfl rfl))
  simpa [oOut, oRight] using
    F.mem_dedupCategoryTargetsAt_of_lifted_traceEdge ctx hR
      (by simpa [oOut] using horiginNode)
      (by simpa [oOut] using horiginCat)
      (by simpa [oOut] using horiginPos)
      hedge

/-- Path-only synchronization between the left-premise and output `C` copies in
contextual forward crossed composition. -/
theorem crossedRight_left_false_path_iff_output_true_path_at
    {Γ Δ Ω : List Category} {C B A Z : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (A ⧹ B)}
    (ctx : DerivationContext (Γ ++ Δ) (A ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedRight))}
    (F : PieceReplacementFamilyCore P) (p : CategoryPath) :
    false :: p ∈ F.categoryTargetPathsAt (ctx.nodePrefix ++ [.left]) ↔
      true :: p ∈ F.categoryTargetPathsAt ctx.nodePrefix := by
  constructor
  · intro hp
    have htarget :
        (false :: p, #F.atomName) ∈
          F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left]) :=
      (F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
        (false :: p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hout := F.crossedRight_left_C_copy_target_to_output_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
      (true :: p, #F.atomName)).mp hout).1
  · intro hp
    have htarget :
        (true :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix :=
      (F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
        (true :: p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hleft := F.crossedRight_output_C_copy_target_to_left_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
      (false :: p, #F.atomName)).mp hleft).1

/-- Path-only synchronization between the two `B` copies in contextual forward
crossed composition. -/
theorem crossedRight_left_true_path_iff_right_true_path_at
    {Γ Δ Ω : List Category} {C B A Z : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (A ⧹ B)}
    (ctx : DerivationContext (Γ ++ Δ) (A ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedRight))}
    (F : PieceReplacementFamilyCore P) (p : CategoryPath) :
    true :: p ∈ F.categoryTargetPathsAt (ctx.nodePrefix ++ [.left]) ↔
      true :: p ∈ F.categoryTargetPathsAt (ctx.nodePrefix ++ [.right]) := by
  constructor
  · intro hp
    have htarget :
        (true :: p, #F.atomName) ∈
          F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left]) :=
      (F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
        (true :: p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hright := F.crossedRight_left_B_copy_target_to_right_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
      (true :: p, #F.atomName)).mp hright).1
  · intro hp
    have htarget :
        (true :: p, #F.atomName) ∈
          F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right]) :=
      (F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
        (true :: p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hleft := F.crossedRight_right_B_copy_target_to_left_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
      (true :: p, #F.atomName)).mp hleft).1

/-- Path-only synchronization between the right-premise and output `A` copies in
contextual forward crossed composition. -/
theorem crossedRight_right_false_path_iff_output_false_path_at
    {Γ Δ Ω : List Category} {C B A Z : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (A ⧹ B)}
    (ctx : DerivationContext (Γ ++ Δ) (A ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedRight))}
    (F : PieceReplacementFamilyCore P) (p : CategoryPath) :
    false :: p ∈ F.categoryTargetPathsAt (ctx.nodePrefix ++ [.right]) ↔
      false :: p ∈ F.categoryTargetPathsAt ctx.nodePrefix := by
  constructor
  · intro hp
    have htarget :
        (false :: p, #F.atomName) ∈
          F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right]) :=
      (F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
        (false :: p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hout := F.crossedRight_right_A_copy_target_to_output_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
      (false :: p, #F.atomName)).mp hout).1
  · intro hp
    have htarget :
        (false :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix :=
      (F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
        (false :: p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hright := F.crossedRight_output_A_copy_target_to_right_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
      (false :: p, #F.atomName)).mp hright).1

/-- Context-parametric forward crossed-composition preservation for canonical
node-local rewriting. -/
theorem rewrite_preserves_crossedRight_at
    {Γ Δ Ω : List Category} {C B A Z : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)}
    {t₂ : DerivationTree Δ (A ⧹ B)}
    (ctx : DerivationContext (Γ ++ Δ) (A ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedRight))}
    (F : PieceReplacementFamilyCore P)
    {L' R' O' : Category}
    (hL :
      F.rewriteNodeCategorySimul? (ctx.nodePrefix ++ [.left]) (C ⧸ B) = some L')
    (hR :
      F.rewriteNodeCategorySimul? (ctx.nodePrefix ++ [.right]) (A ⧹ B) = some R')
    (hO :
      F.rewriteNodeCategorySimul? ctx.nodePrefix (A ⧹ C) = some O') :
    Rule L' R' O' := by
  unfold rewriteNodeCategorySimul? at hL hR hO
  exact Category.replaceSimulAtPaths?_crossedRight_components
    (F.crossedRight_left_root_path_not_target_at ctx)
    (F.crossedRight_right_root_path_not_target_at ctx)
    (F.crossedRight_output_root_path_not_target_at ctx)
    (F.crossedRight_left_false_path_iff_output_true_path_at ctx)
    (F.crossedRight_left_true_path_iff_right_true_path_at ctx)
    (F.crossedRight_right_false_path_iff_output_false_path_at ctx)
    hL
    hR
    hO

/-- In contextual backward crossed composition, the principal slash at the left
child is target-free. -/
theorem crossedLeft_left_root_path_not_target_at
    {Γ Δ Ω : List Category} {B A C Z : Category}
    {t₁ : DerivationTree Γ (B ⧸ A)} {t₂ : DerivationTree Δ (B ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) (C ⧸ A) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedLeft))}
    (F : PieceReplacementFamilyCore P) :
    [] ∉ F.categoryTargetPathsAt (ctx.nodePrefix ++ [.left]) := by
  intro hp
  have htarget :
      ([], #F.atomName) ∈ F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left]) := by
    exact (F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
      ([], #F.atomName)).mpr ⟨hp, rfl⟩
  have hprincipalLocal :
      DerivationTree.PrincipalConstructor
        (DerivationTree.binary t₁ t₂ Rule.crossedLeft) [.left] [] :=
    DerivationTree.PrincipalConstructor.crossedLeft_left t₁ t₂
  have hprincipal :
      DerivationTree.PrincipalConstructor
        (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedLeft))
        (ctx.nodePrefix ++ [.left]) [] :=
    ctx.liftPrincipalConstructor hprincipalLocal
  have hne := F.target_path_ne_of_principal hprincipal htarget
  exact hne rfl

/-- In contextual backward crossed composition, the principal slash at the right
child is target-free. -/
theorem crossedLeft_right_root_path_not_target_at
    {Γ Δ Ω : List Category} {B A C Z : Category}
    {t₁ : DerivationTree Γ (B ⧸ A)} {t₂ : DerivationTree Δ (B ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) (C ⧸ A) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedLeft))}
    (F : PieceReplacementFamilyCore P) :
    [] ∉ F.categoryTargetPathsAt (ctx.nodePrefix ++ [.right]) := by
  intro hp
  have htarget :
      ([], #F.atomName) ∈ F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right]) := by
    exact (F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
      ([], #F.atomName)).mpr ⟨hp, rfl⟩
  have hprincipalLocal :
      DerivationTree.PrincipalConstructor
        (DerivationTree.binary t₁ t₂ Rule.crossedLeft) [.right] [] :=
    DerivationTree.PrincipalConstructor.crossedLeft_right t₁ t₂
  have hprincipal :
      DerivationTree.PrincipalConstructor
        (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedLeft))
        (ctx.nodePrefix ++ [.right]) [] :=
    ctx.liftPrincipalConstructor hprincipalLocal
  have hne := F.target_path_ne_of_principal hprincipal htarget
  exact hne rfl

/-- In contextual backward crossed composition, the principal slash at the
output node is target-free. -/
theorem crossedLeft_output_root_path_not_target_at
    {Γ Δ Ω : List Category} {B A C Z : Category}
    {t₁ : DerivationTree Γ (B ⧸ A)} {t₂ : DerivationTree Δ (B ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) (C ⧸ A) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedLeft))}
    (F : PieceReplacementFamilyCore P) :
    [] ∉ F.categoryTargetPathsAt ctx.nodePrefix := by
  intro hp
  have htarget :
      ([], #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix := by
    exact (F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
      ([], #F.atomName)).mpr ⟨hp, rfl⟩
  have hprincipalLocal :
      DerivationTree.PrincipalConstructor
        (DerivationTree.binary t₁ t₂ Rule.crossedLeft) [] [] :=
    DerivationTree.PrincipalConstructor.crossedLeft_out t₁ t₂
  have hprincipal :
      DerivationTree.PrincipalConstructor
        (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedLeft))
        ctx.nodePrefix [] :=
    by simpa using ctx.liftPrincipalConstructor hprincipalLocal
  have hne := F.target_path_ne_of_principal hprincipal htarget
  exact hne rfl

/-- In contextual backward crossed composition, replacing the left-premise `B`
copy forces the matching right-premise `B` copy to be replaced. -/
theorem crossedLeft_left_B_copy_target_to_right_at
    {Γ Δ Ω : List Category} {B A C Z : Category}
    {t₁ : DerivationTree Γ (B ⧸ A)} {t₂ : DerivationTree Δ (B ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) (C ⧸ A) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedLeft))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget :
      (false :: p, #F.atomName) ∈
        F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left])) :
    (false :: p, #F.atomName) ∈
      F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right]) := by
  let localTree := DerivationTree.binary t₁ t₂ Rule.crossedLeft
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
      (false :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = false :: p := (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? (ctx.nodePrefix ++ [.left]) = some (B ⧸ A) :=
    ctx.categoryAt?_local (by simp [localTree, DerivationTree.categoryAt?])
  have hRcat : R.nodeCategory = B ⧸ A := by
    have hnodeAtR : (ctx.plug localTree).categoryAt? R.nodePath = some (B ⧸ A) := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix ++ [.left] := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = false :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = B ⧸ A := by
    rw [← R.cat_eq]
    exact hRcat
  let oLeft : Occurrence localTree := {
    nodePath := [.left]
    nodeCategory := B ⧸ A
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := false :: p
    isConstructor := by simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oRight : Occurrence localTree := {
    nodePath := [.right]
    nodeCategory := B ⧹ C
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := false :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_rdiv_false, Category.subcategoryAt?_ldiv_false,
            horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_rdiv_false, Category.subcategoryAt?_ldiv_false,
            horiginCat, horiginPos] using hslash)⟩
  }
  have hedge : TraceEdge oLeft oRight :=
    Or.inl (Or.inl (LocalTraceEdge.crossedLeft_B rfl rfl rfl rfl))
  simpa [oLeft, oRight] using
    F.mem_dedupCategoryTargetsAt_of_lifted_traceEdge ctx hR
      (by simpa [oLeft] using horiginNode)
      (by simpa [oLeft] using horiginCat)
      (by simpa [oLeft] using horiginPos)
      hedge

/-- In contextual backward crossed composition, replacing the right-premise `B`
copy forces the matching left-premise `B` copy to be replaced. -/
theorem crossedLeft_right_B_copy_target_to_left_at
    {Γ Δ Ω : List Category} {B A C Z : Category}
    {t₁ : DerivationTree Γ (B ⧸ A)} {t₂ : DerivationTree Δ (B ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) (C ⧸ A) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedLeft))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget :
      (false :: p, #F.atomName) ∈
        F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right])) :
    (false :: p, #F.atomName) ∈
      F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left]) := by
  let localTree := DerivationTree.binary t₁ t₂ Rule.crossedLeft
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
      (false :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = false :: p := (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? (ctx.nodePrefix ++ [.right]) = some (B ⧹ C) :=
    ctx.categoryAt?_local (by simp [localTree, DerivationTree.categoryAt?])
  have hRcat : R.nodeCategory = B ⧹ C := by
    have hnodeAtR : (ctx.plug localTree).categoryAt? R.nodePath = some (B ⧹ C) := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix ++ [.right] := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = false :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = B ⧹ C := by
    rw [← R.cat_eq]
    exact hRcat
  let oRight : Occurrence localTree := {
    nodePath := [.right]
    nodeCategory := B ⧹ C
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := false :: p
    isConstructor := by simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oLeft : Occurrence localTree := {
    nodePath := [.left]
    nodeCategory := B ⧸ A
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := false :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_ldiv_false, Category.subcategoryAt?_rdiv_false,
            horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_ldiv_false, Category.subcategoryAt?_rdiv_false,
            horiginCat, horiginPos] using hslash)⟩
  }
  have hedge : TraceEdge oRight oLeft :=
    Or.inr (Or.inl (LocalTraceEdge.crossedLeft_B rfl rfl rfl rfl))
  simpa [oRight, oLeft] using
    F.mem_dedupCategoryTargetsAt_of_lifted_traceEdge ctx hR
      (by simpa [oRight] using horiginNode)
      (by simpa [oRight] using horiginCat)
      (by simpa [oRight] using horiginPos)
      hedge

/-- In contextual backward crossed composition, replacing the left-premise `A`
copy forces the matching output `A` copy to be replaced. -/
theorem crossedLeft_left_A_copy_target_to_output_at
    {Γ Δ Ω : List Category} {B A C Z : Category}
    {t₁ : DerivationTree Γ (B ⧸ A)} {t₂ : DerivationTree Δ (B ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) (C ⧸ A) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedLeft))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget :
      (true :: p, #F.atomName) ∈
        F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left])) :
    (true :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix := by
  let localTree := DerivationTree.binary t₁ t₂ Rule.crossedLeft
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
      (true :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = true :: p := (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? (ctx.nodePrefix ++ [.left]) = some (B ⧸ A) :=
    ctx.categoryAt?_local (by simp [localTree, DerivationTree.categoryAt?])
  have hRcat : R.nodeCategory = B ⧸ A := by
    have hnodeAtR : (ctx.plug localTree).categoryAt? R.nodePath = some (B ⧸ A) := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix ++ [.left] := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = true :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = B ⧸ A := by
    rw [← R.cat_eq]
    exact hRcat
  let oLeft : Occurrence localTree := {
    nodePath := [.left]
    nodeCategory := B ⧸ A
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := true :: p
    isConstructor := by simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oOut : Occurrence localTree := {
    nodePath := []
    nodeCategory := C ⧸ A
    nodeAt := DerivationTree.categoryAt?_root localTree
    categoryPath := true :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_rdiv_true, horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_rdiv_true, horiginCat, horiginPos] using hslash)⟩
  }
  have hedge : TraceEdge oLeft oOut :=
    Or.inl (Or.inl (LocalTraceEdge.crossedLeft_A rfl rfl rfl rfl))
  simpa [oLeft, oOut] using
    F.mem_dedupCategoryTargetsAt_of_lifted_traceEdge ctx hR
      (by simpa [oLeft] using horiginNode)
      (by simpa [oLeft] using horiginCat)
      (by simpa [oLeft] using horiginPos)
      hedge

/-- In contextual backward crossed composition, replacing the output `A` copy
forces the matching left-premise `A` copy to be replaced. -/
theorem crossedLeft_output_A_copy_target_to_left_at
    {Γ Δ Ω : List Category} {B A C Z : Category}
    {t₁ : DerivationTree Γ (B ⧸ A)} {t₂ : DerivationTree Δ (B ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) (C ⧸ A) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedLeft))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget : (true :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix) :
    (true :: p, #F.atomName) ∈
      F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left]) := by
  let localTree := DerivationTree.binary t₁ t₂ Rule.crossedLeft
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff ctx.nodePrefix
      (true :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = true :: p := (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? ctx.nodePrefix = some (C ⧸ A) :=
    by simpa using ctx.categoryAt?_local (DerivationTree.categoryAt?_root localTree)
  have hRcat : R.nodeCategory = C ⧸ A := by
    have hnodeAtR : (ctx.plug localTree).categoryAt? R.nodePath = some (C ⧸ A) := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = true :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = C ⧸ A := by
    rw [← R.cat_eq]
    exact hRcat
  let oOut : Occurrence localTree := {
    nodePath := []
    nodeCategory := C ⧸ A
    nodeAt := DerivationTree.categoryAt?_root localTree
    categoryPath := true :: p
    isConstructor := by simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oLeft : Occurrence localTree := {
    nodePath := [.left]
    nodeCategory := B ⧸ A
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := true :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_rdiv_true, horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_rdiv_true, horiginCat, horiginPos] using hslash)⟩
  }
  have hedge : TraceEdge oOut oLeft :=
    Or.inr (Or.inl (LocalTraceEdge.crossedLeft_A rfl rfl rfl rfl))
  simpa [oOut, oLeft] using
    F.mem_dedupCategoryTargetsAt_of_lifted_traceEdge ctx hR
      (by simpa [oOut] using horiginNode)
      (by simpa [oOut] using horiginCat)
      (by simpa [oOut] using horiginPos)
      hedge

/-- In contextual backward crossed composition, replacing the right-premise `C`
copy forces the matching output `C` copy to be replaced. -/
theorem crossedLeft_right_C_copy_target_to_output_at
    {Γ Δ Ω : List Category} {B A C Z : Category}
    {t₁ : DerivationTree Γ (B ⧸ A)} {t₂ : DerivationTree Δ (B ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) (C ⧸ A) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedLeft))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget :
      (true :: p, #F.atomName) ∈
        F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right])) :
    (false :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix := by
  let localTree := DerivationTree.binary t₁ t₂ Rule.crossedLeft
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
      (true :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = true :: p := (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? (ctx.nodePrefix ++ [.right]) = some (B ⧹ C) :=
    ctx.categoryAt?_local (by simp [localTree, DerivationTree.categoryAt?])
  have hRcat : R.nodeCategory = B ⧹ C := by
    have hnodeAtR : (ctx.plug localTree).categoryAt? R.nodePath = some (B ⧹ C) := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix ++ [.right] := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = true :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = B ⧹ C := by
    rw [← R.cat_eq]
    exact hRcat
  let oRight : Occurrence localTree := {
    nodePath := [.right]
    nodeCategory := B ⧹ C
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := true :: p
    isConstructor := by simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oOut : Occurrence localTree := {
    nodePath := []
    nodeCategory := C ⧸ A
    nodeAt := DerivationTree.categoryAt?_root localTree
    categoryPath := false :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_ldiv_true, Category.subcategoryAt?_rdiv_false,
            horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_ldiv_true, Category.subcategoryAt?_rdiv_false,
            horiginCat, horiginPos] using hslash)⟩
  }
  have hedge : TraceEdge oRight oOut :=
    Or.inl (Or.inl (LocalTraceEdge.crossedLeft_C rfl rfl rfl rfl))
  simpa [oRight, oOut] using
    F.mem_dedupCategoryTargetsAt_of_lifted_traceEdge ctx hR
      (by simpa [oRight] using horiginNode)
      (by simpa [oRight] using horiginCat)
      (by simpa [oRight] using horiginPos)
      hedge

/-- In contextual backward crossed composition, replacing the output `C` copy
forces the matching right-premise `C` copy to be replaced. -/
theorem crossedLeft_output_C_copy_target_to_right_at
    {Γ Δ Ω : List Category} {B A C Z : Category}
    {t₁ : DerivationTree Γ (B ⧸ A)} {t₂ : DerivationTree Δ (B ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) (C ⧸ A) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedLeft))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget : (false :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix) :
    (true :: p, #F.atomName) ∈
      F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right]) := by
  let localTree := DerivationTree.binary t₁ t₂ Rule.crossedLeft
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff ctx.nodePrefix
      (false :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = false :: p := (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? ctx.nodePrefix = some (C ⧸ A) :=
    by simpa using ctx.categoryAt?_local (DerivationTree.categoryAt?_root localTree)
  have hRcat : R.nodeCategory = C ⧸ A := by
    have hnodeAtR : (ctx.plug localTree).categoryAt? R.nodePath = some (C ⧸ A) := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = false :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = C ⧸ A := by
    rw [← R.cat_eq]
    exact hRcat
  let oOut : Occurrence localTree := {
    nodePath := []
    nodeCategory := C ⧸ A
    nodeAt := DerivationTree.categoryAt?_root localTree
    categoryPath := false :: p
    isConstructor := by simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oRight : Occurrence localTree := {
    nodePath := [.right]
    nodeCategory := B ⧹ C
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := true :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_rdiv_false, Category.subcategoryAt?_ldiv_true,
            horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_rdiv_false, Category.subcategoryAt?_ldiv_true,
            horiginCat, horiginPos] using hslash)⟩
  }
  have hedge : TraceEdge oOut oRight :=
    Or.inr (Or.inl (LocalTraceEdge.crossedLeft_C rfl rfl rfl rfl))
  simpa [oOut, oRight] using
    F.mem_dedupCategoryTargetsAt_of_lifted_traceEdge ctx hR
      (by simpa [oOut] using horiginNode)
      (by simpa [oOut] using horiginCat)
      (by simpa [oOut] using horiginPos)
      hedge

/-- Path-only synchronization between the two `B` copies in contextual backward
crossed composition. -/
theorem crossedLeft_left_false_path_iff_right_false_path_at
    {Γ Δ Ω : List Category} {B A C Z : Category}
    {t₁ : DerivationTree Γ (B ⧸ A)} {t₂ : DerivationTree Δ (B ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) (C ⧸ A) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedLeft))}
    (F : PieceReplacementFamilyCore P) (p : CategoryPath) :
    false :: p ∈ F.categoryTargetPathsAt (ctx.nodePrefix ++ [.left]) ↔
      false :: p ∈ F.categoryTargetPathsAt (ctx.nodePrefix ++ [.right]) := by
  constructor
  · intro hp
    have htarget :
        (false :: p, #F.atomName) ∈
          F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left]) :=
      (F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
        (false :: p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hright := F.crossedLeft_left_B_copy_target_to_right_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
      (false :: p, #F.atomName)).mp hright).1
  · intro hp
    have htarget :
        (false :: p, #F.atomName) ∈
          F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right]) :=
      (F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
        (false :: p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hleft := F.crossedLeft_right_B_copy_target_to_left_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
      (false :: p, #F.atomName)).mp hleft).1

/-- Path-only synchronization between the left-premise and output `A` copies in
contextual backward crossed composition. -/
theorem crossedLeft_left_true_path_iff_output_true_path_at
    {Γ Δ Ω : List Category} {B A C Z : Category}
    {t₁ : DerivationTree Γ (B ⧸ A)} {t₂ : DerivationTree Δ (B ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) (C ⧸ A) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedLeft))}
    (F : PieceReplacementFamilyCore P) (p : CategoryPath) :
    true :: p ∈ F.categoryTargetPathsAt (ctx.nodePrefix ++ [.left]) ↔
      true :: p ∈ F.categoryTargetPathsAt ctx.nodePrefix := by
  constructor
  · intro hp
    have htarget :
        (true :: p, #F.atomName) ∈
          F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.left]) :=
      (F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
        (true :: p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hout := F.crossedLeft_left_A_copy_target_to_output_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
      (true :: p, #F.atomName)).mp hout).1
  · intro hp
    have htarget :
        (true :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix :=
      (F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
        (true :: p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hleft := F.crossedLeft_output_A_copy_target_to_left_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.left])
      (true :: p, #F.atomName)).mp hleft).1

/-- Path-only synchronization between the right-premise and output `C` copies in
contextual backward crossed composition. -/
theorem crossedLeft_right_true_path_iff_output_false_path_at
    {Γ Δ Ω : List Category} {B A C Z : Category}
    {t₁ : DerivationTree Γ (B ⧸ A)} {t₂ : DerivationTree Δ (B ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) (C ⧸ A) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedLeft))}
    (F : PieceReplacementFamilyCore P) (p : CategoryPath) :
    true :: p ∈ F.categoryTargetPathsAt (ctx.nodePrefix ++ [.right]) ↔
      false :: p ∈ F.categoryTargetPathsAt ctx.nodePrefix := by
  constructor
  · intro hp
    have htarget :
        (true :: p, #F.atomName) ∈
          F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.right]) :=
      (F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
        (true :: p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hout := F.crossedLeft_right_C_copy_target_to_output_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
      (false :: p, #F.atomName)).mp hout).1
  · intro hp
    have htarget :
        (false :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix :=
      (F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
        (false :: p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hright := F.crossedLeft_output_C_copy_target_to_right_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.right])
      (true :: p, #F.atomName)).mp hright).1

/-- Context-parametric backward crossed-composition preservation for canonical
node-local rewriting. -/
theorem rewrite_preserves_crossedLeft_at
    {Γ Δ Ω : List Category} {B A C Z : Category}
    {t₁ : DerivationTree Γ (B ⧸ A)}
    {t₂ : DerivationTree Δ (B ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) (C ⧸ A) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedLeft))}
    (F : PieceReplacementFamilyCore P)
    {L' R' O' : Category}
    (hL :
      F.rewriteNodeCategorySimul? (ctx.nodePrefix ++ [.left]) (B ⧸ A) = some L')
    (hR :
      F.rewriteNodeCategorySimul? (ctx.nodePrefix ++ [.right]) (B ⧹ C) = some R')
    (hO :
      F.rewriteNodeCategorySimul? ctx.nodePrefix (C ⧸ A) = some O') :
    Rule L' R' O' := by
  unfold rewriteNodeCategorySimul? at hL hR hO
  exact Category.replaceSimulAtPaths?_crossedLeft_components
    (F.crossedLeft_left_root_path_not_target_at ctx)
    (F.crossedLeft_right_root_path_not_target_at ctx)
    (F.crossedLeft_output_root_path_not_target_at ctx)
    (F.crossedLeft_left_false_path_iff_right_false_path_at ctx)
    (F.crossedLeft_left_true_path_iff_output_true_path_at ctx)
    (F.crossedLeft_right_true_path_iff_output_false_path_at ctx)
    hL
    hR
    hO

/-- In contextual forward type raising, replacing the child `A` copy forces
the matching output `A` copy to be replaced. -/
theorem typeRaiseRight_child_copy_target_to_output_at
    {Γ Ω : List Category} {A C Z : Category} {t : DerivationTree Γ A}
    (ctx : DerivationContext Γ (C ⧸ (A ⧹ C)) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.typeRaiseRight C t))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget : (p, #F.atomName) ∈ F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.unary])) :
    (true :: false :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix := by
  let localTree := DerivationTree.typeRaiseRight C t
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff (ctx.nodePrefix ++ [.unary])
      (p, #F.atomName)).mp hprojected
  have hRpos : R.pos = p := (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? (ctx.nodePrefix ++ [.unary]) = some A :=
    ctx.categoryAt?_local (by simp [localTree, DerivationTree.categoryAt?])
  have hRcat : R.nodeCategory = A := by
    have hnodeAtR : (ctx.plug localTree).categoryAt? R.nodePath = some A := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix ++ [.unary] := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = A := by
    rw [← R.cat_eq]
    exact hRcat
  let oChild : Occurrence localTree := {
    nodePath := [.unary]
    nodeCategory := A
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := p
    isConstructor := by simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oOut : Occurrence localTree := {
    nodePath := []
    nodeCategory := C ⧸ (A ⧹ C)
    nodeAt := DerivationTree.categoryAt?_root localTree
    categoryPath := true :: false :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_rdiv_true, Category.subcategoryAt?_ldiv_false,
            horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_rdiv_true, Category.subcategoryAt?_ldiv_false,
            horiginCat, horiginPos] using hslash)⟩
  }
  have hedge : TraceEdge oChild oOut :=
    Or.inl (Or.inl (LocalTraceEdge.trRight_A rfl rfl rfl rfl))
  simpa [oChild, oOut] using
    F.mem_dedupCategoryTargetsAt_of_lifted_traceEdge ctx hR
      (by simpa [oChild] using horiginNode)
      (by simpa [oChild] using horiginCat)
      (by simpa [oChild] using horiginPos)
      hedge

/-- In contextual forward type raising, replacing the output `A` copy forces
the matching child `A` copy to be replaced. -/
theorem typeRaiseRight_output_A_copy_target_to_child_at
    {Γ Ω : List Category} {A C Z : Category} {t : DerivationTree Γ A}
    (ctx : DerivationContext Γ (C ⧸ (A ⧹ C)) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.typeRaiseRight C t))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget :
      (true :: false :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix) :
    (p, #F.atomName) ∈ F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.unary]) := by
  let localTree := DerivationTree.typeRaiseRight C t
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff ctx.nodePrefix
      (true :: false :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = true :: false :: p := (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? ctx.nodePrefix = some (C ⧸ (A ⧹ C)) :=
    by simpa using ctx.categoryAt?_local (DerivationTree.categoryAt?_root localTree)
  have hRcat : R.nodeCategory = C ⧸ (A ⧹ C) := by
    have hnodeAtR :
        (ctx.plug localTree).categoryAt? R.nodePath = some (C ⧸ (A ⧹ C)) := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = true :: false :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = C ⧸ (A ⧹ C) := by
    rw [← R.cat_eq]
    exact hRcat
  let oOut : Occurrence localTree := {
    nodePath := []
    nodeCategory := C ⧸ (A ⧹ C)
    nodeAt := DerivationTree.categoryAt?_root localTree
    categoryPath := true :: false :: p
    isConstructor := by simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oChild : Occurrence localTree := {
    nodePath := [.unary]
    nodeCategory := A
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_rdiv_true, Category.subcategoryAt?_ldiv_false,
            horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_rdiv_true, Category.subcategoryAt?_ldiv_false,
            horiginCat, horiginPos] using hslash)⟩
  }
  have hedge : TraceEdge oOut oChild :=
    Or.inr (Or.inl (LocalTraceEdge.trRight_A rfl rfl rfl rfl))
  simpa [oChild, oOut] using
    F.mem_dedupCategoryTargetsAt_of_lifted_traceEdge ctx hR
      (by simpa [oOut] using horiginNode)
      (by simpa [oOut] using horiginCat)
      (by simpa [oOut] using horiginPos)
      hedge

/-- In contextual forward type raising, replacing the left `C` copy forces the
right `C` copy to be replaced. -/
theorem typeRaiseRight_left_C_copy_target_to_right_C_at
    {Γ Ω : List Category} {A C Z : Category} {t : DerivationTree Γ A}
    (ctx : DerivationContext Γ (C ⧸ (A ⧹ C)) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.typeRaiseRight C t))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget : (false :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix) :
    (true :: true :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix := by
  let localTree := DerivationTree.typeRaiseRight C t
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff ctx.nodePrefix
      (false :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = false :: p := (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? ctx.nodePrefix = some (C ⧸ (A ⧹ C)) :=
    by simpa using ctx.categoryAt?_local (DerivationTree.categoryAt?_root localTree)
  have hRcat : R.nodeCategory = C ⧸ (A ⧹ C) := by
    have hnodeAtR :
        (ctx.plug localTree).categoryAt? R.nodePath = some (C ⧸ (A ⧹ C)) := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = false :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = C ⧸ (A ⧹ C) := by
    rw [← R.cat_eq]
    exact hRcat
  let oLeft : Occurrence localTree := {
    nodePath := []
    nodeCategory := C ⧸ (A ⧹ C)
    nodeAt := DerivationTree.categoryAt?_root localTree
    categoryPath := false :: p
    isConstructor := by simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oRight : Occurrence localTree := {
    nodePath := []
    nodeCategory := C ⧸ (A ⧹ C)
    nodeAt := DerivationTree.categoryAt?_root localTree
    categoryPath := true :: true :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_rdiv_false, Category.subcategoryAt?_rdiv_true,
            Category.subcategoryAt?_ldiv_true, horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_rdiv_false, Category.subcategoryAt?_rdiv_true,
            Category.subcategoryAt?_ldiv_true, horiginCat, horiginPos] using hslash)⟩
  }
  have hedge : TraceEdge oLeft oRight :=
    Or.inl (Or.inl (LocalTraceEdge.trRight_C rfl rfl rfl rfl))
  simpa [oLeft, oRight] using
    F.mem_dedupCategoryTargetsAt_of_lifted_traceEdge ctx hR
      (by simpa [oLeft] using horiginNode)
      (by simpa [oLeft] using horiginCat)
      (by simpa [oLeft] using horiginPos)
      hedge

/-- In contextual forward type raising, replacing the right `C` copy forces the
left `C` copy to be replaced. -/
theorem typeRaiseRight_right_C_copy_target_to_left_C_at
    {Γ Ω : List Category} {A C Z : Category} {t : DerivationTree Γ A}
    (ctx : DerivationContext Γ (C ⧸ (A ⧹ C)) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.typeRaiseRight C t))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget :
      (true :: true :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix) :
    (false :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix := by
  let localTree := DerivationTree.typeRaiseRight C t
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff ctx.nodePrefix
      (true :: true :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = true :: true :: p := (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? ctx.nodePrefix = some (C ⧸ (A ⧹ C)) :=
    by simpa using ctx.categoryAt?_local (DerivationTree.categoryAt?_root localTree)
  have hRcat : R.nodeCategory = C ⧸ (A ⧹ C) := by
    have hnodeAtR :
        (ctx.plug localTree).categoryAt? R.nodePath = some (C ⧸ (A ⧹ C)) := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = true :: true :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = C ⧸ (A ⧹ C) := by
    rw [← R.cat_eq]
    exact hRcat
  let oRight : Occurrence localTree := {
    nodePath := []
    nodeCategory := C ⧸ (A ⧹ C)
    nodeAt := DerivationTree.categoryAt?_root localTree
    categoryPath := true :: true :: p
    isConstructor := by simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oLeft : Occurrence localTree := {
    nodePath := []
    nodeCategory := C ⧸ (A ⧹ C)
    nodeAt := DerivationTree.categoryAt?_root localTree
    categoryPath := false :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_rdiv_false, Category.subcategoryAt?_rdiv_true,
            Category.subcategoryAt?_ldiv_true, horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_rdiv_false, Category.subcategoryAt?_rdiv_true,
            Category.subcategoryAt?_ldiv_true, horiginCat, horiginPos] using hslash)⟩
  }
  have hedge : TraceEdge oRight oLeft :=
    Or.inr (Or.inl (LocalTraceEdge.trRight_C rfl rfl rfl rfl))
  simpa [oLeft, oRight] using
    F.mem_dedupCategoryTargetsAt_of_lifted_traceEdge ctx hR
      (by simpa [oRight] using horiginNode)
      (by simpa [oRight] using horiginCat)
      (by simpa [oRight] using horiginPos)
      hedge

/-- Path-only synchronization between the child `A` and output `A` copies in
contextual forward type raising. -/
theorem typeRaiseRight_output_A_path_iff_child_path_at
    {Γ Ω : List Category} {A C Z : Category} {t : DerivationTree Γ A}
    (ctx : DerivationContext Γ (C ⧸ (A ⧹ C)) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.typeRaiseRight C t))}
    (F : PieceReplacementFamilyCore P) (p : CategoryPath) :
    true :: false :: p ∈ F.categoryTargetPathsAt ctx.nodePrefix ↔
      p ∈ F.categoryTargetPathsAt (ctx.nodePrefix ++ [.unary]) := by
  constructor
  · intro hp
    have htarget :
        (true :: false :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix :=
      (F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
        (true :: false :: p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hchild := F.typeRaiseRight_output_A_copy_target_to_child_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.unary])
      (p, #F.atomName)).mp hchild).1
  · intro hp
    have htarget :
        (p, #F.atomName) ∈ F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.unary]) :=
      (F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.unary])
        (p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hout := F.typeRaiseRight_child_copy_target_to_output_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
      (true :: false :: p, #F.atomName)).mp hout).1

/-- Path-only synchronization between the two output `C` copies in contextual
forward type raising. -/
theorem typeRaiseRight_left_C_path_iff_right_C_path_at
    {Γ Ω : List Category} {A C Z : Category} {t : DerivationTree Γ A}
    (ctx : DerivationContext Γ (C ⧸ (A ⧹ C)) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.typeRaiseRight C t))}
    (F : PieceReplacementFamilyCore P) (p : CategoryPath) :
    false :: p ∈ F.categoryTargetPathsAt ctx.nodePrefix ↔
      true :: true :: p ∈ F.categoryTargetPathsAt ctx.nodePrefix := by
  constructor
  · intro hp
    have htarget :
        (false :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix :=
      (F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
        (false :: p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hright := F.typeRaiseRight_left_C_copy_target_to_right_C_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
      (true :: true :: p, #F.atomName)).mp hright).1
  · intro hp
    have htarget :
        (true :: true :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix :=
      (F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
        (true :: true :: p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hleft := F.typeRaiseRight_right_C_copy_target_to_left_C_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
      (false :: p, #F.atomName)).mp hleft).1

/-- Protected-skeleton-free contextual preservation for forward type raising. -/
theorem rewrite_preserves_typeRaiseRight_at_of_protectedSkeletonFree
    {Γ Ω : List Category} {A C Z : Category} {t : DerivationTree Γ A}
    (ctx : DerivationContext Γ (C ⧸ (A ⧹ C)) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.typeRaiseRight C t))}
    (F : PieceReplacementFamilyCore P)
    (hsafe : P.ProtectedSkeletonFree)
    {A' O' : Category}
    (hChild :
      F.rewriteNodeCategorySimul? (ctx.nodePrefix ++ [.unary]) A = some A')
    (hOut :
      F.rewriteNodeCategorySimul? ctx.nodePrefix (C ⧸ (A ⧹ C)) = some O') :
    ∃ C', O' = C' ⧸ (A' ⧹ C') := by
  unfold rewriteNodeCategorySimul? at hChild hOut
  exact Category.replaceSimulAtPaths?_typeRaiseRight_shape
    (F.typeRaiseRight_outer_path_not_target_at_of_protectedSkeletonFree ctx hsafe)
    (F.typeRaiseRight_inner_path_not_target_at_of_protectedSkeletonFree ctx hsafe)
    (F.typeRaiseRight_output_A_path_iff_child_path_at ctx)
    (F.typeRaiseRight_left_C_path_iff_right_C_path_at ctx)
    hChild
    hOut

/-- In contextual backward type raising, replacing the child `A` copy forces
the matching output `A` copy to be replaced. -/
theorem typeRaiseLeft_child_copy_target_to_output_at
    {Γ Ω : List Category} {A C Z : Category} {t : DerivationTree Γ A}
    (ctx : DerivationContext Γ ((C ⧸ A) ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.typeRaiseLeft C t))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget : (p, #F.atomName) ∈ F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.unary])) :
    (false :: true :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix := by
  let localTree := DerivationTree.typeRaiseLeft C t
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff (ctx.nodePrefix ++ [.unary])
      (p, #F.atomName)).mp hprojected
  have hRpos : R.pos = p := (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? (ctx.nodePrefix ++ [.unary]) = some A :=
    ctx.categoryAt?_local (by simp [localTree, DerivationTree.categoryAt?])
  have hRcat : R.nodeCategory = A := by
    have hnodeAtR : (ctx.plug localTree).categoryAt? R.nodePath = some A := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix ++ [.unary] := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = A := by
    rw [← R.cat_eq]
    exact hRcat
  let oChild : Occurrence localTree := {
    nodePath := [.unary]
    nodeCategory := A
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := p
    isConstructor := by simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oOut : Occurrence localTree := {
    nodePath := []
    nodeCategory := (C ⧸ A) ⧹ C
    nodeAt := DerivationTree.categoryAt?_root localTree
    categoryPath := false :: true :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_ldiv_false, Category.subcategoryAt?_rdiv_true,
            horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_ldiv_false, Category.subcategoryAt?_rdiv_true,
            horiginCat, horiginPos] using hslash)⟩
  }
  have hedge : TraceEdge oChild oOut :=
    Or.inl (Or.inl (LocalTraceEdge.trLeft_A rfl rfl rfl rfl))
  simpa [oChild, oOut] using
    F.mem_dedupCategoryTargetsAt_of_lifted_traceEdge ctx hR
      (by simpa [oChild] using horiginNode)
      (by simpa [oChild] using horiginCat)
      (by simpa [oChild] using horiginPos)
      hedge

/-- In contextual backward type raising, replacing the output `A` copy forces
the matching child `A` copy to be replaced. -/
theorem typeRaiseLeft_output_A_copy_target_to_child_at
    {Γ Ω : List Category} {A C Z : Category} {t : DerivationTree Γ A}
    (ctx : DerivationContext Γ ((C ⧸ A) ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.typeRaiseLeft C t))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget :
      (false :: true :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix) :
    (p, #F.atomName) ∈ F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.unary]) := by
  let localTree := DerivationTree.typeRaiseLeft C t
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff ctx.nodePrefix
      (false :: true :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = false :: true :: p := (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? ctx.nodePrefix = some ((C ⧸ A) ⧹ C) :=
    by simpa using ctx.categoryAt?_local (DerivationTree.categoryAt?_root localTree)
  have hRcat : R.nodeCategory = (C ⧸ A) ⧹ C := by
    have hnodeAtR :
        (ctx.plug localTree).categoryAt? R.nodePath = some ((C ⧸ A) ⧹ C) := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = false :: true :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = (C ⧸ A) ⧹ C := by
    rw [← R.cat_eq]
    exact hRcat
  let oOut : Occurrence localTree := {
    nodePath := []
    nodeCategory := (C ⧸ A) ⧹ C
    nodeAt := DerivationTree.categoryAt?_root localTree
    categoryPath := false :: true :: p
    isConstructor := by simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oChild : Occurrence localTree := {
    nodePath := [.unary]
    nodeCategory := A
    nodeAt := by simp [localTree, DerivationTree.categoryAt?]
    categoryPath := p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_ldiv_false, Category.subcategoryAt?_rdiv_true,
            horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_ldiv_false, Category.subcategoryAt?_rdiv_true,
            horiginCat, horiginPos] using hslash)⟩
  }
  have hedge : TraceEdge oOut oChild :=
    Or.inr (Or.inl (LocalTraceEdge.trLeft_A rfl rfl rfl rfl))
  simpa [oChild, oOut] using
    F.mem_dedupCategoryTargetsAt_of_lifted_traceEdge ctx hR
      (by simpa [oOut] using horiginNode)
      (by simpa [oOut] using horiginCat)
      (by simpa [oOut] using horiginPos)
      hedge

/-- In contextual backward type raising, replacing the left `C` copy forces the
right `C` copy to be replaced. -/
theorem typeRaiseLeft_left_C_copy_target_to_right_C_at
    {Γ Ω : List Category} {A C Z : Category} {t : DerivationTree Γ A}
    (ctx : DerivationContext Γ ((C ⧸ A) ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.typeRaiseLeft C t))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget :
      (false :: false :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix) :
    (true :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix := by
  let localTree := DerivationTree.typeRaiseLeft C t
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff ctx.nodePrefix
      (false :: false :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = false :: false :: p := (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? ctx.nodePrefix = some ((C ⧸ A) ⧹ C) :=
    by simpa using ctx.categoryAt?_local (DerivationTree.categoryAt?_root localTree)
  have hRcat : R.nodeCategory = (C ⧸ A) ⧹ C := by
    have hnodeAtR :
        (ctx.plug localTree).categoryAt? R.nodePath = some ((C ⧸ A) ⧹ C) := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = false :: false :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = (C ⧸ A) ⧹ C := by
    rw [← R.cat_eq]
    exact hRcat
  let oLeft : Occurrence localTree := {
    nodePath := []
    nodeCategory := (C ⧸ A) ⧹ C
    nodeAt := DerivationTree.categoryAt?_root localTree
    categoryPath := false :: false :: p
    isConstructor := by simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oRight : Occurrence localTree := {
    nodePath := []
    nodeCategory := (C ⧸ A) ⧹ C
    nodeAt := DerivationTree.categoryAt?_root localTree
    categoryPath := true :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_ldiv_false, Category.subcategoryAt?_rdiv_false,
            Category.subcategoryAt?_ldiv_true, horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_ldiv_false, Category.subcategoryAt?_rdiv_false,
            Category.subcategoryAt?_ldiv_true, horiginCat, horiginPos] using hslash)⟩
  }
  have hedge : TraceEdge oLeft oRight :=
    Or.inl (Or.inl (LocalTraceEdge.trLeft_C rfl rfl rfl rfl))
  simpa [oLeft, oRight] using
    F.mem_dedupCategoryTargetsAt_of_lifted_traceEdge ctx hR
      (by simpa [oLeft] using horiginNode)
      (by simpa [oLeft] using horiginCat)
      (by simpa [oLeft] using horiginPos)
      hedge

/-- In contextual backward type raising, replacing the right `C` copy forces
the left `C` copy to be replaced. -/
theorem typeRaiseLeft_right_C_copy_target_to_left_C_at
    {Γ Ω : List Category} {A C Z : Category} {t : DerivationTree Γ A}
    (ctx : DerivationContext Γ ((C ⧸ A) ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.typeRaiseLeft C t))}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget : (true :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix) :
    (false :: false :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix := by
  let localTree := DerivationTree.typeRaiseLeft C t
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff ctx.nodePrefix
      (true :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = true :: p := (congrArg Prod.fst htargetEq).symm
  have hnodeAt :
      (ctx.plug localTree).categoryAt? ctx.nodePrefix = some ((C ⧸ A) ⧹ C) :=
    by simpa using ctx.categoryAt?_local (DerivationTree.categoryAt?_root localTree)
  have hRcat : R.nodeCategory = (C ⧸ A) ⧹ C := by
    have hnodeAtR :
        (ctx.plug localTree).categoryAt? R.nodePath = some ((C ⧸ A) ⧹ C) := by
      simpa [hRnode] using hnodeAt
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAtR)
  have horiginNode : R.origin.nodePath = ctx.nodePrefix := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = true :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = (C ⧸ A) ⧹ C := by
    rw [← R.cat_eq]
    exact hRcat
  let oRight : Occurrence localTree := {
    nodePath := []
    nodeCategory := (C ⧸ A) ⧹ C
    nodeAt := DerivationTree.categoryAt?_root localTree
    categoryPath := true :: p
    isConstructor := by simpa [horiginCat, horiginPos] using R.origin.isConstructor
  }
  let oLeft : Occurrence localTree := {
    nodePath := []
    nodeCategory := (C ⧸ A) ⧹ C
    nodeAt := DerivationTree.categoryAt?_root localTree
    categoryPath := false :: false :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_ldiv_false, Category.subcategoryAt?_rdiv_false,
            Category.subcategoryAt?_ldiv_true, horiginCat, horiginPos] using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_ldiv_false, Category.subcategoryAt?_rdiv_false,
            Category.subcategoryAt?_ldiv_true, horiginCat, horiginPos] using hslash)⟩
  }
  have hedge : TraceEdge oRight oLeft :=
    Or.inr (Or.inl (LocalTraceEdge.trLeft_C rfl rfl rfl rfl))
  simpa [oLeft, oRight] using
    F.mem_dedupCategoryTargetsAt_of_lifted_traceEdge ctx hR
      (by simpa [oRight] using horiginNode)
      (by simpa [oRight] using horiginCat)
      (by simpa [oRight] using horiginPos)
      hedge

/-- Path-only synchronization between the child `A` and output `A` copies in
contextual backward type raising. -/
theorem typeRaiseLeft_output_A_path_iff_child_path_at
    {Γ Ω : List Category} {A C Z : Category} {t : DerivationTree Γ A}
    (ctx : DerivationContext Γ ((C ⧸ A) ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.typeRaiseLeft C t))}
    (F : PieceReplacementFamilyCore P) (p : CategoryPath) :
    false :: true :: p ∈ F.categoryTargetPathsAt ctx.nodePrefix ↔
      p ∈ F.categoryTargetPathsAt (ctx.nodePrefix ++ [.unary]) := by
  constructor
  · intro hp
    have htarget :
        (false :: true :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix :=
      (F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
        (false :: true :: p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hchild := F.typeRaiseLeft_output_A_copy_target_to_child_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.unary])
      (p, #F.atomName)).mp hchild).1
  · intro hp
    have htarget :
        (p, #F.atomName) ∈ F.dedupCategoryTargetsAt (ctx.nodePrefix ++ [.unary]) :=
      (F.mem_dedupCategoryTargetsAt_iff (ctx.nodePrefix ++ [.unary])
        (p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hout := F.typeRaiseLeft_child_copy_target_to_output_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
      (false :: true :: p, #F.atomName)).mp hout).1

/-- Path-only synchronization between the two output `C` copies in contextual
backward type raising. -/
theorem typeRaiseLeft_left_C_path_iff_right_C_path_at
    {Γ Ω : List Category} {A C Z : Category} {t : DerivationTree Γ A}
    (ctx : DerivationContext Γ ((C ⧸ A) ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.typeRaiseLeft C t))}
    (F : PieceReplacementFamilyCore P) (p : CategoryPath) :
    false :: false :: p ∈ F.categoryTargetPathsAt ctx.nodePrefix ↔
      true :: p ∈ F.categoryTargetPathsAt ctx.nodePrefix := by
  constructor
  · intro hp
    have htarget :
        (false :: false :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix :=
      (F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
        (false :: false :: p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hright := F.typeRaiseLeft_left_C_copy_target_to_right_C_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
      (true :: p, #F.atomName)).mp hright).1
  · intro hp
    have htarget :
        (true :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt ctx.nodePrefix :=
      (F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
        (true :: p, #F.atomName)).mpr ⟨hp, rfl⟩
    have hleft := F.typeRaiseLeft_right_C_copy_target_to_left_C_at ctx htarget
    exact ((F.mem_dedupCategoryTargetsAt_iff ctx.nodePrefix
      (false :: false :: p, #F.atomName)).mp hleft).1

/-- Protected-skeleton-free contextual preservation for backward type raising. -/
theorem rewrite_preserves_typeRaiseLeft_at_of_protectedSkeletonFree
    {Γ Ω : List Category} {A C Z : Category} {t : DerivationTree Γ A}
    (ctx : DerivationContext Γ ((C ⧸ A) ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.typeRaiseLeft C t))}
    (F : PieceReplacementFamilyCore P)
    (hsafe : P.ProtectedSkeletonFree)
    {A' O' : Category}
    (hChild :
      F.rewriteNodeCategorySimul? (ctx.nodePrefix ++ [.unary]) A = some A')
    (hOut :
      F.rewriteNodeCategorySimul? ctx.nodePrefix ((C ⧸ A) ⧹ C) = some O') :
    ∃ C', O' = (C' ⧸ A') ⧹ C' := by
  unfold rewriteNodeCategorySimul? at hChild hOut
  exact Category.replaceSimulAtPaths?_typeRaiseLeft_shape
    (F.typeRaiseLeft_outer_path_not_target_at_of_protectedSkeletonFree ctx hsafe)
    (F.typeRaiseLeft_inner_path_not_target_at_of_protectedSkeletonFree ctx hsafe)
    (F.typeRaiseLeft_output_A_path_iff_child_path_at ctx)
    (F.typeRaiseLeft_left_C_path_iff_right_C_path_at ctx)
    hChild
    hOut

/-- A partially rewritten subtree together with the node-local rewrite equation
for its root category.  This is the small sigma object used before implementing
the full recursive tree surgery. -/
structure RewrittenTree
    {Γ Ω : List Category} {A Z : Category} {localTree : DerivationTree Γ A}
    (ctx : DerivationContext Γ A Ω Z)
    {P : InvisiblePiece (ctx.plug localTree)}
    (F : PieceReplacementFamilyCore P) where
  root' : Category
  tree : DerivationTree Γ root'
  root_rewrite : F.rewriteNodeCategorySimul? ctx.nodePrefix A = some root'
  size_le : tree.size ≤ localTree.size
  size_lt_of_target :
    ∀ {R : PieceReplacementTarget P}, R ∈ F.targets →
      ∀ {p : NodePath}, R.nodePath = ctx.nodePrefix ++ p → tree.size < localTree.size
  atoms_preserved :
    (∀ B ∈ localTree.nodeCategories, ∀ name ∈ B.atoms, name ∈ problemAtomNames Ω Z) →
      ∀ B ∈ tree.nodeCategories, ∀ name ∈ B.atoms, name ∈ problemAtomNames Ω Z

namespace RewrittenTree

/-- Leaf nodes rewrite to themselves because replacement families are leaf-free. -/
def leaf
    {Ω : List Category} {A Z : Category}
    (ctx : DerivationContext [A] A Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.leaf A))}
    (F : PieceReplacementFamilyCore P)
    (hleaf : (ctx.plug (DerivationTree.leaf A)).isLeafNode ctx.nodePrefix) :
    RewrittenTree ctx F where
  root' := A
  tree := DerivationTree.leaf A
  root_rewrite := F.rewriteNodeCategorySimul?_leaf hleaf
  size_le := by simp
  size_lt_of_target := by
    intro R hR p hpath
    cases p with
    | nil =>
        have hleafR :
            (ctx.plug (DerivationTree.leaf A)).isLeafNode R.nodePath := by
          simpa [hpath] using hleaf
        exact False.elim ((F.leaf_free R hR) hleafR)
    | cons step rest =>
        have hfull :
            (ctx.plug (DerivationTree.leaf A)).categoryAt?
              (ctx.nodePrefix ++ (step :: rest)) = some R.nodeCategory := by
          simpa [hpath] using R.nodeAt
        have hlocal := ctx.categoryAt?_reflect hfull
        simp [DerivationTree.categoryAt?] at hlocal
  atoms_preserved := by
    intro hatoms B hB name hname
    exact hatoms B hB name hname

/-- Rebuild a protected-skeleton-free forward type-raising node from a rewritten
child. -/
theorem typeRaiseRight
    {Γ Ω : List Category} {A C Z : Category} {t : DerivationTree Γ A}
    (ctx : DerivationContext Γ (C ⧸ (A ⧹ C)) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.typeRaiseRight C t))}
    (F : PieceReplacementFamilyCore P)
    (hsafe : P.ProtectedSkeletonFree)
    (child : RewrittenTree (ctx.inTypeRaiseRight) F) :
    Nonempty (RewrittenTree ctx F) := by
  have hnode :
      (ctx.plug (DerivationTree.typeRaiseRight C t)).categoryAt?
        ctx.nodePrefix = some (C ⧸ (A ⧹ C)) := by
    simpa using ctx.categoryAt?_local
      (DerivationTree.categoryAt?_root (DerivationTree.typeRaiseRight C t))
  obtain ⟨O', hO⟩ := F.rewriteNodeCategorySimul?_success hnode
  obtain ⟨C', hshape⟩ :=
    F.rewrite_preserves_typeRaiseRight_at_of_protectedSkeletonFree
      ctx hsafe child.root_rewrite hO
  refine ⟨{
    root' := C' ⧸ (child.root' ⧹ C')
    tree := DerivationTree.typeRaiseRight C' child.tree
    root_rewrite := ?_
    size_le := ?_
    size_lt_of_target := ?_
    atoms_preserved := ?_
  }⟩
  · simpa [hshape] using hO
  · have hrootLe :
        (C' ⧸ (child.root' ⧹ C')).constructors ≤
          (C ⧸ (A ⧹ C)).constructors := by
      have hle := F.rewriteNodeCategorySimul?_constructors_le hnode hO
      simpa [hshape] using hle
    have hchildLe := child.size_le
    simp [DerivationTree.size_typeRaiseRight]
    omega
  · intro R hR p hpath
    cases p with
    | nil =>
        have hrootLt :
            (C' ⧸ (child.root' ⧹ C')).constructors <
              (C ⧸ (A ⧹ C)).constructors := by
          have hlt :=
            F.rewriteNodeCategorySimul?_constructors_lt_of_target
              hnode hO hR (by simpa [hpath])
          simpa [hshape] using hlt
        have hchildLe := child.size_le
        simp [DerivationTree.size_typeRaiseRight]
        omega
    | cons step rest =>
        cases step with
        | unary =>
            have hchildPath :
                R.nodePath = (ctx.nodePrefix ++ [.unary]) ++ rest := by
              simpa [List.append_assoc] using hpath
            have hchildLt := child.size_lt_of_target hR hchildPath
            have hrootLe :
                (C' ⧸ (child.root' ⧹ C')).constructors ≤
                  (C ⧸ (A ⧹ C)).constructors := by
              have hle := F.rewriteNodeCategorySimul?_constructors_le hnode hO
              simpa [hshape] using hle
            simp [DerivationTree.size_typeRaiseRight]
            omega
        | left =>
            have hfull :
                (ctx.plug (DerivationTree.typeRaiseRight C t)).categoryAt?
                  (ctx.nodePrefix ++ (TreeStep.left :: rest)) = some R.nodeCategory := by
              simpa [hpath] using R.nodeAt
            have hlocal := ctx.categoryAt?_reflect hfull
            simp [DerivationTree.categoryAt?] at hlocal
        | right =>
            have hfull :
                (ctx.plug (DerivationTree.typeRaiseRight C t)).categoryAt?
                  (ctx.nodePrefix ++ (TreeStep.right :: rest)) = some R.nodeCategory := by
              simpa [hpath] using R.nodeAt
            have hlocal := ctx.categoryAt?_reflect hfull
            simp [DerivationTree.categoryAt?] at hlocal
  · intro hatoms B hB name hname
    simp only [DerivationTree.nodeCategories_typeRaiseRight, List.mem_cons] at hB
    rcases hB with hB | hB
    · subst B
      have hrootAtoms :
          ∀ name ∈ (C' ⧸ (child.root' ⧹ C')).atoms,
            name ∈ problemAtomNames Ω Z := by
        have hhost :
            ∀ name ∈ (C ⧸ (A ⧹ C)).atoms,
              name ∈ problemAtomNames Ω Z := by
          intro name hname
          exact hatoms (C ⧸ (A ⧹ C))
            (by simp [DerivationTree.nodeCategories_typeRaiseRight]) name hname
        have hp := F.rewriteNodeCategorySimul?_atoms_preserved hO hhost
        simpa [hshape] using hp
      exact hrootAtoms name hname
    · exact child.atoms_preserved
        (by
          intro B hB name hname
          exact hatoms B
            (by simp [DerivationTree.nodeCategories_typeRaiseRight, hB]) name hname)
        B hB name hname

/-- Rebuild a protected-skeleton-free backward type-raising node from a
rewritten child. -/
theorem typeRaiseLeft
    {Γ Ω : List Category} {A C Z : Category} {t : DerivationTree Γ A}
    (ctx : DerivationContext Γ ((C ⧸ A) ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.typeRaiseLeft C t))}
    (F : PieceReplacementFamilyCore P)
    (hsafe : P.ProtectedSkeletonFree)
    (child : RewrittenTree (ctx.inTypeRaiseLeft) F) :
    Nonempty (RewrittenTree ctx F) := by
  have hnode :
      (ctx.plug (DerivationTree.typeRaiseLeft C t)).categoryAt?
        ctx.nodePrefix = some ((C ⧸ A) ⧹ C) := by
    simpa using ctx.categoryAt?_local
      (DerivationTree.categoryAt?_root (DerivationTree.typeRaiseLeft C t))
  obtain ⟨O', hO⟩ := F.rewriteNodeCategorySimul?_success hnode
  obtain ⟨C', hshape⟩ :=
    F.rewrite_preserves_typeRaiseLeft_at_of_protectedSkeletonFree
      ctx hsafe child.root_rewrite hO
  refine ⟨{
    root' := (C' ⧸ child.root') ⧹ C'
    tree := DerivationTree.typeRaiseLeft C' child.tree
    root_rewrite := ?_
    size_le := ?_
    size_lt_of_target := ?_
    atoms_preserved := ?_
  }⟩
  · simpa [hshape] using hO
  · have hrootLe :
        ((C' ⧸ child.root') ⧹ C').constructors ≤
          ((C ⧸ A) ⧹ C).constructors := by
      have hle := F.rewriteNodeCategorySimul?_constructors_le hnode hO
      simpa [hshape] using hle
    have hchildLe := child.size_le
    simp [DerivationTree.size_typeRaiseLeft]
    omega
  · intro R hR p hpath
    cases p with
    | nil =>
        have hrootLt :
            ((C' ⧸ child.root') ⧹ C').constructors <
              ((C ⧸ A) ⧹ C).constructors := by
          have hlt :=
            F.rewriteNodeCategorySimul?_constructors_lt_of_target
              hnode hO hR (by simpa [hpath])
          simpa [hshape] using hlt
        have hchildLe := child.size_le
        simp [DerivationTree.size_typeRaiseLeft]
        omega
    | cons step rest =>
        cases step with
        | unary =>
            have hchildPath :
                R.nodePath = (ctx.nodePrefix ++ [.unary]) ++ rest := by
              simpa [List.append_assoc] using hpath
            have hchildLt := child.size_lt_of_target hR hchildPath
            have hrootLe :
                ((C' ⧸ child.root') ⧹ C').constructors ≤
                  ((C ⧸ A) ⧹ C).constructors := by
              have hle := F.rewriteNodeCategorySimul?_constructors_le hnode hO
              simpa [hshape] using hle
            simp [DerivationTree.size_typeRaiseLeft]
            omega
        | left =>
            have hfull :
                (ctx.plug (DerivationTree.typeRaiseLeft C t)).categoryAt?
                  (ctx.nodePrefix ++ (TreeStep.left :: rest)) = some R.nodeCategory := by
              simpa [hpath] using R.nodeAt
            have hlocal := ctx.categoryAt?_reflect hfull
            simp [DerivationTree.categoryAt?] at hlocal
        | right =>
            have hfull :
                (ctx.plug (DerivationTree.typeRaiseLeft C t)).categoryAt?
                  (ctx.nodePrefix ++ (TreeStep.right :: rest)) = some R.nodeCategory := by
              simpa [hpath] using R.nodeAt
            have hlocal := ctx.categoryAt?_reflect hfull
            simp [DerivationTree.categoryAt?] at hlocal
  · intro hatoms B hB name hname
    simp only [DerivationTree.nodeCategories_typeRaiseLeft, List.mem_cons] at hB
    rcases hB with hB | hB
    · subst B
      have hrootAtoms :
          ∀ name ∈ ((C' ⧸ child.root') ⧹ C').atoms,
            name ∈ problemAtomNames Ω Z := by
        have hhost :
            ∀ name ∈ ((C ⧸ A) ⧹ C).atoms,
              name ∈ problemAtomNames Ω Z := by
          intro name hname
          exact hatoms ((C ⧸ A) ⧹ C)
            (by simp [DerivationTree.nodeCategories_typeRaiseLeft]) name hname
        have hp := F.rewriteNodeCategorySimul?_atoms_preserved hO hhost
        simpa [hshape] using hp
      exact hrootAtoms name hname
    · exact child.atoms_preserved
        (by
          intro B hB name hname
          exact hatoms B
            (by simp [DerivationTree.nodeCategories_typeRaiseLeft, hB]) name hname)
        B hB name hname

/-- Rebuild a forward application node from rewritten premises. -/
theorem appRight
    {Γ Δ Ω : List Category} {C B Z : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ B}
    (ctx : DerivationContext (Γ ++ Δ) C Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.appRight))}
    (F : PieceReplacementFamilyCore P)
    (left : RewrittenTree (ctx.inBinaryLeft t₂ Rule.appRight) F)
    (right : RewrittenTree (ctx.inBinaryRight t₁ Rule.appRight) F) :
    Nonempty (RewrittenTree ctx F) := by
  have hnode :
      (ctx.plug (DerivationTree.binary t₁ t₂ Rule.appRight)).categoryAt?
        ctx.nodePrefix = some C := by
    simpa using ctx.categoryAt?_local
      (DerivationTree.categoryAt?_root
        (DerivationTree.binary t₁ t₂ Rule.appRight))
  obtain ⟨O', hO⟩ := F.rewriteNodeCategorySimul?_success hnode
  let r : Rule left.root' right.root' O' :=
    F.rewrite_preserves_appRight_at ctx
      left.root_rewrite right.root_rewrite hO
  exact ⟨{
    root' := O'
    tree := DerivationTree.binary left.tree right.tree r
    root_rewrite := hO
    size_le := by
      have hrootLe := F.rewriteNodeCategorySimul?_constructors_le hnode hO
      have hleftLe := left.size_le
      have hrightLe := right.size_le
      simp [DerivationTree.size_binary]
      omega
    size_lt_of_target := by
      intro R hR p hpath
      cases p with
      | nil =>
          have hrootLt :=
            F.rewriteNodeCategorySimul?_constructors_lt_of_target
              hnode hO hR (by simpa [hpath])
          have hleftLe := left.size_le
          have hrightLe := right.size_le
          simp [DerivationTree.size_binary]
          omega
      | cons step rest =>
          cases step with
          | unary =>
              have hlocal := ctx.categoryAt?_reflect
                (p := TreeStep.unary :: rest) (by simpa [hpath] using R.nodeAt)
              simp [DerivationTree.categoryAt?] at hlocal
          | left =>
              have hleftPath :
                  R.nodePath = (ctx.nodePrefix ++ [.left]) ++ rest := by
                simpa [List.append_assoc] using hpath
              have hleftLt := left.size_lt_of_target hR hleftPath
              have hrootLe := F.rewriteNodeCategorySimul?_constructors_le hnode hO
              have hrightLe := right.size_le
              simp [DerivationTree.size_binary]
              omega
          | right =>
              have hrightPath :
                  R.nodePath = (ctx.nodePrefix ++ [.right]) ++ rest := by
                simpa [List.append_assoc] using hpath
              have hrightLt := right.size_lt_of_target hR hrightPath
              have hrootLe := F.rewriteNodeCategorySimul?_constructors_le hnode hO
              have hleftLe := left.size_le
              simp [DerivationTree.size_binary]
              omega
    atoms_preserved := by
      intro hatoms B hB name hname
      simp only [DerivationTree.nodeCategories_binary, List.mem_cons,
        List.mem_append] at hB
      rcases hB with hB | hB | hB
      · subst B
        have hrootAtoms :
            ∀ name ∈ O'.atoms, name ∈ problemAtomNames Ω Z := by
          have hhost :
              ∀ name ∈ C.atoms, name ∈ problemAtomNames Ω Z := by
            intro name hname
            exact hatoms C
              (by simp [DerivationTree.nodeCategories_binary]) name hname
          exact F.rewriteNodeCategorySimul?_atoms_preserved hO hhost
        exact hrootAtoms name hname
      · exact left.atoms_preserved
          (by
            intro B hB name hname
            exact hatoms B
              (by simp [DerivationTree.nodeCategories_binary, hB]) name hname)
          B hB name hname
      · exact right.atoms_preserved
          (by
            intro B hB name hname
            exact hatoms B
              (by simp [DerivationTree.nodeCategories_binary, hB]) name hname)
          B hB name hname
  }⟩

/-- Rebuild a backward application node from rewritten premises. -/
theorem appLeft
    {Γ Δ Ω : List Category} {A C Z : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ (A ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) C Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.appLeft))}
    (F : PieceReplacementFamilyCore P)
    (left : RewrittenTree (ctx.inBinaryLeft t₂ Rule.appLeft) F)
    (right : RewrittenTree (ctx.inBinaryRight t₁ Rule.appLeft) F) :
    Nonempty (RewrittenTree ctx F) := by
  have hnode :
      (ctx.plug (DerivationTree.binary t₁ t₂ Rule.appLeft)).categoryAt?
        ctx.nodePrefix = some C := by
    simpa using ctx.categoryAt?_local
      (DerivationTree.categoryAt?_root
        (DerivationTree.binary t₁ t₂ Rule.appLeft))
  obtain ⟨O', hO⟩ := F.rewriteNodeCategorySimul?_success hnode
  let r : Rule left.root' right.root' O' :=
    F.rewrite_preserves_appLeft_at ctx
      left.root_rewrite right.root_rewrite hO
  exact ⟨{
    root' := O'
    tree := DerivationTree.binary left.tree right.tree r
    root_rewrite := hO
    size_le := by
      have hrootLe := F.rewriteNodeCategorySimul?_constructors_le hnode hO
      have hleftLe := left.size_le
      have hrightLe := right.size_le
      simp [DerivationTree.size_binary]
      omega
    size_lt_of_target := by
      intro R hR p hpath
      cases p with
      | nil =>
          have hrootLt :=
            F.rewriteNodeCategorySimul?_constructors_lt_of_target
              hnode hO hR (by simpa [hpath])
          have hleftLe := left.size_le
          have hrightLe := right.size_le
          simp [DerivationTree.size_binary]
          omega
      | cons step rest =>
          cases step with
          | unary =>
              have hlocal := ctx.categoryAt?_reflect
                (p := TreeStep.unary :: rest) (by simpa [hpath] using R.nodeAt)
              simp [DerivationTree.categoryAt?] at hlocal
          | left =>
              have hleftPath :
                  R.nodePath = (ctx.nodePrefix ++ [.left]) ++ rest := by
                simpa [List.append_assoc] using hpath
              have hleftLt := left.size_lt_of_target hR hleftPath
              have hrootLe := F.rewriteNodeCategorySimul?_constructors_le hnode hO
              have hrightLe := right.size_le
              simp [DerivationTree.size_binary]
              omega
          | right =>
              have hrightPath :
                  R.nodePath = (ctx.nodePrefix ++ [.right]) ++ rest := by
                simpa [List.append_assoc] using hpath
              have hrightLt := right.size_lt_of_target hR hrightPath
              have hrootLe := F.rewriteNodeCategorySimul?_constructors_le hnode hO
              have hleftLe := left.size_le
              simp [DerivationTree.size_binary]
              omega
    atoms_preserved := by
      intro hatoms B hB name hname
      simp only [DerivationTree.nodeCategories_binary, List.mem_cons,
        List.mem_append] at hB
      rcases hB with hB | hB | hB
      · subst B
        have hrootAtoms :
            ∀ name ∈ O'.atoms, name ∈ problemAtomNames Ω Z := by
          have hhost :
              ∀ name ∈ C.atoms, name ∈ problemAtomNames Ω Z := by
            intro name hname
            exact hatoms C
              (by simp [DerivationTree.nodeCategories_binary]) name hname
          exact F.rewriteNodeCategorySimul?_atoms_preserved hO hhost
        exact hrootAtoms name hname
      · exact left.atoms_preserved
          (by
            intro B hB name hname
            exact hatoms B
              (by simp [DerivationTree.nodeCategories_binary, hB]) name hname)
          B hB name hname
      · exact right.atoms_preserved
          (by
            intro B hB name hname
            exact hatoms B
              (by simp [DerivationTree.nodeCategories_binary, hB]) name hname)
          B hB name hname
  }⟩

/-- Rebuild a forward-composition node from rewritten premises. -/
theorem compRight
    {Γ Δ Ω : List Category} {C B A Z : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (B ⧸ A)}
    (ctx : DerivationContext (Γ ++ Δ) (C ⧸ A) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compRight))}
    (F : PieceReplacementFamilyCore P)
    (left : RewrittenTree (ctx.inBinaryLeft t₂ Rule.compRight) F)
    (right : RewrittenTree (ctx.inBinaryRight t₁ Rule.compRight) F) :
    Nonempty (RewrittenTree ctx F) := by
  have hnode :
      (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compRight)).categoryAt?
        ctx.nodePrefix = some (C ⧸ A) := by
    simpa using ctx.categoryAt?_local
      (DerivationTree.categoryAt?_root
        (DerivationTree.binary t₁ t₂ Rule.compRight))
  obtain ⟨O', hO⟩ := F.rewriteNodeCategorySimul?_success hnode
  let r : Rule left.root' right.root' O' :=
    F.rewrite_preserves_compRight_at ctx
      left.root_rewrite right.root_rewrite hO
  exact ⟨{
    root' := O'
    tree := DerivationTree.binary left.tree right.tree r
    root_rewrite := hO
    size_le := by
      have hrootLe := F.rewriteNodeCategorySimul?_constructors_le hnode hO
      have hleftLe := left.size_le
      have hrightLe := right.size_le
      simp [DerivationTree.size_binary]
      omega
    size_lt_of_target := by
      intro R hR p hpath
      cases p with
      | nil =>
          have hrootLt :=
            F.rewriteNodeCategorySimul?_constructors_lt_of_target
              hnode hO hR (by simpa [hpath])
          have hleftLe := left.size_le
          have hrightLe := right.size_le
          simp [DerivationTree.size_binary]
          omega
      | cons step rest =>
          cases step with
          | unary =>
              have hlocal := ctx.categoryAt?_reflect
                (p := TreeStep.unary :: rest) (by simpa [hpath] using R.nodeAt)
              simp [DerivationTree.categoryAt?] at hlocal
          | left =>
              have hleftPath :
                  R.nodePath = (ctx.nodePrefix ++ [.left]) ++ rest := by
                simpa [List.append_assoc] using hpath
              have hleftLt := left.size_lt_of_target hR hleftPath
              have hrootLe := F.rewriteNodeCategorySimul?_constructors_le hnode hO
              have hrightLe := right.size_le
              simp [DerivationTree.size_binary]
              omega
          | right =>
              have hrightPath :
                  R.nodePath = (ctx.nodePrefix ++ [.right]) ++ rest := by
                simpa [List.append_assoc] using hpath
              have hrightLt := right.size_lt_of_target hR hrightPath
              have hrootLe := F.rewriteNodeCategorySimul?_constructors_le hnode hO
              have hleftLe := left.size_le
              simp [DerivationTree.size_binary]
              omega
    atoms_preserved := by
      intro hatoms B₀ hB name hname
      simp only [DerivationTree.nodeCategories_binary, List.mem_cons,
        List.mem_append] at hB
      rcases hB with hB | hB | hB
      · subst B₀
        have hrootAtoms :
            ∀ name ∈ O'.atoms, name ∈ problemAtomNames Ω Z := by
          have hhost :
              ∀ name ∈ (C ⧸ A).atoms, name ∈ problemAtomNames Ω Z := by
            intro name hname
            exact hatoms (C ⧸ A)
              (by simp [DerivationTree.nodeCategories_binary]) name hname
          exact F.rewriteNodeCategorySimul?_atoms_preserved hO hhost
        exact hrootAtoms name hname
      · exact left.atoms_preserved
          (by
            intro B₀ hB name hname
            exact hatoms B₀
              (by simp [DerivationTree.nodeCategories_binary, hB]) name hname)
          B₀ hB name hname
      · exact right.atoms_preserved
          (by
            intro B₀ hB name hname
            exact hatoms B₀
              (by simp [DerivationTree.nodeCategories_binary, hB]) name hname)
          B₀ hB name hname
  }⟩

/-- Rebuild a backward-composition node from rewritten premises. -/
theorem compLeft
    {Γ Δ Ω : List Category} {A B C Z : Category}
    {t₁ : DerivationTree Γ (A ⧹ B)} {t₂ : DerivationTree Δ (B ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) (A ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compLeft))}
    (F : PieceReplacementFamilyCore P)
    (left : RewrittenTree (ctx.inBinaryLeft t₂ Rule.compLeft) F)
    (right : RewrittenTree (ctx.inBinaryRight t₁ Rule.compLeft) F) :
    Nonempty (RewrittenTree ctx F) := by
  have hnode :
      (ctx.plug (DerivationTree.binary t₁ t₂ Rule.compLeft)).categoryAt?
        ctx.nodePrefix = some (A ⧹ C) := by
    simpa using ctx.categoryAt?_local
      (DerivationTree.categoryAt?_root
        (DerivationTree.binary t₁ t₂ Rule.compLeft))
  obtain ⟨O', hO⟩ := F.rewriteNodeCategorySimul?_success hnode
  let r : Rule left.root' right.root' O' :=
    F.rewrite_preserves_compLeft_at ctx
      left.root_rewrite right.root_rewrite hO
  exact ⟨{
    root' := O'
    tree := DerivationTree.binary left.tree right.tree r
    root_rewrite := hO
    size_le := by
      have hrootLe := F.rewriteNodeCategorySimul?_constructors_le hnode hO
      have hleftLe := left.size_le
      have hrightLe := right.size_le
      simp [DerivationTree.size_binary]
      omega
    size_lt_of_target := by
      intro R hR p hpath
      cases p with
      | nil =>
          have hrootLt :=
            F.rewriteNodeCategorySimul?_constructors_lt_of_target
              hnode hO hR (by simpa [hpath])
          have hleftLe := left.size_le
          have hrightLe := right.size_le
          simp [DerivationTree.size_binary]
          omega
      | cons step rest =>
          cases step with
          | unary =>
              have hlocal := ctx.categoryAt?_reflect
                (p := TreeStep.unary :: rest) (by simpa [hpath] using R.nodeAt)
              simp [DerivationTree.categoryAt?] at hlocal
          | left =>
              have hleftPath :
                  R.nodePath = (ctx.nodePrefix ++ [.left]) ++ rest := by
                simpa [List.append_assoc] using hpath
              have hleftLt := left.size_lt_of_target hR hleftPath
              have hrootLe := F.rewriteNodeCategorySimul?_constructors_le hnode hO
              have hrightLe := right.size_le
              simp [DerivationTree.size_binary]
              omega
          | right =>
              have hrightPath :
                  R.nodePath = (ctx.nodePrefix ++ [.right]) ++ rest := by
                simpa [List.append_assoc] using hpath
              have hrightLt := right.size_lt_of_target hR hrightPath
              have hrootLe := F.rewriteNodeCategorySimul?_constructors_le hnode hO
              have hleftLe := left.size_le
              simp [DerivationTree.size_binary]
              omega
    atoms_preserved := by
      intro hatoms B₀ hB name hname
      simp only [DerivationTree.nodeCategories_binary, List.mem_cons,
        List.mem_append] at hB
      rcases hB with hB | hB | hB
      · subst B₀
        have hrootAtoms :
            ∀ name ∈ O'.atoms, name ∈ problemAtomNames Ω Z := by
          have hhost :
              ∀ name ∈ (A ⧹ C).atoms, name ∈ problemAtomNames Ω Z := by
            intro name hname
            exact hatoms (A ⧹ C)
              (by simp [DerivationTree.nodeCategories_binary]) name hname
          exact F.rewriteNodeCategorySimul?_atoms_preserved hO hhost
        exact hrootAtoms name hname
      · exact left.atoms_preserved
          (by
            intro B₀ hB name hname
            exact hatoms B₀
              (by simp [DerivationTree.nodeCategories_binary, hB]) name hname)
          B₀ hB name hname
      · exact right.atoms_preserved
          (by
            intro B₀ hB name hname
            exact hatoms B₀
              (by simp [DerivationTree.nodeCategories_binary, hB]) name hname)
          B₀ hB name hname
  }⟩

/-- Rebuild a forward crossed-composition node from rewritten premises. -/
theorem crossedRight
    {Γ Δ Ω : List Category} {C B A Z : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ (A ⧹ B)}
    (ctx : DerivationContext (Γ ++ Δ) (A ⧹ C) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedRight))}
    (F : PieceReplacementFamilyCore P)
    (left : RewrittenTree (ctx.inBinaryLeft t₂ Rule.crossedRight) F)
    (right : RewrittenTree (ctx.inBinaryRight t₁ Rule.crossedRight) F) :
    Nonempty (RewrittenTree ctx F) := by
  have hnode :
      (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedRight)).categoryAt?
        ctx.nodePrefix = some (A ⧹ C) := by
    simpa using ctx.categoryAt?_local
      (DerivationTree.categoryAt?_root
        (DerivationTree.binary t₁ t₂ Rule.crossedRight))
  obtain ⟨O', hO⟩ := F.rewriteNodeCategorySimul?_success hnode
  let r : Rule left.root' right.root' O' :=
    F.rewrite_preserves_crossedRight_at ctx
      left.root_rewrite right.root_rewrite hO
  exact ⟨{
    root' := O'
    tree := DerivationTree.binary left.tree right.tree r
    root_rewrite := hO
    size_le := by
      have hrootLe := F.rewriteNodeCategorySimul?_constructors_le hnode hO
      have hleftLe := left.size_le
      have hrightLe := right.size_le
      simp [DerivationTree.size_binary]
      omega
    size_lt_of_target := by
      intro R hR p hpath
      cases p with
      | nil =>
          have hrootLt :=
            F.rewriteNodeCategorySimul?_constructors_lt_of_target
              hnode hO hR (by simpa [hpath])
          have hleftLe := left.size_le
          have hrightLe := right.size_le
          simp [DerivationTree.size_binary]
          omega
      | cons step rest =>
          cases step with
          | unary =>
              have hlocal := ctx.categoryAt?_reflect
                (p := TreeStep.unary :: rest) (by simpa [hpath] using R.nodeAt)
              simp [DerivationTree.categoryAt?] at hlocal
          | left =>
              have hleftPath :
                  R.nodePath = (ctx.nodePrefix ++ [.left]) ++ rest := by
                simpa [List.append_assoc] using hpath
              have hleftLt := left.size_lt_of_target hR hleftPath
              have hrootLe := F.rewriteNodeCategorySimul?_constructors_le hnode hO
              have hrightLe := right.size_le
              simp [DerivationTree.size_binary]
              omega
          | right =>
              have hrightPath :
                  R.nodePath = (ctx.nodePrefix ++ [.right]) ++ rest := by
                simpa [List.append_assoc] using hpath
              have hrightLt := right.size_lt_of_target hR hrightPath
              have hrootLe := F.rewriteNodeCategorySimul?_constructors_le hnode hO
              have hleftLe := left.size_le
              simp [DerivationTree.size_binary]
              omega
    atoms_preserved := by
      intro hatoms B₀ hB name hname
      simp only [DerivationTree.nodeCategories_binary, List.mem_cons,
        List.mem_append] at hB
      rcases hB with hB | hB | hB
      · subst B₀
        have hrootAtoms :
            ∀ name ∈ O'.atoms, name ∈ problemAtomNames Ω Z := by
          have hhost :
              ∀ name ∈ (A ⧹ C).atoms, name ∈ problemAtomNames Ω Z := by
            intro name hname
            exact hatoms (A ⧹ C)
              (by simp [DerivationTree.nodeCategories_binary]) name hname
          exact F.rewriteNodeCategorySimul?_atoms_preserved hO hhost
        exact hrootAtoms name hname
      · exact left.atoms_preserved
          (by
            intro B₀ hB name hname
            exact hatoms B₀
              (by simp [DerivationTree.nodeCategories_binary, hB]) name hname)
          B₀ hB name hname
      · exact right.atoms_preserved
          (by
            intro B₀ hB name hname
            exact hatoms B₀
              (by simp [DerivationTree.nodeCategories_binary, hB]) name hname)
          B₀ hB name hname
  }⟩

/-- Rebuild a backward crossed-composition node from rewritten premises. -/
theorem crossedLeft
    {Γ Δ Ω : List Category} {B A C Z : Category}
    {t₁ : DerivationTree Γ (B ⧸ A)} {t₂ : DerivationTree Δ (B ⧹ C)}
    (ctx : DerivationContext (Γ ++ Δ) (C ⧸ A) Ω Z)
    {P : InvisiblePiece (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedLeft))}
    (F : PieceReplacementFamilyCore P)
    (left : RewrittenTree (ctx.inBinaryLeft t₂ Rule.crossedLeft) F)
    (right : RewrittenTree (ctx.inBinaryRight t₁ Rule.crossedLeft) F) :
    Nonempty (RewrittenTree ctx F) := by
  have hnode :
      (ctx.plug (DerivationTree.binary t₁ t₂ Rule.crossedLeft)).categoryAt?
        ctx.nodePrefix = some (C ⧸ A) := by
    simpa using ctx.categoryAt?_local
      (DerivationTree.categoryAt?_root
        (DerivationTree.binary t₁ t₂ Rule.crossedLeft))
  obtain ⟨O', hO⟩ := F.rewriteNodeCategorySimul?_success hnode
  let r : Rule left.root' right.root' O' :=
    F.rewrite_preserves_crossedLeft_at ctx
      left.root_rewrite right.root_rewrite hO
  exact ⟨{
    root' := O'
    tree := DerivationTree.binary left.tree right.tree r
    root_rewrite := hO
    size_le := by
      have hrootLe := F.rewriteNodeCategorySimul?_constructors_le hnode hO
      have hleftLe := left.size_le
      have hrightLe := right.size_le
      simp [DerivationTree.size_binary]
      omega
    size_lt_of_target := by
      intro R hR p hpath
      cases p with
      | nil =>
          have hrootLt :=
            F.rewriteNodeCategorySimul?_constructors_lt_of_target
              hnode hO hR (by simpa [hpath])
          have hleftLe := left.size_le
          have hrightLe := right.size_le
          simp [DerivationTree.size_binary]
          omega
      | cons step rest =>
          cases step with
          | unary =>
              have hlocal := ctx.categoryAt?_reflect
                (p := TreeStep.unary :: rest) (by simpa [hpath] using R.nodeAt)
              simp [DerivationTree.categoryAt?] at hlocal
          | left =>
              have hleftPath :
                  R.nodePath = (ctx.nodePrefix ++ [.left]) ++ rest := by
                simpa [List.append_assoc] using hpath
              have hleftLt := left.size_lt_of_target hR hleftPath
              have hrootLe := F.rewriteNodeCategorySimul?_constructors_le hnode hO
              have hrightLe := right.size_le
              simp [DerivationTree.size_binary]
              omega
          | right =>
              have hrightPath :
                  R.nodePath = (ctx.nodePrefix ++ [.right]) ++ rest := by
                simpa [List.append_assoc] using hpath
              have hrightLt := right.size_lt_of_target hR hrightPath
              have hrootLe := F.rewriteNodeCategorySimul?_constructors_le hnode hO
              have hleftLe := left.size_le
              simp [DerivationTree.size_binary]
              omega
    atoms_preserved := by
      intro hatoms B₀ hB name hname
      simp only [DerivationTree.nodeCategories_binary, List.mem_cons,
        List.mem_append] at hB
      rcases hB with hB | hB | hB
      · subst B₀
        have hrootAtoms :
            ∀ name ∈ O'.atoms, name ∈ problemAtomNames Ω Z := by
          have hhost :
              ∀ name ∈ (C ⧸ A).atoms, name ∈ problemAtomNames Ω Z := by
            intro name hname
            exact hatoms (C ⧸ A)
              (by simp [DerivationTree.nodeCategories_binary]) name hname
          exact F.rewriteNodeCategorySimul?_atoms_preserved hO hhost
        exact hrootAtoms name hname
      · exact left.atoms_preserved
          (by
            intro B₀ hB name hname
            exact hatoms B₀
              (by simp [DerivationTree.nodeCategories_binary, hB]) name hname)
          B₀ hB name hname
      · exact right.atoms_preserved
          (by
            intro B₀ hB name hname
            exact hatoms B₀
              (by simp [DerivationTree.nodeCategories_binary, hB]) name hname)
          B₀ hB name hname
  }⟩

/-- Every protected-skeleton-free local derivation subtree can be rewritten
inside its derivation context.  This is the recursive tree-surgery skeleton:
each case rebuilds the local rule from the rewritten children using the
context-parametric rule-preservation lemmas above. -/
theorem exists_rewrittenTree_of_protectedSkeletonFree
    {Γ Ω : List Category} {A Z : Category}
    {localTree : DerivationTree Γ A}
    (ctx : DerivationContext Γ A Ω Z)
    {P : InvisiblePiece (ctx.plug localTree)}
    (F : PieceReplacementFamilyCore P)
    (hsafe : P.ProtectedSkeletonFree) :
    Nonempty (RewrittenTree ctx F) := by
  induction localTree generalizing Ω Z with
  | leaf A =>
      have hleafLocal : (DerivationTree.leaf A).isLeafNode [] := by
        simp [DerivationTree.isLeafNode]
      have hleaf :
          (ctx.plug (DerivationTree.leaf A)).isLeafNode ctx.nodePrefix := by
        simpa using ctx.liftLeafNode (t := DerivationTree.leaf A) (p := []) hleafLocal
      exact ⟨RewrittenTree.leaf ctx F hleaf⟩
  | typeRaiseRight C t ih =>
      obtain ⟨child⟩ :=
        ih (ctx.inTypeRaiseRight) F hsafe
      exact RewrittenTree.typeRaiseRight ctx F hsafe child
  | typeRaiseLeft C t ih =>
      obtain ⟨child⟩ :=
        ih (ctx.inTypeRaiseLeft) F hsafe
      exact RewrittenTree.typeRaiseLeft ctx F hsafe child
  | binary t₁ t₂ r ih₁ ih₂ =>
      cases r with
      | appRight =>
          obtain ⟨left⟩ :=
            ih₁ (ctx.inBinaryLeft t₂ Rule.appRight) F hsafe
          obtain ⟨right⟩ :=
            ih₂ (ctx.inBinaryRight t₁ Rule.appRight) F hsafe
          exact RewrittenTree.appRight ctx F left right
      | appLeft =>
          obtain ⟨left⟩ :=
            ih₁ (ctx.inBinaryLeft t₂ Rule.appLeft) F hsafe
          obtain ⟨right⟩ :=
            ih₂ (ctx.inBinaryRight t₁ Rule.appLeft) F hsafe
          exact RewrittenTree.appLeft ctx F left right
      | compRight =>
          obtain ⟨left⟩ :=
            ih₁ (ctx.inBinaryLeft t₂ Rule.compRight) F hsafe
          obtain ⟨right⟩ :=
            ih₂ (ctx.inBinaryRight t₁ Rule.compRight) F hsafe
          exact RewrittenTree.compRight ctx F left right
      | compLeft =>
          obtain ⟨left⟩ :=
            ih₁ (ctx.inBinaryLeft t₂ Rule.compLeft) F hsafe
          obtain ⟨right⟩ :=
            ih₂ (ctx.inBinaryRight t₁ Rule.compLeft) F hsafe
          exact RewrittenTree.compLeft ctx F left right
      | crossedRight =>
          obtain ⟨left⟩ :=
            ih₁ (ctx.inBinaryLeft t₂ Rule.crossedRight) F hsafe
          obtain ⟨right⟩ :=
            ih₂ (ctx.inBinaryRight t₁ Rule.crossedRight) F hsafe
          exact RewrittenTree.crossedRight ctx F left right
      | crossedLeft =>
          obtain ⟨left⟩ :=
            ih₁ (ctx.inBinaryLeft t₂ Rule.crossedLeft) F hsafe
          obtain ⟨right⟩ :=
            ih₂ (ctx.inBinaryRight t₁ Rule.crossedLeft) F hsafe
          exact RewrittenTree.crossedLeft ctx F left right

end RewrittenTree

/-- A protected-skeleton-free replacement family reconstructs a strictly
smaller derivation tree.

The recursive `RewrittenTree` construction gives non-increase at every node.
Strictness comes from `F.size_decreasing`: pick one concrete replacement target
`R`.  At the top-level hole context, `[]` is a prefix of every `R.nodePath`, so
the `size_lt_of_target` field follows the unique path to that node and applies
the node-local strict constructor-count lemma there. -/
theorem toContractionWitness_of_protectedSkeletonFree
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t}
    (F : PieceReplacementFamilyCore P)
    (hsafe : P.ProtectedSkeletonFree) :
    Nonempty (ContractionWitness t) := by
  obtain ⟨rw⟩ :=
    RewrittenTree.exists_rewrittenTree_of_protectedSkeletonFree
      (DerivationContext.hole Γ A) F hsafe
  rcases rw with ⟨root', tree, hRewrite, _hSizeLe, hSizeLt, hAtoms⟩
  have hroot : root' = A := by
    have hrootId := F.rewriteNodeCategorySimul?_root A
    exact Option.some.inj (hRewrite.symm.trans hrootId)
  subst root'
  obtain ⟨R, hR, _hdec⟩ := F.size_decreasing
  refine ⟨{
    target := tree
    size_lt := ?_
    preserves_problem_atoms := ?_
  }⟩
  · exact hSizeLt hR (p := R.nodePath) rfl
  · intro hatoms
    exact hAtoms hatoms

end PieceReplacementFamilyCore

/-- Invisible trace components cannot contain two strict-prefix constructor
occurrences at the same derivation node.  The trace component gives equality of
the pointed subcategories, while strict prefix gives a strict constructor-count
decrease. -/
theorem sameInvisibleTraceComponent_forbids_strictPrefix_same_node
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ : Occurrence t}
    (hnode : o₁.nodePath = o₂.nodePath)
    (hstrict : o₁.categoryPath.StrictPrefix o₂.categoryPath)
    (hpiece : SameInvisibleTraceComponent o₁ o₂) :
    False := by
  have hcat : o₁.nodeCategory = o₂.nodeCategory := by
    apply Option.some.inj
    calc
      some o₁.nodeCategory = t.categoryAt? o₁.nodePath := by
        rw [o₁.nodeAt]
      _ = t.categoryAt? o₂.nodePath := by
        rw [hnode]
      _ = some o₂.nodeCategory := by
        rw [o₂.nodeAt]
  obtain ⟨S, hS⟩ : ∃ S, o₁.nodeCategory.subcategoryAt? o₁.categoryPath = some S := by
    rcases o₁.isConstructor with ⟨L, R, hslash | hslash⟩
    · exact ⟨L ⧸ R, hslash⟩
    · exact ⟨L ⧹ R, hslash⟩
  obtain ⟨T, hT⟩ : ∃ T, o₂.nodeCategory.subcategoryAt? o₂.categoryPath = some T := by
    rcases o₂.isConstructor with ⟨L, R, hslash | hslash⟩
    · exact ⟨L ⧸ R, hslash⟩
    · exact ⟨L ⧹ R, hslash⟩
  have hT' : o₁.nodeCategory.subcategoryAt? o₂.categoryPath = some T := by
    simpa [hcat] using hT
  have hlt : T.constructors < S.constructors :=
    Category.constructors_lt_of_strictPrefix_subcategoryAt? hS hT' hstrict
  have hsameSome : some S = some T := by
    have hsameSub := hpiece.sameSub
    rw [hS, hT] at hsameSub
    exact hsameSub
  have hsame : S = T := Option.some.inj hsameSome
  have : S.constructors < S.constructors := by
    simpa [hsame] using hlt
  omega

namespace InvisiblePiece

/-- Occurrences in one invisible piece cannot be strict-prefix related inside
the same derivation node.  This is the non-overlap fact needed before applying
many replacements inside one category. -/
theorem forbids_strictPrefix_same_node
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (P : InvisiblePiece t) {o₁ o₂ : Occurrence t}
    (ho₁ : o₁ ∈ P.carrier) (ho₂ : o₂ ∈ P.carrier)
    (hnode : o₁.nodePath = o₂.nodePath)
    (hstrict : o₁.categoryPath.StrictPrefix o₂.categoryPath) :
    False :=
  sameInvisibleTraceComponent_forbids_strictPrefix_same_node
    hnode hstrict (P.connected o₁ ho₁ o₂ ho₂)

end InvisiblePiece

namespace PieceReplacementTargets

/-- Targets generated from one invisible piece are same-node antichains. -/
theorem sameNodeAntichain
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} {targets : List (PieceReplacementTarget P)} :
    SameNodeAntichain targets := by
  intro R₁ _hR₁ R₂ _hR₂ hnode
  constructor
  · intro hstrict
    have horiginNode : R₁.origin.nodePath = R₂.origin.nodePath := by
      calc
        R₁.origin.nodePath = R₁.nodePath := R₁.node_eq.symm
        _ = R₂.nodePath := hnode
        _ = R₂.origin.nodePath := R₂.node_eq
    have horiginStrict :
        R₁.origin.categoryPath.StrictPrefix R₂.origin.categoryPath := by
      simpa [R₁.pos_eq, R₂.pos_eq] using hstrict
    exact P.forbids_strictPrefix_same_node
      R₁.origin_mem R₂.origin_mem horiginNode horiginStrict
  · intro hstrict
    have horiginNode : R₂.origin.nodePath = R₁.origin.nodePath := by
      calc
        R₂.origin.nodePath = R₂.nodePath := R₂.node_eq.symm
        _ = R₁.nodePath := hnode.symm
        _ = R₁.origin.nodePath := R₁.node_eq
    have horiginStrict :
        R₂.origin.categoryPath.StrictPrefix R₁.origin.categoryPath := by
      simpa [R₁.pos_eq, R₂.pos_eq] using hstrict
    exact P.forbids_strictPrefix_same_node
      R₂.origin_mem R₁.origin_mem horiginNode horiginStrict

end PieceReplacementTargets

namespace InvisiblePiece

/-- A boundary-free invisible piece determines a concrete trace-closed
replacement family using one fixed problem atom. -/
theorem exists_pieceReplacementFamilyCore
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (P : InvisiblePiece t) (hfree : BoundaryFree P) :
    ∃ F : PieceReplacementFamilyCore P, F.targets ≠ [] := by
  obtain ⟨atomName, hatom⟩ := exists_mem_problemAtomNames_goal Γ A
  obtain ⟨targets, hcompleteAttached, hprops⟩ :=
    PieceReplacementTargets.exists_for_attached
      (P := P) (atomName := atomName) hatom P.carrier.attach
  have hcomplete : PieceReplacementTargets.Complete targets := by
    intro o ho
    exact hcompleteAttached ⟨o, ho⟩ (List.mem_attach P.carrier ⟨o, ho⟩)
  have hnonempty : targets ≠ [] := by
    intro hnil
    cases hcarrier : P.carrier with
    | nil =>
        exact P.nonempty hcarrier
    | cons o rest =>
        have ho : o ∈ P.carrier := by simp [hcarrier]
        obtain ⟨R, hRmem, _hRorigin⟩ := hcomplete o ho
        rw [hnil] at hRmem
        cases hRmem
  have hsize : ∃ R : PieceReplacementTarget P,
      R ∈ targets ∧ R.new.constructors < R.old.constructors := by
    cases hcarrier : P.carrier with
    | nil =>
        exact False.elim (P.nonempty hcarrier)
    | cons o rest =>
        have ho : o ∈ P.carrier := by simp [hcarrier]
        obtain ⟨R, hRmem, _hRorigin⟩ := hcomplete o ho
        exact ⟨R, hRmem, (hprops R hRmem).2.1⟩
  refine ⟨{
    atomName := atomName
    atom_mem := hatom
    targets := targets
    nonempty := hnonempty
    target_new := by
      intro R hR
      exact (hprops R hR).1
    complete := hcomplete
    trace_closed := PieceReplacementTargets.traceClosed_of_complete hfree hcomplete
    same_node_antichain := PieceReplacementTargets.sameNodeAntichain
    root_free := by
      intro R _hR
      exact R.root_free
    leaf_free := by
      intro R _hR
      exact R.leaf_free
    principal_free := by
      intro R _hR
      exact R.principal_free
    size_decreasing := hsize
    atoms_preserved := by
      intro R hR name hname
      exact (hprops R hR).2.2 name hname
  }, hnonempty⟩

end InvisiblePiece

/-- Boundary-free pieces that contain no protected unary type-raising skeleton
constructors contract by the node-local atom-replacement construction. -/
theorem boundaryFreeReplaceableInvisiblePieceContractsFromPieces :
    BoundaryFreeReplaceableInvisiblePieceContractsFromPieces := by
  intro Γ A t _hatoms P hfree hsafe
  obtain ⟨F, _hFnonempty⟩ := P.exists_pieceReplacementFamilyCore hfree
  exact F.toContractionWitness_of_protectedSkeletonFree hsafe

/-- A bare contraction step induces an occurrence-free band redex.  This is
useful for examples where the redex is obvious and the concrete trace
occurrences are not important. -/
def HasBandRedex {Γ : List Category} {A : Category} (t : DerivationTree Γ A) : Prop :=
  ∃ t' : DerivationTree Γ A, Contracts t t'

/-- The forward type-raising/application collapse is a bare band redex. -/
theorem hasBandRedex_collapseRight
    {Γ Δ : List Category} {A C : Category}
    (s : DerivationTree Γ A) (w : DerivationTree Δ (A ⧹ C)) :
    HasBandRedex
      (DerivationTree.binary (DerivationTree.typeRaiseRight C s) w Rule.appRight) :=
  ⟨DerivationTree.binary s w Rule.appLeft, Contracts.collapseRight s w⟩

/-!
Protected unary-skeleton occurrences cannot be dispatched by a blanket
visible-boundary theorem.  In the concrete tree

`appRight (typeRaiseRight C (leaf (C / X))) (typeRaiseLeft C (leaf X))`

the inner skeleton of the left `T>` output and the outer skeleton of the right
`T<` output are connected by the `appRight_B` trace edge.  Both are non-root,
non-leaf, non-principal occurrences of the whole tree.  This is exactly the
forward collapse redex, so protected-skeleton pieces must be handled by band
contraction rather than atom replacement or a false visible-boundary lemma.
-/
namespace ProtectedSkeletonCounterexample

private def counterTree (C X : Category) :
    DerivationTree ([C ⧸ X] ++ [X]) C :=
  DerivationTree.binary
    (DerivationTree.typeRaiseRight C (DerivationTree.leaf (C ⧸ X)))
    (DerivationTree.typeRaiseLeft C (DerivationTree.leaf X))
    Rule.appRight

private def leftInner (C X : Category) : Occurrence (counterTree C X) where
  nodePath := [.left]
  nodeCategory := C ⧸ ((C ⧸ X) ⧹ C)
  nodeAt := by rfl
  categoryPath := [true]
  isConstructor := by exact ⟨C ⧸ X, C, Or.inr rfl⟩

private def rightOuter (C X : Category) : Occurrence (counterTree C X) where
  nodePath := [.right]
  nodeCategory := (C ⧸ X) ⧹ C
  nodeAt := by rfl
  categoryPath := []
  isConstructor := by exact ⟨C ⧸ X, C, Or.inr rfl⟩

private theorem leftInner_protected (C X : Category) :
    (leftInner C X).ProtectedUnarySkeleton := by
  change DerivationTree.UnarySkeletonConstructor (counterTree C X) [.left] [true]
  exact DerivationTree.UnarySkeletonConstructor.underBinaryLeft Rule.appRight
    (DerivationTree.UnarySkeletonConstructor.trRight_inner (C := C)
      (DerivationTree.leaf (C ⧸ X)))

private theorem rightOuter_protected (C X : Category) :
    (rightOuter C X).ProtectedUnarySkeleton := by
  change DerivationTree.UnarySkeletonConstructor (counterTree C X) [.right] ([] : CategoryPath)
  exact DerivationTree.UnarySkeletonConstructor.underBinaryRight Rule.appRight
    (DerivationTree.UnarySkeletonConstructor.trLeft_outer (C := C)
      (DerivationTree.leaf X))

private theorem traceEdge_leftInner_rightOuter (C X : Category) :
    TraceEdge (leftInner C X) (rightOuter C X) := by
  exact Or.inl (Or.inl (LocalTraceEdge.appRight_B rfl rfl rfl rfl))

private theorem counterTree_hasBandRedex (C X : Category) :
    HasBandRedex (counterTree C X) :=
  hasBandRedex_collapseRight
    (DerivationTree.leaf (C ⧸ X))
    (DerivationTree.typeRaiseLeft C (DerivationTree.leaf X))

end ProtectedSkeletonCounterexample

/-! ## Worked example: the paper's `long ↝ short` contraction -/

namespace Example

/-- `a` as an atom. -/
private def a : Category := # "a"
/-- `c` as an atom. -/
private def c : Category := # "c"

/-- `X = c/(a\c)`, the once-raised subject of the paper's example. -/
private def X : Category := c ⧸ (a ⧹ c)
/-- `w₂ = (c/(a\c))\c = X\c`, the second input word. -/
private def w₂ : Category := X ⧹ c

/-- The long derivation tree: `(T>)` twice then `(>)`, of the example. -/
private def longTree : DerivationTree [a, w₂] c :=
  DerivationTree.binary
    (DerivationTree.typeRaiseRight c (DerivationTree.typeRaiseRight c (DerivationTree.leaf a)))
    (DerivationTree.leaf w₂)
    Rule.appRight

/-- The short derivation tree: one `(T>)` then `(<)`. -/
private def shortTree : DerivationTree [a, w₂] c :=
  DerivationTree.binary
    (DerivationTree.typeRaiseRight c (DerivationTree.leaf a))
    (DerivationTree.leaf w₂)
    Rule.appLeft

/-- The long tree contracts to the short tree (one band redex). -/
private theorem long_contracts_short : Contracts longTree shortTree :=
  Contracts.collapseRight (DerivationTree.typeRaiseRight c (DerivationTree.leaf a)) (DerivationTree.leaf w₂)

/-- The contraction strictly decreases `size`, matching the paper's
`size(short) < size(long)`. -/
private theorem long_short_size_lt : shortTree.size < longTree.size :=
  long_contracts_short.size_lt

end Example

end Mathling.CCG
