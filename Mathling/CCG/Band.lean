import Mathling.CCG.Atoms
import Mathling.CCG.Trace
import Mathlib.Data.Fintype.Card

/-!
# Band contraction

This module formalizes the band-contraction core of
`ccg_decidability_proof_3-1.pdf` (Lemmas `band-correct`, `rep-band`,
`band-contract`, and Corollary `minimal`).

The paper's band contraction removes an "externally invisible repeated segment"
from a derivation, producing an equivalent derivation of strictly smaller
constructor-occurrence measure `size`.  The repeats that make intermediate
categories unboundedly deep are exactly stacked type-raising steps feeding an
application; collapsing such a step is the engine of contraction.

We formalize contraction as a rewrite relation `Contracts` on explicit
derivation trees (`Mathling.CCG.Tree`):

* two **band redexes** that each delete one type-raising step feeding an
  application (`Contracts.collapseRight` / `collapseLeft`), and
* **congruence** closing the redexes under every tree context (the transport of
  a deletion through the derivation).

The headline results are:

* `Contracts.size_lt` — every contraction strictly decreases `size`
  (the paper's `size(D/B) < size(D)`);
* `Contracts.toDerivable_eq` style preservation is automatic: a `Contracts t t'`
  keeps the indices `Γ`, `A`, so both sides derive the *same* sequent;
* `contractionTarget_contract`, `contractingRepeatablePair_to_contractionTarget`,
  `contractingRepeatablePair_contract` — the proof-carrying contraction interface;
* `Derivable.minimal_no_contractingRepeatablePair` — a `size`-minimal tree has no
  repeatable pair that already carries a contraction witness.
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

/-- Read an old-style concrete contraction step through the common contraction
witness interface. -/
def toContractionWitness
    {Γ : List Category} {A : Category} {t t' : DerivationTree Γ A}
    (h : Contracts t t') : ContractionWitness t where
  target := t'
  size_lt := h.size_lt
  preserves_problem_atoms := h.preserves_nodeCategoriesUseProblemAtoms

end Contracts

/-! ## Transport-closed bands and the band-contraction lemma -/

/-- A transport-closed band over `t`: a contraction target reachable from `t`.

In this development the contraction relation `Contracts` already realizes the
deletion of a transport-closed segment (the congruence cases transport a redex
through the derivation), so a band is exactly a one-step contraction. -/
def ContractionTarget {Γ : List Category} {A : Category} (t : DerivationTree Γ A) : Type :=
  { t' : DerivationTree Γ A // Contracts t t' }

/-- The contracted tree of a band. -/
def contractedTree {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (B : ContractionTarget t) : DerivationTree Γ A := B.1

/-- Contracting a band strictly decreases `size` and keeps the same sequent
(the indices `Γ`, `A` are fixed by typing).  This is Lemma `band-contract`. -/
theorem contractionTarget_contract {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (B : ContractionTarget t) :
    (contractedTree B).size < t.size :=
  B.2.size_lt

/-- Contracting a band gives an explicitly smaller tree for the same sequent. -/
theorem contractionTarget_contract_exists {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (B : ContractionTarget t) :
    ∃ t' : DerivationTree Γ A, t'.size < t.size :=
  ⟨contractedTree B, contractionTarget_contract B⟩

/-- Every old-style contraction target is also a common contraction witness. -/
def ContractionTarget.toContractionWitness
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (B : ContractionTarget t) : ContractionWitness t :=
  B.2.toContractionWitness

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

/-- Every prefix of `p` is a strict prefix of `p` extended by one more branch
step.  This supplies the common branch endpoint used by repeatable-pair
construction, including the case where the lower occurrence is exactly at `p`. -/
theorem CategoryPath.mem_prefixes_strictPrefix_snoc
    {q p : CategoryPath} (hq : q ∈ CategoryPath.prefixes p) (b : Bool) :
    q.StrictPrefix (p ++ [b]) := by
  have hprefix : q.Prefix p := CategoryPath.mem_prefixes_prefix hq
  obtain ⟨rest, hp⟩ := hprefix
  have hprefixEnd : q.Prefix (p ++ [b]) := by
    refine ⟨rest ++ [b], ?_⟩
    rw [hp]
    simp [List.append_assoc]
  refine hprefixEnd.strict_of_ne ?_
  intro hqeq
  have hlen : q.length ≤ p.length := by
    rw [hp, List.length_append]
    omega
  have hlenEq : q.length = p.length + 1 := by
    rw [hqeq, List.length_append]
    simp
  omega

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

/-- The next branch direction after a prefix position.  If `prefix` is not a
proper prefix of `branch`, this total helper returns `false`; repeatability
stores strict-prefix proofs separately, so the meaningful cases are exactly the
nonempty suffix cases. -/
def CategoryPath.nextAfterPrefix : CategoryPath → CategoryPath → Bool
  | [], b :: _ => b
  | [], [] => false
  | _ :: ps, _ :: qs => nextAfterPrefix ps qs
  | _ :: _, [] => false

/-- Branch-aware interface state `st_β(o)`: unlike the older occurrence-only
`interfaceState`, the direction component is read from the branch endpoint β. -/
def interfaceStateOnBranch {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (o : Occurrence t) (branchEnd : CategoryPath) : InterfaceState :=
  { slash := slashKindAt o.nodeCategory o.categoryPath
    branchDir := o.categoryPath.nextAfterPrefix branchEnd
    lowerPort := lowerPortAt o
    upperPort := upperPortAt o }

/-- Branch-aware interface states still lie in the explicit finite interface
state enumeration. -/
theorem interfaceStateOnBranch_mem_all {Γ : List Category} {A : Category}
    {t : DerivationTree Γ A} (o : Occurrence t) (branchEnd : CategoryPath) :
    interfaceStateOnBranch o branchEnd ∈ allInterfaceStates := by
  unfold interfaceStateOnBranch allInterfaceStates allSlashKinds allBranchDirs allPortKinds
  generalize slashKindAt o.nodeCategory o.categoryPath = sk
  generalize o.categoryPath.nextAfterPrefix branchEnd = bd
  generalize lowerPortAt o = lo
  generalize upperPortAt o = hi
  cases sk <;> cases bd <;> cases lo <;> cases hi <;> decide

/-- An occurrence lies strictly between two category positions on the same
branch. -/
def CategoryPath.StrictBetween (lo mid hi : CategoryPath) : Prop :=
  lo.StrictPrefix mid ∧ mid.StrictPrefix hi

/-- The paper's visible-free branch segment condition between two occurrences.
Every constructor strictly between the two category positions, at the same tree
node, must be invisible. -/
def VisibleFreeSegment {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (o₁ o₂ : Occurrence t) : Prop :=
  ∀ o : Occurrence t,
    o.nodePath = o₁.nodePath →
      CategoryPath.StrictBetween o₁.categoryPath o.categoryPath o₂.categoryPath →
        o.Invisible

/-! ## Branch slices and slice transport -/

/-- A branch slice is the concrete segment deleted by a band contraction: the
category path `topOcc` is a strict ancestor of `botOcc` in the same derivation
node, both endpoints are invisible constructor occurrences, and the interior of
the segment is visible-free.

The key design point is that this is a *segment* object.  It does not assert
that the two endpoint occurrences are in the same trace component, avoiding the
`SameTraceComponent.sameSub` contradiction for strict-prefix pairs. -/
structure BandSlice {Γ : List Category} {A : Category}
    (t : DerivationTree Γ A) where
  topOcc : Occurrence t
  botOcc : Occurrence t
  same_node : topOcc.nodePath = botOcc.nodePath
  strict : topOcc.categoryPath.StrictPrefix botOcc.categoryPath
  top_invisible : topOcc.Invisible
  bot_invisible : botOcc.Invisible
  removed_invisible : VisibleFreeSegment topOcc botOcc

namespace BandSlice

variable {Γ : List Category} {A : Category} {t : DerivationTree Γ A}

/-- Node containing the slice. -/
def nodePath (S : BandSlice t) : NodePath := S.topOcc.nodePath

/-- Category containing the slice. -/
def nodeCategory (S : BandSlice t) : Category := S.topOcc.nodeCategory

/-- Top category position of the removed segment. -/
def top (S : BandSlice t) : CategoryPath := S.topOcc.categoryPath

/-- Bottom category position of the removed segment. -/
def bot (S : BandSlice t) : CategoryPath := S.botOcc.categoryPath

/-- The top endpoint is a constructor position in the containing category. -/
theorem top_is_constructor (S : BandSlice t) :
    S.top ∈ S.nodeCategory.constructorPositions :=
  Category.mem_constructorPositions_of_isConstructor S.nodeCategory S.topOcc.isConstructor

/-- The bottom endpoint is a constructor position in its containing category. -/
theorem bot_is_constructor (S : BandSlice t) :
    S.botOcc.categoryPath ∈ S.botOcc.nodeCategory.constructorPositions :=
  Category.mem_constructorPositions_of_isConstructor S.botOcc.nodeCategory S.botOcc.isConstructor

end BandSlice

/-- Transport of deletion slices through equal metavariable copies.  Endpoint
trace connectivity is used pairwise: top endpoints transport to top endpoints,
and bottom endpoints transport to bottom endpoints.  It never connects a top
endpoint to its own bottom endpoint, so strict-prefix slices are not collapsed
by `sameSub`. -/
inductive BandSliceTransport {Γ : List Category} {A : Category}
    {t : DerivationTree Γ A} : BandSlice t → BandSlice t → Prop where
  | endpointTrace {S T : BandSlice t}
      (top_trace : SameInvisibleTraceComponent S.topOcc T.topOcc)
      (bot_trace : SameInvisibleTraceComponent S.botOcc T.botOcc) :
      BandSliceTransport S T

/-- Same invisible piece on a branch, now defined as transport closure of
branch-deletion slices rather than occurrence-level trace-component equality. -/
def SameInvisiblePieceOnBranch {Γ : List Category} {A : Category}
    {t : DerivationTree Γ A} (S T : BandSlice t) : Prop :=
  Relation.ReflTransGen BandSliceTransport S T

namespace SameInvisiblePieceOnBranch

@[refl]
theorem refl {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (S : BandSlice t) : SameInvisiblePieceOnBranch S S :=
  Relation.ReflTransGen.refl

theorem of_endpoint_traces
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {S T : BandSlice t}
    (htop : SameInvisibleTraceComponent S.topOcc T.topOcc)
    (hbot : SameInvisibleTraceComponent S.botOcc T.botOcc) :
    SameInvisiblePieceOnBranch S T :=
  Relation.ReflTransGen.single (BandSliceTransport.endpointTrace htop hbot)

end SameInvisiblePieceOnBranch

/-- The honest carrier of a transport-closed band, before constructing the
contracted derivation tree.  This structure deliberately does **not** contain a
`ContractionWitness`: it is only the finite slice family and the closure/free
side conditions that the paper calls a transport-closed band.

The remaining hard theorem is to turn this core object into an actual smaller
typed derivation tree for the same sequent. -/
structure TransportClosedBandCore {Γ : List Category} {A : Category}
    (t : DerivationTree Γ A) where
  slices : List (BandSlice t)
  nonempty : slices ≠ []
  transport_closed :
    ∀ S T : BandSlice t, S ∈ slices → BandSliceTransport S T → T ∈ slices
  root_free :
    ∀ S : BandSlice t, S ∈ slices → S.topOcc.nodePath ≠ []
  leaf_free :
    ∀ S : BandSlice t, S ∈ slices → ¬ t.isLeafNode S.topOcc.nodePath
  principal_free :
    ∀ S : BandSlice t, S ∈ slices →
      ¬ DerivationTree.PrincipalConstructor t S.topOcc.nodePath S.topOcc.categoryPath

/-- Compatibility wrapper used by the existing minimality/parser bridges.  It
keeps the older proof-carrying band API available while the honest core theorem
is proved separately.  Unlike `TransportClosedBandCore`, this wrapper may be an
empty compatibility band created directly from a known contraction witness. -/
structure TransportClosedBand {Γ : List Category} {A : Category}
    (t : DerivationTree Γ A) where
  slices : List (BandSlice t)
  transport_closed :
    ∀ S T : BandSlice t, S ∈ slices → BandSliceTransport S T → T ∈ slices
  root_free :
    ∀ S : BandSlice t, S ∈ slices → S.topOcc.nodePath ≠ []
  leaf_free :
    ∀ S : BandSlice t, S ∈ slices → ¬ t.isLeafNode S.topOcc.nodePath
  principal_free :
    ∀ S : BandSlice t, S ∈ slices →
      ¬ DerivationTree.PrincipalConstructor t S.topOcc.nodePath S.topOcc.categoryPath
  contraction : ContractionWitness t

/-- The paper's `band-correct`/`band-contract` theorem target in its honest
core form.  It is a named proposition, not an axiom: downstream code must still
provide a proof before it can obtain a contraction witness from bare slices. -/
def TransportClosedBandCoreContracts : Prop :=
  ∀ {Γ : List Category} {A : Category} {t : DerivationTree Γ A},
    TransportClosedBandCore t → Nonempty (ContractionWitness t)

namespace TransportClosedBand

/-- Forget the compatibility wrapper and keep only the honest core band data. -/
def toCore
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (B : TransportClosedBand t) (hnonempty : B.slices ≠ []) :
    TransportClosedBandCore t where
  slices := B.slices
  nonempty := hnonempty
  transport_closed := B.transport_closed
  root_free := B.root_free
  leaf_free := B.leaf_free
  principal_free := B.principal_free

/-- The common contraction witness carried by a transport-closed band. -/
def toContractionWitness
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (B : TransportClosedBand t) : ContractionWitness t :=
  B.contraction

/-- Compatibility constructor: an already-built contraction witness can be
viewed as an empty proof-carrying band.  Full band proofs should construct a
nonempty `slices` carrier; this helper keeps older concrete redex examples
usable while the slice saturation proof is developed. -/
def ofContractionWitness
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (w : ContractionWitness t) : TransportClosedBand t where
  slices := []
  transport_closed := by intro S T hmem _; cases hmem
  root_free := by intro S hmem; cases hmem
  leaf_free := by intro S hmem; cases hmem
  principal_free := by intro S hmem; cases hmem
  contraction := w

end TransportClosedBand

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

/-- Boundary-free pieces contain every invisible occurrence in the invisible
trace component of any carrier member. -/
theorem mem_of_sameInvisibleTraceComponent_of_boundaryFree
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (P : InvisiblePiece t) (hfree : BoundaryFree P)
    {o p : Occurrence t}
    (ho : o ∈ P.carrier)
    (hcomp : SameInvisibleTraceComponent o p) :
    p ∈ P.carrier := by
  induction hcomp with
  | refl => exact ho
  | tail _ hedge ih =>
      exact P.closed_traceEdge_of_boundaryFree hfree ih hedge.traceEdge

/-- No carrier occurrence of a boundary-free invisible piece has a visible
boundary.  This is the reusable contradiction form for non-redex protected
skeleton cases: once a local rule analysis finds a trace path from the protected
component to a visible endpoint, boundary-freeness rules that case out. -/
theorem no_hasVisibleBoundary_of_boundaryFree
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (P : InvisiblePiece t) (hfree : BoundaryFree P)
    {o : Occurrence t} (ho : o ∈ P.carrier) :
    ¬ HasVisibleBoundary o := by
  rintro ⟨p, v, hcomp, _hpInv, hv, hedge⟩
  have hp : p ∈ P.carrier :=
    P.mem_of_sameInvisibleTraceComponent_of_boundaryFree hfree ho hcomp
  exact hfree p hp v hv hedge

/-- Contradiction package for the previous lemma when the visible boundary is
already available as component connectivity plus one trace edge. -/
theorem false_of_visibleBoundary_of_mem_boundaryFree
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (P : InvisiblePiece t) (hfree : BoundaryFree P)
    {o p v : Occurrence t} (ho : o ∈ P.carrier)
    (hcomp : SameInvisibleTraceComponent o p)
    (hv : v.Visible) (hedge : TraceEdge p v) :
    False := by
  exact P.no_hasVisibleBoundary_of_boundaryFree hfree ho
    ⟨p, v, hcomp,
      P.all_invisible p
        (P.mem_of_sameInvisibleTraceComponent_of_boundaryFree hfree ho hcomp),
      hv, hedge⟩

/-- No visible occurrence can be a carrier member of an invisible piece. -/
theorem false_of_visible_mem
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (P : InvisiblePiece t)
    {o : Occurrence t} (ho : o ∈ P.carrier) (hv : o.Visible) :
    False :=
  P.all_invisible o ho hv

end InvisiblePiece

/-- Every recognition problem has at least one problem atom, namely an atom
from the goal category. -/
theorem exists_mem_problemAtomNames_goal
    (Γ : List Category) (A : Category) :
    ∃ atomName, atomName ∈ problemAtomNames Γ A := by
  obtain ⟨atomName, hatom⟩ := A.exists_mem_atoms
  exact ⟨atomName, mem_problemAtomNames_of_mem_goal hatom⟩

/-- The finite invisible trace component generated by an invisible occurrence,
packaged as an `InvisiblePiece`.  This is a proof-level construction: the
carrier is the finite occurrence enumeration filtered to the invisible
component of `o`. -/
theorem exists_invisiblePieceOfOccurrence
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (o : Occurrence t) (hinv : o.Invisible) :
    ∃ P : InvisiblePiece t, o ∈ P.carrier := by
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
  exact ⟨P, hself⟩

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

/-- Applying a well-formed replacement target to its owning node category
always succeeds, because the target stores a successful `subcategoryAt?`
lookup for the same position. -/
theorem exists_apply?
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (R : ReplacementTarget t) : ∃ C', R.apply? = some C' :=
  Category.replaceSubcategoryAt?_exists_of_subcategoryAt?
    R.nodeCategory R.pos R.old R.new R.old_at

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

/-- A constructor occurrence can be targeted for replacement by some problem
atom of the recognition problem. -/
theorem exists_ofOccurrenceToProblemAtom
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (o : Occurrence t) :
    ∃ atomName, atomName ∈ problemAtomNames Γ A ∧
      ∃ R : ReplacementTarget t,
        R.nodePath = o.nodePath ∧
          R.nodeCategory = o.nodeCategory ∧
          R.pos = o.categoryPath ∧
          R.new = # atomName ∧
          R.new.constructors < R.old.constructors ∧
          (∀ name ∈ R.new.atoms, name ∈ problemAtomNames Γ A) := by
  obtain ⟨atomName, hatom⟩ := exists_mem_problemAtomNames_goal Γ A
  exact ⟨atomName, hatom, exists_ofOccurrenceToAtom o hatom⟩

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
piece.  Unlike the compatibility `ClosedReplacementFamilyCore.transport_closed :
Prop`, the closure fields here are explicit predicates over the origin
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

/-- Honest carrier for a rule-transport-closed family of replacements, before
the contracted derivation tree is reconstructed.  As with
`TransportClosedBandCore`, this core structure contains no contraction witness;
it records exactly the data whose correctness must imply one. -/
structure ClosedReplacementFamilyCore {Γ : List Category} {A : Category}
    (t : DerivationTree Γ A) where
  targets : List (ReplacementTarget t)
  nonempty : targets ≠ []
  transport_closed : Prop
  root_free :
    ∀ R : ReplacementTarget t, R ∈ targets → R.nodePath ≠ []
  leaf_free :
    ∀ R : ReplacementTarget t, R ∈ targets → ¬ t.isLeafNode R.nodePath
  principal_free :
    ∀ R : ReplacementTarget t, R ∈ targets →
      ¬ DerivationTree.PrincipalConstructor t R.nodePath R.pos
  size_decreasing :
    ∃ R : ReplacementTarget t, R ∈ targets ∧ R.new.constructors < R.old.constructors
  atoms_preserved :
    ∀ R : ReplacementTarget t, R ∈ targets →
      ∀ name ∈ R.new.atoms, name ∈ problemAtomNames Γ A

/-- Compatibility wrapper for existing boundary-free-piece bridges: an honest
replacement-family core plus the still-hard contracted derivation witness. -/
structure ClosedReplacementFamily {Γ : List Category} {A : Category}
    (t : DerivationTree Γ A) extends ClosedReplacementFamilyCore t where
  contraction : ContractionWitness t

/-- The paper's boundary-free replacement correctness theorem target in core
form.  It states the missing tree-reconstruction theorem without assuming it. -/
def ClosedReplacementFamilyCoreContracts : Prop :=
  ∀ {Γ : List Category} {A : Category} {t : DerivationTree Γ A},
    ClosedReplacementFamilyCore t → Nonempty (ContractionWitness t)

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

/-- Forget the piece-origin bookkeeping while retaining the concrete closure
predicate in the `transport_closed` proposition field.  This is a data bridge
only; it does not produce a contraction witness. -/
def toClosedReplacementFamilyCore
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P) :
    ClosedReplacementFamilyCore t where
  targets := F.targets.map (fun R => R.toReplacementTarget)
  nonempty := by
    intro hnil
    apply F.nonempty
    cases htargets : F.targets with
    | nil => rfl
    | cons R rest =>
        simp [htargets] at hnil
  transport_closed := PieceReplacementTargets.TraceClosed F.targets
  root_free := by
    intro R hR
    obtain ⟨R', hR', rfl⟩ := List.mem_map.mp hR
    exact F.root_free R' hR'
  leaf_free := by
    intro R hR
    obtain ⟨R', hR', rfl⟩ := List.mem_map.mp hR
    exact F.leaf_free R' hR'
  principal_free := by
    intro R hR
    obtain ⟨R', hR', rfl⟩ := List.mem_map.mp hR
    exact F.principal_free R' hR'
  size_decreasing := by
    obtain ⟨R, hR, hdec⟩ := F.size_decreasing
    exact ⟨R.toReplacementTarget, List.mem_map.mpr ⟨R, hR, rfl⟩, hdec⟩
  atoms_preserved := by
    intro R hR name hname
    obtain ⟨R', hR', rfl⟩ := List.mem_map.mp hR
    exact F.atoms_preserved R' hR' name hname

end PieceReplacementFamilyCore

namespace ClosedReplacementFamily

/-- Forget the compatibility wrapper and keep only the honest replacement data. -/
def toCore
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (R : ClosedReplacementFamily t) : ClosedReplacementFamilyCore t :=
  R.toClosedReplacementFamilyCore

/-- The common contraction witness carried by a closed replacement family. -/
def toContractionWitness
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (R : ClosedReplacementFamily t) : ContractionWitness t :=
  R.contraction

end ClosedReplacementFamily

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

/-- The original strong paper-facing target trivially implies the
replacement-only target. -/
theorem boundaryFreeReplaceableInvisiblePieceContractsFromPieces_of_allPieces
    (h : BoundaryFreeInvisiblePieceContractsFromPieces) :
    BoundaryFreeReplaceableInvisiblePieceContractsFromPieces := by
  intro Γ A t hatoms P hfree _hprotected
  exact h hatoms P hfree

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

/-- Executable placeholder for slice enumeration.  The correctness theorem for
finite saturation is kept separate so this definition can be strengthened
without changing downstream theorem statements. -/
def allBandSlices {Γ : List Category} {A : Category}
    (t : DerivationTree Γ A) : List (BandSlice t) :=
  []

/-- One-step saturation shell around a seed slice.  The full implementation will
replace this with finite closure over `BandSliceTransport`; current users rely
on the `TransportClosedBand` proof fields, not this helper's completeness. -/
def saturateBandSlices {Γ : List Category} {A : Category}
    {t : DerivationTree Γ A} (seed : BandSlice t) : List (BandSlice t) :=
  [seed]

/-! ## Branch segments and visible-free zones -/

/-- Two category occurrences lie on the same category branch of one derivation
node when they have the same node address and comparable category paths. -/
structure BranchSegment {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (lower upper : Occurrence t) : Prop where
  same_node : lower.nodePath = upper.nodePath
  proper_prefix : lower.categoryPath.StrictPrefix upper.categoryPath

/-- A visible-free zone is a branch segment whose strictly interior constructor
occurrences are all invisible.  This is the faithful paper object used before
turning repeated interface states into a transport-closed band. -/
structure VisibleFreeZone {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (lower upper : Occurrence t) : Prop extends BranchSegment lower upper where
  visible_free : VisibleFreeSegment lower upper

/-- The branch endpoint used to read the branch-sensitive interface state of a
branch occurrence. -/
structure BranchEndpoint {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (o : Occurrence t) where
  endpoint : CategoryPath
  strict_prefix : o.categoryPath.StrictPrefix endpoint

/-- Two branch occurrences have the same paper interface state on a common
branch endpoint. -/
def SameBranchInterface {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (o₁ o₂ : Occurrence t) : Prop :=
  ∃ branchEnd : CategoryPath,
    o₁.categoryPath.StrictPrefix branchEnd ∧
      o₂.categoryPath.StrictPrefix branchEnd ∧
        interfaceStateOnBranch o₁ branchEnd = interfaceStateOnBranch o₂ branchEnd

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

/-- The derivation root has no canonical path-rewrite targets. -/
theorem categoryTargetPathsAt_root_eq_nil
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P) :
    F.categoryTargetPathsAt ([] : NodePath) = [] :=
  F.categoryTargetPathsAt_eq_nil_of_no_targets
    (by
      intro R hR hnode
      exact F.root_free R hR hnode)

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

/-- Leaf nodes have no canonical path-rewrite targets. -/
theorem categoryTargetPathsAt_leaf_eq_nil
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece t} (F : PieceReplacementFamilyCore P)
    {nodePath : NodePath}
    (hleaf : t.isLeafNode nodePath) :
    F.categoryTargetPathsAt nodePath = [] :=
  F.categoryTargetPathsAt_eq_nil_of_no_targets
    (by
      intro R hR hnode
      exact F.leaf_free R hR (by simpa [hnode] using hleaf))

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

/-- In a forward application, replacing the left premise's `C` copy would force
a replacement at the derivation root by trace closure, contradicting
`root_free`. -/
theorem appRight_no_left_result_copy_target
    {Γ Δ : List Category} {C B : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ B}
    {P : InvisiblePiece (DerivationTree.binary t₁ t₂ Rule.appRight)}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath} :
    (false :: p, #F.atomName) ∉ F.dedupCategoryTargetsAt [.left] := by
  intro htarget
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff [.left] (false :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = false :: p := by
    exact (congrArg Prod.fst htargetEq).symm
  have hRcat : R.nodeCategory = C ⧸ B := by
    have hnodeAt : (DerivationTree.binary t₁ t₂ Rule.appRight).categoryAt? R.nodePath =
        some (C ⧸ B) := by
      simp [DerivationTree.categoryAt?, hRnode]
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAt)
  have horiginNode : R.origin.nodePath = [.left] := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = false :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = C ⧸ B := by
    rw [← R.cat_eq]
    exact hRcat
  let oRoot : Occurrence (DerivationTree.binary t₁ t₂ Rule.appRight) := {
    nodePath := []
    nodeCategory := C
    nodeAt := by simp [DerivationTree.categoryAt?]
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
  have hlocal : LocalTraceEdge R.origin oRoot :=
    LocalTraceEdge.appRight_C horiginNode horiginPos rfl rfl
  have hdirect : DirectedTraceEdge R.origin oRoot := by
    exact Or.inl hlocal
  have hedge : TraceEdge R.origin oRoot := Or.inl hdirect
  have hrootTarget := F.mem_dedupCategoryTargetsAt_of_traceEdge hR hedge
  simpa [oRoot, F.dedupCategoryTargetsAt_root_eq_nil] using hrootTarget

/-- In a forward application, replacing the `B` copy in the left premise forces
the matching right-premise `B` copy to be replaced. -/
theorem appRight_left_arg_copy_target_to_right
    {Γ Δ : List Category} {C B : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ B}
    {P : InvisiblePiece (DerivationTree.binary t₁ t₂ Rule.appRight)}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget : (true :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt [.left]) :
    (p, #F.atomName) ∈ F.dedupCategoryTargetsAt [.right] := by
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff [.left] (true :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = true :: p := by
    exact (congrArg Prod.fst htargetEq).symm
  have hRcat : R.nodeCategory = C ⧸ B := by
    have hnodeAt : (DerivationTree.binary t₁ t₂ Rule.appRight).categoryAt? R.nodePath =
        some (C ⧸ B) := by
      simp [DerivationTree.categoryAt?, hRnode]
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAt)
  have horiginNode : R.origin.nodePath = [.left] := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = true :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = C ⧸ B := by
    rw [← R.cat_eq]
    exact hRcat
  let oRight : Occurrence (DerivationTree.binary t₁ t₂ Rule.appRight) := {
    nodePath := [.right]
    nodeCategory := B
    nodeAt := by simp [DerivationTree.categoryAt?]
    categoryPath := p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · refine ⟨X, Y, Or.inl ?_⟩
        have hslash' : (C ⧸ B).subcategoryAt? (true :: p) = some (X ⧸ Y) := by
          simpa [horiginCat, horiginPos] using hslash
        simpa [Category.subcategoryAt?_rdiv_true] using hslash'
      · refine ⟨X, Y, Or.inr ?_⟩
        have hslash' : (C ⧸ B).subcategoryAt? (true :: p) = some (X ⧹ Y) := by
          simpa [horiginCat, horiginPos] using hslash
        simpa [Category.subcategoryAt?_rdiv_true] using hslash'
  }
  have hlocal : LocalTraceEdge R.origin oRight :=
    LocalTraceEdge.appRight_B horiginNode horiginPos rfl rfl
  have hdirect : DirectedTraceEdge R.origin oRight := by
    exact Or.inl hlocal
  have hedge : TraceEdge R.origin oRight := Or.inl hdirect
  have hrightTarget := F.mem_dedupCategoryTargetsAt_of_traceEdge hR hedge
  simpa [oRight] using hrightTarget

/-- In a forward application, replacing the right-premise `B` copy forces the
matching left-premise `B` copy to be replaced. -/
theorem appRight_right_arg_copy_target_to_left
    {Γ Δ : List Category} {C B : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ B}
    {P : InvisiblePiece (DerivationTree.binary t₁ t₂ Rule.appRight)}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget : (p, #F.atomName) ∈ F.dedupCategoryTargetsAt [.right]) :
    (true :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt [.left] := by
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff [.right] (p, #F.atomName)).mp hprojected
  have hRpos : R.pos = p := by
    exact (congrArg Prod.fst htargetEq).symm
  have hRcat : R.nodeCategory = B := by
    have hnodeAt : (DerivationTree.binary t₁ t₂ Rule.appRight).categoryAt? R.nodePath =
        some B := by
      simp [DerivationTree.categoryAt?, hRnode]
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAt)
  have horiginNode : R.origin.nodePath = [.right] := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = B := by
    rw [← R.cat_eq]
    exact hRcat
  let oLeft : Occurrence (DerivationTree.binary t₁ t₂ Rule.appRight) := {
    nodePath := [.left]
    nodeCategory := C ⧸ B
    nodeAt := by simp [DerivationTree.categoryAt?]
    categoryPath := true :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · refine ⟨X, Y, Or.inl ?_⟩
        have hslash' : B.subcategoryAt? p = some (X ⧸ Y) := by
          simpa [horiginCat, horiginPos] using hslash
        simpa [Category.subcategoryAt?_rdiv_true] using hslash'
      · refine ⟨X, Y, Or.inr ?_⟩
        have hslash' : B.subcategoryAt? p = some (X ⧹ Y) := by
          simpa [horiginCat, horiginPos] using hslash
        simpa [Category.subcategoryAt?_rdiv_true] using hslash'
  }
  have hlocal : LocalTraceEdge oLeft R.origin :=
    LocalTraceEdge.appRight_B rfl rfl horiginNode horiginPos
  have hdirect : DirectedTraceEdge oLeft R.origin := by
    exact Or.inl hlocal
  have hedge : TraceEdge R.origin oLeft := Or.inr hdirect
  have hleftTarget := F.mem_dedupCategoryTargetsAt_of_traceEdge hR hedge
  simpa [oLeft] using hleftTarget

/-- In a forward application, every left-premise target must live in the
argument copy `B`; the result copy `C` and the principal root are target-free. -/
theorem appRight_left_target_starts_true
    {Γ Δ : List Category} {C B : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ B}
    {P : InvisiblePiece (DerivationTree.binary t₁ t₂ Rule.appRight)}
    (F : PieceReplacementFamilyCore P) :
    ∀ target ∈ F.dedupCategoryTargetsAt [.left],
      ∃ p, target = (true :: p, #F.atomName) := by
  intro target htarget
  obtain ⟨hpath, hnew⟩ :=
    (F.mem_dedupCategoryTargetsAt_iff [.left] target).mp htarget
  cases hpos : target.1 with
  | nil =>
      have hprincipal :
          DerivationTree.PrincipalConstructor
            (DerivationTree.binary t₁ t₂ Rule.appRight) [.left] [] :=
        DerivationTree.PrincipalConstructor.appRight_left t₁ t₂
      have hne := F.target_path_ne_of_principal hprincipal htarget
      exact False.elim (hne hpos)
  | cons b p =>
      cases b
      · have htargetEq : target = (false :: p, #F.atomName) := by
          ext <;> simp [hpos, hnew]
        have hfalse : (false :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt [.left] := by
          simpa [htargetEq] using htarget
        exact False.elim (F.appRight_no_left_result_copy_target hfalse)
      · exact ⟨p, by ext <;> simp [hpos, hnew]⟩

/-- In a forward application, left-premise argument targets are exactly the
right-premise targets at the corresponding position. -/
theorem appRight_left_true_target_iff_right_target
    {Γ Δ : List Category} {C B : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ B}
    {P : InvisiblePiece (DerivationTree.binary t₁ t₂ Rule.appRight)}
    (F : PieceReplacementFamilyCore P) (p : CategoryPath) :
    (true :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt [.left] ↔
      (p, #F.atomName) ∈ F.dedupCategoryTargetsAt [.right] :=
  ⟨F.appRight_left_arg_copy_target_to_right,
    F.appRight_right_arg_copy_target_to_left⟩

/-- Path-only form of `appRight_left_target_starts_true`. -/
theorem appRight_left_path_starts_true
    {Γ Δ : List Category} {C B : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ B}
    {P : InvisiblePiece (DerivationTree.binary t₁ t₂ Rule.appRight)}
    (F : PieceReplacementFamilyCore P) :
    ∀ p ∈ F.categoryTargetPathsAt [.left], ∃ q, p = true :: q := by
  intro p hp
  have htarget : (p, #F.atomName) ∈ F.dedupCategoryTargetsAt [.left] := by
    rw [F.mem_dedupCategoryTargetsAt_iff [.left] (p, #F.atomName)]
    exact ⟨hp, rfl⟩
  obtain ⟨q, hq⟩ := F.appRight_left_target_starts_true (p, #F.atomName) htarget
  exact ⟨q, congrArg Prod.fst hq⟩

/-- Path-only form of appRight argument-copy synchronization. -/
theorem appRight_left_true_path_iff_right_path
    {Γ Δ : List Category} {C B : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)} {t₂ : DerivationTree Δ B}
    {P : InvisiblePiece (DerivationTree.binary t₁ t₂ Rule.appRight)}
    (F : PieceReplacementFamilyCore P) (p : CategoryPath) :
    true :: p ∈ F.categoryTargetPathsAt [.left] ↔
      p ∈ F.categoryTargetPathsAt [.right] := by
  have htarget := F.appRight_left_true_target_iff_right_target p
  rw [F.mem_dedupCategoryTargetsAt_iff [.left] (true :: p, #F.atomName)] at htarget
  rw [F.mem_dedupCategoryTargetsAt_iff [.right] (p, #F.atomName)] at htarget
  simpa using htarget

/-- Root-level forward application is preserved by the canonical node rewrite:
the result copy `C` is untouched, while the left and right `B` copies are
rewritten by the same path set. -/
theorem rewrite_preserves_appRight_root
    {Γ Δ : List Category} {C B : Category}
    {t₁ : DerivationTree Γ (C ⧸ B)}
    {t₂ : DerivationTree Δ B}
    {P : InvisiblePiece (DerivationTree.binary t₁ t₂ Rule.appRight)}
    (F : PieceReplacementFamilyCore P)
    {L' R' O' : Category}
    (hL :
      F.rewriteNodeCategorySimul? [.left] (C ⧸ B) = some L')
    (hR :
      F.rewriteNodeCategorySimul? [.right] B = some R')
    (hO :
      F.rewriteNodeCategorySimul? [] C = some O') :
    Rule L' R' O' := by
  have hOeq : O' = C := by
    have hroot := F.rewriteNodeCategorySimul?_root C
    rw [hroot] at hO
    exact (Option.some.inj hO).symm
  have hLeq : L' = C ⧸ R' := by
    unfold rewriteNodeCategorySimul? at hL hR
    exact Category.replaceSimulAtPaths?_rdiv_right_only
      (F.appRight_left_path_starts_true)
      (F.appRight_left_true_path_iff_right_path)
      hR
      hL
  subst O'
  subst L'
  exact Rule.appRight

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

/-- In a backward application, replacing the right premise's `C` copy would
force a replacement at the derivation root by trace closure, contradicting
`root_free`. -/
theorem appLeft_no_right_result_copy_target
    {Γ Δ : List Category} {A C : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ (A ⧹ C)}
    {P : InvisiblePiece (DerivationTree.binary t₁ t₂ Rule.appLeft)}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath} :
    (true :: p, #F.atomName) ∉ F.dedupCategoryTargetsAt [.right] := by
  intro htarget
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff [.right] (true :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = true :: p := by
    exact (congrArg Prod.fst htargetEq).symm
  have hRcat : R.nodeCategory = A ⧹ C := by
    have hnodeAt : (DerivationTree.binary t₁ t₂ Rule.appLeft).categoryAt? R.nodePath =
        some (A ⧹ C) := by
      simp [DerivationTree.categoryAt?, hRnode]
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAt)
  have horiginNode : R.origin.nodePath = [.right] := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = true :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = A ⧹ C := by
    rw [← R.cat_eq]
    exact hRcat
  let oRoot : Occurrence (DerivationTree.binary t₁ t₂ Rule.appLeft) := {
    nodePath := []
    nodeCategory := C
    nodeAt := by simp [DerivationTree.categoryAt?]
    categoryPath := p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · refine ⟨X, Y, Or.inl ?_⟩
        have hslash' : (A ⧹ C).subcategoryAt? (true :: p) = some (X ⧸ Y) := by
          simpa [horiginCat, horiginPos] using hslash
        simpa [Category.subcategoryAt?_ldiv_true] using hslash'
      · refine ⟨X, Y, Or.inr ?_⟩
        have hslash' : (A ⧹ C).subcategoryAt? (true :: p) = some (X ⧹ Y) := by
          simpa [horiginCat, horiginPos] using hslash
        simpa [Category.subcategoryAt?_ldiv_true] using hslash'
  }
  have hlocal : LocalTraceEdge R.origin oRoot :=
    LocalTraceEdge.appLeft_C horiginNode horiginPos rfl rfl
  have hdirect : DirectedTraceEdge R.origin oRoot := by
    exact Or.inl hlocal
  have hedge : TraceEdge R.origin oRoot := Or.inl hdirect
  have hrootTarget := F.mem_dedupCategoryTargetsAt_of_traceEdge hR hedge
  simpa [oRoot, F.dedupCategoryTargetsAt_root_eq_nil] using hrootTarget

/-- In a backward application, replacing the `A` copy in the left premise
forces the matching right-premise `A` copy to be replaced. -/
theorem appLeft_left_arg_copy_target_to_right
    {Γ Δ : List Category} {A C : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ (A ⧹ C)}
    {P : InvisiblePiece (DerivationTree.binary t₁ t₂ Rule.appLeft)}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget : (p, #F.atomName) ∈ F.dedupCategoryTargetsAt [.left]) :
    (false :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt [.right] := by
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff [.left] (p, #F.atomName)).mp hprojected
  have hRpos : R.pos = p := by
    exact (congrArg Prod.fst htargetEq).symm
  have hRcat : R.nodeCategory = A := by
    have hnodeAt : (DerivationTree.binary t₁ t₂ Rule.appLeft).categoryAt? R.nodePath =
        some A := by
      simp [DerivationTree.categoryAt?, hRnode]
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAt)
  have horiginNode : R.origin.nodePath = [.left] := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = A := by
    rw [← R.cat_eq]
    exact hRcat
  let oRight : Occurrence (DerivationTree.binary t₁ t₂ Rule.appLeft) := {
    nodePath := [.right]
    nodeCategory := A ⧹ C
    nodeAt := by simp [DerivationTree.categoryAt?]
    categoryPath := false :: p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · refine ⟨X, Y, Or.inl ?_⟩
        have hslash' : A.subcategoryAt? p = some (X ⧸ Y) := by
          simpa [horiginCat, horiginPos] using hslash
        simpa [Category.subcategoryAt?_ldiv_false] using hslash'
      · refine ⟨X, Y, Or.inr ?_⟩
        have hslash' : A.subcategoryAt? p = some (X ⧹ Y) := by
          simpa [horiginCat, horiginPos] using hslash
        simpa [Category.subcategoryAt?_ldiv_false] using hslash'
  }
  have hlocal : LocalTraceEdge R.origin oRight :=
    LocalTraceEdge.appLeft_A horiginNode horiginPos rfl rfl
  have hdirect : DirectedTraceEdge R.origin oRight := by
    exact Or.inl hlocal
  have hedge : TraceEdge R.origin oRight := Or.inl hdirect
  have hrightTarget := F.mem_dedupCategoryTargetsAt_of_traceEdge hR hedge
  simpa [oRight] using hrightTarget

/-- In a backward application, replacing the right-premise `A` copy forces the
matching left-premise `A` copy to be replaced. -/
theorem appLeft_right_arg_copy_target_to_left
    {Γ Δ : List Category} {A C : Category}
    {t₁ : DerivationTree Γ A} {t₂ : DerivationTree Δ (A ⧹ C)}
    {P : InvisiblePiece (DerivationTree.binary t₁ t₂ Rule.appLeft)}
    (F : PieceReplacementFamilyCore P) {p : CategoryPath}
    (htarget : (false :: p, #F.atomName) ∈ F.dedupCategoryTargetsAt [.right]) :
    (p, #F.atomName) ∈ F.dedupCategoryTargetsAt [.left] := by
  have hprojected := F.mem_categoryTargetsAt_of_mem_dedupCategoryTargetsAt htarget
  obtain ⟨R, hR, hRnode, htargetEq⟩ :=
    (F.mem_categoryTargetsAt_iff [.right] (false :: p, #F.atomName)).mp hprojected
  have hRpos : R.pos = false :: p := by
    exact (congrArg Prod.fst htargetEq).symm
  have hRcat : R.nodeCategory = A ⧹ C := by
    have hnodeAt : (DerivationTree.binary t₁ t₂ Rule.appLeft).categoryAt? R.nodePath =
        some (A ⧹ C) := by
      simp [DerivationTree.categoryAt?, hRnode]
    exact Option.some.inj (R.nodeAt.symm.trans hnodeAt)
  have horiginNode : R.origin.nodePath = [.right] := by
    rw [← R.node_eq, hRnode]
  have horiginPos : R.origin.categoryPath = false :: p := by
    rw [← R.pos_eq, hRpos]
  have horiginCat : R.origin.nodeCategory = A ⧹ C := by
    rw [← R.cat_eq]
    exact hRcat
  let oLeft : Occurrence (DerivationTree.binary t₁ t₂ Rule.appLeft) := {
    nodePath := [.left]
    nodeCategory := A
    nodeAt := by simp [DerivationTree.categoryAt?]
    categoryPath := p
    isConstructor := by
      rcases R.origin.isConstructor with ⟨X, Y, hslash | hslash⟩
      · refine ⟨X, Y, Or.inl ?_⟩
        have hslash' : (A ⧹ C).subcategoryAt? (false :: p) = some (X ⧸ Y) := by
          simpa [horiginCat, horiginPos] using hslash
        simpa [Category.subcategoryAt?_ldiv_false] using hslash'
      · refine ⟨X, Y, Or.inr ?_⟩
        have hslash' : (A ⧹ C).subcategoryAt? (false :: p) = some (X ⧹ Y) := by
          simpa [horiginCat, horiginPos] using hslash
        simpa [Category.subcategoryAt?_ldiv_false] using hslash'
  }
  have hlocal : LocalTraceEdge oLeft R.origin :=
    LocalTraceEdge.appLeft_A rfl rfl horiginNode horiginPos
  have hdirect : DirectedTraceEdge oLeft R.origin := by
    exact Or.inl hlocal
  have hedge : TraceEdge R.origin oLeft := Or.inr hdirect
  have hleftTarget := F.mem_dedupCategoryTargetsAt_of_traceEdge hR hedge
  simpa [oLeft] using hleftTarget

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

/-- The raw paper repeatability conditions on one category branch, without yet
asserting that the branch slice transports to a contraction. -/
structure RepeatablePairOnBranch {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (o₁ o₂ : Occurrence t) where
  left_invisible : o₁.Invisible
  right_invisible : o₂.Invisible
  same_node : o₁.nodePath = o₂.nodePath
  proper_prefix : o₁.categoryPath.StrictPrefix o₂.categoryPath
  branch_interface :
    ∃ branchEnd : CategoryPath,
      o₁.categoryPath.StrictPrefix branchEnd ∧
        o₂.categoryPath.StrictPrefix branchEnd ∧
          interfaceStateOnBranch o₁ branchEnd = interfaceStateOnBranch o₂ branchEnd
  slice : BandSlice t
  slice_top : slice.topOcc = o₁
  slice_bot : slice.botOcc = o₂
  transportedSlice : BandSlice t
  same_invisible_piece : SameInvisiblePieceOnBranch slice transportedSlice
  visible_free_segment : VisibleFreeSegment o₁ o₂

/-- Backward-compatible short name while downstream files are migrated. -/
abbrev RepeatablePair {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (o₁ o₂ : Occurrence t) :=
  RepeatablePairOnBranch o₁ o₂

/-- Branch-counting-only bad repeated interface pattern.  This deliberately does
not assert the paper's same-invisible-piece transport condition, so it must not
be used as an input to `RepeatablePairHasContractionWitness`. -/
structure RepeatedInterfaceSliceOnBranch
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (o₁ o₂ : Occurrence t) : Prop where
  left_invisible : o₁.Invisible
  right_invisible : o₂.Invisible
  same_node : o₁.nodePath = o₂.nodePath
  proper_prefix : o₁.categoryPath.StrictPrefix o₂.categoryPath
  branch_interface :
    ∃ branchEnd : CategoryPath,
      o₁.categoryPath.StrictPrefix branchEnd ∧
        o₂.categoryPath.StrictPrefix branchEnd ∧
          interfaceStateOnBranch o₁ branchEnd = interfaceStateOnBranch o₂ branchEnd
  visible_free_segment : VisibleFreeSegment o₁ o₂

namespace RepeatedInterfaceSliceOnBranch

/-- Build the branch-counting-only repeated-interface predicate from one
visible-free slice.  This is intentionally weaker than `RepeatablePairOnBranch`:
it uses no invisible-piece transport evidence. -/
theorem ofSlice {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (S : BandSlice t) (branchEnd : CategoryPath)
    (htop : S.topOcc.categoryPath.StrictPrefix branchEnd)
    (hbot : S.botOcc.categoryPath.StrictPrefix branchEnd)
    (hinterface :
      interfaceStateOnBranch S.topOcc branchEnd =
        interfaceStateOnBranch S.botOcc branchEnd) :
    RepeatedInterfaceSliceOnBranch S.topOcc S.botOcc where
  left_invisible := S.top_invisible
  right_invisible := S.bot_invisible
  same_node := S.same_node
  proper_prefix := S.strict
  branch_interface := ⟨branchEnd, htop, hbot, hinterface⟩
  visible_free_segment := S.removed_invisible

end RepeatedInterfaceSliceOnBranch

namespace RepeatablePair

/-- A raw repeatable pair determines the visible-free branch zone between its
two repeated occurrences. -/
theorem visibleFreeZone {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ : Occurrence t} (h : RepeatablePair o₁ o₂) :
    VisibleFreeZone o₁ o₂ where
  same_node := h.same_node
  proper_prefix := h.proper_prefix
  visible_free := h.visible_free_segment

/-- A raw repeatable pair carries the branch-sensitive interface equality used
by the paper's repeated-state test. -/
theorem sameBranchInterface {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ : Occurrence t} (h : RepeatablePair o₁ o₂) :
    SameBranchInterface o₁ o₂ :=
  h.branch_interface

end RepeatablePair

/-- Occurrence-indexed repeatable pair with an explicit contraction witness.

The paper's raw repeatability conditions are: same invisible trace piece, same
interface state, proper ancestor relation on one branch, and a visible-free
branch segment.  This proof-carrying variant additionally stores the resulting
contraction step.  Thus no graph-to-band implication is hidden as an axiom
while the full paper `rep-band` proof is being developed. -/
structure ContractingRepeatablePair {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (o₁ o₂ : Occurrence t) where
  left_invisible : o₁.Invisible
  right_invisible : o₂.Invisible
  same_node : o₁.nodePath = o₂.nodePath
  proper_prefix : o₁.categoryPath.StrictPrefix o₂.categoryPath
  branch_interface :
    ∃ branchEnd : CategoryPath,
      o₁.categoryPath.StrictPrefix branchEnd ∧
        o₂.categoryPath.StrictPrefix branchEnd ∧
          interfaceStateOnBranch o₁ branchEnd = interfaceStateOnBranch o₂ branchEnd
  slice : BandSlice t
  slice_top : slice.topOcc = o₁
  slice_bot : slice.botOcc = o₂
  transportedSlice : BandSlice t
  same_invisible_piece : SameInvisiblePieceOnBranch slice transportedSlice
  visible_free_segment : VisibleFreeSegment o₁ o₂
  contraction : ContractionWitness t

/-- Forget the current contraction witness and retain only the raw paper
repeatability conditions. -/
def ContractingRepeatablePair.toRepeatablePair {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ : Occurrence t} (h : ContractingRepeatablePair o₁ o₂) :
    RepeatablePair o₁ o₂ where
  left_invisible := h.left_invisible
  right_invisible := h.right_invisible
  same_node := h.same_node
  proper_prefix := h.proper_prefix
  branch_interface := h.branch_interface
  slice := h.slice
  slice_top := h.slice_top
  slice_bot := h.slice_bot
  transportedSlice := h.transportedSlice
  same_invisible_piece := h.same_invisible_piece
  visible_free_segment := h.visible_free_segment

/-- Convenience predicate: a tree has at least one occurrence-indexed
repeatable pair with an explicit contraction witness. -/
def HasContractingRepeatablePair {Γ : List Category} {A : Category} (t : DerivationTree Γ A) : Prop :=
  ∃ o₁ o₂ : Occurrence t, Nonempty (ContractingRepeatablePair o₁ o₂)

/-- The tree has a raw paper repeatable pair, without a contraction witness. -/
def HasRepeatablePair {Γ : List Category} {A : Category} (t : DerivationTree Γ A) : Prop :=
  ∃ o₁ o₂ : Occurrence t, Nonempty (RepeatablePair o₁ o₂)

/-- Explicit branch-qualified spelling for the raw repeatable-pair predicate. -/
abbrev HasRepeatablePairOnBranch {Γ : List Category} {A : Category}
    (t : DerivationTree Γ A) : Prop :=
  HasRepeatablePair t

/-- Every proof-carrying repeatable pair is in particular a raw paper
repeatable pair. -/
theorem HasContractingRepeatablePair.toRepeatablePair {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (h : HasContractingRepeatablePair t) : HasRepeatablePair t := by
  obtain ⟨o₁, o₂, ⟨hp⟩⟩ := h
  exact ⟨o₁, o₂, ⟨hp.toRepeatablePair⟩⟩

/-- The exact remaining band-contraction theorem target: every raw paper
repeatable pair transports to a band.  This is kept as a `Prop` definition, not
an axiom, so downstream theorems can state precisely which proof is still
needed. -/
def AllRepeatablePairsContract : Prop :=
  ∀ {Γ : List Category} {A : Category} {t : DerivationTree Γ A} {o₁ o₂ : Occurrence t},
    RepeatablePair o₁ o₂ → Nonempty (ContractionWitness t)

/-- Faithful paper-facing band theorem target: every raw repeatable pair first
produces a transport-closed band. -/
def RepeatablePairProducesBand : Prop :=
  ∀ {Γ : List Category} {A : Category} {t : DerivationTree Γ A} {o₁ o₂ : Occurrence t},
    RepeatablePair o₁ o₂ → Nonempty (TransportClosedBand t)

/-- Local proof target for `rep-band`: enrich every raw repeatable pair with an
explicit contraction witness.  This is slightly stronger than
`RepeatablePairProducesBand`, but its fields match the data used by concrete
band-construction proofs. -/
def RepeatablePairHasContractionWitness : Prop :=
  ∀ {Γ : List Category} {A : Category} {t : DerivationTree Γ A} {o₁ o₂ : Occurrence t},
    (h : RepeatablePair o₁ o₂) → Nonempty (ContractionWitness t)

/-- A contraction witness for every raw repeatable pair gives the paper-facing
transport-closed band theorem. -/
theorem repeatablePairProducesBand_of_contractionWitness
    (hwitness : RepeatablePairHasContractionWitness) :
    RepeatablePairProducesBand := by
  intro Γ A t o₁ o₂ hpair
  obtain ⟨w⟩ := hwitness hpair
  exact ⟨TransportClosedBand.ofContractionWitness w⟩

/-- The paper-facing band theorem implies the contraction-target interface used
by the existing minimality lemmas. -/
theorem allRepeatablePairsContract_of_repeatablePairProducesBand
    (hband : RepeatablePairProducesBand) : AllRepeatablePairsContract := by
  intro Γ A t o₁ o₂ hpair
  obtain ⟨B⟩ := hband hpair
  exact ⟨B.toContractionWitness⟩

/-- If the real paper `rep-band` theorem has been proved, then any raw paper
repeatable pair contracts to a smaller derivation tree. -/
theorem repeatablePair_contract_of_contractibility
    (hrep : AllRepeatablePairsContract)
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A} {o₁ o₂ : Occurrence t}
    (h : RepeatablePair o₁ o₂) :
    ∃ t' : DerivationTree Γ A, t'.size < t.size := by
  obtain ⟨w⟩ := hrep h
  exact ⟨w.target, w.size_lt⟩

/-- If the real paper `rep-band` theorem has been proved, then a tree with a
raw paper repeatable pair contracts. -/
theorem hasRepeatablePair_contract_of_contractibility
    (hrep : AllRepeatablePairsContract)
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (h : HasRepeatablePair t) :
    ∃ t' : DerivationTree Γ A, t'.size < t.size := by
  obtain ⟨o₁, o₂, hp⟩ := h
  obtain ⟨hp⟩ := hp
  exact repeatablePair_contract_of_contractibility hrep hp

/-- A bare contraction step induces an occurrence-free band redex.  This is
useful for examples where the redex is obvious and the concrete trace
occurrences are not important. -/
def HasBandRedex {Γ : List Category} {A : Category} (t : DerivationTree Γ A) : Prop :=
  ∃ t' : DerivationTree Γ A, Contracts t t'

/-- A bare band redex gives the common contraction witness used by the
boundary-free piece arguments. -/
theorem contractionWitness_of_hasBandRedex
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (h : HasBandRedex t) :
    Nonempty (ContractionWitness t) := by
  obtain ⟨t', hc⟩ := h
  exact ⟨hc.toContractionWitness⟩

/-- The forward type-raising/application collapse is a bare band redex. -/
theorem hasBandRedex_collapseRight
    {Γ Δ : List Category} {A C : Category}
    (s : DerivationTree Γ A) (w : DerivationTree Δ (A ⧹ C)) :
    HasBandRedex
      (DerivationTree.binary (DerivationTree.typeRaiseRight C s) w Rule.appRight) :=
  ⟨DerivationTree.binary s w Rule.appLeft, Contracts.collapseRight s w⟩

/-- The backward type-raising/application collapse is a bare band redex. -/
theorem hasBandRedex_collapseLeft
    {Γ Δ : List Category} {A C : Category}
    (w : DerivationTree Δ (C ⧸ A)) (s : DerivationTree Γ A) :
    HasBandRedex
      (DerivationTree.binary w (DerivationTree.typeRaiseLeft C s) Rule.appLeft) :=
  ⟨DerivationTree.binary w s Rule.appRight, Contracts.collapseLeft w s⟩

/-- The forward collapse redex directly supplies a contraction witness. -/
theorem contractionWitness_collapseRight
    {Γ Δ : List Category} {A C : Category}
    (s : DerivationTree Γ A) (w : DerivationTree Δ (A ⧹ C)) :
    Nonempty (ContractionWitness
      (DerivationTree.binary (DerivationTree.typeRaiseRight C s) w Rule.appRight)) :=
  contractionWitness_of_hasBandRedex (hasBandRedex_collapseRight s w)

/-- The backward collapse redex directly supplies a contraction witness. -/
theorem contractionWitness_collapseLeft
    {Γ Δ : List Category} {A C : Category}
    (w : DerivationTree Δ (C ⧸ A)) (s : DerivationTree Γ A) :
    Nonempty (ContractionWitness
      (DerivationTree.binary w (DerivationTree.typeRaiseLeft C s) Rule.appLeft)) :=
  contractionWitness_of_hasBandRedex (hasBandRedex_collapseLeft w s)

/-- A boundary-free protected-skeleton occurrence inside the forward collapse
redex is dispatched by the redex contraction itself.  This is the protected
piece case for `T>` feeding forward application. -/
theorem contractionWitness_of_boundaryFree_protectedSkeleton_collapseRight
    {Γ Δ : List Category} {A C : Category}
    (s : DerivationTree Γ A) (w : DerivationTree Δ (A ⧹ C))
    {P : InvisiblePiece
      (DerivationTree.binary (DerivationTree.typeRaiseRight C s) w Rule.appRight)}
    (_hfree : BoundaryFree P)
    {o : Occurrence
      (DerivationTree.binary (DerivationTree.typeRaiseRight C s) w Rule.appRight)}
    (_ho : o ∈ P.carrier)
    (_hprot : o.ProtectedUnarySkeleton) :
    Nonempty (ContractionWitness
      (DerivationTree.binary (DerivationTree.typeRaiseRight C s) w Rule.appRight)) :=
  contractionWitness_collapseRight s w

/-- A boundary-free protected-skeleton occurrence inside the backward collapse
redex is dispatched by the redex contraction itself.  This is the protected
piece case for `T<` feeding backward application. -/
theorem contractionWitness_of_boundaryFree_protectedSkeleton_collapseLeft
    {Γ Δ : List Category} {A C : Category}
    (w : DerivationTree Δ (C ⧸ A)) (s : DerivationTree Γ A)
    {P : InvisiblePiece
      (DerivationTree.binary w (DerivationTree.typeRaiseLeft C s) Rule.appLeft)}
    (_hfree : BoundaryFree P)
    {o : Occurrence
      (DerivationTree.binary w (DerivationTree.typeRaiseLeft C s) Rule.appLeft)}
    (_ho : o ∈ P.carrier)
    (_hprot : o.ProtectedUnarySkeleton) :
    Nonempty (ContractionWitness
      (DerivationTree.binary w (DerivationTree.typeRaiseLeft C s) Rule.appLeft)) :=
  contractionWitness_collapseLeft w s

namespace Occurrence

/-- If a constructor occurrence is the root of the child category in a forward
type-raising node, then its lifted occurrence has a visible boundary at the
type-raising output root. -/
theorem hasVisibleBoundary_underUnaryRight_of_root
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (C : Category) (o : Occurrence t)
    (hroot : o.nodePath = [])
    (hinv : (DerivationTree.CategoryOccurrence.underUnaryRight C o).Invisible) :
    HasVisibleBoundary (DerivationTree.CategoryOccurrence.underUnaryRight C o) := by
  have hcat : o.nodeCategory = A := by
    apply Option.some.inj
    calc
      some o.nodeCategory = t.categoryAt? o.nodePath := by rw [o.nodeAt]
      _ = t.categoryAt? [] := by rw [hroot]
      _ = some A := by rw [DerivationTree.categoryAt?_root]
  let lifted : Occurrence (DerivationTree.typeRaiseRight C t) :=
    DerivationTree.CategoryOccurrence.underUnaryRight C o
  let v : Occurrence (DerivationTree.typeRaiseRight C t) := {
    nodePath := []
    nodeCategory := C ⧸ (A ⧹ C)
    nodeAt := DerivationTree.categoryAt?_root (DerivationTree.typeRaiseRight C t)
    categoryPath := true :: false :: o.categoryPath
    isConstructor := by
      rcases o.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_rdiv_true, Category.subcategoryAt?_ldiv_false, hcat]
            using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_rdiv_true, Category.subcategoryAt?_ldiv_false, hcat]
            using hslash)⟩
  }
  refine ⟨lifted, v, SameInvisibleTraceComponent.refl lifted, hinv, ?_, ?_⟩
  · exact Or.inl rfl
  · exact Or.inl (Or.inl (LocalTraceEdge.trRight_A
      (by simp [lifted, DerivationTree.CategoryOccurrence.underUnaryRight, hroot])
      rfl rfl rfl))

/-- If a constructor occurrence is the root of the child category in a backward
type-raising node, then its lifted occurrence has a visible boundary at the
type-raising output root. -/
theorem hasVisibleBoundary_underUnaryLeft_of_root
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (C : Category) (o : Occurrence t)
    (hroot : o.nodePath = [])
    (hinv : (DerivationTree.CategoryOccurrence.underUnaryLeft C o).Invisible) :
    HasVisibleBoundary (DerivationTree.CategoryOccurrence.underUnaryLeft C o) := by
  have hcat : o.nodeCategory = A := by
    apply Option.some.inj
    calc
      some o.nodeCategory = t.categoryAt? o.nodePath := by rw [o.nodeAt]
      _ = t.categoryAt? [] := by rw [hroot]
      _ = some A := by rw [DerivationTree.categoryAt?_root]
  let lifted : Occurrence (DerivationTree.typeRaiseLeft C t) :=
    DerivationTree.CategoryOccurrence.underUnaryLeft C o
  let v : Occurrence (DerivationTree.typeRaiseLeft C t) := {
    nodePath := []
    nodeCategory := (C ⧸ A) ⧹ C
    nodeAt := DerivationTree.categoryAt?_root (DerivationTree.typeRaiseLeft C t)
    categoryPath := false :: true :: o.categoryPath
    isConstructor := by
      rcases o.isConstructor with ⟨X, Y, hslash | hslash⟩
      · exact ⟨X, Y, Or.inl (by
          simpa [Category.subcategoryAt?_ldiv_false, Category.subcategoryAt?_rdiv_true, hcat]
            using hslash)⟩
      · exact ⟨X, Y, Or.inr (by
          simpa [Category.subcategoryAt?_ldiv_false, Category.subcategoryAt?_rdiv_true, hcat]
            using hslash)⟩
  }
  refine ⟨lifted, v, SameInvisibleTraceComponent.refl lifted, hinv, ?_, ?_⟩
  · exact Or.inl rfl
  · exact Or.inl (Or.inl (LocalTraceEdge.trLeft_A
      (by simp [lifted, DerivationTree.CategoryOccurrence.underUnaryLeft, hroot])
      rfl rfl rfl))

end Occurrence

namespace Occurrence

/-- Invisible occurrences remain invisible when lifted through a forward
type-raising context. -/
theorem invisible_underUnaryRight_of_invisible
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (C : Category) {o : Occurrence t} (hinv : o.Invisible) :
    (DerivationTree.CategoryOccurrence.underUnaryRight C o).Invisible := by
  intro hvis
  rcases hvis with hroot | hleaf | hprincipal
  · cases hroot
  · exact hinv (Or.inr (Or.inl (by
      simpa [DerivationTree.isLeafNode,
        DerivationTree.CategoryOccurrence.underUnaryRight] using hleaf)))
  · cases hprincipal with
    | underUnaryRight _ h =>
        exact hinv (Or.inr (Or.inr h))

/-- Invisible occurrences remain invisible when lifted through a backward
type-raising context. -/
theorem invisible_underUnaryLeft_of_invisible
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (C : Category) {o : Occurrence t} (hinv : o.Invisible) :
    (DerivationTree.CategoryOccurrence.underUnaryLeft C o).Invisible := by
  intro hvis
  rcases hvis with hroot | hleaf | hprincipal
  · cases hroot
  · exact hinv (Or.inr (Or.inl (by
      simpa [DerivationTree.isLeafNode,
        DerivationTree.CategoryOccurrence.underUnaryLeft] using hleaf)))
  · cases hprincipal with
    | underUnaryLeft _ h =>
        exact hinv (Or.inr (Or.inr h))

end Occurrence

namespace InvisibleTraceEdge

/-- Invisible trace edges lift through a forward type-raising context. -/
theorem underUnaryRight
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ : Occurrence t} (C : Category)
    (h : InvisibleTraceEdge o₁ o₂) :
    InvisibleTraceEdge
      (DerivationTree.CategoryOccurrence.underUnaryRight C o₁)
      (DerivationTree.CategoryOccurrence.underUnaryRight C o₂) :=
  ⟨Occurrence.invisible_underUnaryRight_of_invisible C h.left_invisible,
    Occurrence.invisible_underUnaryRight_of_invisible C h.right_invisible,
    TraceEdge.underUnaryRight C h.traceEdge⟩

/-- Invisible trace edges lift through a backward type-raising context. -/
theorem underUnaryLeft
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ : Occurrence t} (C : Category)
    (h : InvisibleTraceEdge o₁ o₂) :
    InvisibleTraceEdge
      (DerivationTree.CategoryOccurrence.underUnaryLeft C o₁)
      (DerivationTree.CategoryOccurrence.underUnaryLeft C o₂) :=
  ⟨Occurrence.invisible_underUnaryLeft_of_invisible C h.left_invisible,
    Occurrence.invisible_underUnaryLeft_of_invisible C h.right_invisible,
    TraceEdge.underUnaryLeft C h.traceEdge⟩

end InvisibleTraceEdge

namespace SameInvisibleTraceComponent

/-- Invisible trace components lift through a forward type-raising context. -/
theorem underUnaryRight
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ : Occurrence t} (C : Category)
    (h : SameInvisibleTraceComponent o₁ o₂) :
    SameInvisibleTraceComponent
      (DerivationTree.CategoryOccurrence.underUnaryRight C o₁)
      (DerivationTree.CategoryOccurrence.underUnaryRight C o₂) := by
  induction h with
  | refl => exact SameInvisibleTraceComponent.refl _
  | tail _ hedge ih =>
      exact Relation.ReflTransGen.tail ih (InvisibleTraceEdge.underUnaryRight C hedge)

/-- Invisible trace components lift through a backward type-raising context. -/
theorem underUnaryLeft
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ : Occurrence t} (C : Category)
    (h : SameInvisibleTraceComponent o₁ o₂) :
    SameInvisibleTraceComponent
      (DerivationTree.CategoryOccurrence.underUnaryLeft C o₁)
      (DerivationTree.CategoryOccurrence.underUnaryLeft C o₂) := by
  induction h with
  | refl => exact SameInvisibleTraceComponent.refl _
  | tail _ hedge ih =>
      exact Relation.ReflTransGen.tail ih (InvisibleTraceEdge.underUnaryLeft C hedge)

end SameInvisibleTraceComponent

namespace HasVisibleBoundary

/-- Visible-boundary witnesses lift through a forward type-raising context.
When the visible endpoint in the child is the child root, its lifted occurrence
may cease to be visible; in that case the type-raising output root supplies the
visible boundary through the local `T>` trace edge. -/
theorem underUnaryRight
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o : Occurrence t} (C : Category)
    (h : HasVisibleBoundary o) :
    HasVisibleBoundary (DerivationTree.CategoryOccurrence.underUnaryRight C o) := by
  rcases h with ⟨p, v, hcomp, hpInv, hv, hedge⟩
  let lp : Occurrence (DerivationTree.typeRaiseRight C t) :=
    DerivationTree.CategoryOccurrence.underUnaryRight C p
  let lv : Occurrence (DerivationTree.typeRaiseRight C t) :=
    DerivationTree.CategoryOccurrence.underUnaryRight C v
  have hcompLift :
      SameInvisibleTraceComponent
        (DerivationTree.CategoryOccurrence.underUnaryRight C o) lp := by
    simpa [lp] using SameInvisibleTraceComponent.underUnaryRight C hcomp
  have hpLiftInv : lp.Invisible := by
    simpa [lp] using Occurrence.invisible_underUnaryRight_of_invisible C hpInv
  by_cases hvLift : lv.Visible
  · exact ⟨lp, lv, hcompLift, hpLiftInv, hvLift, by
      simpa [lp, lv] using TraceEdge.underUnaryRight C hedge⟩
  · rcases hv with hroot | hleaf | hprincipal
    · have hedgeLift : TraceEdge lp lv := by
        simpa [lp, lv] using TraceEdge.underUnaryRight C hedge
      have htoLv :
          SameInvisibleTraceComponent
            (DerivationTree.CategoryOccurrence.underUnaryRight C o) lv :=
        Relation.ReflTransGen.tail hcompLift ⟨hpLiftInv, hvLift, hedgeLift⟩
      rcases Occurrence.hasVisibleBoundary_underUnaryRight_of_root C v hroot hvLift with
        ⟨q, w, hq, hqInv, hw, hqw⟩
      exact ⟨q, w, SameInvisibleTraceComponent.trans htoLv hq, hqInv, hw, hqw⟩
    · exact False.elim (hvLift (Or.inr (Or.inl (by
        simpa [DerivationTree.isLeafNode, lv,
          DerivationTree.CategoryOccurrence.underUnaryRight] using hleaf))))
    · exact False.elim (hvLift (Or.inr (Or.inr
        (DerivationTree.PrincipalConstructor.underUnaryRight C hprincipal))))

/-- Visible-boundary witnesses lift through a backward type-raising context.
When the visible endpoint in the child is the child root, its lifted occurrence
may cease to be visible; in that case the type-raising output root supplies the
visible boundary through the local `T<` trace edge. -/
theorem underUnaryLeft
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o : Occurrence t} (C : Category)
    (h : HasVisibleBoundary o) :
    HasVisibleBoundary (DerivationTree.CategoryOccurrence.underUnaryLeft C o) := by
  rcases h with ⟨p, v, hcomp, hpInv, hv, hedge⟩
  let lp : Occurrence (DerivationTree.typeRaiseLeft C t) :=
    DerivationTree.CategoryOccurrence.underUnaryLeft C p
  let lv : Occurrence (DerivationTree.typeRaiseLeft C t) :=
    DerivationTree.CategoryOccurrence.underUnaryLeft C v
  have hcompLift :
      SameInvisibleTraceComponent
        (DerivationTree.CategoryOccurrence.underUnaryLeft C o) lp := by
    simpa [lp] using SameInvisibleTraceComponent.underUnaryLeft C hcomp
  have hpLiftInv : lp.Invisible := by
    simpa [lp] using Occurrence.invisible_underUnaryLeft_of_invisible C hpInv
  by_cases hvLift : lv.Visible
  · exact ⟨lp, lv, hcompLift, hpLiftInv, hvLift, by
      simpa [lp, lv] using TraceEdge.underUnaryLeft C hedge⟩
  · rcases hv with hroot | hleaf | hprincipal
    · have hedgeLift : TraceEdge lp lv := by
        simpa [lp, lv] using TraceEdge.underUnaryLeft C hedge
      have htoLv :
          SameInvisibleTraceComponent
            (DerivationTree.CategoryOccurrence.underUnaryLeft C o) lv :=
        Relation.ReflTransGen.tail hcompLift ⟨hpLiftInv, hvLift, hedgeLift⟩
      rcases Occurrence.hasVisibleBoundary_underUnaryLeft_of_root C v hroot hvLift with
        ⟨q, w, hq, hqInv, hw, hqw⟩
      exact ⟨q, w, SameInvisibleTraceComponent.trans htoLv hq, hqInv, hw, hqw⟩
    · exact False.elim (hvLift (Or.inr (Or.inl (by
        simpa [DerivationTree.isLeafNode, lv,
          DerivationTree.CategoryOccurrence.underUnaryLeft] using hleaf))))
    · exact False.elim (hvLift (Or.inr (Or.inr
        (DerivationTree.PrincipalConstructor.underUnaryLeft C hprincipal))))

end HasVisibleBoundary

namespace InvisiblePiece

/-- A boundary-free piece in a forward type-raising tree cannot contain the
lift of a root occurrence of the child category: that occurrence has the
type-raising output root as a visible boundary. -/
theorem false_of_underUnaryRight_root_mem_boundaryFree
    {Γ : List Category} {A C : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece (DerivationTree.typeRaiseRight C t)}
    (hfree : BoundaryFree P)
    (o : Occurrence t)
    (hroot : o.nodePath = [])
    (ho : DerivationTree.CategoryOccurrence.underUnaryRight C o ∈ P.carrier) :
    False := by
  have hinv : (DerivationTree.CategoryOccurrence.underUnaryRight C o).Invisible :=
    P.all_invisible _ ho
  exact P.no_hasVisibleBoundary_of_boundaryFree hfree ho
    (Occurrence.hasVisibleBoundary_underUnaryRight_of_root C o hroot hinv)

/-- A boundary-free piece in a backward type-raising tree cannot contain the
lift of a root occurrence of the child category: that occurrence has the
type-raising output root as a visible boundary. -/
theorem false_of_underUnaryLeft_root_mem_boundaryFree
    {Γ : List Category} {A C : Category} {t : DerivationTree Γ A}
    {P : InvisiblePiece (DerivationTree.typeRaiseLeft C t)}
    (hfree : BoundaryFree P)
    (o : Occurrence t)
    (hroot : o.nodePath = [])
    (ho : DerivationTree.CategoryOccurrence.underUnaryLeft C o ∈ P.carrier) :
    False := by
  have hinv : (DerivationTree.CategoryOccurrence.underUnaryLeft C o).Invisible :=
    P.all_invisible _ ho
  exact P.no_hasVisibleBoundary_of_boundaryFree hfree ho
    (Occurrence.hasVisibleBoundary_underUnaryLeft_of_root C o hroot hinv)

end InvisiblePiece

namespace HasBandRedex

/-- A redex in the child of a forward type-raising node lifts to the whole
tree. -/
theorem typeRaiseRight
    {Γ : List Category} {A : Category} {s : DerivationTree Γ A}
    (C : Category) (h : HasBandRedex s) :
    HasBandRedex (DerivationTree.typeRaiseRight C s) := by
  obtain ⟨s', hs⟩ := h
  exact ⟨DerivationTree.typeRaiseRight C s', Contracts.typeRaiseRight C hs⟩

/-- A redex in the child of a backward type-raising node lifts to the whole
tree. -/
theorem typeRaiseLeft
    {Γ : List Category} {A : Category} {s : DerivationTree Γ A}
    (C : Category) (h : HasBandRedex s) :
    HasBandRedex (DerivationTree.typeRaiseLeft C s) := by
  obtain ⟨s', hs⟩ := h
  exact ⟨DerivationTree.typeRaiseLeft C s', Contracts.typeRaiseLeft C hs⟩

/-- A redex in the left premise of a binary rule lifts to the whole tree. -/
theorem binaryLeft
    {Γ Δ : List Category} {A B C : Category}
    {t₁ : DerivationTree Γ A} (t₂ : DerivationTree Δ B)
    (r : Rule A B C) (h : HasBandRedex t₁) :
    HasBandRedex (DerivationTree.binary t₁ t₂ r) := by
  obtain ⟨t₁', ht₁⟩ := h
  exact ⟨DerivationTree.binary t₁' t₂ r, Contracts.binaryLeft t₂ r ht₁⟩

/-- A redex in the right premise of a binary rule lifts to the whole tree. -/
theorem binaryRight
    {Γ Δ : List Category} {A B C : Category}
    (t₁ : DerivationTree Γ A) {t₂ : DerivationTree Δ B}
    (r : Rule A B C) (h : HasBandRedex t₂) :
    HasBandRedex (DerivationTree.binary t₁ t₂ r) := by
  obtain ⟨t₂', ht₂⟩ := h
  exact ⟨DerivationTree.binary t₁ t₂' r, Contracts.binaryRight t₁ r ht₂⟩

end HasBandRedex

/-- Unary protected-skeleton analysis through a forward type-raising frame.

This is the type-raising context case of the protected-skeleton band argument:
a protected skeleton occurrence under the child either exposes a child band
redex, which lifts through the frame, or already has a visible boundary, which
also lifts through the frame.  If the child occurrence is the child root, the
new type-raising output root gives the visible boundary directly. -/
theorem protectedSkeleton_contracts_or_boundary_underTypeRaiseRight
    {Γ : List Category} {A : Category} (C : Category)
    (t : DerivationTree Γ A)
    (IH : ∀ o : Occurrence t,
      o.ProtectedUnarySkeleton → o.Invisible →
        HasBandRedex t ∨ HasVisibleBoundary o)
    (o : Occurrence (DerivationTree.typeRaiseRight C t))
    (hprot : o.ProtectedUnarySkeleton)
    (hinv : o.Invisible) :
    HasBandRedex (DerivationTree.typeRaiseRight C t) ∨ HasVisibleBoundary o := by
  rcases o with ⟨nodePath, nodeCategory, nodeAt, categoryPath, isConstructor⟩
  change DerivationTree.UnarySkeletonConstructor
    (DerivationTree.typeRaiseRight C t) nodePath categoryPath at hprot
  cases hprot with
  | trRight_outer t =>
      exact False.elim (hinv (Or.inl rfl))
  | trRight_inner t =>
      exact False.elim (hinv (Or.inl rfl))
  | underUnaryRight C hchild =>
      let child : Occurrence t := {
        nodePath := _
        nodeCategory := nodeCategory
        nodeAt := by
          simpa [DerivationTree.categoryAt?] using nodeAt
        categoryPath := categoryPath
        isConstructor := isConstructor
      }
      by_cases hroot : child.nodePath = []
      · have hboundary :
            HasVisibleBoundary
              (DerivationTree.CategoryOccurrence.underUnaryRight C child) :=
          Occurrence.hasVisibleBoundary_underUnaryRight_of_root C child hroot
            (by
              simpa [child, DerivationTree.CategoryOccurrence.underUnaryRight]
                using hinv)
        exact Or.inr (by
          simpa [child, DerivationTree.CategoryOccurrence.underUnaryRight]
            using hboundary)
      · have hchildInv : child.Invisible := by
          intro hv
          rcases hv with hchildRoot | hchildLeaf | hchildPrincipal
          · exact hroot hchildRoot
          · exact hinv (Or.inr (Or.inl (by
              simpa [child, DerivationTree.isLeafNode] using hchildLeaf)))
          · exact hinv (Or.inr (Or.inr
              (DerivationTree.PrincipalConstructor.underUnaryRight C
                hchildPrincipal)))
        have hchildProt : child.ProtectedUnarySkeleton := by
          simpa [Occurrence.ProtectedUnarySkeleton,
            DerivationTree.CategoryOccurrence.ProtectedUnarySkeleton, child]
            using hchild
        rcases IH child hchildProt hchildInv with hred | hboundary
        · exact Or.inl (HasBandRedex.typeRaiseRight C hred)
        · exact Or.inr (by
            simpa [child, DerivationTree.CategoryOccurrence.underUnaryRight]
              using HasVisibleBoundary.underUnaryRight C hboundary)

/-- Unary protected-skeleton analysis through a backward type-raising frame.

This is the backward analogue of
`protectedSkeleton_contracts_or_boundary_underTypeRaiseRight`. -/
theorem protectedSkeleton_contracts_or_boundary_underTypeRaiseLeft
    {Γ : List Category} {A : Category} (C : Category)
    (t : DerivationTree Γ A)
    (IH : ∀ o : Occurrence t,
      o.ProtectedUnarySkeleton → o.Invisible →
        HasBandRedex t ∨ HasVisibleBoundary o)
    (o : Occurrence (DerivationTree.typeRaiseLeft C t))
    (hprot : o.ProtectedUnarySkeleton)
    (hinv : o.Invisible) :
    HasBandRedex (DerivationTree.typeRaiseLeft C t) ∨ HasVisibleBoundary o := by
  rcases o with ⟨nodePath, nodeCategory, nodeAt, categoryPath, isConstructor⟩
  change DerivationTree.UnarySkeletonConstructor
    (DerivationTree.typeRaiseLeft C t) nodePath categoryPath at hprot
  cases hprot with
  | trLeft_outer t =>
      exact False.elim (hinv (Or.inl rfl))
  | trLeft_inner t =>
      exact False.elim (hinv (Or.inl rfl))
  | underUnaryLeft C hchild =>
      let child : Occurrence t := {
        nodePath := _
        nodeCategory := nodeCategory
        nodeAt := by
          simpa [DerivationTree.categoryAt?] using nodeAt
        categoryPath := categoryPath
        isConstructor := isConstructor
      }
      by_cases hroot : child.nodePath = []
      · have hboundary :
            HasVisibleBoundary
              (DerivationTree.CategoryOccurrence.underUnaryLeft C child) :=
          Occurrence.hasVisibleBoundary_underUnaryLeft_of_root C child hroot
            (by
              simpa [child, DerivationTree.CategoryOccurrence.underUnaryLeft]
                using hinv)
        exact Or.inr (by
          simpa [child, DerivationTree.CategoryOccurrence.underUnaryLeft]
            using hboundary)
      · have hchildInv : child.Invisible := by
          intro hv
          rcases hv with hchildRoot | hchildLeaf | hchildPrincipal
          · exact hroot hchildRoot
          · exact hinv (Or.inr (Or.inl (by
              simpa [child, DerivationTree.isLeafNode] using hchildLeaf)))
          · exact hinv (Or.inr (Or.inr
              (DerivationTree.PrincipalConstructor.underUnaryLeft C
                hchildPrincipal)))
        have hchildProt : child.ProtectedUnarySkeleton := by
          simpa [Occurrence.ProtectedUnarySkeleton,
            DerivationTree.CategoryOccurrence.ProtectedUnarySkeleton, child]
            using hchild
        rcases IH child hchildProt hchildInv with hred | hboundary
        · exact Or.inl (HasBandRedex.typeRaiseLeft C hred)
        · exact Or.inr (by
            simpa [child, DerivationTree.CategoryOccurrence.underUnaryLeft]
              using HasVisibleBoundary.underUnaryLeft C hboundary)

/-- Boundary-free protected-skeleton contraction through a forward
type-raising frame, assuming the child protected-skeleton analysis is already
available.  The visible-boundary alternative contradicts boundary-freeness, and
the redex alternative gives the common contraction witness. -/
theorem contractionWitness_of_boundaryFree_protectedSkeleton_underTypeRaiseRight
    {Γ : List Category} {A : Category} (C : Category)
    (t : DerivationTree Γ A)
    (IH : ∀ o : Occurrence t,
      o.ProtectedUnarySkeleton → o.Invisible →
        HasBandRedex t ∨ HasVisibleBoundary o)
    {P : InvisiblePiece (DerivationTree.typeRaiseRight C t)}
    (hfree : BoundaryFree P)
    {o : Occurrence (DerivationTree.typeRaiseRight C t)}
    (ho : o ∈ P.carrier)
    (hprot : o.ProtectedUnarySkeleton) :
    Nonempty (ContractionWitness (DerivationTree.typeRaiseRight C t)) := by
  have hinv : o.Invisible := P.all_invisible o ho
  rcases protectedSkeleton_contracts_or_boundary_underTypeRaiseRight
      C t IH o hprot hinv with hred | hboundary
  · exact contractionWitness_of_hasBandRedex hred
  · exact False.elim (P.no_hasVisibleBoundary_of_boundaryFree hfree ho hboundary)

/-- Boundary-free protected-skeleton contraction through a backward
type-raising frame, assuming the child protected-skeleton analysis is already
available. -/
theorem contractionWitness_of_boundaryFree_protectedSkeleton_underTypeRaiseLeft
    {Γ : List Category} {A : Category} (C : Category)
    (t : DerivationTree Γ A)
    (IH : ∀ o : Occurrence t,
      o.ProtectedUnarySkeleton → o.Invisible →
        HasBandRedex t ∨ HasVisibleBoundary o)
    {P : InvisiblePiece (DerivationTree.typeRaiseLeft C t)}
    (hfree : BoundaryFree P)
    {o : Occurrence (DerivationTree.typeRaiseLeft C t)}
    (ho : o ∈ P.carrier)
    (hprot : o.ProtectedUnarySkeleton) :
    Nonempty (ContractionWitness (DerivationTree.typeRaiseLeft C t)) := by
  have hinv : o.Invisible := P.all_invisible o ho
  rcases protectedSkeleton_contracts_or_boundary_underTypeRaiseLeft
      C t IH o hprot hinv with hred | hboundary
  · exact contractionWitness_of_hasBandRedex hred
  · exact False.elim (P.no_hasVisibleBoundary_of_boundaryFree hfree ho hboundary)

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

/-- A proof-carrying repeatable pair yields a common contraction witness. -/
theorem contractingRepeatablePair_to_contractionWitness
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ : Occurrence t} (h : ContractingRepeatablePair o₁ o₂) :
    Nonempty (ContractionWitness t) :=
  ⟨h.contraction⟩

/-- A proof-carrying repeatable pair gives a strictly smaller derivation tree
for the same sequent. -/
theorem contractingRepeatablePair_contract {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ : Occurrence t} (h : ContractingRepeatablePair o₁ o₂) :
    ∃ t' : DerivationTree Γ A, t'.size < t.size := by
  exact ⟨h.contraction.target, h.contraction.size_lt⟩

/-- If a tree has some proof-carrying repeatable pair, it contracts to a
strictly smaller tree. -/
theorem hasContractingRepeatablePair_contract {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (h : HasContractingRepeatablePair t) : ∃ t' : DerivationTree Γ A, t'.size < t.size := by
  obtain ⟨o₁, o₂, ⟨hp⟩⟩ := h
  exact contractingRepeatablePair_contract hp

/-- A bare band redex also contracts to a strictly smaller tree. -/
theorem hasBandRedex_contract {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (h : HasBandRedex t) : ∃ t' : DerivationTree Γ A, t'.size < t.size := by
  obtain ⟨t', hc⟩ := h
  exact ⟨t', hc.size_lt⟩

/-- Contraction preserves the derived sequent: the contracted tree witnesses the
same `Γ ⇒ccg A`.  (The indices are fixed by typing, so this is `toDerivable` of
the target; it is recorded as a named result for the soundness story.) -/
theorem Contracts.preserves_derives {Γ : List Category} {A : Category} {t t' : DerivationTree Γ A}
    (_h : Contracts t t') : Γ ⇒ccg A :=
  t'.toDerivable

/-- A proof-carrying repeatable pair on a tree for `Γ ⇒ccg A` yields a
strictly smaller tree that still derives `Γ ⇒ccg A`. -/
theorem contractingRepeatablePair_contract_derives
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    {o₁ o₂ : Occurrence t} (h : ContractingRepeatablePair o₁ o₂) :
    ∃ t' : DerivationTree Γ A, t'.size < t.size ∧ (Γ ⇒ccg A) := by
  exact ⟨h.contraction.target, h.contraction.size_lt, h.contraction.target.toDerivable⟩

/-- A `size`-minimal derivation tree has no proof-carrying repeatable pair. -/
theorem Derivable.minimal_no_contractingRepeatablePair {Γ : List Category} {A : Category}
    {t : DerivationTree Γ A} (hmin : ∀ t' : DerivationTree Γ A, t.size ≤ t'.size) :
    ¬ HasContractingRepeatablePair t := by
  intro h
  obtain ⟨t', hlt⟩ := hasContractingRepeatablePair_contract h
  have := hmin t'
  omega

/-- Corollary `minimal` in the paper-facing form: once the real `rep-band`
theorem is available, a size-minimal derivation tree has no raw paper repeatable
pair. -/
theorem Derivable.minimal_no_repeatablePair_of_contractibility
    (hrep : AllRepeatablePairsContract)
    {Γ : List Category} {A : Category} {t : DerivationTree Γ A}
    (hmin : ∀ t' : DerivationTree Γ A, t.size ≤ t'.size) :
    ¬ HasRepeatablePair t := by
  intro h
  obtain ⟨t', hlt⟩ := hasRepeatablePair_contract_of_contractibility hrep h
  have := hmin t'
  omega

/-- A size-minimal derivation tree has no bare band redex either. -/
theorem Derivable.minimal_no_bandRedex {Γ : List Category} {A : Category}
    {t : DerivationTree Γ A} (hmin : ∀ t' : DerivationTree Γ A, t.size ≤ t'.size) :
    ¬ HasBandRedex t := by
  intro h
  obtain ⟨t', hlt⟩ := hasBandRedex_contract h
  have := hmin t'
  omega

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
