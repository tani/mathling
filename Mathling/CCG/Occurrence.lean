module

public import Mathling.CCG.Tree

@[expose] public section

/-!
# Category positions and one-hole contexts

The band-contraction argument manipulates *occurrences* inside a category: it
locates a constructor, walks down a branch, and deletes a repeated segment.
This module provides the positional plumbing:

* `CategoryPath`, a path of `Bool`s into the binary tree of a category
  (`false = left child`, `true = right child`);
* `Category.subcategoryAt?`, reading the subcategory at a position;
* `Category.replaceSubcategoryAt?`, replacing the subcategory at a position.

The headline results are that replacing a subterm by a strictly smaller one
strictly decreases `Category.constructors` (`replaceSubcategoryAt?_constructors_lt`), and that a
replacement's atoms come from the host or the inserted subterm
(`mem_atoms_replaceSubcategoryAt?`).  These feed the `size`-decrease and atom-preservation
obligations of `Band`.
-/

set_option linter.style.longLine false

namespace Mathling.CCG

open Category

/-- A position inside a category, as a path of child selectors
(`false`: left subtree, `true`: right subtree). -/
abbrev CategoryPath := List Bool

namespace Category

/-- Read the subcategory at a position, if the path stays inside the tree. -/
def subcategoryAt? : Category → CategoryPath → Option Category
  | A, [] => some A
  | # _, _ :: _ => none
  | A ⧹ B, b :: p => if b then B.subcategoryAt? p else A.subcategoryAt? p
  | A ⧸ B, b :: p => if b then B.subcategoryAt? p else A.subcategoryAt? p

@[simp, grind =]
theorem subcategoryAt?_nil (A : Category) : A.subcategoryAt? [] = some A := by
  cases A <;> rfl

@[simp, grind =]
theorem subcategoryAt?_atom_cons (name : String) (b : Bool) (p : CategoryPath) :
    (# name).subcategoryAt? (b :: p) = none := rfl

@[simp, grind =]
theorem subcategoryAt?_ldiv_false (A B : Category) (p : CategoryPath) :
    (A ⧹ B).subcategoryAt? (false :: p) = A.subcategoryAt? p := rfl

@[simp, grind =]
theorem subcategoryAt?_ldiv_true (A B : Category) (p : CategoryPath) :
    (A ⧹ B).subcategoryAt? (true :: p) = B.subcategoryAt? p := rfl

@[simp, grind =]
theorem subcategoryAt?_rdiv_false (A B : Category) (p : CategoryPath) :
    (A ⧸ B).subcategoryAt? (false :: p) = A.subcategoryAt? p := rfl

@[simp, grind =]
theorem subcategoryAt?_rdiv_true (A B : Category) (p : CategoryPath) :
    (A ⧸ B).subcategoryAt? (true :: p) = B.subcategoryAt? p := rfl

/-- Replace the subcategory at a position by `new`, if the path stays inside the
tree.  Returns `none` when the path runs off an atom. -/
def replaceSubcategoryAt? : Category → CategoryPath → Category → Option Category
  | _, [], new => some new
  | # _, _ :: _, _ => none
  | A ⧹ B, b :: p, new =>
      if b then (B.replaceSubcategoryAt? p new).map (fun B' => A ⧹ B')
      else (A.replaceSubcategoryAt? p new).map (fun A' => A' ⧹ B)
  | A ⧸ B, b :: p, new =>
      if b then (B.replaceSubcategoryAt? p new).map (fun B' => A ⧸ B')
      else (A.replaceSubcategoryAt? p new).map (fun A' => A' ⧸ B)

@[simp, grind =]
theorem replaceSubcategoryAt?_nil (A new : Category) : A.replaceSubcategoryAt? [] new = some new := by
  cases A <;> rfl

@[simp, grind =]
theorem replaceSubcategoryAt?_atom_cons (name : String) (b : Bool) (p : CategoryPath) (new : Category) :
    (# name).replaceSubcategoryAt? (b :: p) new = none := rfl

@[simp, grind =]
theorem replaceSubcategoryAt?_ldiv_false (A B : Category) (p : CategoryPath) (new : Category) :
    (A ⧹ B).replaceSubcategoryAt? (false :: p) new = (A.replaceSubcategoryAt? p new).map (fun A' => A' ⧹ B) := rfl

@[simp, grind =]
theorem replaceSubcategoryAt?_ldiv_true (A B : Category) (p : CategoryPath) (new : Category) :
    (A ⧹ B).replaceSubcategoryAt? (true :: p) new = (B.replaceSubcategoryAt? p new).map (fun B' => A ⧹ B') := rfl

@[simp, grind =]
theorem replaceSubcategoryAt?_rdiv_false (A B : Category) (p : CategoryPath) (new : Category) :
    (A ⧸ B).replaceSubcategoryAt? (false :: p) new = (A.replaceSubcategoryAt? p new).map (fun A' => A' ⧸ B) := rfl

@[simp, grind =]
theorem replaceSubcategoryAt?_rdiv_true (A B : Category) (p : CategoryPath) (new : Category) :
    (A ⧸ B).replaceSubcategoryAt? (true :: p) new = (B.replaceSubcategoryAt? p new).map (fun B' => A ⧸ B') := rfl

/-- `subcategoryAt?` succeeds exactly at *valid* positions; we package validity as a
predicate via `Option.isSome`. -/
@[grind =]
def ValidPos (A : Category) (p : CategoryPath) : Prop := (A.subcategoryAt? p).isSome

/-- Constructor count strictly drops when a position is replaced by a strictly
smaller subterm. -/
theorem replaceSubcategoryAt?_constructors_lt :
    ∀ (A : Category) (p : CategoryPath) (old new A' : Category),
      A.subcategoryAt? p = some old → A.replaceSubcategoryAt? p new = some A' →
      new.constructors < old.constructors →
      A'.constructors < A.constructors := by
  intro A
  induction A with
  | atom name =>
      intro p old new A' hsub hrep hlt
      cases p with
      | nil => simp only [subcategoryAt?_nil, Option.some.injEq] at hsub; subst hsub
               simp only [replaceSubcategoryAt?_nil, Option.some.injEq] at hrep; grind
      | cons b q => simp only [subcategoryAt?_atom_cons, reduceCtorEq] at hsub
  | ldiv A B ihA ihB =>
      intro p old new A' hsub hrep hlt
      cases p with
      | nil => simp only [subcategoryAt?_nil, Option.some.injEq] at hsub; subst hsub
               simp only [replaceSubcategoryAt?_nil, Option.some.injEq] at hrep; grind
      | cons b q =>
          cases b with
          | false =>
              simp only [subcategoryAt?_ldiv_false] at hsub
              simp only [replaceSubcategoryAt?_ldiv_false, Option.map_eq_some_iff] at hrep
              obtain ⟨A'', hopt, rfl⟩ := hrep
              have := ihA q old new A'' hsub hopt hlt
              simp only [constructors]; omega
          | true =>
              simp only [subcategoryAt?_ldiv_true] at hsub
              simp only [replaceSubcategoryAt?_ldiv_true, Option.map_eq_some_iff] at hrep
              obtain ⟨B'', hopt, rfl⟩ := hrep
              have := ihB q old new B'' hsub hopt hlt
              simp only [constructors]; omega
  | rdiv A B ihA ihB =>
      intro p old new A' hsub hrep hlt
      cases p with
      | nil => simp only [subcategoryAt?_nil, Option.some.injEq] at hsub; subst hsub
               simp only [replaceSubcategoryAt?_nil, Option.some.injEq] at hrep; grind
      | cons b q =>
          cases b with
          | false =>
              simp only [subcategoryAt?_rdiv_false] at hsub
              simp only [replaceSubcategoryAt?_rdiv_false, Option.map_eq_some_iff] at hrep
              obtain ⟨A'', hopt, rfl⟩ := hrep
              have := ihA q old new A'' hsub hopt hlt
              simp only [constructors]; omega
          | true =>
              simp only [subcategoryAt?_rdiv_true] at hsub
              simp only [replaceSubcategoryAt?_rdiv_true, Option.map_eq_some_iff] at hrep
              obtain ⟨B'', hopt, rfl⟩ := hrep
              have := ihB q old new B'' hsub hopt hlt
              simp only [constructors]; omega

/-- Atoms of a replacement are contained in the atoms of the host together with
the atoms of the inserted subterm. -/
theorem mem_atoms_replaceSubcategoryAt? :
    ∀ (A : Category) (p : CategoryPath) (new A' : Category),
      A.replaceSubcategoryAt? p new = some A' →
      ∀ name ∈ A'.atoms, name ∈ A.atoms ∨ name ∈ new.atoms := by
  intro A
  induction A with
  | atom name =>
      intro p new A' hrep nm hnm
      cases p with
      | nil => simp only [replaceSubcategoryAt?_nil, Option.some.injEq] at hrep; subst hrep; grind
      | cons b q => simp only [replaceSubcategoryAt?_atom_cons, reduceCtorEq] at hrep
  | ldiv A B ihA ihB =>
      intro p new A' hrep nm hnm
      cases p with
      | nil => simp only [replaceSubcategoryAt?_nil, Option.some.injEq] at hrep; subst hrep; grind
      | cons b q =>
          cases b with
          | false =>
              simp only [replaceSubcategoryAt?_ldiv_false, Option.map_eq_some_iff] at hrep
              obtain ⟨A'', hopt, rfl⟩ := hrep
              simp only [atoms, List.mem_append] at hnm ⊢
              rcases hnm with h | h
              · rcases ihA q new A'' hopt nm h with h' | h' <;> grind
              · grind
          | true =>
              simp only [replaceSubcategoryAt?_ldiv_true, Option.map_eq_some_iff] at hrep
              obtain ⟨B'', hopt, rfl⟩ := hrep
              simp only [atoms, List.mem_append] at hnm ⊢
              rcases hnm with h | h
              · grind
              · rcases ihB q new B'' hopt nm h with h' | h' <;> grind
  | rdiv A B ihA ihB =>
      intro p new A' hrep nm hnm
      cases p with
      | nil => simp only [replaceSubcategoryAt?_nil, Option.some.injEq] at hrep; subst hrep; grind
      | cons b q =>
          cases b with
          | false =>
              simp only [replaceSubcategoryAt?_rdiv_false, Option.map_eq_some_iff] at hrep
              obtain ⟨A'', hopt, rfl⟩ := hrep
              simp only [atoms, List.mem_append] at hnm ⊢
              rcases hnm with h | h
              · rcases ihA q new A'' hopt nm h with h' | h' <;> grind
              · grind
          | true =>
              simp only [replaceSubcategoryAt?_rdiv_true, Option.map_eq_some_iff] at hrep
              obtain ⟨B'', hopt, rfl⟩ := hrep
              simp only [atoms, List.mem_append] at hnm ⊢
              rcases hnm with h | h
              · grind
              · rcases ihB q new B'' hopt nm h with h' | h' <;> grind

/-! ## Finite constructor-position enumeration -/

/-- All slash-constructor positions of a category.  This is the finite
category-local occurrence list used by the node-addressed trace graph. -/
def constructorPositions : Category → List CategoryPath
  | # _ => []
  | A ⧹ B =>
      [] :: (A.constructorPositions.map (fun p => false :: p) ++
        B.constructorPositions.map (fun p => true :: p))
  | A ⧸ B =>
      [] :: (A.constructorPositions.map (fun p => false :: p) ++
        B.constructorPositions.map (fun p => true :: p))

@[simp, grind =]
theorem constructorPositions_atom (name : String) :
    (# name).constructorPositions = [] := rfl

@[simp, grind =]
theorem constructorPositions_ldiv (A B : Category) :
    (A ⧹ B).constructorPositions =
      [] :: (A.constructorPositions.map (fun p => false :: p) ++
        B.constructorPositions.map (fun p => true :: p)) := rfl

@[simp, grind =]
theorem constructorPositions_rdiv (A B : Category) :
    (A ⧸ B).constructorPositions =
      [] :: (A.constructorPositions.map (fun p => false :: p) ++
        B.constructorPositions.map (fun p => true :: p)) := rfl

/-- Soundness of the executable constructor-position enumeration. -/
theorem isConstructor_of_mem_constructorPositions :
    ∀ (A : Category) {p : CategoryPath}, p ∈ A.constructorPositions →
      ∃ X Y, A.subcategoryAt? p = some (X ⧸ Y) ∨ A.subcategoryAt? p = some (X ⧹ Y)
  | # _, _, h => by simp at h
  | A ⧹ B, p, h => by
      simp only [constructorPositions_ldiv, List.mem_cons, List.mem_append, List.mem_map] at h
      rcases h with hp | h | h
      · subst hp
        exact ⟨A, B, Or.inr rfl⟩
      · obtain ⟨q, hq, rfl⟩ := h
        rcases isConstructor_of_mem_constructorPositions A hq with ⟨X, Y, hsub | hsub⟩
        · exact ⟨X, Y, Or.inl (by simp [subcategoryAt?_ldiv_false, hsub])⟩
        · exact ⟨X, Y, Or.inr (by simp [subcategoryAt?_ldiv_false, hsub])⟩
      · obtain ⟨q, hq, rfl⟩ := h
        rcases isConstructor_of_mem_constructorPositions B hq with ⟨X, Y, hsub | hsub⟩
        · exact ⟨X, Y, Or.inl (by simp [subcategoryAt?_ldiv_true, hsub])⟩
        · exact ⟨X, Y, Or.inr (by simp [subcategoryAt?_ldiv_true, hsub])⟩
  | A ⧸ B, p, h => by
      simp only [constructorPositions_rdiv, List.mem_cons, List.mem_append, List.mem_map] at h
      rcases h with hp | h | h
      · subst hp
        exact ⟨A, B, Or.inl rfl⟩
      · obtain ⟨q, hq, rfl⟩ := h
        rcases isConstructor_of_mem_constructorPositions A hq with ⟨X, Y, hsub | hsub⟩
        · exact ⟨X, Y, Or.inl (by simp [subcategoryAt?_rdiv_false, hsub])⟩
        · exact ⟨X, Y, Or.inr (by simp [subcategoryAt?_rdiv_false, hsub])⟩
      · obtain ⟨q, hq, rfl⟩ := h
        rcases isConstructor_of_mem_constructorPositions B hq with ⟨X, Y, hsub | hsub⟩
        · exact ⟨X, Y, Or.inl (by simp [subcategoryAt?_rdiv_true, hsub])⟩
        · exact ⟨X, Y, Or.inr (by simp [subcategoryAt?_rdiv_true, hsub])⟩

/-- Completeness of the executable constructor-position enumeration. -/
theorem mem_constructorPositions_of_isConstructor :
    ∀ (A : Category) {p : CategoryPath},
      (∃ X Y, A.subcategoryAt? p = some (X ⧸ Y) ∨ A.subcategoryAt? p = some (X ⧹ Y)) →
        p ∈ A.constructorPositions
  | # name, p, h => by
      cases p with
      | nil =>
          rcases h with ⟨X, Y, h | h⟩ <;> simp at h
      | cons b q =>
          simp at h
  | A ⧹ B, p, h => by
      cases p with
      | nil =>
          simp [constructorPositions_ldiv]
      | cons b q =>
          cases b with
          | false =>
              simp only [subcategoryAt?_ldiv_false] at h
              have hq : q ∈ A.constructorPositions :=
                mem_constructorPositions_of_isConstructor A h
              simp only [constructorPositions_ldiv, List.mem_cons, List.mem_append,
                List.mem_map]
              exact Or.inr (Or.inl ⟨q, hq, rfl⟩)
          | true =>
              simp only [subcategoryAt?_ldiv_true] at h
              have hq : q ∈ B.constructorPositions :=
                mem_constructorPositions_of_isConstructor B h
              simp only [constructorPositions_ldiv, List.mem_cons, List.mem_append,
                List.mem_map]
              exact Or.inr (Or.inr ⟨q, hq, rfl⟩)
  | A ⧸ B, p, h => by
      cases p with
      | nil =>
          simp [constructorPositions_rdiv]
      | cons b q =>
          cases b with
          | false =>
              simp only [subcategoryAt?_rdiv_false] at h
              have hq : q ∈ A.constructorPositions :=
                mem_constructorPositions_of_isConstructor A h
              simp only [constructorPositions_rdiv, List.mem_cons, List.mem_append,
                List.mem_map]
              exact Or.inr (Or.inl ⟨q, hq, rfl⟩)
          | true =>
              simp only [subcategoryAt?_rdiv_true] at h
              have hq : q ∈ B.constructorPositions :=
                mem_constructorPositions_of_isConstructor B h
              simp only [constructorPositions_rdiv, List.mem_cons, List.mem_append,
                List.mem_map]
              exact Or.inr (Or.inr ⟨q, hq, rfl⟩)

/-- Characterization of the finite constructor-position list. -/
theorem mem_constructorPositions_iff (A : Category) {p : CategoryPath} :
    p ∈ A.constructorPositions ↔
      ∃ X Y, A.subcategoryAt? p = some (X ⧸ Y) ∨ A.subcategoryAt? p = some (X ⧹ Y) :=
  ⟨isConstructor_of_mem_constructorPositions A,
    mem_constructorPositions_of_isConstructor A⟩

/-- The finite constructor-position enumeration has exactly one entry for each
slash constructor. -/
theorem length_constructorPositions :
    ∀ A : Category, A.constructorPositions.length = A.constructors
  | # _ => rfl
  | A ⧹ B => by
      simp [constructorPositions_ldiv, constructors, length_constructorPositions A,
        length_constructorPositions B, Nat.add_assoc]
  | A ⧸ B => by
      simp [constructorPositions_rdiv, constructors, length_constructorPositions A,
        length_constructorPositions B, Nat.add_assoc]

end Category

end Mathling.CCG
