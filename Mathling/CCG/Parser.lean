import Mathling.CCG.Soundness
import Mathling.CCG.Completeness

/-!
# Parser entry points and the recognizer/derivation equivalence

This module combines soundness and relative completeness into the recognition
equivalences, and exposes the user-facing parsers `parseWithDepth` and
`parseWithPaperBound` over the finite candidate set, together with their
soundness corollaries and worked examples.
-/

namespace Mathling.CCG

open Tp

/-! ## Recognizer/derivation equivalence -/

/-- Soundness and relative completeness together: over a candidate list `K` that
contains all hidden binary-rule choices, inductive derivability is equivalent to
successful recognition for some finite fuel. -/
theorem exists_recognizes_iff_derives_of_universal_K (K : List Tp)
    (hK : ∀ A : Tp, A ∈ K) {Γ : List Tp} {A : Tp} :
    (∃ fuel, recognizes K fuel Γ A = true) ↔ Γ ⇒ccg A := by
  have hcomplete := recognizes_complete_exists K hK (Γ := Γ) (A := A)
  grind

/-- The corresponding equivalence for `decideBounded`. -/
theorem exists_decideBounded_iff_derives_of_universal_K (K : List Tp)
    (hK : ∀ A : Tp, A ∈ K) {Γ : List Tp} {A : Tp} :
    (∃ fuel, decideBounded K fuel Γ A = true) ↔ Γ ⇒ccg A :=
  exists_recognizes_iff_derives_of_universal_K K hK (Γ := Γ) (A := A)

/-! ## Parsers over the finite candidate set -/

/-- A small, mechanically computable fuel heuristic for a fixed finite chart. -/
@[grind =]
def fuelFor (K : List Tp) (Γ : List Tp) : Nat :=
  (K.length + 1) * (Γ.length + 1) * (Γ.length + 1) + 1

/-- Bounded parser using all categories over the problem atoms up to `depthLimit`. -/
@[grind =]
def parseWithDepth (depthLimit : Nat) (Γ : List Tp) (goal : Tp) : Bool :=
  let K := candidateCategories Γ goal depthLimit
  decideBounded K (fuelFor K Γ) Γ goal

/-- Bounded parser using the schematic paper bound `H = V + q*r*V*(V+1)`.

The constants `q` and `r` are rule-system constants in the paper: `q` bounds
interface states and `r` bounds trace degree.  This definition is not evaluated
by default, because the resulting finite set can be very large. -/
@[grind =]
def parseWithPaperBound (q r : Nat) (Γ : List Tp) (goal : Tp) : Bool :=
  parseWithDepth (depthBound q r Γ goal) Γ goal

/-- Parsing with a fixed depth bound is sound for the inductive derivability relation. -/
@[grind =>]
theorem parseWithDepth_sound {depthLimit : Nat} {Γ : List Tp} {goal : Tp}
    (h : parseWithDepth depthLimit Γ goal = true) : Γ ⇒ccg goal :=
  decideBounded_sound h

/-- Parsing with the schematic paper bound is sound for the inductive derivability relation. -/
@[grind =>]
theorem parseWithPaperBound_sound {q r : Nat} {Γ : List Tp} {goal : Tp}
    (h : parseWithPaperBound q r Γ goal = true) : Γ ⇒ccg goal :=
  parseWithDepth_sound h

/-! ## Worked examples -/

/-- The CCG derivation from the proof's running example. -/
example :
    [# "a", (# "a" ⧹ # "s") ⧸ # "b", # "b"] ⇒ccg # "s" :=
  Derives.appRight (Γ := [# "a", (# "a" ⧹ # "s") ⧸ # "b"]) (B := # "b")
    (Derives.compRight (Γ := [# "a"]) (B := # "a" ⧹ # "s")
      (Derives.typeRaiseRight (C := # "s") Derives.leaf) Derives.leaf)
    Derives.leaf

/-- The standard `John loves Mary` derivation without type raising. -/
example :
    [# "np", (# "np" ⧹ # "s") ⧸ # "np", # "np"] ⇒ccg # "s" :=
  Derives.appLeft (Γ := [# "np"]) (A := # "np") Derives.leaf
    (Derives.appRight (Γ := [(# "np" ⧹ # "s") ⧸ # "np"]) Derives.leaf Derives.leaf)

/-- The `John loves Mary` derivation with subject type raising and composition. -/
example :
    [# "np", (# "np" ⧹ # "s") ⧸ # "np", # "np"] ⇒ccg # "s" :=
  Derives.appRight (Γ := [# "np", (# "np" ⧹ # "s") ⧸ # "np"]) (B := # "np")
    (Derives.compRight (Γ := [# "np"]) (B := # "np" ⧹ # "s")
      (Derives.typeRaiseRight (C := # "s") Derives.leaf) Derives.leaf)
    Derives.leaf

/-- The direct application example is found by the bounded recognizer. -/
example :
    parseWithDepth 1 [# "s" ⧸ # "np", # "np"] (# "s") = true := by
  decide

/-- Closed CCG sequents can be proved by running the bounded recognizer. -/
example :
    [# "s" ⧸ # "np", # "np"] ⇒ccg # "s" := by
  exact parseWithDepth_sound (depthLimit := 1) (by decide)

/-- Closed bounded recognition failures can also be checked by computation. -/
example :
    parseWithDepth 1 [# "np"] (# "s") = false := by
  decide

end Mathling.CCG
