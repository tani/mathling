import Mathling.CCG.Soundness
import Mathling.CCG.Completeness

/-!
# Parser entry points and the recognizer/derivation equivalence

This module combines soundness and relative completeness into the recognition
equivalences, and exposes the user-facing parsers `parseWithDepthLimit` and
`parseWithCompleteBound` over the finite candidate set, together with their
soundness corollaries and worked examples.
-/

set_option linter.style.longLine false

namespace Mathling.CCG

open Category

/-! ## Recognizer/derivation equivalence -/

/-- Soundness and relative completeness together: over a candidate list `K` that
contains all hidden binary-rule choices, inductive derivability is equivalent to
successful recognition for some finite fuel. -/
theorem exists_recognize_iff_derives_of_universal_K (K : List Category)
    (hK : ∀ A : Category, A ∈ K) {Γ : List Category} {A : Category} :
    (∃ fuel, recognize K fuel Γ A = true) ↔ Γ ⇒ccg A := by
  have hcomplete := recognize_complete_exists K hK (Γ := Γ) (A := A)
  grind

/-- The corresponding equivalence for `decideWithFuel`. -/
theorem exists_decideWithFuel_iff_derives_of_universal_K (K : List Category)
    (hK : ∀ A : Category, A ∈ K) {Γ : List Category} {A : Category} :
    (∃ fuel, decideWithFuel K fuel Γ A = true) ↔ Γ ⇒ccg A :=
  exists_recognize_iff_derives_of_universal_K K hK (Γ := Γ) (A := A)

/-! ## Parsers over the finite candidate set -/

/-- Maximum syntactic depth of a finite category list. -/
@[grind =]
def maxDepth : List Category → Nat
  | [] => 0
  | A :: K => Nat.max A.depth (maxDepth K)

@[grind =>]
theorem depth_le_maxDepth_of_mem {K : List Category} {A : Category} (hA : A ∈ K) :
    A.depth ≤ maxDepth K := by
  induction K with
  | nil => simp at hA
  | cons B K ih =>
      simp only [List.mem_cons] at hA
      simp only [maxDepth]
      rcases hA with rfl | hA
      · exact Nat.le_max_left _ _
      · exact le_trans (ih hA) (Nat.le_max_right _ _)

/-- A computable fuel bound for a fixed finite chart.

Backward binary expansion strictly shortens the input span, but can increase
the target depth by at most `maxDepth K + 1`; unary backward expansion keeps
the span and strictly decreases target depth.  Hence

`A.depth + Γ.length * (maxDepth K + 2) + 1`

is enough for any successful search whose root `A` is in the finite chart.
Since the user-facing parser does not take `A` as an argument here, we use the
uniform upper bound `maxDepth K` for the root depth. -/
@[grind =]
def fuelFor (K : List Category) (Γ : List Category) : Nat :=
  maxDepth K + Γ.length * (maxDepth K + 2) + 1

/-- The uniform parser fuel dominates the target-specific fuel whenever the
target category is a member of the finite chart alphabet. -/
theorem targetFuel_le_fuelFor {K : List Category} {Γ : List Category} {A : Category} (hA : A ∈ K) :
    A.depth + Γ.length * (maxDepth K + 2) + 1 ≤ fuelFor K Γ := by
  unfold fuelFor
  have hdepth := depth_le_maxDepth_of_mem hA
  omega

@[grind =>]
theorem depth_succ_le_typeRaiseRight (A C : Category) :
    A.depth + 1 ≤ (C ⧸ (A ⧹ C)).depth := by
  simp only [Category.depth]
  apply Nat.succ_le_succ
  exact le_trans (Nat.le_max_left A.depth C.depth)
    (le_trans (Nat.le_succ _) (Nat.le_max_right C.depth (Nat.max A.depth C.depth + 1)))

@[grind =>]
theorem depth_succ_le_typeRaiseLeft (A C : Category) :
    A.depth + 1 ≤ ((C ⧸ A) ⧹ C).depth := by
  simp only [Category.depth]
  apply Nat.succ_le_succ
  exact le_trans (Nat.le_max_right C.depth A.depth)
    (le_trans (Nat.le_succ _) (Nat.le_max_left (Nat.max C.depth A.depth + 1) C.depth))

/-- Target-specific fuel used by the bounded-fuel completeness proof. -/
@[grind =]
def targetFuel (K : List Category) (Γ : List Category) (A : Category) : Nat :=
  A.depth + Γ.length * (maxDepth K + 2) + 1

theorem targetFuel_le_after_unaryRight (K : List Category) (Γ : List Category) (A C : Category) :
    targetFuel K Γ A ≤ (C ⧸ (A ⧹ C)).depth + Γ.length * (maxDepth K + 2) := by
  unfold targetFuel
  have h := depth_succ_le_typeRaiseRight A C
  omega

theorem targetFuel_le_after_unaryLeft (K : List Category) (Γ : List Category) (A C : Category) :
    targetFuel K Γ A ≤ ((C ⧸ A) ⧹ C).depth + Γ.length * (maxDepth K + 2) := by
  unfold targetFuel
  have h := depth_succ_le_typeRaiseLeft A C
  omega

theorem targetFuel_le_binary_left {K : List Category} {Γ Δ : List Category} {A C : Category}
    (hA : A ∈ K) (hΔ : isNonemptyList Δ = true) :
    targetFuel K Γ A ≤ C.depth + (Γ ++ Δ).length * (maxDepth K + 2) := by
  unfold targetFuel
  let M := maxDepth K + 2
  have hAd : A.depth ≤ maxDepth K := depth_le_maxDepth_of_mem hA
  have hΔlen : 1 ≤ Δ.length := by
    cases Δ with
    | nil => simp [isNonemptyList] at hΔ
    | cons _ _ => simp
  have hM : maxDepth K + 1 ≤ Δ.length * M := by
    have hmul : 1 * M ≤ Δ.length * M := Nat.mul_le_mul_right M hΔlen
    dsimp [M] at hmul ⊢
    omega
  have h1 : A.depth + Γ.length * M + 1 ≤ Γ.length * M + (maxDepth K + 1) := by
    omega
  have h2 : Γ.length * M + (maxDepth K + 1) ≤ Γ.length * M + Δ.length * M :=
    Nat.add_le_add_left hM _
  have h3 : Γ.length * M + Δ.length * M = (Γ.length + Δ.length) * M :=
    (Nat.add_mul Γ.length Δ.length M).symm
  have h4 : Γ.length * M + Δ.length * M ≤ C.depth + (Γ.length + Δ.length) * M := by
    rw [h3]
    exact Nat.le_add_left _ _
  have hlen : (Γ ++ Δ).length = Γ.length + Δ.length := by
    simp
  rw [hlen]
  exact le_trans h1 (le_trans h2 h4)

theorem targetFuel_le_binary_right {K : List Category} {Γ Δ : List Category} {B C : Category}
    (hB : B ∈ K) (hΓ : isNonemptyList Γ = true) :
    targetFuel K Δ B ≤ C.depth + (Γ ++ Δ).length * (maxDepth K + 2) := by
  unfold targetFuel
  let M := maxDepth K + 2
  have hBd : B.depth ≤ maxDepth K := depth_le_maxDepth_of_mem hB
  have hΓlen : 1 ≤ Γ.length := by
    cases Γ with
    | nil => simp [isNonemptyList] at hΓ
    | cons _ _ => simp
  have hM : maxDepth K + 1 ≤ Γ.length * M := by
    have hmul : 1 * M ≤ Γ.length * M := Nat.mul_le_mul_right M hΓlen
    dsimp [M] at hmul ⊢
    omega
  have h1 : B.depth + Δ.length * M + 1 ≤ Δ.length * M + (maxDepth K + 1) := by
    omega
  have h2 : Δ.length * M + (maxDepth K + 1) ≤ Δ.length * M + Γ.length * M :=
    Nat.add_le_add_left hM _
  have h3 : Δ.length * M + Γ.length * M = (Γ.length + Δ.length) * M := by
    rw [Nat.add_comm (Δ.length * M) (Γ.length * M)]
    exact (Nat.add_mul Γ.length Δ.length M).symm
  have h4 : Δ.length * M + Γ.length * M ≤ C.depth + (Γ.length + Δ.length) * M := by
    rw [h3]
    exact Nat.le_add_left _ _
  have hlen : (Γ ++ Δ).length = Γ.length + Δ.length := by
    simp
  rw [hlen]
  exact le_trans h1 (le_trans h2 h4)

/-- Finite-candidate completeness with a concrete fuel bound, not merely an
existentially chosen fuel.  This closes the parser-side saturation gap for
`ChartDerivable`: unary backtracking consumes target depth, while binary backtracking
consumes a nonempty input span. -/
theorem recognize_complete_bounded_of_chartDerivable (K : List Category) :
    ∀ {Γ : List Category} {A : Category}, ChartDerivable K Γ A →
      recognize K (targetFuel K Γ A) Γ A = true := by
  intro Γ A h
  induction h with
  | leaf hA =>
      unfold targetFuel
      simp [recognize, hA]
  | typeRaiseRight hC hOut h ih =>
      rename_i C0 A0 Γ0
      have hmono := recognize_mono_le K (targetFuel_le_after_unaryRight K Γ0 A0 C0) ih
      change recognize K (((C0 ⧸ (A0 ⧹ C0)).depth + Γ0.length * (maxDepth K + 2)) + 1) Γ0
        (C0 ⧸ (A0 ⧹ C0)) = true
      rw [recognize_succ_eq_true_iff]
      refine ⟨hOut, Or.inr (Or.inl ?_)⟩
      rw [tryUnaryStep_eq_true_iff]
      exact Or.inl ⟨C0, A0, rfl, hmono⟩
  | typeRaiseLeft hC hOut h ih =>
      rename_i C0 A0 Γ0
      have hmono := recognize_mono_le K (targetFuel_le_after_unaryLeft K Γ0 A0 C0) ih
      change recognize K ((((C0 ⧸ A0) ⧹ C0).depth + Γ0.length * (maxDepth K + 2)) + 1) Γ0
        ((C0 ⧸ A0) ⧹ C0) = true
      rw [recognize_succ_eq_true_iff]
      refine ⟨hOut, Or.inr (Or.inl ?_)⟩
      rw [tryUnaryStep_eq_true_iff]
      exact Or.inr ⟨C0, A0, rfl, hmono⟩
  | binary h₁ h₂ rule ih₁ ih₂ =>
      rename_i Γ0 A0 Δ0 B0 C0
      have hleftmono := recognize_mono_le K
        (targetFuel_le_binary_left (Γ := Γ0) (Δ := Δ0) (A := A0) (C := C0)
          rule.left_mem (chartDerivable_isNonemptyList h₂)) ih₁
      have hrightmono := recognize_mono_le K
        (targetFuel_le_binary_right (Γ := Γ0) (Δ := Δ0) (B := B0) (C := C0)
          rule.right_mem (chartDerivable_isNonemptyList h₁)) ih₂
      have hbinary := binaryBack_complete_of_ruleIn
        (chartDerivable_isNonemptyList h₁) (chartDerivable_isNonemptyList h₂) hleftmono hrightmono rule
      change recognize K ((C0.depth + (Γ0 ++ Δ0).length * (maxDepth K + 2)) + 1)
        (Γ0 ++ Δ0) C0 = true
      rw [recognize_succ_eq_true_iff]
      exact ⟨rule.result_mem, Or.inr (Or.inr hbinary)⟩

/-- Bounded-decision completeness with the concrete `targetFuel`. -/
theorem decideWithFuel_complete_bounded_of_chartDerivable (K : List Category)
    {Γ : List Category} {A : Category} (h : ChartDerivable K Γ A) :
    decideWithFuel K (targetFuel K Γ A) Γ A = true :=
  recognize_complete_bounded_of_chartDerivable K h

/-- Finite-candidate completeness with the public chart fuel `fuelFor`. -/
theorem decideWithFuel_complete_fuelFor_of_chartDerivable (K : List Category)
    {Γ : List Category} {A : Category} (h : ChartDerivable K Γ A) :
    decideWithFuel K (fuelFor K Γ) Γ A = true := by
  exact recognize_mono_le K (targetFuel_le_fuelFor h.result_mem)
    (recognize_complete_bounded_of_chartDerivable K h)

/-- Bounded parser using all categories over the problem atoms up to `depthLimit`. -/
@[grind =]
def parseWithDepthLimit (depthLimit : Nat) (Γ : List Category) (goal : Category) : Bool :=
  let K := categoryPool Γ goal depthLimit
  decideWithFuel K (fuelFor K Γ) Γ goal

/-- Fuel-explicit bounded parser using all categories over the problem atoms up
to `depthLimit`.

This version is the clean theorem-proving interface: relative completeness
below produces a finite fuel for any `ChartDerivable` normal-form derivation.  The
fuel-free `parseWithDepthLimit` uses the concrete computable heuristic `fuelFor`. -/
@[grind =]
def parseWithDepthLimitAndFuel (depthLimit fuel : Nat) (Γ : List Category) (goal : Category) : Bool :=
  let K := categoryPool Γ goal depthLimit
  decideWithFuel K fuel Γ goal

/-- Bounded parser using the schematic paper bound `H = V + q*r*V*(V+1)`.

The constants `q` and `r` are rule-system constants in the paper: `q` bounds
interface states and `r` bounds trace degree.  This definition is not evaluated
by default, because the resulting finite set can be very large. -/
@[grind =]
def parseWithCompleteBound (q r : Nat) (Γ : List Category) (goal : Category) : Bool :=
  parseWithDepthLimit (depthBound q r Γ goal) Γ goal

/-- Fuel-explicit parser using the schematic paper depth bound. -/
@[grind =]
def parseWithCompleteBoundAndFuel (q r fuel : Nat) (Γ : List Category) (goal : Category) : Bool :=
  parseWithDepthLimitAndFuel (depthBound q r Γ goal) fuel Γ goal

/-- Parsing with a fixed depth bound is sound for the inductive derivability relation. -/
@[grind =>]
theorem parseWithDepthLimit_sound {depthLimit : Nat} {Γ : List Category} {goal : Category}
    (h : parseWithDepthLimit depthLimit Γ goal = true) : Γ ⇒ccg goal :=
  decideWithFuel_sound h

/-- Parsing with the schematic paper bound is sound for the inductive derivability relation. -/
@[grind =>]
theorem parseWithCompleteBound_sound {q r : Nat} {Γ : List Category} {goal : Category}
    (h : parseWithCompleteBound q r Γ goal = true) : Γ ⇒ccg goal :=
  parseWithDepthLimit_sound h

/-- Fuel-explicit parsing with a fixed depth bound is sound. -/
@[grind =>]
theorem parseWithDepthLimitAndFuel_sound {depthLimit fuel : Nat} {Γ : List Category} {goal : Category}
    (h : parseWithDepthLimitAndFuel depthLimit fuel Γ goal = true) : Γ ⇒ccg goal :=
  decideWithFuel_sound h

/-- Fuel-explicit parsing with the schematic paper bound is sound. -/
@[grind =>]
theorem parseWithCompleteBoundAndFuel_sound {q r fuel : Nat} {Γ : List Category} {goal : Category}
    (h : parseWithCompleteBoundAndFuel q r fuel Γ goal = true) : Γ ⇒ccg goal :=
  parseWithDepthLimitAndFuel_sound h

/-- If the paper's bounded-normal-form transformation has produced a derivation
inside the concrete candidate set for `depthLimit`, then some finite fuel makes
the depth-bounded parser accept. -/
theorem exists_parseWithDepthLimitAndFuel_of_chartDerivable {depthLimit : Nat} {Γ : List Category} {goal : Category}
    (h : ChartDerivable (categoryPool Γ goal depthLimit) Γ goal) :
    ∃ fuel, parseWithDepthLimitAndFuel depthLimit fuel Γ goal = true :=
  decideWithFuel_complete_exists_of_chartDerivable (categoryPool Γ goal depthLimit) h

/-- The bounded parser with its concrete fuel is complete for a derivation
already living inside its finite candidate set. -/
theorem parseWithDepthLimit_complete_of_chartDerivable {depthLimit : Nat} {Γ : List Category} {goal : Category}
    (h : ChartDerivable (categoryPool Γ goal depthLimit) Γ goal) :
    parseWithDepthLimit depthLimit Γ goal = true :=
  decideWithFuel_complete_fuelFor_of_chartDerivable (categoryPool Γ goal depthLimit) h

/-- The corresponding statement for the paper depth bound `H(Γ,goal)`. -/
theorem exists_parseWithCompleteBoundAndFuel_of_chartDerivable {q r : Nat} {Γ : List Category} {goal : Category}
    (h : ChartDerivable (categoryPool Γ goal (depthBound q r Γ goal)) Γ goal) :
    ∃ fuel, parseWithCompleteBoundAndFuel q r fuel Γ goal = true :=
  exists_parseWithDepthLimitAndFuel_of_chartDerivable h

/-- The paper-bound parser with its concrete fuel is complete for a derivation
already living inside the paper candidate set. -/
theorem parseWithCompleteBound_complete_of_chartDerivable {q r : Nat} {Γ : List Category} {goal : Category}
    (h : ChartDerivable (categoryPool Γ goal (depthBound q r Γ goal)) Γ goal) :
    parseWithCompleteBound q r Γ goal = true :=
  parseWithDepthLimit_complete_of_chartDerivable h

/-! ## Worked examples -/

/-- The CCG derivation from the proof's running example. -/
example :
    [# "a", (# "a" ⧹ # "s") ⧸ # "b", # "b"] ⇒ccg # "s" :=
  Derivable.appRight (Γ := [# "a", (# "a" ⧹ # "s") ⧸ # "b"]) (B := # "b")
    (Derivable.compRight (Γ := [# "a"]) (B := # "a" ⧹ # "s")
      (Derivable.typeRaiseRight (C := # "s") Derivable.leaf) Derivable.leaf)
    Derivable.leaf

/-- The standard `John loves Mary` derivation without type raising. -/
example :
    [# "np", (# "np" ⧹ # "s") ⧸ # "np", # "np"] ⇒ccg # "s" :=
  Derivable.appLeft (Γ := [# "np"]) (A := # "np") Derivable.leaf
    (Derivable.appRight (Γ := [(# "np" ⧹ # "s") ⧸ # "np"]) Derivable.leaf Derivable.leaf)

/-- The `John loves Mary` derivation with subject type raising and composition. -/
example :
    [# "np", (# "np" ⧹ # "s") ⧸ # "np", # "np"] ⇒ccg # "s" :=
  Derivable.appRight (Γ := [# "np", (# "np" ⧹ # "s") ⧸ # "np"]) (B := # "np")
    (Derivable.compRight (Γ := [# "np"]) (B := # "np" ⧹ # "s")
      (Derivable.typeRaiseRight (C := # "s") Derivable.leaf) Derivable.leaf)
    Derivable.leaf

/-- The direct application example is found by the bounded recognizer. -/
example :
    parseWithDepthLimit 1 [# "s" ⧸ # "np", # "np"] (# "s") = true := by
  decide

/-- The same direct application as a finite-candidate normal-form derivation. -/
example :
    ChartDerivable (categoryPool [# "s" ⧸ # "np", # "np"] (# "s") 1)
      [# "s" ⧸ # "np", # "np"] (# "s") :=
  ChartDerivable.binary
    (ChartDerivable.leaf (by decide))
    (ChartDerivable.leaf (by decide))
    (ChartRule.appRight (by decide) (by decide) (by decide))

/-- Finite-candidate relative completeness produces an accepting finite fuel. -/
example :
    ∃ fuel, parseWithDepthLimitAndFuel 1 fuel [# "s" ⧸ # "np", # "np"] (# "s") = true :=
  exists_parseWithDepthLimitAndFuel_of_chartDerivable (depthLimit := 1)
    (ChartDerivable.binary
      (ChartDerivable.leaf (by decide))
      (ChartDerivable.leaf (by decide))
      (ChartRule.appRight (by decide) (by decide) (by decide)))

/-! ## Deciding derivability via the bounded parser

The bounded parser is executable, and `parseWithDepthLimit_sound` turns a successful
parse into the inductive sequent.  These examples show the parser side being
discharged by `decide`; after importing `Mathling.CCG.Decidability`, closed
`⇒ccg` sequents can also be closed directly by `by decide`. -/

/-- Forward application `s/np, np ⇒ccg s`, proved by `decide` on the parser. -/
example : [# "s" ⧸ # "np", # "np"] ⇒ccg # "s" :=
  parseWithDepthLimit_sound (depthLimit := 1) (by decide)

/-- Backward application `np, np\s ⇒ccg s`, proved by `decide` on the parser. -/
example : [# "np", # "np" ⧹ # "s"] ⇒ccg # "s" :=
  parseWithDepthLimit_sound (depthLimit := 1) (by decide)

/-- The `John loves Mary` sequent itself. -/
example : [# "np", (# "np" ⧹ # "s") ⧸ # "np", # "np"] ⇒ccg # "s" :=
  Derivable.appLeft (Γ := [# "np"]) (A := # "np") Derivable.leaf
    (Derivable.appRight (Γ := [(# "np" ⧹ # "s") ⧸ # "np"]) Derivable.leaf Derivable.leaf)

/-- A closed CCG sequent can itself be closed by `decide` once the bounded parser
provides a local executable `Decidable` witness for that concrete sequent. -/
example :
    [# "s" ⧸ # "np", # "np"] ⇒ccg # "s" := by
  letI : Decidable ([# "s" ⧸ # "np", # "np"] ⇒ccg # "s") :=
    isTrue (parseWithDepthLimit_sound (depthLimit := 1) (by decide))
  decide

/-- Closed bounded recognition failures can also be checked by computation. -/
example :
    parseWithDepthLimit 1 [# "np"] (# "s") = false := by
  decide

end Mathling.CCG
