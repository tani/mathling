import Mathling.CCG.Search
import Mathling.CCG.Soundness
import Mathling.CCG.Completeness
import Mathling.CCG.Parser
import Mathling.CCG.Finite
import Mathling.CCG.Atoms
import Mathling.CCG.Depth

/-!
# Decision procedure for the eight-rule CCG system

The decision procedure is the finite chart parser `parseWithCompleteBound r`
over the candidate pool `K_{Γ,A}` of categories built from problem atoms with
depth at most `H = V + V*r`, where `V` is the visible budget of the problem
and `r = 64` is the proved trace-degree constant.

**Proved unconditionally:**

* soundness — an accepting parse yields `Γ ⇒ccg A`
  (`completeBoundParser_sound`);
* exactness for the bounded relation — the Boolean equals `ChartDerivable`
  over the candidate pool (`recognize_sound_chartDerivable_candidate` and
  `parseWithCompleteBound_complete_of_chartDerivable`);
* the depth-bounded normal form implies completeness
  (`completeBoundParserComplete_of_depthBoundedNormalForm`);
* the reduction of the normal form to boundary elimination, of which the
  replaceable-piece case is proved
  (`boundaryFreeReplaceableInvisiblePieceContractsFromPieces`).

**The single remaining obligation** is
`BoundaryFreeProtectedSkeletonPieceContracts` (Band.lean): a size-minimal
problem-atom tree cannot contain a boundary-free invisible trace piece that
includes a protected type-raising skeleton constructor.  Every route from the
draft paper's band-contraction section that was previously kept alive here has
been removed: the paper's repeatable pairs are unsatisfiable (trace components
preserve the addressed subcategory, so a piece never meets a branch twice), so
the counting needs no contraction of repeats, and the sharp bound `V + V*r`
replaces `V + q*r*V*(V+1)`.
-/

set_option linter.style.longLine false

namespace Mathling.CCG

/-! ## Fixed rule-system constant -/

/-- The proved trace-degree constant for the eight-rule trace graph. -/
@[grind =]
def traceNeighborLimit : Nat := 64

/-- Every occurrence of every derivation tree has at most
`traceNeighborLimit = 64` trace neighbours, witnessed by an explicit finite
neighbour list. -/
theorem traceDegreeLimit_traceNeighborLimit : TraceDegreeLimit traceNeighborLimit :=
  traceDegreeLimit

/-! ## The executable recognizer -/

/-- The executable recognizer at the fixed rule-system constant: chart parsing
over the finite candidate pool at depth `H = V + V * 64`. -/
@[grind =]
def completeBoundParser (Γ : List Category) (A : Category) : Bool :=
  parseWithCompleteBound traceNeighborLimit Γ A

/-- Soundness of the executable recognizer. -/
@[grind =>]
theorem completeBoundParser_sound {Γ : List Category} {A : Category}
    (h : completeBoundParser Γ A = true) : Γ ⇒ccg A :=
  parseWithCompleteBound_sound h

/-- Completeness statement for the executable recognizer.  This is the target
that remains conditional on the protected-skeleton case of boundary
elimination. -/
def CompleteBoundParserComplete : Prop :=
  ∀ {Γ : List Category} {A : Category}, Γ ⇒ccg A → completeBoundParser Γ A = true

/-! ## Exactness for the bounded relation

Independently of the open lemma, the Boolean recognizer *exactly* decides the
bounded relation `ChartDerivable` over its own candidate pool: accepting runs
reflect back into bounded derivations.
-/

/-- A successful bounded recognizer run over a concrete candidate pool can be
reflected back into a `ChartDerivable` derivation over that same pool.

`recognize` rejects goals outside `K`, so every recursive leaf/unary/binary
target is known to be in the finite chart; the pool's subcategory closure
supplies the hidden schematic metavariables of binary rules. -/
theorem recognize_sound_chartDerivable_candidate
    {Ω : List Category} {goal : Category} {depthLimit : Nat} :
    ∀ fuel Γ A,
      recognize (categoryPool Ω goal depthLimit) fuel Γ A = true →
        ChartDerivable (categoryPool Ω goal depthLimit) Γ A := by
  intro fuel
  induction fuel with
  | zero =>
      intro Γ A h
      rw [recognize_zero] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with ⟨hA, hleaf⟩
      have hΓ : Γ = [A] := by simpa using hleaf
      subst Γ
      exact ChartDerivable.leaf hA
  | succ fuel ih =>
      intro Γ A h
      rw [recognize_succ_eq_true_iff] at h
      rcases h with ⟨hA, hleaf | hunary | hbinary⟩
      · have hΓ : Γ = [A] := by simpa using hleaf
        subst Γ
        exact ChartDerivable.leaf hA
      · rw [tryUnaryStep_eq_true_iff] at hunary
        rcases hunary with ⟨C, A0, rfl, hprem⟩ | ⟨C, A0, rfl, hprem⟩
        · have hpremDer := ih Γ A0 hprem
          have hC : C ∈ categoryPool Ω goal depthLimit := candidate_rdiv_left_of_mem hA
          exact ChartDerivable.typeRaiseRight hC hA hpremDer
        · have hpremDer := ih Γ A0 hprem
          have hC : C ∈ categoryPool Ω goal depthLimit := candidate_ldiv_right_of_mem hA
          exact ChartDerivable.typeRaiseLeft hC hA hpremDer
      · rw [tryBinaryStep_eq_true_iff] at hbinary
        rcases hbinary with ⟨p, hp, r, _hr, hleft, hright⟩
        have hleftDer := ih p.1 r.left hleft
        have hrightDer := ih p.2 r.right hright
        have hruleIn :
            ChartRule (categoryPool Ω goal depthLimit) r.left r.right A :=
          Rule.toChartRule_of_candidate r.sound
            hleftDer.result_mem hrightDer.result_mem hA
        have happ : p.1 ++ p.2 = Γ := nonemptySplits_append_eq hp
        simpa [happ] using ChartDerivable.binary hleftDer hrightDer hruleIn

/-! ## Completeness from the bounded normal form -/

/-- A depth-bounded normal-form theorem at the fixed constant implies the
completeness of the executable recognizer. -/
theorem completeBoundParserComplete_of_depthBoundedNormalForm
    (hbounded : DepthBoundedNormalForm traceNeighborLimit) :
    CompleteBoundParserComplete := by
  intro Γ A hDerives
  obtain ⟨t, hcert⟩ := nodeCategoryBoundComplete_of_depthBoundedNormalForm hbounded hDerives
  exact parseWithCompleteBound_complete_of_chartDerivable
    (t.toChartDerivable_of_nodeCategoryBoundCertificate hcert)

/-- **Main conditional theorem.**  The only remaining mathematical obligation
is the protected-skeleton case of boundary elimination: pieces free of
protected skeletons are already handled by the proved node-local atom
replacement (`boundaryFreeReplaceableInvisiblePieceContractsFromPieces`). -/
theorem completeBoundParserComplete_of_protectedSkeletonPieceContracts
    (hprotected : BoundaryFreeProtectedSkeletonPieceContracts) :
    CompleteBoundParserComplete :=
  completeBoundParserComplete_of_depthBoundedNormalForm
    (depthBoundedNormalForm_of_replaceable_or_protected_piece_contracts_and_trace
      boundaryFreeReplaceableInvisiblePieceContractsFromPieces
      hprotected
      traceDegreeLimit_traceNeighborLimit)

/-! ## Decidability -/

/-- A proved completeness theorem converts the recognizer into a computable
`Decidable` value.

This definition is intentionally not an instance: installing a global
`Decidable (Γ ⇒ccg A)` before proving `CompleteBoundParserComplete` would hide
the main missing theorem. -/
def decidableOfParserComplete (hcomplete : CompleteBoundParserComplete)
    (Γ : List Category) (A : Category) : Decidable (Γ ⇒ccg A) :=
  if h : completeBoundParser Γ A = true then
    isTrue (completeBoundParser_sound h)
  else
    isFalse (fun hDerives => h (hcomplete hDerives))

/-- Typeclass wrapper for the eventual completeness theorem.  Providing this
witness upgrades instance search from classical propositional decidability to
the executable parser. -/
class ParserCompletenessWitness : Prop where
  complete : CompleteBoundParserComplete

/-- Parser-backed decidability, available as soon as the completeness witness
is in scope. -/
instance instDecidableDerivableOfParserComplete [h : ParserCompletenessWitness]
    (Γ : List Category) (A : Category) : Decidable (Γ ⇒ccg A) :=
  decidableOfParserComplete h.complete Γ A

/-- Package the remaining obligation as the witness class enabling executable
parser-backed decidability. -/
theorem parserCompletenessWitness_of_protectedSkeletonPieceContracts
    (hprotected : BoundaryFreeProtectedSkeletonPieceContracts) :
    ParserCompletenessWitness :=
  ⟨completeBoundParserComplete_of_protectedSkeletonPieceContracts hprotected⟩

/-! ## Closed examples

Until `CompleteBoundParserComplete` is proved globally, concrete closed
sequents can still be decided by computation on the parser side. -/

/-- Direct forward application: the parser-side computation is discharged by
`decide`, then the CCG sequent itself is closed by `decide` using the local
witness. -/
example : [# "s" ⧸ # "np", # "np"] ⇒ccg # "s" := by
  letI : Decidable ([# "s" ⧸ # "np", # "np"] ⇒ccg # "s") :=
    isTrue (parseWithDepthLimit_sound (depthLimit := 1) (by decide))
  decide

/-- Direct backward application, similarly. -/
example : [# "np", # "np" ⧹ # "s"] ⇒ccg # "s" := by
  letI : Decidable ([# "np", # "np" ⧹ # "s"] ⇒ccg # "s") :=
    isTrue (parseWithDepthLimit_sound (depthLimit := 1) (by decide))
  decide

/-- The application-only `John loves Mary` derivation. -/
example : [# "np", (# "np" ⧹ # "s") ⧸ # "np", # "np"] ⇒ccg # "s" := by
  exact Derivable.appLeft (Γ := [# "np"]) (A := # "np") Derivable.leaf
    (Derivable.appRight (Γ := [(# "np" ⧹ # "s") ⧸ # "np"]) Derivable.leaf Derivable.leaf)

end Mathling.CCG
