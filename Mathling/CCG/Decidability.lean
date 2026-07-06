import Mathling.CCG.Search
import Mathling.CCG.Soundness
import Mathling.CCG.Completeness
import Mathling.CCG.Parser
import Mathling.CCG.Finite
import Mathling.CCG.Atoms
import Mathling.CCG.Depth

/-!
# Decision procedure interface for the eight-rule CCG system

This file is the stable public entry point for the CCG decision procedure.  The
current Lean development contains the executable finite parser and its
soundness theorem.  The global paper-level completeness theorem from
`ccg_decidability_proof_3-1.pdf`, §22--§26, is stated below as an ordinary
proposition/theorem target rather than assumed as an axiom.

Importing `Mathling.CCG.Decidability` re-exports the CCG syntax, search,
soundness, relative completeness, parser entry points, and the conditional
construction of a `Decidable (Γ ⇒ccg A)` from a proved finite-chart
completeness theorem.
-/

set_option linter.style.longLine false

namespace Mathling.CCG

/-!
## Fixed paper constants

The eventual executable decision procedure uses constants depending only on the
rule system.  `interfaceStateLimit` is the number of interface states already enumerated in
`Trace`; `traceNeighborLimit` is a conservative trace-degree budget reserved for the
trace-neighbour proof.
-/

/-- The paper's interface-state count constant. -/
@[grind =]
def interfaceStateLimit : Nat := InterfaceStateCount

/-- A conservative trace-degree constant for the eight-rule trace graph. -/
@[grind =]
def traceNeighborLimit : Nat := 64

/-- The proved trace-degree bound, restated at the fixed paper constant
`traceNeighborLimit`.  Every occurrence of every derivation tree has at most
`traceNeighborLimit = 64` trace neighbours, witnessed by an explicit finite
neighbour list.  This is the faithful, non-vacuous formalization of the paper's
"trace degree is a rule-system constant `r`" (§"Trace degree 定数 `r`"). -/
theorem traceDegreeLimit_traceNeighborLimit : TraceDegreeLimit traceNeighborLimit :=
  traceDegreeLimit

/-- The branch constructor-position count at the fixed paper constants. -/
theorem branchConstructorPositionCountingComplete :
    BranchConstructorPositionCountingComplete interfaceStateLimit traceNeighborLimit := by
  unfold interfaceStateLimit
  exact branchConstructorPositionCountingComplete_interfaceStateCount (r := traceNeighborLimit)

/-- Fixed-constant depth-bounded normal form from boundary-free-piece
elimination alone.  Repeatable-pair contraction is no longer needed for the
depth-counting route. -/
theorem depthBoundedNormalForm_of_boundaryElimination
    (hboundary : BoundaryFreeInvisiblePieceElimination) :
    DepthBoundedNormalForm interfaceStateLimit traceNeighborLimit := by
  unfold interfaceStateLimit
  exact depthBoundedNormalForm_of_boundaryElimination_and_trace
    hboundary traceDegreeLimit_traceNeighborLimit

/-- Fixed-constant normal form from the faithful piece-level boundary-free
contraction target. -/
theorem depthBoundedNormalForm_of_boundaryPieceContracts
    (hboundary : BoundaryFreeInvisiblePieceContractsFromPieces) :
    DepthBoundedNormalForm interfaceStateLimit traceNeighborLimit := by
  unfold interfaceStateLimit
  exact depthBoundedNormalForm_of_pieceContracts_and_trace
    hboundary traceDegreeLimit_traceNeighborLimit

/-- Fixed-constant normal form from the repaired two-case boundary-free
architecture: replaceable pieces are handled by atom replacement, while pieces
containing protected unary type-raising skeleton constructors are handled by a
separate contraction argument. -/
theorem depthBoundedNormalForm_of_replaceable_or_protected_boundaryPieces
    (hreplace : BoundaryFreeReplaceableInvisiblePieceContractsFromPieces)
    (hprotected : BoundaryFreeProtectedSkeletonPieceContracts) :
    DepthBoundedNormalForm interfaceStateLimit traceNeighborLimit := by
  unfold interfaceStateLimit
  exact depthBoundedNormalForm_of_replaceable_or_protected_piece_contracts_and_trace
    hreplace hprotected traceDegreeLimit_traceNeighborLimit

/-!
## Executable Boolean used for decidability

The paper proves that for constants `q,r` depending only on the eight-rule
system, parsing with the finite paper bound

`H(Γ,y) = V + q*r*V*(V+1)`

is sound and complete.  The Boolean below is the executable part of that
decision procedure.  Its soundness is already formalized.  Its completeness is
precisely the remaining bounded-normal-form/chart-completeness theorem.
-/

/-- The executable paper-bound recognizer for a fixed choice of rule-system
constants `q` and `r`. -/
@[grind =]
def completeBoundParser (q r : Nat) (Γ : List Category) (A : Category) : Bool :=
  parseWithCompleteBound q r Γ A

/-- Soundness of the executable paper-bound recognizer. -/
@[grind =>]
theorem completeBoundParser_sound {q r : Nat} {Γ : List Category} {A : Category}
    (h : completeBoundParser q r Γ A = true) : Γ ⇒ccg A :=
  parseWithCompleteBound_sound h

/-- The paper-level completeness statement for fixed constants `q,r`.

This is the Lean target corresponding to `ccg_decidability_proof_3-1.pdf`,
§22--§26: bounded-category normal form plus finite chart completeness.  It is
not assumed here; it must be proved from the trace-graph / band-contraction / depth-bound
argument before deriving the global computable instance. -/
def CompleteBoundParserComplete (q r : Nat) : Prop :=
  ∀ {Γ : List Category} {A : Category}, Γ ⇒ccg A → completeBoundParser q r Γ A = true

/-!
For auditability, we split the paper-level completeness target into the two
mathematical obligations that remain after the executable parser, soundness,
finite candidate-set lemma, and finite-candidate relative completeness have
been formalized.
-/

/-- Bounded-normal-form obligation: every derivable sequent has an equivalent
derivation whose categories and binary-rule metavariables are contained in the
paper candidate set `K_{Γ,A}` at depth `H(Γ,A)`.

This is the Lean interface for the trace-graph / invisible-piece /
band-contraction / depth-bound argument of the paper. -/
def ChartNormalFormComplete (q r : Nat) : Prop :=
  ∀ {Γ : List Category} {A : Category}, Γ ⇒ccg A →
    ChartDerivable (categoryPool Γ A (depthBound q r Γ A)) Γ A

/-- The remaining trace/zone-counting obligation in its sharpest current form:
every derivable sequent has an explicit derivation tree whose node categories
all lie in the paper candidate set. -/
def NodeCategoryBoundComplete (q r : Nat) : Prop :=
  ∀ {Γ : List Category} {A : Category}, Γ ⇒ccg A →
    ∃ t : DerivationTree Γ A, NodeCategoryBoundCertificate q r t

/-- A proved depth-counting certificate theorem implies the bounded normal form
statement required by the parser completeness layer. -/
theorem chartNormalFormComplete_of_depthCountingComplete
    {q r : Nat} (hdepth : NodeCategoryBoundComplete q r) :
    ChartNormalFormComplete q r := by
  intro Γ A hDerives
  obtain ⟨t, hcert⟩ := hdepth hDerives
  exact t.toChartDerivable_of_nodeCategoryBoundCertificate hcert

/-- Fixed-fuel obligation: if some finite fuel accepts for the paper candidate
set, then the concrete fuel chosen by `parseWithCompleteBound` is already enough.

Equivalently, this is the finite chart saturation bound for the executable
recognizer. -/
def ParserFuelComplete (q r : Nat) : Prop :=
  ∀ {Γ : List Category} {A : Category} {fuel : Nat},
    parseWithCompleteBoundAndFuel q r fuel Γ A = true →
      parseWithCompleteBound q r Γ A = true

/-- A successful bounded recognizer run over a concrete paper candidate set can
be reflected back into a `ChartDerivable` derivation over that same candidate set.

The key point is that `recognize` now rejects goals outside `K`; therefore
every recursive leaf/unary/binary target is known to be in the finite chart.
For binary rules, the candidate set's subcategory closure supplies the hidden
schematic metavariables. -/
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

/-- The fixed-fuel saturation obligation is now proved: any accepting
fuel-explicit paper parser run reflects to `ChartDerivable`, and the concrete
`fuelFor` parser is complete for all such finite-candidate derivations. -/
theorem parserFuelCompleteFor (q r : Nat) : ParserFuelComplete q r := by
  intro Γ A fuel h
  unfold parseWithCompleteBoundAndFuel parseWithDepthLimitAndFuel at h
  have hDerivesIn :
      ChartDerivable (categoryPool Γ A (depthBound q r Γ A)) Γ A :=
    recognize_sound_chartDerivable_candidate fuel Γ A h
  exact parseWithCompleteBound_complete_of_chartDerivable (q := q) (r := r) hDerivesIn

/-- The fixed-fuel part of the paper parser is already complete for the chosen
paper constants. -/
theorem parserFuelComplete : ParserFuelComplete interfaceStateLimit traceNeighborLimit :=
  parserFuelCompleteFor interfaceStateLimit traceNeighborLimit

/-- The already-formalized finite-candidate completeness layer: a proved
bounded-normal-form theorem gives acceptance by the paper parser for some
finite fuel. -/
theorem exists_parseWithCompleteBoundAndFuel_of_chartNormalForm
    {q r : Nat} (hnf : ChartNormalFormComplete q r)
    {Γ : List Category} {A : Category} (h : Γ ⇒ccg A) :
    ∃ fuel, parseWithCompleteBoundAndFuel q r fuel Γ A = true :=
  exists_parseWithCompleteBoundAndFuel_of_chartDerivable (hnf h)

/-- With the concrete parser fuel proved sufficient for every `ChartDerivable`
normal-form derivation, bounded normal form now directly implies the
paper-level Boolean completeness theorem. -/
theorem completeBoundParserComplete_of_normalForm
    {q r : Nat} (hnf : ChartNormalFormComplete q r) :
    CompleteBoundParserComplete q r := by
  intro Γ A hDerives
  exact parseWithCompleteBound_complete_of_chartDerivable (hnf hDerives)

/-- A proved depth-counting certificate theorem directly implies paper-level
Boolean completeness. -/
theorem completeBoundParserComplete_of_depthCountingComplete
    {q r : Nat} (hdepth : NodeCategoryBoundComplete q r) :
    CompleteBoundParserComplete q r :=
  completeBoundParserComplete_of_normalForm (chartNormalFormComplete_of_depthCountingComplete hdepth)

/-- A fully bounded tree normal-form theorem directly implies paper-level
Boolean completeness. -/
theorem completeBoundParserComplete_of_depthBoundedNormalForm
    {q r : Nat} (hbounded : DepthBoundedNormalForm q r) :
    CompleteBoundParserComplete q r :=
  completeBoundParserComplete_of_depthCountingComplete
    (nodeCategoryBoundComplete_of_depthBoundedNormalForm hbounded)

/-- A size-bounded normal-form theorem directly implies paper-level Boolean
completeness. -/
theorem completeBoundParserComplete_of_sizeBoundedNormalForm
    {q r : Nat} (hmu : SizeBoundedNormalForm q r) :
    CompleteBoundParserComplete q r :=
  completeBoundParserComplete_of_depthBoundedNormalForm
    (depthBoundedNormalForm_of_sizeBoundedNormalForm hmu)

/-- Fixed parser completeness from the boundary-free-piece contraction target
alone, using the repeatable-pair-free depth-counting bridge. -/
theorem completeBoundParserComplete_of_boundaryContracts
    (hboundary : BoundaryFreeInvisiblePieceContracts) :
    CompleteBoundParserComplete interfaceStateLimit traceNeighborLimit :=
  completeBoundParserComplete_of_depthBoundedNormalForm
    (depthBoundedNormalForm_of_boundaryElimination
      (boundaryFreeInvisiblePieceElimination_of_contracts hboundary))

/-- Fixed parser completeness from the piece-level boundary-free contraction
target.  This keeps the remaining hard theorem focused on the faithful
finite-piece formulation. -/
theorem completeBoundParserComplete_of_boundaryPieceContracts
    (hboundary : BoundaryFreeInvisiblePieceContractsFromPieces) :
    CompleteBoundParserComplete interfaceStateLimit traceNeighborLimit :=
  completeBoundParserComplete_of_depthBoundedNormalForm
    (depthBoundedNormalForm_of_boundaryPieceContracts hboundary)

/-- Fixed parser completeness from the repaired two-case boundary-free
architecture.  This theorem does not solve either hard case; it only records
the now-explicit split caused by protected unary type-raising skeletons. -/
theorem completeBoundParserComplete_of_replaceable_or_protected_boundaryPieces
    (hreplace : BoundaryFreeReplaceableInvisiblePieceContractsFromPieces)
    (hprotected : BoundaryFreeProtectedSkeletonPieceContracts) :
    CompleteBoundParserComplete interfaceStateLimit traceNeighborLimit :=
  completeBoundParserComplete_of_depthBoundedNormalForm
    (depthBoundedNormalForm_of_replaceable_or_protected_boundaryPieces
      hreplace hprotected)

/-- The full paper pipeline, before the final fixed-constant specialization:
repeatable pairs produce contractions, boundary-free invisible pieces are
eliminated in minimal trees, and branch/zone counting gives the bounded normal
form consumed by the parser. -/
theorem completeBoundParserComplete_of_branchZoneCounting
    {q r : Nat}
    (hrep : AllRepeatablePairsContract)
    (hboundary : BoundaryFreeInvisiblePieceElimination)
    (hcount : BranchZoneCountingComplete q r)
    (htrace : TraceDegreeLimit r) :
    CompleteBoundParserComplete q r :=
  completeBoundParserComplete_of_depthBoundedNormalForm
    (depthBoundedNormalForm_of_branchZoneCounting hrep hboundary hcount htrace)

/-- Same parser-completeness pipeline, using the paper-facing `rep-band` target
that first constructs a transport-closed band. -/
theorem completeBoundParserComplete_of_repeatablePairProducesBand_of_branchZoneCounting
    {q r : Nat}
    (hband : RepeatablePairProducesBand)
    (hboundary : BoundaryFreeInvisiblePieceElimination)
    (hcount : BranchZoneCountingComplete q r)
    (htrace : TraceDegreeLimit r) :
    CompleteBoundParserComplete q r :=
  completeBoundParserComplete_of_branchZoneCounting
    (allRepeatablePairsContract_of_repeatablePairProducesBand hband)
    hboundary hcount htrace

/-- Parser completeness from the more local constructor-position branch
counting target. -/
theorem completeBoundParserComplete_of_constructorPositionCounting
    {q r : Nat}
    (hrep : AllRepeatablePairsContract)
    (hboundary : BoundaryFreeInvisiblePieceElimination)
    (hcount : BranchConstructorPositionCountingComplete q r)
    (htrace : TraceDegreeLimit r) :
    CompleteBoundParserComplete q r :=
  completeBoundParserComplete_of_branchZoneCounting hrep hboundary
    (branchZoneCountingComplete_of_constructorPositionCounting hcount) htrace

/-- Paper-facing band variant of parser completeness from constructor-position
branch counting. -/
theorem completeBoundParserComplete_of_repeatablePairProducesBand_of_constructorPositionCounting
    {q r : Nat}
    (hband : RepeatablePairProducesBand)
    (hboundary : BoundaryFreeInvisiblePieceElimination)
    (hcount : BranchConstructorPositionCountingComplete q r)
    (htrace : TraceDegreeLimit r) :
    CompleteBoundParserComplete q r :=
  completeBoundParserComplete_of_constructorPositionCounting
    (allRepeatablePairsContract_of_repeatablePairProducesBand hband)
    hboundary hcount htrace

/-- Parser completeness from the local boundary-free-piece contraction theorem
and the local constructor-position branch counting theorem. -/
theorem completeBoundParserComplete_of_boundaryContracts_of_constructorPositionCounting
    {q r : Nat}
    (hrep : AllRepeatablePairsContract)
    (hboundary : BoundaryFreeInvisiblePieceContracts)
    (hcount : BranchConstructorPositionCountingComplete q r)
    (htrace : TraceDegreeLimit r) :
    CompleteBoundParserComplete q r :=
  completeBoundParserComplete_of_constructorPositionCounting hrep
    (boundaryFreeInvisiblePieceElimination_of_contracts hboundary)
    hcount htrace

/-- Paper-facing band variant using local boundary-free-piece contraction and
constructor-position branch counting. -/
theorem completeBoundParserComplete_of_repeatablePairProducesBand_of_boundaryContracts_of_constructorPositionCounting
    {q r : Nat}
    (hband : RepeatablePairProducesBand)
    (hboundary : BoundaryFreeInvisiblePieceContracts)
    (hcount : BranchConstructorPositionCountingComplete q r)
    (htrace : TraceDegreeLimit r) :
    CompleteBoundParserComplete q r :=
  completeBoundParserComplete_of_boundaryContracts_of_constructorPositionCounting
    (allRepeatablePairsContract_of_repeatablePairProducesBand hband)
    hboundary hcount htrace

/-- Parser completeness from the contraction-witness form of `rep-band`,
boundary-free-piece contraction, and constructor-position branch counting. -/
theorem completeBoundParserComplete_of_contractionWitness_of_boundaryContracts_of_constructorPositionCounting
    {q r : Nat}
    (hwitness : RepeatablePairHasContractionWitness)
    (hboundary : BoundaryFreeInvisiblePieceContracts)
    (hcount : BranchConstructorPositionCountingComplete q r)
    (htrace : TraceDegreeLimit r) :
    CompleteBoundParserComplete q r :=
  completeBoundParserComplete_of_repeatablePairProducesBand_of_boundaryContracts_of_constructorPositionCounting
    (repeatablePairProducesBand_of_contractionWitness hwitness)
    hboundary hcount htrace

/-- Bounded normal form plus a fixed-fuel chart saturation bound imply the
paper-level completeness statement used by the computable decidability wrapper. -/
theorem completeBoundParserComplete_of_normalForm_of_fuelBound
    {q r : Nat} (hnf : ChartNormalFormComplete q r) (hfuel : ParserFuelComplete q r) :
    CompleteBoundParserComplete q r := by
  intro Γ A hDerives
  rcases exists_parseWithCompleteBoundAndFuel_of_chartNormalForm hnf hDerives with ⟨fuel, hfuelTrue⟩
  exact hfuel hfuelTrue

/-- Depth-counting certificate completeness plus the finite fixed-fuel chart
bound imply paper-level Boolean completeness. -/
theorem completeBoundParserComplete_of_depthCountingComplete_of_fuelBound
    {q r : Nat} (hdepth : NodeCategoryBoundComplete q r) (hfuel : ParserFuelComplete q r) :
    CompleteBoundParserComplete q r :=
  completeBoundParserComplete_of_normalForm_of_fuelBound
    (chartNormalFormComplete_of_depthCountingComplete hdepth) hfuel

/-- A fully bounded tree normal-form theorem plus the finite fixed-fuel chart
bound imply paper-level Boolean completeness.  This is the final bridge from
the trace/zone depth-counting theorem to the executable parser. -/
theorem completeBoundParserComplete_of_depthBoundedNormalForm_of_fuelBound
    {q r : Nat} (hbounded : DepthBoundedNormalForm q r) (hfuel : ParserFuelComplete q r) :
    CompleteBoundParserComplete q r :=
  completeBoundParserComplete_of_depthCountingComplete_of_fuelBound
    (nodeCategoryBoundComplete_of_depthBoundedNormalForm hbounded) hfuel

/-- A size-bounded normal-form theorem plus finite fixed-fuel chart saturation is
now enough to obtain the paper-level Boolean completeness theorem.  This is the
preferred target for the remaining band-contraction/counting work, because
`DerivationTree.depth_le_size_of_mem_nodeCategories` turns a global size bound into all node-depth
bounds. -/
theorem completeBoundParserComplete_of_sizeBoundedNormalForm_of_fuelBound
    {q r : Nat} (hmu : SizeBoundedNormalForm q r) (hfuel : ParserFuelComplete q r) :
    CompleteBoundParserComplete q r :=
  completeBoundParserComplete_of_depthBoundedNormalForm_of_fuelBound
    (depthBoundedNormalForm_of_sizeBoundedNormalForm hmu) hfuel

/-- Conversely, a `NodeCategoryBoundComplete` theorem yields the concrete
bounded-tree normal-form statement: candidate membership gives both
problem-atom containment and the paper depth bound for every node category. -/
theorem depthBoundedNormalForm_of_depthCountingComplete
    {q r : Nat} (hdepth : NodeCategoryBoundComplete q r) :
    DepthBoundedNormalForm q r := by
  intro Γ A hDerives
  obtain ⟨t, hcert⟩ := hdepth hDerives
  refine ⟨t, ?_, ?_⟩
  · intro B hB
    exact atoms_of_mem_categoryPool (hcert B hB)
  · intro B hB
    exact depth_le_of_mem_categoryPool (hcert B hB)

/-- `NodeCategoryBoundComplete` is exactly the finite-candidate form of the
bounded-tree normal-form theorem. -/
theorem nodeCategoryBoundComplete_iff_depthBoundedNormalForm {q r : Nat} :
    NodeCategoryBoundComplete q r ↔ DepthBoundedNormalForm q r := by
  constructor
  · exact depthBoundedNormalForm_of_depthCountingComplete
  · exact nodeCategoryBoundComplete_of_depthBoundedNormalForm

/-- Soundness and a proved `CompleteBoundParserComplete q r` give the desired equivalence
between inductive derivability and the executable Boolean. -/
@[grind =]
theorem completeBoundParser_eq_true_iff_of_completeBoundParserComplete
    {q r : Nat} (hcomplete : CompleteBoundParserComplete q r)
    {Γ : List Category} {A : Category} :
    completeBoundParser q r Γ A = true ↔ Γ ⇒ccg A := by
  constructor
  · exact completeBoundParser_sound
  · exact hcomplete

/-- Once the paper-level finite-chart completeness theorem is formalized,
this converts it into an actual computable `Decidable` value.

This definition is intentionally not an instance: installing a global
`Decidable (Γ ⇒ccg A)` before proving `CompleteBoundParserComplete q r` would hide the
main missing theorem. -/
def decidableOfParserComplete {q r : Nat} (hcomplete : CompleteBoundParserComplete q r)
    (Γ : List Category) (A : Category) : Decidable (Γ ⇒ccg A) :=
  if h : completeBoundParser q r Γ A = true then
    isTrue (completeBoundParser_sound h)
  else
    isFalse (fun hDerives => h (hcomplete hDerives))

/-- Typeclass wrapper for the eventual paper-completeness theorem at the fixed
rule-system constants.  Providing this witness upgrades instance search from
classical propositional decidability to the executable paper parser. -/
class ParserCompletenessWitness : Prop where
  complete : CompleteBoundParserComplete interfaceStateLimit traceNeighborLimit

/-- Parser-backed decidability, available as soon as the paper-completeness
witness is in scope. -/
instance instDecidableDerivableOfParserComplete [h : ParserCompletenessWitness]
    (Γ : List Category) (A : Category) : Decidable (Γ ⇒ccg A) :=
  decidableOfParserComplete h.complete Γ A

/-- Extract the fixed-constant parser completeness theorem from a
`ParserCompletenessWitness`.  This is the theorem-shaped interface requested by
downstream files that prefer not to depend directly on class projection syntax. -/
theorem completeBoundParserComplete_of_parserCompletenessWitness
    [h : ParserCompletenessWitness] :
    CompleteBoundParserComplete interfaceStateLimit traceNeighborLimit :=
  h.complete

/-- Package a proved fixed-constant parser completeness theorem as the witness
class that enables executable parser-backed decidability. -/
theorem parserCompletenessWitness_of_complete
    (h : CompleteBoundParserComplete interfaceStateLimit traceNeighborLimit) :
    ParserCompletenessWitness :=
  ⟨h⟩

/-- Build the fixed parser-completeness witness from the fixed
node-category-bound theorem.  This is the final packaging step needed after the
depth-counting normal-form proof is supplied. -/
theorem parserCompletenessWitness_of_nodeCategoryBoundComplete
    (h : NodeCategoryBoundComplete interfaceStateLimit traceNeighborLimit) :
    ParserCompletenessWitness :=
  parserCompletenessWitness_of_complete
    (completeBoundParserComplete_of_depthCountingComplete h)

/-- Build the fixed parser-completeness witness from the fixed depth-bounded
normal-form theorem. -/
theorem parserCompletenessWitness_of_depthBoundedNormalForm
    (h : DepthBoundedNormalForm interfaceStateLimit traceNeighborLimit) :
    ParserCompletenessWitness :=
  parserCompletenessWitness_of_complete
    (completeBoundParserComplete_of_depthBoundedNormalForm h)

/-- Build the fixed parser-completeness witness from the fixed size-bounded
normal-form theorem. -/
theorem parserCompletenessWitness_of_sizeBoundedNormalForm
    (h : SizeBoundedNormalForm interfaceStateLimit traceNeighborLimit) :
    ParserCompletenessWitness :=
  parserCompletenessWitness_of_complete
    (completeBoundParserComplete_of_sizeBoundedNormalForm h)

/-- Build the fixed parser-completeness witness from boundary-free-piece
contraction alone, via the repeatable-pair-free depth-counting bridge. -/
theorem parserCompletenessWitness_of_boundaryContracts
    (hboundary : BoundaryFreeInvisiblePieceContracts) :
    ParserCompletenessWitness :=
  parserCompletenessWitness_of_complete
    (completeBoundParserComplete_of_boundaryContracts hboundary)

/-- Parser-completeness witness from the faithful piece-level boundary-free
contraction target, without installing a global instance prematurely. -/
theorem parserCompletenessWitness_of_boundaryPieceContracts
    (hboundary : BoundaryFreeInvisiblePieceContractsFromPieces) :
    ParserCompletenessWitness :=
  parserCompletenessWitness_of_complete
    (completeBoundParserComplete_of_boundaryPieceContracts hboundary)

/-- Parser-completeness witness from the repaired two-case boundary-free
architecture, with the protected unary-skeleton case kept explicit. -/
theorem parserCompletenessWitness_of_replaceable_or_protected_boundaryPieces
    (hreplace : BoundaryFreeReplaceableInvisiblePieceContractsFromPieces)
    (hprotected : BoundaryFreeProtectedSkeletonPieceContracts) :
    ParserCompletenessWitness :=
  parserCompletenessWitness_of_complete
    (completeBoundParserComplete_of_replaceable_or_protected_boundaryPieces
      hreplace hprotected)

/-- Build the final parser-completeness witness from the explicit remaining
paper lemmas at the fixed constants. -/
theorem parserCompletenessWitness_of_branchZoneCounting
    (hrep : AllRepeatablePairsContract)
    (hboundary : BoundaryFreeInvisiblePieceElimination)
    (hcount : BranchZoneCountingComplete interfaceStateLimit traceNeighborLimit) :
    ParserCompletenessWitness :=
  parserCompletenessWitness_of_complete
    (completeBoundParserComplete_of_branchZoneCounting
      hrep hboundary hcount traceDegreeLimit_traceNeighborLimit)

/-- Final witness packaging in the paper-facing formulation where raw
repeatable pairs first yield transport-closed bands. -/
theorem parserCompletenessWitness_of_repeatablePairProducesBand_of_branchZoneCounting
    (hband : RepeatablePairProducesBand)
    (hboundary : BoundaryFreeInvisiblePieceElimination)
    (hcount : BranchZoneCountingComplete interfaceStateLimit traceNeighborLimit) :
    ParserCompletenessWitness :=
  parserCompletenessWitness_of_branchZoneCounting
    (allRepeatablePairsContract_of_repeatablePairProducesBand hband)
    hboundary hcount

/-- Fixed-constant parser witness from the local constructor-position branch
counting theorem. -/
theorem parserCompletenessWitness_of_constructorPositionCounting
    (hrep : AllRepeatablePairsContract)
    (hboundary : BoundaryFreeInvisiblePieceElimination)
    (hcount : BranchConstructorPositionCountingComplete interfaceStateLimit traceNeighborLimit) :
    ParserCompletenessWitness :=
  parserCompletenessWitness_of_branchZoneCounting hrep hboundary
    (branchZoneCountingComplete_of_constructorPositionCounting hcount)

/-- Paper-facing fixed-constant parser witness from transport-closed bands,
boundary elimination, and constructor-position branch counting. -/
theorem parserCompletenessWitness_of_repeatablePairProducesBand_of_constructorPositionCounting
    (hband : RepeatablePairProducesBand)
    (hboundary : BoundaryFreeInvisiblePieceElimination)
    (hcount : BranchConstructorPositionCountingComplete interfaceStateLimit traceNeighborLimit) :
    ParserCompletenessWitness :=
  parserCompletenessWitness_of_constructorPositionCounting
    (allRepeatablePairsContract_of_repeatablePairProducesBand hband)
    hboundary hcount

/-- Fixed-constant parser witness using local boundary-free-piece contraction
and constructor-position branch counting. -/
theorem parserCompletenessWitness_of_boundaryContracts_of_constructorPositionCounting
    (hrep : AllRepeatablePairsContract)
    (hboundary : BoundaryFreeInvisiblePieceContracts)
    (hcount : BranchConstructorPositionCountingComplete interfaceStateLimit traceNeighborLimit) :
    ParserCompletenessWitness :=
  parserCompletenessWitness_of_constructorPositionCounting hrep
    (boundaryFreeInvisiblePieceElimination_of_contracts hboundary)
    hcount

/-- Paper-facing fixed-constant witness using transport-closed bands,
boundary-free-piece contraction, and constructor-position branch counting. -/
theorem parserCompletenessWitness_of_repeatablePairProducesBand_of_boundaryContracts_of_constructorPositionCounting
    (hband : RepeatablePairProducesBand)
    (hboundary : BoundaryFreeInvisiblePieceContracts)
    (hcount : BranchConstructorPositionCountingComplete interfaceStateLimit traceNeighborLimit) :
    ParserCompletenessWitness :=
  parserCompletenessWitness_of_boundaryContracts_of_constructorPositionCounting
    (allRepeatablePairsContract_of_repeatablePairProducesBand hband)
    hboundary hcount

/-- Fixed-constant parser witness from the three local remaining proof targets:
repeatable-pair contraction witnesses, boundary-free-piece contraction, and
constructor-position branch counting. -/
theorem parserCompletenessWitness_of_contractionWitness_of_boundaryContracts_of_constructorPositionCounting
    (hwitness : RepeatablePairHasContractionWitness)
    (hboundary : BoundaryFreeInvisiblePieceContracts)
    (hcount : BranchConstructorPositionCountingComplete interfaceStateLimit traceNeighborLimit) :
    ParserCompletenessWitness :=
  parserCompletenessWitness_of_repeatablePairProducesBand_of_boundaryContracts_of_constructorPositionCounting
    (repeatablePairProducesBand_of_contractionWitness hwitness)
    hboundary hcount

/-! ## Closed examples

Until `CompleteBoundParserComplete q r` is proved globally, concrete closed sequents can
still be proved by computation on the parser side.  The final `decide` below is
on the `⇒ccg` proposition itself, using a local executable `Decidable` witness
obtained from parser soundness. -/

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

/-- The application-only `John loves Mary` derivation, similarly. -/
example : [# "np", (# "np" ⧹ # "s") ⧸ # "np", # "np"] ⇒ccg # "s" := by
  exact Derivable.appLeft (Γ := [# "np"]) (A := # "np") Derivable.leaf
    (Derivable.appRight (Γ := [(# "np" ⧹ # "s") ⧸ # "np"]) Derivable.leaf Derivable.leaf)

end Mathling.CCG
