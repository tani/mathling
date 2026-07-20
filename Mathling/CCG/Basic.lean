module

public import Mathling.CCG.Category
public import Mathling.CCG.Derivation
public import Mathling.CCG.Finite
public import Mathling.CCG.Atoms
public import Mathling.CCG.Tree
public import Mathling.CCG.Occurrence
public import Mathling.CCG.Trace
public import Mathling.CCG.Band
public import Mathling.CCG.Depth
public import Mathling.CCG.Protected

@[expose] public section

/-!
# Basic definitions for the eight-rule CCG system

This file is the stable public entry point for the CCG syntax and derivation
layers.  The contents were split into focused modules during refactoring:

* `Mathling.CCG.Category` — categories `Category`, notation, structural measures
  (`depth`, `constructors`, `atoms`), context measures, the schematic bounds
  `V`/`H`, and the finite candidate-set generator `categoryPool`.
* `Mathling.CCG.Derivation` — the binary rule schemata `Rule`, the
  derivability relation `⇒ccg`, the eight rule wrappers, and atom-homomorphism
  preservation.
* `Mathling.CCG.Finite` — the paper §23 proof that `categoriesWithDepthAtMost` /
  `categoryPool` contains every category bounded by atoms and depth.
* `Mathling.CCG.Tree` — explicit `Type`-valued derivation trees `DerivationTree`, the
  size measure `size`, and `Derivable.exists_derivationTree`.
* `Mathling.CCG.Occurrence` — category positions `CategoryPath`, subterm read/replace,
  and the constructor-count/atom lemmas used by band contraction.
* `Mathling.CCG.Trace` — node-category occurrences, the visibility
  classification, and the size-minimal derivation tree `D_min`.
* `Mathling.CCG.Band` — the contraction relation and boundary-free
  invisible-piece elimination, replaceable case proved.
* `Mathling.CCG.Depth` — the sharp branch-counting theorem H = V + V*r.
* `Mathling.CCG.Protected` — the structural-induction reduction of the
  protected-skeleton obligation to the root-crossing case
  (`CrossingBoundaryFreeSkeletonPieceHasRedex`).

Importing `Mathling.CCG.Basic` re-exports these layers, preserving the original public
surface.
-/
