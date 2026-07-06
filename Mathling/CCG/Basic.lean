import Mathling.CCG.Category
import Mathling.CCG.Derivation
import Mathling.CCG.Finite
import Mathling.CCG.Atoms
import Mathling.CCG.Tree
import Mathling.CCG.Occurrence
import Mathling.CCG.Trace
import Mathling.CCG.Band
import Mathling.CCG.Depth

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
* `Mathling.CCG.Band` — the band-contraction relation `Contracts`, its strict
  `size`-decrease, and the repeatable-pair/minimality interface.
* `Mathling.CCG.Depth` — node-addressed visibility/principal constructors,
  finite-candidate soundness, and the explicit depth-counting theorem.

Importing `Mathling.CCG.Basic` re-exports these layers, preserving the original public
surface.
-/
