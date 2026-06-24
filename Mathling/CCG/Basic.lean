import Mathling.CCG.Category
import Mathling.CCG.Derivation

/-!
# Basic definitions for the eight-rule CCG system

This file is the stable public entry point for the CCG syntax and derivation
layers.  The contents were split into focused modules during refactoring:

* `Mathling.CCG.Category` — categories `Tp`, notation, structural measures
  (`depth`, `constructors`, `atoms`), context measures, the schematic bounds
  `V`/`H`, and the finite candidate-set generator `candidateCategories`.
* `Mathling.CCG.Derivation` — the binary rule schemata `BinaryRule`, the
  derivability relation `⇒ccg`, the eight rule wrappers, and atom-homomorphism
  preservation.

Importing `Mathling.CCG.Basic` re-exports both, preserving the original public
surface.
-/
