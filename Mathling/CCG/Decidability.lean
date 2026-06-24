import Mathling.CCG.Search
import Mathling.CCG.Soundness
import Mathling.CCG.Completeness
import Mathling.CCG.Parser

/-!
# Decision procedure for the eight-rule CCG system

This file is the stable public entry point for the CCG decision procedure.  The
contents were split into focused modules during refactoring:

* `Mathling.CCG.Search` — list-splitting helpers, the backward rule view
  `BackRule`, the one-step search combinators `unaryBack` / `binaryBack`, the
  fuel-bounded recognizer `recognizes`, its decidable wrapper, and the shared
  characterization lemmas.
* `Mathling.CCG.Soundness` — every successful recognizer run yields a `⇒ccg`
  derivation.
* `Mathling.CCG.Completeness` — fuel monotonicity and relative completeness over
  a sufficiently rich candidate set.
* `Mathling.CCG.Parser` — the recognizer/derivation equivalences, the
  `parseWithDepth` / `parseWithPaperBound` entry points, their soundness, and
  worked examples.

Importing `Mathling.CCG.Decidability` re-exports all of them, preserving the
original public surface.
-/
