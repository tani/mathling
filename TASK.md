# Remaining automata–grammar relation work

The regular, epsilon-NFA, DPDA, and deterministic context-free-language edges
are implemented. This file records the remaining work needed to complete the
linear-grammar / one-turn-PDA part of the relation map.

## 1. Redesign `OneTurnNPDA`

The current `OneTurnNPDA.step` is a relation over complete stacks. It can
inspect and replace an arbitrary stack word, so it is not a finite-local PDA
and does not admit the standard linear-grammar characterization.

- Replace `step` with a finite `List (PushdownRule α (State × TurnPhase) Stack)`.
- Keep starts, accepting states, and the initial stack finite.
- Express the one-turn invariant over local rules:
  - computations start in `push`;
  - a transition from `pop` remains in `pop`;
  - a push-phase rule does not reduce stack height;
  - a rule entering or remaining in pop phase does not increase stack height.
- Define `OneTurnNPDA.toNPDA`, `Accepts`, and `language` through the shared
  local NPDA interpreter, and prove its language is preserved.

**Done when:** no OneTurn API can observe or replace an entire stack, and a
OneTurn machine can be forgotten to `NPDA` without changing its language.

## 2. Move the linear-grammar construction to local rules

`LinearGrammar.toOneTurnNPDA` currently depends on the non-local `step`
relation.

- Replace proof-carrying, arbitrary-list control states with a finite encoding
  based on a grammar rule and a position in that rule.
- Add a private bottom marker and enumerate the finite terminal support of the
  grammar.
- Compile each grammar action into finite local rules: rule choice, consuming a
  prefix symbol, pushing a suffix symbol, switching phase, matching a stack
  symbol, and final bottom-marker removal.
- Port the forward and reverse simulation invariants and re-prove
  `LinearGrammar.toOneTurnNPDA_language`.

**Done when:** the conversion has finite rules and still proves equality with
the source linear grammar language.

## 3. Normalize arbitrary one-turn machines

The reverse construction needs a small-step normal form.

- Introduce fresh bottom-marker and administrative state types.
- Normalize to one start and one final state, with acceptance after draining the
  bottom marker.
- Split a rule that pushes several stack symbols into finitely many `+1` and
  `0` stack-height microsteps.
- Retain only `+1`, `0`, and `-1` stack-height changes, and prove language
  preservation.

**Done when:** each normalized rule has one of the three height changes and
the normalizer has a proved language-preservation theorem.

## 4. Convert normalized one-turn machines to linear grammars

- Use nonterminals representing balanced push/pop spans over a fixed stack
  suffix (a `Bridge` state-pair construction).
- Emit linear productions for neutral push steps, neutral pop steps, a turn
  step, and paired grow/shrink steps.
- Prove, inductively, that grammar derivations are equivalent to balanced
  one-turn spans.
- Connect the start production to normalized accepting runs.

Public results to add:

- `OneTurnNPDA.toLinearGrammar`
- `OneTurnNPDA.toLinearGrammar_language`
- `OneTurnNPDA.language_isLinear`
- `Language.isLinear_iff_exists_oneTurnNPDA`

**Done when:** every finite-local OneTurn machine has a language-equivalent
`LinearGrammar`, and the final theorem proves the bidirectional
characterization.

## 5. Documentation and regression coverage

- Update the README edge between `Linear` and `OneTurn` to a proved
  bidirectional language-class equivalence.
- Add regression machines covering epsilon transitions, the empty word, a
  phase switch, neutral rules, and multi-symbol pushes before normalization.
- Keep each changed Lean module LiterateLean-compliant and document the
  normalizer and bridge invariant.
- Run:
  - `Scripts/check_visibility_policy.sh`
  - `Scripts/check_literatelean.sh`
  - `lake build --wfail`
  - `lake test`
  - `git diff --check`
