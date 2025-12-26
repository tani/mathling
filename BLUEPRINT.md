# BLUEPRINT

## Introduction

The **Lambek Calculus** ($L$) is a substructural logic designed for mathematical linguistics. Unlike standard propositional logic, it is non-commutative (order matters) and lacks contraction, weakening, and exchange rules. This makes it an ideal framework for modeling natural language syntax, where the order of words and their "consumption" of expected types are critical.

This project formalizes the Lambek Calculus in Lean 4, providing a verified environment for categorical grammar research.

## Preliminaries

In the Lambek Calculus, we deal with **types** (categories) and **sequents**.
- Types $A, B$ can be atoms (like $np$ for noun phrase, $s$ for sentence) or complex types formed by division.
- $A \setminus B$ (Left division): B missing an A on the left.
- $B / A$ (Right division): B missing an A on the right.
- A sequent has the form $\Gamma \Rightarrow A$, where $\Gamma$ is a non-empty list of types and $A$ is a single type.

## Formal Definitions of Lambek Calculus

The implementation in `Lambek/Basic.lean` defines the syntax and the inference rules.

The set of types is defined inductively:
- Atomic types: $p, q, \dots$
- Complex types: $A \setminus B$ and $B / A$ for types $A, B$.
  - `ldiv A B` corresponds to $A \setminus B$.
  - `rdiv B A` corresponds to $B / A$.

### Sequent Calculus

The calculus is implemented as an inductive proposition $\Gamma \Rightarrow A$, where $\Gamma$ is a list of types and $A$ is a type.

- **Axiom**: $A \Rightarrow A$
- **Right Rules**:
  - $(\setminus R)$: If $A, \Gamma \Rightarrow B$, then $\Gamma \Rightarrow A \setminus B$.
  - $(/ R)$: If $\Gamma, A \Rightarrow B$, then $\Gamma \Rightarrow B / A$.
  - *Condition*: $\Gamma$ must be non-empty.
- **Left Rules**:
  - $(\setminus L)$: If $\Delta \Rightarrow A$ and $\Gamma, B, \Lambda \Rightarrow C$, then $\Gamma, \Delta, A \setminus B, \Lambda \Rightarrow C$.
  - $(/ L)$: If $\Delta \Rightarrow A$ and $\Gamma, B, \Lambda \Rightarrow C$, then $\Gamma, B / A, \Delta, \Lambda \Rightarrow C$.

## Cut Admissibility

The Cut rule allows for compositional reasoning: if $\Delta \Rightarrow A$ and $[\Gamma, A, \Lambda] \Rightarrow B$, then $[\Gamma, \Delta, \Lambda] \Rightarrow B$. While useful for proving theorems, it makes search difficult.

### Main Theorem

We have proven that the Cut rule is admissible in $L$, meaning any sequent provable with Cut is also provable without it.

> **Theorem** (Cut Admissibility): 
> If $\Gamma \Rightarrow A$ and $\Delta, A, \Lambda \Rightarrow B$, then $\Delta, \Gamma, \Lambda \Rightarrow B$.

The proof is by nested, strong induction on a complexity measure consisting of the degree of the cut formula $A$ and the sum of the sizes of the two derivations. We perform a case analysis on the last rule used in the left derivation:

1. **Axiom**: If the left derivation is an axiom ($A \Rightarrow A$), then $\Gamma$ is just $A$. The goal becomes $\Delta, A, \Lambda \Rightarrow B$, which is exactly the right premise.
2. **Right Rules**: If the left derivation ends with a right rule ($(\setminus R)$ or $(/ R)$), the cut formula $A$ must be complex. We construct the proof by inverting the logical rules or applying the induction hypothesis to simpler cuts.
3. **Left Rules**: If the left derivation ends with a left rule acting on $\Gamma$, we permute the cut upwards. This requires splitting the context of the right premise into possible zones where the premises of the left inference might land. A specialized lemma handles the complex context matching for $\Delta, \Gamma, \Lambda$.

### Corollaries

> **Corollary** (Invertibility of Division):
> - If $\Gamma \Rightarrow A \setminus B$, then $A, \Gamma \Rightarrow B$.
> - If $\Gamma \Rightarrow B / A$, then $\Gamma, A \Rightarrow B$.

Both are proved by applying the Cut Admissibility theorem with the derivable identity sequents for $A \setminus B$ and $B / A$.

> **Theorem** (Generations of Atoms): 
> If $\Gamma$ consists only of atomic types and $\Gamma \Rightarrow s$ where $s$ is an atom, then $\Gamma = s$.

Proof by cases on the derivation. The only applicable rule for an atomic goal with atomic context is the Axiom. Left rules ($/L, \setminus L$) would require a complex type in $\Gamma$ as the principal formula, contradicting the assumption that $\Gamma$ contains only atoms.

## Decision Procedure

The Lambek calculus is decidable. We provide a verified decision procedure grounded in the cut-free sequent calculus.

> **Theorem** (Decidability): 
> For any context $\Gamma$ and type $A$, there exists a computational procedure to determine if $\Gamma \Rightarrow A$ is provable.

The algorithm performs a root-first search matching on the structure of the goal $A$:
1. **Case $A = A_1 \setminus A_2$**: Recursively check $A_1, \Gamma \Rightarrow A_2$. (Invertible Right Rule)
2. **Case $A = A_2 / A_1$**: Recursively check $\Gamma, A_1 \Rightarrow A_2$. (Invertible Right Rule)
3. **Case $A$ is an atom**:
   - If $\Gamma$ is exactly the atom $A$, return true (Axiom).
   - Otherwise, nondeterministically try all possible applications of Left Rules $(\setminus L)$ and $(/ L)$.
     - Iterate through every type $X \in \Gamma$.
     - If $X = C \setminus D$, split the context $\Gamma$ into $\Gamma_L, X, \Gamma_R$ and try to find a split of $\Gamma_L$ into $\Delta_1, \Delta_2$ such that $\Delta_2 \Rightarrow C$ and $\Delta_1, D, \Gamma_R \Rightarrow A$.
     - Similar logic applies for $X = D / C$.
   - If any valid derivation is found, return true. If all possibilities fail, return false.

Termination is guaranteed because in all recursive calls, a well-founded measure based on the total degree of types strictly decreases.
- **Right Rules**: For a goal $A \setminus B$, the measure reduces because we shift complexity from the goal to the context, but the overall structural complexity defined for termination decreases.
- **Left Rules**: These rules split the context, so the premises involve strictly smaller portions of the original sequent's complexity, while the goal remains atomic.

## Verified Parser for Lambek Grammar

*Status: To be implemented.*

A future component of this project is a verified parser that:
1. Takes a set of lexical assignments (e.g., "John" : $np$, "loves" : $(np \setminus s) / np$).
2. Converts a string of words into a sequent.
3. Uses the `derive` procedure to check grammaticality.

## Future Work

- **Product Type**: Add the multiplicative conjunction ($\otimes$) and its rules.
- **Grishin Interactions**: Explore extensions like the Symmetric Lambek Calculus.
- **Natural Deduction**: Formalize a natural deduction system for $L$.
- **Semantics**: Attach lambda-term annotations to derivations for compositional semantics.