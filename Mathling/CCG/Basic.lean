import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic

inductive Direction
| forward
| backward

inductive Category (α : Type _)
| atomic (a : α)
| slash (d : Direction) (l r : Category α)

prefix:65 "#" => Category.atomic
infixr:65 " / " => Category.slash Direction.forward
infixr:65 " \\ " => Category.slash Direction.backward

abbrev UnaryRule α := Set (Category α × Category α)
abbrev BinaryRule α := Set (Category α × Category α × Category α)

inductive TypeRaising {α : Type _} : UnaryRule α
| forward (x t : Category α) : TypeRaising (x, t/(t\x))
| backward (x t : Category α) : TypeRaising (x, t\(t/x))

inductive Application {α : Type _} : BinaryRule α
| forward (x y : Category α) : Application (x/y, y, x)
| backward (x y : Category α) : Application (y, x\y, x)

inductive Composition {α : Type _} : BinaryRule α
| forward (x y z : Category α) : Composition (x/y, y/z, x/z)
| backward (x y z : Category α) : Composition (y\z, x\y, x\z)

inductive CrossedComposition {α : Type _} : BinaryRule α
| forward (x y z : Category α) : CrossedComposition (x/y, y\z, x\z)
| backward (x y z : Category α) : CrossedComposition (y\z, x/y, x/z)

structure CategorialGrammar where
  α : Type _
  σ : Type _
  lexicon : Finset (σ × Category α)
  start : Category α
  u : UnaryRule α
  b : BinaryRule α

inductive DerivationTree
  (g : CategorialGrammar) :
  List g.σ → Category g.α → Type _
| leaf
  (s : g.σ)
  (c : Category g.α)
  (h : (s, c) ∈ g.lexicon) :
  DerivationTree g [s] c
| unary
  {w : List g.σ}
  (l r : Category g.α)
  (t : DerivationTree g w l)
  (h : (l, r) ∈ g.u) :
  DerivationTree g w r
| binary
  {w₁ w₂ : List g.σ}
  (l₁ l₂ r : Category g.α)
  (t₁ : DerivationTree g w₁ l₁)
  (t₂ : DerivationTree g w₂ l₂)
  (h : (l₁, l₂, r) ∈ g.b) :
  DerivationTree g (w₁ ++ w₂) r

