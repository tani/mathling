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

structure CategorialGrammar (α : Type _) (σ : Type _) where
  lexicon : σ → Category α → Prop
  start : Category α

