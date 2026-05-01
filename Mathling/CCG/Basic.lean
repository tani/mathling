@[grind cases]
inductive Category where
  | atomic (name : String)
  | forward (a b : Category)
  | backward (a b : Category)
  deriving DecidableEq

prefix:65 "#" => Category.atomic
infixr:65 " / " => Category.forward
infixr:65 " \\ " => Category.backward

