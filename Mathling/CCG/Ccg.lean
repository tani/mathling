universe u

variable {α : Type u} [DecidableEq α]

section Lean.Parser.Category

inductive Dir : Type
  | Fwd -- /
  | Bwd -- \
  deriving DecidableEq

inductive Cat (α : Type u) where
  | Atom : α → Cat α
  | Fun : Dir → Cat α → Cat α → Cat α
  deriving DecidableEq

infixl:70 " /> "   => Cat.Fun Dir.Fwd
infixl:70 " \\> "  => Cat.Fun Dir.Bwd

section Combinator

/-- A combinator
  x/y y => x
  y x\y => y -/
def a_comb_f : Cat α → Cat α → Option (Cat α)
  | .Fun .Fwd a b, b' => if b = b' then some a else none
  | _, _ => none

def a_comb_b : Cat α → Cat α → Option (Cat α)
  | b', .Fun .Bwd a b => if b = b' then some a else none
  | _, _ => none

/-- B combinator
  x/y y/z => x/z
  x\y y\z => x\z -/
def b_comb : Cat α → Cat α → Option (Cat α)
  | .Fun .Fwd a b, .Fun .Fwd b' c => if b = b' then some (.Fun .Fwd a c) else none
  | .Fun .Bwd a b, .Fun .Bwd b' c => if b = b' then some (.Fun .Bwd a c) else none
  | _, _ => none

/-- Bx combinator
  x/y z\y => z/y
  x/y y\z => x\z -/
def bx_comb_f : Cat α → Cat α → Option (Cat α)
  | .Fun .Fwd a b, .Fun .Bwd c a' => if a = a' then some (.Fun .Fwd c b) else none
  | _, _ => none

def bx_comb_b : Cat α → Cat α → Option (Cat α)
  | .Fun .Fwd a b, .Fun .Bwd b' c => if b = b' then some (.Fun .Bwd a c) else none
  | _, _ => none

/-- T combinator
  x => y/(y\x)
  x => y\(y/x) -/
def t_comb_f (y : Cat α) : Cat α → Cat α :=
  fun x ↦ y /> (y \> x)

def t_comb_b (y : Cat α) : Cat α → Cat α :=
  fun x ↦ y \> (y /> x)

/-- D combinator
  x/y => (x/z)/(y/z)
  x\y => (x\z)\(y\z) -/
def d_comb (z : Cat α) : Cat α → Option (Cat α)
  | .Fun .Fwd x y => some (.Fun .Fwd (.Fun .Fwd x z) (.Fun .Fwd y z))
  | .Fun .Bwd x y => some (.Fun .Bwd (.Fun .Bwd x z) (.Fun .Bwd y z))
  | _ => none

/-- Q combinator
  x/y => (z/y)\(z/x)
  x\y => (z\y)/(z\x) -/
def q_comb (z : Cat α) : Cat α → Option (Cat α)
  | .Fun .Fwd x y => some (.Fun .Bwd (.Fun .Fwd z y) (.Fun .Fwd z x))
  | .Fun .Bwd x y => some (.Fun .Fwd (.Fun .Bwd z y) (.Fun .Bwd z x))
  | _ => none

end Combinator

section Grammar

class CG (a : Type u) [DecidableEq a] where
  a_comb_f : Cat a → Cat a → Option (Cat a)
  a_comb_b : Cat a → Cat a → Option (Cat a)

instance (α : Type u) [DecidableEq α] : CG α where
  a_comb_f := a_comb_f
  a_comb_b := a_comb_b

class CGB (a : Type u) [DecidableEq a] [CG a] where
  b_comb : Cat a → Cat a → Option (Cat a)

instance (α : Type u) [DecidableEq α] : CGB α where
  b_comb := b_comb

class CGT (a : Type u) [DecidableEq a] [CG a] where
  t_comb_f (_ : Cat a): Cat a → Cat a
  t_comb_b (_ : Cat a) : Cat a → Cat a

instance (α : Type u) [DecidableEq α] : CGT α where
  t_comb_f := t_comb_f
  t_comb_b := t_comb_b

class CGBT (a : Type u) [DecidableEq a] extends CGB a, CGT a

end Grammar
