import Mathlib.Data.Finset.Prod

universe u

variable {α : Type u} [DecidableEq α]

inductive category (α : Type u) where
  | Atom : α → category α
  | Fwd : category α → category α → category α
  | Bwd : category α → category α → category α
  deriving DecidableEq

infixl:70 " /> "   => category.Fwd
infixl:70 " \\> "  => category.Bwd

/-- A combinator
  x/y y => x
  y y\x => x
-/
def a_comb_f : category α → category α → Option (category α)
  | a /> b, b' => if b = b' then some a else none
  | _, _ => none

def a_comb_b : category α → category α → Option (category α)
  | b', b \> a => if b = b' then some a else none
  | _, _ => none

/-- B combinator
  x/y y/z => x/z
  x\y y\z => x\z
-/
def b_comb : category α → category α → Option (category α)
  | a /> b, b' /> c => if b = b' then some (a /> c) else none
  | a \> b, b' \> c => if b = b' then some (a \> c) else none
  | _, _ => none

-- Bn combinator (TODO)

/-- Bx combinator
  x/y z\y => z\x
  y/z y\x => x/z
-/
def bx_comb_f : category α → category α → Option (category α)
  | a /> b, c \> b' => if b = b' then some (c \> a) else none
  | _, _ => none

def bx_comb_b : category α → category α → Option (category α)
  | b /> c, b' \> a => if b = b' then some (a /> c) else none
  | _, _ => none

/-- T combinator
  x => y/(x\y)
  x => (y/x)\y -/
def t_comb_f (y : category α) : category α → category α :=
  fun x ↦ y /> (x \> y)

def t_comb_b (y : category α) : category α → category α :=
  fun x ↦  (y /> x) \> y

structure CCG (α t : Type u) [DecidableEq t] where
  A' : Finset α
  Sigma : Finset t
  L : Finset (t × category α)
  s' : category α

section
variable {s a b c : α} {A B C : t} [DecidableEq t]

def l_example (s a b c : α) (A B C : t) : Finset (t × category α) :=
  { (A, category.Atom a),
    (B, .Atom s /> .Atom c \> .Atom a),
    (B, .Atom b /> .Atom c \> .Atom a),
    (B, .Atom s /> .Atom c /> .Atom b \> .Atom a),
    (B, .Atom b /> .Atom c /> .Atom b \> .Atom a),
    (C, .Atom c)
  }

def ccg_example : CCG α t :=
  {A' := {s,a,b,c}, Sigma := {A,B,C}, L := l_example s a b c A B C, s' := .Atom s}

end
