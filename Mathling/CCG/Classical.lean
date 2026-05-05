import Mathling.CCG.Basic

namespace Mathling

inductive Reduce : List Category → List Category → Prop where
  | forward (Γ : List Category) (u v : Category) (Γ' : List Category) :
    Reduce (Γ ++ (v / u) :: u :: Γ') (Γ ++ v :: Γ')
  | backward (Γ : List Category) (u v : Category) (Γ' : List Category) :
    Reduce (Γ ++ u :: (u \ v) :: Γ') (Γ ++ v :: Γ') 

def reduceCore (l r : List Category) : List (List Category) :=
  match r with
  | [] => []
  | [_] => []
  | x₁ :: x₂ :: xs =>
    let l' := l.concat x₁
    let r' := x₂ :: xs
    let recursiveResult := reduceCore l' r'
    match x₁, x₂ with
    | .forward v u, _ =>
      if u == x₂ then
        (l ++ v :: xs) :: recursiveResult
      else
        recursiveResult
    | _, .backward u v =>
      if u == x₁ then
        (l ++ v :: xs) :: recursiveResult
      else
        recursiveResult
    | _, _ =>
      recursiveResult

def reduce (cats : List Category) : List (List Category) :=
  reduceCore [] cats

end Mathling
