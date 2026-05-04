import Mathling.CCG.Basic

namespace Mathling

inductive Reduce : List Category → List Category → Prop where
  | forward (Γ : List Category) (u v : Category) (Γ' : List Category) :
    Reduce (Γ ++ (v / u) :: u :: Γ') (Γ ++ v :: Γ')
  | backward (Γ : List Category) (u v : Category) (Γ' : List Category) :
    Reduce (Γ ++ u :: (u \ v) :: Γ') (Γ ++ v :: Γ') 

end Mathling
