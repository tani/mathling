import Mathling.CCG.Basic

namespace Classical

inductive Derives : List Category → Category → Prop where
  | word (u : Category) :
    Derives [u] u
  | applyFoward :
    Derives l (v / u) →
    Derives r u →
    Derives (l ++ r) v
  | applyBackward :
    Derives l u →
    Derives r (u \ v) →
    Derives (l ++ r) v

end Classical

