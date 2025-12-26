import Std.Data.HashMap.Basic
import Mathling.Lambek.ProductFree.Basic
import Mathling.Lambek.ProductFree.Decidable

namespace Mathling.Lambek.ProductFree

/-
  Γ, A ごとの `Decidable (Γ ⇒ A)` を格納するメモ用のエントリ
-/
structure DeriveMemoEntry where
  Γ : List Tp
  A : Tp
  d : Decidable (Γ ⇒ A)

/-- `derive` 用メモテーブル（HashMap による実装） -/
abbrev DeriveMemo := Std.HashMap (List Tp × Tp) DeriveMemoEntry

namespace DeriveMemo

/-- すでに計算済みならメモから取り出す -/
def lookup (Γ : List Tp) (A : Tp) (memo : DeriveMemo) : Option (Decidable (Γ ⇒ A)) :=
  match memo[(Γ, A)]? with
  | none => none
  | some entry =>
      if hΓ : entry.Γ = Γ then
        if hA : entry.A = A then
          some (by
            cases hΓ
            cases hA
            exact entry.d)
        else
          none
      else
        none

/-- 新しい結果をメモに追加する -/
def insert (Γ : List Tp) (A : Tp) (d : Decidable (Γ ⇒ A)) (memo : DeriveMemo) :
    DeriveMemo :=
  Std.HashMap.insert memo (Γ, A) { Γ := Γ, A := A, d := d }

end DeriveMemo

/-
  メモテーブルを引数にとる内部版．
  `derive` と同じ帰結 `Decidable (Γ ⇒ A)` を返しつつ，
  再帰呼び出しの結果をメモする．
-/
mutual
  def deriveM_impl (Γ : List Tp) (A : Tp) (memo : DeriveMemo) :
      Decidable (Γ ⇒ A) × DeriveMemo :=
    match DeriveMemo.lookup Γ A memo with
    | some d => (d, memo)
    | none =>
        match A with
        | Tp.atom s =>
            if hax : Γ = [Tp.atom s] then
              let d := isTrue (by grind)
              (d, DeriveMemo.insert Γ (Tp.atom s) d memo)
            else
              let rdiv_cands := (rdiv_candidates Γ).attach
              match process_rdiv_cands s Γ rdiv_cands memo with
              | (Search.found ⟨cand_sub, _, h1, h2⟩, memo1) =>
                  let d := isTrue (by grind)
                  (d, DeriveMemo.insert Γ (Tp.atom s) d memo1)
              | (Search.not_found h_rdiv, memo1) =>
                  let ldiv_cands := (ldiv_candidates Γ).attach
                  match process_ldiv_cands s Γ ldiv_cands memo1 with
                  | (Search.found ⟨cand_sub, _, h1, h2⟩, memo2) =>
                      let d := isTrue (by grind)
                      (d, DeriveMemo.insert Γ (Tp.atom s) d memo2)
                  | (Search.not_found h_ldiv, memo2) =>
                      let d : Decidable (Γ ⇒ Tp.atom s) := isFalse (by
                        intro hder
                        cases hder
                        case ax => grind
                        case rdiv_l Δ A Γ_left B Λ d_arg d_main =>
                          let cand0 : RDivCand := ⟨Γ_left, B, A, Δ, Λ⟩
                          let cand_sub : {c // c ∈ rdiv_candidates (Γ_left ++ [B ⧸ A] ++ Δ ++ Λ)} :=
                            ⟨cand0, by grind⟩
                          apply h_rdiv ⟨cand_sub, by grind, by grind, by grind⟩
                        case ldiv_l Δ A Γ_left B Λ d_arg d_main =>
                          let cand0 : LDivCand := ⟨Γ_left, A, B, Δ, Λ⟩
                          let cand_sub : {c // c ∈ ldiv_candidates (Γ_left ++ Δ ++ [A ⧹ B] ++ Λ)} :=
                            ⟨cand0, by grind⟩
                          apply h_ldiv ⟨cand_sub, by grind, by grind, by grind⟩)
                      (d, DeriveMemo.insert Γ (Tp.atom s) d memo2)
        | Tp.ldiv A B =>
            let A' := Tp.ldiv A B
            if hΓ : Γ = [] then
              let d := isFalse (by grind)
              (d, DeriveMemo.insert Γ A' d memo)
            else
              match deriveM_impl ([A] ++ Γ) B memo with
              | (isTrue h, memo1) =>
                  let d := isTrue (by grind)
                  (d, DeriveMemo.insert Γ A' d memo1)
              | (isFalse h, memo1) =>
                  let d := isFalse (by grind)
                  (d, DeriveMemo.insert Γ A' d memo1)
        | Tp.rdiv B A =>
            let A' := Tp.rdiv B A
            if hΓ : Γ = [] then
              let d := isFalse (by grind)
              (d, DeriveMemo.insert Γ A' d memo)
            else
              match deriveM_impl (Γ ++ [A]) B memo with
              | (isTrue h, memo1) =>
                  let d := isTrue (by grind)
                  (d, DeriveMemo.insert Γ A' d memo1)
              | (isFalse h, memo1) =>
                  let d := isFalse (by grind)
                  (d, DeriveMemo.insert Γ A' d memo1)
  termination_by (list_degree Γ + tp_degree A, 1, 0)
  decreasing_by all_goals grind

  def process_rdiv_cands (s : String) (Γ : List Tp)
      (cands : List {c // c ∈ rdiv_candidates Γ}) (memo : DeriveMemo) :
      Search {x : {c // c ∈ rdiv_candidates Γ} // x ∈ cands ∧ (x.val.Δ ⇒ x.val.A) ∧ ((x.val.left ++ [x.val.B] ++ x.val.Λ) ⇒ Tp.atom s)} × DeriveMemo :=
    match cands with
    | [] => (Search.not_found (by intro ⟨x, hx, _⟩; cases hx), memo)
    | cand :: rest =>
        match deriveM_impl cand.val.Δ cand.val.A memo with
        | (isTrue h1, memo1) =>
            match deriveM_impl (cand.val.left ++ [cand.val.B] ++ cand.val.Λ) (Tp.atom s) memo1 with
            | (isTrue h2, memo2) =>
                (Search.found ⟨cand, by grind, h1, h2⟩, memo2)
            | (isFalse h2, memo2) =>
                 match process_rdiv_cands s Γ rest memo2 with
                 | (Search.found ⟨res, h_mem, h_p1, h_p2⟩, memo3) =>
                     (Search.found ⟨res, by grind, h_p1, h_p2⟩, memo3)
                 | (Search.not_found h, memo3) =>
                     (Search.not_found (by
                       intro ⟨x, hx_mem, hx_p1, hx_p2⟩
                       apply h ⟨x, ?_, hx_p1, hx_p2⟩
                       grind), memo3)
        | (isFalse h1, memo1) =>
             match process_rdiv_cands s Γ rest memo1 with
             | (Search.found ⟨res, h_mem, h_p1, h_p2⟩, memo2) =>
                 (Search.found ⟨res, by grind, h_p1, h_p2⟩, memo2)
             | (Search.not_found h, memo2) =>
                 (Search.not_found (by
                   intro ⟨x, hx_mem, hx_p1, hx_p2⟩
                   apply h ⟨x, ?_, hx_p1, hx_p2⟩
                   grind), memo2)
  termination_by (list_degree Γ + tp_degree (Tp.atom s), 0, cands.length)
  decreasing_by all_goals grind

  def process_ldiv_cands (s : String) (Γ : List Tp)
      (cands : List {c // c ∈ ldiv_candidates Γ}) (memo : DeriveMemo) :
      Search {x : {c // c ∈ ldiv_candidates Γ} // x ∈ cands ∧ (x.val.Δ ⇒ x.val.A) ∧ ((x.val.left ++ [x.val.B] ++ x.val.Λ) ⇒ Tp.atom s)} × DeriveMemo :=
    match cands with
    | [] => (Search.not_found (by intro ⟨x, hx, _⟩; cases hx), memo)
    | cand :: rest =>
        match deriveM_impl cand.val.Δ cand.val.A memo with
        | (isTrue h1, memo1) =>
            match deriveM_impl (cand.val.left ++ [cand.val.B] ++ cand.val.Λ) (Tp.atom s) memo1 with
            | (isTrue h2, memo2) =>
                (Search.found ⟨cand, by apply List.mem_cons_self, h1, h2⟩, memo2)
            | (isFalse h2, memo2) =>
                 match process_ldiv_cands s Γ rest memo2 with
                 | (Search.found ⟨res, h_mem, h_p1, h_p2⟩, memo3) =>
                     (Search.found ⟨res, by grind, h_p1, h_p2⟩, memo3)
                 | (Search.not_found h, memo3) =>
                     (Search.not_found (by
                       intro ⟨x, hx_mem, hx_p1, hx_p2⟩
                       apply h ⟨x, ?_, hx_p1, hx_p2⟩
                       grind), memo3)
        | (isFalse h1, memo1) =>
             match process_ldiv_cands s Γ rest memo1 with
             | (Search.found ⟨res, h_mem, h_p1, h_p2⟩, memo2) =>
                 (Search.found ⟨res, by grind, h_p1, h_p2⟩, memo2)
             | (Search.not_found h, memo2) =>
                 (Search.not_found (by
                   intro ⟨x, hx_mem, hx_p1, hx_p2⟩
                   apply h ⟨x, ?_, hx_p1, hx_p2⟩
                   grind), memo2)
  termination_by (list_degree Γ + tp_degree (Tp.atom s), 0, cands.length)
  decreasing_by all_goals grind
end

def deriveM (Γ : List Tp) (A : Tp) : Decidable (Γ ⇒ A) :=
  (deriveM_impl Γ A ∅).1

instance (Γ : List Tp) (A : Tp) : Decidable (Γ ⇒ A) := deriveM Γ A

-- An example of a simple derivation: (A / B) , B => A
example : [Tp.atom "A" ⧸ Tp.atom "B", Tp.atom "B"] ⇒ Tp.atom "A" := by
  decide

end Mathling.Lambek.ProductFree
