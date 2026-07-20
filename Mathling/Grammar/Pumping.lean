module

public import Mathling.Grammar.ChomskyNormal.Classical

@[expose] public section

/-!
# Pumping lemma for context-free languages

Parse-tree height counts nodes: a leaf has height `1`, and a binary node has
height one plus the maximum height of its children.
-/

namespace Mathling.Grammar

universe u

variable {T : Type u}

/-- A nonempty derivation tree for a grammar in Chomsky normal form. -/
inductive ParseTree (g : ChomskyNormalGrammar T) : g.cfg.NT → Type u where
  | leaf (A : g.cfg.NT) (a : T)
      (h : ({ input := A, output := [Symbol.terminal a] } :
        ContextFreeRule T g.cfg.NT) ∈ g.cfg.rules) : ParseTree g A
  | node (A B C : g.cfg.NT)
      (h : ({ input := A, output := [Symbol.nonterminal B, Symbol.nonterminal C] } :
        ContextFreeRule T g.cfg.NT) ∈ g.cfg.rules)
      (l : ParseTree g B) (r : ParseTree g C) : ParseTree g A

namespace ParseTree

/-- The terminal word along the leaves of a parse tree. -/
def yield {g : ChomskyNormalGrammar T} {A : g.cfg.NT} :
    ParseTree g A → List T
  | .leaf _ a _ => [a]
  | .node _ _ _ _ l r => yield l ++ yield r

/-- Node height, with leaves at height one. -/
def height {g : ChomskyNormalGrammar T} {A : g.cfg.NT} :
    ParseTree g A → Nat
  | .leaf _ _ _ => 1
  | .node _ _ _ _ l r => 1 + max (height l) (height r)

@[simp] theorem one_le_height {g : ChomskyNormalGrammar T} {A : g.cfg.NT}
    (t : ParseTree g A) : 1 ≤ height t := by
  cases t <;> simp [height]

@[simp] theorem one_le_yield_length {g : ChomskyNormalGrammar T} {A : g.cfg.NT}
    (t : ParseTree g A) : 1 ≤ (yield t).length := by
  induction t with
  | leaf => simp [yield]
  | node A B C h l r ihl ihr =>
      simp only [yield, List.length_append]
      omega

/-- A binary parse tree of height `h` has at most `2^(h-1)` leaves. -/
theorem yield_length_le {g : ChomskyNormalGrammar T} {A : g.cfg.NT}
    (t : ParseTree g A) : (yield t).length ≤ 2 ^ (height t - 1) := by
  induction t with
  | leaf => simp [yield, height]
  | node A B C h l r ihl ihr =>
      simp only [yield, height, List.length_append]
      let m := max (height l) (height r)
      have hlm : height l ≤ m := Nat.le_max_left _ _
      have hrm : height r ≤ m := Nat.le_max_right _ _
      have hlpow : 2 ^ (height l - 1) ≤ 2 ^ (m - 1) :=
        Nat.pow_le_pow_right (by omega) (Nat.sub_le_sub_right hlm 1)
      have hrpow : 2 ^ (height r - 1) ≤ 2 ^ (m - 1) :=
        Nat.pow_le_pow_right (by omega) (Nat.sub_le_sub_right hrm 1)
      calc
        (yield l).length + (yield r).length
            ≤ 2 ^ (height l - 1) + 2 ^ (height r - 1) := Nat.add_le_add ihl ihr
        _ ≤ 2 ^ (m - 1) + 2 ^ (m - 1) := Nat.add_le_add hlpow hrpow
        _ = 2 * 2 ^ (m - 1) := by omega
        _ = 2 ^ (m - 1 + 1) := by rw [Nat.pow_succ']
        _ = 2 ^ m := by
          congr 1
          have hm : 1 ≤ m := le_trans (one_le_height l) hlm
          omega
        _ = 2 ^ (1 + m - 1) := by
          congr 1
          omega

/-- A parse tree witnesses a grammar derivation of its yield. -/
theorem yield_derives {g : ChomskyNormalGrammar T} {A : g.cfg.NT}
    (t : ParseTree g A) :
    g.cfg.Derives [Symbol.nonterminal A] (terminalSymbols (yield t)) := by
  induction t with
  | leaf A a h =>
      exact ContextFreeGrammar.Produces.single
        ⟨_, h, ContextFreeRule.Rewrites.input_output⟩
  | node A B C h l r ihl ihr =>
      apply (ContextFreeGrammar.Produces.single
        ⟨_, h, ContextFreeRule.Rewrites.input_output⟩).trans
      have hl := ihl.append_right [Symbol.nonterminal C]
      have hr := ihr.append_left (terminalSymbols (yield l))
      change g.cfg.Derives [Symbol.nonterminal B, Symbol.nonterminal C]
        (terminalSymbols (yield l ++ yield r))
      simpa [terminalSymbols, List.map_append, List.append_assoc] using hl.trans hr

end ParseTree

/-- A typed one-hole context in a CNF parse tree. -/
inductive ParseCtx (g : ChomskyNormalGrammar T) : g.cfg.NT → g.cfg.NT → Type u where
  | hole (A : g.cfg.NT) : ParseCtx g A A
  | left (A B C X : g.cfg.NT)
      (h : ({ input := A, output := [Symbol.nonterminal B, Symbol.nonterminal C] } :
        ContextFreeRule T g.cfg.NT) ∈ g.cfg.rules)
      (c : ParseCtx g B X) (r : ParseTree g C) : ParseCtx g A X
  | right (A B C X : g.cfg.NT)
      (h : ({ input := A, output := [Symbol.nonterminal B, Symbol.nonterminal C] } :
        ContextFreeRule T g.cfg.NT) ∈ g.cfg.rules)
      (l : ParseTree g B) (c : ParseCtx g C X) : ParseCtx g A X

namespace ParseCtx

/-- Fill a parse context's hole. -/
def plug {g : ChomskyNormalGrammar T} {A X : g.cfg.NT} :
    ParseCtx g A X → ParseTree g X → ParseTree g A
  | .hole _, t => t
  | .left A B C X h c r, t => .node A B C h (plug c t) r
  | .right A B C X h l c, t => .node A B C h l (plug c t)

/-- Terminals strictly to the left of a context's hole. -/
def preYield {g : ChomskyNormalGrammar T} {A X : g.cfg.NT} :
    ParseCtx g A X → List T
  | .hole _ => []
  | .left _ _ _ _ _ c _ => preYield c
  | .right _ _ _ _ _ l c => ParseTree.yield l ++ preYield c

/-- Terminals strictly to the right of a context's hole. -/
def postYield {g : ChomskyNormalGrammar T} {A X : g.cfg.NT} :
    ParseCtx g A X → List T
  | .hole _ => []
  | .left _ _ _ _ _ c r => postYield c ++ ParseTree.yield r
  | .right _ _ _ _ _ _ c => postYield c

/-- The maximum contextual contribution to the height of a plugged tree. -/
def ctxHeight {g : ChomskyNormalGrammar T} {A X : g.cfg.NT} :
    ParseCtx g A X → Nat
  | .hole _ => 0
  | .left _ _ _ _ _ c r => 1 + max (ctxHeight c) (ParseTree.height r)
  | .right _ _ _ _ _ l c => 1 + max (ParseTree.height l) (ctxHeight c)

/-- A context is proper when its hole is strictly below its root. -/
def IsProper {g : ChomskyNormalGrammar T} {A X : g.cfg.NT} :
    ParseCtx g A X → Prop
  | .hole _ => False
  | .left _ _ _ _ _ _ _ => True
  | .right _ _ _ _ _ _ _ => True

@[simp] theorem yield_plug {g : ChomskyNormalGrammar T} {A X : g.cfg.NT}
    (c : ParseCtx g A X) (t : ParseTree g X) :
    ParseTree.yield (plug c t) =
      preYield c ++ ParseTree.yield t ++ postYield c := by
  induction c with
  | hole => simp [plug, preYield, postYield]
  | left A B C X h c r ih =>
      simp [plug, ParseTree.yield, preYield, postYield, ih, List.append_assoc]
  | right A B C X h l c ih =>
      simp [plug, ParseTree.yield, preYield, postYield, ih, List.append_assoc]

@[simp] theorem height_plug_le {g : ChomskyNormalGrammar T} {A X : g.cfg.NT}
    (c : ParseCtx g A X) (t : ParseTree g X) :
    ParseTree.height (plug c t) ≤ ctxHeight c + ParseTree.height t := by
  induction c with
  | hole => simp [plug, ctxHeight]
  | left A B C X h c r ih =>
      simp only [plug, ParseTree.height, ctxHeight]
      have hc := ih t
      have hleft := Nat.le_max_left (ctxHeight c) (ParseTree.height r)
      have hright := Nat.le_max_right (ctxHeight c) (ParseTree.height r)
      omega
  | right A B C X h l c ih =>
      simp only [plug, ParseTree.height, ctxHeight]
      have hc := ih t
      have hleft := Nat.le_max_left (ParseTree.height l) (ctxHeight c)
      have hright := Nat.le_max_right (ParseTree.height l) (ctxHeight c)
      omega

/-- A proper context contributes at least one terminal outside its hole. -/
theorem proper_yield_pos {g : ChomskyNormalGrammar T} {A X : g.cfg.NT}
    (c : ParseCtx g A X) (hc : IsProper c) :
    1 ≤ (preYield c ++ postYield c).length := by
  cases c with
  | hole => simp [IsProper] at hc
  | left A B C X h c r =>
      simp only [preYield, postYield, List.length_append]
      have hr := ParseTree.one_le_yield_length r
      omega
  | right A B C X h l c =>
      simp only [preYield, postYield, List.length_append]
      have hl := ParseTree.one_le_yield_length l
      omega

/-- Compose contexts by grafting the second context at the first context's hole. -/
def compose {g : ChomskyNormalGrammar T} {A X Y : g.cfg.NT} :
    ParseCtx g A X → ParseCtx g X Y → ParseCtx g A Y
  | .hole _, d => d
  | .left A B C X h c r, d => .left A B C Y h (compose c d) r
  | .right A B C X h l c, d => .right A B C Y h l (compose c d)

@[simp] theorem plug_compose {g : ChomskyNormalGrammar T} {A X Y : g.cfg.NT}
    (c : ParseCtx g A X) (d : ParseCtx g X Y) (t : ParseTree g Y) :
    plug (compose c d) t = plug c (plug d t) := by
  induction c with
  | hole => rfl
  | left A B C X h c r ih => simp [compose, plug, ih]
  | right A B C X h l c ih => simp [compose, plug, ih]

@[simp] theorem preYield_compose {g : ChomskyNormalGrammar T} {A X Y : g.cfg.NT}
    (c : ParseCtx g A X) (d : ParseCtx g X Y) :
    preYield (compose c d) = preYield c ++ preYield d := by
  induction c with
  | hole => simp [compose, preYield]
  | left A B C X h c r ih => simp [compose, preYield, ih]
  | right A B C X h l c ih =>
      simp [compose, preYield, ih, List.append_assoc]

@[simp] theorem postYield_compose {g : ChomskyNormalGrammar T} {A X Y : g.cfg.NT}
    (c : ParseCtx g A X) (d : ParseCtx g X Y) :
    postYield (compose c d) = postYield d ++ postYield c := by
  induction c with
  | hole => simp [compose, postYield]
  | left A B C X h c r ih =>
      simp [compose, postYield, ih, List.append_assoc]
  | right A B C X h l c ih => simp [compose, postYield, ih]

/-- Plugging a context cannot decrease the height of its argument. -/
theorem height_le_plug {g : ChomskyNormalGrammar T} {A X : g.cfg.NT}
    (c : ParseCtx g A X) (t : ParseTree g X) :
    ParseTree.height t ≤ ParseTree.height (plug c t) := by
  induction c with
  | hole => simp [plug]
  | left A B C X h c r ih =>
      simp only [plug, ParseTree.height]
      exact le_trans (ih t)
        (le_trans (Nat.le_max_left _ _) (Nat.le_add_left _ _))
  | right A B C X h l c ih =>
      simp only [plug, ParseTree.height]
      exact le_trans (ih t)
        (le_trans (Nat.le_max_right _ _) (Nat.le_add_left _ _))

end ParseCtx


/-- Every height between one and a tree's height occurs at some subtree. -/
theorem ParseTree.exists_subtree_height_eq
    {g : ChomskyNormalGrammar T} {A : g.cfg.NT} {k : Nat}
    (t : ParseTree g A) (hk : 1 ≤ k) (hk' : k ≤ t.height) :
    ∃ (X : g.cfg.NT) (c : ParseCtx g A X) (s : ParseTree g X),
      c.plug s = t ∧ s.height = k := by
  induction t generalizing k with
  | leaf A a h =>
      have hkeq : k = 1 := by
        simp only [ParseTree.height] at hk'
        omega
      subst k
      exact ⟨A, .hole A, .leaf A a h, rfl, rfl⟩
  | node A B C h l r ihl ihr =>
      by_cases heq : k = ParseTree.height (.node A B C h l r)
      · subst k
        exact ⟨A, .hole A, .node A B C h l r, rfl, rfl⟩
      · have hlt : k < ParseTree.height (.node A B C h l r) :=
          lt_of_le_of_ne hk' heq
        have hkmax : k ≤ max l.height r.height := by
          simp only [ParseTree.height] at hlt
          omega
        by_cases hkl : k ≤ l.height
        · obtain ⟨X, c, s, hplug, hs⟩ := ihl hk hkl
          exact ⟨X, .left A B C X h c r, s,
            by simp [ParseCtx.plug, hplug], hs⟩
        · have hkr : k ≤ r.height := by
            exact (le_max_iff.mp hkmax).resolve_left hkl
          obtain ⟨X, c, s, hplug, hs⟩ := ihr hk hkr
          exact ⟨X, .right A B C X h l c, s,
            by simp [ParseCtx.plug, hplug], hs⟩

/-- A root-to-leaf branch, represented by its successive parse-tree roots. -/
inductive Spine (g : ChomskyNormalGrammar T) :
    {A : g.cfg.NT} → ParseTree g A → Type u where
  | stop (A : g.cfg.NT) (t : ParseTree g A) : Spine g t
  | downLeft (A B C : g.cfg.NT)
      (h : ({ input := A, output := [Symbol.nonterminal B, Symbol.nonterminal C] } :
        ContextFreeRule T g.cfg.NT) ∈ g.cfg.rules)
      (l : ParseTree g B) (r : ParseTree g C) (b : Spine g l) :
      Spine g (.node A B C h l r)
  | downRight (A B C : g.cfg.NT)
      (h : ({ input := A, output := [Symbol.nonterminal B, Symbol.nonterminal C] } :
        ContextFreeRule T g.cfg.NT) ∈ g.cfg.rules)
      (l : ParseTree g B) (r : ParseTree g C) (b : Spine g r) :
      Spine g (.node A B C h l r)

namespace Spine

/-- Variables encountered along a branch. -/
def vars {g : ChomskyNormalGrammar T} {A : g.cfg.NT}
    {t : ParseTree g A} : Spine g t → List g.cfg.NT
  | .stop A _ => [A]
  | .downLeft A _ _ _ _ _ b => A :: vars b
  | .downRight A _ _ _ _ _ b => A :: vars b

/-- Choose a branch whose length is the height of the tree. -/
def longest {g : ChomskyNormalGrammar T} {A : g.cfg.NT}
    (t : ParseTree g A) : Spine g t :=
  match t with
  | .leaf A a h => .stop A (.leaf A a h)
  | .node A B C h l r =>
      if r.height ≤ l.height then
        .downLeft A B C h l r (longest l)
      else
        .downRight A B C h l r (longest r)
termination_by sizeOf t

@[simp] theorem vars_longest_length
    {g : ChomskyNormalGrammar T} {A : g.cfg.NT}
    (t : ParseTree g A) : (vars (longest t)).length = t.height := by
  induction t with
  | leaf => simp [longest, vars, ParseTree.height]
  | node A B C h l r ihl ihr =>
      simp only [longest]
      split
      · simp [vars, ParseTree.height, ihl, max_eq_left ‹_›, Nat.add_comm]
      · have hlr : l.height ≤ r.height := Nat.le_of_lt (Nat.lt_of_not_ge ‹_›)
        simp [vars, ParseTree.height, ihr, max_eq_right hlr, Nat.add_comm]

/-- The root variable of every parse tree occurs in the grammar's active support. -/
theorem root_mem_active
    {g : ChomskyNormalGrammar T} {A : g.cfg.NT} (t : ParseTree g A) :
    A ∈ ContextFreeGrammar.activeNonterminals g.cfg := by
  cases t with
  | leaf A a h => exact ContextFreeGrammar.rule_input_mem_activeNonterminals g.cfg h
  | node A B C h l r =>
      exact ContextFreeGrammar.rule_input_mem_activeNonterminals g.cfg h

theorem vars_mem_active
    {g : ChomskyNormalGrammar T} {A : g.cfg.NT} {t : ParseTree g A}
    (b : Spine g t) :
    ∀ X ∈ vars b, X ∈ ContextFreeGrammar.activeNonterminals g.cfg := by
  induction b with
  | stop A t =>
      intro X hX
      simp only [vars, List.mem_singleton] at hX
      subst X
      exact root_mem_active t
  | downLeft A B C h l r b ih =>
      intro X hX
      simp only [vars, List.mem_cons] at hX
      rcases hX with hEq | hX
      · subst X
        exact ContextFreeGrammar.rule_input_mem_activeNonterminals g.cfg h
      · exact ih X hX
  | downRight A B C h l r b ih =>
      intro X hX
      simp only [vars, List.mem_cons] at hX
      rcases hX with hEq | hX
      · subst X
        exact ContextFreeGrammar.rule_input_mem_activeNonterminals g.cfg h
      · exact ih X hX

/-- An entry on a branch determines a subtree and the context above it. -/
theorem exists_context_of_mem
    {g : ChomskyNormalGrammar T} {A : g.cfg.NT} {t : ParseTree g A}
    (b : Spine g t) {X : g.cfg.NT} (hX : X ∈ vars b) :
    ∃ (c : ParseCtx g A X) (s : ParseTree g X), c.plug s = t := by
  induction b with
  | stop A t =>
      simp only [vars, List.mem_singleton] at hX
      subst X
      exact ⟨.hole A, t, rfl⟩
  | downLeft A B C h l r b ih =>
      simp only [vars, List.mem_cons] at hX
      rcases hX with hEq | hX
      · subst X
        exact ⟨.hole A, .node A B C h l r, rfl⟩
      · obtain ⟨c, s, hs⟩ := ih hX
        exact ⟨.left A B C X h c r, s, by simp [ParseCtx.plug, hs]⟩
  | downRight A B C h l r b ih =>
      simp only [vars, List.mem_cons] at hX
      rcases hX with hEq | hX
      · subst X
        exact ⟨.hole A, .node A B C h l r, rfl⟩
      · obtain ⟨c, s, hs⟩ := ih hX
        exact ⟨.right A B C X h l c, s, by simp [ParseCtx.plug, hs]⟩

/-- A repeated variable on a branch gives a nontrivial self-context. -/
theorem exists_repeat_of_not_nodup
    {g : ChomskyNormalGrammar T} {A : g.cfg.NT} {t : ParseTree g A}
    (b : Spine g t) (hdup : ¬ (vars b).Nodup) :
    ∃ (X : g.cfg.NT) (cin : ParseCtx g X X) (s : ParseTree g X)
        (cmid : ParseCtx g A X),
      cmid.plug (cin.plug s) = t ∧ cin.IsProper := by
  induction b with
  | stop A t => simp [vars] at hdup
  | downLeft A B C h l r b ih =>
      simp only [vars, List.nodup_cons] at hdup
      by_cases hmem : A ∈ vars b
      · obtain ⟨d, s, hs⟩ := exists_context_of_mem b hmem
        exact ⟨A, .left A B C A h d r, s, .hole A,
          by simp [ParseCtx.plug, hs], by simp [ParseCtx.IsProper]⟩
      · have htail : ¬ (vars b).Nodup := by tauto
        obtain ⟨X, cin, s, cmid, hs, hp⟩ := ih htail
        exact ⟨X, cin, s, .left A B C X h cmid r,
          by simp [ParseCtx.plug, hs], hp⟩
  | downRight A B C h l r b ih =>
      simp only [vars, List.nodup_cons] at hdup
      by_cases hmem : A ∈ vars b
      · obtain ⟨d, s, hs⟩ := exists_context_of_mem b hmem
        exact ⟨A, .right A B C A h l d, s, .hole A,
          by simp [ParseCtx.plug, hs], by simp [ParseCtx.IsProper]⟩
      · have htail : ¬ (vars b).Nodup := by tauto
        obtain ⟨X, cin, s, cmid, hs, hp⟩ := ih htail
        exact ⟨X, cin, s, .right A B C X h l cmid,
          by simp [ParseCtx.plug, hs], hp⟩

end Spine

/-- A sufficiently tall parse tree contains a repeated variable on a bounded
suffix of a root-to-leaf branch. -/
theorem ParseTree.exists_pump
    {g : ChomskyNormalGrammar T} {A : g.cfg.NT} (t : ParseTree g A)
    (hm : (ContextFreeGrammar.activeNonterminals g.cfg).card < t.height) :
    ∃ (X : g.cfg.NT) (cout : ParseCtx g A X)
        (cin : ParseCtx g X X) (s : ParseTree g X),
      cout.plug (cin.plug s) = t ∧ cin.IsProper ∧
      (cin.plug s).height ≤
        (ContextFreeGrammar.activeNonterminals g.cfg).card + 1 := by
  classical
  let m := (ContextFreeGrammar.activeNonterminals g.cfg).card
  have hk : 1 ≤ m + 1 := by omega
  have hkt : m + 1 ≤ t.height := by omega
  obtain ⟨X₀, c, t', ht', hh⟩ :=
    ParseTree.exists_subtree_height_eq t hk hkt
  let b := Spine.longest t'
  have hdup : ¬ (Spine.vars b).Nodup := by
    intro hn
    have hsubset :
        (Spine.vars b).toFinset ⊆ ContextFreeGrammar.activeNonterminals g.cfg := by
      intro X hX
      rw [List.mem_toFinset] at hX
      exact Spine.vars_mem_active b X hX
    have hcard := Finset.card_le_card hsubset
    rw [List.toFinset_card_of_nodup hn, Spine.vars_longest_length, hh] at hcard
    omega
  obtain ⟨X, cin, s, cmid, hmid, hproper⟩ :=
    Spine.exists_repeat_of_not_nodup b hdup
  refine ⟨X, c.compose cmid, cin, s, ?_, hproper, ?_⟩
  · rw [ParseCtx.plug_compose, hmid, ht']
  · calc
      (cin.plug s).height ≤ (cmid.plug (cin.plug s)).height :=
        ParseCtx.height_le_plug cmid _
      _ = t'.height := congrArg ParseTree.height hmid
      _ = m + 1 := hh

mutual
  /-- A generic derivation tree converted to either a CNF parse tree or the
  distinguished initial-symbol epsilon derivation. -/
  inductive CnfSymbolResult (g : ChomskyNormalGrammar T) :
      Symbol T g.cfg.NT → List T → Prop
    | terminal (a : T) : CnfSymbolResult g (.terminal a) [a]
    | tree {A : g.cfg.NT} (t : ParseTree g A) :
        CnfSymbolResult g (.nonterminal A) t.yield
    | empty (A : g.cfg.NT) (hA : A = g.cfg.initial) :
        CnfSymbolResult g (.nonterminal A) []

  inductive CnfFormResult (g : ChomskyNormalGrammar T) :
      List (Symbol T g.cfg.NT) → List T → Prop
    | nil : CnfFormResult g [] []
    | cons {x : Symbol T g.cfg.NT} {u : List T}
        {xs : List (Symbol T g.cfg.NT)} {v : List T}
        (head : CnfSymbolResult g x u) (tail : CnfFormResult g xs v) :
        CnfFormResult g (x :: xs) (u ++ v)
end

private theorem cnfNonterminalResult
    (g : ChomskyNormalGrammar T)
    (r : ContextFreeRule T g.cfg.NT) (hr : r ∈ g.cfg.rules)
    {w : List T} (hc : CnfFormResult g r.output w) :
    CnfSymbolResult g (.nonterminal r.input) w := by
  rcases g.chomskyNormal r hr with hε | ⟨a, hout⟩ | ⟨B, C, hout⟩
  · rcases hε with ⟨hin, hout⟩
    rw [hout] at hc
    cases hc
    exact .empty r.input hin
  · rw [hout] at hc
    cases hc with
    | cons hs ht =>
        cases hs with
        | terminal =>
            cases ht
            let t : ParseTree g r.input :=
              ParseTree.leaf r.input a (by
                have heq :
                    ({ input := r.input, output := [Symbol.terminal a] } :
                      ContextFreeRule T g.cfg.NT) = r := by
                  cases r
                  simp_all
                rw [heq]
                exact hr)
            have hyield : t.yield = [a] := rfl
            rw [← hyield]
            exact CnfSymbolResult.tree t
  · rw [hout] at hc
    cases hc with
    | cons hsB rest =>
        cases rest with
        | cons hsC tail =>
            cases tail
            cases hsB with
            | tree tB =>
                cases hsC with
                | tree tC =>
                    let t : ParseTree g r.input :=
                      ParseTree.node r.input B C (by
                        have heq :
                            ({ input := r.input, output :=
                              [Symbol.nonterminal B, Symbol.nonterminal C] } :
                              ContextFreeRule T g.cfg.NT) = r := by
                          cases r
                          simp_all
                        rw [heq]
                        exact hr) tB tC
                    have hyield :
                        t.yield = tB.yield ++ tC.yield := rfl
                    simp only [List.append_nil]
                    rw [← hyield]
                    exact CnfSymbolResult.tree t
                | empty _ hC =>
                    exfalso
                    apply g.initial_not_output r hr
                    simp [hout, hC]
            | empty _ hB =>
                exfalso
                apply g.initial_not_output r hr
                simp [hout, hB]

theorem cnfSymbolResult_of_derivationTree
    {g : ChomskyNormalGrammar T} {x : Symbol T g.cfg.NT} {w : List T}
    (h : ContextFreeGrammar.DerivationSymbolTree g.cfg x w) :
    CnfSymbolResult g x w := by
  exact ContextFreeGrammar.DerivationSymbolTree.rec
    (motive_1 := fun x w _ => CnfSymbolResult g x w)
    (motive_2 := fun xs w _ => CnfFormResult g xs w)
    (fun a => CnfSymbolResult.terminal a)
    (fun r hr _ children ih => cnfNonterminalResult g r hr ih)
    CnfFormResult.nil
    (fun head tail ihHead ihTail => CnfFormResult.cons ihHead ihTail)
    h

theorem cnfFormResult_of_derivationTree
    {g : ChomskyNormalGrammar T}
    {xs : List (Symbol T g.cfg.NT)} {w : List T}
    (h : ContextFreeGrammar.DerivationFormTree g.cfg xs w) :
    CnfFormResult g xs w := by
  exact ContextFreeGrammar.DerivationFormTree.rec
    (motive_1 := fun x w _ => CnfSymbolResult g x w)
    (motive_2 := fun xs w _ => CnfFormResult g xs w)
    (fun a => CnfSymbolResult.terminal a)
    (fun r hr _ children ih => cnfNonterminalResult g r hr ih)
    CnfFormResult.nil
    (fun head tail ihHead ihTail => CnfFormResult.cons ihHead ihTail)
    h

/-- A nonempty terminal derivation in CNF has a binary parse tree. -/
theorem ParseTree.exists_of_derives
    {g : ChomskyNormalGrammar T} {A : g.cfg.NT} {w : List T}
    (hw : w ≠ [])
    (h : g.cfg.Derives [Symbol.nonterminal A] (terminalSymbols w)) :
    ∃ t : ParseTree g A, t.yield = w := by
  have htree := ContextFreeGrammar.derivationFormTree_of_derives g.cfg h
  have hresult := cnfFormResult_of_derivationTree (g := g) htree
  cases hresult with
  | cons hs tail =>
      cases tail
      cases hs with
      | tree t => exact ⟨t, by simp⟩
      | empty _ _ => exact (hw rfl).elim

/-- Repeatedly plug a self-context around a parse tree. -/
def ParseCtx.nest {g : ChomskyNormalGrammar T} {X : g.cfg.NT}
    (c : ParseCtx g X X) (s : ParseTree g X) : Nat → ParseTree g X
  | 0 => s
  | i + 1 => c.plug (nest c s i)

private theorem append_flatten_replicate_comm (w : List T) (i : Nat) :
    w ++ (List.replicate i w).flatten =
      (List.replicate i w).flatten ++ w := by
  induction i with
  | zero => simp
  | succ i ih =>
      simp only [List.replicate_succ, List.flatten_cons]
      rw [List.append_assoc, ih, ← List.append_assoc]

private theorem flatten_replicate_succ_right (w : List T) (i : Nat) :
    (List.replicate (i + 1) w).flatten =
      (List.replicate i w).flatten ++ w := by
  simpa [List.replicate_succ] using append_flatten_replicate_comm w i

@[simp] theorem ParseCtx.yield_nest
    {g : ChomskyNormalGrammar T} {X : g.cfg.NT}
    (c : ParseCtx g X X) (s : ParseTree g X) (i : Nat) :
    (c.nest s i).yield =
      (List.replicate i c.preYield).flatten ++ s.yield ++
        (List.replicate i c.postYield).flatten := by
  induction i with
  | zero => simp [ParseCtx.nest]
  | succ i ih =>
      simp only [ParseCtx.nest, ParseCtx.yield_plug, ih]
      rw [flatten_replicate_succ_right]
      simp only [List.replicate_succ, List.flatten_cons]
      simp only [List.append_assoc]
      let p := (List.replicate i c.preYield).flatten
      let q := (List.replicate i c.postYield).flatten
      change c.preYield ++ (p ++ (s.yield ++ (q ++ c.postYield))) =
        p ++ (c.preYield ++ (s.yield ++ (c.postYield ++ q)))
      calc
        c.preYield ++ (p ++ (s.yield ++ (q ++ c.postYield))) =
            (c.preYield ++ p) ++ (s.yield ++ (q ++ c.postYield)) :=
          (List.append_assoc _ _ _).symm
        _ = (p ++ c.preYield) ++ (s.yield ++ (q ++ c.postYield)) := by
          rw [append_flatten_replicate_comm c.preYield i]
        _ = (p ++ c.preYield) ++ (s.yield ++ (c.postYield ++ q)) := by
          rw [← append_flatten_replicate_comm c.postYield i]
        _ = p ++ (c.preYield ++ (s.yield ++ (c.postYield ++ q))) := by
          simp [List.append_assoc]

/-- Every context-free language satisfies the pumping lemma. -/
theorem Language.IsContextFree.pumping_lemma
    {T : Type} {L : Language T} (h : L.IsContextFree) :
    ∃ p ≥ 1, ∀ w ∈ L, p ≤ w.length →
      ∃ u v x y z, w = u ++ v ++ x ++ y ++ z ∧
        (v ++ x ++ y).length ≤ p ∧ v ++ y ≠ [] ∧
        ∀ i : ℕ, u ++ (List.replicate i v).flatten ++ x ++
          (List.replicate i y).flatten ++ z ∈ L := by
  rcases h with ⟨g₀, rfl⟩
  let g := ContextFreeGrammar.Classical.toChomskyNormalGrammar g₀
  let m := (ContextFreeGrammar.activeNonterminals g.cfg).card
  have hp : 1 ≤ 2 ^ m := by simpa using Nat.one_le_pow' m 1
  refine ⟨2 ^ m, hp, ?_⟩
  intro w hw hlen
  have hwg : w ∈ g.language := by simpa [g] using hw
  have hwne : w ≠ [] := by
    intro heq
    subst w
    simp at hlen
  have hder :
      g.cfg.Derives [Symbol.nonterminal g.cfg.initial] (terminalSymbols w) :=
    (ContextFreeGrammar.mem_language_iff g.cfg w).mp hwg
  obtain ⟨t, htYield⟩ := ParseTree.exists_of_derives hwne hder
  have hpows : 2 ^ m ≤ 2 ^ (t.height - 1) := by
    calc
      2 ^ m ≤ w.length := hlen
      _ = t.yield.length := congrArg List.length htYield |>.symm
      _ ≤ 2 ^ (t.height - 1) := ParseTree.yield_length_le t
  have hmheight : m < t.height := by
    have hexp : m ≤ t.height - 1 :=
      (Nat.pow_le_pow_iff_right (by omega)).mp hpows
    exact lt_of_le_of_lt hexp
      (Nat.sub_lt (ParseTree.one_le_height t) (by omega))
  obtain ⟨X, cout, cin, s, htree, hproper, hheight⟩ :=
    ParseTree.exists_pump t hmheight
  let u := cout.preYield
  let v := cin.preYield
  let x := s.yield
  let y := cin.postYield
  let z := cout.postYield
  refine ⟨u, v, x, y, z, ?_, ?_, ?_, ?_⟩
  · calc
      w = t.yield := htYield.symm
      _ = (cout.plug (cin.plug s)).yield :=
        congrArg ParseTree.yield htree |>.symm
      _ = u ++ v ++ x ++ y ++ z := by
        simp [u, v, x, y, z, ParseCtx.yield_plug, List.append_assoc]
  · have hyield := ParseTree.yield_length_le (cin.plug s)
    have hexp : (cin.plug s).height - 1 ≤ m := by omega
    have hpow : 2 ^ ((cin.plug s).height - 1) ≤ 2 ^ m :=
      Nat.pow_le_pow_right (by omega) hexp
    calc
      (v ++ x ++ y).length = (cin.plug s).yield.length := by
        simp [v, x, y, ParseCtx.yield_plug]
      _ ≤ 2 ^ ((cin.plug s).height - 1) := hyield
      _ ≤ 2 ^ m := hpow
  · intro hempty
    have hpos := ParseCtx.proper_yield_pos cin hproper
    rw [show v ++ y = cin.preYield ++ cin.postYield by rfl, hempty] at hpos
    simp at hpos
  · intro i
    have hd := ParseTree.yield_derives (cout.plug (cin.nest s i))
    have hyield :
        (cout.plug (cin.nest s i)).yield =
          u ++ (List.replicate i v).flatten ++ x ++
            (List.replicate i y).flatten ++ z := by
      simp [u, v, x, y, z, ParseCtx.yield_plug, ParseCtx.yield_nest,
        List.append_assoc]
    have hmemg :
        u ++ (List.replicate i v).flatten ++ x ++
            (List.replicate i y).flatten ++ z ∈ g.language := by
      apply (ContextFreeGrammar.mem_language_iff g.cfg _).mpr
      simpa [hyield] using hd
    simpa [g] using hmemg
end Mathling.Grammar
