import Mathlib.Data.List.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Arc-end descent: the two local patterns of a list not met through one end

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-22.

The list lemmas behind `Piece10Live/ExtremalArcEndDescent`, for a Boolean predicate `p` on a
list `l` (in the application `p = keptPred K r` and `l` one of the two arcs):

* `ExtremalArcEndDescentEnd p l`: `l = pre ++ post` with `p` constant on `pre` and constant with
  the other value on `post` (the shape of `ExtremalJordanArcEnd`);
* `ExtremalArcEndDescentKRKList p l`: a factor `d :: (B ++ [e])` of `l` with `p d = p e = true`,
  `B` nonempty and `p = false` on `B` (kept / removed / kept);
* `ExtremalArcEndDescentRKRList p l`: the same with the values exchanged (removed / kept /
  removed).

Proved: the trichotomy `extremalArcEndDescent_trichotomy` (every list is met through one end or
contains one of the two patterns), and conversely each pattern refutes the arc-end shape
(`extremalArcEndDescent_not_end_of_krk`, `extremalArcEndDescent_not_end_of_rkr`).

## Proof route

Trichotomy: induction on `l`, adding the head `a` in front of the three cases for the tail.
Only the arc-end case needs work: if `a` has the value of `pre` it joins `pre`; otherwise it is a
new first block, which is fine when `pre` or `post` is empty and gives a pattern `a, pre, head of
post` when both are nonempty.

Converse: `extremalArcEndDescent_false_of_order`: a list `pre ++ post` with `p = c` on `pre` and
`p = !c` on `post` has no `x` with `p x = !c` before a `y` with `p y = c`
(`List.append_eq_append_iff`).  In each pattern a removed dart of the middle run lies between
the two outer darts, which gives such an order for either orientation of `pre` and `post`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

section Lists

variable {α : Type _}

/-- **Met through one end** (list form of `ExtremalJordanArcEnd`). -/
def ExtremalArcEndDescentEnd (p : α → Bool) (l : List α) : Prop :=
  ∃ pre post : List α, l = pre ++ post ∧
    (((∀ x ∈ pre, p x = true) ∧ ∀ x ∈ post, p x = false) ∨
      ((∀ x ∈ pre, p x = false) ∧ ∀ x ∈ post, p x = true))

/-- **Kept / removed / kept**: a nonempty `false` run between two `true` members. -/
def ExtremalArcEndDescentKRKList (p : α → Bool) (l : List α) : Prop :=
  ∃ (P : List α) (d : α) (B : List α) (e : α) (Q : List α),
    l = P ++ d :: (B ++ e :: Q) ∧ p d = true ∧ p e = true ∧ B ≠ [] ∧ ∀ x ∈ B, p x = false

/-- **Removed / kept / removed**: a nonempty `true` run between two `false` members. -/
def ExtremalArcEndDescentRKRList (p : α → Bool) (l : List α) : Prop :=
  ∃ (P : List α) (d : α) (B : List α) (e : α) (Q : List α),
    l = P ++ d :: (B ++ e :: Q) ∧ p d = false ∧ p e = false ∧ B ≠ [] ∧ ∀ x ∈ B, p x = true

/-- **A constant value on a cons.** -/
theorem extremalArcEndDescent_forall_cons {p : α → Bool} {c : Bool} {a : α} {l : List α}
    (ha : p a = c) (hl : ∀ x ∈ l, p x = c) : ∀ x ∈ a :: l, p x = c := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx'
  · exact ha
  · exact hl x hx'

/-- **Trichotomy**: a list is met through one end, or contains kept / removed / kept, or
contains removed / kept / removed. -/
theorem extremalArcEndDescent_trichotomy (p : α → Bool) (l : List α) :
    ExtremalArcEndDescentEnd p l ∨ ExtremalArcEndDescentKRKList p l ∨
      ExtremalArcEndDescentRKRList p l := by
  induction l with
  | nil =>
    exact Or.inl ⟨[], [], rfl, Or.inl ⟨fun _ h => absurd h List.not_mem_nil,
      fun _ h => absurd h List.not_mem_nil⟩⟩
  | cons a t ih =>
    rcases ih with ⟨pre, post, ht, hcase⟩ | ⟨P, d, B, e, Q, ht, hd, he, hB, hBx⟩ |
        ⟨P, d, B, e, Q, ht, hd, he, hB, hBx⟩
    · subst ht
      rcases hcase with ⟨hpre, hpost⟩ | ⟨hpre, hpost⟩
      · -- `pre` kept, `post` removed.
        cases ha : p a
        · cases pre with
          | nil =>
            exact Or.inl ⟨[], a :: post, rfl, Or.inl ⟨fun _ h => absurd h List.not_mem_nil,
              extremalArcEndDescent_forall_cons ha hpost⟩⟩
          | cons g pre₀ =>
            cases post with
            | nil =>
              exact Or.inl ⟨[a], g :: pre₀, by simp, Or.inr
                ⟨extremalArcEndDescent_forall_cons ha (fun _ h => absurd h List.not_mem_nil),
                  hpre⟩⟩
            | cons f post₀ =>
              exact Or.inr (Or.inr ⟨[], a, g :: pre₀, f, post₀, rfl, ha,
                hpost f List.mem_cons_self, List.cons_ne_nil g pre₀, hpre⟩)
        · exact Or.inl ⟨a :: pre, post, rfl,
            Or.inl ⟨extremalArcEndDescent_forall_cons ha hpre, hpost⟩⟩
      · -- `pre` removed, `post` kept.
        cases ha : p a
        · exact Or.inl ⟨a :: pre, post, rfl,
            Or.inr ⟨extremalArcEndDescent_forall_cons ha hpre, hpost⟩⟩
        · cases pre with
          | nil =>
            exact Or.inl ⟨[], a :: post, rfl, Or.inr ⟨fun _ h => absurd h List.not_mem_nil,
              extremalArcEndDescent_forall_cons ha hpost⟩⟩
          | cons g pre₀ =>
            cases post with
            | nil =>
              exact Or.inl ⟨[a], g :: pre₀, by simp, Or.inl
                ⟨extremalArcEndDescent_forall_cons ha (fun _ h => absurd h List.not_mem_nil),
                  hpre⟩⟩
            | cons f post₀ =>
              exact Or.inr (Or.inl ⟨[], a, g :: pre₀, f, post₀, rfl, ha,
                hpost f List.mem_cons_self, List.cons_ne_nil g pre₀, hpre⟩)
    · exact Or.inr (Or.inl ⟨a :: P, d, B, e, Q, by subst ht; rfl, hd, he, hB, hBx⟩)
    · exact Or.inr (Or.inr ⟨a :: P, d, B, e, Q, by subst ht; rfl, hd, he, hB, hBx⟩)

/-- **No `!c` member before a `c` member** in a list `pre ++ post` with `p = c` on `pre` and
`p = !c` on `post`. -/
theorem extremalArcEndDescent_false_of_order (p : α → Bool) (c : Bool)
    {pre post U V Z : List α} {x y : α} (h : pre ++ post = U ++ x :: (V ++ y :: Z))
    (hpre : ∀ z ∈ pre, p z = c) (hpost : ∀ z ∈ post, p z = !c) (hx : p x = !c)
    (hy : p y = c) : False := by
  have key : ∀ z, p z = c → p z = !c → False := by
    intro z h₁ h₂
    have h₃ : c = !c := h₁.symm.trans h₂
    cases c <;> exact absurd h₃ (by decide)
  rcases List.append_eq_append_iff.mp h with ⟨s₁, _, hpost'⟩ | ⟨bs, hpre', htail⟩
  · exact key y hy (hpost y (by rw [hpost']; simp))
  · cases bs with
    | nil =>
      have hp : post = x :: (V ++ y :: Z) := htail.symm
      exact key y hy (hpost y (by rw [hp]; simp))
    | cons g bs₀ =>
      have htail' : x :: (V ++ y :: Z) = g :: (bs₀ ++ post) := htail
      have hxg : x = g := (List.cons.inj htail').1
      exact key x (hpre x (by rw [hpre', hxg]; simp)) hx
