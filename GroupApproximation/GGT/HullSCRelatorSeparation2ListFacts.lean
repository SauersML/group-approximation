import GroupApproximation.GGT.HullSCRelatorSeparation2Quotient

/-!
# The list facts step (b) runs on, and the run without repetition

`GGT/HullSCRelatorSeparationRotation.lean` proves step (b) over one subgroup and
keeps its list lemmas `private`, so they cannot be reused here.  They are
restated -- with distinct names, so nothing can clash -- and they are exactly
the ones that went green there, which is why they are copied rather than
reworked.

`nodup_blockWord` is the new content: the alternating run has no repeated
letter.  It does not use the alternation at all.  Two block letters are equal
only if their indices agree and then their exponents do, so distinctness of the
exponents alone suffices, and `HullSC.exists_separated_exponents_family` supplies
that.  The alternation is what makes each letter its own *component*
(`HullSC.isComp_relatorWord₂`); repetition-freeness is a separate matter and
comes from the design.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry

universe u v

/-! ## Reading lists at an index -/

/-- In a list without repetition an entry determines its position. -/
theorem getElem?_eq_of_nodup {α : Type v} :
    ∀ {l : List α}, l.Nodup → ∀ {i j : ℕ} {x : α},
      l[i]? = some x → l[j]? = some x → i = j := by
  intro l
  induction l with
  | nil =>
      intro _ _ _ _ hi _
      simp at hi
  | cons b t ih =>
      intro hnd i j x hi hj
      rw [List.nodup_cons] at hnd
      cases i with
      | zero =>
          cases j with
          | zero => rfl
          | succ j' =>
              rw [List.getElem?_cons_zero] at hi
              rw [List.getElem?_cons_succ] at hj
              refine absurd ?_ hnd.1
              rw [Option.some.inj hi]
              exact List.mem_of_getElem? hj
      | succ i' =>
          cases j with
          | zero =>
              rw [List.getElem?_cons_zero] at hj
              rw [List.getElem?_cons_succ] at hi
              refine absurd ?_ hnd.1
              rw [Option.some.inj hj]
              exact List.mem_of_getElem? hi
          | succ j' =>
              rw [List.getElem?_cons_succ] at hi
              rw [List.getElem?_cons_succ] at hj
              have hij := ih hnd.2 hi hj
              omega

/-- An entry of a concatenation that misses the first part and does not repeat
in the second determines its position. -/
theorem getElem?_append_index_eq {α : Type v} {l₁ l₂ : List α} {x : α}
    (hnd : l₂.Nodup) (hx : x ∉ l₁) {q q' : ℕ}
    (h : (l₁ ++ l₂)[q]? = some x) (h' : (l₁ ++ l₂)[q']? = some x) : q = q' := by
  have key : ∀ r : ℕ, (l₁ ++ l₂)[r]? = some x →
      l₁.length ≤ r ∧ l₂[r - l₁.length]? = some x := by
    intro r hr
    rcases Nat.lt_or_ge r l₁.length with hlt | hge
    · rw [List.getElem?_append_left hlt] at hr
      exact absurd (List.mem_of_getElem? hr) hx
    · exact ⟨hge, by rwa [List.getElem?_append_right hge] at hr⟩
  obtain ⟨hq, hq2⟩ := key q h
  obtain ⟨hq', hq'2⟩ := key q' h'
  have hsub := getElem?_eq_of_nodup hnd hq2 hq'2
  omega

/-- The first letter of a rotation. -/
theorem getElem?_rotate_head {α : Type v} {l : List α} (hl : 0 < l.length)
    (e : ℕ) : (l.rotate e)[0]? = l[e % l.length]? := by
  rw [List.getElem?_rotate hl, Nat.zero_add]

/-- Reading a rotation at an offset is reading a further rotation at its
start. -/
theorem getElem?_rotate_at {α : Type v} {l : List α} {c d : ℕ}
    (hd : d < l.length) : (l.rotate c)[d]? = (l.rotate (c + d))[0]? := by
  rw [List.getElem?_rotate hd,
    getElem?_rotate_head (Nat.lt_of_le_of_lt (Nat.zero_le d) hd),
    Nat.add_comm c d]

/-- A common further rotation can be cancelled. -/
theorem rotate_cancel_right {α : Type v} {l : List α} {c c' d : ℕ}
    (h : l.rotate (c + d) = l.rotate (c' + d)) : l.rotate c = l.rotate c' := by
  rw [← List.rotate_rotate, ← List.rotate_rotate] at h
  exact List.rotate_injective d h

/-! ## The run has no repeated letter -/

section Nodup

variable {G : Type u} [Group G]

/-- **The alternating run has no repeated letter.**

Only the distinctness of the exponents is used: two block letters are equal
only if their indices agree, and then their exponents do by injectivity of the
powers.  The alternation plays no part here -- it is what makes each letter its
own component, which is a different statement. -/
theorem nodup_blockWord {h₀ h₁ : G}
    (hinj : ∀ b : Bool,
      Function.Injective (fun n : ℕ => (if b then h₁ else h₀) ^ n)) :
    ∀ (s : Bool) (ms : List ℕ), ms.Nodup → (blockWord h₀ h₁ s ms).Nodup := by
  intro s ms
  induction ms generalizing s with
  | nil =>
      intro _
      rw [blockWord_nil]
      exact List.nodup_nil
  | cons m t ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      rw [blockWord_cons, List.nodup_cons]
      refine ⟨?_, ih (!s) hnd.2⟩
      intro hmem
      obtain ⟨b, m', hm', heq⟩ := mem_blockWord h₀ h₁ (!s) t _ hmem
      rw [GGT.RelLetter.comp.injEq] at heq
      obtain ⟨hb, hpow⟩ := heq
      rw [← hb] at hpow
      refine hnd.1 ?_
      rw [hinj s hpow]
      exact hm'

end Nodup

end HullSC
end GroupApproximation
