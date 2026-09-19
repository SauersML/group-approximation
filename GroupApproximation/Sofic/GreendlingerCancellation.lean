import GroupApproximation.Sofic.GreendlingerExpression

/-!
# The cancellation decomposition of a product of two reduced words

The layer still open in `GreendlingerGate` is the descent from a minimal
conjugate-product expression with `n ≥ 2` factors to the single-conjugate case.
Every treatment of that descent has to control what happens when two reduced
words are multiplied, and the statement it needs is that the cancellation is a
single matched block:

for reduced `A` and `B` there are `A'`, `M`, `B'` with

`A = A' ++ M`,  `B = invRev M ++ B'`,  `A' ++ B'` reduced,
`mk A * mk B = mk (A' ++ B')`.

`M` is the part of `A` that the product destroys; `invRev M` is the matching
part of `B`.  Mathlib has no such decomposition, so this file proves it.

## The induction

On `B`, peeling one letter at a time, with the conjugator `A` universally
quantified in the motive.  With `B = b :: B₁` and `A` nonempty, write
`A = A₀ ++ [a]`; there are exactly two cases:

* `b` does not cancel `a`.  Then `A ++ B` is already reduced --- the two halves
  are reduced and the junction condition is exactly `b ≠ invLetter a` --- so the
  decomposition is trivial, with `M = []`.
* `b = invLetter a`.  Then the two letters annihilate, `mk A * mk B` collapses
  to `mk A₀ * mk B₁`, and the induction hypothesis applied to the *shorter* pair
  `(A₀, B₁)` returns a decomposition which is extended by putting `a` back at
  the end of the destroyed block: `M = M'' ++ [a]`, and
  `invRev (M'' ++ [a]) = [invLetter a] ++ invRev M''` puts `b` back at the front
  of `B`.

Both degenerate cases -- `B` empty and `A` empty -- are decompositions with
`M = []`.

Unconditional, and independent of small cancellation: this is a fact about free
groups, and the `C'(1/6)` hypothesis appears nowhere in it.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-- **The cancellation decomposition.**  Multiplying two reduced words destroys
a single matched block: a suffix `M` of the first against the matching prefix
`invRev M` of the second, with what remains already reduced. -/
theorem exists_cancellation_decomposition :
    ∀ (B : List (α × Bool)), FreeGroup.IsReduced B →
      ∀ (A : List (α × Bool)), FreeGroup.IsReduced A →
        ∃ A' M B' : List (α × Bool),
          A = A' ++ M ∧ B = FreeGroup.invRev M ++ B' ∧
            FreeGroup.IsReduced (A' ++ B') ∧
            FreeGroup.mk A * FreeGroup.mk B = FreeGroup.mk (A' ++ B') := by
  intro B
  induction B with
  | nil =>
      intro _ A hA
      refine ⟨A, [], [], by simp, by simp, by simpa using hA, ?_⟩
      rw [← FreeGroup.one_eq_mk, mul_one, List.append_nil]
  | cons b B₁ ih =>
      intro hB A hA
      have hB₁ : FreeGroup.IsReduced B₁ := List.IsChain.tail hB
      rcases eq_or_ne A [] with rfl | hAne
      · refine ⟨[], [], b :: B₁, by simp, by simp, by simpa using hB, ?_⟩
        rw [← FreeGroup.one_eq_mk, one_mul, List.nil_append]
      · obtain ⟨A₀, a, rfl⟩ : ∃ A₀ a, A = A₀ ++ [a] :=
          ⟨A.dropLast, A.getLast hAne, (List.dropLast_append_getLast hAne).symm⟩
        have hA₀ : FreeGroup.IsReduced A₀ :=
          isReduced_of_infix ⟨[], [a], by simp⟩ hA
        by_cases hcancel : b = invLetter a
        · -- the junction letters annihilate; recurse on the shorter pair
          obtain ⟨A'', M'', B'', h1, h2, h3, h4⟩ := ih hB₁ A₀ hA₀
          refine ⟨A'', M'' ++ [a], B'', ?_, ?_, h3, ?_⟩
          · rw [h1, List.append_assoc]
          · rw [FreeGroup.invRev_append, invRev_singleton, List.append_assoc,
              ← h2, hcancel]
          · calc FreeGroup.mk (A₀ ++ [a]) * FreeGroup.mk (b :: B₁)
                = (FreeGroup.mk A₀ * FreeGroup.mk [a])
                    * ((FreeGroup.mk [a])⁻¹ * FreeGroup.mk B₁) := by
                  rw [mk_append_singleton, hcancel, mk_cons, ← mk_singleton_inv]
              _ = FreeGroup.mk A₀ * FreeGroup.mk B₁ := by group
              _ = FreeGroup.mk (A'' ++ B'') := h4
        · -- nothing cancels, so the concatenation is already reduced
          refine ⟨A₀ ++ [a], [], b :: B₁, by simp, by simp, ?_, ?_⟩
          · refine List.isChain_append.mpr ⟨hA, hB, ?_⟩
            intro p hp q hq
            have hlast : (A₀ ++ [a]).getLast? = some a := List.getLast?_concat
            rw [hlast] at hp
            have hpa : p = a := by simpa using hp
            have hqb : q = b := by simpa using hq
            subst hpa
            subst hqb
            exact isReduced_step_iff.mpr hcancel
          · exact FreeGroup.mul_mk

/-- The destroyed block is a suffix of the first word and its formal inverse is
a prefix of the second, which is the form the descent uses. -/
theorem cancellation_suffix_prefix {A B : List (α × Bool)}
    (hA : FreeGroup.IsReduced A) (hB : FreeGroup.IsReduced B) :
    ∃ A' M B' : List (α × Bool),
      M <:+ A ∧ FreeGroup.invRev M <+: B ∧
        FreeGroup.IsReduced (A' ++ B') ∧
        FreeGroup.mk A * FreeGroup.mk B = FreeGroup.mk (A' ++ B') := by
  obtain ⟨A', M, B', h1, h2, h3, h4⟩ :=
    exists_cancellation_decomposition B hB A hA
  exact ⟨A', M, B', ⟨A', h1.symm⟩, ⟨B', h2.symm⟩, h3, h4⟩

end SmallCancellationRouter
end GroupApproximation
