import GroupApproximation.Higman.GeneratedBasic
import GroupApproximation.Higman.ShiftOperation

/-!
# The adjacent-block transition device

Higman's Section 2 uses one construction four separate times — in Lemma 2.1, in
the primitive-recursion Lemma 2.4, in Lemma 2.5, and in the final assembly of
Theorem 3.  Given a set `A` of `2k`-tuples, read as a *transition relation*
between two adjacent `k`-blocks, the set

    ω₂ₖ A  ∩  σᵏ (ω₂ₖ A)

is exactly the set of sequences all of whose adjacent `k`-blocks are
`A`-related.  This module isolates that construction once.

## Why the intersection is the right object

`ω₂ₖ A` constrains the `2k`-windows of `f` that start at a multiple of `2k`,
i.e. at `k·r` for **even** `r`.  Shifting the whole set by `k` moves the
constraint onto the windows starting at `2k·i + k`, i.e. at `k·r` for **odd**
`r`.  Intersecting therefore constrains the `2k`-window at `k·r` for *every*
integer `r`, and consecutive `k`-blocks are exactly the two halves of such a
window.

This is the step that crosses from a bounded-arity relation to a condition
imposed at infinitely many positions, which is what makes an unbounded-support
recursively enumerable set reachable at all.

## Contents

* `windowAt m s f` — the `m`-window of `f` starting at an arbitrary index `s`,
  generalizing `blockAt` (which is the case `s = m * i`).
* `mem_transitionSet_iff` — the description above, as an iff.
* `higmanGenerated_transitionSet` — and the resulting generation statement,
  which is what Section 2 actually consumes.

Every operation used here is applied at a positive index (`ω₂ₖ` with `k ≥ 1`),
matching Higman's "for all positive integers `m`".
-/

namespace GroupApproximation
namespace Higman
namespace Seq

/-! ## Windows at an arbitrary offset -/

/-- The `m`-window of `f` starting at index `s`, read as a sequence supported on
`[0, m)`.  `blockAt` is the special case `s = m * i`. -/
noncomputable def windowAt (m : ℕ) (s : ℤ) (f : E) : E :=
  Finsupp.onFinset (Finset.Ico (0 : ℤ) (m : ℤ))
    (fun j => if j ∈ Finset.Ico (0 : ℤ) (m : ℤ) then f (s + j) else 0)
    (by
      intro j hj
      by_contra hcon
      rw [if_neg hcon] at hj
      exact hj rfl)

@[simp] theorem windowAt_apply (m : ℕ) (s : ℤ) (f : E) (j : ℤ) :
    windowAt m s f j =
      if j ∈ Finset.Ico (0 : ℤ) (m : ℤ) then f (s + j) else 0 := rfl

/-- `blockAt` is the window at a multiple of the block length. -/
theorem blockAt_eq_windowAt (m : ℕ) (i : ℤ) (f : E) :
    blockAt m i f = windowAt m (m * i) f := rfl

/-! ## Iterated shift -/

theorem shiftSeq_iterate_apply (k : ℕ) (f : E) (i : ℤ) :
    shiftSeq^[k] f i = f (i - k) := by
  induction k generalizing i with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', shiftSeq_apply, ih]
      congr 1
      push_cast
      ring

/-- The `k`-fold shift is surjective: every sequence is the shift of the
sequence read `k` steps later. -/
theorem exists_shiftSeq_iterate (k : ℕ) (f : E) :
    ∃ g : E, shiftSeq^[k] g = f := by
  refine ⟨(Finsupp.equivMapDomain (Equiv.addRight (-(k : ℤ))) f), ?_⟩
  ext i
  rw [shiftSeq_iterate_apply]
  rw [Finsupp.equivMapDomain_apply]
  congr 1
  simp [Equiv.addRight]

theorem mem_sigmaOp_iterate_iff (k : ℕ) (B : Set E) (f : E) :
    f ∈ sigmaOp^[k] B ↔ ∃ g ∈ B, ∀ i : ℤ, f i = g (i - k) := by
  induction k generalizing f with
  | zero =>
      simp only [Function.iterate_zero, id_eq, Nat.cast_zero, sub_zero]
      exact ⟨fun h => ⟨f, h, fun _ => rfl⟩, fun ⟨g, hg, h⟩ => by
        have : f = g := by ext i; exact h i
        rwa [this]⟩
  | succ n ih =>
      constructor
      · intro hf
        rw [Function.iterate_succ_apply'] at hf
        obtain ⟨h, hh, rfl⟩ := hf
        obtain ⟨g, hg, hgh⟩ := (ih h).mp hh
        refine ⟨g, hg, fun i => ?_⟩
        rw [shiftSeq_apply, hgh]
        congr 1
        push_cast
        ring
      · rintro ⟨g, hg, hfg⟩
        rw [Function.iterate_succ_apply']
        refine ⟨shiftSeq^[n] g, ?_, ?_⟩
        · exact (ih _).mpr ⟨g, hg, fun i => shiftSeq_iterate_apply n g i⟩
        · ext i
          rw [shiftSeq_apply, shiftSeq_iterate_apply, hfg]
          congr 1
          push_cast
          ring

/-! ## The device -/

/-- The sequences all of whose `2k`-windows at offsets divisible by `k` lie in
`A`. -/
def transitionSet (k : ℕ) (A : Set E) : Set E :=
  {f | ∀ r : ℤ, windowAt (2 * k) (k * r) f ∈ A}

/-- **The transition device.**  `ω₂ₖ A ∩ σᵏ (ω₂ₖ A)` constrains the `2k`-window
at every offset divisible by `k`: the unshifted copy handles the even multiples
and the shifted copy the odd ones. -/
theorem mem_transitionSet_iff (k : ℕ) (A : Set E) (f : E) :
    f ∈ omegaOp (2 * k) A ∩ sigmaOp^[k] (omegaOp (2 * k) A) ↔
      f ∈ transitionSet k A := by
  constructor
  · rintro ⟨heven, hodd⟩ r
    obtain ⟨g, hg, hfg⟩ := (mem_sigmaOp_iterate_iff k _ f).mp hodd
    rcases Int.even_or_odd r with ⟨i, hi⟩ | ⟨i, hi⟩
    · have := heven i
      rw [blockAt_eq_windowAt] at this
      have hoff : (k : ℤ) * r = ((2 * k : ℕ) : ℤ) * i := by
        push_cast
        rw [hi]
        ring
      rwa [hoff]
    · have := hg i
      rw [blockAt_eq_windowAt] at this
      have hshift : windowAt (2 * k) (k * r) f
          = windowAt (2 * k) (((2 * k : ℕ) : ℤ) * i) g := by
        ext j
        by_cases hj : j ∈ Finset.Ico (0 : ℤ) ((2 * k : ℕ) : ℤ)
        · rw [windowAt_apply, windowAt_apply, if_pos hj, if_pos hj, hfg]
          congr 1
          push_cast
          rw [hi]
          ring
        · rw [windowAt_apply, windowAt_apply, if_neg hj, if_neg hj]
      rwa [hshift]
  · intro hf
    constructor
    · intro i
      rw [blockAt_eq_windowAt]
      have hoff : ((2 * k : ℕ) : ℤ) * i = (k : ℤ) * (2 * i) := by
        push_cast; ring
      rw [hoff]
      exact hf (2 * i)
    · obtain ⟨g, hgf⟩ := exists_shiftSeq_iterate k f
      refine (mem_sigmaOp_iterate_iff k _ f).mpr ⟨g, ?_, ?_⟩
      · intro i
        rw [blockAt_eq_windowAt]
        have hval : windowAt (2 * k) (((2 * k : ℕ) : ℤ) * i) g
            = windowAt (2 * k) ((k : ℤ) * (2 * i + 1)) f := by
          ext j
          by_cases hj : j ∈ Finset.Ico (0 : ℤ) ((2 * k : ℕ) : ℤ)
          · rw [windowAt_apply, windowAt_apply, if_pos hj, if_pos hj,
              ← hgf, shiftSeq_iterate_apply]
            congr 1
            push_cast
            ring
          · rw [windowAt_apply, windowAt_apply, if_neg hj, if_neg hj]
        rw [hval]
        exact hf (2 * i + 1)
      · intro i
        rw [← hgf, shiftSeq_iterate_apply]

/-- **The device, as a generation statement.**  This is the form Section 2
consumes: a generated set of `2k`-tuples yields the generated set of sequences
whose adjacent `k`-blocks are all related by it. -/
theorem higmanGenerated_transitionSet (k : ℕ) (hk : 0 < k) {A : Set E}
    (hA : HigmanGenerated A) : HigmanGenerated (transitionSet k A) := by
  have hk2 : 0 < 2 * k := by omega
  have hiter : ∀ (n : ℕ) {B : Set E}, HigmanGenerated B →
      HigmanGenerated (sigmaOp^[n] B) := by
    intro n
    induction n with
    | zero => intro B hB; simpa using hB
    | succ m ih =>
        intro B hB
        rw [Function.iterate_succ_apply']
        exact HigmanGenerated.sigma (ih hB)
  have hset : transitionSet k A
      = omegaOp (2 * k) A ∩ sigmaOp^[k] (omegaOp (2 * k) A) := by
    ext f
    exact (mem_transitionSet_iff k A f).symm
  rw [hset]
  exact HigmanGenerated.inter (HigmanGenerated.omega (2 * k) hk2 hA)
    (hiter k (HigmanGenerated.omega (2 * k) hk2 hA))

end Seq
end Higman
end GroupApproximation
