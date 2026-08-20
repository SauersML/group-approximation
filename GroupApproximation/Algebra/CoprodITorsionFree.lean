import GroupApproximation.Algebra.FreeProductOrder
import GroupApproximation.Algebra.GroupTorsionFree

/-!
# Torsion in an indexed free product

A free product of torsion-free groups is torsion-free.  Mathlib does not have
it, and `Monsters.ChiodoTorsionFreeAbsorber` avoided needing it by taking a
torsion-free *quotient* rather than a torsion-free free product.  It is needed
again for the Higman--Neumann--Neumann bridge `Higman.CountableToFG`: the
bridge embeds a countable group `A` into an HNN extension of `A ∗ F₂`, and the
torsion clause of the bridge asks that `A ∗ F₂` be torsion-free when `A` is.

The proof splits into two halves that are quite unequal.

**The power half, proved here.**  An element whose reduced word is a nonempty
alternating word with *distinct end indices* --- a `Monoid.CoprodI.NeWord M i j`
with `j ≠ i`, i.e. a cyclically reduced word --- has infinite order, because its
powers are again such words (`NeWord.append`) and a nonempty reduced word is
never trivial (`FreeProductOrder.neWord_prod_ne_one`, already proved in this
repository).

**The cyclic-reduction half, not proved here.**  That every non-identity
element is conjugate either into a factor or to such a word.  This is the
combinatorial content --- conjugate to minimal length, then observe the ends
cannot share an index --- and it is what `isPowerTorsionFree_of_cyclicReduction`
takes as its hypothesis.
-/

namespace GroupApproximation
namespace CoprodITorsionFree

open Monoid Monoid.CoprodI

variable {ι : Type*} [DecidableEq ι] {M : ι → Type*} [∀ i, Group (M i)]
  [∀ i, DecidableEq (M i)]

/-! ## 1.  Powers of a cyclically reduced word -/

/-- The `(n+1)`-st power of a cyclically reduced word, as a reduced word. -/
def neWordPow {i j : ι} (hij : j ≠ i) (w : NeWord M i j) : ℕ → NeWord M i j
  | 0 => w
  | n + 1 => (neWordPow hij w n).append hij w

theorem prod_neWordPow {i j : ι} (hij : j ≠ i) (w : NeWord M i j) (n : ℕ) :
    (neWordPow hij w n).prod = w.prod ^ (n + 1) := by
  induction n with
  | zero => simp [neWordPow]
  | succ n ih =>
      show (NeWord.append (neWordPow hij w n) hij w).prod = _
      rw [NeWord.append_prod, ih, ← pow_succ]

/-- **A cyclically reduced word has infinite order.** -/
theorem prod_pow_ne_one {i j : ι} (hij : j ≠ i) (w : NeWord M i j) (n : ℕ) :
    w.prod ^ (n + 1) ≠ 1 := by
  rw [← prod_neWordPow hij w n]
  exact FreeProductOrder.neWord_prod_ne_one _

/-! ## 2.  Torsion-freeness, given cyclic reduction -/

/-- **A free product of torsion-free groups is torsion-free**, given that every
non-identity element is conjugate into a factor or to a cyclically reduced
word.

The two cases are the two ways an element can fail to have infinite order, and
neither can happen: a conjugate into a factor is torsion-free there, and a
cyclically reduced word has infinite order by `prod_pow_ne_one`. -/
theorem isPowerTorsionFree_of_cyclicReduction
    (hfac : ∀ i, IsPowerTorsionFree (M i))
    (hcyc : ∀ x : CoprodI M, x ≠ 1 →
      (∃ (g : CoprodI M) (i : ι) (m : M i), g * x * g⁻¹ = CoprodI.of m) ∨
      (∃ (g : CoprodI M) (i j : ι) (_ : j ≠ i) (w : NeWord M i j),
        g * x * g⁻¹ = w.prod)) :
    IsPowerTorsionFree (CoprodI M) := by
  intro x n hn hxn
  by_contra hx
  have hconj : ∀ g : CoprodI M, (g * x * g⁻¹) ^ n = 1 := by
    intro g
    rw [conj_pow, hxn, mul_one, mul_inv_cancel]
  rcases hcyc x hx with ⟨g, i, m, hg⟩ | ⟨g, i, j, hij, w, hg⟩
  · have hpow : (CoprodI.of m : CoprodI M) ^ n = 1 := by rw [← hg]; exact hconj g
    have hm : m ^ n = 1 := by
      apply CoprodI.of_injective i
      rw [map_pow, map_one]
      exact hpow
    have hm1 : m = 1 := hfac i m n hn hm
    have : g * x * g⁻¹ = 1 := by rw [hg, hm1, map_one]
    exact hx (by
      have := congrArg (fun y ↦ g⁻¹ * y * g) this
      simpa [mul_assoc] using this)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff.mp hn).ne'
    exact prod_pow_ne_one hij w k (by rw [← hg]; exact hconj g)

end CoprodITorsionFree
end GroupApproximation
