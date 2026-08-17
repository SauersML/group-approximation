import GroupApproximation.Algebra.AlternatingDoubledTransport
import Mathlib.Algebra.GCDMonoid.Multiset

/-!
# Involutions are reachable, block by block

The consumption half of the premise `hBNG` of proof-ledger row `SO.17` factors
an even permutation into two involutions
(`Algebra/PermutationTwoInvolutions.lean`) and then splits each involution into
blocks small enough for the production half
(`Algebra/AlternatingDoubledTransport.lean`) to reach in two conjugates.  This
file supplies the step in the middle: **an involution whose transposition count
is even is reachable**, with an explicit arithmetic condition relating its
support to the support of `s`.

## What is proved

* `exists_cycleType_replicate_two` — for every `k` with `2k ≤ |Ω|` there is a
  permutation of cycle type `2^k`, built one transposition at a time on the
  complement of what is already used.  This is the *witness* the production
  theorem asks for; it is constructed rather than extracted, so nothing has to
  be halved.
* `cycleType_involution` — an involution's cycle type is `2^p`: every entry is
  at least `2` and divides the order, which divides `2`.
* `isBoundedConjProduct_two_of_involution` — hence an involution with `2k`
  transpositions is a product of at most **two** conjugates of `s` and `s⁻¹`
  as soon as `6k ≤ |supp s|`.

The constant is what the blocking step will consume: a block of `2k`
transpositions occupies `4k` points, and the condition `6k ≤ |supp s|` says a
block may be as large as two thirds of the support of `s`.

## What still remains for `SO.17`

Two steps, both combinatorial: cutting an involution's cycle factors into
blocks of a prescribed even size (`Equiv.Perm.cycleFactorsFinset` with
`Finset.noncommProd`, whose cycle type adds by
`Equiv.Perm.Disjoint.cycleType_noncommProd`), and the arithmetic that turns
`|supp s| ≥ δ|Ω|` into a block count depending on `δ` alone.  The parity repair
is already available: the two involutions of an even permutation have equal
sign (`PermutationTwoInvolutions.sign_eq_of_sign_mul_eq_one`), so their
transposition counts are congruent mod `2`, and the one leftover pair is
absorbed by `(x y)(u v) · (u v)(y z)`, which is two elements of type `2²`.
-/

namespace GroupApproximation
namespace InvolutionBlocks

open AlternatingBoundedNormalGeneration SoficEnvelopeSimplicity

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-! ## The witness of a doubled type -/

/-- **An involution with `k` disjoint transpositions exists whenever there is
room for one.**  Built by induction: `k` transpositions occupy `2k` points, so
below the bound there are always two more points free for the next one. -/
theorem exists_cycleType_replicate_two (k : ℕ) (hk : 2 * k ≤ Fintype.card Y) :
    ∃ g : Equiv.Perm Y, g.cycleType = Multiset.replicate k 2 := by
  induction k with
  | zero => exact ⟨1, by simp⟩
  | succ k ih =>
      obtain ⟨g, hg⟩ := ih (by omega)
      have hsupp : g.support.card = 2 * k := by
        have hsum := Equiv.Perm.sum_cycleType g
        rw [hg, Multiset.sum_replicate, smul_eq_mul] at hsum
        omega
      have hcompl : (g.supportᶜ : Finset Y).card
          = Fintype.card Y - g.support.card := Finset.card_compl _
      have hlt : 1 < (g.supportᶜ : Finset Y).card := by omega
      obtain ⟨x, y, hx, hy, hxy⟩ := Finset.one_lt_card_iff.mp hlt
      have hxs : x ∉ g.support := Finset.mem_compl.mp hx
      have hys : y ∉ g.support := Finset.mem_compl.mp hy
      have hdisj : Equiv.Perm.Disjoint g (Equiv.swap x y) := by
        rw [Equiv.Perm.disjoint_iff_disjoint_support, Finset.disjoint_left]
        intro z hz hz'
        rw [Equiv.Perm.support_swap hxy, Finset.mem_insert,
          Finset.mem_singleton] at hz'
        rcases hz' with rfl | rfl
        · exact hxs hz
        · exact hys hz
      refine ⟨g * Equiv.swap x y, ?_⟩
      rw [hdisj.cycleType_mul, hg, (Equiv.Perm.isCycle_swap hxy).cycleType,
        Equiv.Perm.card_support_swap hxy, Multiset.replicate_succ, add_comm,
        Multiset.singleton_add]

/-! ## The cycle type of an involution -/

/-- **An involution's cycle type is a power of `2`.**  Every entry of a cycle
type is at least `2`, and every entry divides the order, which divides `2`. -/
theorem cycleType_involution {z : Equiv.Perm Y} (hz : z * z = 1) :
    z.cycleType = Multiset.replicate (Multiset.card z.cycleType) 2 := by
  refine Multiset.eq_replicate_card.mpr fun b hb => ?_
  have h2 : 2 ≤ b := Equiv.Perm.two_le_of_mem_cycleType hb
  have hdvd : b ∣ orderOf z := by
    rw [← Equiv.Perm.lcm_cycleType]
    exact Multiset.dvd_lcm hb
  have horder : orderOf z ∣ 2 := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [pow_two]
    exact hz
  have hb2 : b ∣ 2 := hdvd.trans horder
  have hle : b ≤ 2 := Nat.le_of_dvd (by norm_num) hb2
  omega

/-! ## Involutions with evenly many transpositions are reachable -/

/-- **An involution with `2k` transpositions is a product of two conjugates of
`s` and `s⁻¹`, as soon as `6k ≤ |supp s|`.**

Its cycle type is `2^{2k} = 2^k + 2^k`, a doubling, and the witness of that
doubling is the permutation of type `2^k` built by
`exists_cycleType_replicate_two` — not a piece of `z`, which is why no halving
of `z` is needed.  The production theorem then reaches every permutation of
that cycle type in two conjugates. -/
theorem isBoundedConjProduct_two_of_involution {s z : Equiv.Perm Y} {k : ℕ}
    (hz : z * z = 1) (hk : Multiset.card z.cycleType = 2 * k)
    (hroom : 2 * k ≤ Fintype.card Y) (hfit : 6 * k ≤ s.support.card) :
    IsBoundedConjProduct s 2 z := by
  obtain ⟨g, hg⟩ := exists_cycleType_replicate_two k hroom
  have hgsupp : g.support.card = 2 * k := by
    have hsum := Equiv.Perm.sum_cycleType g
    rw [hg, Multiset.sum_replicate, smul_eq_mul] at hsum
    omega
  refine isBoundedConjProduct_two_of_cycleType_doubled (g := g) ?_ ?_
  · omega
  · rw [cycleType_involution hz, hk, hg, two_mul, Multiset.replicate_add]

end InvolutionBlocks
end GroupApproximation
