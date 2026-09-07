import GroupApproximation.Leavitt.ElementaryNormalGeneration
import GroupApproximation.Leavitt.OneSidedCompressorDefect
import Mathlib.Algebra.BigOperators.Fin

/-!
# A full coefficient normally generates the elementary group

`non_mf_groups_exist.tex`, Section `sec:one-sided-inverses`, the last step of
the proof of Theorem `thm:full-defect-ring`:

> Let `N` be the normal closure of `d` in `G`.  For arbitrary `a,b ∈ R`, the
> Steinberg relations give `[e₄₁(a), e₁₃(e)] = e₄₃(ae)` and
> `[e₄₃(ae), e₃₂(b)] = e₄₂(aeb)`.  It follows that
> `e₄₂(1) = ∏_j e₄₂(a_j e b_j) ∈ N`.

This module proves that step over an arbitrary unital ring, for an arbitrary
coefficient `x` in place of `e`, and for an arbitrary index type with at least
four indices: a normal subgroup containing one root `e_{ij}(x)` whose
coefficient is **full**, i.e. satisfies the printed ideal condition

  `∃ m, ∃ a b : Fin m → R, ∑ k, a k * x * b k = 1`,

is already everything.  Idempotence of `x` is not used, and neither is any
structure theory of `R`.

The printed proof then says "Elementary signed permutation matrices conjugate
this element to every off-diagonal position, up to a sign", and finishes with
one more Steinberg relation.  Both are already carried by
`elementaryGroup_normal_eq_top_of_elementaryRoot_mem`
(`Leavitt.ElementaryNormalGeneration`), whose hypothesis is a *unit sandwich*
`a * x * b = 1`; the unit root `e_{pq}(1)` produced below is sandwiched for
free.  So four indices are spent only on the two commutators above, and the
spread over all positions costs three.

The rank-four corollary `printedDefect_eq_top` combines this with the
rank-four milestone of `Leavitt.OneSidedCompressorDefect`: for a one-sided
inverse pair with full `e = 1 - st`, the printed defect `𝔇_G(L)` of the
upper-left `EL₃(R)` in `EL₄(R)` is all of `EL₄(R)`.
-/

namespace GroupApproximation
namespace FullIdempotent

open scoped commutatorElement

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-! ### Two indices away from a given pair -/

/-- With four indices available, a given ordered pair has two further indices
distinct from it and from each other.  This is what the two printed Steinberg
commutators consume. -/
theorem exists_two_further_indices (hcard : 4 ≤ Fintype.card ι) (i j : ι) :
    ∃ p q : ι, p ≠ i ∧ p ≠ j ∧ q ≠ i ∧ q ≠ j ∧ p ≠ q := by
  classical
  have hcompl : 1 < (({i, j} : Finset ι)ᶜ).card := by
    have h1 : (({i, j} : Finset ι)ᶜ).card
        = Fintype.card ι - ({i, j} : Finset ι).card := Finset.card_compl _
    have h2 : ({i, j} : Finset ι).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by simp)
    omega
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hcompl
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton,
    not_or] at hp hq
  exact ⟨p, q, hp.1, hp.2, hq.1, hq.2, hpq⟩

/-! ### Commutators against a normal subgroup -/

/-- A commutator whose **right** entry lies in a normal subgroup lies in it. -/
theorem commutator_mem_of_right (N : Subgroup (elementaryGroup ι R))
    [hN : N.Normal] (x : elementaryGroup ι R) {n : elementaryGroup ι R}
    (hn : n ∈ N) : ⁅x, n⁆ ∈ N := by
  rw [commutatorElement_def]
  exact N.mul_mem (hN.conj_mem n hn x) (N.inv_mem hn)

/-- A commutator whose **left** entry lies in a normal subgroup lies in it. -/
theorem commutator_mem_of_left (N : Subgroup (elementaryGroup ι R))
    [N.Normal] {n : elementaryGroup ι R} (hn : n ∈ N)
    (x : elementaryGroup ι R) : ⁅n, x⁆ ∈ N := by
  rw [← commutatorElement_inv]
  exact N.inv_mem (commutator_mem_of_right N x hn)

/-! ### Finite sums of coefficients inside one root subgroup -/

/-- A finite product of roots at a fixed pair is the root of the sum of the
coefficients, so a normal subgroup containing each summand's root contains the
root of the sum.  This is the printed `e₄₂(1) = ∏_j e₄₂(a_j e b_j)`. -/
theorem elementaryRoot_sum_mem {α : Type*} [DecidableEq α]
    (N : Subgroup (elementaryGroup ι R)) {p q : ι} (hpq : p ≠ q)
    (s : Finset α) (f : α → R)
    (hf : ∀ c ∈ s, elementaryRoot p q hpq (f c) ∈ N) :
    elementaryRoot p q hpq (∑ c ∈ s, f c) ∈ N := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
      intro _
      rw [Finset.sum_empty, elementaryRoot_zero]
      exact N.one_mem
  | insert c s hc ih =>
      intro hf
      rw [Finset.sum_insert hc, ← elementaryRoot_mul]
      exact N.mul_mem (hf c (Finset.mem_insert_self c s))
        (ih fun d hd ↦ hf d (Finset.mem_insert_of_mem hd))

/-! ### The theorem -/

/-- **A full coefficient normally generates `EL_ι(R)`.**  If a normal subgroup
`N` of `EL_ι(R)` contains one elementary root `e_{ij}(x)` and `x` is full,
`R x R = R` in the printed indexed-sum form `∑ k, a k * x * b k = 1`, then
`N = ⊤`.  Four indices are needed, exactly as in the printed proof; no
idempotence of `x` and no structure theory of `R` is used. -/
theorem elementaryGroup_normal_eq_top_of_full (hcard : 4 ≤ Fintype.card ι)
    (N : Subgroup (elementaryGroup ι R)) [N.Normal]
    {i j : ι} (hij : i ≠ j) {x : R}
    (hmem : elementaryRoot i j hij x ∈ N)
    (hfull : ∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * x * b k = 1) :
    N = ⊤ := by
  classical
  obtain ⟨m, aa, bb, hsum⟩ := hfull
  obtain ⟨p, q, hpi, hpj, -, hqj, hpq⟩ := exists_two_further_indices hcard i j
  have hjq : j ≠ q := Ne.symm hqj
  -- The two printed Steinberg steps.
  have step : ∀ a b : R, elementaryRoot p q hpq (a * x * b) ∈ N := by
    intro a b
    have h1 : elementaryRoot p j hpj (a * x) ∈ N := by
      have h := commutator_mem_of_right N (elementaryRoot p i hpi a) hmem
      rwa [elementaryRoot_commutator p i j hpi hij hpj a x] at h
    have h2 := commutator_mem_of_left N h1 (elementaryRoot j q hjq b)
    rwa [elementaryRoot_commutator p j q hpj hjq hpq (a * x) b] at h2
  -- The finite sum turns the full coefficient into a unit root.
  have hone : elementaryRoot p q hpq (1 : R) ∈ N := by
    have h := elementaryRoot_sum_mem N hpq Finset.univ
      (fun c : Fin m ↦ aa c * x * bb c) (fun c _ ↦ step (aa c) (bb c))
    rwa [hsum] at h
  exact elementaryGroup_normal_eq_top_of_elementaryRoot_mem (by omega) N hpq hone
    ⟨1, 1, by simp⟩

/-- **Normal generation from a single full root.** -/
theorem normalClosure_elementaryRoot_eq_top_of_full
    (hcard : 4 ≤ Fintype.card ι) {i j : ι} (hij : i ≠ j) {x : R}
    (hfull : ∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * x * b k = 1) :
    Subgroup.normalClosure
        ({elementaryRoot i j hij x} : Set (elementaryGroup ι R)) = ⊤ :=
  elementaryGroup_normal_eq_top_of_full hcard _ hij
    (Subgroup.subset_normalClosure (Set.mem_singleton _)) hfull

/-! ### The rank-four corollary -/

open OneSidedCompressor

/-- **`𝔇_G(L) = ⊤` at rank four.**  For a one-sided inverse pair over any
unital ring whose complementary idempotent `e = 1 - st` is full, the printed
defect of the upper-left `EL₃(R)` inside `EL₄(R)` is everything. -/
theorem printedDefect_eq_top (P : OneSidedInverse R)
    (hfull : ∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * P.e * b k = 1) :
    Manuscript.OneSidedMFRadical.printedDefect (core R) = ⊤ := by
  have hmem : elementaryRoot (coreIdx 0) (coreIdx 2)
      (coreIdx_injective.ne zeroNeTwo) P.e ∈
        Manuscript.OneSidedMFRadical.printedDefect (core R) :=
    printedDefectRoot_mem_printedDefect P
  refine elementaryGroup_normal_eq_top_of_full ?_ _
    (coreIdx_injective.ne zeroNeTwo) hmem hfull
  simp

end FullIdempotent
end GroupApproximation
