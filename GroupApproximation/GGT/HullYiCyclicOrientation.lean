import Mathlib

/-!
# The orientation combinatorics in Hull's `yi`

Hull excludes the inverse orientation after Lemma 4.21(b) because a cyclic
word on at least three distinct peripheral indices advances by one, whereas
its inverse retreats by one.  Two consecutive matched components would force
the successor and predecessor of one cyclic index to coincide, which is
impossible once the cycle has length at least three.
-/

namespace GroupApproximation
namespace HullSC

/-- The next index in a cyclically ordered `Fin k`. -/
def cyclicSucc {k : ℕ} (i : Fin k) : Fin k :=
  ⟨(i + 1) % k, Nat.mod_lt _ i.pos⟩

/-- The preceding index in a cyclically ordered `Fin k`. -/
def cyclicPred {k : ℕ} (i : Fin k) : Fin k :=
  ⟨(i + k - 1) % k, Nat.mod_lt _ i.pos⟩

/-- On a cycle of length at least three, advancing and retreating from the
same index give different indices. -/
theorem cyclicSucc_ne_cyclicPred {k : ℕ} (hk : 3 ≤ k) (i : Fin k) :
    cyclicSucc i ≠ cyclicPred i := by
  intro heq
  have hval : (i.val + 1) % k = (i.val + k - 1) % k :=
    congrArg Fin.val heq
  have hi : i.val < k := i.isLt
  by_cases hi0 : i.val = 0
  · have hk0 : 0 < k := by omega
    have h1 : (1 : ℕ) % k = 1 := Nat.mod_eq_of_lt (by omega)
    have hk1 : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by omega)
    rw [hi0] at hval
    simp only [Nat.zero_add] at hval
    rw [h1, hk1] at hval
    omega
  · have hi1 : 1 ≤ i.val := by omega
    have hsum : i.val + k - 1 = (i.val - 1) + k := by omega
    have him1 : i.val - 1 < k := by omega
    have hrhs : (i.val + k - 1) % k = i.val - 1 := by
      rw [hsum, Nat.add_mod, Nat.mod_self, add_zero]
      rw [Nat.mod_mod]
      exact Nat.mod_eq_of_lt him1
    by_cases hilast : i.val + 1 < k
    · have hlhs : (i.val + 1) % k = i.val + 1 := Nat.mod_eq_of_lt hilast
      rw [hlhs, hrhs] at hval
      omega
    · have hieq : i.val + 1 = k := by omega
      have hlhs : (i.val + 1) % k = 0 := by rw [hieq, Nat.mod_self]
      rw [hlhs, hrhs] at hval
      omega

/-- Two words following opposite cyclic orientations cannot have two
consecutive component indices matched in order.  This is the precise
`123123…` versus `321321…` step in Hull's proofs of Lemmas 5.4 and 5.6. -/
theorem not_two_consecutive_matches_opposite_orientation
    {k : ℕ} (hk : 3 ≤ k) (forward backward : ℕ → Fin k)
    (hforward : ∀ n, forward (n + 1) = cyclicSucc (forward n))
    (hbackward : ∀ n, backward (n + 1) = cyclicPred (backward n)) :
    ¬ ∃ n m : ℕ,
      forward n = backward m ∧ forward (n + 1) = backward (m + 1) := by
  rintro ⟨n, m, hzero, hone⟩
  have hbad : cyclicSucc (forward n) = cyclicPred (forward n) := by
    calc
      cyclicSucc (forward n) = forward (n + 1) := (hforward n).symm
      _ = backward (m + 1) := hone
      _ = cyclicPred (backward m) := hbackward m
      _ = cyclicPred (forward n) := by rw [hzero]
  exact cyclicSucc_ne_cyclicPred hk (forward n) hbad

end HullSC
end GroupApproximation
