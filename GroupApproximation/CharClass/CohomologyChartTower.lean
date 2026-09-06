import GroupApproximation.CharClass.CohomologyChartPeelUniq

/-!
# The peel tower, and existence of the decomposition

`cpSplit_closed` peels one generator off a class on `U × ℂP^{d+1}`.  Iterating it
expresses a class as a polynomial in the generator with coefficients pulled back
from the base.  This file gives that polynomial a name and proves it exists.

## The degree convention, which is forced

Indexing degrees as `m + 2 * j` and cupping the generator on the **right** is the
only arrangement in which no cast appears in the statement.  `Nat.mul` recurses on
its second argument, so `2 * (k + 1)` reduces to `2 * k + 2`; `Nat.add` recurses on
its second, so `m + (2 * k + 2)` and `(m + 2 * k) + 2` are the same term.  Indexing
as `2 * j + m`, or cupping on the left, breaks one of those and forces a
`cohCast` into the type of the tower itself.  `cpSplit_closed` peels with the
generator on the left, so one `cup_comm` is unavoidable; `peel_right` pays it once,
inside the proof, so that nothing downstream sees it.

## Why the recursion is on the degree

Each peel drops the degree by two and leaves the fibre alone, so the tower
terminates when the degree falls below two, where `lhLow_gen` says the class is a
pullback.  The rank never enters.  That is why existence needs no truncation,
and it is the reason existence is much cheaper than uniqueness: uniqueness does
need the truncation, and with it a Mayer–Vietoris induction on the rank.

## Main declarations

* `KnCP.peel_right` — one peel, with the generator on the right.
* `KnCP.peelTower` — the Horner polynomial in the generator.
* `KnCP.peelTower_congr` — it depends only on the coefficients it reaches.
* `KnCP.peelTower_succ_of` — extending a tower by one coefficient at the top.
* `KnCP.exists_peelTower` — **every class is a tower**.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

variable (U : Type) [TopologicalSpace U] (d : ℕ)

/-! ## 1. One peel, with the generator on the right -/

set_option maxHeartbeats 1000000 in
/-- **`cpSplit_closed` with the generator cupped on the right**, and the degree
written as `m + 2`.  This is where the single `cup_comm` is spent. -/
theorem peel_right (hd : 1 ≤ d + 1) (m : ℕ) (z : Hmod2 (cpProdTop U d) (m + 2)) :
    ∃ (a : Hmod2 (TopCat.of U) (m + 2)) (y : Hmod2 (cpProdTop U d) m),
      z = pull (cpPrU U d) (m + 2) a
        + cup y (pull (cpPrCP U d) 2 (cpGen (d + 1) hd)) := by
  obtain ⟨a, y, hay⟩ :=
    cpSplit_closed (d + 1) (by omega) U hd m (cohCast (Nat.add_comm m 2) z)
  refine ⟨cohCast (Nat.add_comm 2 m) a, y, ?_⟩
  have h := congrArg (cohCast (Nat.add_comm 2 m)) hay
  rw [cohCast_cohCast, cohCast_self, cohCast_add, ← KnHemi.pull_cohCast,
    cup_comm (pull (cpSnd U (d + 1)) 2 (cpGen (d + 1) hd)) y, cohCast_cohCast,
    cohCast_self] at h
  exact h

/-! ## 2. The tower -/

/-- **The Horner polynomial in the generator**, with every coefficient pulled back
from the base.  Expanded, `peelTower … a k` is the sum over `i ≤ k` of `a i`
pulled back and cupped with the `(k - i)`-th power of the generator: coefficient
on the left, power on the right, which is `lhTerm`'s convention. -/
def peelTower (hd : 1 ≤ d + 1) (m : ℕ)
    (a : (j : ℕ) → Hmod2 (TopCat.of U) (m + 2 * j)) :
    (k : ℕ) → Hmod2 (cpProdTop U d) (m + 2 * k)
  | 0 => pull (cpPrU U d) (m + 2 * 0) (a 0)
  | (k + 1) => pull (cpPrU U d) (m + 2 * (k + 1)) (a (k + 1))
      + cup (peelTower hd m a k) (pull (cpPrCP U d) 2 (cpGen (d + 1) hd))

/-- The tower reads only the coefficients up to its length. -/
theorem peelTower_congr (hd : 1 ≤ d + 1) (m : ℕ)
    (a b : (j : ℕ) → Hmod2 (TopCat.of U) (m + 2 * j)) :
    ∀ (k : ℕ), (∀ j, j ≤ k → a j = b j) →
      peelTower U d hd m a k = peelTower U d hd m b k := by
  intro k
  induction k with
  | zero =>
    intro h
    simp only [peelTower]
    rw [h 0 (by omega)]
  | succ e ih =>
    intro h
    simp only [peelTower]
    rw [h (e + 1) (by omega), ih (fun j hj => h j (by omega))]

/-- Extending a tower by one coefficient at the top.  The new coefficient is
stated at the index the tower needs, so the branch that selects it carries a cast
between syntactically equal degrees and disappears. -/
theorem peelTower_succ_of (hd : 1 ≤ d + 1) (m k : ℕ)
    (a : (j : ℕ) → Hmod2 (TopCat.of U) (m + 2 * j))
    (atop : Hmod2 (TopCat.of U) (m + 2 * (k + 1))) :
    ∃ b : (j : ℕ) → Hmod2 (TopCat.of U) (m + 2 * j),
      peelTower U d hd m b (k + 1)
        = pull (cpPrU U d) (m + 2 * (k + 1)) atop
          + cup (peelTower U d hd m a k)
              (pull (cpPrCP U d) 2 (cpGen (d + 1) hd)) := by
  refine ⟨fun j => if h : j = k + 1 then cohCast (by omega) atop else a j, ?_⟩
  have hcong : peelTower U d hd m
      (fun j => if h : j = k + 1 then cohCast (by omega) atop else a j) k
      = peelTower U d hd m a k :=
    peelTower_congr U d hd m _ a k (fun j hj => by rw [dif_neg (by omega)])
  simp only [peelTower]
  rw [dif_pos trivial, cohCast_self, hcong]

/-! ## 3. Existence -/

set_option maxHeartbeats 1000000 in
/-- **Every class on `U × ℂP^{d+1}` is a tower.**  The recursion is on the degree,
not the rank: each peel drops the degree by two, and below two `lhLow_gen`
finishes.  No truncation is needed, because the coefficients beyond the rank
multiply powers of the generator that vanish. -/
theorem exists_peelTower (hd : 1 ≤ d + 1) :
    ∀ (N : ℕ) (z : Hmod2 (cpProdTop U d) N),
      ∃ (m k : ℕ) (_ : m < 2) (hN : m + 2 * k = N)
        (a : (j : ℕ) → Hmod2 (TopCat.of U) (m + 2 * j)),
        z = cohCast hN (peelTower U d hd m a k) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro z
    rcases Nat.lt_or_ge N 2 with hN | hN
    · obtain ⟨a₀, ha₀⟩ := exists_pull_cpFst_of_lt U (d + 1) N hN z
      refine ⟨N, 0, hN, by omega,
        fun j => Nat.casesOn (motive := fun j => Hmod2 (TopCat.of U) (N + 2 * j)) j a₀
          (fun _ => 0), ?_⟩
      rw [cohCast_self]
      exact ha₀
    · obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
      obtain ⟨atop, y, hay⟩ := peel_right U d hd M z
      obtain ⟨m, k, hm, hMk, a', ha'⟩ := ih M (by omega) y
      subst hMk
      rw [cohCast_self] at ha'
      obtain ⟨b, hb⟩ := peelTower_succ_of U d hd m k a' atop
      refine ⟨m, k + 1, hm, by omega, b, ?_⟩
      rw [cohCast_self, hb, ← ha']
      exact hay

end KnCP

end

end GroupApproximation.CharClass
