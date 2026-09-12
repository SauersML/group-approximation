import GroupApproximation.CharClass.CohomologyChartPeelUniqOf
import GroupApproximation.CharClass.CohomologyChartKunnethClosedOf

/-!
# The peel tower over a field, and existence of the decomposition

The coefficient-generic form of `CohomologyChartTower`, with the fibre class an arbitrary nonzero
`h ∈ H^2(ℂP^{d+1}; K)` rather than `cpGen`.  The degree convention and the recursion on the degree
are the `F₂` file's, for the same reasons: indexing as `m + 2 * j` with the class on the right puts
no cast in the tower's type, and each peel drops the degree by two, so existence needs no
truncation.

## Main declarations

* `KnCP.peel_rightOf` — one peel, with the class on the right.
* `KnCP.peelTowerOf` — the Horner polynomial in the pulled-back class.
* `KnCP.peelTower_congrOf`, `KnCP.peelTower_succ_ofOf`.
* `KnCP.exists_peelTowerOf` — **every class is a tower**, over the ring input.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

variable (K : Type) [Field K] (U : Type) [TopologicalSpace U] (d : ℕ)

/-! ## 1. One peel, with the class on the right -/

set_option maxHeartbeats 1000000 in
/-- **`cpSplitOf_closed` with the class cupped on the right**, and the degree written as `m + 2`. -/
theorem peel_rightOf (hring : CPRingOf K) (h : Hmod K (CPtop (d + 1)) 2) (h0 : h ≠ 0) (m : ℕ)
    (z : Hmod K (cpProdTop U d) (m + 2)) :
    ∃ (a : Hmod K (TopCat.of U) (m + 2)) (y : Hmod K (cpProdTop U d) m),
      z = pull (cpPrU U d) (m + 2) a + cup y (pull (cpPrCP U d) 2 h) := by
  obtain ⟨a, y, hay⟩ :=
    cpSplitOf_closed K hring (d + 1) (by omega) U h h0 m (cohCast (Nat.add_comm m 2) z)
  refine ⟨cohCast (Nat.add_comm 2 m) a, y, ?_⟩
  have h' := congrArg (cohCast (Nat.add_comm 2 m)) hay
  rw [cohCast_cohCast, cohCast_self, cohCast_add, ← KnHemi.pull_cohCastOf,
    cup_comm_of_even_left even_two (pull (cpSnd U (d + 1)) 2 h) y, cohCast_cohCast,
    cohCast_self] at h'
  exact h'

/-! ## 2. The tower -/

/-- **The Horner polynomial in the pulled-back class**, with every coefficient pulled back from
the base. -/
def peelTowerOf (h : Hmod K (CPtop (d + 1)) 2) (m : ℕ)
    (a : (j : ℕ) → Hmod K (TopCat.of U) (m + 2 * j)) :
    (k : ℕ) → Hmod K (cpProdTop U d) (m + 2 * k)
  | 0 => pull (cpPrU U d) (m + 2 * 0) (a 0)
  | (k + 1) => pull (cpPrU U d) (m + 2 * (k + 1)) (a (k + 1))
      + cup (peelTowerOf h m a k) (pull (cpPrCP U d) 2 h)

/-- The tower reads only the coefficients up to its length. -/
theorem peelTower_congrOf (h : Hmod K (CPtop (d + 1)) 2) (m : ℕ)
    (a b : (j : ℕ) → Hmod K (TopCat.of U) (m + 2 * j)) :
    ∀ (k : ℕ), (∀ j, j ≤ k → a j = b j) →
      peelTowerOf K U d h m a k = peelTowerOf K U d h m b k := by
  intro k
  induction k with
  | zero =>
    intro hab
    simp only [peelTowerOf]
    rw [hab 0 (by omega)]
  | succ e ih =>
    intro hab
    simp only [peelTowerOf]
    rw [hab (e + 1) (by omega), ih (fun j hj => hab j (by omega))]

/-- Extending a tower by one coefficient at the top. -/
theorem peelTower_succ_ofOf (h : Hmod K (CPtop (d + 1)) 2) (m k : ℕ)
    (a : (j : ℕ) → Hmod K (TopCat.of U) (m + 2 * j))
    (atop : Hmod K (TopCat.of U) (m + 2 * (k + 1))) :
    ∃ b : (j : ℕ) → Hmod K (TopCat.of U) (m + 2 * j),
      peelTowerOf K U d h m b (k + 1)
        = pull (cpPrU U d) (m + 2 * (k + 1)) atop
          + cup (peelTowerOf K U d h m a k) (pull (cpPrCP U d) 2 h) := by
  refine ⟨fun j => if hj : j = k + 1 then cohCast (by omega) atop else a j, ?_⟩
  have hcong : peelTowerOf K U d h m
      (fun j => if hj : j = k + 1 then cohCast (by omega) atop else a j) k
      = peelTowerOf K U d h m a k :=
    peelTower_congrOf K U d h m _ a k (fun j hj => by rw [dif_neg (by omega)])
  simp only [peelTowerOf]
  rw [dif_pos trivial, cohCast_self, hcong]

/-! ## 3. Existence -/

set_option maxHeartbeats 1000000 in
/-- **Every class on `U × ℂP^{d+1}` is a tower**, over the ring input, for any nonzero class. -/
theorem exists_peelTowerOf (hring : CPRingOf K) (h : Hmod K (CPtop (d + 1)) 2) (h0 : h ≠ 0) :
    ∀ (N : ℕ) (z : Hmod K (cpProdTop U d) N),
      ∃ (m k : ℕ) (_ : m < 2) (hN : m + 2 * k = N)
        (a : (j : ℕ) → Hmod K (TopCat.of U) (m + 2 * j)),
        z = cohCast hN (peelTowerOf K U d h m a k) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro z
    rcases Nat.lt_or_ge N 2 with hN | hN
    · obtain ⟨a₀, ha₀⟩ := exists_pull_cpFst_of_ltOf K U (d + 1) N hN z
      refine ⟨N, 0, hN, by omega,
        fun j => Nat.casesOn (motive := fun j => Hmod K (TopCat.of U) (N + 2 * j)) j a₀
          (fun _ => 0), ?_⟩
      rw [cohCast_self]
      exact ha₀
    · obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
      obtain ⟨atop, y, hay⟩ := peel_rightOf K U d hring h h0 M z
      obtain ⟨m, k, hm, hMk, a', ha'⟩ := ih M (by omega) y
      subst hMk
      rw [cohCast_self] at ha'
      obtain ⟨b, hb⟩ := peelTower_succ_ofOf K U d h m k a' atop
      refine ⟨m, k + 1, hm, by omega, b, ?_⟩
      rw [cohCast_self, hb, ← ha']
      exact hay

end KnCP

end

end GroupApproximation.CharClass
