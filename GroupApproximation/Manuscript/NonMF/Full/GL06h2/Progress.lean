import GroupApproximation.GGT.HullSCLemma49PowerChain

/-!
# GL06h2: linear progress along the powers of a two-block element

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex ~2121).

Split a relator value `x` at a half-way vertex `a`.  The chain
`1, a, x, x a, x², x² a, …` has two alternating edge lengths `d(1,a)` and `d(a,x)` and two
alternating local Gromov products.  When both edges are long and both products are small, the
bounded-index local-to-global engine `HullGeometry.finite_chain_backtracking_and_progress` gives
linear progress: `|x^m| ≥ 2m (L - 2(C + δ))`.

* `halfChain`: the alternating chain.
* `progress_halfChain`: the linear lower bound on `|x^m|`.
-/

namespace GroupApproximation.Full.GL06h2

universe u

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

variable {G : Type u} [Group G]

/-- The alternating chain `x^k` (even index `2k`) and `x^k a` (odd index `2k+1`). -/
def halfChain (x a : G) (t : ℕ) : G :=
  if t % 2 = 0 then x ^ (t / 2) else x ^ (t / 2) * a

theorem halfChain_of_mod_eq_zero (x a : G) {t : ℕ} (ht : t % 2 = 0) :
    halfChain x a t = x ^ (t / 2) := by
  unfold halfChain
  rw [if_pos ht]

theorem halfChain_of_mod_eq_one (x a : G) {t : ℕ} (ht : t % 2 = 1) :
    halfChain x a t = x ^ (t / 2) * a := by
  have hne : ¬ t % 2 = 0 := by omega
  unfold halfChain
  rw [if_neg hne]

theorem halfChain_even (x a : G) (k : ℕ) : halfChain x a (2 * k) = x ^ k := by
  have h0 : (2 * k) % 2 = 0 := by omega
  have h1 : (2 * k) / 2 = k := by omega
  rw [halfChain_of_mod_eq_zero x a h0, h1]

theorem halfChain_odd (x a : G) (k : ℕ) : halfChain x a (2 * k + 1) = x ^ k * a := by
  have h0 : (2 * k + 1) % 2 = 1 := by omega
  have h1 : (2 * k + 1) / 2 = k := by omega
  rw [halfChain_of_mod_eq_one x a h0, h1]

/-- **Linear progress of a two-block element** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121).  If both blocks `1 → a` and `a → x` have length at least `L`,
and the vertex `a` is `C`-close to geodesic between `1` and `x` and between `a⁻¹ x` shifted
(`a → x → x a`), then `|x^m| ≥ 2m (L - 2(C + δ))`. -/
theorem progress_halfChain (A : Alphabet G) {delta : ℕ}
    (hdelta : Hyperbolic.IsFourPointHyperbolic A.carrier delta) {x a : G} {L C : ℕ}
    (hedge1 : L ≤ wordDist A.carrier 1 a) (hedge2 : L ≤ wordDist A.carrier a x)
    (hloc1 : wordDist A.carrier 1 a + wordDist A.carrier a x ≤
      wordDist A.carrier 1 x + 2 * C)
    (hloc2 : wordDist A.carrier a x + wordDist A.carrier 1 a ≤
      wordDist A.carrier a (x * a) + 2 * C)
    (hgap : 2 * (C + delta) < L) (m : ℕ) :
    2 * m * (L - 2 * (C + delta)) ≤ wordNorm A.carrier (x ^ m) := by
  have hS := A.symmetricGenerating
  have hhyp : IsHyperbolicSpace (delta : ℝ) (Cayley A) :=
    GGT.isHyperbolicSpace_cayley_of_fourPoint A hdelta
  have T1 : ∀ k : ℕ, wordDist A.carrier (x ^ k) (x ^ k * a) = wordDist A.carrier 1 a := by
    intro k
    have h := wordDist_left_invariant A.carrier (x ^ k) 1 a
    rw [mul_one] at h
    exact h
  have T2 : ∀ k : ℕ,
      wordDist A.carrier (x ^ k * a) (x ^ (k + 1)) = wordDist A.carrier a x := by
    intro k
    rw [pow_succ]
    exact wordDist_left_invariant A.carrier (x ^ k) a x
  have T3 : ∀ k : ℕ, wordDist A.carrier (x ^ k) (x ^ (k + 1)) = wordDist A.carrier 1 x := by
    intro k
    have h := wordDist_left_invariant A.carrier (x ^ k) 1 x
    rw [mul_one, ← pow_succ] at h
    exact h
  have T4 : ∀ k : ℕ,
      wordDist A.carrier (x ^ (k + 1) * a) (x ^ (k + 1)) = wordDist A.carrier 1 a := by
    intro k
    have h := wordDist_left_invariant A.carrier (x ^ (k + 1)) a 1
    rw [mul_one] at h
    rw [h]
    exact wordDist_comm hS a 1
  have T5 : ∀ k : ℕ,
      wordDist A.carrier (x ^ k * a) (x ^ (k + 1) * a) = wordDist A.carrier a (x * a) := by
    intro k
    have h := wordDist_left_invariant A.carrier (x ^ k) a (x * a)
    rw [← mul_assoc, ← pow_succ] at h
    exact h
  let y : ℕ → Cayley A := fun t => Cayley.of A (halfChain x a t)
  have hdist : ∀ s t : ℕ, dist (y s) (y t) =
      ((wordDist A.carrier (halfChain x a s) (halfChain x a t) : ℕ) : ℝ) := by
    intro s t
    rfl
  have hpar : ∀ n : ℕ, (∃ k, n = 2 * k) ∨ ∃ k, n = 2 * k + 1 := by
    intro n
    by_cases h : n % 2 = 0
    · exact Or.inl ⟨n / 2, by omega⟩
    · exact Or.inr ⟨n / 2, by omega⟩
  have hedge : ∀ n : ℕ, n < 2 * m → (L : ℝ) ≤ dist (y n) (y (n + 1)) := by
    intro n _hn
    rw [hdist]
    rcases hpar n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [halfChain_even x a k, halfChain_odd x a k, T1 k]
      exact_mod_cast hedge1
    · have h2 : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
      rw [h2, halfChain_odd x a k, halfChain_even x a (k + 1), T2 k]
      exact_mod_cast hedge2
  have hlocal : ∀ n : ℕ, n + 2 ≤ 2 * m →
      gromovProduct (y n) (y (n + 2)) (y (n + 1)) ≤ (C : ℝ) := by
    intro n _hn
    unfold gromovProduct
    rw [hdist, hdist, hdist, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    rcases hpar n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have h2 : 2 * k + 2 = 2 * (k + 1) := by omega
      rw [h2, halfChain_even x a k, halfChain_odd x a k, halfChain_even x a (k + 1),
        T1 k, T3 k]
      have hc : wordDist A.carrier (x ^ (k + 1)) (x ^ k * a) = wordDist A.carrier a x := by
        rw [wordDist_comm hS, T2 k]
      rw [hc]
      have hloc1' : ((wordDist A.carrier 1 a : ℕ) : ℝ) + ((wordDist A.carrier a x : ℕ) : ℝ) ≤
          ((wordDist A.carrier 1 x : ℕ) : ℝ) + 2 * (C : ℝ) := by
        exact_mod_cast hloc1
      linarith
    · have h2 : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
      have h3 : 2 * k + 1 + 2 = 2 * (k + 1) + 1 := by omega
      rw [h2, h3, halfChain_odd x a k, halfChain_even x a (k + 1), halfChain_odd x a (k + 1),
        T2 k, T4 k, T5 k]
      have hloc2' : ((wordDist A.carrier a x : ℕ) : ℝ) + ((wordDist A.carrier 1 a : ℕ) : ℝ) ≤
          ((wordDist A.carrier a (x * a) : ℕ) : ℝ) + 2 * (C : ℝ) := by
        exact_mod_cast hloc2
      linarith
  have hCd : (0 : ℝ) ≤ (C : ℝ) + (delta : ℝ) := by positivity
  have hgapR : 2 * ((C : ℝ) + (delta : ℝ)) < (L : ℝ) := by exact_mod_cast hgap
  have hprog := (finite_chain_backtracking_and_progress hhyp hCd hgapR y hedge hlocal
    (2 * m) le_rfl).1
  have h0 : halfChain x a 0 = 1 := by
    have h := halfChain_even x a 0
    rw [Nat.mul_zero, pow_zero] at h
    exact h
  have hd : dist (y 0) (y (2 * m)) = ((wordNorm A.carrier (x ^ m) : ℕ) : ℝ) := by
    rw [hdist, h0, halfChain_even x a m, wordDist_one_left]
  rw [hd] at hprog
  obtain ⟨e, he⟩ : ∃ e, L = 2 * (C + delta) + e := ⟨L - 2 * (C + delta), by omega⟩
  have hsub : L - 2 * (C + delta) = e := by omega
  have hL : (L : ℝ) = 2 * ((C : ℝ) + (delta : ℝ)) + (e : ℝ) := by exact_mod_cast he
  have hcoef : (L : ℝ) - 2 * ((C : ℝ) + (delta : ℝ)) = (e : ℝ) := by linarith
  rw [hcoef] at hprog
  have hnat : e * (2 * m) ≤ wordNorm A.carrier (x ^ m) := by exact_mod_cast hprog
  rw [hsub]
  calc 2 * m * e = e * (2 * m) := by ring
    _ ≤ wordNorm A.carrier (x ^ m) := hnat

end GroupApproximation.Full.GL06h2
