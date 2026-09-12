import GroupApproximation.CharClass.ParityPTwistSymm

/-!
# L4a: the linear coefficient of the twisted elementary symmetric polynomial

Lane `lix-evenside` (successor of `sp-evenside`), `sp-design` §3.3, L4a.

With `φ_κ : y ↦ y + κ·y^p` the twist and `N = i·p + 1`, this file computes the coefficient of
`e_N` in the `e`-expansion of `φ_κ(e_{i+1})`, modulo decomposables:

```text
  eCoeff_{N}( φ_κ(e_{i+1}) )  =  (−1)^{i + ip} · κ^i · N .
```

`sp-design`'s proof, and the one formalised: `φ_κ` is a ring endomorphism, so it descends to
the indecomposables; there Newton reads `p_M ≡ (−1)^{M+1}·M·e_M`
(`ParityPNewtonValue.eCoeff_psumSub`), and the binomial theorem gives
`φ_κ(p_b) = ∑_k κ^{b−k}·C(b,k)·p_{k + p(b−k)}` (`ParityPTwist.twist_psum`), in which only
`k = 1` reaches weight `N` (`twist_psum_weight`).  Newton applied to `e_{i+1}` itself, pushed
through `φ_κ`, gives `(i+1)·(−1)^{i+2}·eCoeff_N(φ_κ e_{i+1}) = κ^i·(i+1)·(−1)^{N+1}·N`, and the
factor `i + 1` cancels in any domain of characteristic zero.  No division survives into the
statement.

## Signs, and the change of Chern-root convention

The sign `(−1)^{i + ip} = (−1)^{i(p−1)}` is the only place a convention could enter.  The change of
Chern-root convention is the ring automorphism `h ↦ −h`.  It commutes with the total reduced
power `P`, for two different reasons:
* at odd `p`, because `p − 1` is even, every weight component of `E_j` scales by the same
  `(−1)^j`;
* at `p = 2`, because `h ↦ −h` is the identity.

Both clauses are needed, and neither covers the primes the other does.  The leading coefficient
is invariant under the change: applying `h ↦ −h` to `P^i(γ_{i+1}) = u_i·γ_{ip+1} + D` scales the
two sides by `(−1)^{i+1}` and `(−1)^{ip+1}`, whose ratio `(−1)^{i(p−1)}` is `1` at odd `p`, while
the automorphism is the identity at `p = 2`.  So the unit field of (W) is required by the
normalisation constant `κ` alone.  The single authority on the root convention is the
Chern-relation file (program note §1.5, "Ruling on the roots"); nothing here restates it.

## Main results

* `ParityP.eCoeff_esymmSub_of_ne`, `ParityP.eCoeff_psumSub_self` — `eCoeff` on `e_M` and `p_M`.
* `ParityP.twistSub_psumSub` — the binomial expansion of `φ_κ(p_b)` in the subalgebra.
* `ParityP.eCoeff_twistSub_psumSub` — Newton modulo decomposables survives the twist.
* `ParityP.eCoeff_twistSub_esymmSub_succ` — **the value** `(−1)^{i+ip}·κ^i·(ip+1)`.
-/

set_option autoImplicit false

namespace GroupApproximation.CharClass

namespace ParityP

open MvPolynomial

section WuValue

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The sign bookkeeping of the value, isolated so that no `ring` call ever meets a sign
with a variable exponent. -/
theorem neg_one_pow_add_two_mul_pow_add_two {S : Type*} [Ring S] (a b : ℕ) :
    (-1 : S) ^ (a + 1 + 1) * (-1 : S) ^ (b + 1 + 1) = (-1 : S) ^ (a + b) := by
  rw [← pow_add, show a + 1 + 1 + (b + 1 + 1) = (a + b) + 2 * 2 by omega, pow_add, pow_mul,
    neg_one_sq, one_pow, mul_one]

/-- `eCoeff j` annihilates `e_M` unless `M = j + 1`. -/
theorem eCoeff_esymmSub_of_ne (j : Fin n) {M : ℕ} (hM : M ≠ (j : ℕ) + 1) :
    eCoeff j (esymmSub R n M) = 0 :=
  eCoeff_eq_zero_of_degree_ne j (esymmSub R n M) (esymm_isHomogeneous M) (Ne.symm hM)

/-- `eCoeff j` annihilates `p_M` unless `M = j + 1`. -/
theorem eCoeff_psumSub_of_ne (j : Fin n) {M : ℕ} (hM : 0 < M) (hne : M ≠ (j : ℕ) + 1) :
    eCoeff j (psumSub R n M) = 0 := by
  rw [eCoeff_psumSub j M hM, eCoeff_esymmSub_of_ne j hne, mul_zero]

/-- Newton modulo decomposables at the index `eCoeff j` reads. -/
theorem eCoeff_psumSub_self (j : Fin n) :
    eCoeff j (psumSub R n ((j : ℕ) + 1))
      = (-1 : R) ^ ((j : ℕ) + 1 + 1) * (((j : ℕ) + 1 : ℕ) : R) := by
  rw [eCoeff_psumSub j ((j : ℕ) + 1) (Nat.succ_pos _), eCoeff_esymmSub_self j, mul_one]

/-- **The twist on a power sum, in the symmetric subalgebra.** -/
theorem twistSub_psumSub (p : ℕ) (κ : R) (b : ℕ) :
    twistSub p κ (psumSub R n b)
      = ∑ k ∈ Finset.range (b + 1),
          (κ ^ (b - k) * (b.choose k : R)) • psumSub R n (k + p * (b - k)) := by
  apply Subtype.ext
  rw [twistSub_coe, psumSub_coe, twist_psum, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Subalgebra.coe_smul, psumSub_coe, MvPolynomial.smul_eq_C_mul, map_mul, map_natCast]

/-- **Newton modulo decomposables survives the twist.**  Every term of the subtracted sum in
Newton's identity is `e_a · p_b` with `a, b > 0`; the twist preserves products and constant
terms, so both twisted factors still have vanishing constant term and `eCoeff` kills their
product. -/
theorem eCoeff_twistSub_psumSub {p : ℕ} (hp : 1 ≤ p) (κ : R) (j : Fin n) (M : ℕ) (hM : 0 < M) :
    eCoeff j (twistSub p κ (psumSub R n M))
      = (-1 : R) ^ (M + 1) * (M : R) * eCoeff j (twistSub p κ (esymmSub R n M)) := by
  rw [psumSub_eq_newton M hM, map_sub, map_smul, map_sum, eCoeff_sub, eCoeff_smul, eCoeff_sum]
  have hzero : ∀ a ∈ newtonIdx M,
      eCoeff j (twistSub p κ (((-1 : R) ^ a.1) • (esymmSub R n a.1 * psumSub R n a.2))) = 0 := by
    intro a ha
    obtain ⟨h1, h2⟩ := newtonIdx_mem ha
    rw [map_smul, map_mul, eCoeff_smul]
    have hf : (eLin j (twistSub p κ (esymmSub R n a.1))).fst = 0 := by
      rw [eLin_twistSub_fst hp]
      exact eLin_fst_esymm j h1
    have hg : (eLin j (twistSub p κ (psumSub R n a.2))).fst = 0 := by
      rw [eLin_twistSub_fst hp]
      exact eLin_fst_psum j h2
    rw [eCoeff_mul_eq_zero j _ _ hf hg, mul_zero]
  rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, sub_zero]

/-- **The twisted power sum at weight `ip + 1`.**  Only the term `k = 1` of the binomial
expansion reaches the weight `eCoeff j` reads, with coefficient `κ^i·(i+1)`. -/
theorem eCoeff_twistSub_psumSub_succ {p : ℕ} (hp : 2 ≤ p) (κ : R) (i : ℕ) (j : Fin n)
    (hj : (j : ℕ) = i * p) :
    eCoeff j (twistSub p κ (psumSub R n (i + 1)))
      = κ ^ i * ((i + 1 : ℕ) : R)
          * ((-1 : R) ^ ((j : ℕ) + 1 + 1) * (((j : ℕ) + 1 : ℕ) : R)) := by
  rw [twistSub_psumSub, eCoeff_sum, Finset.sum_eq_single 1]
  · have hidx : 1 + p * (i + 1 - 1) = (j : ℕ) + 1 := by
      rw [Nat.add_sub_cancel, hj]
      ring
    rw [eCoeff_smul, hidx, eCoeff_psumSub_self, Nat.add_sub_cancel, Nat.choose_one_right]
  · intro k hk hk1
    have hkb : k ≤ i + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hpos : 0 < k + p * (i + 1 - k) := by
      rcases Nat.eq_zero_or_pos k with h0 | hk0
      · rw [h0, Nat.zero_add, Nat.sub_zero]
        exact Nat.mul_pos (by omega) (Nat.succ_pos i)
      · exact Nat.lt_of_lt_of_le hk0 (Nat.le_add_right k _)
    have hne : k + p * (i + 1 - k) ≠ (j : ℕ) + 1 := by
      rw [hj]
      intro h
      exact hk1 ((twist_psum_weight hp i k hkb).mp h)
    rw [eCoeff_smul, eCoeff_psumSub_of_ne j hpos hne, mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- Newton applied to `e_{i+1}` and pushed through the twist, before cancelling `i + 1`. -/
theorem eCoeff_twistSub_esymmSub_succ_mul [IsDomain R] [CharZero R] {p : ℕ} (hp : 2 ≤ p)
    (κ : R) (i : ℕ) (j : Fin n) (hj : (j : ℕ) = i * p) :
    (-1 : R) ^ (i + 1 + 1) * eCoeff j (twistSub p κ (esymmSub R n (i + 1)))
      = κ ^ i * ((-1 : R) ^ ((j : ℕ) + 1 + 1) * (((j : ℕ) + 1 : ℕ) : R)) := by
  have h1 := eCoeff_twistSub_psumSub (p := p) (by omega) κ j (i + 1) (Nat.succ_pos i)
  have h2 := eCoeff_twistSub_psumSub_succ hp κ i j hj
  rw [h1] at h2
  have hne : ((i + 1 : ℕ) : R) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero i)
  apply mul_left_cancel₀ hne
  calc ((i + 1 : ℕ) : R)
        * ((-1 : R) ^ (i + 1 + 1) * eCoeff j (twistSub p κ (esymmSub R n (i + 1))))
      = (-1 : R) ^ (i + 1 + 1) * ((i + 1 : ℕ) : R)
          * eCoeff j (twistSub p κ (esymmSub R n (i + 1))) := by ring
    _ = κ ^ i * ((i + 1 : ℕ) : R)
          * ((-1 : R) ^ ((j : ℕ) + 1 + 1) * (((j : ℕ) + 1 : ℕ) : R)) := h2
    _ = ((i + 1 : ℕ) : R)
          * (κ ^ i * ((-1 : R) ^ ((j : ℕ) + 1 + 1) * (((j : ℕ) + 1 : ℕ) : R))) := by ring

/-- **L4a, the value.**  The coefficient of `e_{ip+1}` in `φ_κ(e_{i+1})`, modulo decomposables,
is `(−1)^{i+ip}·κ^i·(ip+1)`.  Mod `p` this is the unit `(−1)^{i(p−1)}·κ^i`. -/
theorem eCoeff_twistSub_esymmSub_succ [IsDomain R] [CharZero R] {p : ℕ} (hp : 2 ≤ p) (κ : R)
    (i : ℕ) (j : Fin n) (hj : (j : ℕ) = i * p) :
    eCoeff j (twistSub p κ (esymmSub R n (i + 1)))
      = (-1 : R) ^ (i + (j : ℕ)) * κ ^ i * (((j : ℕ) + 1 : ℕ) : R) := by
  have hE := eCoeff_twistSub_esymmSub_succ_mul hp κ i j hj
  have hsq : (-1 : R) ^ (i + 1 + 1) * (-1 : R) ^ (i + 1 + 1) = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨i + 1 + 1, rfl⟩
  calc eCoeff j (twistSub p κ (esymmSub R n (i + 1)))
      = ((-1 : R) ^ (i + 1 + 1) * (-1 : R) ^ (i + 1 + 1))
          * eCoeff j (twistSub p κ (esymmSub R n (i + 1))) := by
        rw [hsq, one_mul]
    _ = (-1 : R) ^ (i + 1 + 1)
          * ((-1 : R) ^ (i + 1 + 1) * eCoeff j (twistSub p κ (esymmSub R n (i + 1)))) := by
        ring
    _ = (-1 : R) ^ (i + 1 + 1)
          * (κ ^ i * ((-1 : R) ^ ((j : ℕ) + 1 + 1) * (((j : ℕ) + 1 : ℕ) : R))) := by
        rw [hE]
    _ = ((-1 : R) ^ (i + 1 + 1) * (-1 : R) ^ ((j : ℕ) + 1 + 1))
          * κ ^ i * (((j : ℕ) + 1 : ℕ) : R) := by ring
    _ = (-1 : R) ^ (i + (j : ℕ)) * κ ^ i * (((j : ℕ) + 1 : ℕ) : R) := by
        rw [neg_one_pow_add_two_mul_pow_add_two]

end WuValue

end ParityP

end GroupApproximation.CharClass
