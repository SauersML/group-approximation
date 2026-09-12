import GroupApproximation.CharClass.OddPDescentPairing

/-!
# The cyclic domino operator, and where the factorial comes from

This file holds the closed form that makes the degree-one constant computable generic in
`p`.  Let

```text
    ρ := Σ_{a ∈ ℤ/p} ξ_a ∧ ξ_{a+1}          eR := ρ ∧ (−)
```

the sum over the `p` cyclically adjacent pairs of slots.  Three facts:

1. **`eR` commutes with every `eWedge b` and with `eT`.**  `ρ` has even degree, so moving a
   letter past it costs `(−1)² = 1`; and `ρ` is manifestly invariant under the shift, which
   permutes its summands.
2. **`eN (ξ_0 ∧ ξ_1 ∧ y) = ρ ∧ y` for `T`-invariant `y`.**  `T^k(ξ_0 ∧ ξ_1 ∧ y) =
   ξ_{−k} ∧ ξ_{1−k} ∧ y`, and summing over `k` sweeps out every cyclically adjacent pair.
   This single identity is the whole content of one round of the descent.
3. **`⟨ρ^k, e_{\{i,…,i+2k−1\}}⟩ = k!`** for any interval of `2k` slots inside
   `{1, …, p−1}`.  This is where the factorial is produced, and it is produced by the
   derivation identity `∂_i ρ^k = k·ρ^{k−1}(ξ_{i+1} − ξ_{i−1})`, **not** by counting domino
   tilings: the `k` in front is the `k` of the product rule, the `ξ_{i−1}` term misses the
   interval, and `ξ_{i+1}` peels the next letter, leaving the same statement with `i ↦ i+2`
   and `k ↦ k−1`.

VERIFIED (model): every identity of this file, on every basis element, at `p = 3, 5, 7`;
and `ξ_0 ∧ ρ^k` is the `k`-th term of the dual descent at `p = 3, 5, 7, 11`, with
`ξ_0 ∧ ρ^{(p−1)/2} = ((p−1)/2)!·ω` on the nose over `ℤ`.
-/

namespace GroupApproximation.CharClass

-- The `ℕ → Fin p` coercion is a SCOPED instance (`Fin.NatCast`), deliberately not
-- global; without this `open` the ascription `(n : Fin p)` reports a bare type
-- mismatch with no mention of a missing instance.
open Fin.NatCast

variable {p : ℕ} [NeZero p] (K : Type) [CommRing K]

/-! ## 1. Pointwise forms of the two Clifford relations -/

omit [NeZero p] in
theorem eWedge_anticomm_apply (a b : Fin p) (y : EMod K p) :
    eWedge K a (eWedge K b y) = -eWedge K b (eWedge K a y) := by
  have h := congrArg (fun f : EMod K p →ₗ[K] EMod K p => f y) (eWedge_anticomm K a b)
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply] at h
  exact eq_neg_of_add_eq_zero_right h

omit [NeZero p] in
theorem ePart_eWedge_apply (i a : Fin p) (y : EMod K p) :
    ePart K i (eWedge K a y)
      = (if i = a then y else 0) - eWedge K a (ePart K i y) := by
  by_cases h : i = a
  · subst h
    have hh := congrArg (fun f : EMod K p →ₗ[K] EMod K p => f y) (ePart_eWedge_self K i)
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] at hh
    rw [if_pos rfl]
    exact eq_sub_of_add_eq hh
  · have hh := congrArg (fun f : EMod K p →ₗ[K] EMod K p => f y) (ePart_eWedge_of_ne K i a h)
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply] at hh
    rw [if_neg h]
    exact eq_sub_of_add_eq hh

/-! ## 2. The cyclic domino operator -/

/-- **`eR = ρ ∧ (−)`**, the cyclic domino operator. -/
noncomputable def eR : EMod K p →ₗ[K] EMod K p :=
  ∑ a : Fin p, (eWedge K a).comp (eWedge K (a + 1))

theorem eR_apply (x : EMod K p) :
    eR K x = ∑ a : Fin p, eWedge K a (eWedge K (a + 1) x) := by
  rw [eR, LinearMap.sum_apply]
  rfl

/-- `ρ` has even degree, so wedging with a letter commutes with it. -/
theorem eWedge_eR_apply (b : Fin p) (x : EMod K p) :
    eWedge K b (eR K x) = eR K (eWedge K b x) := by
  rw [eR_apply, map_sum, eR_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [eWedge_anticomm_apply K b a, eWedge_anticomm_apply K b (a + 1), map_neg, neg_neg]

theorem eWedge_eR_pow_apply (b : Fin p) (n : ℕ) (x : EMod K p) :
    eWedge K b ((eR K ^ n) x) = (eR K ^ n) (eWedge K b x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, eWedge_eR_apply, ih]

/-- **The derivation identity.**  `∂_i` is an odd derivation, `ρ` is a sum of products of
two letters, and only the two dominoes that touch slot `i` survive. -/
theorem ePart_eR_apply (i : Fin p) (x : EMod K p) :
    ePart K i (eR K x)
      = eR K (ePart K i x) + eWedge K (i + 1) x - eWedge K (i - 1) x := by
  classical
  have hterm : ∀ a : Fin p, ePart K i (eWedge K a (eWedge K (a + 1) x))
      = (if i = a then eWedge K (a + 1) x else 0)
        - (if i - 1 = a then eWedge K a x else 0)
        + eWedge K a (eWedge K (a + 1) (ePart K i x)) := by
    intro a
    -- rewriting the CONDITION of an `ite` with a `Prop` equality makes the motive
    -- ill-typed (the `Decidable` instance travels with it); rewrite the whole term instead
    have hite : (if i = a + 1 then eWedge K a x else 0)
        = (if i - 1 = a then eWedge K a x else 0) := by
      by_cases hc : i = a + 1
      · rw [if_pos hc, if_pos (by rw [hc]; abel)]
      · rw [if_neg hc, if_neg (fun hcon => hc (by rw [← hcon]; abel))]
    rw [ePart_eWedge_apply K i a, ePart_eWedge_apply K i (a + 1), map_sub,
      apply_ite (eWedge K a), map_zero, hite]
    abel
  rw [eR_apply, map_sum, Finset.sum_congr rfl fun a _ => hterm a,
    Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq Finset.univ i (fun a => eWedge K (a + 1) x),
    Finset.sum_ite_eq Finset.univ (i - 1) (fun a => eWedge K a x),
    if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _), ← eR_apply]
  have hsub : i - 1 + 1 = i := by abel
  rw [hsub]
  abel

/-- **The factorial appears here.**  `∂_i ρ^{n+1} = (n+1)·ρ^n(ξ_{i+1} − ξ_{i−1})` whenever
`∂_i` kills the input: the product rule contributes one copy per factor. -/
theorem ePart_eR_pow_apply (i : Fin p) (n : ℕ) (x : EMod K p) (hx : ePart K i x = 0) :
    ePart K i ((eR K ^ (n + 1)) x)
      = (n + 1) • ((eR K ^ n) (eWedge K (i + 1) x - eWedge K (i - 1) x)) := by
  induction n with
  | zero =>
      rw [pow_one, ePart_eR_apply K i x, hx, map_zero, zero_add, pow_zero]
      simp
  | succ n ih =>
      rw [pow_succ' (eR K) (n + 1), Module.End.mul_apply, ePart_eR_apply K i, ih,
        map_nsmul, eWedge_eR_pow_apply K (i + 1) (n + 1) x,
        eWedge_eR_pow_apply K (i - 1) (n + 1) x, add_sub_assoc, ← map_sub,
        pow_succ' (eR K) n, Module.End.mul_apply]
      abel

/-! ## 3. Coefficient extraction -/

omit [NeZero p] in
theorem eWedge_coeff_of_true (a : Fin p) (x : EMod K p) (w' : EWord p) (h : w' a = true) :
    (eWedge K a x) w' = ((-1 : K) ^ ePre w' a) * x (Function.update w' a false) := by
  classical
  rw [show (eWedge K a x) w' = ∑ w : EWord p, x w * (eWedgeGen K a w) w' from
    eLC_coeff K (eWedgeGen K a) x w']
  rw [Finset.sum_eq_single (Function.update w' a false)]
  · rw [eWedgeGen_of_false K (by simp), ePre_update_of_le w' a false a le_rfl,
      Function.update_idem, Function.update_eq_self_iff.2 h.symm, Finsupp.smul_apply,
      Finsupp.single_eq_same, smul_eq_mul, mul_one, mul_comm]
  · intro w _ hw
    by_cases hwa : w a = true
    · rw [eWedgeGen_of_true K hwa, Finsupp.coe_zero, Pi.zero_apply, mul_zero]
    · have hwf : w a = false := Bool.eq_false_of_not_eq_true hwa
      rw [eWedgeGen_of_false K hwf, Finsupp.smul_apply, Finsupp.single_apply, if_neg,
        smul_zero, mul_zero]
      intro hcon
      apply hw
      rw [← hcon, Function.update_idem, eq_update_self_iff]
      exact hwf
  · intro h'
    exact absurd (Finset.mem_univ _) h'

omit [NeZero p] in
theorem eWedge_coeff_of_false (a : Fin p) (x : EMod K p) (w' : EWord p) (h : w' a = false) :
    (eWedge K a x) w' = 0 := by
  classical
  rw [show (eWedge K a x) w' = ∑ w : EWord p, x w * (eWedgeGen K a w) w' from
    eLC_coeff K (eWedgeGen K a) x w']
  refine Finset.sum_eq_zero fun w _ => ?_
  by_cases hwa : w a = true
  · rw [eWedgeGen_of_true K hwa, Finsupp.coe_zero, Pi.zero_apply, mul_zero]
  · have hwf : w a = false := Bool.eq_false_of_not_eq_true hwa
    rw [eWedgeGen_of_false K hwf, Finsupp.smul_apply, Finsupp.single_apply, if_neg,
      smul_zero, mul_zero]
    intro hcon
    have hval := congrFun hcon a
    rw [Function.update_self] at hval
    rw [← hval] at h
    exact absurd h (by simp)

omit [NeZero p] in
theorem ePart_coeff_of_false (a : Fin p) (x : EMod K p) (w' : EWord p) (h : w' a = false) :
    (ePart K a x) w' = ((-1 : K) ^ ePre w' a) * x (Function.update w' a true) := by
  classical
  rw [show (ePart K a x) w' = ∑ w : EWord p, x w * (ePartGen K a w) w' from
    eLC_coeff K (ePartGen K a) x w']
  rw [Finset.sum_eq_single (Function.update w' a true)]
  · rw [ePartGen_of_true K (by simp), ePre_update_of_le w' a true a le_rfl,
      Function.update_idem, Function.update_eq_self_iff.2 h.symm, Finsupp.smul_apply,
      Finsupp.single_eq_same, smul_eq_mul, mul_one, mul_comm]
  · intro w _ hw
    by_cases hwa : w a = true
    · rw [ePartGen_of_true K hwa, Finsupp.smul_apply, Finsupp.single_apply, if_neg,
        smul_zero, mul_zero]
      intro hcon
      apply hw
      rw [← hcon, Function.update_idem, eq_update_self_iff]
      exact hwa
    · rw [ePartGen_of_false K (Bool.eq_false_of_not_eq_true hwa), Finsupp.coe_zero,
        Pi.zero_apply, mul_zero]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

/-! ## 4. Interval words -/

/-- The all-`f` word. -/
def eBotWord (p : ℕ) : EWord p := fun _ => false

/-- The all-`f` basis element, the bottom of `E^{⊗p}`. -/
noncomputable def eBot : EMod K p := Finsupp.single (eBotWord p) (1 : K)

/-- The word whose `g`s occupy exactly the slots `i, i+1, …, i+len−1`. -/
def eIntervalWord (i len : ℕ) : EWord p := fun j => decide (i ≤ (j : ℕ) ∧ (j : ℕ) < i + len)

omit [NeZero p] in
theorem eIntervalWord_apply (i len : ℕ) (j : Fin p) :
    (eIntervalWord (p := p) i len) j = true ↔ (i ≤ (j : ℕ) ∧ (j : ℕ) < i + len) := by
  simp [eIntervalWord]

omit [NeZero p] in
theorem eIntervalWord_zero (i : ℕ) : eIntervalWord (p := p) i 0 = eBotWord p := by
  funext j
  simp [eIntervalWord, eBotWord]

omit [NeZero p] in
/-- Below the interval the prefix is empty. -/
theorem ePre_eIntervalWord (i len : ℕ) (a : Fin p) (ha : (a : ℕ) ≤ i) :
    ePre (eIntervalWord (p := p) i len) a = 0 := by
  refine Finset.sum_eq_zero fun l hl => ?_
  have hlt : (l : ℕ) < (a : ℕ) := by
    have := Finset.mem_Iio.mp hl
    exact this
  have : (eIntervalWord (p := p) i len) l = false := by
    simp only [eIntervalWord, decide_eq_false_iff_not, not_and, not_lt]
    intro hcon
    omega
  rw [this, eLetterDeg_false]

omit [NeZero p] in
theorem eIntervalWord_update_head (i len : ℕ) (a : Fin p) (ha : (a : ℕ) = i) :
    Function.update (eIntervalWord (p := p) i (len + 1)) a false
      = eIntervalWord (p := p) (i + 1) len := by
  funext j
  by_cases hj : j = a
  · subst hj
    rw [Function.update_self]
    symm
    simp only [eIntervalWord, decide_eq_false_iff_not, not_and, not_lt, ha]
    omega
  · rw [Function.update_of_ne hj]
    have hjv : (j : ℕ) ≠ i := by
      intro hcon
      exact hj (Fin.ext (by omega))
    -- `decide_eq_decide` avoids a `congr` on `decide`, which would leave an `HEq` goal
    -- between the two `Decidable` instances
    simp only [eIntervalWord, decide_eq_decide]
    omega

/-! ## 5. The value of `ρ^k` on an interval -/

/-- **`⟨ρ^k, e_{\{i,…,i+2k−1\}}⟩ = k!`**, for any interval of `2k` slots inside
`{1, …, p−1}`.  The proof peels two slots at a time: `∂_i` turns `ρ^k` into
`k·ρ^{k−1}(ξ_{i+1} − ξ_{i−1})`, the `ξ_{i−1}` term is supported off the interval, and
`ξ_{i+1}` supplies the next letter. -/
theorem eR_pow_interval (hp : 1 < p) :
    ∀ (k i : ℕ), 1 ≤ i → i + 2 * k ≤ p →
      ((eR K ^ k) (eBot K)) (eIntervalWord i (2 * k)) = (Nat.factorial k : K) := by
  intro k
  induction k with
  | zero =>
      intro i _ _
      rw [pow_zero, Module.End.one_apply, Nat.mul_zero, eIntervalWord_zero, eBot,
        Finsupp.single_eq_same, Nat.factorial_zero, Nat.cast_one]
  | succ k ih =>
      intro i hi hle
      have hip : i < p := by omega
      obtain ⟨a, hav⟩ : ∃ a : Fin p, (a : ℕ) = i := ⟨⟨i, hip⟩, rfl⟩
      have hlen : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
      -- the interval word and its head
      have hI' : Function.update (eIntervalWord (p := p) i (2 * (k + 1))) a false
          = eIntervalWord (p := p) (i + 1) (2 * k + 1) := by
        rw [hlen]
        exact eIntervalWord_update_head i (2 * k + 1) a hav
      have hIa : (eIntervalWord (p := p) i (2 * (k + 1))) a = true := by
        rw [eIntervalWord_apply]
        omega
      have hI'a : (eIntervalWord (p := p) (i + 1) (2 * k + 1)) a = false := by
        simp only [eIntervalWord, decide_eq_false_iff_not, not_and, not_lt, hav]
        omega
      have hpre' : ePre (eIntervalWord (p := p) (i + 1) (2 * k + 1)) a = 0 :=
        ePre_eIntervalWord (i + 1) (2 * k + 1) a (by omega)
      -- step 1: the coefficient at the interval is a coefficient of `∂_a`
      have hstep1 : ∀ x : EMod K p,
          (ePart K a x) (eIntervalWord (p := p) (i + 1) (2 * k + 1))
            = x (eIntervalWord (p := p) i (2 * (k + 1))) := by
        intro x
        rw [ePart_coeff_of_false K a x _ hI'a, hpre', pow_zero, one_mul, ← hI',
          Function.update_idem, Function.update_eq_self_iff.2 hIa.symm]
      -- step 2: the derivation identity
      have hbot : ePart K a (eBot K) = 0 := by
        rw [eBot, ePart_single, ePartGen_of_false K (by rfl)]
      have hstep2 := ePart_eR_pow_apply K a k (eBot K) hbot
      -- step 3: evaluate the two wedge terms
      have hsucc : (a + 1 : Fin p) = (⟨i + 1, by omega⟩ : Fin p) :=
        Fin.ext (by rw [eSucc_val hp a (by omega), hav])
      have hpred : (a - 1 : Fin p) = (⟨i - 1, by omega⟩ : Fin p) :=
        Fin.ext (by rw [ePred_val hp a (by rw [hav]; omega), hav])
      have hsuccv : ((a + 1 : Fin p) : ℕ) = i + 1 := by rw [hsucc]
      have hpredv : ((a - 1 : Fin p) : ℕ) = i - 1 := by rw [hpred]
      have hplus : ((eR K ^ k) (eWedge K (a + 1) (eBot K)))
            (eIntervalWord (p := p) (i + 1) (2 * k + 1))
          = (Nat.factorial k : K) := by
        have hval : (eIntervalWord (p := p) (i + 1) (2 * k + 1)) (a + 1) = true := by
          rw [eIntervalWord_apply, hsuccv]
          omega
        have hpre2 : ePre (eIntervalWord (p := p) (i + 1) (2 * k + 1)) (a + 1) = 0 :=
          ePre_eIntervalWord (i + 1) (2 * k + 1) (a + 1) (by omega)
        have hupd2 : Function.update (eIntervalWord (p := p) (i + 1) (2 * k + 1)) (a + 1) false
            = eIntervalWord (p := p) (i + 2) (2 * k) :=
          eIntervalWord_update_head (i + 1) (2 * k) (a + 1) hsuccv
        rw [← eWedge_eR_pow_apply K (a + 1) k (eBot K),
          eWedge_coeff_of_true K (a + 1) _ _ hval, hpre2, pow_zero, one_mul, hupd2]
        exact ih (i + 2) (by omega) (by omega)
      have hminus : ((eR K ^ k) (eWedge K (a - 1) (eBot K)))
            (eIntervalWord (p := p) (i + 1) (2 * k + 1)) = 0 := by
        have hval : (eIntervalWord (p := p) (i + 1) (2 * k + 1)) (a - 1) = false := by
          simp only [eIntervalWord, decide_eq_false_iff_not, not_and, not_lt, hpredv]
          intro _
          omega
        rw [← eWedge_eR_pow_apply K (a - 1) k (eBot K)]
        exact eWedge_coeff_of_false K (a - 1) _ _ hval
      -- assemble
      rw [← hstep1, hstep2]
      simp only [Finsupp.smul_apply, nsmul_eq_mul, Finsupp.coe_smul, Pi.smul_apply,
        map_sub, Finsupp.coe_sub, Pi.sub_apply]
      rw [hplus, hminus, sub_zero, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
        Nat.cast_one]

/-! ## 6. One round of the descent, in closed form -/

theorem eT_pow_eWedge (hp : 1 < p) (k : ℕ) (a : Fin p) (y : EMod K p) :
    ((eT K) ^ k) (eWedge K a y) = eWedge K (a - (k : Fin p)) (((eT K) ^ k) y) := by
  induction k generalizing a y with
  | zero => simp
  | succ k ih =>
      have hstep : eT K (eWedge K a y) = eWedge K (a - 1) (eT K y) := by
        have h := congrArg (fun f : EMod K p →ₗ[K] EMod K p => f y)
          (eT_comp_eWedge K hp (a - 1))
        simp only [LinearMap.comp_apply] at h
        rw [show (a - 1 : Fin p) + 1 = a from by abel] at h
        exact h
      have hidx : (a - 1 : Fin p) - (k : Fin p) = a - ((k + 1 : ℕ) : Fin p) := by
        rw [Nat.cast_add, Nat.cast_one]
        abel
      rw [pow_succ, Module.End.mul_apply, hstep, ih, ← Module.End.mul_apply, ← pow_succ,
        hidx]

theorem eT_pow_apply_of_inv (k : ℕ) {y : EMod K p} (hy : eT K y = y) :
    ((eT K) ^ k) y = y := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, hy]

/-- **One round of the descent.**  `N(ξ_0 ∧ ξ_1 ∧ y) = ρ ∧ y` for `T`-invariant `y`: the
shift sweeps the pair `(0,1)` over every cyclically adjacent pair. -/
theorem eN_eWedge_zero_one (hp : 1 < p) {y : EMod K p} (hy : eT K y = y) :
    eN K (eWedge K 0 (eWedge K 1 y)) = eR K y := by
  have hterm : ∀ k : ℕ, ((eT K) ^ k) (eWedge K 0 (eWedge K 1 y))
      = eWedge K (0 - (k : Fin p)) (eWedge K (1 - (k : Fin p)) y) := by
    intro k
    rw [eT_pow_eWedge K hp k 0, eT_pow_eWedge K hp k 1, eT_pow_apply_of_inv K k hy]
  rw [eN, LinearMap.sum_apply, Finset.sum_congr rfl fun k _ => hterm k]
  rw [← Fin.sum_univ_eq_sum_range
    (fun k => eWedge K (0 - ((k : ℕ) : Fin p)) (eWedge K (1 - ((k : ℕ) : Fin p)) y)) p]
  rw [eR_apply]
  refine Fintype.sum_equiv (Equiv.neg (Fin p))
    (fun j : Fin p => eWedge K (0 - (((j : ℕ) : ℕ) : Fin p))
      (eWedge K (1 - (((j : ℕ) : ℕ) : Fin p)) y))
    (fun a : Fin p => eWedge K a (eWedge K (a + 1) y)) ?_
  intro j
  rw [Fin.cast_val_eq_self]
  have hA : (0 : Fin p) - j = -j := by abel
  have hB : (1 : Fin p) - j = -j + 1 := by abel
  rw [hA, hB]
  rfl

/-- The bottom word is fixed by the shift. -/
theorem eT_eBot : eT K (eBot K) = (eBot K : EMod K p) := by
  rw [eBot, eT_single]
  have hrot : eRot (eBotWord p) = eBotWord p := rfl
  have hsgn : eSgn K (eBotWord p) = (1 : K) := by
    rw [eSgn]
    simp [eBotWord, eLetterDeg]
  rw [hrot, hsgn, one_smul]

theorem eT_eR_apply (hp : 1 < p) (x : EMod K p) : eT K (eR K x) = eR K (eT K x) := by
  rw [eR_apply, map_sum, eR_apply]
  refine (Fintype.sum_equiv (Equiv.addRight (1 : Fin p))
    (fun b : Fin p => eWedge K b (eWedge K (b + 1) (eT K x)))
    (fun a : Fin p => eT K (eWedge K a (eWedge K (a + 1) x))) ?_).symm
  intro b
  have h1 := eT_pow_eWedge K hp 1 (b + 1) (eWedge K (b + 1 + 1) x)
  have h2 := eT_pow_eWedge K hp 1 (b + 1 + 1) x
  simp only [pow_one, Nat.cast_one] at h1 h2
  rw [show (b + 1 - 1 : Fin p) = b from by abel] at h1
  rw [show (b + 1 + 1 - 1 : Fin p) = b + 1 from by abel] at h2
  rw [h1, h2]

theorem eT_eR_pow_eBot (hp : 1 < p) (n : ℕ) :
    eT K ((eR K ^ n) (eBot K)) = ((eR K ^ n) (eBot K) : EMod K p) := by
  induction n with
  | zero => simpa using eT_eBot K
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, eT_eR_apply K hp, ih]

end GroupApproximation.CharClass
