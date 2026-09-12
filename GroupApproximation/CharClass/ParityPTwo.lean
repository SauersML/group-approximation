import GroupApproximation.CharClass.ParityEven
import GroupApproximation.CharClass.ParityPData

/-!
# The `p = 2` instance: `ParityData` is a `ParityPData 2`

`CharClass/ParityPData.lean` states Step D at an arbitrary prime.  This file is the
calibration case demanded by `notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.4: at `p = 2`
the general statement must specialise to the `F₂` one that the verified LIX answer already
uses, and `CharClass/ParityEven.lean` must not be edited to make that true.

So the whole of `ParityData` is turned into a `ParityPData 2` here, field by field, and the
two general conclusions are re-derived in the `F₂` vocabulary:

* `ParityData.toParityPData.b_eq_zero_of_mod` gives `ParityData.b_odd_eq_zero`;
* `ParityData.toParityPData.gamma_rank_eq_zero` gives `ParityData.gamma_top_eq_zero`
  (`n = 2`, so `z = t x` has weight `3` and the rank is `m + 3`).

The dictionary, for the record:

| `ParityPData 2 R H` | `ParityData R H` |
|---|---|
| `z` | `t * x` |
| `PH i` | `SqH (2 * i)` |
| `PR i` | `SqR (2 * i)` |
| `pH_z_mul` | `sqH_tx_mul` |
| `a_eq_zero` (`¬ 2 ∣ q`) | `a_odd` (`Odd q`) |
| `pR_b_succ` | `sq_b (i+1) (2*i)` |
| `c i` (a unit) | `1` — at `p = 2` the normalisation constant `κ` is `1` |
| `wu` (`γ_{2i+1} + decomposables`) | `wu` (`∑_{j ≤ i} γ_{i−j} γ_{i+1+j}`), split at `j = i` |

The only step with any content is the last one: the `j = i` term of the `F₂` diagonal Wu
relation is `γ_0 · γ_{2i+1}`, and `γ_0 = 1` has to be *derived* from `ParityData` (it is not
a field) before that term can be recognised as the distinguished `c_i·γ_{ip+1}` of the
general hypothesis.  Instability at index `0` does it: `Sq^0 (b 0) = b 0` and
`2·0 < 0 + 6`.

## Main results

* `GroupApproximation.CharClass.ParityData.gamma_zero` — `γ_0 = 1`.
* `ParityData.toParityPData` — **the instance**.
* `ParityData.b_odd_eq_zero'`, `ParityData.gamma_top_eq_zero'` — the two `F₂` conclusions,
  obtained from the general theorem rather than from `ParityEven.lean`'s own proof.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation.CharClass

open ParityP

namespace ParityData

variable {R H : Type*} [CommRing R] [CommRing H] (P : ParityData R H)

/-! ### `γ 0 = 1`, which `ParityData` does not state -/

/-- `Sq^0` is the identity on the `H^*(Y)`-component, read through `ι`. -/
theorem iota_sqR_zero (r : R) : P.ι (P.SqR 0 r) = P.ι r := by
  rw [← P.sqH_ι, P.sqH_zero_apply]

/-- The `t x`-component of `γ 0` vanishes: instability at index `0` kills `b 0`, whose
degree is `2·0 − 6 < 0`. -/
theorem iota_b_zero : P.ι (P.b 0) = 0 := by
  rw [← P.iota_sqR_zero (P.b 0), P.sq_b 0 0 (by omega), map_zero]

/-- `γ 0 = 1`. -/
theorem gamma_zero : P.γ 0 = 1 := by
  rw [P.γ_eq 0, P.a_zero, map_one, P.iota_b_zero, mul_zero, add_zero]

/-! ### The instance -/

/-- **`ParityEven.lean`'s hypotheses are the `p = 2` case of `ParityPData`.**  Every field
is a field or a theorem of `ParityData`; nothing in `ParityEven.lean` is changed. -/
def toParityPData : ParityPData 2 R H where
  p_two_le := le_rfl
  ι := P.ι
  z := P.t * P.x
  z_mul_z := P.tx_mul_tx
  z_inj := P.tx_inj
  PH := fun i => P.SqH (2 * i)
  PR := fun i => P.SqR (2 * i)
  pH_ι := fun i r => P.sqH_ι (2 * i) r
  pH_z_mul := fun i r => P.sqH_tx_mul (2 * i) r
  γ := P.γ
  a := P.a
  b := P.b
  γ_eq := P.γ_eq
  a_eq_zero := fun q hq => P.a_odd q (Nat.odd_iff.mpr (by omega))
  pR_b_succ := fun i => P.sq_b (i + 1) (2 * i) (by omega)
  c := fun _ => 1
  c_isUnit := fun _ => isUnit_one
  wu := fun i => by
    show IsDecomposable P.γ (i * 2 + 1)
      (P.SqH (2 * i) (P.γ (i + 1)) - P.ι 1 * P.γ (i * 2 + 1))
    rw [map_one, one_mul]
    have hidx : i * 2 + 1 = i + 1 + i := by omega
    have hsplit : ∑ j ∈ Finset.range (i + 1), P.γ (i - j) * P.γ (i + 1 + j)
        = (∑ j ∈ Finset.range i, P.γ (i - j) * P.γ (i + 1 + j)) + P.γ (i + 1 + i) := by
      rw [Finset.sum_range_succ, Nat.sub_self, P.gamma_zero, one_mul]
    have hdiff : P.SqH (2 * i) (P.γ (i + 1)) - P.γ (i * 2 + 1)
        = ∑ j ∈ Finset.range i, P.γ (i - j) * P.γ (i + 1 + j) := by
      rw [P.wu i, hsplit, hidx]
      ring
    rw [hdiff]
    refine IsDecomposable.sum _ _ ?_
    intro j hj
    have hj' : j < i := Finset.mem_range.mp hj
    have h1 : 1 ≤ i - j := by omega
    have h2 : 1 ≤ i + 1 + j := by omega
    have h3 : i - j + (i + 1 + j) = i * 2 + 1 := by omega
    exact IsDecomposable.pair h1 h2 h3

/-! ### The two `F₂` conclusions, from the general theorem -/

/-- `ParityData.b_odd_eq_zero`, obtained from `ParityPData.b_eq_zero_of_mod` at `p = 2`.
The primed name marks that this is the general theorem specialised, not `ParityEven.lean`'s
own induction. -/
theorem b_odd_eq_zero' {N : ℕ} (hN : Odd N) : P.b N = 0 :=
  P.toParityPData.b_eq_zero_of_mod (Nat.odd_iff.mp hN)

/-- `ParityData.gamma_top_eq_zero`, obtained from `ParityPData.gamma_rank_eq_zero` at
`p = 2`, `n = 2`: the weight of `z = t x` is `3 = n + 1`, so the rank index is `m + 3`. -/
theorem gamma_top_eq_zero' {m : ℕ} (hm : Even m) (ha : ∀ q : ℕ, m < q → P.a q = 0) :
    P.γ (2 + 1 + m) = 0 := by
  obtain ⟨k, hk⟩ := hm
  have hn : (2 : ℕ) ∣ 2 := dvd_refl 2
  have hmm : (2 : ℕ) ∣ m := ⟨k, by omega⟩
  have hq : P.a (2 + 1 + m) = 0 := ha (2 + 1 + m) (by omega)
  exact P.toParityPData.gamma_rank_eq_zero hn hmm hq

end ParityData

end GroupApproximation.CharClass
