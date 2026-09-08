import GroupApproximation.Algebra.PurelyInfiniteMatrixUnitsWithin

/-!
# Matrix-unit witnesses inside a nonzero idempotent, individually absorbed

`exists_matrixUnitWitnesses_within` transports matrix-unit witnesses inside a
prescribed nonzero idempotent `h`, but only guarantees the *product* `s i * t i`
is below `h`.  Combining such a family with a *separately built* diagonal
block (as `AGPStepOne` does with `r_1 = 1 - e + f`, built by hand) needs more:
the individual witnesses `s i, t i` must themselves be absorbed by `h`, so
that cross terms against anything supported off `h` vanish for a structural
reason rather than needing to unpick the specific construction of the other
block.

This module reruns the transport with normalised comparability witnesses.

## The normalisation

Comparability gives `Q ≤ h` and `Q ~ P` via *some* `p, q` with `Q = p * q`,
`P = q * p`.  Two general facts about any equivalent pair —
`Q * p = p * P` and `q * Q = P * q`, both immediate from `Q = p*q`, `P = q*p`
by re-associating — let the witnesses be re-sandwiched by `Q` and `P`
themselves:

    `p' := Q * p * P`,  `q' := P * q * Q`.

These still satisfy `Q = p' * q'` and `P = q' * p'` (the same computation, now
idempotent on both sides), and additionally `h * p' = p'`, `q' * h = q'`
outright, since `h * Q = Q = Q * h` puts `h` in front of (resp. behind) the
`Q` that is already there.
-/

namespace GroupApproximation
namespace MFQuotientUnits

variable {R : Type*} [Ring R]

/-- **Matrix-unit witnesses inside a prescribed nonzero idempotent, with the
individual witnesses absorbed by it.** -/
theorem exists_matrixUnitWitnesses_within' (hR : IsPurelyInfiniteSimpleRing R)
    {h : R} (hh : IsIdempotentElem h) (hhne : h ≠ 0) (n : ℕ) :
    ∃ s t : Fin n → R, (∀ i, t i * s i = 1) ∧
      (∀ i j : Fin n, i ≠ j → t i * s j = 0) ∧
        (∀ i, IdempotentLE (s i * t i) h) ∧
          (∀ i, h * s i = s i) ∧ ∀ i, t i * h = t i := by
  obtain ⟨s, t, hts, hcross⟩ := exists_matrixUnitWitnesses hR n
  set P : R := ∑ i, s i * t i with hPdef
  have hPidem : IsIdempotentElem P := isIdempotentElem_matrixWitnessSum hts hcross
  have htP : ∀ i, t i * P = t i := fun i => by
    have h1 : t i * P = ∑ k, t i * (s k * t k) := by rw [hPdef, Finset.mul_sum]
    rw [h1, Finset.sum_eq_single i (fun k _ hki => by
        have h2 : t i * (s k * t k) = (t i * s k) * t k := by noncomm_ring
        rw [h2, hcross i k hki.symm, zero_mul])
      (fun hcon => absurd (Finset.mem_univ i) hcon)]
    have h2 : t i * (s i * t i) = (t i * s i) * t i := by noncomm_ring
    rw [h2, hts i, one_mul]
  have hPs : ∀ i, P * s i = s i := fun i => by
    have h1 : P * s i = ∑ k, (s k * t k) * s i := by rw [hPdef, Finset.sum_mul]
    rw [h1, Finset.sum_eq_single i (fun k _ hki => by
        have h2 : (s k * t k) * s i = s k * (t k * s i) := by noncomm_ring
        rw [h2, hcross k i hki, mul_zero])
      (fun hcon => absurd (Finset.mem_univ i) hcon)]
    have h2 : (s i * t i) * s i = s i * (t i * s i) := by noncomm_ring
    rw [h2, hts i, mul_one]
  obtain ⟨Q, hQidem, hQle, hQequiv⟩ :=
    exists_idempotentLE_equivalent
      (fun a ha => exists_sandwich_of_isPurelyInfiniteSimpleRing hR ha) hh hPidem hhne
  obtain ⟨p, q, hQpq, hPqp⟩ := hQequiv
  -- General facts about any equivalent pair.
  have hQpP : Q * p = p * P := by
    calc Q * p = (p * q) * p := by rw [hQpq]
      _ = p * (q * p) := by noncomm_ring
      _ = p * P := by rw [hPqp]
  have hqQP : q * Q = P * q := by
    calc q * Q = q * (p * q) := by rw [hQpq]
      _ = (q * p) * q := by noncomm_ring
      _ = P * q := by rw [hPqp]
  set p' : R := Q * p * P with hp'def
  set q' : R := P * q * Q with hq'def
  have hp'q' : Q = p' * q' := by
    have e1 : p' * q' = Q * p * (P * P) * q * Q := by rw [hp'def, hq'def]; noncomm_ring
    rw [e1, hPidem]
    have e2 : Q * p * P * q * Q = Q * (p * P) * q * Q := by noncomm_ring
    rw [e2, ← hQpP]
    have e3 : Q * (Q * p) * q * Q = (Q * Q) * p * q * Q := by noncomm_ring
    rw [e3, hQidem]
    have e4 : Q * p * q * Q = Q * (p * q) * Q := by noncomm_ring
    rw [e4, ← hQpq]
    rw [hQidem, hQidem]
  have hq'p' : P = q' * p' := by
    have e1 : q' * p' = P * q * (Q * Q) * p * P := by rw [hp'def, hq'def]; noncomm_ring
    rw [e1, hQidem]
    have e2 : P * q * Q * p * P = P * (q * Q) * p * P := by noncomm_ring
    rw [e2, hqQP]
    have e3 : P * (P * q) * p * P = (P * P) * q * p * P := by noncomm_ring
    rw [e3, hPidem]
    have e4 : P * q * p * P = P * (q * p) * P := by noncomm_ring
    rw [e4, ← hPqp]
    rw [hPidem, hPidem]
  have hhp' : h * p' = p' := by
    have h1 : h * p' = (h * Q) * p * P := by rw [hp'def]; noncomm_ring
    rw [h1, hQle.1]
  have hq'h : q' * h = q' := by
    have h1 : q' * h = P * q * (Q * h) := by rw [hq'def]; noncomm_ring
    rw [h1, hQle.2]
  refine ⟨fun i => p' * s i, fun i => t i * q', fun i => ?_, fun i j hij => ?_,
    fun i => ?_, fun i => ?_, fun i => ?_⟩
  · calc t i * q' * (p' * s i) = t i * (q' * p') * s i := by noncomm_ring
      _ = t i * P * s i := by rw [← hq'p']
      _ = (t i * P) * s i := by noncomm_ring
      _ = t i * s i := by rw [htP i]
      _ = 1 := hts i
  · calc t i * q' * (p' * s j) = t i * (q' * p') * s j := by noncomm_ring
      _ = t i * P * s j := by rw [← hq'p']
      _ = (t i * P) * s j := by noncomm_ring
      _ = t i * s j := by rw [htP i]
      _ = 0 := hcross i j hij
  · have heq : p' * s i * (t i * q') = p' * s i * t i * q' := by noncomm_ring
    rw [heq]
    have hriQ : IdempotentLE (p' * s i * t i * q') Q := by
      constructor
      · show Q * (p' * s i * t i * q') = p' * s i * t i * q'
        have h1 : Q * (p' * s i * t i * q') = (Q * p') * s i * t i * q' := by
          noncomm_ring
        have h2 : Q * p' = p' := by
          have h3 : Q * p' = (Q * Q) * p * P := by rw [hp'def]; noncomm_ring
          rw [h3, hQidem, ← hp'def]
        rw [h1, h2]
      · show p' * s i * t i * q' * Q = p' * s i * t i * q'
        have h1 : p' * s i * t i * q' * Q = p' * s i * t i * (q' * Q) := by
          noncomm_ring
        have h2 : q' * Q = q' := by
          have h3 : q' * Q = P * q * (Q * Q) := by rw [hq'def]; noncomm_ring
          rw [h3, hQidem, ← hq'def]
        rw [h1, h2]
    exact hriQ.trans hQle
  · show h * (p' * s i) = p' * s i
    have h1 : h * (p' * s i) = (h * p') * s i := by noncomm_ring
    rw [h1, hhp']
  · show t i * q' * h = t i * q'
    have h1 : t i * q' * h = t i * (q' * h) := by noncomm_ring
    rw [h1, hq'h]

end MFQuotientUnits
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.MFQuotientUnits.exists_matrixUnitWitnesses_within'
