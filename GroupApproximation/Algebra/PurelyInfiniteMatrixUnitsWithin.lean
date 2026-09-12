import GroupApproximation.Algebra.PurelyInfiniteMatrixUnits
import GroupApproximation.Algebra.PurelyInfiniteMatrixEmbedding

/-!
# Matrix-unit witnesses, exposed raw, and transported inside any nonzero idempotent

`Algebra/PurelyInfiniteMatrixUnits.lean` builds matrix units `E i j`, but only
exposes their products, not the underlying witnesses `s i, t i` with
`t i * s i = 1`, `s i * t i = E i i`.  `Algebra/PurelyInfiniteMatrixEmbedding.lean`'s
`matrixEmbed` needs those witnesses directly, so this module exposes them.

It also transports the whole package inside **any** nonzero idempotent `h`,
with a single comparability application — no splitting, and no need for `h`
to be infinite: comparability embeds a copy of the *global* package (all `n`
copies of `1` at once, already built) inside `h`, and the transported
witnesses satisfy exactly the same two relations as the originals.

## The transport, in one paragraph

Comparability gives `p, q` with `q * p = P := ∑ i, s i * t i` (the sum of the
global copies) and `p * q ≤ h`.  Setting `s' i := p * s i`, `t' i := t i * q`,
one checks `t i * P = t i` and `P * s i = s i` (each `s i, t i` is already
`P`-fixed, since `P` restricted to the `i`-th copy is `s i * t i` itself), so

    `t' i * s' i = t i * (q * p) * s i = t i * P * s i = t i * s i = 1`,
    `t' i * s' j = t i * P * s j = t i * s j = 0` (`i ≠ j`),

exactly the same two relations, with no reference to `P` or `h` surviving.
-/

namespace GroupApproximation
namespace MFQuotientUnits

variable {R : Type*} [Ring R]

/-- **The raw matrix-unit witnesses.**  `t i * s i = 1` and `t i * s j = 0`
(`i ≠ j`); the diagonal idempotents `s i * t i` are pairwise orthogonal and
each equivalent to `1`. -/
theorem exists_matrixUnitWitnesses (hR : IsPurelyInfiniteSimpleRing R) (n : ℕ) :
    ∃ s t : Fin n → R, (∀ i, t i * s i = 1) ∧
      ∀ i j : Fin n, i ≠ j → t i * s j = 0 := by
  obtain ⟨r, hridem, hrortho, hrequiv⟩ := exists_orthogonal_unit_family hR n
  have hchoice : ∀ i : Fin n, ∃ s t : R, t * s = 1 ∧ s * t = r i ∧
      (1 : R) * s = s ∧ s * 1 = s ∧ (1 : R) * t = t ∧ t * 1 = t := fun i =>
    exists_normalized_isometry IsIdempotentElem.one (hridem i) (one_mul (r i))
      (mul_one (r i)) (hrequiv i).symm
  choose s t hts hst hes hse het hte using hchoice
  have hrs : ∀ k, r k * s k = s k := fun k => by
    calc r k * s k = (s k * t k) * s k := by rw [hst k]
      _ = s k * (t k * s k) := by noncomm_ring
      _ = s k * 1 := by rw [hts k]
      _ = s k := hse k
  have htr : ∀ j, t j * r j = t j := fun j => by
    calc t j * r j = t j * (s j * t j) := by rw [hst j]
      _ = (t j * s j) * t j := by noncomm_ring
      _ = 1 * t j := by rw [hts j]
      _ = t j := het j
  refine ⟨s, t, hts, fun i j hij => ?_⟩
  have h1 : r i * s j = 0 := by
    calc r i * s j = r i * (r j * s j) := by rw [hrs j]
      _ = (r i * r j) * s j := by noncomm_ring
      _ = 0 * s j := by rw [hrortho i j hij]
      _ = 0 := zero_mul _
  calc t i * s j = (t i * r i) * s j := by rw [htr i]
    _ = t i * (r i * s j) := by noncomm_ring
    _ = t i * 0 := by rw [h1]
    _ = 0 := mul_zero _

/-- **Matrix-unit witnesses landing inside a prescribed nonzero idempotent.**
Same two relations as `exists_matrixUnitWitnesses`, with the diagonal
idempotents `s i * t i` all below `h`.  No hypothesis on `h` beyond
nonvanishing: comparability embeds the whole `n`-fold package at once. -/
theorem exists_matrixUnitWitnesses_within (hR : IsPurelyInfiniteSimpleRing R)
    {h : R} (hh : IsIdempotentElem h) (hhne : h ≠ 0) (n : ℕ) :
    ∃ s t : Fin n → R, (∀ i, t i * s i = 1) ∧
      (∀ i j : Fin n, i ≠ j → t i * s j = 0) ∧
        ∀ i, IdempotentLE (s i * t i) h := by
  obtain ⟨s, t, hts, hcross⟩ := exists_matrixUnitWitnesses hR n
  set P : R := ∑ i, s i * t i with hPdef
  have hPidem : IsIdempotentElem P := isIdempotentElem_matrixWitnessSum hts hcross
  have htP : ∀ i, t i * P = t i := fun i => by
    have h1 : t i * P = ∑ k, t i * (s k * t k) := by
      rw [hPdef, Finset.mul_sum]
    rw [h1, Finset.sum_eq_single i (fun k _ hki => by
        have h2 : t i * (s k * t k) = (t i * s k) * t k := by noncomm_ring
        rw [h2, hcross i k hki.symm, zero_mul])
      (fun hcon => absurd (Finset.mem_univ i) hcon)]
    have h2 : t i * (s i * t i) = (t i * s i) * t i := by noncomm_ring
    rw [h2, hts i, one_mul]
  have hPs : ∀ i, P * s i = s i := fun i => by
    have h1 : P * s i = ∑ k, (s k * t k) * s i := by
      rw [hPdef, Finset.sum_mul]
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
  refine ⟨fun i => p * s i, fun i => t i * q, fun i => ?_, fun i j hij => ?_, fun i => ?_⟩
  · calc t i * q * (p * s i) = t i * (q * p) * s i := by noncomm_ring
      _ = t i * P * s i := by rw [← hPqp]
      _ = (t i * P) * s i := by noncomm_ring
      _ = t i * s i := by rw [htP i]
      _ = 1 := hts i
  · calc t i * q * (p * s j) = t i * (q * p) * s j := by noncomm_ring
      _ = t i * P * s j := by rw [← hPqp]
      _ = (t i * P) * s j := by noncomm_ring
      _ = t i * s j := by rw [htP i]
      _ = 0 := hcross i j hij
  · have heq : p * s i * (t i * q) = p * s i * t i * q := by noncomm_ring
    rw [heq]
    have hriQ : IdempotentLE (p * s i * t i * q) Q := by
      constructor
      · show Q * (p * s i * t i * q) = p * s i * t i * q
        have h1 : Q * (p * s i * t i * q) = (Q * p) * s i * t i * q := by
          noncomm_ring
        have h2 : Q * p = p * (q * p) := by rw [hQpq]; noncomm_ring
        rw [h1, h2]
        have h3 : p * (q * p) * s i * t i * q = p * (q * p * s i) * t i * q := by
          noncomm_ring
        rw [h3, ← hPqp, hPs i]
      · show p * s i * t i * q * Q = p * s i * t i * q
        have h1 : p * s i * t i * q * Q = p * s i * t i * (q * Q) := by
          noncomm_ring
        have h2 : q * Q = (q * p) * q := by rw [hQpq]; noncomm_ring
        rw [h1, h2, ← hPqp]
        have h3 : p * s i * t i * (P * q) = p * s i * (t i * P) * q := by
          noncomm_ring
        rw [h3, htP i]
    exact hriQ.trans hQle

end MFQuotientUnits
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.MFQuotientUnits.exists_matrixUnitWitnesses
#audit_axioms GroupApproximation.MFQuotientUnits.exists_matrixUnitWitnesses_within
