---
rg: 2
id: direct-sum-weil-compressions-have-quadratic-padding
kind: claim
title: Direct sums of even-Weil compressions have a common rank-density upper ledger
distinct_from:
  sl2-half-explicit-strict-flexible-separation: that treats one irreducible Weil block and proves strict separation; this gives the exact many-block defect/padding ledger without asserting strict separation for arbitrary mixtures.
  iwahori-torsion-multiplicity-stratum-reconciliation: that asks for a converse theorem for all near-solutions; this proves the target scaling on the canonical boundary family.
---

Take any finite multiset of primes `p_j=1 mod 4`, with repetitions allowed,
and form the orthogonal direct sum `Phi` of the compressed tuples from
`even-weil-fixed-line-compression`.  Put

```text
D = sum_j (p_j-1)/2,
K = number of summands.                                (DSW1)
```

There are universal constants `C,C'` such that

```text
presentation_defect(Phi) <= C sqrt(K/D),              (DSW2)
```

and adjoining exactly `K` dimensions gives the direct sum `Pi` of the full
even Weil representations with

```text
d_2(Phi,Pi) <= C' sqrt(K/(D+K)).                       (DSW3)
```

Here `d_2` is the generalized flexible Hilbert--Schmidt metric used by
Dogon--Vigdorovich.  Thus `K/D` simultaneously upper-bounds squared
presentation defect and measures the evident repair's missing-dimension
density:

```text
missing_dimension_density = K/(D+K),
presentation_defect(Phi)^2 = O(K/D).                     (DSW4)
```

The displayed estimates do **not** imply
`missing_dimension_density=O(presentation_defect(Phi)^2)`: that direction
requires a matching lower bound on at least one compressed cubic residual.
The rank-one excursion proves support and an upper bound, but the current
calculation does not rule out cancellation in those particular words.

## Proof

On each summand, every fixed relator error has unnormalized Frobenius norm
bounded by one universal constant: all errors factor through the one deleted
line, and polar rounding also costs rank at most one.  Frobenius squares add
over orthogonal direct sums, giving total squared error `O(K)`; normalization
by `D` proves `(DSW2)`.

Restore the deleted fixed line in every summand.  The resulting tuple `Pi` is
an exact representation, its dimension is `D+K`, and the difference from the
zero-padded `Phi` again has unnormalized Frobenius square `O(K)` on every
fixed generator.  Normalizing by `D+K` proves `(DSW3)`.

This is an upper-ledger theorem, not the converse reconciliation theorem or
a sharp defect-to-padding law.  It does show that `K=o(D)` makes the
presentation defect vanish and that restoring the deleted arithmetic lines
costs exactly `K` dimensions.  Proving that every flexible repair must pay a
quantity comparable to the squared observed defect requires the missing
cubic lower bound and a minimal-padding argument.
