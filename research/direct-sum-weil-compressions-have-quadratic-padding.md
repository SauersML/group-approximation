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

The displayed upper estimates by themselves do **not** imply
`missing_dimension_density=O(presentation_defect(Phi)^2)`: that direction
requires a matching lower bound on at least one compressed cubic residual.
The rank-one excursion alone proves support and an upper bound, but does not
rule out cancellation in those particular words.  The next two spectral
inputs supply the needed lower bounds.

There is now a sharp positive estimate for every such prime.  If
`p_j=5 mod 8`,
`even-weil-second-cubic-has-a-rank-six-determinant-gap` gives unnormalized
Frobenius square at least `2/3` for the second cubic.  If `p_j=1 mod 8`,
`deleted-fixed-line-first-cubic-has-explicit-positive-spectrum` gives
unnormalized Frobenius square at least `144/125` for the first cubic.  Since
the energy is the **sum** of the two squared cubic residuals and direct sums
preserve both block diagonal words,

```text
||((X S^2)^3-1)||_F^2+||((X R S)^3-1)||_F^2
  >= (2/3)K.                                          (DSW5)
```

Together with `(DSW2)`, the root-sum-square presentation defect is
`Theta(sqrt(K/D))` for arbitrary heterogeneous sums of the canonical
compressed blocks, and the evident `K`-line arithmetic completion has
genuinely quadratic relative padding.  This is an existence ledger for that
completion; it does not prove that no smaller enlargement can couple
different blocks globally.

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

This is a canonical-family ledger, not the converse reconciliation theorem.
It shows that `K=o(D)` makes the presentation defect vanish, that restoring
the deleted arithmetic lines costs exactly `K` dimensions, and that this
chosen padding is bounded by the observed two-cubic energy.  Proving that
every flexible repair must pay comparable padding, or that arbitrary
cross-packet near-solutions admit this ledger, requires a separate global
multiplicity argument.
