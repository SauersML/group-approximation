---
rg: 2
id: bounded-hs-loss-kills-static-heavy-tail-library
kind: claim
title: Bounded unitary loss makes every static heavy-tail challenge library dilutable
distinct_from:
  word-recursion-cannot-amplify-sublinear-summands: that pads one finite recursive packet by a reducing bad summand; this treats a countable static library and shows that unbounded challenge severity cannot compensate for vanishing carrier density.
  summable-power-return-detectors-miss-growing-cycles: that constructs cyclic spectra defeating weighted power moments; this is independent of spectral form and uses only the diameter bound of the unitary Hilbert--Schmidt metric.
  bounded-overlap-syndrome-energy-accounting: that turns a pre-existing positive total syndrome mass into global energy; this proves that a static infinite library cannot assign positive mass to every capacity challenge under bounded overlap.
---

Let `(M,tau)` be a finite tracial matrix algebra and let `P_n` be challenge
carrier projections with bounded overlap

```text
sum_(n=1)^N P_n <= L I                  for every N.   (BHL1)
```

Suppose the `n`th challenge is inspected by `m_n<infinity` unitary
comparisons `U_(n,j),V_(n,j)` localized to `P_n`:

```text
(U_(n,j)-V_(n,j))(1-P_n)=0.                          (BHL2)
```

Then

```text
sum_(j<=m_n)||U_(n,j)-V_(n,j)||_2^2
 <=4 m_n tau(P_n).                                    (BHL3)
```

In particular, when the number of defining tests is one fixed `m`, there
are arbitrarily late challenges whose entire visible energy is arbitrarily
small.  Indeed `(BHL1)` gives

```text
sum_n tau(P_n)<=L,
#{n:tau(P_n)>=epsilon}<=L/epsilon.                    (BHL4)
```

No increase in the local algebraic severity, dimension demand, order,
runtime, or number of mutually distinguishable states inside `P_n` changes
the factor `4 tau(P_n)`: two unitaries are never more than `2` apart.

The conclusion also defeats an arbitrary finite test packet at each depth.
Given any prescribed finite costs `b_n>=1`, there are positive densities

```text
mu_n=2^(-n)/(1+b_n),             sum_n mu_n<1,         (BHL5)
```

for which `b_n mu_n->0`.  Rational approximations to the `mu_n` give actual
finite block multiplicities.  Thus a static convex direct sum can contain
every capacity challenge while making the normalized-HS cost of the
dimension-selected challenge tend to zero, even if `b_n` grows faster than
every computable function.

This is the precise limitation of the heavy-tail metaphor in a bounded
metric:

```text
rarity times severity
```

cannot stay macroscopic by sending severity to infinity, because unitary
severity saturates at `4`.  A viable construction must instead force a
positive total mass of challenges to fire simultaneously, reuse the same
positive-density marked carrier through a contraction, or aggregate
orthogonal scale syndromes into one fixed checksum.

