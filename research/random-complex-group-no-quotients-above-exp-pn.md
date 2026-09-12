---
rg: 2
id: random-complex-group-no-quotients-above-exp-pn
kind: claim
title: Mid-range Linial--Meshulam groups have no nontrivial finite quotient of order above exp(n^eta/8)
distinct_from:
  random-complex-group-no-large-finite-quotients: that is the premise with the polynomial threshold n^c; this is the regime that remains open after random-complex-group-no-quotients-below-exp-pn, and together with that claim it implies the premise through random-complex-large-quotients-split-at-exp-pn.
  random-complex-group-no-quotients-below-exp-pn: that is the proved first-moment regime, orders at most exp(pn/8); this is the complementary regime of larger orders, where the first moment fails.
  meshulam-random-complex-no-polynomial-quotients: that excludes quotients of polynomial order; this asks about orders above exp(n^eta/8), far past any polynomial.
  random-complex-missing-triangle-detected-by-quotient: that asks a random missing triangle to survive in some finite quotient, which by the proved lower regime needs a quotient of order above exp(n^eta/8) and so would refute this claim; this forbids every such quotient.
---

**OPEN, conjectural.** For some `0 < η < 1/2`, with `p = n^(-1+η)`, a.a.s.
`π_1(Y(n,p))` has no nontrivial finite quotient of order greater than
`exp(n^η/8)`.

Together with `random-complex-group-no-quotients-below-exp-pn` this says that
a.a.s. `π_1(Y)` has no nontrivial finite quotient at all. That settles
`random-complex-group-no-large-finite-quotients`, and hence both the
quotientless Kazhdan target and the non-residually-finite target through their
existing random-complex routes.

## What is left

Every nontrivial finite quotient has a nontrivial simple quotient. By the
proved lower regime, a.a.s. every simple quotient of `π_1(Y)` has order above
`exp(n^η/8)`. So the claim is exactly the absence of epimorphisms onto:

- **alternating groups `A_m` with `log(m!/2) > n^η/8`.** The degree `m` is only
  polynomial in `n`, of order `n^η / log n`, so these are connected `m`-sheeted
  covers of `Y` with alternating monodromy;
- **simple groups of Lie type of order above `exp(n^η/8)`,** of unbounded rank or
  over large fields;
- **cyclic groups of prime order above `exp(n^η/8)`,** which is a homological
  question about `H_1(Y; Z/ℓ)`.

Sporadic groups have bounded order, so none survive for large `n`. As
`hyperbolic-rf` notes, superrigidity kills bounded-rank Lie quotients only for
arithmetic hosts, not for random complexes.

## Attempts

- **First moment, run past its range.** The count behind the lower regime pays
  `|G|` per support edge against `exp(-pn/3)` per edge, so it cannot pass order
  `exp(pn/3)`. A refined count must use cancellation in the labels: a present
  triangle containing a support edge must contain a second support edge, and
  that forces equalities between labels. The open problem is to control the
  entropy of these forced label classes when `|G|` is superexponential in
  `n^η`.
- **Local spectral expansion and property (T).** A connected cover of `Y` has the
  same links as `Y`, so it is again a `λ`-local spectral expander, and every
  finite-index subgroup of `π_1(Y)` is again Kazhdan. Nothing local bounds the
  degree of a cover: Ramanujan complexes are local spectral expanders with
  connected covers of unbounded degree along their congruence towers. A proof
  has to use the randomness globally.
- **Calibration by computer (small index only).** GAP `LowIndexSubgroupsFpGroup`,
  index at most 5, on Gromov density-model presentations with 2 generators
  (`experiments/hyperbolic-random-models/`).
  - First run, relator lengths 8, 10, 12: all 144 samples had a proper subgroup
    of index at most 5 and none was perfect. This is an artifact: every freely
    reduced word of even length lies in the kernel of `F_2 -> Z/2`,
    `a, b -> 1`, so even-length models always keep the parity quotient.
  - Rerun with odd lengths: recorded in the experiment directory.
  This probes only the regime the first moment already controls. It is evidence
  about nothing above `exp(n^η/8)`.
