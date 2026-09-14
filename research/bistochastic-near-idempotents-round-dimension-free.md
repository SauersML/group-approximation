---
rg: 2
id: bistochastic-near-idempotents-round-dimension-free
kind: claim
title: Near-idempotent self-adjoint bistochastic channels are uniformly close to matrix-algebra expectations
refuted_by: [bistochastic-channel-rounding-fails]
distinct_from:
  leavitt-channel-rounding-forces-nonhyperlinearity: that is the proved implication from this premise to nonhyperlinearity of the binary Leavitt unit group; this is the premise itself, a statement about matrices with no group in it.
  ucp-factorizations-round-to-matrix-expectations: that rounds under a supplied completely bounded UCP factorization, as Kitaev supplies from a cb idempotence defect; this assumes only the mixed infinity-to-2 defect.
  symmetric-markov-near-idempotents-round-to-partitions: that is the commutative special case, symmetric Markov operators on a finite set; this is the unrestricted noncommutative class.
  schur-near-idempotents-round-dimension-uniformly: that rounds channels diagonal in one matrix-unit basis; this allows arbitrary Kraus operators.
  bounded-kraus-minorants-force-channel-rounding: that needs a bistochastic minorant of bounded Kraus rank, which canonical long-time heat of an infinite group never has; this imposes no rank condition.
---

**OPEN.** There is a function `f(delta) -> 0` as `delta -> 0`, independent
of `d`, such that every UCP map `P:M_d -> M_d` that is unital,
trace-preserving and self-adjoint on `L^2(M_d,tr_d)`, with

```text
||P^2 - P||_(infinity->2) <= delta,
||T||_(infinity->2) = sup_(||x||_op<=1) ||T(x)||_(2,tr_d),
```

has a unital `*`-subalgebra `A subset M_d` with
`||P - E_A||_(infinity->2) <= f(delta)`.

Equivalently, in a tracial matrix ultraproduct: whenever `P_n` are such maps
with defects tending to zero, the idempotent ultraproduct map `E_B` has range
`B = product_omega A_n` for unital subalgebras `A_n subset M_(d_n)`. The
equivalence is the witness argument of Section 5 of the heat-rounding
artifact.

By `leavitt-channel-rounding-forces-nonhyperlinearity` this premise would
make `L_(F_2)(1,2)^x` the first nonhyperlinear group. Conversely, on the
unstable Steinberg branch the native heat maps of any canonical model are
counterexamples. It is a pure matrix-analysis question. The completely
bounded analogue, approximating `eta`-idempotent UCP maps by exactly
idempotent ones, is left open in Kitaev, arXiv:2405.02434v2, Section 1.2.

## Attempts

- **Spectral cutoff.** `Q=1_[1/2,1](P)` satisfies `||P-Q||_(infinity->2)<=2delta`,
  but `Q` need not be positive. The three-state heat example in Section 5 of
  `research/artifacts/leavitt-kazhdan-heat-rounding-boundary-and-factorial-center-countermodel-2026-09-08.md`
  has a non-positive cutoff range, and its infinite-power limit is also far
  from `P`. The good algebra there is a coarse-graining, found by neither
  construction.
- **Multiplicative closure.** Section 4 of the same artifact proves
  `||P(ab)-ab||_2 <= sqrt(2delta)+2delta` for `a,b` in `P((M_d)_1)`, and
  linear error growth over bounded word length. No bound uniform over the
  generated algebra follows.
- **Special classes that do round.**
  - Symmetric Markov and Schur channels, `symmetric-markov-near-idempotents-round-to-partitions`
    and `schur-near-idempotents-round-dimension-uniformly`.
  - Channels with a fixed identity component, `identity-dominated-near-idempotent-channels-round`.
  - Weyl-diagonal channels, Section 11 of the artifact.
  - Bounded Kraus minorants, `bounded-kraus-minorants-force-channel-rounding`.
  - CP reflections, `cp-reflection-near-idempotents-round-to-pinchings`.
  - Near-fixed masas, `near-fixed-masas-round-channels-but-exclude-native-heat`.
  - Supplied cb factorizations, `ucp-factorizations-round-to-matrix-expectations`.

  None of these covers native Kazhdan heat: those maps have growing Kraus
  rank, vanishing purity and no near-fixed masa.
- **Compact group selection.** Sections 14 and 16 of the artifact show that
  almost-fixed unitaries exist but generate an escaping group, and that
  metric approximate closure selects no compact subgroup. A correctly
  selected compact group would suffice, so the complete-positivity input has
  to be used.
- **Counterexample shapes already excluded.** The Ioana tensor-deformation
  average fails idempotence (Section 3.1 of the artifact). Group twirls over
  average-case almost-representations of finite groups round, by
  Gowers--Hatami followed by the dimension-change corner theorem of Section
  10.
- **Non-algebra exact idempotents.** The self-adjoint trace-preserving
  idempotent `E_D+E_(FDF*)-E_C`, for two mutually unbiased diagonal
  algebras, is not completely positive. Its Choi matrix has eigenvalue
  `-1/d` with multiplicity at least `d^2-2d`. Whether UCP maps can approximate such an
  idempotent in the infinity-to-2 norm is not settled here.
