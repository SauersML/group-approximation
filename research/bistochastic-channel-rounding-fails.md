---
rg: 2
id: bistochastic-channel-rounding-fails
kind: claim
title: Some near-idempotent self-adjoint bistochastic channels stay uniformly far from every matrix-algebra expectation
distinct_from:
  bistochastic-near-idempotents-round-dimension-free: that is the positive rounding premise; this is its negation, established by one family of maps with vanishing infinity-to-2 idempotence defect and distance bounded below from every algebra expectation.
  ozawa-sos-does-not-round-approximate-actor-to-exact-commutant: that refutes rounding to the literal commutant of approximate generators; this asks for failure against every algebra expectation, a much weaker target for the rounding and a much stronger one for the counterexample.
---

**OPEN.** There are `c>0`, dimensions `d_n`, and self-adjoint bistochastic
UCP maps `P_n:M_(d_n)->M_(d_n)` with

```text
||P_n^2 - P_n||_(infinity->2) -> 0,
inf_(A subset M_(d_n) unital subalgebra) ||P_n - E_A||_(infinity->2) >= c.
```

This is the negation of `bistochastic-near-idempotents-round-dimension-free`.
The route `channel-rounding-fails-on-the-unstable-branch` shows that the
unstable Steinberg branch forces it: the native heat maps of a canonical
model of `L_(F_2)(1,2)^x` would be such a family. So building a
counterexample is a necessary target for that branch.

## Necessary features of any counterexample family

Each item follows from an established rounding theorem, along a subsequence.

1. **The completely bounded defect stays large.** By
   `ucp-factorizations-round-to-matrix-expectations` with Kitaev's
   factorization theorem, a cb idempotence defect `epsilon` gives distance
   `O(epsilon^(1/4))`. So `liminf ||P_n^2-P_n||_cb` is bounded below by a
   constant depending on `c`. The idempotence failure must therefore live
   on outputs that are large in operator norm but small in normalized
   Hilbert--Schmidt norm. Normalized tracial amplification changes the
   mixed defect by at most `sqrt 2`, so amplification alone cannot produce
   the cb gap.
2. **No bounded-Kraus minorant.** By `bounded-kraus-minorants-force-channel-rounding`,
   for no fixed `lambda>0` and `r` can `P_n - lambda Q_n` be CP with
   `Q_n` bistochastic of Kraus rank at most `r`.
3. **No near-fixed masa.** `near-fixed-masas-round-channels-but-exclude-native-heat`
   forces the averaged masa energy to stay bounded below. The family is not
   close to any Schur channel, `schur-near-idempotents-round-dimension-uniformly`.
4. **The ultraproduct fixed algebra is not internal.** `P^omega=E_B` is an
   exact expectation, and rounding holds exactly when
   `B=product_omega A_n` for unital subalgebras `A_n`. The approximate fixed
   sets `S_n={x : ||x||<=1, ||P_n x-x||_2<=epsilon_n}` have ultraproduct `B`,
   and they are closed under products of bounded length up to
   `O(sqrt(epsilon_n))`. So a counterexample is exactly a tracial
   approximate algebra that is not near an algebra.

## Attempts

- **The unstable Steinberg branch.** Canonical heat maps of `H` would work
  by `leavitt-channel-rounding-forces-nonhyperlinearity`, but canonical
  models of `H` are not known to exist.
- **Deformed pairs of algebras.** The average of expectations onto `A` and a
  slightly rotated `theta(A)` (Ioana's tensor deformation) is not nearly
  idempotent once the deformation is macroscopic. Section 3.1 of the
  heat-rounding boundary artifact shows the defect tends to `1/4`.
- **Non-CP exact idempotents are uniformly excluded.** For any two
  mutually unbiased masas, `Q=E_D+E_C-E_scalar` has exact distance
  `1/3` from every UCP competitor, by
  `mub-sum-idempotents-have-uniform-cp-distance`. This excludes the
  proposed vanishing-perturbation construction in all dimensions. The
  optimizer `(id+E_D+E_C)/3` has idempotence defect exactly `2/9`.
- **Group twirls.** Averages over average-case almost-representations of
  finite groups round, by Gowers--Hatami plus the dimension-change corner
  theorem. A counterexample cannot be a twirl of that kind.
