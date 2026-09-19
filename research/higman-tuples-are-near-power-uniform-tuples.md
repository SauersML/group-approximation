---
rg: 2
id: higman-tuples-are-near-power-uniform-tuples
kind: claim
title: Near-Higman unitary tuples are close, after identity padding, to tuples with small power-uniform BS(1,2) defect
distinct_from:
  bs12-trivially-padded-opnorm-correction: that asks for padded correction of every approximate BS(1,2) pair; this asks for it only for the four cyclically glued pairs of an approximate Higman tuple, and only up to power-uniform defect, so it can hold even if that claim fails.
  higman-four-cycle-intrinsic-mf-seed: that asks for collapse to the identity; this asks only for an upgrade from the relator defect to the power-uniform defect, which is necessary for that collapse but does not force it.
  bs12-conjugator-correction-is-power-uniform-defect: that proves the fixed-base estimate and the equivalence (HMF5) <=> (PUU)+(CGC); this is the open first prerequisite (PUU) of that equivalence.
---

**OPEN.**  All norms are operator norms.  Write

```text
Delta(A,B) = sup_(k in Z) || A B^k A^* - B^(2k) ||
```

as in `bs12-conjugator-correction-is-power-uniform-defect`, and let the
Higman relator defect of `U = (U_0,...,U_3)` be
`max_(i in Z/4) ||U_i U_(i+1) U_i^* - U_(i+1)^2||`.

**(PUU).**  For every `epsilon>0` there is `delta>0` such that for every `N`
and every tuple `U` in `U(N)^4` with Higman relator defect at most `delta`,
there are `k>=0` and `V` in `U(N+k)^4` with

```text
||V_i - (U_i (+) 1_k)|| <= epsilon,    max_(i in Z/4) Delta(V_i, V_(i+1)) <= epsilon.
```

## Status and position

- **Necessary for the marked collapse.**  `(HMF5)` implies `(PUU)` with
  `V_i = 1`.  So a refutation of `(PUU)` refutes
  `higman-four-cycle-intrinsic-mf-seed` (operator-norm collapse), and with it
  the packet route.
- **Sufficient together with glued-cycle collapse.**  By
  `bs12-conjugator-correction-is-power-uniform-defect`, `(PUU)` together with
  `(CGC)` of `higman-exact-packet-cycles-collapse-opnorm` is equivalent to
  `(HMF5)`.
- **Weaker than `(TPC)`.**  `(TPC)` of `bs12-trivially-padded-opnorm-correction`
  implies `(PUU)`.  The per-pair version of `(PUU)` asks, for every
  approximate `BS(1,2)` pair `(A,B)`, for a padded pair `(A',B')` close to it
  with `Delta(A',B')` small.  By `(PU1a)` and `(PU1b)` of that claim, the
  per-pair version is equivalent to `(TPC)`, with constants changed by a
  factor of at most `3`.  So `(PUU)` gains over `(TPC)` only through the
  special shape of Higman tuples: every base `U_(i+1)` must itself be an
  approximate conjugator of `U_(i+2)`.  A counterexample to `(TPC)` refutes
  `(PUU)` only if it can be completed to an approximate Higman tuple.
- **Known cases.**  Suppose some `U_j` is within a fixed `c < 2 sin(2 pi/5)`
  of `1`.  Then `one-small-higman-generator-collapses-the-four-cycle` makes
  the whole tuple small, and `V_i = 1` works.  Any counterexample to `(PUU)`
  must therefore keep every generator at distance at least about
  `2 sin(2 pi/5)` from `1`.
- **Where the gap is.**  The twisted fine clock (item 4 of
  `bs12-conjugator-correction-is-power-uniform-defect`) is a single pair
  with relator defect `2 sin(2 pi/o)` and `Delta` near `2`.  Moving the base
  by `2 sin(2 pi/o)` repairs it.  So `(PUU)` must be allowed to move every
  generator, and the only question is whether those moves can be made
  compatible around the cycle.
