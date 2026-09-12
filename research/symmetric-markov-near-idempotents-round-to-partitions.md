---
rg: 2
id: symmetric-markov-near-idempotents-round-to-partitions
kind: claim
title: Finite reversible Markov near-idempotents round to partition expectations uniformly in dimension and atom weights
distinct_from:
  central-markov-near-idempotents-round-to-normal-cosets: That gives a linear bound and a normal-coset target for central finite-group convolution; this removes all group symmetry and permits every finite reversible stochastic kernel, with a weaker power modulus and a general partition target.
  schur-near-idempotents-round-dimension-uniformly: That concerns entrywise multiplication on matrices and rounds to full coordinate matrix blocks; this concerns stochastic averaging of functions and rounds to block-constant function algebras.
  near-fixed-masas-round-channels-but-exclude-native-heat: That assumes an ambient maximal abelian algebra is almost fixed pointwise; this only requires the channel range to be commutative and permits arbitrarily large multiplicities in the rounded algebra.
  ucp-factorizations-round-to-matrix-expectations: That assumes an approximate UCP factorization through a supplied finite-dimensional algebra; this obtains a partition directly from a reversible Markov kernel and its mixed-norm idempotence defect.
artifacts:
  - research/artifacts/symmetric-markov-partition-rounding-2026-09-08.md
---

Let `Omega` be any finite set with a strictly positive probability
measure `mu`. Let `K` be a stochastic matrix satisfying detailed balance
`mu_i K_ij=mu_j K_ji`, and use complex-valued functions with the
normalized `L^2(mu)` norm. Put

```text
delta=||K^2-K||_(infinity->2).
```

There is a partition `Pi` of the original set such that its
`mu`-preserving conditional expectation satisfies

```text
||K-E_Pi||_(infinity->2) <= min{2,750 delta^(1/5)}.
```

The constants do not depend on the number of atoms, their masses,
the support sizes of the rows, or a lower bound on nonzero transition
probabilities. At zero defect the kernel itself is a partition
expectation.

For `0<delta<=1`, the construction gives an actual partition with

```text
sum_(P in Pi) sum_(i in P,j outside P) mu_i K_ij
 <= [2+12 sqrt(3c)] delta^(2/5) < 25 delta^(2/5),
c=2/sqrt(pi),
```

and every block has the following expansion property in the ORIGINAL
kernel: if `S` is contained in that block and has at most half its
`mu`-mass, then

```text
sum_(i in S,j outside S) mu_i K_ij >= mu(S)/36.
```

No compressed kernel or changed invariant measure is used.

In particular, every self-adjoint bistochastic UCP map on `M_n(C)`
whose range is commutative has, in the same matrix dimension, a
trace-preserving conditional expectation at distance at most
`min{2,750 delta^(1/5)}` in normalized `infinity->2` norm. The
rounded algebra is unitarily conjugate to
`direct_sum_(P in Pi) C I_(|P|)` and can have unbounded
representation multiplicities.

This includes all symmetric finite-group convolution kernels, without
centrality, as diagonal-output matrix channels. It does not assert a
coset target in that generality. General noncommutative-range UCP
rounding, native Kazhdan heat rounding, and nonhyperlinearity remain
outside this theorem.
