---
rg: 2
id: manzoor-two-grade-placement-forces-a-kernel-sandwich
kind: claim
title: A two-grade Manzoor placement collapses to a homogeneous grading and forces a kernel sandwich
distinct_from:
  manzoor-irs-generators-cannot-be-single-actor-grade: that rules out the homogeneous placement when the actor grading is injective; this treats arbitrary actor gradings and identifies the exact residual noninjective case.
  cyclic-aperiodicity-collapses-two-actor-grade-unitaries: that classifies one target unitary; this applies the classification simultaneously to the Manzoor generators and extracts source IRS consequences.
  random-coset-lamp-correlations-realize-every-irs-character: that gives nonmultiplicative four-letter correlations in a random coset-lamp field; this concerns a trace-preserving multiplicative embedding into one fixed algebraic crossed product.
---

Use the notation of `manzoor-irs-generators-cannot-be-single-actor-grade`, and
let `H` act cyclic-aperiodically on `A` as in `(CAT1)`. Suppose there is a
trace-preserving embedding

```text
Psi:P_mu -> L(A rtimes H)                              (MTG1)
```

such that the image of each free generator of `F` has actor Fourier support
of cardinality at most two. Then there is a homomorphism

```text
theta:F->H                                             (MTG2)
```

for which every generator, and hence every word, has one homogeneous actor
grade. If `S` denotes the random subgroup with law `mu`, then necessarily

```text
[ker(theta),ker(theta)] <= S <= ker(theta)             (MTG3)
```

for `mu`-almost every `S`.

Thus two grades do not provide a finite Fourier compiler for the Manzoor
source. If `theta` is injective, `(MTG3)` contradicts the fact that the
Manzoor stabilizer is infinite almost surely. If `theta` is trivial, all
generator images lie in the abelian base, contradicting non-Connes-
embeddability of `P_mu`. The only residual two-grade scenario would be a
proper nontrivial quotient `theta(F)<H` such that the unnamed Manzoor IRS is
almost surely sandwiched between the derived subgroup of the kernel and the
kernel itself. The published source provides no such quotient, and the
two-grade construction has reduced to a one-grade algebraic cocycle rather
than genuine Fourier mixing.
---
