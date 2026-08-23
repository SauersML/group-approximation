---
rg: 2
id: phase-covariance-words-exactly-measure-type-transport-leakage
kind: claim
title: Two-sided phase covariance exactly measures type-transport leakage
distinct_from:
  finite-phase-codewords-weight-type-gram-leakage: that weights off-type block-Gram products using normalizer commutators; this weights the diagonal population of every source-to-target transport block using two-sided phase matching.
  normalizer-phase-tests-leave-diagonal-type-transport: that exhibits the population kernel of phase-normalizer commutators; this supplies the complementary covariance identity which sees that kernel.
---

Let `(E_alpha)_(alpha in A)` and `(F_beta)_(beta in B)` be finite PVMs in a
finite tracial von Neumann algebra `(M,tau)`, and let `U` be unitary.  For
`1<=l<=t`, choose phases `lambda_(l,alpha),mu_(l,beta) in T` and put

```text
D_l=sum_alpha lambda_(l,alpha)E_alpha,
C_l=sum_beta  mu_(l,beta)F_beta.                         (PCT1)
```

Then the exact dimension-free identity is

```text
sum_l ||D_lU-UC_l||_2^2
 =sum_(alpha,beta) W_(alpha,beta)||E_alpha U F_beta||_2^2,

W_(alpha,beta)=sum_l |lambda_(l,alpha)-mu_(l,beta)|^2.  (PCT2)
```

In particular, take a primitive `m`th root `zeta` and source and target
codewords in `(Z/m)^t`.  If the prescribed match `beta=sigma(alpha)` has the
same codeword and every mismatched pair has Hamming distance at least `h_0`,
then

```text
sum_alpha sum_(beta!=sigma(alpha))
 ||E_alpha U F_beta||_2^2
 <=1/(4h_0 sin^2(pi/m)) sum_l ||D_lU-UC_l||_2^2.        (PCT3)
```

When `D_l,C_l,U` are evaluations of ordinary group words, each term on the
right is exactly the defect of

```text
D_l U C_l^(-1) U^(-1).                                 (PCT4)
```

Thus authenticated finite-order type tags give exact word control of
wrong-type population transport, not merely of cross-Gram coherence.  The
hypothesis that the type PVMs are spectral cuts of the named tags is
load-bearing: `(PCT2)` does not manufacture a word tag for an analytically
chosen forbidden subprojection.

